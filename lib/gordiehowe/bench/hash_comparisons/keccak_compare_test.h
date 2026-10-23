// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Keccak comparison harness. It proves the SHAKE256 work of
// one H domain alone, with Keccak batched (keccak.h) or in GKR
// (Longfellow's Sha3Circuit::assert_shake256), for one of four presets:
// falcon (HashToPoint), ml-dsa (mu, c_tilde and SampleInBall's stream),
// perms (N independent Keccak-f[1600] permutations, batched only) and sha3
// (the relation of examples/keccak/sha3_preimage.h, batched only). This
// header holds the workloads and the systems; keccak_compare_test.cc holds
// the tests and keccak_compare_bench.cc the bench commands.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BENCH_HASH_COMPARISONS_KECCAK_COMPARE_TEST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BENCH_HASH_COMPARISONS_KECCAK_COMPARE_TEST_H_

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <memory>
#include <random>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/examples/shared/keccak_host.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "circuits/tests/sha3/sha3_circuit.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "circuits/tests/sha3/sha3_slicing.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/shared/bit_phase_testing.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/examples/shared/ligero_testing.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/keccak/sha3_preimage.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/system.h"
#include "gordiehowe/threads_testing.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::keccak_compare {
namespace {

enum class Mode { kGkr, kBatched };
enum class Preset { kFalcon, kMlDsa, kPerms, kSha3 };

const char *name(Mode m) { return m == Mode::kGkr ? "gkr" : "batched"; }
const char *name(Preset p) {
  if (p == Preset::kPerms) return "perms";
  if (p == Preset::kSha3) return "sha3";
  return p == Preset::kFalcon ? "falcon" : "ml-dsa";
}

// The perms preset's default permutation count.
constexpr size_t kDefaultPerms = 8;

// The perms preset's private input states, 200 bytes each in FIPS 202's
// byte order, and their Keccak-f[1600] outputs.
std::vector<uint8_t> perms_inputs(size_t n) {
  std::mt19937 g(20261014);
  std::vector<uint8_t> in(200 * n);
  for (auto &x : in) x = uint8_t(g());
  return in;
}
std::vector<uint8_t> perms_outputs(const std::vector<uint8_t> &in) {
  std::vector<uint8_t> out(in.size());
  for (size_t p = 0; p < in.size() / 200; ++p) {
    uint64_t a[5][5] = {};
    Sha3Reference::xorin(a, in.data() + 200 * p, 200);
    Sha3Reference::keccak_f_1600_DEBUG_ONLY(a);
    for (size_t l = 0; l < 25; ++l)
      for (size_t b = 0; b < 8; ++b)
        out[200 * p + 8 * l + b] = uint8_t(a[l % 5][l / 5] >> (8 * b));
  }
  return out;
}

constexpr size_t kShakeRate = 136;

// ---- The sha3 preset: SHA3-256 of a private message of L bytes.
// The blocks of an L-byte message: its padding (suffix 0x06 and the final
// 0x80, in one byte when they meet) takes at least one byte, so L bytes
// fill floor(L / 136) + 1 blocks of the rate, one permutation each.
size_t sha3_blocks(size_t bytes) {
  return bytes / lib::keccak::kSha3_256.rate + 1;
}
// The default message length at N permutations: 136 N - 1 bytes, the
// longest message of N blocks.
size_t sha3_default_bytes(size_t perms) {
  return lib::keccak::kSha3_256.rate * perms - 1;
}
std::vector<uint8_t> sha3_message(size_t bytes) {
  std::mt19937 g(20261016);
  std::vector<uint8_t> m(bytes);
  for (auto &x : m) x = uint8_t(g());
  return m;
}
// SHA3-256 by the reference implementation (Sha3Reference at a 32-byte
// digest: rate 200 - 64 = 136, suffix 0x06).
std::vector<uint8_t> sha3_256_reference(const std::vector<uint8_t> &m) {
  Sha3Reference h(lib::keccak::kSha3_256DigestBytes);
  h.update(reinterpret_cast<const char *>(m.data()), m.size());
  std::vector<uint8_t> d(lib::keccak::kSha3_256DigestBytes);
  h.final(d.data());
  return d;
}
// ---- end of the sha3 preset's host code.

// The compiler tier: the GKR column states Keccak as one circuit of
// Sha3Circuit's gates, the baseline the batched column is compared with.
struct L : compiler::Lowering {
  using compiler::Lowering::gkr;
};

// ------------------------------------------------------------ workloads --

// One byte range of a hash input: constant, public, private, or the whole
// output of an earlier call.
struct Segment {
  enum Kind { kConst, kPublic, kPrivate, kOutput } kind;
  std::vector<uint8_t> bytes;  // kConst, kPublic, kPrivate
  size_t call = 0;             // kOutput
};
struct Call {
  std::vector<Segment> in;
  size_t outlen;
};
// The calls in order; the last call's output is asserted public.
using Workload = std::vector<Call>;

Workload falcon_workload() {
  constexpr size_t kSaltBytes = 40, kMessageBytes = 32;
  constexpr size_t kSamples = 512 + 127;  // n + falcon_oversamples(512)
  std::mt19937 g(20260915);
  std::vector<uint8_t> seed(kSaltBytes + kMessageBytes);
  for (auto &x : seed) x = uint8_t(g());
  return {{{{Segment::kPrivate, seed}}, 2 * kSamples}};
}

Workload ml_dsa_workload() {
  constexpr size_t kW1Bytes = 4 * 192;  // K w1_bytes, ML-DSA-44
  // SampleInBall's stream: two blocks, at least FIPS 204 Appendix C's 221.
  constexpr size_t kCTildeBytes = 32, kSibBytes = 272;
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  std::vector<uint8_t> tr(64);
  Sha3Reference::shake256Hash(ex.pkey.data(), ex.pkey.size(), tr.data(),
                              tr.size());
  // w1_tilde is an algebra output; its value does not change the hashing.
  std::mt19937 g(20260929);
  std::vector<uint8_t> w1(kW1Bytes);
  for (auto &x : w1) x = uint8_t(g());
  Workload w;
  std::vector<Segment> mu{{Segment::kPublic, tr},
                          {Segment::kConst, {0x00, uint8_t(ex.ctx.size())}}};
  if (!ex.ctx.empty()) mu.push_back({Segment::kPublic, ex.ctx});
  mu.push_back({Segment::kPrivate, ex.msg});
  w.push_back({mu, 64});
  w.push_back({{{Segment::kOutput, {}, 0}, {Segment::kPrivate, w1}},
               kCTildeBytes});
  w.push_back({{{Segment::kOutput, {}, 1}}, kSibBytes});
  return w;
}

Workload workload(Preset p) {
  if (p == Preset::kPerms) return {};
  return p == Preset::kFalcon ? falcon_workload() : ml_dsa_workload();
}

// The input and output bytes of each call, from the input segments' bytes
// (VALUES: each kPublic and kPrivate segment's bytes, in workload order).
struct HostCalls {
  std::vector<std::vector<uint8_t>> in, out;
};
HostCalls host_calls(const Workload &w,
                     const std::vector<std::vector<uint8_t>> &values) {
  HostCalls h;
  size_t v = 0;
  for (const auto &c : w) {
    std::vector<uint8_t> in;
    for (const auto &s : c.in) {
      const std::vector<uint8_t> *b = &s.bytes;
      if (s.kind == Segment::kOutput) b = &h.out.at(s.call);
      if (s.kind == Segment::kPublic || s.kind == Segment::kPrivate)
        b = &values.at(v++);
      in.insert(in.end(), b->begin(), b->end());
    }
    std::vector<uint8_t> out(c.outlen);
    Sha3Reference::shake256Hash(in.data(), in.size(), out.data(), out.size());
    h.in.push_back(std::move(in));
    h.out.push_back(std::move(out));
  }
  return h;
}
std::vector<std::vector<uint8_t>> segment_values(const Workload &w) {
  std::vector<std::vector<uint8_t>> v;
  for (const auto &c : w)
    for (const auto &s : c.in)
      if (s.kind == Segment::kPublic || s.kind == Segment::kPrivate)
        v.push_back(s.bytes);
  return v;
}

// Block witnesses Sha3Circuit::assert_shake256 takes for one call.
size_t gkr_blocks(size_t inlen, size_t outlen) {
  return (inlen + kShakeRate) / kShakeRate +
         (outlen == 0 ? 0 : (outlen - 1) / kShakeRate);
}
size_t slices() {
  size_t n = 0;
  for (size_t r = 0; r < 24; ++r) n += sha3_slice_at(r) ? 1 : 0;
  return n;
}

// --------------------------------------------------------------- system --

template <class P>
struct Env {
  using HF = typename P::HashField;
  using PH = typename P::ProtocolHash;
  using RSH = LCH14ReedSolomonFactory<HF>;
  using Sys = ConstraintSystem<PH, HF>;
  HF hf;
  RSH rsh{hf};
};

// Domain H at the default profile of its field (domain_profile.h), the
// profile of every application's H domain, for every preset. NO_SKIP: the
// batches without the univariate skip (DomainProfile::no_skip, a test-only
// ablation).
template <class P>
DomainProfile<typename Env<P>::HF, typename Env<P>::RSH, typename Env<P>::PH>
h_profile(const Env<P> &env, bool no_skip = false) {
  auto p = domain_profile<P>(env.hf, env.rsh);
  p.no_skip = no_skip;
  return p;
}

template <class P>
class KeccakSystem {
 public:
  using HF = typename Env<P>::HF;
  using Elt = typename HF::Elt;
  using Vec = std::vector<Elt>;
  using Sys = typename Env<P>::Sys;
  using Assignment = typename Sys::Assignment;
  using Compiled = typename Sys::Compiled;
  using CLogic = Logic<HF, CompilerBackend<HF>>;
  using BitW = typename CLogic::BitW;

  Sys cs{"gh-keccak-compare"};
  // A committed Keccak value for the tampering test: its node and index.
  size_t tamper_node = 0, tamper_at = 0;
  bool tamper_word = false;  // a GF(2^16) state word, else a Bit

  // SHA3_BYTES: the sha3 preset's message length (0:
  // sha3_default_bytes(PERMS)); PERMS: the perms preset's permutation
  // count.
  KeccakSystem(const Env<P> &env, Preset preset, Mode mode,
               bool no_skip = false, size_t sha3_bytes = 0,
               size_t perms = kDefaultPerms)
      : env_(env), preset_(preset), mode_(mode), w_(workload(preset)) {
    auto &H = cs.domain(h_profile(env, no_skip), "H");
    if (preset == Preset::kSha3) {
      check(mode == Mode::kBatched, "the sha3 preset is batched only");
      sha3_bytes_ = sha3_bytes != 0 ? sha3_bytes : sha3_default_bytes(perms);
      nwords_ = lib::keccak::kSha3_256DigestBytes / 2;
      const auto r = sha3_preimage::sha3_preimage(H, sha3_bytes_);
      priv_.push_back(r.witness.message);
      words_ = r.statement.words;
      sha3_perms_ = r.sha3.perms;
      set_tamper(r.sha3);
      return;
    }
    if (preset == Preset::kPerms) {
      check(mode == Mode::kBatched, "the perms preset is batched only");
      check(perms > 0, "the perms preset needs a permutation");
      nperms_ = perms;
      nwords_ = 100 * nperms_;
      priv_.push_back(H.priv(Bit{}, "states", 1600 * nperms_));
      words_ = H.pub(Field{}, "words", nwords_);
      declare_perms(H);
      return;
    }
    const HostCalls host = host_calls(w_, segment_values(w_));
    nwords_ = host.out.back().size() / 2;
    // Public: each call's public bytes in call order, then the output
    // words. Private: each call's private bytes.
    size_t np = 0, nq = 0;
    for (const auto &c : w_)
      for (const auto &sg : c.in) {
        if (sg.kind == Segment::kPublic) {
          pub_.push_back(H.pub(Bit{}, "pub" + std::to_string(np++),
                                        8 * sg.bytes.size()));
          inputs_.push_back(pub_.back());
        } else if (sg.kind == Segment::kPrivate) {
          priv_.push_back(H.priv(
              Bit{}, "priv" + std::to_string(nq++), 8 * sg.bytes.size()));
          inputs_.push_back(priv_.back());
        }
      }
    words_ = H.pub(Field{}, "words", nwords_);
    if (mode == Mode::kBatched)
      declare_batched(H);
    else
      declare_gkr(H, host);
  }

  std::unique_ptr<Compiled> compile() { return gordiehowe::compile(cs); }

  Assignment statement(bool wrong = false) const {
    const auto values = segment_values(w_);
    const HF &f = env_.hf;
    Assignment st;
    std::vector<uint8_t> out;
    if (preset_ == Preset::kSha3) {
      out = sha3_256_reference(sha3_message(sha3_bytes_));
    } else if (preset_ == Preset::kPerms) {
      out = perms_outputs(perms_inputs(nperms_));
    } else {
      const HostCalls host = host_calls(w_, values);
      size_t v = 0, p = 0;
      for (const auto &c : w_)
        for (const auto &sg : c.in) {
          if (sg.kind == Segment::kPublic)
            st.set(pub_.at(p++), bits(values[v]));
          if (sg.kind == Segment::kPublic || sg.kind == Segment::kPrivate) ++v;
        }
      out = host.out.back();
    }
    Vec d;
    for (size_t i = 0; i < nwords_; ++i)
      d.push_back(f.of_scalar(uint16_t(out[2 * i] | (out[2 * i + 1] << 8))));
    if (wrong) d[nwords_ / 2] = f.addf(d[nwords_ / 2], f.one());
    st.set(words_, d);
    return st;
  }

  // FLIP: the sha3 preset's message with bit FLIP - 1 flipped (0: none).
  Assignment witness(size_t flip = 0) const {
    const auto values = segment_values(w_);
    Assignment w;
    if (preset_ == Preset::kSha3) {
      Vec m = bits(sha3_message(sha3_bytes_));
      if (flip != 0) {
        auto &e = m.at(flip - 1);
        e = e == env_.hf.one() ? env_.hf.zero() : env_.hf.one();
      }
      w.set(priv_.at(0), m);
      return w;
    }
    if (preset_ == Preset::kPerms) {
      w.set(priv_.at(0), bits(perms_inputs(nperms_)));
      return w;
    }
    size_t v = 0, q = 0;
    for (const auto &c : w_)
      for (const auto &sg : c.in) {
        if (sg.kind == Segment::kPrivate) w.set(priv_.at(q++), bits(values[v]));
        if (sg.kind == Segment::kPublic || sg.kind == Segment::kPrivate) ++v;
      }
    return w;
  }

  // The sha3 preset's message bytes.
  size_t sha3_bytes() const { return sha3_bytes_; }

  // Keccak-f permutations the workload runs.
  size_t permutations() const {
    if (preset_ == Preset::kPerms) return nperms_;
    // The sponge's own count (SpongeCall::perms), not the requested N.
    if (preset_ == Preset::kSha3) return sha3_perms_;
    const HostCalls host = host_calls(w_, segment_values(w_));
    size_t n = 0;
    for (size_t c = 0; c < w_.size(); ++c)
      n += gkr_blocks(host.in[c].size(), w_[c].outlen);
    return n;
  }

 private:
  Vec bits(const std::vector<uint8_t> &bytes) const {
    Vec v;
    for (uint8_t b : bytes)
      for (size_t i = 0; i < 8; ++i)
        v.push_back((b >> i) & 1 ? env_.hf.one() : env_.hf.zero());
    return v;
  }

  // The output as 16-bit little-endian words equals the public words. The
  // perms preset leaves the check's placement to the compiler, which makes
  // it affine rows; the falcon and ml-dsa presets pin it to the circuit.
  // The sha3 preset is the relation of sha3_preimage.h.
  template <class D, class O>
  void assert_words(D &H, const O &out) {
    const Expr<HF> words = sha3_preimage::le_words(H, out, nwords_);
    if (preset_ == Preset::kPerms) {
      assert_equal(words, words_, "words");
      return;
    }
    assert_equal(words, words_, "words").pin(Placement::kCircuit);
  }

  template <class D>
  void declare_batched(D &H) {
    const auto kb = lib::keccak::keccak_batch(H, "keccak");
    if (preset_ == Preset::kFalcon) {
      const auto sh =
          lib::keccak::shake256(kb, "h2p", priv_.at(0), w_[0].outlen);
      set_tamper(sh);
      assert_words(H, sh.out);
      return;
    }
    // tr || 0 || |ctx| || [ctx] || M, then mu || w1, then c_tilde.
    const auto &mu_in = w_[0].in;
    const auto prefix = lib::keccak::constant_bytes(mu_in[1].bytes);
    const bool ctx = pub_.size() > 1;
    const auto mu =
        ctx ? lib::keccak::shake256(
                  kb, "mu",
                  lib::keccak::sponge_input(pub_[0], prefix, pub_[1], priv_[0]),
                  w_[0].outlen)
            : lib::keccak::shake256(
                  kb, "mu",
                  lib::keccak::sponge_input(pub_[0], prefix, priv_[0]),
                  w_[0].outlen);
    const auto ct = lib::keccak::shake256(
        kb, "c_tilde", lib::keccak::sponge_input(mu.out, priv_[1]),
        w_[1].outlen);
    const auto sib = lib::keccak::shake256(kb, "sib", ct.out, w_[2].outlen);
    set_tamper(mu);
    assert_words(H, sib.out);
  }
  // Each permutation's rounds by keccak_f (one round per committed state,
  // so placement merges every round of every permutation into one batch),
  // its output state read as the 100 16-bit words of its last round state,
  // as sponge() reads a squeezed block.
  template <class D>
  void declare_perms(D &H) {
    std::vector<Ref<HF, Bit, Committed>> outs;
    std::vector<Coord> at;
    for (size_t p = 0; p < nperms_; ++p) {
      const std::string nm = "keccak.p" + std::to_string(p);
      const Expr<HF, Bit> in(
          priv_[0].slice(1600 * p, 1600 * (p + 1)).reshape(Shape{5, 5, 64}));
      const auto s = lib::keccak::keccak_f(H, nm, in);
      if (p == 0) {
        tamper_node = cs.graph().nodes.at(s.at(10).id).deps.at(0);
        tamper_at = 7;
        tamper_word = true;
      }
      Ref<HF, Bit, Committed> part = s.back();
      if (const auto words = H.words_of(part)) {
        std::vector<size_t> select(100);
        for (size_t q = 0; q < select.size(); ++q) select[q] = q;
        part = H.bits(nm + ".out", *words, std::move(select));
      }
      for (size_t i = 0; i < 1600; ++i) at.push_back({outs.size(), i});
      outs.push_back(part);
    }
    assert_words(H, gather(outs, at).named("keccak.out"));
  }

  // Word 7 of round state 10, a round word only the batch reads (the words
  // its bit view reads).
  template <class Sh>
  void set_tamper(const Sh &sh) {
    tamper_node = cs.graph().nodes.at(sh.states.at(10).id).deps.at(0);
    tamper_at = 7;
    tamper_word = true;
  }

  template <class D>
  void declare_gkr(D &H, const HostCalls &host) {
    const HF *pf = &env_.hf;
    const size_t ns = slices();
    const Workload w = w_;
    std::vector<Ref<HF>> reads(inputs_.begin(), inputs_.end());
    std::vector<size_t> nblocks;
    for (size_t c = 0; c < w.size(); ++c) {
      const size_t nb = gkr_blocks(host.in[c].size(), w[c].outlen);
      nblocks.push_back(nb);
      // The checkpoints of call C from the inputs (Sha3Witness, in
      // fill_witness's order: blocks, checkpoint rounds, lanes (x, y),
      // bits low first).
      const auto cp = H.priv(
          Bit{}, "c" + std::to_string(c) + ".checkpoints",
          Shape(nb * ns * 25 * 64), std::vector<Ref<HF>>(reads.begin(),
                                                         reads.begin() +
                                                             long(inputs_.size())),
          [pf, w, c](const std::vector<const std::vector<Elt> *> &in) {
            std::vector<std::vector<uint8_t>> values;
            for (const auto *v : in) {
              std::vector<uint8_t> b(v->size() / 8, 0);
              for (size_t i = 0; i < v->size(); ++i)
                if ((*v)[i] == pf->one()) b[i / 8] |= uint8_t(1u << (i % 8));
              values.push_back(std::move(b));
            }
            const HostCalls h = host_calls(w, values);
            std::vector<Sha3Witness::BlockWitness> hb;
            Sha3Witness::compute_witness_shake256(h.in[c], w[c].outlen, hb);
            std::vector<Elt> out;
            for (const auto &b : hb)
              for (size_t r = 0; r < 24; ++r) {
                if (!sha3_slice_at(r)) continue;
                for (size_t x = 0; x < 5; ++x)
                  for (size_t y = 0; y < 5; ++y)
                    for (size_t i = 0; i < 64; ++i)
                      out.push_back((b.a_intermediate[r][x][y] >> i) & 1
                                        ? pf->one()
                                        : pf->zero());
              }
            return out;
          });
      if (c == 0) {
        tamper_node = cp.id;
        tamper_at = 0;
        tamper_word = false;
      }
      reads.push_back(cp);
    }
    reads.push_back(words_);
    const size_t ninputs = inputs_.size(), nwords = nwords_;
    L::gkr(
        H, "keccak", reads,
        [pf, w, ns, nblocks, ninputs, nwords](
            const CLogic &lc, const std::vector<std::vector<size_t>> &wr) {
          using v8 = typename CLogic::v8;
          using v16 = typename CLogic::v16;
          using BW = typename Sha3Circuit<CLogic>::BlockWitness;
          auto bit = [pf](size_t x) { return BitW(pf->zero(), pf->one(), x); };
          std::vector<std::vector<v8>> outs;
          size_t v = 0;
          for (size_t c = 0; c < w.size(); ++c) {
            std::vector<v8> in;
            for (const auto &sg : w[c].in) {
          if (sg.kind == Segment::kConst) {
            for (uint8_t b : sg.bytes) in.push_back(lc.template vbit<8>(b));
          } else if (sg.kind == Segment::kOutput) {
            const auto &o = outs.at(sg.call);
            in.insert(in.end(), o.begin(), o.end());
          } else {
            const auto &x = wr.at(v++);
            for (size_t k = 0; k < x.size() / 8; ++k) {
              v8 byte;
              for (size_t i = 0; i < 8; ++i) byte[i] = bit(x[8 * k + i]);
              in.push_back(byte);
            }
          }
            }
            const auto &cw = wr.at(ninputs + c);
            std::vector<BW> bws(nblocks[c]);
            size_t at = 0;
            for (auto &b : bws)
          for (size_t r = 0; r < 24; ++r) {
            if (!sha3_slice_at(r)) continue;
            for (size_t x = 0; x < 5; ++x)
              for (size_t y = 0; y < 5; ++y)
                for (size_t i = 0; i < 64; ++i)
                  b.a_intermediate[r][x][y][i] = bit(cw.at(at++));
          }
            check(at == cw.size(), "checkpoint wires");
            (void)ns;
            std::vector<v8> o;
            Sha3Circuit<CLogic>(lc).assert_shake256(in, w[c].outlen, o, bws);
            outs.push_back(std::move(o));
          }
          const auto &pw = wr.at(ninputs + w.size());
          for (size_t i = 0; i < nwords; ++i) {
            v16 word;
            for (size_t b = 0; b < 8; ++b) {
          word[b] = outs.back()[2 * i][b];
          word[8 + b] = outs.back()[2 * i + 1][b];
            }
            lc.assert_eq(lc.as_scalar(word), pw.at(i));
          }
        });
  }

  const Env<P> &env_;
  Preset preset_;
  Mode mode_;
  Workload w_;
  size_t nperms_ = 0;
  size_t nwords_ = 0;
  size_t sha3_perms_ = 0;
  size_t sha3_bytes_ = 0;
  std::vector<Ref<HF, Bit, Public>> pub_;
  std::vector<Ref<HF, Bit, Committed>> priv_;
  std::vector<Ref<HF>> inputs_;  // public and private segments, in order
  Ref<HF, Field, Public> words_;
};

}  // namespace
}  // namespace proofs::gordiehowe::examples::keccak_compare

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BENCH_HASH_COMPARISONS_KECCAK_COMPARE_TEST_H_
