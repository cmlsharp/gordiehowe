// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the SHA-256 comparison harness. It proves SHA-256 of a
// private message to a public digest in three columns: longfellow
// (Longfellow's own pipeline in mdoc's hash-circuit configuration, outside
// GordieHowe), gkr and batched (the relation of
// examples/sha256/sha256_preimage.h in its two modes). This header holds the
// workloads, the Ligero parameters of each column, the systems and the
// timed runs; sha256_compare_test.cc holds the tests and
// sha256_compare_bench.cc the bench commands.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BENCH_HASH_COMPARISONS_SHA256_COMPARE_TEST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BENCH_HASH_COMPARISONS_SHA256_COMPARE_TEST_H_

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <memory>
#include <random>
#include <regex>
#include <string>
#include <utility>
#include <vector>

#include "bench/timing.h"
#include "arrays/dense.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/bit_plucker.h"
#include "circuits/logic/bit_plucker_encoder.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/mdoc/mdoc_zk.h"
#include "circuits/sha/flatsha256_circuit.h"
#include "circuits/sha/flatsha256_witness.h"
#include "gordiehowe/examples/shared/packed_bits.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/shared/bit_phase_testing.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/examples/shared/ligero_testing.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/sha256/sha256_preimage.h"
#include "gordiehowe/lib/sha256.h"
#include "gordiehowe/system.h"
#include "gordiehowe/threads_testing.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "util/crypto.h"
#include "util/readbuffer.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::sha256_compare {
namespace {

enum class Column { kLongfellow, kGkr, kBatched };
const char *name(Column c) {
  return c == Column::kLongfellow ? "longfellow"
         : c == Column::kGkr      ? "gkr"
                                  : "batched";
}
lib::sha256::Sha256Mode mode_of(Column c) {
  return c == Column::kGkr ? lib::sha256::Sha256Mode::kGkr
                           : lib::sha256::Sha256Mode::kBatched;
}

// The message of BLOCKS blocks: BYTES bytes, or 64 BLOCKS - 9 when BYTES is
// 0.
std::vector<uint8_t> workload(size_t blocks, size_t bytes = 0) {
  std::mt19937 g(20261004 + uint32_t(blocks));
  check(bytes == 0 || lib::sha256::sha256_internal::blocks_of(bytes) == blocks,
        "SHA-256 workload: the message length is not BLOCKS blocks");
  std::vector<uint8_t> m(bytes != 0 ? bytes : 64 * blocks - 9);
  for (auto &b : m) b = uint8_t(g());
  return m;
}

std::vector<uint8_t> openssl_sha256(const std::vector<uint8_t> &m) {
  SHA256 h;
  h.Update(m.data(), m.size());
  std::vector<uint8_t> d(kSHA256DigestSize);
  h.DigestData(d.data());
  return d;
}

using bench::Clock;
using bench::ms_since;

// ------------------------------------------------------ unique decoding --

// The unique-decoding Ligero error model: a tableau of N query positions
// (block_enc - (2k - 1)) and message length k, opened at t columns, has
// column round [2 ((N + k) / 2)_t + (a)_t] / (N)_t with
// a = johnsonAgreement(N, 2k - 2), and test round 2N / |F|.
struct Tableau {
  size_t N = 0, k = 0;
};
Tableau tableau_of(size_t block_enc, size_t rate) {
  const size_t k = (block_enc + 1) / (2 + rate);
  return {block_enc - (2 * k - 1), k};
}
size_t johnson_agreement(size_t N, size_t d) {
  const unsigned __int128 x = (unsigned __int128)d * (N - 1);
  size_t s = size_t(std::sqrt((long double)x));
  while ((unsigned __int128)s * s > x) --s;
  while ((unsigned __int128)(s + 1) * (s + 1) <= x) ++s;
  return x <= (unsigned __int128)s * (s + 1) ? s : s + 1;
}
// log2 of the falling factorial (n)_t; -infinity when t > n.
long double log2_ff(size_t n, size_t t) {
  if (t > n) return -INFINITY;
  return (std::lgammal((long double)n + 1) -
          std::lgammal((long double)(n - t) + 1)) /
         std::log(2.0L);
}
long double log2_sum(long double x, long double y) {
  if (x < y) std::swap(x, y);
  if (y == -INFINITY) return x;
  return x + std::log2(1 + std::exp2(y - x));
}
// -log2 of the largest round error (column or test) at T opened columns.
double ud_bits(Tableau tb, size_t t, size_t field_bits) {
  const size_t a = johnson_agreement(tb.N, 2 * tb.k - 2);
  const long double col =
      log2_sum(1 + log2_ff((tb.N + tb.k) / 2, t), log2_ff(a, t)) -
      log2_ff(tb.N, t);
  const long double test = std::log2((long double)(2 * tb.N)) - field_bits;
  return -double(std::max(col, test));
}
// The baseline's per-round target (Longfellow's column and its column rule):
// 2^-108 at the ROM parameters, 2^-236 at the QROM parameters.
template <class P>
constexpr double baseline_target() {
  return P::kPostQuantum ? 236 : 108;
}
// The GordieHowe columns' per-round target, the profile's.
template <class P>
constexpr double gh_target() {
  return compiler::target_bits(ligero_target<P>());
}

// ---------------------------------------------------------- list radius --

// The GordieHowe columns' list-radius tableau: per profile, column and block
// count, its block_enc at the profile's rate (domain_profile.h), from the
// packed-layout search of Prepared (sha256_compare_bench's tableaus command
// prints these lines).
// The planner chooses t, the masking and the low-degree repetitions on it
// at the profile's target.
struct ListRadiusEntry {
  const char *profile;
  Column column;
  size_t blocks, block_enc;
};
const std::vector<ListRadiusEntry> kListRadius = {
    // profile, column, blocks, block_enc;  // (N, k)
    // 17, 129 and 513 blocks: the 1 KiB, 8 KiB and 32 KiB messages of the
    // Binius64 comparison; 33 blocks: a 2048-byte message.
    {"narrow", Column::kGkr, 1, 2747},  // (2356, 196)
    {"narrow", Column::kBatched, 1, 2747},  // (2356, 196)
    {"narrow", Column::kGkr, 2, 2919},  // (2504, 208)
    {"narrow", Column::kBatched, 2, 2585},  // (2218, 184)
    {"narrow", Column::kGkr, 8, 2919},  // (2504, 208)
    {"narrow", Column::kBatched, 8, 3503},  // (3004, 250)
    {"narrow", Column::kGkr, 17, 3722},  // (3193, 265)
    {"narrow", Column::kBatched, 17, 4096},  // (3513, 292)
    {"narrow", Column::kGkr, 32, 3722},  // (3193, 265)
    {"narrow", Column::kBatched, 32, 4746},  // (4069, 339)
    {"narrow", Column::kGkr, 33, 3722},  // (3193, 265)
    {"narrow", Column::kBatched, 33, 4746},  // (4069, 339)
    {"narrow", Column::kGkr, 64, 4203},  // (3604, 300)
    {"narrow", Column::kBatched, 64, 7258},  // (6223, 518)
    {"narrow", Column::kGkr, 129, 4746},  // (4069, 339)
    {"narrow", Column::kBatched, 129, 9832},  // (8429, 702)
    {"narrow", Column::kGkr, 513, 9253},  // (7932, 661)
    {"narrow", Column::kBatched, 513, 18034},  // (15459, 1288)
    {"wide", Column::kGkr, 1, 4203},  // (3604, 300)
    {"wide", Column::kBatched, 1, 3722},  // (3193, 265)
    {"wide", Column::kGkr, 2, 4096},  // (3513, 292)
    {"wide", Column::kBatched, 2, 3722},  // (3193, 265)
    {"wide", Column::kGkr, 8, 4746},  // (4069, 339)
    {"wide", Column::kBatched, 8, 3955},  // (3392, 282)
    {"wide", Column::kGkr, 17, 4203},  // (3604, 300)
    {"wide", Column::kBatched, 17, 4746},  // (4069, 339)
    {"wide", Column::kGkr, 32, 4746},  // (4069, 339)
    {"wide", Column::kBatched, 32, 7258},  // (6223, 518)
    {"wide", Column::kGkr, 33, 4746},  // (4069, 339)
    {"wide", Column::kBatched, 33, 6429},  // (5512, 459)
    {"wide", Column::kGkr, 64, 4746},  // (4069, 339)
    {"wide", Column::kBatched, 64, 7712},  // (6613, 550)
    {"wide", Column::kBatched, 129, 11794},  // (10111, 842)
    {"wide", Column::kBatched, 513, 18034},  // (15459, 1288)
};
// The batched column with its GF(2^16) words committed unpacked
// (DomainProfile::unpacked_s0): block_enc from the same search.
const std::vector<ListRadiusEntry> kListRadiusUnpacked = {
    // profile, column, blocks, block_enc;  // (N, k)
    {"narrow", Column::kBatched, 1, 2585},  // (2218, 184)
    {"narrow", Column::kBatched, 8, 3503},  // (3004, 250)
    {"narrow", Column::kBatched, 32, 4746},  // (4069, 339)
    {"wide", Column::kBatched, 1, 3722},  // (3193, 265)
    {"wide", Column::kBatched, 8, 4746},  // (4069, 339)
    {"wide", Column::kBatched, 32, 4746},  // (4069, 339)
};
const ListRadiusEntry *list_radius(const char *profile, Column c,
                                   size_t blocks, bool unpacked = false) {
  for (const auto &e : unpacked ? kListRadiusUnpacked : kListRadius)
    if (std::strcmp(e.profile, profile) == 0 && e.column == c &&
        e.blocks == blocks)
      return &e;
  return nullptr;
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

// One GordieHowe column's Ligero: the planner's (the default), or explicit
// parameters, unique decoding at NREQ opened columns or list radius at T
// with MASKING, BLOCK_ENC fixed or 0 for the packed-layout search.
struct LigeroChoice {
  size_t nreq = 0, block_enc = 0;
  bool list_radius = false;
  size_t t = 0;
  LigeroMasking masking = LigeroMasking::kSplit;
  // H's GF(2^16) words committed unpacked (DomainProfile::unpacked_s0).
  bool unpacked_s0 = false;
  // The batches without the univariate skip (DomainProfile::no_skip, a
  // test-only ablation).
  bool no_skip = false;
  // The bit-index sumcheck (DomainProfile::bit_phase); false is its
  // ablation.
  bool bit_phase = true;
  // The planner's list-radius Ligero at the profile's target
  // (DomainProfile::target) on BLOCK_ENC (block_enc_fixed), or on the
  // profile's block grid when BLOCK_ENC is 0; NREQ, LIST_RADIUS, T and
  // MASKING are then unread.
  bool planned = true;
  // Unique decoding by Longfellow's column rule (LongfellowSha): for t from
  // 16 up, block_enc from the packed-layout search at t opened columns,
  // until the tableau meets the profile's target at t. The search writes
  // the t it stops at here; BLOCK_ENC and NREQ are then ignored.
  std::shared_ptr<size_t> ud_rule_t;
};

// Domain H at the default profile of its field (domain_profile.h), the
// profile of every application's H domain, with Ligero CHOICE.
template <class P>
DomainProfile<typename Env<P>::HF, typename Env<P>::RSH, typename Env<P>::PH>
h_profile(const Env<P> &env, const LigeroChoice &choice) {
  using HF = typename Env<P>::HF;
  using PH = typename Env<P>::PH;
  auto p = domain_profile<P>(env.hf, env.rsh);
  p.unpacked_s0 = choice.unpacked_s0;
  p.bit_phase = choice.bit_phase;
  p.no_skip = choice.no_skip;
  if (choice.planned) {
    p.block_enc_fixed = choice.block_enc;
    return p;
  }
  // Explicit parameters at the profile's rate.
  p.target.reset();
  p.nreq = choice.nreq;
  p.list_radius = choice.list_radius;
  p.t = choice.t;
  p.masking = choice.masking;
  const size_t rate = p.rate, opened = p.opened(), be = choice.block_enc;
  if (const auto out = choice.ud_rule_t) {
    p.block_enc = [rate, out](const Circuit<HF> &c, size_t, size_t) {
      for (size_t t = 16;; ++t) {
        const size_t e = h_block_enc<PH>("GH-SHA-UD", c, rate, t);
        const Tableau tb = tableau_of(e, rate);
        check(2 * t <= tb.k, "GordieHowe SHA-256: no t meets the target");
        if (ud_bits(tb, t, HF::kBits) >= baseline_target<P>()) {
          *out = t;
          return e;
        }
      }
    };
    return p;
  }
  p.block_enc = [rate, opened, be](const Circuit<HF> &c, size_t, size_t) {
    return be ? be : h_block_enc<PH>("GH-SHA-H", c, rate, opened);
  };
  return p;
}

// The node of the graph REF lies in named NAME.
template <class R>
size_t node_named(const R &ref, const std::string &nm) {
  const auto &N = ref.g->nodes;
  for (size_t id = 0; id < N.size(); ++id)
    if (N[id].name == nm) return id;
  fail("no node " + nm);
}

template <class P>
class ShaSystem {
 public:
  using HF = typename Env<P>::HF;
  using Elt = typename HF::Elt;
  using Sys = typename Env<P>::Sys;
  using Assignment = typename Sys::Assignment;
  using Compiled = typename Sys::Compiled;

  Sys cs{"gh-sha256-compare"};
  // A committed value only SHA-256's constraints read, for the tampering
  // test: its node and index, and whether it is a GF(2^16) word.
  size_t tamper_node = 0, tamper_at = 0;
  bool tamper_word = false;

  ShaSystem(const Env<P> &env, size_t blocks, Column c,
            const LigeroChoice &ligero, size_t bytes = 0)
      : env_(env), msg_(workload(blocks, bytes)) {
    auto &H = cs.domain(h_profile<P>(env, ligero), "H");
    const auto r =
        sha256_preimage::sha256_preimage(cs, H, msg_.size(), mode_of(c));
    m_ = r.witness.message;
    want_ = r.statement.digest;
    const auto &out = r.hash;
    if (c == Column::kBatched) {
      // A bit of e after round 10 of block 0 (its family e, [64, nb,
      // 32]), whose bits the compiler stores as GF(2^16) words: bit 0 of
      // the word's low half.
      tamper_node = node_named(out, "sha.e.words");
      tamper_at = 2 * 10 * lib::sha256::sha256_internal::blocks_of(msg_.size());
      tamper_word = true;
    } else {
      tamper_node = node_named(out, "sha.witness");
      tamper_at = (48 + 10) * 32 + 5;  // a bit of oute[10] of block 0
      tamper_word = false;
    }
  }

  std::unique_ptr<Compiled> compile() { return gordiehowe::compile(cs); }

  Assignment statement(bool wrong = false) const {
    auto d = openssl_sha256(msg_);
    if (wrong) d[13] ^= 0x40;
    Assignment st;
    st.set(want_, bits(d));
    return st;
  }
  Assignment witness() const {
    Assignment w;
    w.set(m_, bits(msg_));
    return w;
  }
  size_t message_bytes() const { return msg_.size(); }

 private:
  std::vector<Elt> bits(const std::vector<uint8_t> &bytes) const {
    std::vector<Elt> v;
    for (uint8_t b : bytes)
      for (size_t i = 0; i < 8; ++i)
        v.push_back((b >> i) & 1 ? env_.hf.one() : env_.hf.zero());
    return v;
  }

  const Env<P> &env_;
  std::vector<uint8_t> msg_;
  Ref<HF, Bit, Committed> m_;
  Ref<HF, Bit, Public> want_;
};

// ------------------------------------------------------------ the bench --

struct ProofRun {
  double witness = 0, commit = 0, prove = 0, verify = 0;
  size_t bytes = 0;
  bool ok = false;
};

// Longfellow's SHA-256 (the header's longfellow column) over profile P's
// hash field and protocol hash, at the least opened count meeting P's
// target under the unique-decoding model on Longfellow's own tableau.
template <class P>
class LongfellowSha {
 public:
  using F = typename P::HashField;
  using Elt = typename F::Elt;
  using RS = LCH14ReedSolomonFactory<F>;
  using Hash = typename P::ProtocolHash;
  static constexpr size_t kRate = kLigeroRatev7;
  // mdoc_hash.h's plucker.
  static constexpr size_t kPluckerBits = 4;
  static constexpr size_t kVersion = 7;
  static constexpr char kLabel[] = "longfellow-sha256";

  explicit LongfellowSha(size_t blocks)
      : blocks_(blocks), msg_(workload(blocks)), rs_(f_) {
    using CB = CompilerBackend<F>;
    using LC = Logic<F, CB>;
    using Flat = FlatSHA256Circuit<LC, BitPlucker<LC, kPluckerBits>>;
    QuadCircuit<F> q(f_);
    const CB cb(&q);
    const LC lc(&cb, f_);
    const Flat sha(lc);
    const auto target = lc.template vinput<256>();
    q.private_input();
    const auto nb = lc.template vinput<8>();
    std::vector<typename LC::v8> in(64 * blocks);
    for (auto &x : in) x = lc.template vinput<8>();
    std::vector<typename Flat::BlockWitness> bw(blocks);
    for (auto &b : bw) b.input(lc);
    // Every private input is a subfield element (a bit or a plucked
    // element), as in mdoc's hash circuit.
    q.begin_full_field();
    sha.assert_message_hash(blocks, nb, in.data(), target, bw.data());
    // The circuit id, which the transcript absorbs, at P's hash.
    c_ = q.template mkcircuit<Hash>(1);
    // The least t whose own tableau (Ligero's block_enc search at t) meets
    // the target.
    for (size_t t = 16;; ++t) {
      const auto prm = ZkProof<F, Hash>(*c_, kRate, t).param;
      const Tableau tb = tableau_of(prm.block_enc, kRate);
      if (ud_bits(tb, t, F::kBits) >= baseline_target<P>()) {
        nreq_ = t;
        block_enc_ = prm.block_enc;
        tableau_ = tb;
        break;
      }
      check(2 * t <= tb.k,
            "Longfellow SHA-256: no opened count meets the target");
    }
  }
  size_t nreq() const { return nreq_; }
  size_t block_enc() const { return block_enc_; }
  Tableau tableau() const { return tableau_; }
  double bits() const { return ud_bits(tableau_, nreq_, F::kBits); }
  const Circuit<F> &circuit() const { return *c_; }
  // The Ligero tableau's committed witness length.
  size_t nw() const {
    return ZkProof<F, Hash>(*c_, kRate, nreq_, block_enc_).param.nw;
  }
  // The Ligero tableau's rows.
  size_t nrow() const {
    return ZkProof<F, Hash>(*c_, kRate, nreq_, block_enc_).param.nrow;
  }
  // The private inputs by kind: block-witness elements of kPluckerBits
  // plucked bits each (outw, oute, outa, h1: 184 32-bit words per block),
  // and elements of one bit each (nb and the padded message).
  size_t plucked_elements() const {
    return blocks_ * 184 * 32 / kPluckerBits;
  }
  size_t bit_elements() const { return 8 + 512 * blocks_; }

  // The witness in the circuit's input order: 1, the digest (bit j of the
  // v256 is bit j % 8 of byte 31 - j / 8), then nb, the padded message's
  // bytes and the plucked block witnesses.
  std::unique_ptr<Dense<F>> witness(const std::vector<uint8_t> &digest) const {
    auto out = std::make_unique<Dense<F>>(1, c_->ninputs);
    Dense<F> &w = *out;
    size_t at = 0;
    auto bit = [&](uint64_t b) {
      w.v_[at++] = (b & 1) ? f_.one() : f_.zero();
    };
    w.v_[at++] = f_.one();
    for (size_t j = 0; j < 256; ++j) bit(digest[(255 - j) / 8] >> (j % 8));
    uint8_t numb = 0;
    std::vector<uint8_t> padded(64 * blocks_);
    std::vector<FlatSHA256Witness::BlockWitness> bw(blocks_);
    FlatSHA256Witness::transform_and_witness_message(
        msg_.size(), msg_.data(), blocks_, numb, padded.data(), bw.data());
    for (size_t i = 0; i < 8; ++i) bit(numb >> i);
    for (uint8_t x : padded)
      for (size_t i = 0; i < 8; ++i) bit(x >> i);
    BitPluckerEncoder<F, kPluckerBits> enc(f_);
    auto push = [&](uint32_t v) {
      for (const auto &e : enc.mkpacked_v32(v)) w.v_[at++] = e;
    };
    for (const auto &b : bw) {
      for (size_t k = 0; k < 48; ++k) push(b.outw[k]);
      for (size_t k = 0; k < 64; ++k) {
        push(b.oute[k]);
        push(b.outa[k]);
      }
      for (size_t k = 0; k < 8; ++k) push(b.h1[k]);
    }
    check(at == c_->ninputs, "Longfellow SHA-256 witness size");
    return out;
  }

  // One proof and its verification. Witness covers the witness assembly;
  // commit covers the prover's setup, the statement and the commitment;
  // verify covers the verifier's setup, the parsing of the serialized
  // proof, the statement and the checks.
  ProofRun run(SecureRandomEngine &rng, bool wrong_digest = false) const {
    const auto digest = openssl_sha256(msg_);
    ProofRun r;
    auto t0 = Clock::now();
    const auto wp = witness(digest);
    const Dense<F> &w = *wp;
    r.witness = ms_since(t0);

    t0 = Clock::now();
    ZkProof<F, Hash> zk(*c_, kRate, nreq_, block_enc_);
    ZkProver<F, RS, Hash> prover(*c_, f_, rs_);
    const BasicProofSeed<Hash> seed = BasicProofSeed<Hash>::draw(rng);
    BasicTranscript<Hash> tp(reinterpret_cast<const uint8_t *>(kLabel),
                             sizeof(kLabel) - 1, seed, kVersion);
    absorb_circuit_statement(tp, *c_, w, f_);
    prover.commit(zk, w, tp, rng);
    r.commit = ms_since(t0);
    t0 = Clock::now();
    const bool proved = prover.prove(zk, w, tp);
    r.prove = ms_since(t0);
    // [seed] [ZK proof].
    std::vector<uint8_t> buf;
    seed.write(buf);
    zk.write(buf, f_);
    r.bytes = buf.size();

    t0 = Clock::now();
    ZkVerifier<F, RS, Hash> verifier(*c_, rs_, kRate, nreq_, block_enc_, f_);
    ReadBuffer rb(buf);
    BasicProofSeed<Hash> vseed;
    ZkProof<F, Hash> vz(*c_, kRate, nreq_, block_enc_);
    bool ok = vseed.read(rb) && vz.read(rb, f_) && rb.remaining() == 0;
    Dense<F> pub(1, c_->npub_in);
    for (size_t i = 0; i < c_->npub_in; ++i) pub.v_[i] = w.v_[i];
    if (wrong_digest) pub.v_[1 + 77] = f_.addf(pub.v_[1 + 77], f_.one());
    BasicTranscript<Hash> tv(reinterpret_cast<const uint8_t *>(kLabel),
                             sizeof(kLabel) - 1, vseed, kVersion);
    if (ok) {
      absorb_circuit_statement(tv, *c_, pub, f_);
      verifier.recv_commitment(vz, tv);
      ok = verifier.verify(vz, pub, tv);
    }
    r.verify = ms_since(t0);
    r.ok = proved && ok;
    return r;
  }

 private:
  const F f_;
  size_t blocks_;
  std::vector<uint8_t> msg_;
  RS rs_;
  std::unique_ptr<Circuit<F>> c_;
  size_t nreq_ = 0, block_enc_ = 0;
  Tableau tableau_;
};

// The H domain's circuit and batch in the compile report.
struct Shape {
  size_t layers = 0, quad = 0, committed = 0, nw = 0, ligero = 0, lanes = 0,
         degree = 0, messages = 0, pads = 0, rounds = 0;
};
Shape shape_of(const std::string &r) {
  Shape s;
  std::smatch m;
  auto num = [&](const char *re, size_t &out) {
    if (std::regex_search(r, m, std::regex(re))) out = std::stoul(m[1]);
  };
  num(R"(committed=(\d+))", s.committed);
  num(R"(nw=(\d+))", s.nw);
  num(R"(rows, (\d+) committed)", s.ligero);
  num(R"(layers=(\d+))", s.layers);
  num(R"(quad_terms=(\d+))", s.quad);
  num(R"(Q degree (\d+))", s.degree);
  num(R"((\d+) lanes, width)", s.lanes);
  num(R"((\d+) rounds, \d+ pads)", s.rounds);
  num(R"((\d+) pads,)", s.pads);
  num(R"((\d+) message elements)", s.messages);
  return s;
}

size_t block_enc_of(const std::string &r) {
  std::smatch m;
  check(std::regex_search(r, m, std::regex(R"(block_enc=(\d+))")),
        "compile report: no block_enc");
  return std::stoul(m[1]);
}

// The packed-layout search's rounds at most (Prepared's search).
constexpr size_t kSearchRounds = 8;

// A GordieHowe column's system, compiled and prepared once: at list radius
// on the block_enc of kListRadius, or else of the search. The search starts
// from the planner's t on the profile's own block grid, finds the
// packed-layout search's block_enc at the profile's rate and that many
// opened columns (h_block_enc), plans list-radius Ligero on it, and
// repeats at the planner's new t until the t it plans is the t it searched
// at (at most kSearchRounds rounds).
template <class P>
struct Prepared {
  using T = ShaSystem<P>;
  std::unique_ptr<T> t;
  std::unique_ptr<typename T::Compiled> c;
  std::unique_ptr<typename T::Sys::Prepared> prep;
  Shape shape;
  LigeroChoice ligero;
  Tableau tableau;
  double compile_ms = 0, build_ms = 0, bits = 0;
  // Whether the block_enc came from the search (no kListRadius entry), the
  // search's rounds, and the planner's own choice on the profile's block
  // grid, where the search starts.
  bool searched = false;
  size_t search_rounds = 0, grid_block_enc = 0, grid_t = 0;
  // UD_RULE: unique decoding by Longfellow's column rule
  // (LigeroChoice::ud_rule_t) in place of the list-radius table. NO_SKIP:
  // the batches without the univariate skip (DomainProfile::no_skip).
  // BYTES: the message length (workload), 0 for 64 BLOCKS - 9. TABLE: the
  // block_enc of kListRadius where it has an entry (else always the
  // search). REPORT: print the compile report.
  Prepared(const Env<P> &env, size_t blocks, Column col,
           bool unpacked = false, bool ud_rule = false, bool no_skip = false,
           size_t bytes = 0, bool table = true, bool report = false) {
    using HF = typename P::HashField;
    ligero.unpacked_s0 = unpacked;
    ligero.no_skip = no_skip;
    const size_t rate = domain_profile<P>(env.hf, env.rsh).rate;
    auto build = [&](const LigeroChoice &l) {
      auto t0 = Clock::now();
      t = std::make_unique<T>(env, blocks, col, l, bytes);
      build_ms = ms_since(t0);
      t0 = Clock::now();
      c = t->compile();
      compile_ms = ms_since(t0);
      return block_enc_of(c->report());
    };
    // The explicit parameters of the probes.
    LigeroChoice probe;
    probe.planned = false;
    probe.unpacked_s0 = unpacked;
    probe.no_skip = no_skip;
    if (ud_rule) {
      probe.ud_rule_t = std::make_shared<size_t>(0);
      const size_t be = build(probe);
      ligero.planned = false;
      ligero.nreq = *probe.ud_rule_t;
      ligero.block_enc = be;
      check(build(ligero) == be, "unique-decoding block_enc");
      tableau = tableau_of(be, rate);
      bits = ud_bits(tableau, ligero.nreq, HF::kBits);
      shape = shape_of(c->report());
      if (report) std::printf("%s\n", c->report().c_str());
      return;
    }
    if (const ListRadiusEntry *e =
            table ? list_radius(P::kId, col, blocks, unpacked) : nullptr) {
      ligero.block_enc = e->block_enc;
      check(build(ligero) == e->block_enc, "list-radius block_enc");
    } else {
      searched = true;
      ligero.block_enc = 0;
      grid_block_enc = build(ligero);
      size_t at = grid_t = c->compiled_domain(0).plan().t;
      for (search_rounds = 1;; ++search_rounds) {
        probe.nreq = at;
        ligero.block_enc = build(probe);
        check(build(ligero) == ligero.block_enc, "searched block_enc");
        const size_t planned_t = c->compiled_domain(0).plan().t;
        if (planned_t == at) break;
        check(search_rounds < kSearchRounds,
              "SHA-256 search: the planner's t does not settle");
        at = planned_t;
      }
    }
    // The planner's choice on the tableau.
    const DomainPlan dp = c->compiled_domain(0).plan();
    ligero.list_radius = true;
    ligero.t = dp.t;
    ligero.masking =
        dp.split ? LigeroMasking::kSplit : LigeroMasking::kUntested;
    tableau = tableau_of(ligero.block_enc, rate);
    bits = std::min({dp.commit_bits, dp.test_bits, dp.column_bits});
    shape = shape_of(c->report());
    if (report) std::printf("%s\n", c->report().c_str());
  }
  void prepare() {
    prep = std::make_unique<typename T::Sys::Prepared>(
        c->prepare(t->statement()));
  }
  size_t opened() const {
    return ligero.list_radius ? ligero.t : ligero.nreq;
  }
  const char *model() const {
    if (!ligero.list_radius) return "unique-decoding";
    return ligero.masking == LigeroMasking::kSplit ? "list-radius-split"
                                                   : "list-radius-untested";
  }
  ProofRun run(SecureRandomEngine &rng) const {
    const auto w = t->witness();
    ProveTimes pt;
    typename T::Sys::ProveOptions opt;
    opt.times = &pt;
    const auto proof = prep->prove(w, rng, opt);
    const auto t0 = Clock::now();
    ProofRun r;
    r.ok = prep->verify(proof);
    r.verify = ms_since(t0);
    r.witness = pt.witness;
    r.commit = pt.commit;
    r.prove = pt.prove;
    r.bytes = proof.size();
    return r;
  }
};

constexpr Column kColumns[] = {Column::kLongfellow, Column::kGkr,
                               Column::kBatched};

}  // namespace
}  // namespace proofs::gordiehowe::examples::sha256_compare

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BENCH_HASH_COMPARISONS_SHA256_COMPARE_TEST_H_
