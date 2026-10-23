// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: SelectFirst with a scheme scan (select.h,
// examples/mldsa/sample_in_ball.h), the record permutation (permutation.h) and
// ML-DSA's SampleInBall on them.
//   - SampleInBallScan on a short stream: the honest selection, and a
//     skipped sample, a wrong count (a threshold that does not advance) and
//     a rejected sample in the output are rejected;
//   - assert_permutation: a permutation proves, a multiset that differs is
//     rejected, and misuse is a compile error;
//   - SampleInBall at ML-DSA-44's parameters: the decoded challenge equals
//     the reference Fisher-Yates shuffle, and a wrong read value, a wrong
//     final cell, a stale read origin and swapped positions are rejected;
//     on a stream whose first 128 candidates fall short, the scan selects
//     past them (SampleInBallPastOneBlock).

#include <cstddef>
#include <cstdint>
#include <map>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/compile_error_testing.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/examples/mldsa/sample_in_ball.h"
#include "gordiehowe/lib/permutation.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

// The sample-in-ball and selection gadgets are the ML-DSA example's.
using namespace ::proofs::gordiehowe::examples;  // NOLINT

using HF = GF2_128<>;
using HElt = HF::Elt;
using HV = std::vector<HElt>;
using RSH = LCH14ReedSolomonFactory<HF>;
using Sys = ConstraintSystem<SHA384, HF>;
using SysValue = Sys::Value;
using Assignment = Sys::Assignment;
using ProveOptions = Sys::ProveOptions;
using CompiledSystem = Sys::Compiled;

struct Env {
  HF hf;
  RSH rsh{hf};
  DomainProfile<HF, RSH, SHA384> h_profile() const {
    DomainProfile<HF, RSH, SHA384> p;
    p.f = &hf;
    p.rsf = &rsh;
    p.field_name = "GF(2^128)";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    return p;
  }
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}
const HF &hf() { return env().hf; }

bool honest(const CompiledSystem &c, const Assignment &w) {
  auto prep = c.prepare({});
  SecureRandomEngine rng;
  return prep.verify(prep.prove(w, rng));
}
template <class Tamper>
bool verifier_rejects(const CompiledSystem &c, const Assignment &w,
                      Tamper tamper) {
  auto prep = c.prepare({});
  ProveOptions opt;
  opt.tamper = tamper;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  std::vector<uint8_t> proof;
  try {
    proof = prep.prove(w, rng, opt);
  } catch (const std::runtime_error &e) {
    ADD_FAILURE() << "the cheating prover stopped: " << e.what();
    return false;
  }
  return !prep.verify(proof);
}
// The values the honest prover computes.
std::map<size_t, SysValue> capture(const CompiledSystem &c, const Assignment &w) {
  std::map<size_t, SysValue> cap;
  auto prep = c.prepare({});
  ProveOptions opt;
  opt.tamper = [&](size_t id, SysValue &v) { cap[id] = v; };
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng, opt)));
  return cap;
}
HV bytes_bits(const std::vector<uint8_t> &b) {
  HV out;
  for (uint8_t x : b)
    for (size_t j = 0; j < 8; ++j) out.push_back((x >> j) & 1 ? hf().one() : hf().zero());
  return out;
}
std::vector<uint8_t> bits_bytes(const HV &v) {
  std::vector<uint8_t> out(v.size() / 8, 0);
  for (size_t i = 0; i < v.size(); ++i)
    if (v[i] == hf().one()) out[i / 8] |= uint8_t(1u << (i % 8));
  return out;
}
// SampleInBall's selection (FIPS 204 Algorithm 29) on the stream bytes.
std::vector<uint8_t> reference_j(const std::vector<uint8_t> &u, size_t tau) {
  std::vector<uint8_t> j;
  size_t thr = 256 - tau;
  for (uint8_t b : u)
    if (j.size() < tau && b <= thr) {
      j.push_back(b);
      ++thr;
    }
  return j;
}

// ------------------------------------------------------------ selection --

struct SelSys {
  Sys cs{"gh-sample-select"};
  Domain<HF> *H;
  Ref<HF, Bit, Committed> stream;
  SampleInBallSelection<HF> sel;
  SelSys(size_t S, size_t tau) {
    H = &cs.domain(env().h_profile(), "H");
    stream = H->priv(Bit{}, "stream", 8 * S);
    sel = sample_in_ball_select(cs, *H, "sib", stream, tau);
  }
};

TEST(GordieHoweSample, SampleInBallScanSelects) {
  // tau = 4: thresholds 252, 253, 254, 255, then 0.
  const std::vector<uint8_t> u = {254, 3,   255, 10, 255, 255, 5,  200,
                                  9,   250, 1,   0,  77,  255, 31, 2};
  const size_t tau = 4;
  SelSys t(u.size(), tau);
  auto c = compile(t.cs);
  EXPECT_EQ(c->phase(t.sel.delta), 1u);
  Assignment w;
  w.set(t.stream, bytes_bits(u));
  auto cap = capture(*c, w);
  EXPECT_EQ(bits_bytes(std::get<HV>(cap.at(t.sel.j.id))),
            (std::vector<uint8_t>{3, 10, 5, 200}));
  EXPECT_EQ(reference_j(u, tau), (std::vector<uint8_t>{3, 10, 5, 200}));
  auto put = [](size_t id, HV v) {
    return [id, v](size_t at, SysValue &x) {
      if (at == id) std::get<HV>(x) = v;
    };
  };
  // A skipped sample: the output starts at the second accepted one.
  EXPECT_TRUE(verifier_rejects(
      *c, w, put(t.sel.j.id, bytes_bits({10, 5, 200, 9}))));
  // A rejected sample in the output.
  EXPECT_TRUE(verifier_rejects(
      *c, w, put(t.sel.j.id, bytes_bits({254, 10, 5, 200}))));
  // A wrong count: the threshold does not advance after the first
  // selection (its low bits stay those of 252).
  const size_t tid = t.sel.threshold.id, L = t.sel.threshold.dims()[1];
  EXPECT_TRUE(verifier_rejects(*c, w, [tid, L](size_t at, SysValue &x) {
    if (at != tid) return;
    auto &v = std::get<HV>(x);
    for (size_t b = 0; b < L; ++b)
      v[2 * L + b] = (252 >> b) & 1 ? hf().one() : hf().zero();
  }));
  // Too few acceptable samples: the honest prover fails completeness.
  SelSys t2(4, 4);
  auto c2 = compile(t2.cs);
  Assignment w2;
  w2.set(t2.stream, bytes_bits({255, 255, 1, 2}));
  auto prep = c2->prepare({});
  SecureRandomEngine rng;
  EXPECT_THROW(prep.prove(w2, rng), CompletenessFailure);
}

// ---------------------------------------------------------- permutation --

TEST(GordieHoweSample, PermutationOfRecords) {
  for (bool equal : {true, false}) {
    Sys cs("gh-sample-perm");
    auto &H = cs.domain(env().h_profile(), "H");
    auto a = H.priv(Subfield{}, "a", 3);
    auto b = H.priv(Bit{}, "b", 3);
    auto x = H.priv(Subfield{}, "x", 3);
    lib::permutation::Records<HF, 3> left(H), right(H);
    left.push(a, b, 5);
    right.push(x, b.reindex({1, 0, 2}).named("bp"), 5);
    lib::permutation::assert_multiset_equal(cs, H, "perm", left, right);
    auto c = compile(cs);
    const HV av = {hf().of_scalar(7), hf().of_scalar(9), hf().of_scalar(11)};
    const HV bv = {hf().one(), hf().zero(), hf().one()};
    HV xv = {av[1], av[0], av[2]};
    if (!equal) xv[2] = hf().of_scalar(12);
    Assignment w;
    w.set(a, av);
    w.set(b, bv);
    w.set(x, xv);
    if (equal) {
      EXPECT_TRUE(honest(*c, w));
    } else {
      auto prep = c->prepare({});
      ProveOptions opt;
      opt.require_satisfied = false;
      SecureRandomEngine rng;
      EXPECT_FALSE(prep.verify(prep.prove(w, rng, opt)));
    }
  }
}

// A component outside the subfield packs by a challenge (perm.gamma); the
// subfield components pack by the fixed kappa (no gamma).
TEST(GordieHoweSample, PermutationPacking) {
  const HElt kappa = lib::permutation::selection_kappa(hf());
  for (int k = 0; k < 3; ++k) {
    for (bool equal : {true, false}) {
      Sys cs("gh-sample-packing");
      auto &H = cs.domain(env().h_profile(), "H");
      auto a = H.priv(Subfield{}, "a", 2);
      auto b = H.priv(Subfield{}, "b", 2);
      auto x = H.priv(Field{}, "x", 2);
      auto y = H.priv(Field{}, "y", 2);
      lib::permutation::Records<HF, 2> l(H), r(H);
      if (k == 0) {
        l.push(a, 1);
        r.push(b, 1);
      } else if (k == 1) {
        l.push(x, 1);
        r.push(y, 1);
      } else {
        l.push(kappa * a, 1);
        r.push(kappa * b, 1);
      }
      const auto m =
          lib::permutation::assert_multiset_equal(cs, H, "perm", l, r);
      EXPECT_EQ(m.packing.gamma.has_value(), k != 0) << k;
      auto c = compile(cs);
      const HV av = {hf().of_scalar(7), hf().of_scalar(9)};
      const HV xv = {hf().of_scalar(11), hf().of_scalar(13)};
      HV bv = {av[1], av[0]}, yv = {xv[1], xv[0]};
      if (!equal) {
        bv[0] = hf().of_scalar(8);
        yv[0] = hf().of_scalar(12);
      }
      Assignment w;
      w.set(a, av).set(b, bv).set(x, xv).set(y, yv);
      if (equal) {
        EXPECT_TRUE(honest(*c, w)) << k;
      } else {
        auto prep = c->prepare({});
        ProveOptions opt;
        opt.require_satisfied = false;
        SecureRandomEngine rng;
        EXPECT_FALSE(prep.verify(prep.prove(w, rng, opt))) << k;
      }
    }
  }
}

TEST(GordieHoweSample, PermutationMisuseIsACompileError) {
  // Components of different lengths.
  EXPECT_NE(error_of([] {
              Sys cs("e3");
              auto &H = cs.domain(env().h_profile(), "H");
              auto a = H.priv(Subfield{}, "a", 2);
              auto b = H.priv(Subfield{}, "b", 3);
              lib::permutation::Records<HF, 2> l(H);
              l.push(a, b);
            }),
            "");
  // SelectFirst: an output of another width.
  EXPECT_NE(error_of([] {
              Sys cs("e4");
              auto &H = cs.domain(env().h_profile(), "H");
              auto st = H.priv(Bit{}, "st", Shape{8, 8});
              auto out = H.priv(Bit{}, "out", Shape{2, 4});
              SampleInBallScan<HF> scan;
              lib::select::select_first(cs, H, "sel", st, out, scan);
            }),
            "");
  EXPECT_NE(error_of([] {
              Sys cs("e5");
              auto &H = cs.domain(env().h_profile(), "H");
              auto st = H.priv(Bit{}, "st", 8 * 8);
              sample_in_ball_select(cs, H, "sib", st, 200);
            }),
            "");
}

// ---------------------------------------------------------- SampleInBall --

// kS: the 264 candidates of ML-DSA's 272-byte stream (mldsa_hash.h).
constexpr size_t kTau = 39, kS = 264, kN = 256;

// The reference Fisher-Yates shuffle of the selection J and signs SGN.
std::vector<int> reference_c(const std::vector<uint8_t> &j,
                             const std::vector<int> &sgn) {
  std::vector<int> c(kN, 0);
  for (size_t s = 0; s < kTau; ++s) {
    const size_t i = kN - kTau + s;
    c[i] = c[j[s]];
    c[j[s]] = sgn[s] ? -1 : 1;
  }
  return c;
}

struct SibSys {
  Sys cs{"gh-sample-sib"};
  Domain<HF> *H;
  Ref<HF, Bit, Committed> stream, signs;
  SampleInBall<HF> sib;
  SibSys() {
    H = &cs.domain(env().h_profile(), "H");
    stream = H->priv(Bit{}, "stream", 8 * kS);
    signs = H->priv(Bit{}, "signs", kTau);
    sib = sample_in_ball(cs, *H, "sib", stream, signs);
    // Read the decoded challenge, as the crossing would.
    assert_true((sib.shuffle.sign & sib.shuffle.support) |
                      !sib.shuffle.sign,
                  "decoded");
  }
};

TEST(GordieHoweSample, SampleInBallMatchesTheReference) {
  SibSys t;
  auto c = compile(t.cs);
  std::mt19937_64 g(5);
  std::vector<uint8_t> u(kS);
  for (auto &x : u) x = uint8_t(g());
  HV sg;
  std::vector<int> sgn(kTau);
  for (size_t k = 0; k < kTau; ++k) {
    sgn[k] = int(g() & 1);
    sg.push_back(sgn[k] ? hf().one() : hf().zero());
  }
  Assignment w;
  w.set(t.stream, bytes_bits(u));
  w.set(t.signs, sg);
  auto cap = capture(*c, w);
  // The reference shuffle.
  const auto j = reference_j(u, kTau);
  ASSERT_EQ(j.size(), kTau);
  const std::vector<int> cref = reference_c(j, sgn);
  const HV cenc = std::get<HV>(cap.at(t.sib.shuffle.c_enc.id));
  const HElt theta = sample_in_ball_theta(hf());
  for (size_t k = 0; k < kN; ++k) {
    const HElt want = cref[k] == 0 ? hf().zero() : cref[k] == 1 ? hf().one() : theta;
    EXPECT_EQ(cenc[k], want) << k;
  }
  // DecodeTernary: sign = v^2 + v, support = v + (theta + 1) sign.
  for (size_t k = 0; k < kN; ++k) {
    const HElt v = cenc[k];
    const HElt sv = hf().addf(hf().mulf(v, v), v);
    const HElt pv = hf().addf(v, hf().mulf(hf().addf(theta, hf().one()), sv));
    EXPECT_EQ(sv, cref[k] == -1 ? hf().one() : hf().zero()) << k;
    EXPECT_EQ(pv, cref[k] != 0 ? hf().one() : hf().zero()) << k;
  }
  auto flip = [](size_t id, size_t i, HElt v) {
    return [id, i, v](size_t at, SysValue &x) {
      if (at == id) std::get<HV>(x).at(i) = v;
    };
  };
  const auto &sh = t.sib.shuffle;
  // A wrong read value at a step that reads a written cell.
  size_t step = 0;
  while (step < kTau && j[step] == kN - kTau + step) ++step;
  ASSERT_LT(step, kTau);
  EXPECT_TRUE(verifier_rejects(*c, w, flip(sh.read_value.id, step, theta)));
  // A wrong final cell.
  size_t k1 = 0;
  while (cref[k1] != 1) ++k1;
  EXPECT_TRUE(verifier_rejects(*c, w, flip(sh.c_enc.id, k1, theta)));
  // A stale read origin (o_t = t + 1 is not below t + 1), its bits and its
  // record cell consistent.
  const size_t lb = sh.read_origin.dims()[1];
  EXPECT_TRUE(verifier_rejects(*c, w, [&](size_t at, SysValue &x) {
    auto &v = std::get<HV>(x);
    if (at == sh.origin.id) v[step] = lib::select::host::word_value(hf(), step + 1, 16);
    if (at != sh.read_origin.id) return;
    for (size_t b = 0; b < lb; ++b)
      v[step * lb + b] = ((step + 1) >> b) & 1 ? hf().one() : hf().zero();
  }));
  // A record origin off its bits, and a unit off its sign.
  EXPECT_TRUE(verifier_rejects(
      *c, w, flip(sh.origin.id, step, lib::select::host::word_value(hf(), step + 1, 16))));
  EXPECT_TRUE(verifier_rejects(
      *c, w, flip(sh.unit.id, step, hf().addf(theta, hf().one()))));
  // Two positions swapped.
  const size_t jid = t.sib.select.j.id;
  EXPECT_TRUE(verifier_rejects(*c, w, [jid](size_t at, SysValue &x) {
    if (at != jid) return;
    auto &v = std::get<HV>(x);
    for (size_t b = 0; b < 8; ++b) std::swap(v[3 * 8 + b], v[7 * 8 + b]);
  }));
}

// A stream whose first 130 candidates are 255 (rejected at i = 256 - tau),
// so one SHAKE256 block's 128 candidates give no sample: the scan selects
// from candidates 130 onward, and the decoded challenge equals the
// reference shuffle's.
TEST(GordieHoweSample, SampleInBallPastOneBlock) {
  SibSys t;
  auto c = compile(t.cs);
  std::mt19937_64 g(7);
  constexpr size_t kRejected = 130;
  std::vector<uint8_t> u(kS);
  for (size_t i = 0; i < kS; ++i) u[i] = i < kRejected ? 255 : uint8_t(g());
  EXPECT_TRUE(reference_j(std::vector<uint8_t>(u.begin(), u.begin() + 128),
                          kTau)
                  .empty());
  const auto j = reference_j(u, kTau);
  ASSERT_EQ(j.size(), kTau);
  HV sg;
  std::vector<int> sgn(kTau);
  for (size_t k = 0; k < kTau; ++k) {
    sgn[k] = int(g() & 1);
    sg.push_back(sgn[k] ? hf().one() : hf().zero());
  }
  Assignment w;
  w.set(t.stream, bytes_bits(u));
  w.set(t.signs, sg);
  auto cap = capture(*c, w);
  EXPECT_EQ(bits_bytes(std::get<HV>(cap.at(t.sib.select.j.id))), j);
  const std::vector<int> cref = reference_c(j, sgn);
  const HV cenc = std::get<HV>(cap.at(t.sib.shuffle.c_enc.id));
  const HElt theta = sample_in_ball_theta(hf());
  for (size_t k = 0; k < kN; ++k) {
    const HElt want = cref[k] == 0 ? hf().zero() : cref[k] == 1 ? hf().one() : theta;
    EXPECT_EQ(cenc[k], want) << k;
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
