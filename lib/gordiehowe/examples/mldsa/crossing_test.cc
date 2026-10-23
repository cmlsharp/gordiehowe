// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: integers of H carried to A by x.to(A) (a Bit copy and the
// cross-field assert_equal) between the ML-DSA native profile's domains,
// H = GF(2^128) or GF(2^256) and A = F_q^6 or F_q^11, their bound q an
// explicit predicate in H (x.from_bits() < q), with A's Boolean checks in
// the circuit and as one batched relation.
//
//   Honest            the proof verifies, A's bits are H's integers, and the
//                     report places A's Boolean checks as asked
//   Rejected          each of these is rejected by the verifier:
//                       an A bit flipped (A differs from H)
//                       an H integer changed, A keeping the old bits
//                       an integer at the bound q (out of range)
//                       a wrong bit decomposition in A (2 at bit 0, 0 at
//                       bit 1: the same field value, not Boolean)
//
// crossing_bench (crossing_bench.cc) times the crossing.

#include "gordiehowe/examples/mldsa/crossing_fixture.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

template <class P>
class CrossingTest : public ::testing::Test {};
TYPED_TEST_SUITE(CrossingTest, param_sets::Profiles, param_sets::ProfileName);

template <class T>
bool prove_verify(const T &t, const typename T::Sys::Compiled &c,
                  const std::vector<uint64_t> &v,
                  std::function<void(size_t, typename T::Value &)> tamper,
                  bool cheating) {
  auto prep = c.prepare(typename T::Sys::Assignment{});
  typename T::Sys::ProveOptions opt;
  if (tamper) opt.tamper = std::move(tamper);
  opt.require_satisfied = !cheating;
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(t.witness(v), rng, opt));
  } catch (const std::runtime_error &) {
    return false;
  }
}

TYPED_TEST(CrossingTest, HonestAndRejected) {
  using T = CrossingSystem<TypeParam>;
  using Value = typename T::Value;
  using AV = typename T::AV;
  const Env<TypeParam> env;
  const auto &af = env.af;
  const size_t n = 64;
  const auto v = sample_integers(n);
  for (Placement where : {Placement::kCircuit, Placement::kBatch}) {
    SCOPED_TRACE(placement_name(where));
    T t(env, n, where);
    const auto c = gordiehowe::compile(t.cs, compile_profile<TypeParam>());
    const std::string rep = c->report();
    if (where == Placement::kCircuit) {
      EXPECT_NE(rep.find("batch_bit_checks=0"), std::string::npos);
    } else {
      EXPECT_NE(rep.find(" cell_bit_checks=0 "), std::string::npos) << rep;
      EXPECT_NE(rep.find("batch A.boolean"), std::string::npos) << rep;
    }
    const size_t bits = t.id("crossing.bits");
    // Honest, with A's bits equal to the integers'.
    std::map<size_t, Value> cap;
    EXPECT_TRUE(prove_verify(
        t, *c, v, [&cap](size_t at, Value &x) { cap[at] = x; }, false));
    {
      const auto &b = std::get<AV>(cap.at(bits));
      for (size_t i = 0; i < n; ++i) {
        uint64_t y = 0;
        for (size_t j = 0; j < kW; ++j)
          y |= uint64_t(ct::bit_of(af, b[i * kW + j])) << j;
        EXPECT_EQ(y, v[i]);
      }
    }
    // An A bit flipped.
    EXPECT_FALSE(prove_verify(
        t, *c, v,
        [&af, bits](size_t at, Value &x) {
          if (at != bits) return;
          auto &e = std::get<AV>(x).at(5 * kW + 3);
          e = af.subf(af.one(), e);
        },
        true));
    // An H integer changed; A keeps the honest bits.
    {
      auto w = v;
      w[7] ^= 1u << 4;
      const auto honest = cap.at(bits);
      EXPECT_FALSE(prove_verify(
          t, *c, w,
          [&honest, bits](size_t at, Value &x) {
            if (at == bits) x = honest;
          },
          true));
    }
    // An integer at the bound.
    {
      auto w = v;
      w[9] = kQ;
      EXPECT_FALSE(prove_verify(t, *c, w, nullptr, true));
    }
    // A wrong decomposition of integer 2 in A: 2 at bit 0, 0 at bit 1.
    EXPECT_FALSE(prove_verify(
        t, *c, v,
        [&af, bits](size_t at, Value &x) {
          if (at != bits) return;
          auto &b = std::get<AV>(x);
          b.at(2 * kW + 0) = af.of_scalar(2);
          b.at(2 * kW + 1) = af.zero();
        },
        true));
  }
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
