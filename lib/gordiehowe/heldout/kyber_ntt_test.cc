// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Kyber's NTT modulo 3329 (kyber_ntt.h): the host transform against the
// schoolbook evaluation at the NTT's roots, and the relation: an honest
// transform verifies; a coefficient at q, a wrong output and a tampered
// middle layer are rejected.

#include "gordiehowe/heldout/kyber_ntt.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::kyber_ntt {
namespace {

uint64_t pow_mod(uint64_t b, uint64_t e) {
  uint64_t r = 1;
  for (; e; e >>= 1, b = b * b % kQ)
    if (e & 1) r = r * b % kQ;
  return r;
}

// Output pair (2i, 2i + 1) is the residue of a mod X^2 - zeta^(2 brv7(i)
// + 1) (FIPS 203): a_even + a_odd X evaluated through the two-term
// residue.
TEST(HeldoutKyberNtt, HostMatchesResidues) {
  const Instance in = instance(5);
  std::vector<uint64_t> a(in.witness.poly.begin(), in.witness.poly.end());
  const auto t = ntt(a);
  for (size_t i = 0; i < 128; ++i) {
    size_t r = 0;
    for (size_t b = 0; b < 7; ++b) r |= ((i >> b) & 1) << (6 - b);
    const uint64_t g = pow_mod(17, 2 * r + 1);
    uint64_t e = 0, o = 0;
    for (size_t j = 0; j < 128; ++j) {
      e = (e + a[2 * j] * pow_mod(g, j)) % kQ;
      o = (o + a[2 * j + 1] * pow_mod(g, j)) % kQ;
    }
    EXPECT_EQ(t[2 * i], e) << i;
    EXPECT_EQ(t[2 * i + 1], o) << i;
  }
}

TEST(HeldoutKyberNtt, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance(7);
  Witness<Value> at_q = in.witness;
  at_q.poly[17] = uint16_t(kQ);
  Witness<Value> plus_q = in.witness;
  plus_q.poly[3] = uint16_t(plus_q.poly[3] + kQ);
  Statement<Value> s = in.statement;
  s.ntt[100] = uint16_t((s.ntt[100] + 1) % kQ);
  check_relation<GoldSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {{"coefficient q", at_q}, {"coefficient + q", plus_q}},
      {{"output", s}}, "kyber-ntt");
  // A middle layer's output off by one.
  const auto &typed = rel.typed<GoldSys>();
  const auto &c = typed.compiled();
  const size_t layer3 = node_named(c, "layer3.out");
  EXPECT_FALSE(proves(c, typed.statement(in.statement),
                      typed.witness(in.witness),
                      bump<GoldSys::Set>(fields().gf, layer3, 40)));
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::kyber_ntt
