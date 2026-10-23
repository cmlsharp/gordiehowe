// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The congruence chain modulo 101 (congruence_chain.h): honest seeds
// verify; a seed of 101 and a wrong last state are rejected, and so is a
// chain whose state is off by 101.

#include "gordiehowe/heldout/congruence_chain.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::congruence_chain {
namespace {

TEST(HeldoutCongruenceChain, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance(42);
  const Instance zero = instance(0);
  SecureRandomEngine rng;
  EXPECT_TRUE(rel.verify(zero.statement,
                         rel.prove(zero.statement, zero.witness, rng)));
  Witness<Value> big = in.witness;
  big.seed[0] = uint8_t(kM + 42);
  Statement<Value> s = in.statement;
  s.last[0] = uint8_t((s.last[0] + 1) % kM);
  check_relation<SmallSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {{"seed + 101", big}}, {{"last", s}}, "congruence-chain");
  const auto &typed = rel.typed<SmallSys>();
  const auto &c = typed.compiled();
  EXPECT_FALSE(proves(c, typed.statement(in.statement),
                      typed.witness(in.witness),
                      bump<SmallSys::Set>(fields().qf, node_named(c, "chain"),
                                          30)));
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::congruence_chain
