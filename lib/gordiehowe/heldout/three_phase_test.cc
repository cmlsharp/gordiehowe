// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Three challenge phases (three_phase.h): r1, r2 and r3 lie in phases 1,
// 2 and 3; a permutation of Y's rows verifies; a table with a changed row
// and tampered compressions and prefix products are rejected.

#include "gordiehowe/heldout/three_phase.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::three_phase {
namespace {

TEST(HeldoutThreePhase, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance(13);
  const auto &typed = rel.typed<GoldSys>();
  const auto &c = typed.compiled();
  EXPECT_EQ(c.phase(node_named(c, "r1")), 1u);
  EXPECT_EQ(c.phase(node_named(c, "r2")), 2u);
  EXPECT_EQ(c.phase(node_named(c, "r3")), 3u);
  EXPECT_EQ(c.phases(), 3u);
  Witness<Value> w = in.witness;
  w.x[4][2] ^= 1;
  Statement<Value> s = in.statement;
  s.y[0][0] += 1;
  check_relation<GoldSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {{"row", w}}, {{"statement row", s}}, "three-phase");
  for (const char *nm : {"compressed", "prefix"})
    EXPECT_FALSE(proves(c, typed.statement(in.statement),
                        typed.witness(in.witness),
                        bump<GoldSys::Set>(fields().gf, node_named(c, nm), 5)))
        << nm;
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::three_phase
