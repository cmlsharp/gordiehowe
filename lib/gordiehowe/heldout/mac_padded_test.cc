// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// A MAC on fewer bits than its width (mac_padded.h): honest words verify; a
// wrong word and a tampered copy of the bits in A are rejected.

#include "gordiehowe/heldout/mac_padded.h"

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::mac_padded {
namespace {

TEST(HeldoutMacPadded, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance(23);
  Statement<Value> wrong = in.statement;
  wrong.words[1] += 1;
  check_relation<MixedSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {}, {{"word", wrong}}, "mac-padded");
  const auto &typed = rel.typed<MixedSys>();
  const auto &c = typed.compiled();
  EXPECT_FALSE(proves(c, typed.statement(in.statement),
                      typed.witness(in.witness),
                      bump<MixedSys::Set>(fields().gf, node_named(c, "x_in_a"),
                                          7)));
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::mac_padded
