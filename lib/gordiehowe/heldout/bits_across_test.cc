// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Bits across fields (bits_across.h): honest words verify; a wrong XOR, a
// wrong sum and tampered copies of the bits in A are rejected.

#include "gordiehowe/heldout/bits_across.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::bits_across {
namespace {

TEST(HeldoutBitsAcross, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance(17);
  Statement<Value> wrong_xor = in.statement;
  wrong_xor.xor_words[3] ^= 0x100;
  Statement<Value> wrong_sum = in.statement;
  wrong_sum.sum[5] += 1;
  Witness<Value> w = in.witness;
  w.y[2] ^= 1;
  check_relation<MixedSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {{"word", w}}, {{"xor", wrong_xor}, {"sum", wrong_sum}},
      "bits-across");
  const auto &typed = rel.typed<MixedSys>();
  const auto &c = typed.compiled();
  for (const char *nm : {"x_in_a", "and_words"})
    EXPECT_FALSE(proves(c, typed.statement(in.statement),
                        typed.witness(in.witness),
                        bump<MixedSys::Set>(fields().gf, node_named(c, nm), 7)))
        << nm;
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::bits_across
