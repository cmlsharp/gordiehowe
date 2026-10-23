// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Offline memory checking (memory_check.h): an honest trace verifies; a
// read that returns another value, an address past the memory, a write
// flag of 2, a wrong final memory and a tampered old time are rejected.

#include "gordiehowe/heldout/memory_check.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::memory_check {
namespace {

TEST(HeldoutMemoryCheck, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance(11);
  size_t read = 0;
  while (in.witness.is_write[read] != 0) ++read;
  Witness<Value> wrong_read = in.witness;
  wrong_read.value[read] ^= 1;
  Witness<Value> far = in.witness;
  far.addr[0] = uint8_t(kM);
  Witness<Value> flag = in.witness;
  flag.is_write[1] = 2;
  Statement<Value> s = in.statement;
  s.final_memory[2] ^= 4;
  check_relation<GoldSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {{"read value", wrong_read}, {"address", far}, {"write flag", flag}},
      {{"final memory", s}}, "memory-check");
  const auto &typed = rel.typed<GoldSys>();
  const auto &c = typed.compiled();
  EXPECT_FALSE(proves(c, typed.statement(in.statement),
                      typed.witness(in.witness),
                      bump<GoldSys::Set>(fields().gf,
                                         node_named(c, "old_time"), 9)));
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::memory_check
