// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Merkle path (merkle_sha256.h) at depths 1, 4 and 32: honest paths
// verify; a wrong sibling, a wrong leaf, an index past 2^depth and a wrong
// root are rejected.

#include "gordiehowe/heldout/merkle_sha256.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::merkle {
namespace {

void check_depth(size_t depth) {
  const auto rel = relation(depth);
  const Instance in = instance(depth, 100 + depth);
  std::vector<std::pair<std::string, Witness<Value>>> bad;
  Witness<Value> w = in.witness;
  w.siblings[depth - 1][3] ^= 1;
  bad.push_back({"sibling", w});
  w = in.witness;
  w.leaf[0] ^= 0x80;
  bad.push_back({"leaf", w});
  if (depth < 32) {
    w = in.witness;
    w.index |= uint32_t(1) << depth;
    bad.push_back({"index past 2^depth", w});
  }
  Statement<Value> s = in.statement;
  s.root[31] ^= 1;
  check_relation<BinarySys>(rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
                            bad, {{"root", s}},
                            "merkle-" + std::to_string(depth));
}

TEST(HeldoutMerkle, Depth1) { check_depth(1); }
TEST(HeldoutMerkle, Depth4) { check_depth(4); }
TEST(HeldoutMerkle, Depth32) { check_depth(32); }

}  // namespace
}  // namespace proofs::gordiehowe::heldout::merkle
