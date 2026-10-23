// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Irregular index maps (index_maps.h): the honest sums verify; each wrong
// statement sum and a changed coordinate of x are rejected.

#include "gordiehowe/heldout/index_maps.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::index_maps {
namespace {

TEST(HeldoutIndexMaps, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance(19);
  std::vector<std::pair<std::string, Statement<Value>>> bad;
  const char *names[5] = {"mirror", "triangle", "overlap", "single",
                          "stride"};
  for (size_t k = 0; k < 5; ++k) {
    Statement<Value> s = in.statement;
    s.sums[k] += 1;
    bad.push_back({names[k], s});
  }
  Statement<Value> s = in.statement;
  s.columns[6] += 1;
  bad.push_back({"columns", s});
  Witness<Value> w = in.witness;
  w.x[63] ^= 1;
  check_relation<GoldSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {{"x", w}}, bad, "index-maps");
  const auto &typed = rel.typed<GoldSys>();
  const auto &c = typed.compiled();
  for (const char *nm : {"mirror.value", "overlap.value"})
    EXPECT_FALSE(proves(c, typed.statement(in.statement),
                        typed.witness(in.witness),
                        bump<GoldSys::Set>(fields().gf, node_named(c, nm), 3)))
        << nm;
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::index_maps
