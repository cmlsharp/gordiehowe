// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The degenerate programs (degenerate.h): one predicate in one binary
// domain, and the smallest lookup tables in one odd domain.

#include "gordiehowe/heldout/degenerate.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::degenerate {
namespace {

TEST(HeldoutDegenerate, SinglePredicate) {
  const auto rel = single_predicate();
  using St = SingleStatement<Value>;
  using W = SingleWitness<Value>;
  const W w{{true}, {true}};
  check_relation<BinarySys>(rel, Case<St, W>{St{{true}}, w},
                            {{"a = 0", W{{false}, {true}}}},
                            {{"z = 0", St{{false}}}}, "single-predicate");
  SecureRandomEngine rng;
  const St zero{{false}};
  const W w01{{false}, {true}};
  EXPECT_TRUE(rel.verify(zero, rel.prove(zero, w01, rng)));
}

TEST(HeldoutDegenerate, MinimalTables) {
  const auto rel = minimal_tables();
  using St = TableStatement<Value>;
  using W = TableWitness<Value>;
  const W w{{7}, {3, 9, 9}, {1, 2}, {1}};
  check_relation<GoldSys>(
      rel, Case<St, W>{St{{22}}, w},
      {{"seven", W{{6}, {3, 9, 9}, {1, 2}, {1}}},
       {"pick", W{{7}, {3, 9, 8}, {1, 2}, {0}}},
       {"pair", W{{7}, {3, 9, 9}, {2, 1}, {1}}},
       {"bit", W{{7}, {3, 3, 9}, {1, 2}, {7}}}},
      {{"total", St{{23}}}}, "minimal-tables");
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::degenerate
