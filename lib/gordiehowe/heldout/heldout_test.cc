// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The held-out set's list (heldout_programs.h): configuration and Lean
// names are distinct, and every Lean name is a dotted path of Lean
// identifiers. The programs' own tests are in <program>_test.cc.

#include <cctype>
#include <set>
#include <string>

#include "gordiehowe/heldout/heldout_programs.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout {
namespace {

TEST(HeldoutPrograms, Names) {
  std::set<std::string> configs, leans;
  for (const auto &e : exports()) {
    EXPECT_TRUE(configs.insert(e.config).second) << e.config;
    EXPECT_TRUE(leans.insert(e.lean).second) << e.lean;
    bool start = true;
    for (char c : e.lean) {
      if (c == '.') {
        EXPECT_FALSE(start) << e.lean;
        start = true;
        continue;
      }
      EXPECT_TRUE(start ? std::isupper(c) : std::isalnum(c)) << e.lean;
      start = false;
    }
  }
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout
