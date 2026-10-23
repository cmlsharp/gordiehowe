// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The age predicate (date_age.h): an adult's date verifies; a non-digit,
// a wrong separator, month 13, April 31 and a minor are rejected.

#include "gordiehowe/heldout/date_age.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::date_age {
namespace {

TEST(HeldoutDateAge, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance("1990-02-29", 2026, 10, 21, 18);
  auto witness = [](const std::string &b) {
    return instance(b, 2026, 10, 21, 18).witness;
  };
  // Born exactly 18 years before today: accepted.
  const Instance edge = instance("2008-10-21", 2026, 10, 21, 18);
  SecureRandomEngine rng;
  EXPECT_TRUE(rel.verify(edge.statement,
                         rel.prove(edge.statement, edge.witness, rng)));
  Statement<Value> older = in.statement;
  older.today[3] = 40;
  check_relation<GoldSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {{"non-digit", witness("19a0-02-28")},
       {"separator", witness("1990/02-28")},
       {"month 13", witness("1990-13-01")},
       {"month 0", witness("1990-00-10")},
       {"April 31", witness("1990-04-31")},
       {"day 0", witness("1990-04-00")},
       {"minor", witness("2008-10-22")},
       {"year 1899", witness("1899-01-01")}},
      {{"minimum age 40", older}}, "date-age");
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::date_age
