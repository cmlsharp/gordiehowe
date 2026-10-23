// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The toy credential (credential.h): an adult's credential from a listed
// country verifies; a minor, a country off the list, a wrong preimage, a
// changed name (another digest, so other key digests) and another key are
// rejected.

#include "gordiehowe/heldout/credential.h"

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout::credential {
namespace {

TEST(HeldoutCredential, HonestAndBad) {
  const auto rel = relation();
  const Instance in = instance(31, 1990, 2026, 2);
  // The same key (seed) with another birth year or country: the attributes
  // change, so does the digest, and the preimages follow it.
  const Instance minor = instance(31, 2010, 2026, 2);
  Witness<Value> off_list = in.witness;
  off_list.attrs[18] = 'F';
  off_list.attrs[19] = 'R';
  Witness<Value> preimage = in.witness;
  preimage.preimages[5][0] ^= 1;
  Witness<Value> name = in.witness;
  name.attrs[0] ^= 1;
  const Instance other = instance(37, 1990, 2026, 2);
  check_relation<MixedSys>(
      rel, Case<Statement<Value>, Witness<Value>>{in.statement, in.witness},
      {{"minor", minor.witness},
       {"country", off_list},
       {"preimage", preimage},
       {"name", name}},
      {{"other key", other.statement}}, "credential");
  // A minor's own honest instance fails the age check.
  const auto &typed = rel.typed<MixedSys>();
  EXPECT_FALSE(proves(typed.compiled(), typed.statement(minor.statement),
                      typed.witness(minor.witness), nullptr, true));
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout::credential
