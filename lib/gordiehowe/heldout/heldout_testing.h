// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe held-out programs: the checks every program's test runs.
//
// check_program(rel, honest, bad_witnesses, bad_statements, config) proves
// and verifies the honest instance, refuses every bad witness (a cheating
// prover, the honest prover's check off) and every bad statement (proved
// with the honest witness), and builds the realized program of the plan
// export, checking its structure (examples::check_program).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_TESTING_H_

#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout {

template <class St, class W>
struct Case {
  St statement;
  W witness;
};

// The honest proof verifies; each bad witness (against the honest
// statement) and each bad statement (with the honest witness) is
// rejected; the plan export's realized program is well formed.
template <class Sys, class Rel, class St, class W>
void check_relation(const Rel &rel, const Case<St, W> &honest,
                    const std::vector<std::pair<std::string, W>> &bad_witnesses,
                    const std::vector<std::pair<std::string, St>> &bad_statements,
                    const std::string &config, bool exports = true) {
  SecureRandomEngine rng;
  const auto proof = rel.prove(honest.statement, honest.witness, rng);
  EXPECT_TRUE(rel.verify(honest.statement, proof)) << config;
  const auto &typed = rel.template typed<Sys>();
  const auto &c = typed.compiled();
  const auto st = typed.statement(honest.statement);
  for (const auto &[what, w] : bad_witnesses)
    EXPECT_FALSE(proves(c, st, typed.witness(w), nullptr, true))
        << config << ": " << what;
  const auto w = typed.witness(honest.witness);
  for (const auto &[what, s] : bad_statements) {
    EXPECT_FALSE(proves(c, typed.statement(s), w, nullptr, true))
        << config << ": " << what;
    EXPECT_FALSE(rel.verify(s, proof)) << config << ": " << what;
  }
  if (exports) examples::check_program(program_of(c, config));
}

}  // namespace proofs::gordiehowe::heldout

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_TESTING_H_
