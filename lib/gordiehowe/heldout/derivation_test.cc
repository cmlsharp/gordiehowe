// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The derivations the lowerings record (compiler/derivation.h), on held-out
// programs: every predicate of the congruence chain, the date predicate,
// the minimal tables and the bits across fields has a derivation that the
// C++ check (compiler/derivation_check.h) accepts; and the check refuses
// tampered ones: a wrong linear coefficient, a missing conclusion, a
// citation of a predicate of no lower rank, a lookup of another needle's
// members, an interval claimed too narrow.
//
// The cross-test with the Lean checker (MutantsForLean): every listed
// derivation of the programs, and per step its variants (a premise moved,
// a coefficient or bound changed, the derivation cut before it), with the
// C++ check's verdict on each. With GH_DERIV_MUTANTS_DIR set, each
// program's export goes under it with a module Mutants.lean holding the
// variants and the verdicts (`mutants`, `expected`), which
// heldout/derivation_mutants.sh checks with the Lean checker.

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/derivation_check.h"
#include "gordiehowe/compiler/program_builder.h"
#include "gordiehowe/compiler/program_printer.h"
#include "gordiehowe/heldout/heldout_env.h"
#include "gordiehowe/heldout/bits_across.h"
#include "gordiehowe/heldout/congruence_chain.h"
#include "gordiehowe/heldout/date_age.h"
#include "gordiehowe/heldout/degenerate.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::heldout {
namespace {

// The program and certificates of REL's system SYS.
template <class Sys, class R>
std::pair<ir::Program, ir::Certificates> built(const R &rel) {
  ir::Certificates c;
  ir::Program p = compiler::build_ir(rel.template typed<Sys>().compiled(), c);
  return {std::move(p), std::move(c)};
}

void expect_all_derived(const ir::Program &p, const ir::Certificates &c,
                        const std::string &what) {
  ASSERT_EQ(c.derivations.size(), p.predicates.size()) << what;
  for (size_t i = 0; i < p.predicates.size(); ++i) {
    EXPECT_EQ(c.deriv_gaps.at(i), "") << what << ": " << p.predicates[i].name;
    EXPECT_FALSE(c.derivations[i].empty()) << what << ": " << p.predicates[i].name;
  }
}

// The id of the predicate NAME.
size_t pred_named(const ir::Program &p, const std::string &name) {
  for (size_t i = 0; i < p.predicates.size(); ++i)
    if (p.predicates[i].name == name) return i;
  ADD_FAILURE() << "no predicate " << name;
  return 0;
}

TEST(HeldoutDerivations, EveryPredicateDerived) {
  {
    const auto [p, c] = built<SmallSys>(congruence_chain::relation());
    expect_all_derived(p, c, "congruence-chain");
  }
  {
    const auto [p, c] = built<GoldSys>(date_age::relation());
    expect_all_derived(p, c, "date-age");
  }
  {
    const auto [p, c] = built<GoldSys>(degenerate::minimal_tables());
    expect_all_derived(p, c, "minimal-tables");
  }
  {
    const auto [p, c] = built<MixedSys>(bits_across::relation());
    expect_all_derived(p, c, "bits-across");
  }
}

TEST(HeldoutDerivations, TamperedRefused) {
  auto [p, c0] = built<SmallSys>(congruence_chain::relation());
  const size_t step = pred_named(p, "step");
  const size_t states = pred_named(p, "states");
  auto refused = [&](ir::Certificates c, size_t pid) {
    compiler::DerivChecker check(p, c);
    return !check.check(pid).empty();
  };
  ASSERT_FALSE(refused(c0, step));
  ASSERT_FALSE(refused(c0, states));
  // A wrong coefficient of the quotient's definition.
  {
    ir::Certificates c = c0;
    bool done = false;
    for (auto &s : c.derivations[step])
      if (s.rule == ir::DStep::kLinear && !s.coeffs.empty() && !done) {
        s.coeffs[0] = "-100";
        done = true;
      }
    ASSERT_TRUE(done);
    EXPECT_TRUE(refused(c, step));
  }
  // No conclusion.
  {
    ir::Certificates c = c0;
    c.derivations[step].pop_back();
    EXPECT_TRUE(refused(c, step));
  }
  // A citation of a predicate of no lower rank.
  {
    ir::Certificates c = c0;
    c.deriv_ranks[states] = c.deriv_ranks[step];
    EXPECT_TRUE(refused(c, step));
  }
  // Another needle's members.
  {
    ir::Certificates c = c0;
    auto &s = c.derivations[states].at(0);
    ASSERT_EQ(s.rule, ir::DStep::kLookup);
    s.members[0][2] += 1;
    EXPECT_TRUE(refused(c, states));
  }
  // The difference's interval claimed too narrow.
  {
    ir::Certificates c = c0;
    bool done = false;
    for (auto &s : c.derivations[step])
      if (s.rule == ir::DStep::kIvlExpr && !done) {
        s.ints[1] = "0";
        done = true;
      }
    ASSERT_TRUE(done);
    EXPECT_TRUE(refused(c, step));
  }
}


// The variants of the derivations of C: per listed derivation and step, a
// premise moved, a coefficient raised, the upper bound lowered, and the
// derivation cut before the step; with the C++ verdicts.
std::pair<std::vector<std::pair<size_t, std::vector<ir::DStep>>>, std::vector<bool>>
mutants(const ir::Program &p, const ir::Certificates &c0) {
  std::vector<std::pair<size_t, std::vector<ir::DStep>>> out;
  std::vector<bool> ok;
  auto add = [&](size_t pid, std::vector<ir::DStep> st) {
    ir::Certificates c = c0;
    c.derivations[pid] = st;
    compiler::DerivChecker check(p, c);
    ok.push_back(check.check(pid).empty());
    out.push_back({pid, std::move(st)});
  };
  for (size_t pid = 0; pid < c0.derivations.size(); ++pid) {
    const auto &d = c0.derivations[pid];
    if (d.empty() || (d.size() == 2 && d[0].rule == ir::DStep::kRealized)) continue;
    add(pid, d);
    for (size_t j = 0; j < d.size(); ++j) {
      if (!d[j].premises.empty() && d[j].premises[0] > 0) {
        auto m = d;
        m[j].premises[0] -= 1;
        add(pid, std::move(m));
      }
      if (!d[j].coeffs.empty()) {
        auto m = d;
        m[j].coeffs[0] = (WideInt(std::stoll(m[j].coeffs[0])) + WideInt(1)).str();
        add(pid, std::move(m));
      }
      if (d[j].ints.size() >= 2) {
        auto m = d;
        m[j].ints[1] = (compiler::derivation_check_internal::parse_int(m[j].ints[1]) -
                        WideInt(1)).str();
        add(pid, std::move(m));
      }
      if (j > 0) add(pid, std::vector<ir::DStep>(d.begin(), d.begin() + long(j)));
    }
  }
  return {out, ok};
}

template <class Sys, class R>
void mutants_for(const R &rel, const std::string &config, const std::string &lean) {
  const auto &c = rel.template typed<Sys>().compiled();
  ir::Certificates certs;
  const ir::Program p = compiler::build_ir(c, certs);
  const auto [ms, ok] = mutants(p, certs);
  size_t accepted = 0;
  for (bool b : ok) accepted += b;
  EXPECT_GT(ms.size(), 0u) << config;
  // Each original derivation is accepted.
  const char *dir = std::getenv("GH_DERIV_MUTANTS_DIR");
  std::printf("GH_DERIV_MUTANTS config=%s variants=%zu accepted=%zu\n", config.c_str(),
              ms.size(), accepted);
  if (dir == nullptr) return;
  export_program(c, dir, config, lean, "mutants");
  const std::string ns = "GordieHowe.Generated.Heldout." + lean + "." +
                         compiler::lean_param_set(P::kId);
  std::string t = "namespace " + ns + ".Mutants\nopen GordieHowe.RealizedProgram " + ns +
                  ".Program\n\n" + compiler::print_derivations(p, certs, &ms) +
                  "\ndef expected : List Bool :=\n  [";
  for (size_t i = 0; i < ok.size(); ++i) t += std::string(i ? ", " : "") + (ok[i] ? "true" : "false");
  t += "]\n\nend " + ns + ".Mutants\n";
  const auto path = std::filesystem::path(dir) / "GordieHowe/Generated/Heldout" / lean /
                    compiler::lean_param_set(P::kId) / "Mutants.lean";
  std::ofstream(path) << t;
}

TEST(HeldoutDerivations, MutantsForLean) {
  mutants_for<SmallSys>(congruence_chain::relation(), "congruence-chain", "CongruenceChain");
  mutants_for<GoldSys>(date_age::relation(), "date-age", "DateAge");
  mutants_for<GoldSys>(degenerate::minimal_tables(), "minimal-tables", "MinimalTables");
  mutants_for<MixedSys>(bits_across::relation(), "bits-across", "BitsAcross");
}

}  // namespace
}  // namespace proofs::gordiehowe::heldout
