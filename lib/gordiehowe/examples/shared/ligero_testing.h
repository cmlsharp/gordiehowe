// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: test support for the Ligero parameters the compiler chooses
// from a domain profile's target (compiler/ligero_choice.h,
// domain_profile.h):
//   expect_ligero_target  every domain of a compiled system at list radius
//                         at the target, every round at least s bits

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_LIGERO_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_LIGERO_TESTING_H_

#include <cstddef>

#include "gordiehowe/domain.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples {

// Every domain of the compiled system C runs list-radius Ligero at P's
// target 2^-s, or, at a fallback (the domain's own rounds besides Ligero's
// exceed P's classical target), at the largest of those rounds,
// target_num/|K|: the commit, test and column rounds are each at most
// 2^-s, the blinding width is the opened columns, and split masks have
// 2t <= k.
template <class P, class C>
void expect_ligero_target(const C &c) {
  for (size_t d = 0; d < c.num_domains(); ++d) {
    const DomainPlan p = c.compiled_domain(d).plan();
    const std::string name = c.domain(d).name;
    const double profile = compiler::target_bits(ligero_target<P>());
    const double s = p.target_fallback ? p.target : profile;
    EXPECT_EQ(p.target, s) << name;
    if (p.target_fallback) {
      EXPECT_EQ(ligero_target<P>(), compiler::LigeroTarget::kClassical)
          << name;
      EXPECT_LT(p.target, profile) << name;
      EXPECT_NE(p.target_num, 0u) << name;
    }
    EXPECT_TRUE(p.list_radius) << name;
    // The rounds meet the target exactly; their bits are rounded doubles.
    EXPECT_GE(p.commit_bits, s - 1e-9) << name;
    EXPECT_GE(p.test_bits, s - 1e-9) << name;
    EXPECT_GE(p.column_bits, s - 1e-9) << name;
    EXPECT_EQ(p.r, p.t) << name;
    EXPECT_GE(p.agreement, p.k) << name;
    EXPECT_LE(p.agreement, p.N) << name;
    if (p.split) EXPECT_LE(2 * p.t, p.k) << name;
  }
}

}  // namespace proofs::gordiehowe::examples

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_LIGERO_TESTING_H_
