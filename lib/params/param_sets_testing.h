// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Typed gtest suites over the field profiles: correctness tests instantiate
// every profile of AllProfiles, named by its kId. And the profile a
// measurement test runs, from the environment: PQ_FIELD_PROFILE names a
// profile's kId; unset selects the first. The bench executables take it as
// --profile (bench/cli.h).
#ifndef PRIVACY_PROOFS_ZK_LIB_PARAMS_PARAM_SETS_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_PARAMS_PARAM_SETS_TESTING_H_
#include <cstdlib>
#include <string>
#include <string_view>
#include <utility>

#include "params/param_sets.h"
#include "gtest/gtest.h"

namespace proofs::param_sets {
template <class L> struct GtestTypes;
template <class... Ps> struct GtestTypes<ProfileList<Ps...>> {
  using type = ::testing::Types<Ps...>;
};
// Every profile of AllProfiles, as gtest types.
using Profiles = GtestTypes<AllProfiles>::type;
// Names each instance by the profile's kId.
struct ProfileName {
  template <class P> static std::string GetName(int) { return P::kId; }
};

// with_profile(id, fn) at the profile PQ_FIELD_PROFILE names.
template <class Fn> decltype(auto) with_profile(Fn &&fn) {
  const char *id = std::getenv("PQ_FIELD_PROFILE");
  return with_profile(id == nullptr ? std::string_view() : std::string_view(id),
                      std::forward<Fn>(fn));
}
}  // namespace proofs::param_sets

#endif  // PRIVACY_PROOFS_ZK_LIB_PARAMS_PARAM_SETS_TESTING_H_
