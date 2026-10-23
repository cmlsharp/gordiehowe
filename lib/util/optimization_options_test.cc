// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#include "util/optimization_options.h"
#include "gtest/gtest.h"

namespace proofs {
TEST(OptimizationOptions, BaselineIsExplicitlyUnoptimized) {
  constexpr auto options = OptimizationOptions::baseline();
  static_assert(!options.unit_coefficients && !options.subfield_encoding &&
                !options.native_ntt);
  EXPECT_STREQ(options.preset_name(), "baseline");
  EXPECT_STREQ(OptimizationOptions{}.preset_name(), "baseline");
}
TEST(OptimizationOptions, OptimizedAndIndividualOverrides) {
  auto options = OptimizationOptions::optimized();
  EXPECT_TRUE(options.unit_coefficients);
  EXPECT_TRUE(options.subfield_encoding);
  EXPECT_TRUE(options.native_ntt);
  EXPECT_STREQ(options.preset_name(), "optimized");
  options.native_ntt = false;
  EXPECT_STREQ(options.preset_name(), "custom");
  EXPECT_TRUE(options.unit_coefficients);
  EXPECT_TRUE(options.subfield_encoding);
}
}  // namespace proofs
