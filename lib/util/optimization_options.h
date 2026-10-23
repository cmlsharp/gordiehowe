// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#ifndef PRIVACY_PROOFS_ZK_LIB_UTIL_OPTIMIZATION_OPTIONS_H_
#define PRIVACY_PROOFS_ZK_LIB_UTIL_OPTIMIZATION_OPTIONS_H_

namespace proofs {

// Implementation policy, not protocol parameters. These switches preserve
// the relation, transcript and proof format. Baseline callers stay opted out;
// add future optimizations here with an explicit false baseline default.
struct OptimizationOptions {
  bool unit_coefficients = false;
  bool subfield_encoding = false;
  bool native_ntt = false;

  static constexpr OptimizationOptions baseline() { return {}; }
  static constexpr OptimizationOptions optimized() {
    return {true, true, true};
  }

  constexpr const char* preset_name() const {
    if (!unit_coefficients && !subfield_encoding && !native_ntt)
      return "baseline";
    if (unit_coefficients && subfield_encoding && native_ntt)
      return "optimized";
    return "custom";
  }
};

}  // namespace proofs
#endif
