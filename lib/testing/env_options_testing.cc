// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Linked into every test binary (proofs_add_testing_libraries):
// applies the environment's options (env_options_testing.h) before main.

#include "testing/env_options_testing.h"

namespace proofs::testing_env {
namespace {

const bool kApplied = [] {
  diagnostics::set(diagnostics_from_env());
  gordiehowe::set_prove_seam_defaults(prove_seams_from_env());
  return true;
}();

}  // namespace
}  // namespace proofs::testing_env
