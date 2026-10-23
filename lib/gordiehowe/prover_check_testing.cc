// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe test binaries: the prover's self-checks
// (compiler/test_switches.h) on in each test, off in the DISABLED_ ones,
// the measurement tests. A gtest listener sets them as each test starts.
// The bench executables (examples/*_bench.cc) link no listener and run
// with the checks off.

#include <cstring>

#include "gordiehowe/compiler/test_switches.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::compiler {
namespace {

class Listener : public ::testing::EmptyTestEventListener {
  void OnTestStart(const ::testing::TestInfo &t) override {
    const bool disabled =
        std::strstr(t.test_suite_name(), "DISABLED_") != nullptr ||
        std::strstr(t.name(), "DISABLED_") != nullptr;
    test_switches().subfield_check = !disabled;
    test_switches().adjoint_check = !disabled;
  }
};

const bool kInstalled = [] {
  ::testing::UnitTest::GetInstance()->listeners().Append(new Listener);
  return true;
}();

}  // namespace
}  // namespace proofs::gordiehowe::compiler
