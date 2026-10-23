// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// GordieHowe: test-only switches that never change a proof. The prover's
// self-checks check values the proof does not depend on (a witness that
// fails one gives a proof the verifier rejects); the path switches choose
// between two computations of the same value, so that a test can compare
// the proofs of the two. The GordieHowe tests turn the self-checks on in
// every test but the DISABLED_ ones, the measurement tests
// (prover_check_testing.cc); the bench executables leave them off.
//
// Compiled in only with GORDIEHOWE_TEST_SWITCHES=1, which this repository's
// test build defines. Without it, test_switches() is a constant at the
// defaults below and every guarded path compiles away.
//
//   subfield_check  commit_compute checks that every value packed into a
//                   word of a subfield lies in that subfield (tree_zk.h)
//   adjoint_check   BitViewMap::adjoint runs every instance both ways, by
//                   its template's lane-program steps and by its folded
//                   products, and checks that the two give the same blocks,
//                   element for element (view_map.h)
//   adjoint_path    BitViewMap::adjoint takes one way for every template
//                   in place of the cheaper one per template
//   stage_opts_off  turns the packing stages' optimizations off (bits of
//                   StageOpt): each computes the same data as the code it
//                   replaces
//   full_rows       the batches' provers run over all 2^logs rows, the zero
//                   padding included, in place of their live rows
//                   (field_skip.h)
//   bit_phase_bridge  the bit phase's output claim reaches the bit stage as
//                   its 16 materialized Frobenius forms, in place of its
//                   product form (batch.h); the same rows and proof
// The op counts (op_counts.h) read none of them.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TEST_SWITCHES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TEST_SWITCHES_H_

#include <cstdint>

#ifndef GORDIEHOWE_TEST_SWITCHES
#define GORDIEHOWE_TEST_SWITCHES 0
#endif

namespace proofs::gordiehowe::compiler {

// The way BitViewMap::adjoint takes: per template, the one of fewer
// products (kChosen, the default), or for every template its lane-program
// steps (kSteps) or its folded products (kFolded).
enum class AdjointPath { kChosen, kSteps, kFolded };

// The packing stages' optimizations (tree_zk.h, stage.h):
//   kCheck  the prover's subfield check skips intermediate nodes, whose
//           regions hold only packed words (in their subfield by
//           construction)
//   kPack   words over the prime subfield of an odd field pack by scalar
//           multiplications
//   kTwist  characteristic-2 stages apply phi^-k from per-stage byte tables
//   kUnit   a stage with one routed row adds its terms without multiplying
//           them by its weight, one
//   kParts  a stage's measurement rows point into its stored forms (one
//           part each) in place of copying them into (position, value)
//           terms
enum class StageOpt : uint32_t {
  kCheck = 2,
  kPack = 4,
  kTwist = 8,
  kUnit = 16,
  kParts = 32
};

struct TestSwitches {
  bool subfield_check = false;
  bool adjoint_check = false;
  AdjointPath adjoint_path = AdjointPath::kChosen;
  uint32_t stage_opts_off = 0;
  bool full_rows = false;
  bool bit_phase_bridge = false;
  constexpr bool stage_opt_on(StageOpt o) const {
    return (stage_opts_off & uint32_t(o)) == 0;
  }
};

#if GORDIEHOWE_TEST_SWITCHES
// The switches in effect; a test sets them between proofs
// (single-threaded).
inline TestSwitches &test_switches() {
  static TestSwitches s;
  return s;
}
#else
inline constexpr TestSwitches kTestSwitchDefaults{};
inline constexpr const TestSwitches &test_switches() {
  return kTestSwitchDefaults;
}
#endif

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TEST_SWITCHES_H_
