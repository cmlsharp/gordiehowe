// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// GordieHowe: the defaults of the proof options' test seams
// (BasicProveOptions in system.h). A seam changes how a proof is made, never
// whether it verifies; each is off unless a driver turns it on. A driver that
// cannot reach every ProveOptions of a process (the test and bench binaries'
// environment, testing/env_options_testing.cc) sets the defaults once,
// before the first proof; any other caller sets the option itself.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TEST_SEAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TEST_SEAMS_H_

#include <cstdint>
#include <optional>

namespace proofs::gordiehowe {

struct ProveSeams {
  // Fixed-seed proofs, for byte-identity checks between builds: the proof
  // draws its randomness from std::mt19937_64 seeded with the value,
  // restarted per proof, in place of the caller's engine, and prints
  //   GH_PROOF_DIGEST <SHA-256 of the proof, hex> bytes=<size>
  // Draws come in one order only single-threaded or with SERIAL_COMMITMENTS.
  std::optional<uint64_t> fixed_seed;
  // The commitments' computations in domain order on the calling thread,
  // even in multi-threaded mode. The proof does not change.
  bool serial_commitments = false;
};

namespace internal {
inline ProveSeams &mutable_prove_seam_defaults() {
  static ProveSeams s;
  return s;
}
}  // namespace internal

// The defaults of every BasicProveOptions made after the call.
inline const ProveSeams &prove_seam_defaults() {
  return internal::mutable_prove_seam_defaults();
}
inline void set_prove_seam_defaults(const ProveSeams &s) {
  internal::mutable_prove_seam_defaults() = s;
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TEST_SEAMS_H_
