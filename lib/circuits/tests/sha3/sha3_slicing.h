// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: a comment on why the slicing period is 6

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_TESTS_SHA3_SHA3_SLICING_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_TESTS_SHA3_SHA3_SLICING_H_

#include <cstddef>

// slicing parameters for sha/shake3
namespace proofs {
static inline bool sha3_slice_at(size_t round) {
  // Commit the Keccak state every 6 rounds.  With H's committed bits packed
  // 16 per GF(2^16) element, a checkpoint is cheap, and each one removes
  // recomputed rounds from the circuit; H's depth does not change at any
  // period up to 8.  Period 6 gives the smallest proofs in both schemes.
  constexpr size_t period = 6;
  // We always slice at the final round 23.  In
  // addition, we may slice at other rounds as well.
  return (round == 23) || ((round % period) == (period - 1));
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_TESTS_SHA3_SHA3_SLICING_H_
