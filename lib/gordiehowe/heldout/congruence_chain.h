// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: a congruence chain modulo a small odd prime.
//
// The witness is a seed s in [0, 101); the statement is the last state of
// the linear congruential chain
//   x_0 = s,  x_{i+1} = 37 x_i + 11 (mod 101),  i < L,
// with L = 64. The prover commits the chain, each state range checked
// below 101 and each step one congruence modulo 101 (assert_mod) in
// Falcon's field F_q^9 (q = 12289), the only domain of the system: the
// modulus is neither the field's characteristic nor a power of two.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CONGRUENCE_CHAIN_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CONGRUENCE_CHAIN_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::congruence_chain {

constexpr uint64_t kM = 101;
constexpr uint64_t kA = 37;
constexpr uint64_t kC = 11;
constexpr size_t kSteps = 64;

template <template <class> class F>
struct Statement {
  F<std::array<uint8_t, 1>> last;
};
template <template <class> class F>
struct Witness {
  F<std::array<uint8_t, 1>> seed;
};

inline std::vector<uint64_t> chain(uint64_t s) {
  std::vector<uint64_t> x = {s};
  for (size_t i = 0; i < kSteps; ++i) x.push_back((kA * x.back() + kC) % kM);
  return x;
}

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("congruence-chain"),
      [](SmallSys &cs, Statement<In> st, Witness<In> w) {
        auto &A = cs.domain(small_profile(), "A");
        const auto seed = A.priv(Subfield<>{}, w.seed);
        const auto x = A.priv(Subfield<>{}, "chain", Shape{kSteps + 1},
                              depends_on(seed),
                              [](const std::vector<uint64_t> &s) {
                                return chain(s[0] % kM);
                              });
        assert_equal(x.slice(0, 1), seed, "seed");
        assert_range(x, kM, "states");
        const auto c = A.constant(
            "increment",
            std::vector<QF::Elt>(kSteps, A.field().of_scalar(kC)));
        assert_mod(x.slice(1, kSteps + 1), kA * x.slice(0, kSteps) + c, kM,
                   "step");
        assert_equal(x.slice(kSteps, kSteps + 1), st.last.values(A), "last");
      },
      "heldout-congruence-chain");
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
inline Instance instance(uint64_t s) {
  Instance in;
  in.witness.seed[0] = uint8_t(s % kM);
  in.statement.last[0] = uint8_t(chain(s % kM).back());
  return in;
}

}  // namespace proofs::gordiehowe::heldout::congruence_chain

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CONGRUENCE_CHAIN_H_
