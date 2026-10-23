// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: one MAC whose operand is shorter than its width.
//
// The witness is kWords 32-bit words; the statement is their integer
// values. Domain H (GF(2^128)) commits the words' bits; domain A
// (Goldilocks^2) receives them (x.to(A): a copy and a MAC equality) and
// states each word as the integer of its bits. The kWords * 32 bits are
// fewer than the MAC's width of 128, so the MAC reads the bits padded by
// zeros to its width, in one chunk.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MAC_PADDED_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MAC_PADDED_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::mac_padded {

constexpr size_t kWords = 3;

template <template <class> class F>
struct Statement {
  F<std::array<uint64_t, kWords>> words;
};
template <template <class> class F>
struct Witness {
  F<std::array<uint32_t, kWords>> x;
};

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("mac-padded"),
      [](MixedSys &cs, Statement<In> st, Witness<In> w) {
        auto &H = cs.domain(binary_profile(), "H");
        auto &A = cs.domain(gold_profile(), "A");
        // Bit [kWords, 32].
        const auto xb = H.priv(Bit{}, w.x);
        const auto xa = xb.to(A, "x_in_a");
        assert_equal(xa.from_digits(2), st.words.values(A), "words");
      },
      "heldout-mac-padded");
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
inline Instance instance(uint64_t seed) {
  std::mt19937_64 g(seed);
  Instance in;
  for (size_t i = 0; i < kWords; ++i) {
    const uint32_t x = uint32_t(g());
    in.witness.x[i] = x;
    in.statement.words[i] = x;
  }
  return in;
}

}  // namespace proofs::gordiehowe::heldout::mac_padded

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_MAC_PADDED_H_
