// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: bits shared across two fields, with no hash.
//
// The witness is n pairs of 32-bit words (x, y); the statement is each
// pair's XOR and integer sum. Domain H (GF(2^128)) commits the words' bits
// and states x XOR y, which is addition in characteristic 2, and x AND y,
// one product per bit. Domain A (Goldilocks^2) receives the bits of x and
// y (x.to(A): a copy and a MAC equality) and the AND words as integers
// (assert_same_bits in its integer form, 32 bits per word), and states
// the sum two ways: as the integers of the copied bits, and as
// (x XOR y) + 2 (x AND y).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_BITS_ACROSS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_BITS_ACROSS_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::bits_across {

constexpr size_t kPairs = 8;

template <template <class> class F>
struct Statement {
  F<std::array<uint32_t, kPairs>> xor_words;
  F<std::array<uint64_t, kPairs>> sum;
};
template <template <class> class F>
struct Witness {
  F<std::array<uint32_t, kPairs>> x;
  F<std::array<uint32_t, kPairs>> y;
};

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("bits-across"),
      [](MixedSys &cs, Statement<In> st, Witness<In> w) {
        auto &H = cs.domain(binary_profile(), "H");
        auto &A = cs.domain(gold_profile(), "A");
        // Bit [n, 32] each.
        const auto xb = H.priv(Bit{}, w.x);
        const auto yb = H.priv(Bit{}, w.y);
        assert_equal(xb + yb, st.xor_words.bits(H), "xor");
        const auto andb = H.priv("and", xb * yb);
        // The words' bits in A, and their integer sum.
        const auto xa = xb.to(A, "x_in_a");
        const auto ya = yb.to(A, "y_in_a");
        const auto sum = st.sum.values(A);
        assert_equal(xa.from_digits(2) + ya.from_digits(2), sum, "sum_bits");
        // The AND words as integers in A, the same bits as H's.
        const auto and_words = A.priv(
            Subfield<>{}, "and_words", Shape{kPairs}, depends_on(xa, ya),
            [](const std::vector<uint64_t> &x, const std::vector<uint64_t> &y) {
              std::vector<uint64_t> out(kPairs, 0);
              for (size_t i = 0; i < kPairs; ++i)
                for (size_t b = 0; b < 32; ++b)
                  out[i] |= (x[32 * i + b] & y[32 * i + b]) << b;
              return out;
            });
        assert_same_bits(andb, and_words, BitWidth{32}, "and_same");
        assert_equal(st.xor_words.values(A) + 2 * and_words, sum,
                     "sum_xor_and");
      },
      "heldout-bits-across");
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
inline Instance instance(uint64_t seed) {
  std::mt19937_64 g(seed);
  Instance in;
  for (size_t i = 0; i < kPairs; ++i) {
    const uint32_t x = uint32_t(g()), y = uint32_t(g());
    in.witness.x[i] = x;
    in.witness.y[i] = y;
    in.statement.xor_words[i] = x ^ y;
    in.statement.sum[i] = uint64_t(x) + y;
  }
  return in;
}

}  // namespace proofs::gordiehowe::heldout::bits_across

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_BITS_ACROSS_H_
