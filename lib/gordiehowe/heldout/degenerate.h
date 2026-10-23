// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out programs: degenerate cases.
//
// single_predicate: one domain (GF(2^128)), two private bits a and b, a
// public bit z and one predicate, a b = z (with the core's two Boolean
// checks).
//
// minimal_tables: one domain (Goldilocks^2), lookups into the smallest
// tables: a value in the table of one row {7}, three values in the table
// of two rows {3, 9}, a pair in a table of one row of arity 2 {(1, 2)},
// and a range check below 2 (the table [0, 2)). The statement is the sum
// of the three values, so the program has one predicate beside its
// lookups.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_DEGENERATE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_DEGENERATE_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::degenerate {

// ------------------------------------------------------ single predicate --

template <template <class> class F>
struct SingleStatement {
  F<std::array<bool, 1>> z;
};
template <template <class> class F>
struct SingleWitness {
  F<std::array<bool, 1>> a;
  F<std::array<bool, 1>> b;
};

inline auto single_predicate() {
  return compile<SingleStatement, SingleWitness>(
      compile_profile("single-predicate"),
      [](BinarySys &cs, SingleStatement<In> st, SingleWitness<In> w) {
        auto &H = cs.domain(binary_profile(), "H");
        const auto a = H.priv(w.a);
        const auto b = H.priv(w.b);
        assert_equal(a * b, st.z.bits(H), "and");
      },
      "heldout-single-predicate");
}

// --------------------------------------------------------- minimal tables --

template <template <class> class F>
struct TableStatement {
  F<std::array<uint64_t, 1>> total;
};
template <template <class> class F>
struct TableWitness {
  F<std::array<uint64_t, 1>> seven;
  F<std::array<uint64_t, 3>> picks;
  F<std::array<uint64_t, 2>> pair;
  F<std::array<uint64_t, 1>> bit;
};

inline auto minimal_tables() {
  return compile<TableStatement, TableWitness>(
      compile_profile("minimal-tables"),
      [](GoldSys &cs, TableStatement<In> st, TableWitness<In> w) {
        auto &A = cs.domain(gold_profile(), "A");
        const GF &f = A.field();
        const auto seven = A.priv(Subfield<>{}, w.seven);
        const auto picks = A.priv(Subfield<>{}, w.picks);
        const auto pair = A.priv(Subfield<>{}, w.pair);
        const auto bit = A.priv(Subfield<>{}, w.bit);
        const auto one_row = A.constant("one_row", {f.of_scalar(7)});
        const auto two_rows =
            A.constant("two_rows", {f.of_scalar(3), f.of_scalar(9)});
        const auto pair_row = A.constant("pair_row", {f.of_scalar(1), f.of_scalar(2)})
                                  .reshape({1, 2});
        assert_in(seven, in_table(cs, "one", one_row), "seven");
        assert_in(picks, in_table(cs, "two", two_rows), "picks");
        assert_in(pair, in_table(cs, "pair", pair_row), "pair");
        assert_range(bit, 2, "bit");
        assert_equal(picks.sum() + bit, st.total.values(A), "total");
      },
      "heldout-minimal-tables");
}

}  // namespace proofs::gordiehowe::heldout::degenerate

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_DEGENERATE_H_
