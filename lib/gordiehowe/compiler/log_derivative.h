// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the log-derivative lookup identity as a circuit, shared by
// the range lowering (range.h, tables [0, T)) and assert_in
// (compiler/assert_in.h).
//
// For needles v_t, a challenge alpha, counts m_j and weights
// w_j = (alpha - table_j)^-1, the identity
//
//   sum_t 1 / (alpha - v_t) = sum_j m_j w_j
//
// is checked by a balanced fraction tree: leaves (1, alpha - v_t), a node
// N = N_l D_r + N_r D_l over D = D_l D_r, and at the root N = D sum_j m_j w_j.
// Several count vectors (a static and a late histogram) share the weights,
// count vector k read against weights 0..|m_k| - 1. A table whose rows
// the circuit reads (every assert_in table, public or committed) has no
// public weights: its side is a second fraction tree
// (assert_log_derivative_committed).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LOG_DERIVATIVE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LOG_DERIVATIVE_H_

#include <cstddef>
#include <optional>
#include <utility>
#include <vector>

namespace proofs::gordiehowe::compiler {

// A fraction-tree node: numerator (absent means 1) and denominator.
struct Fraction {
  std::optional<size_t> n;
  size_t d;
};

// The balanced fraction tree over the leaves LEVEL (not empty): its root,
// sum_i n_i / d_i as one fraction.
template <class LC>
Fraction fraction_sum(const LC &lc, std::vector<Fraction> level) {
  while (level.size() > 1) {
    std::vector<Fraction> next;
    for (size_t i = 0; i + 1 < level.size(); i += 2) {
      const Fraction &l = level[i], &r = level[i + 1];
      const size_t lr = l.n ? lc.mul(*l.n, r.d) : r.d;
      const size_t rl = r.n ? lc.mul(*r.n, l.d) : l.d;
      next.push_back({lc.add(lr, rl), lc.mul(l.d, r.d)});
    }
    if (level.size() % 2) next.push_back(level.back());
    level = std::move(next);
  }
  return level.at(0);
}

// The identity over the needle wires NEEDLES, the alpha wire ALPHA, the
// count wires COUNTS (each indexable by j) and the weight wires WEIGHTS.
template <class LC, class Counts, class Weights>
void assert_log_derivative(const LC &lc, const std::vector<size_t> &needles,
                           size_t alpha,
                           const std::vector<const Counts *> &counts,
                           const Weights &weights) {
  std::vector<Fraction> level;
  level.reserve(needles.size());
  for (size_t v : needles) level.push_back({std::nullopt, lc.sub(alpha, v)});
  const Fraction root = fraction_sum(lc, std::move(level));
  std::vector<size_t> sum;
  for (const Counts *m : counts)
    for (size_t j = 0; j < m->size(); ++j)
      sum.push_back(lc.mul((*m)[j], weights[j]));
  // A balanced sum: the circuit compiler stores each sum node as the
  // merged term list of its addends, so a left fold over T products keeps
  // T^2 / 2 terms; the balanced tree keeps T log T and yields the same
  // root node.
  while (sum.size() > 1) {
    std::vector<size_t> next;
    for (size_t i = 0; i + 1 < sum.size(); i += 2)
      next.push_back(lc.add(sum[i], sum[i + 1]));
    if (sum.size() % 2) next.push_back(sum.back());
    sum = std::move(next);
  }
  const size_t num = root.n ? *root.n : lc.konst(lc.one());
  lc.assert_eq(num, lc.mul(root.d, sum.at(0)));
}

// The identity over a table whose packed rows TABLE are wires (an
// assert_in table): the table side is a second fraction tree with leaves
// (m_j, alpha - table_j), and the two roots N_v / D_v and N_t / D_t agree
// after clearing denominators, N_v D_t = N_t D_v. As a polynomial in alpha
// it has degree at most n + R - 1 (n needles, R rows) and vanishes for the
// honest counts, so it needs no weight and has no pole.
template <class LC, class Counts>
void assert_log_derivative_committed(const LC &lc,
                                     const std::vector<size_t> &needles,
                                     size_t alpha, const Counts &counts,
                                     const std::vector<size_t> &table) {
  std::vector<Fraction> lv, lt;
  lv.reserve(needles.size());
  for (size_t v : needles) lv.push_back({std::nullopt, lc.sub(alpha, v)});
  lt.reserve(table.size());
  for (size_t j = 0; j < table.size(); ++j)
    lt.push_back({counts[j], lc.sub(alpha, table[j])});
  const Fraction rv = fraction_sum(lc, std::move(lv));
  const Fraction rt = fraction_sum(lc, std::move(lt));
  const size_t lhs = rv.n ? lc.mul(*rv.n, rt.d) : rt.d;
  lc.assert_eq(lhs, lc.mul(*rt.n, rv.d));
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LOG_DERIVATIVE_H_
