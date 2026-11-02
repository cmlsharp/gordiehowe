// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the spectral sums of spectral.h as values, without its
// builders, and the two sides of spectral rows as expressions
// (spectral_sides), so that an integer congruence's spectral product term
// (ops/integer_congruence.h) can hold and state one.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_SUM_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_SUM_H_

#include <cstddef>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"

namespace proofs::gordiehowe::ops {

// scale * spec[k] * Ntt(x)[k], spec read at an offset (in elements) of its
// node, x at an offset of its expression's coordinates. KEY names the
// operand x: a handle's node, or the expression itself, so that an operand
// passed twice is transformed once.
template <class F>
struct SpectralTerm {
  Ref<F> spec;
  size_t spec_at = 0;
  ExprPtr<F> x;
  size_t x_at = 0;
  typename F::Elt scale;
  std::pair<size_t, const void *> key;
};

// A sum of spectral terms under one staged transform (OP, the Ntt
// operator; NTT its stages).
template <class F>
struct SpectralSum {
  std::shared_ptr<const StagedNtt<F>> ntt;
  Op<F> op;
  std::vector<SpectralTerm<F>> terms;
};

// One spectral row: Ntt(lhs) == rhs, LHS an expression of n coordinates.
template <class F>
struct SpectralRow {
  ExprPtr<F> lhs;
  SpectralSum<F> rhs;
};

// The two sides of each row, Ntt(rows[i].lhs) and rows[i].rhs, as
// expressions. Every row shares one transform, applied through its staged
// butterflies (the Ntt operator's circuit expansion): each distinct operand
// x is transformed once (one expression, emitted once), each row's lhs
// once, and a row's right side is the sum of scale_t spec_t[k] Ntt(x_t)[k].
// WHAT names the caller in errors.
template <class F>
std::vector<std::pair<Expr<F>, Expr<F>>> spectral_sides(
    const std::vector<SpectralRow<F>> &rows, const std::string &what) {
  if (rows.empty()) fail(what + ": no rows");
  const auto t = rows[0].rhs.ntt;
  const Op<F> ntt = rows[0].rhs.op;
  const size_t n = t->n;
  std::map<std::pair<size_t, const void *>, Expr<F>> hat;
  std::vector<std::pair<Expr<F>, Expr<F>>> out;
  for (const auto &r : rows) {
    if (r.rhs.ntt != t) fail(what + ": rows under different transforms");
    if (r.lhs->n != n)
      fail(what + ": a left side of " + std::to_string(r.lhs->n) +
           " elements, not " + std::to_string(n));
    if (r.rhs.terms.empty()) fail(what + ": a row without terms");
    std::optional<Expr<F>> rhs;
    for (const auto &tm : r.rhs.terms) {
      auto it = hat.find(tm.key);
      if (it == hat.end())
        it = hat.emplace(tm.key, ntt(Expr<F>(tm.x))).first;
      const Expr<F> p =
          Expr<F>(tm.spec).flat().slice(tm.spec_at, tm.spec_at + n) *
          it->second.flat().slice(tm.x_at, tm.x_at + n);
      const Expr<F> sp = tm.scale == tm.spec.f->one() ? p : tm.scale * p;
      rhs = rhs.has_value() ? *rhs + sp : sp;
    }
    out.push_back({ntt(Expr<F>(r.lhs)), *rhs});
  }
  return out;
}

}  // namespace proofs::gordiehowe::ops

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_SUM_H_
