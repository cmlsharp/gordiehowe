// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: rows of a value at a private offset, as a library function
// over the core.
//
//   shift(D, x, amount, k)   rows amount .. amount + k - 1 of X, zero past
//                            X's last row
//
// X is [n, ...] (any trailing shape: a byte is [8] bits), AMOUNT a Bit word
// (least significant first) that the prover commits or computes. shift is
// Longfellow's barrel shifter (circuits/logic/routing.h, Routing::shift):
// the amount's bits are consumed from the most significant down in rounds
// of about UNROLL bits. A round of c bits keeps, for each output row i,
//
//   sum_{j < c} [the c bits = j] tmp[i + j s],
//
// s = 2^(bits left after the round), a one-hot selection over c views of
// the rows: shifted copies of the rows, read through one index map (a view
// with no storage), times the bits' equality with each j (Logic::eq on the
// c bits). After the last round s = 1 and row i holds X[i + amount].
//
// Cost: per round, about 2^c (k + s) row multiplexers; the rows a round
// keeps shrink to min(n, k + s), as Longfellow's do.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_ROUTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_ROUTING_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"

namespace proofs::gordiehowe::lib::routing {

// Rows AMOUNT .. AMOUNT + K - 1 of X ([n, ...] Bit), zero past row n - 1,
// [k, ...]: Longfellow's Routing::shift (above), its rounds consuming
// about UNROLL of AMOUNT's bits each.
template <class F>
Expr<F, Bit> shift(const Domain<F> &D, const Expr<F, Bit> &x,
                   const Expr<F, Bit> &amount, size_t k, size_t unroll = 3) {
  const auto dims = x.dims();
  const size_t n = dims[0], logn = amount.size();
  // One row's trailing shape, and a zero row past the last.
  std::vector<size_t> row(dims.begin() + 1, dims.end());
  size_t width = 1;
  for (size_t d : row) width *= d;
  std::vector<size_t> one_row = {1};
  one_row.insert(one_row.end(), row.begin(), row.end());
  const Expr<F, Bit> zero_row = D.constant(
      Bit{}, std::vector<uint64_t>(width, 0), Shape(one_row));
  Expr<F, Bit> tmp = x;
  size_t rows = n, l = logn;
  size_t rounds = (logn + unroll - 1) / unroll;
  while (rounds > 0) {
    const size_t consumed = (l + rounds - 1) / rounds;
    --rounds;
    l -= consumed;
    const size_t s = size_t{1} << l, c = size_t{1} << consumed;
    const size_t m = std::min(n, k + s);
    // is[j] = [the consumed bits = j], the bits repeated per j.
    std::vector<uint64_t> js(c);
    for (size_t j = 0; j < c; ++j) js[j] = j;
    const Expr<F, Bit> bits = amount.slice(l, l + consumed)
                                  .reshape({1, consumed})
                                  .reindex(std::vector<size_t>(c, 0), 0);
    const Expr<F, Bit> is = bits.from_bits() == js;
    // Copy j of the rows starts at row j s: rows i + j s for i < m, the
    // zero row past the last.
    std::vector<size_t> starts;
    for (size_t j = 0; j < c; ++j)
      for (size_t i = 0; i < m; ++i)
        starts.push_back(std::min(i + j * s, rows));
    std::vector<size_t> copies = {c, m};
    copies.insert(copies.end(), row.begin(), row.end());
    const Expr<F, Bit> shifted =
        tmp.concat(zero_row).reindex(starts, 0).reshape(Shape(copies));
    std::vector<size_t> per_copy = {c, 1};
    per_copy.insert(per_copy.end(), row.size(), 1);
    tmp = (is.reshape(Shape(per_copy)) & shifted).sum(0);
    rows = m;
  }
  return tmp.slice(0, k);
}

}  // namespace proofs::gordiehowe::lib::routing

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_ROUTING_H_
