// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the work of a batch, counted by its kernels; the placement cost
// prices the counts at the field's measured rates.
//
// A batch's prover and verifier work per proof is its BatchKernel's
// reduce:
//   - the masked skip (field_skip.h): its first round (field operands, or
//     the bit-sliced kernels on the operand lanes), its rounds and terminal
//     values, and the verifier's rows, instance weights and opening row;
//   - the operand map (view_map.h, batch.h): the prover's operands from the
//     table words and the verifier's forms on them (BatchOperands::
//     map_work).
// Both are counted by running the code over CountingField<F>
// (counting_field.h), so the counts follow it. The map runs once, at its
// size. The skip's work is a function of the relation, the width and the
// instances only, exactly a sum of seven terms (skip_terms): its loops run
// over the instances, the live rows (the first round's, ceil(n / w)), the
// 2^logs eq weights, the round pairs (each round's sums and folds stop at
// the live rows) and the logs rounds, the verifier's round claims growing
// a round at a time. skip_ops runs it at small sizes, solves for the
// terms' parts, checks them on every size, and evaluates them at the
// batch's instances. The bit-sliced
// kernels' byte-lane steps, which no field operation counts, come from
// their loops' trip counts (BatchOperands::lane_work).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_OP_COUNTS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_OP_COUNTS_H_

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "gordiehowe/compiler/batch.h"
#include "gordiehowe/compiler/bit_skip.h"
#include "gordiehowe/compiler/counting_field.h"
#include "gordiehowe/compiler/field_skip.h"
#include "random/transcript.h"
#include "sumcheck/boolean_skip.h"
#include "util/panic.h"

namespace proofs::gordiehowe::compiler {

namespace op_counts_internal {

// The rounds of the skip of UNITS (instances; bit-sliced: 64-bit lanes,
// 64 instances each) at WIDTH.
inline size_t logs_of(size_t units, SkipKind kind, unsigned width) {
  const size_t rows = kind == SkipKind::kField ? units : units * 64;
  size_t n = 1, logs = 0;
  while (n * width < rows) {
    n *= 2;
    ++logs;
  }
  return logs;
}

// The terms the skip's work at UNITS is a sum of, each times a constant
// of the relation and the width: 1, the instances, the live rows (the first
// round's), 2^logs (the eq weights and their folds), the round pairs (each
// round's sums and folds, MaskedFieldSkip::prove's pairs), logs and logs^2.
inline std::vector<double> skip_terms(size_t units, SkipKind kind,
                                      unsigned width) {
  const size_t instances = kind == SkipKind::kField ? units : units * 64;
  const size_t logs = logs_of(units, kind, width);
  const size_t live = (instances + width - 1) / width;
  size_t pairs = 0;
  for (size_t m = size_t(1) << logs, l = live; m > 1; m /= 2) {
    const size_t half = std::min(m / 2, (l + 1) / 2);
    pairs += half;
    l = half;
  }
  return {1.0, double(instances), double(live), std::ldexp(1.0, int(logs)),
          double(pairs), double(logs), double(logs) * double(logs)};
}

// The skip's field operations at UNITS, run over CF on zero operands.
template <class F, class Hash>
OpCounts skip_at(const CountingField<F> &cf,
                 const FieldRelation<CountingField<F>> &rel, SkipKind kind,
                 size_t units, unsigned width) {
  using CF = CountingField<F>;
  using Elt = typename F::Elt;
  const size_t instances = kind == SkipKind::kField ? units : units * 64;
  const MaskedFieldSkip<CF> sk(cf, rel, instances, width);
  std::vector<Elt> pads(sk.layout.count);
  for (size_t i = 0; i < pads.size(); ++i) pads[i] = cf.of_scalar(i + 1);
  static const uint8_t kLabel[] = "gordiehowe.op-counts";
  const BasicProofSeed<Hash> seed{};
  BasicTranscript<Hash> tp(kLabel, sizeof(kLabel) - 1, seed);
  BasicTranscript<Hash> tv(kLabel, sizeof(kLabel) - 1, seed);
  // The kernels' constructions (skip domains, tables) are not per proof.
  if constexpr (!F::kCharacteristicTwo) {
    check(kind == SkipKind::kField, "batch op counts: a bit skip off GF(2^k)");
    const FieldSkipOperands<CF> first(std::vector<std::vector<Elt>>(
        instances, std::vector<Elt>(rel.operands, cf.zero())));
    cf.counts() = OpCounts{};
    const auto proof = sk.prove(first, tp, pads.data());
    auto ctx = sk.rows_of(proof, tv, 0);
    (void)sk.instance_weights(ctx);
    sk.opening_row(ctx, cf.zero(), 0);
  } else {
    std::unique_ptr<SkipOperands<CF>> first;
    std::unique_ptr<RuntimeBooleanSkip<CF>> run;
    std::unique_ptr<BasicBooleanSkip<CF, SkipChi>> chi;
    if (kind == SkipKind::kField) {
      first = std::make_unique<FieldSkipOperands<CF>>(
          std::vector<std::vector<Elt>>(
              instances, std::vector<Elt>(rel.operands, cf.zero())));
    } else if (kind == SkipKind::kBitChi) {
      chi = std::make_unique<BasicBooleanSkip<CF, SkipChi>>(cf, width);
    } else {
      std::vector<std::vector<unsigned>> monos;
      for (const auto &m : rel.monomials) monos.push_back(m.ops);
      run = std::make_unique<RuntimeBooleanSkip<CF>>(cf, rel.operands, monos,
                                                     width);
    }
    cf.counts() = OpCounts{};
    if (chi) {
      first = std::make_unique<BitSkipOperands<CF, SkipChi>>(
          *chi, chi->rows(std::vector<SkipWord>(units, SkipWord{0, 0, 0})));
    } else if (run) {
      size_t n = 0;
      auto rows =
          run->rows(std::vector<uint64_t>(units * rel.operands, 0), n);
      first = std::make_unique<RuntimeBitSkipOperands<CF>>(
          *run, std::move(rows), n);
    }
    const auto proof = sk.prove(*first, tp, pads.data());
    auto ctx = sk.rows_of(proof, tv, 0);
    (void)sk.instance_weights(ctx);
    if (chi) (void)chi->bit_basis(ctx.r);
    if (run) (void)run->bit_basis(ctx.r);
    sk.opening_row(ctx, cf.zero(), 0);
  }
  return cf.counts();
}

}  // namespace op_counts_internal

// The masked skip's field operations at UNITS (instances; bit-sliced:
// lanes): the parts of skip_terms (the verifier's round claims grow by D
// terms a round, so logs^2), solved by least squares from runs at small
// sizes and checked exactly on every one of them (a mismatch fails the
// compile: the kernel's work is then not of that form).
template <class F, class Hash>
OpCounts skip_ops(const CountingField<F> &cf,
                  const FieldRelation<CountingField<F>> &rel, SkipKind kind,
                  size_t units, unsigned width) {
  using op_counts_internal::logs_of;
  using op_counts_internal::skip_at;
  using op_counts_internal::skip_terms;
  // The most units at LOGS rounds.
  auto at = [&](size_t logs) {
    return kind == SkipKind::kField
               ? size_t(width) << logs
               : std::max<size_t>((size_t(width) << logs) / 64, 1);
  };
  // At 3 to 8 rounds, each full, one unit short, three quarters full and
  // just over half full: live rows apart from the instances, round pairs
  // apart from the live rows.
  std::vector<size_t> sizes;
  for (size_t l = 3; l <= 8; ++l)
    for (size_t u : {at(l), at(l) - 1, at(l) / 4 * 3, at(l) / 2 + 1})
      if (u >= 1 && std::find(sizes.begin(), sizes.end(), u) == sizes.end())
        sizes.push_back(u);
  std::vector<OpCounts> c;
  for (size_t u : sizes) c.push_back(skip_at<F, Hash>(cf, rel, kind, u, width));
  // The terms' columns that vary independently over the sizes: a term that
  // is a combination of earlier ones over every size (the instances of a
  // bit-sliced batch, 64 / w live rows each, or of width 1) joins them.
  // Gram-Schmidt on the columns, a residual below 1e-9 of the column's
  // norm dropping it.
  const size_t nt = skip_terms(1, kind, width).size();
  std::vector<std::vector<double>> rows;
  for (size_t u : sizes) rows.push_back(skip_terms(u, kind, width));
  std::vector<size_t> cols;
  std::vector<std::vector<long double>> basis;
  for (size_t t = 0; t < nt; ++t) {
    std::vector<long double> v(rows.size());
    long double norm = 0;
    for (size_t i = 0; i < rows.size(); ++i) {
      v[i] = rows[i][t];
      norm += v[i] * v[i];
    }
    for (const auto &q : basis) {
      long double dot = 0;
      for (size_t i = 0; i < v.size(); ++i) dot += v[i] * q[i];
      for (size_t i = 0; i < v.size(); ++i) v[i] -= dot * q[i];
    }
    long double rest = 0;
    for (long double x : v) rest += x * x;
    if (rest <= 1e-18L * norm) continue;
    for (auto &x : v) x /= std::sqrt(rest);
    basis.push_back(std::move(v));
    cols.push_back(t);
  }
  // Least squares by the normal equations, in long double.
  auto solve = [&](auto get) {
    const size_t k = cols.size();
    std::vector<std::vector<long double>> m(k,
                                            std::vector<long double>(k + 1));
    for (size_t i = 0; i < rows.size(); ++i)
      for (size_t a = 0; a < k; ++a) {
        for (size_t b = 0; b < k; ++b)
          m[a][b] += (long double)rows[i][cols[a]] * rows[i][cols[b]];
        m[a][k] += (long double)rows[i][cols[a]] * (long double)get(c[i]);
      }
    for (size_t i = 0; i < k; ++i) {
      size_t piv = i;
      for (size_t r = i + 1; r < k; ++r)
        if (std::fabs(m[r][i]) > std::fabs(m[piv][i])) piv = r;
      std::swap(m[i], m[piv]);
      check(m[i][i] != 0, "batch op counts: singular skip fit");
      for (size_t r = 0; r < k; ++r) {
        if (r == i) continue;
        const long double q = m[r][i] / m[i][i];
        for (size_t b = i; b <= k; ++b) m[r][b] -= q * m[i][b];
      }
    }
    std::vector<long double> p(k);
    for (size_t i = 0; i < k; ++i) p[i] = m[i][k] / m[i][i];
    return p;
  };
  auto eval = [&](const std::vector<long double> &p, size_t u) {
    const auto t = skip_terms(u, kind, width);
    long double v = 0;
    for (size_t i = 0; i < cols.size(); ++i) v += p[i] * t[cols[i]];
    return std::llround(v);
  };
  OpCounts out;
  auto part = [&](auto get, uint64_t &dst, const char *name) {
    const auto p = solve(get);
    for (size_t i = 0; i < sizes.size(); ++i)
      check(eval(p, sizes[i]) == (long long)get(c[i]),
            (std::string("batch op counts: the skip's ") + name +
             " count is not a sum of skip_terms")
                .c_str());
    dst = uint64_t(eval(p, units));
  };
  part([](const OpCounts &x) { return x.mul; }, out.mul, "mul");
  part([](const OpCounts &x) { return x.add; }, out.add, "add");
  part([](const OpCounts &x) { return x.mac; }, out.mac, "mac");
  part([](const OpCounts &x) { return x.reduce; }, out.reduce, "reduce");
  part([](const OpCounts &x) { return x.inv; }, out.inv, "inv");
  return out;
}

// The work of one proof of the batch OPS (over CountingField<F>) at skip
// WIDTH: the skip's field operations (skip_ops, its first round of
// BatchOperands::skip_kind),
// the operand map's (BatchOperands::map_work, run once), the byte-lane
// steps (BatchOperands::lane_work) and the opening row's table words.
template <class F, class Hash>
OpCounts batch_ops(const CountingField<F> &cf,
                   std::shared_ptr<const BatchOperands<CountingField<F>>> ops,
                   unsigned width) {
  using CF = CountingField<F>;
  const SkipKind kind = ops->skip_kind();
  FieldRelation<CF> rel = ops->relation(cf.one());
  if (kind == SkipKind::kBitChi) {
    rel.operands = 3;
    rel.monomials = {{cf.one(), {0, 1}}, {cf.one(), {2}}};
  }
  const size_t units =
      kind == SkipKind::kField ? ops->instances() : ops->instances() / 64;
  OpCounts c = skip_ops<F, Hash>(cf, rel, kind, units, width);
  cf.counts() = OpCounts{};
  ops->map_work(width);
  const OpCounts m = cf.counts();
  c.mul += m.mul;
  c.add += m.add;
  c.mac += m.mac;
  c.reduce += m.reduce;
  c.inv += m.inv;
  c.map_mul = m.mul;
  c.map_add = m.add;
  c.map_mac = m.mac;
  const OpCounts lanes = ops->lane_work(width);
  c.lane_lookup = lanes.lane_lookup;
  c.lane_mul = lanes.lane_mul;
  c.lane_term = lanes.lane_term;
  c.lin = ops->words();
  return c;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_OP_COUNTS_H_
