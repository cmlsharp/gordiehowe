// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the masked univariate-skip zerocheck over any field, for
// batched relations on field-element operands (word-level relations in
// characteristic 2, any relation in odd characteristic).
//
// This is sumcheck/boolean_skip.h's generic-Q path with a masked
// zerocheck, written for a field of any characteristic and operands that
// are field elements:
//   - the relation Q is a polynomial over the operand field, every monomial
//     reading an operand (Q(0) = 0, so the zero rows that pad the instances
//     to a power of two satisfy it);
//   - the instances t = r w + z put z, the skip variable, on a w-point
//     domain: the additive GF(2^8) subspace of the binary skip in
//     characteristic 2 (SkipByteField's elements 0..w-1), and the integers
//     0..w-1 otherwise, extended to D(w-1)+1 points (0..D(w-1)) with
//     closed-form Lagrange weights;
//   - the rounds bind r from its low bit, with eq(rho, X) = 1 - rho - X +
//     2 rho X, which is 1 + rho + X in characteristic 2;
//   - every message m = x + P is masked by a committed pad P; the terminal
//     check claim = eq Q(m - P) expands over pad monomials, a monomial of
//     degree >= 2 a committed product cell.
// The terminal operand claims, combined with challenges u, are a linear
// claim on the table's coordinates (the operand map's adjoint), which the
// domain's packing tree opens: the row
//     sum_c A_c W_c + sum_j u_j P_j = sum_j u_j m_j - constant.
// The prover's skip values, binds, round sums and folds stop at the live
// rows, the first ceil(instances / w) of the 2^logs rows: the zero rows
// after them add nothing to any message. The live count is fixed by the
// batch's shape, so every loop bound is public. Under a runner
// (util/parallel.h) the round sums and folds run in chunks, the sums added
// in chunk order.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_FIELD_SKIP_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_FIELD_SKIP_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "arrays/eqs.h"
#include "gordiehowe/compiler/prover_scratch.h"
#include "gordiehowe/compiler/test_switches.h"
#include "gordiehowe/core.h"
#include "ligero/ligero_param.h"
#include "random/transcript.h"
#include "sumcheck/boolean_skip.h"
#include "util/panic.h"
#include "util/parallel.h"
#include "util/prover_profile.h"

namespace proofs::gordiehowe::compiler {

// A relation over K operands: a sum of monomials coeff * prod_t x_{op_t},
// coefficients in the operand field (as elements of F).
template <class F>
struct FieldRelation {
  using Elt = typename F::Elt;
  struct Monomial {
    Elt coeff;
    std::vector<unsigned> ops;  // sorted operand indices, with repetition
  };
  std::string name;
  unsigned operands = 0;
  std::vector<Monomial> monomials;
  unsigned degree() const {
    size_t d = 0;
    for (const auto &m : monomials) d = std::max(d, m.ops.size());
    return unsigned(d);
  }
  Elt eval(const F &f, const Elt *x) const {
    Elt s = f.zero();
    for (const auto &m : monomials) {
      Elt p = m.coeff;
      for (unsigned j : m.ops) f.mul(p, x[j]);
      f.add(s, p);
    }
    return s;
  }
  // Why it is no batched relation, or "".
  std::string error() const {
    if (operands == 0 || monomials.empty()) return "no operand or monomial";
    for (size_t i = 0; i < monomials.size(); ++i) {
      if (monomials[i].ops.empty())
        return "monomial " + std::to_string(i) + " is constant; Q has no "
               "constant term";
      for (unsigned j : monomials[i].ops)
        if (j >= operands)
          return "monomial " + std::to_string(i) + " reads operand " +
                 std::to_string(j) + " of " + std::to_string(operands);
    }
    return "";
  }
};

// The skip domain: D(w-1)+1 points, the first w the instances' skip
// coordinates, and Lagrange weights over any prefix of them.
template <class F>
class SkipDomain {
 public:
  using Elt = typename F::Elt;
  SkipDomain() = default;
  SkipDomain(const F &f, unsigned width, unsigned degree)
      : w_(width), npts_(degree * (width - 1) + 1) {
    check(width >= 1, "skip width");
    points_.resize(npts_);
    if constexpr (F::kCharacteristicTwo) {
      check(npts_ <= 256, "binary skip: D (w - 1) + 1 <= 256");
      using Small = typename SkipByteField<F>::type;
      Small s;
      for (unsigned i = 0; i < npts_; ++i)
        points_[i] = f.of_scalar_field(s.of_scalar(i).unpack().u64());
    } else {
      // The points 0..npts-1 are distinct iff the characteristic is at
      // least npts, i.e. no i in [1, npts) is zero in F.
      for (unsigned i = 1; i < npts_; ++i)
        if (f.of_scalar(i) == f.zero())
          fail("odd-characteristic skip: the characteristic is below "
               "D (w - 1) + 1 = " + std::to_string(npts_) +
               ", so the skip points 0..npts-1 collide");
      for (unsigned i = 0; i < npts_; ++i) points_[i] = f.of_scalar(i);
    }
  }
  unsigned width() const { return w_; }
  unsigned points() const { return npts_; }
  const Elt &point(unsigned i) const { return points_[i]; }
  // Lagrange weights at R over the first N points.
  std::vector<Elt> basis(const F &f, unsigned n, const Elt &r) const {
    std::vector<Elt> l(n, f.zero());
    for (unsigned i = 0; i < n; ++i)
      if (r == points_[i]) {
        l[i] = f.one();
        return l;
      }
    Elt prod = f.one();
    for (unsigned j = 0; j < n; ++j) f.mul(prod, f.subf(r, points_[j]));
    for (unsigned i = 0; i < n; ++i) {
      Elt den;
      if constexpr (F::kCharacteristicTwo) {
        den = f.one();
        for (unsigned j = 0; j < n; ++j)
          if (j != i) f.mul(den, f.subf(points_[i], points_[j]));
      } else {
        // Consecutive integers: prod_{j != i} (i - j) = (-1)^(n-1-i) i!
        // (n-1-i)!.
        den = f.one();
        for (unsigned k = 1; k <= i; ++k) f.mul(den, f.of_scalar(k));
        for (unsigned k = 1; k + i < n; ++k) f.mul(den, f.of_scalar(k));
        if ((n - 1 - i) & 1) den = f.negf(den);
      }
      l[i] = f.mulf(prod, f.invertf(f.mulf(den, f.subf(r, points_[i]))));
    }
    return l;
  }

 private:
  unsigned w_ = 1, npts_ = 1;
  std::vector<Elt> points_;
};

template <class F>
class MaskedFieldSkip;

// The first round of the masked skip, by operand type: the skip values and
// the operands bound at the skip point. The rounds after it, the masking
// and the verifier's rows are MaskedFieldSkip's, whatever the operands.
template <class F>
class SkipOperands {
 public:
  using Elt = typename F::Elt;
  virtual ~SkipOperands() = default;
  // S(x) = sum_r e_r Q(sum_z L_z(x) op(r w + z)) at the skip points
  // w .. D (w - 1), unmasked; E has 2^logs weights. The rows from
  // sk.live_rows() on are zero and add nothing.
  virtual std::vector<Elt> skip_values(const MaskedFieldSkip<F> &sk,
                                       const std::vector<Elt> &e) const = 0;
  // A bound operand's table (util/parallel.h's Buffer: the binds write
  // every entry in their chunks).
  using Table = parallel::Buffer<Elt>;
  // Operand j of row r with the skip variable bound at R: K tables of
  // 2^logs entries, zero beyond the instances (from sk.live_rows() on),
  // written into OUT, whose tables keep their capacity (prover_scratch.h).
  virtual void bind_into(const MaskedFieldSkip<F> &sk, const Elt &r,
                         std::vector<Table> &out) const = 0;
  std::vector<Table> bind(const MaskedFieldSkip<F> &sk, const Elt &r) const {
    std::vector<Table> out;
    bind_into(sk, r, out);
    return out;
  }
};

// Field-element operands: OPS[t][j] is operand j of instance t, evaluated
// generically in F.
template <class F>
class FieldSkipOperands final : public SkipOperands<F> {
 public:
  using Elt = typename F::Elt;
  // Borrows OPS, or owns them.
  explicit FieldSkipOperands(const std::vector<std::vector<Elt>> &ops)
      : ops_(&ops) {}
  explicit FieldSkipOperands(std::vector<std::vector<Elt>> &&ops)
      : own_(std::move(ops)), ops_(&own_) {}
  std::vector<Elt> skip_values(const MaskedFieldSkip<F> &sk,
                               const std::vector<Elt> &e) const override {
    const F &f = sk.f;
    const unsigned w = sk.dom.width();
    std::vector<Elt> out, x(sk.K);
    const size_t live = std::min(e.size(), sk.live_rows());
    for (unsigned pt = w; pt < sk.dom.points(); ++pt) {
      const auto l = sk.dom.basis(f, w, sk.dom.point(pt));
      Elt sv = f.zero();
      for (size_t r = 0; r < live; ++r) {
        for (unsigned j = 0; j < sk.K; ++j) {
          Elt v = f.zero();
          for (unsigned z = 0; z < w; ++z) f.add(v, f.mulf(l[z], op(f, r * w + z, j)));
          x[j] = v;
        }
        f.add(sv, f.mulf(e[r], sk.rel.eval(f, x.data())));
      }
      out.push_back(sv);
    }
    return out;
  }
  using Table = typename SkipOperands<F>::Table;
  void bind_into(const MaskedFieldSkip<F> &sk, const Elt &r,
                 std::vector<Table> &o) const override {
    const F &f = sk.f;
    const unsigned w = sk.dom.width();
    const size_t n = size_t(1) << sk.layout.logs;
    const size_t live = std::min(n, sk.live_rows());
    const auto lr = sk.dom.basis(f, w, r);
    o.resize(sk.K);
    for (unsigned j = 0; j < sk.K; ++j) parallel::fill(o[j], n, f.zero());
    for (unsigned j = 0; j < sk.K; ++j)
      for (size_t i = 0; i < live; ++i)
        for (unsigned z = 0; z < w; ++z)
          f.add(o[j][i], f.mulf(lr[z], op(f, i * w + z, j)));
  }

 private:
  Elt op(const F &f, size_t t, unsigned j) const {
    return t < ops_->size() ? (*ops_)[t][j] : f.zero();
  }
  std::vector<std::vector<Elt>> own_;
  const std::vector<std::vector<Elt>> *ops_;
};

template <class F>
class MaskedFieldSkip {
 public:
  using Elt = typename F::Elt;
  using Term = LigeroLinearConstraint<F>;
  using Table = typename SkipOperands<F>::Table;
  struct Proof {
    std::vector<Elt> skip;                // (D-1)(w-1) values
    std::vector<std::vector<Elt>> rounds;  // D coefficients per round
    std::vector<Elt> terminal;            // K values
  };
  struct Layout {
    size_t logs = 0, terminal = 0, product = 0, count = 0;
  };
  struct Expr {
    Elt known;
    std::vector<std::pair<size_t, Elt>> terms;
  };
  // Rows over witness indices (A, B: the row says sum A w = B).
  struct Context {
    std::vector<Term> a;
    std::vector<Elt> b;
    Elt r;
    std::vector<Elt> s;
    std::vector<Elt> u;
    std::vector<Elt> terminal;
  };

  const F &f;
  FieldRelation<F> rel;
  SkipDomain<F> dom;
  unsigned K = 0, D = 0;
  size_t rows = 0;  // instances
  Layout layout;
  std::vector<std::vector<unsigned>> products;
  std::vector<LigeroQuadraticConstraint> pad_quadratic;

  MaskedFieldSkip(const F &field, FieldRelation<F> relation, size_t instances,
                  unsigned width)
      : f(field), rel(std::move(relation)), K(rel.operands), D(rel.degree()),
        rows(instances) {
    dom = SkipDomain<F>(f, width, D);
    size_t n = 1;
    while (n * width < rows) {
      n *= 2;
      ++layout.logs;
    }
    layout.terminal = extra() + D * layout.logs;
    layout.product = layout.terminal + K;
    products = pad_monomials();
    layout.count = layout.product + products.size();
    for (size_t i = 0; i < products.size(); ++i) {
      const auto &m = products[i];
      std::vector<unsigned> prefix(m.begin(), m.end() - 1);
      const size_t x = prefix.size() == 1 ? layout.terminal + prefix[0]
                                          : layout.product + product_index(prefix);
      pad_quadratic.push_back({x, layout.terminal + m.back(), layout.product + i});
    }
  }

  unsigned width() const { return dom.width(); }
  size_t extra() const { return size_t(D - 1) * (dom.width() - 1); }
  size_t round_pad(size_t i, unsigned d) const { return extra() + D * i + d; }
  size_t message_elts() const { return extra() + D * layout.logs + K; }
  // The rows that may be nonzero, ceil(instances / w) of the 2^logs: the
  // rows after them are the zero padding. Their operands are zero and Q
  // has no constant term, so they add nothing to the skip values or a
  // round's sums, and a pair of them folds to zero. A count the batch's
  // shape fixes: public.
  size_t live_rows() const {
    // The full_rows test switch (test_switches.h): all 2^logs rows; the
    // live-row tests compare the two proofs byte for byte.
    if (test_switches().full_rows) return size_t(1) << layout.logs;
    return (rows + dom.width() - 1) / dom.width();
  }

  template <class RNG>
  void fill_pads(Elt *p, RNG &rng) const {
    for (size_t i = 0; i < layout.product; ++i) p[i] = rng.elt(f);
    for (size_t i = 0; i < products.size(); ++i) {
      const auto &q = pad_quadratic[i];
      p[q.z] = f.mulf(p[q.x], p[q.y]);
    }
  }

  // The prover on the field operands OPS[t][j], operand j of instance t
  // (t < rows); messages masked by PADS.
  template <class Hash>
  Proof prove(const std::vector<std::vector<Elt>> &ops,
              BasicTranscript<Hash> &ts, const Elt *pads) const {
    const FieldSkipOperands<F> first(ops);
    return prove(first, ts, pads);
  }

  // The prover: the first round from OPS (the operand type's evaluation),
  // then the rounds on the bound operands; messages masked by PADS. The eq
  // weights, the bound tables and their fold targets are SCRATCH's when
  // given (prover_scratch.h), this call's own otherwise.
  template <class Hash>
  Proof prove(const SkipOperands<F> &ops, BasicTranscript<Hash> &ts,
              const Elt *pads, BatchScratch<F> *scratch = nullptr) const {
    const size_t n = size_t(1) << layout.logs;
    size_t pad = 0;
    auto mask = [&](Elt &v) { f.add(v, pads[pad++]); };
    std::vector<Elt> rho(layout.logs);
    for (auto &x : rho) x = challenge(ts);
    BatchScratch<F> own;
    BatchScratch<F> &buf = scratch != nullptr ? *scratch : own;
    auto eq_scope = std::make_unique<profiling::Scope>("batch.eq_weights");
    std::vector<Elt> &e = buf.eq;
    eq_table_into(rho, e);
    eq_scope.reset();
    Proof proof;
    {
      // The phase timers (util/prover_profile.h).
      profiling::Scope sc("batch.skip_values");
      proof.skip = ops.skip_values(*this, e);
    }
    check(proof.skip.size() == extra(), "skip values");
    for (auto &v : proof.skip) mask(v);
    ts.write(proof.skip.data(), 1, proof.skip.size(), f);
    const Elt rs = challenge(ts);
    auto bind_scope = std::make_unique<profiling::Scope>("batch.bind");
    std::vector<Table> &o = buf.bound;
    ops.bind_into(*this, rs, o);
    bind_scope.reset();
    profiling::Scope rounds_scope("batch.rounds");
    check(o.size() == K, "bound operands");
    for (const auto &v : o) check(v.size() == n, "bound operand rows");
    // Rounds: e holds eq(rho_{>i}, .) after dropping eq(rho_i, .).
    size_t m = n;
    if (m > 1) {
      for (size_t i = 0; i < m / 2; ++i) e[i] = f.addf(e[2 * i], e[2 * i + 1]);
      e.resize(m / 2);
    }
    // The tables' live rows; the rows after them are zero.
    size_t live = std::min(n, live_rows());
    // The tables' fold targets under a runner (fold).
    std::vector<Table> &targets = buf.fold;
    targets.resize(K);
    while (m > 1) {
      // The pairs that read a live row; the pairs after them are zero.
      const size_t half = std::min(m / 2, (live + 1) / 2);
      auto msg_scope =
          std::make_unique<profiling::Scope>("batch.rounds.message");
      std::vector<Elt> msg = round_message(o, e, half);
      msg_scope.reset();
      for (auto &v : msg) mask(v);
      proof.rounds.push_back(msg);
      ts.write(msg.data(), 1, msg.size(), f);
      const Elt s = challenge(ts);
      profiling::Scope fold_scope("batch.rounds.fold");
      for (unsigned j = 0; j < K; ++j) fold(o[j], targets[j], s, half, m / 2);
      for (size_t i = 0; i < m / 4; ++i) e[i] = f.addf(e[2 * i], e[2 * i + 1]);
      live = half;
      m /= 2;
    }
    for (unsigned j = 0; j < K; ++j) proof.terminal.push_back(o[j][0]);
    for (auto &v : proof.terminal) mask(v);
    // A fold swaps a table with its target: the larger buffer goes back
    // to the bound tables, which the next proof's bind fills whole.
    for (unsigned j = 0; j < K; ++j)
      if (targets[j].capacity() > o[j].capacity()) std::swap(o[j], targets[j]);
    if (!buf.keep) {
      release(e);
      release(o);
      release(targets);
    }
    return proof;
  }

  // eq(RHO, t) for every row t < 2^logs, into E, which keeps its capacity
  // (prover_scratch.h). Under a runner (util/parallel.h) as
  // eq(RHO_lo, t mod 2^h) eq(RHO_hi, t >> h), h = logs / 2, from two
  // tables of about sqrt(2^logs) entries, in chunks of rows; without one,
  // Eqs' recurrence (fill_eq). Each entry is the product of the same
  // factors, and field products are exact, so both give the same elements.
  void eq_table_into(const std::vector<Elt> &rho, std::vector<Elt> &e) const {
    const size_t logs = layout.logs, n = size_t(1) << logs;
    if (parallel::current == nullptr || logs < 2) {
      fill_eq(f, logs, n, rho.data(), e);
      return;
    }
    const size_t h = logs / 2, nlo = size_t(1) << h;
    const Eqs<F> lo(h, nlo, rho.data(), f);
    const Eqs<F> hi(logs - h, n >> h, rho.data() + h, f);
    e.resize(n);
    parallel::for_chunks(n, parallel::grain_for(n, parallel::kChunks),
                         [&](size_t b, size_t en) {
                           for (size_t t = b; t < en; ++t)
                             e[t] = f.mulf(lo.at(t & (nlo - 1)), hi.at(t >> h));
                         });
  }

  // One round's message, unmasked: the D sums over the pairs i < HALF.
  // Under a runner the pairs run in chunks (util/parallel.h), each chunk's
  // sums reduced and added in chunk order: the same field elements.
  std::vector<Elt> round_message(const std::vector<Table> &o,
                                 const std::vector<Elt> &e,
                                 size_t half) const {
    const size_t grain = parallel::grain_for(half, parallel::kChunks);
    std::vector<std::vector<typename F::Accum>> part(
        parallel::chunks(half, grain), std::vector<typename F::Accum>(D));
    parallel::for_chunks(half, grain, [&](size_t b, size_t en) {
      auto &acc = part[b / grain];
      if (D <= 2)
        quadratic_round_sums(o, e, b, en, acc);
      else if (D <= 4)
        round_sums<4>(o, e, b, en, acc);
      else
        round_sums<0>(o, e, b, en, acc);
    });
    std::vector<Elt> msg(D, f.zero());
    for (const auto &acc : part)
      for (unsigned d = 0; d < D; ++d) f.add(msg[d], f.reduce(acc[d]));
    return msg;
  }

  // Folds table V at S over its pairs i < HALF of M2: v_i = v_2i + s
  // (v_2i+1 - v_2i). On one chunk in place (entry i reads 2i and 2i + 1,
  // never below i); under a runner, chunks of pairs write into SCRATCH,
  // which then becomes V. Entry HALF, which the next round's last pair
  // may read, is the fold of two zero rows: zero.
  void fold(Table &v, Table &scratch, const Elt &s,
            size_t half, size_t m2) const {
    auto pairs = [&](const Elt *src, Elt *dst, size_t b, size_t en) {
      for (size_t i = b; i < en; ++i)
        dst[i] = f.addf(src[2 * i],
                        f.mulf(s, f.subf(src[2 * i + 1], src[2 * i])));
    };
    const size_t grain = parallel::grain_for(half, parallel::kChunks);
    if (parallel::chunks(half, grain) < 2) {
      pairs(v.data(), v.data(), 0, half);
    } else {
      if (scratch.size() < half + 1) scratch.resize(half + 1);
      parallel::for_chunks(half, grain, [&](size_t b, size_t en) {
        pairs(v.data(), scratch.data(), b, en);
      });
      std::swap(v, scratch);
    }
    if (half < m2) v[half] = f.zero();
  }

  // round_sums for Q of degree at most 2: per monomial c x y, q_1 gets
  // c (dx y0 + x0 dy) and q_2 gets c dx dy; per monomial c x, q_1 gets c dx.
  void quadratic_round_sums(const std::vector<Table> &o,
                            const std::vector<Elt> &e, size_t begin,
                            size_t end,
                            std::vector<typename F::Accum> &acc) const {
    struct Mono {
      const Elt *x, *y;  // y null: degree 1
      bool unit;
      Elt coeff;
    };
    std::vector<Mono> ms;
    for (const auto &mono : rel.monomials)
      ms.push_back({o[mono.ops[0]].data(),
                    mono.ops.size() > 1 ? o[mono.ops[1]].data() : nullptr,
                    mono.coeff == f.one(), mono.coeff});
    for (size_t i = begin; i < end; ++i) {
      Elt q1 = f.zero(), q2 = f.zero();
      for (const Mono &mm : ms) {
        const Elt x0 = mm.x[2 * i];
        const Elt dx = f.subf(mm.x[2 * i + 1], x0);
        if (mm.y == nullptr) {
          f.add(q1, mm.unit ? dx : f.mulf(mm.coeff, dx));
          continue;
        }
        const Elt y0 = mm.y[2 * i];
        const Elt dy = f.subf(mm.y[2 * i + 1], y0);
        Elt t1 = f.addf(f.mulf(dx, y0), f.mulf(x0, dy));
        Elt t2 = f.mulf(dx, dy);
        if (!mm.unit) {
          f.mul(t1, mm.coeff);
          f.mul(t2, mm.coeff);
        }
        f.add(q1, t1);
        f.add(q2, t2);
      }
      f.mac(acc[0], e[i], q1);
      if (D == 2) f.mac(acc[1], e[i], q2);
    }
  }

  // One round's sums: ACC[d - 1] += e_i q_d over the pairs BEGIN <= i <
  // END, where q(X) = Q(x0 + X dx) on the operands' rows 2i and 2i + 1
  // (q_0 is not sent). DM > 0 bounds the degree at compile time
  // (fixed-size buffers); DM = 0 is any degree.
  template <unsigned DM>
  void round_sums(const std::vector<Table> &o,
                  const std::vector<Elt> &e, size_t begin, size_t end,
                  std::vector<typename F::Accum> &acc) const {
    constexpr size_t kBuf = DM > 0 ? DM + 1 : 1;
    using Buf = std::conditional_t<(DM > 0), std::array<Elt, kBuf>,
                                   std::vector<Elt>>;
    // The monomials with their operands' rows; coefficient one skips its
    // scaling.
    struct Mono {
      std::vector<const Elt *> x;
      bool unit;
      Elt coeff;
    };
    std::vector<Mono> ms;
    for (const auto &mono : rel.monomials) {
      Mono mm{{}, mono.coeff == f.one(), mono.coeff};
      for (unsigned j : mono.ops) mm.x.push_back(o[j].data());
      ms.push_back(std::move(mm));
    }
    Buf q, p;
    if constexpr (DM == 0) {
      q.resize(D + 1);
      p.resize(D + 1);
    }
    for (size_t i = begin; i < end; ++i) {
      for (unsigned d = 1; d <= D; ++d) q[d] = f.zero();
      for (const Mono &mm : ms) {
        const size_t deg = mm.x.size();
        {
          const Elt x0 = mm.x[0][2 * i];
          const Elt dx = f.subf(mm.x[0][2 * i + 1], x0);
          p[0] = mm.unit ? x0 : f.mulf(mm.coeff, x0);
          p[1] = mm.unit ? dx : f.mulf(mm.coeff, dx);
        }
        for (size_t t = 1; t < deg; ++t) {
          const Elt x0 = mm.x[t][2 * i];
          const Elt dx = f.subf(mm.x[t][2 * i + 1], x0);
          p[t + 1] = f.mulf(p[t], dx);
          for (size_t d = t; d >= 1; --d) {
            p[d] = f.mulf(p[d], x0);
            f.add(p[d], f.mulf(p[d - 1], dx));
          }
          if (t + 1 < deg) p[0] = f.mulf(p[0], x0);
        }
        for (size_t d = 1; d <= deg; ++d) f.add(q[d], p[d]);
      }
      for (unsigned d = 0; d < D; ++d) f.mac(acc[d], e[i], q[d + 1]);
    }
  }

  // Replays the transcript and emits the terminal check row over the pads
  // at witness index BASE + pad; draws u after the terminal values.
  template <class Hash>
  Context rows_of(const Proof &proof, BasicTranscript<Hash> &ts,
                  size_t base) const {
    Context ctx;
    const unsigned w = dom.width();
    std::vector<Elt> rho(layout.logs);
    for (auto &x : rho) x = challenge(ts);
    ts.write(proof.skip.data(), 1, proof.skip.size(), f);
    ctx.r = challenge(ts);
    const auto l = dom.basis(f, dom.points(), ctx.r);
    Expr claim{f.zero(), {}};
    for (size_t j = 0; j < proof.skip.size(); ++j)
      add(claim, message(proof.skip[j], base + j), l[w + j]);
    // claim = prefix (q0 + rho_i sum_d q_d) fixes q0; the next claim is
    //   eq_i(s) claim + prefix eq_i(s) sum_d (s^d - rho_i) q_d.
    Elt prefix = f.one();
    for (size_t i = 0; i < layout.logs; ++i) {
      const auto &q = proof.rounds[i];
      ts.write(q.data(), 1, q.size(), f);
      const Elt s = challenge(ts);
      ctx.s.push_back(s);
      const Elt eq_i = eq(rho[i], s);
      f.mul(prefix, eq_i);
      Expr next{f.zero(), {}};
      add(next, claim, eq_i);
      Elt sd = f.one();
      for (unsigned d = 0; d < D; ++d) {
        f.mul(sd, s);
        add(next, message(q[d], base + round_pad(i, d)),
            f.mulf(prefix, f.subf(sd, rho[i])));
      }
      claim = next;
    }
    // claim - prefix Q(m - P) = 0.
    Expr last = claim;
    add(last, terminal_expr(proof.terminal, base), f.negf(prefix));
    row(ctx, last);
    ts.write(proof.terminal.data(), 1, K, f);
    ctx.terminal = proof.terminal;
    for (unsigned j = 0; j < K; ++j) ctx.u.push_back(challenge(ts));
    return ctx;
  }

  // Instance weights of the opening: eq(s, r) L_z(r_skip) for t = r w + z.
  std::vector<Elt> instance_weights(const Context &ctx) const {
    const unsigned w = dom.width();
    const size_t n = size_t(1) << layout.logs;
    Eqs<F> eqs(layout.logs, n, ctx.s.data(), f);
    const auto lr = dom.basis(f, w, ctx.r);
    std::vector<Elt> out(rows);
    for (size_t t = 0; t < rows; ++t)
      out[t] = f.mulf(eqs.at(t / w), lr[t % w]);
    return out;
  }

  // The opening row: sum_c A_c W_c + sum_j u_j P_j = sum_j u_j m_j - CONSTANT.
  // Appends its sparse pad terms and right-hand side; its dense part (A)
  // is the caller's form.
  void opening_row(Context &ctx, const Elt &constant, size_t base) const {
    Expr e{f.negf(constant), {}};
    for (unsigned j = 0; j < K; ++j)
      add(e, message(ctx.terminal[j], base + layout.terminal + j), ctx.u[j]);
    // e = sum u_j (m_j - P_j) - constant = A.W; as a row, the pads move to
    // the left: A.W + sum u_j P_j = sum u_j m_j - constant.
    for (auto &t : e.terms) t.second = f.negf(t.second);
    for (auto t : e.terms) ctx.a.push_back({ctx.b.size(), t.first, t.second});
    ctx.b.push_back(e.known);
  }

  template <class Hash>
  Elt challenge(BasicTranscript<Hash> &t) const {
    return f.sample([&](size_t n, uint8_t *b) { t.bytes(b, n); });
  }

 private:
  Elt eq(const Elt &rho, const Elt &x) const {
    // 1 - rho - x + 2 rho x
    Elt v = f.subf(f.subf(f.one(), rho), x);
    const Elt rx = f.mulf(rho, x);
    return f.addf(v, f.addf(rx, rx));
  }
  // Q(m - P) as an expression over the pads and their products.
  Expr terminal_expr(const std::vector<Elt> &m, size_t base) const {
    std::map<std::vector<unsigned>, Elt> coef;
    for (const auto &mono : rel.monomials) {
      const auto &fs = mono.ops;
      for (size_t mask = 0; mask < (size_t(1) << fs.size()); ++mask) {
        Elt c = mono.coeff;
        std::vector<unsigned> pads;
        for (size_t t = 0; t < fs.size(); ++t) {
          if ((mask >> t) & 1) {
            pads.push_back(fs[t]);
            c = f.negf(c);
          } else {
            f.mul(c, m[fs[t]]);
          }
        }
        std::sort(pads.begin(), pads.end());
        auto it = coef.find(pads);
        if (it == coef.end())
          coef.emplace(pads, c);
        else
          f.add(it->second, c);
      }
    }
    Expr e{f.zero(), {}};
    for (const auto &[pads, c] : coef) {
      if (pads.empty()) {
        f.add(e.known, c);
        continue;
      }
      const size_t at = pads.size() == 1 ? layout.terminal + pads[0]
                                         : layout.product + product_index(pads);
      e.terms.push_back({base + at, c});
    }
    return e;
  }
  std::vector<std::vector<unsigned>> pad_monomials() const {
    std::vector<std::vector<unsigned>> out;
    auto insert = [&](std::vector<unsigned> m) {
      if (std::find(out.begin(), out.end(), m) == out.end())
        out.push_back(std::move(m));
    };
    for (const auto &mono : rel.monomials) {
      const auto &fs = mono.ops;
      for (size_t mask = 0; mask < (size_t(1) << fs.size()); ++mask) {
        std::vector<unsigned> pads;
        for (size_t t = 0; t < fs.size(); ++t)
          if ((mask >> t) & 1) pads.push_back(fs[t]);
        std::sort(pads.begin(), pads.end());
        for (size_t len = 2; len <= pads.size(); ++len)
          insert(std::vector<unsigned>(pads.begin(), pads.begin() + len));
      }
    }
    std::sort(out.begin(), out.end(), [](const auto &a, const auto &b) {
      return a.size() != b.size() ? a.size() < b.size() : a < b;
    });
    return out;
  }
  size_t product_index(const std::vector<unsigned> &m) const {
    auto it = std::find(products.begin(), products.end(), m);
    check(it != products.end(), "pad monomial");
    return size_t(it - products.begin());
  }
  void add(Expr &dst, const Expr &src, const Elt &factor) const {
    f.add(dst.known, f.mulf(factor, src.known));
    for (auto t : src.terms) dst.terms.push_back({t.first, f.mulf(factor, t.second)});
  }
  Expr message(const Elt &x, size_t at) const {
    // The unmasked value x - P.
    return Expr{x, {{at, f.mone()}}};
  }
  // A row from an expression that must vanish: sum terms w = -known.
  void row(Context &c, const Expr &e) const {
    for (auto t : e.terms) c.a.push_back({c.b.size(), t.first, t.second});
    c.b.push_back(f.negf(e.known));
  }
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_FIELD_SKIP_H_
