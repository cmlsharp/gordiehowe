// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out programs: linear operators the language and its library do not
// have, defined the way a user defines one (linear_operator, linear.h).
//
// hadamard: the Walsh-Hadamard transform of length 32, a constant matrix
// with entries +-1, applied by the fast transform (5 butterfly layers). In
// the sparse form it is given with its sparse rows (emit), so a predicate
// in the circuit can read it; in the dense form it has none and is
// applied in affine rows only, y = H x. The witness is x of 32 values; the statement is y = H x and
// Parseval's identity sum_i (H x)_i^2 = 32 sum_i x_i^2, stated over the
// committed squares s_i = (H x)_i^2.
//
// cyclic_conv: the cyclic convolution y = c * x of length 16 by a public
// kernel c, a matrix that depends on the statement (the operator's
// dependency), applied directly in O(n^2), and described as data by its
// rows over c's coordinates.
//
// One Goldilocks^2 domain holds each.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CUSTOM_OPS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CUSTOM_OPS_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <random>
#include <utility>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::custom_ops {

constexpr size_t kHadamard = 32;
constexpr size_t kConv = 16;

// ------------------------------------------------------------ Hadamard --

// The Walsh-Hadamard transform of length N (a power of two), symmetric, so
// its transpose is itself.
template <class F>
class HadamardOp final : public LinearOperator<F> {
 public:
  using Elt = typename F::Elt;
  HadamardOp(const F &f, size_t n) : f_(f), n_(n) {}
  size_t rows() const override { return n_; }
  size_t cols() const override { return n_; }
  void apply(const Elt *x, Elt *y) const override {
    std::copy(x, x + n_, y);
    for (size_t h = 1; h < n_; h *= 2)
      for (size_t i = 0; i < n_; i += 2 * h)
        for (size_t j = i; j < i + h; ++j) {
          const Elt a = y[j], b = y[j + h];
          y[j] = f_.addf(a, b);
          y[j + h] = f_.subf(a, b);
        }
  }
  void transpose_apply(const Elt *y, Elt *x) const override { apply(y, x); }

 private:
  const F &f_;
  size_t n_;
};

// H_ij = (-1)^popcount(i & j).
inline int hadamard_sign(size_t i, size_t j) {
  return __builtin_popcountll(i & j) % 2 == 0 ? 1 : -1;
}

// EMIT gives the sparse rows; without them the operator is applied in
// affine rows only.
template <class F>
Op<F> Hadamard(const F &f, size_t n, bool emit) {
  if (!emit)
    return linear_operator<F>({
        .name = "hadamard",
        .params = {uint8_t(n)},
        .rows = n,
        .cols = n,
        .make = [n](const F &g) {
          return std::make_shared<HadamardOp<F>>(g, n);
        },
        .field = &f,
    });
  return linear_operator<F>({
      .name = "hadamard",
      .params = {uint8_t(n)},
      .rows = n,
      .cols = n,
      .make = [n](const F &g) { return std::make_shared<HadamardOp<F>>(g, n); },
      .emit =
          [&f, n]() {
            typename OpSpec<F>::SparseRows rows(n);
            for (size_t i = 0; i < n; ++i)
              for (size_t j = 0; j < n; ++j)
                rows[i].push_back(
                    {j, hadamard_sign(i, j) > 0 ? f.one() : f.negf(f.one())});
            return rows;
          },
      .field = &f,
  });
}

template <template <class> class F>
struct HadamardStatement {
  F<std::array<GF::Elt, kHadamard>> y;
};
template <template <class> class F>
struct HadamardWitness {
  F<std::array<uint32_t, kHadamard>> x;
};

// With SPARSE the operator carries its sparse rows and a circuit
// predicate reads it (the squares and Parseval's identity); otherwise it
// is applied in affine rows only.
inline auto hadamard(bool sparse) {
  return compile<HadamardStatement, HadamardWitness>(
      compile_profile(sparse ? "hadamard-sparse" : "hadamard-dense"),
      [sparse](GoldSys &cs, HadamardStatement<In> st, HadamardWitness<In> w) {
        auto &A = cs.domain(gold_profile(), "A");
        const auto H = Hadamard(A.field(), kHadamard, sparse);
        const auto x = A.priv(Subfield<>{}, w.x);
        assert_equal(H(x), st.y.values(A), "transform");
        if (!sparse) return;
        // The squares of the spectrum, through the operator in the circuit.
        const auto squares = A.priv("squares", as_expr(H(x)) * as_expr(H(x)));
        assert_equal(squares.sum(), uint64_t(kHadamard) * (x * x).sum(),
                     "parseval");
      },
      sparse ? "heldout-hadamard-sparse" : "heldout-hadamard-dense");
}

struct HadamardInstance {
  HadamardStatement<Value> statement;
  HadamardWitness<Value> witness;
};
inline HadamardInstance hadamard_instance(uint64_t seed) {
  const GF &f = fields().gf;
  std::mt19937_64 g(seed);
  HadamardInstance in;
  std::vector<GF::Elt> x(kHadamard), y(kHadamard);
  for (size_t i = 0; i < kHadamard; ++i) {
    in.witness.x[i] = uint32_t(g());
    x[i] = f.of_scalar(in.witness.x[i]);
  }
  HadamardOp<GF>(f, kHadamard).apply(x.data(), y.data());
  for (size_t i = 0; i < kHadamard; ++i) in.statement.y[i] = y[i];
  return in;
}

// ---------------------------------------------------- cyclic convolution --

// y = c * x, (c * x)_i = sum_j c_j x_{(i - j) mod n}; the transpose is the
// convolution by c_{(-j) mod n}.
template <class F>
class CyclicConvOp final : public LinearOperator<F> {
 public:
  using Elt = typename F::Elt;
  CyclicConvOp(const F &f, std::vector<Elt> c) : f_(f), c_(std::move(c)) {}
  size_t rows() const override { return c_.size(); }
  size_t cols() const override { return c_.size(); }
  void apply(const Elt *x, Elt *y) const override { conv(c_, x, y); }
  void transpose_apply(const Elt *y, Elt *x) const override {
    const size_t n = c_.size();
    std::vector<Elt> r(n);
    for (size_t j = 0; j < n; ++j) r[(n - j) % n] = c_[j];
    conv(r, y, x);
  }

 private:
  void conv(const std::vector<Elt> &c, const Elt *x, Elt *y) const {
    const size_t n = c.size();
    for (size_t i = 0; i < n; ++i) {
      y[i] = f_.zero();
      for (size_t j = 0; j < n; ++j)
        f_.add(y[i], f_.mulf(c[j], x[(i + n - j) % n]));
    }
  }
  const F &f_;
  std::vector<Elt> c_;
};

// The cyclic convolution by the public value C. Its matrix, M[i][(i - j)
// mod n] = c_j, is described as data by its rows over C's coordinates
// (dep_rows), which the realized program states as `.linear` rows with
// `Coef.node`.
template <class F, class T, class Pl>
Op<F> CyclicConv(Ref<F, T, Pl> c) {
  const size_t n = c.n;
  return linear_operator<F>({
      .name = "cyclic_conv",
      .rows = n,
      .cols = n,
      .deps = depends_on(c),
      .make =
          [](const F &f, const std::vector<typename F::Elt> &cv) {
            return std::make_shared<CyclicConvOp<F>>(f, cv);
          },
      .dep_rows =
          [n]() {
            typename OpSpec<F>::DepRows rows(n);
            for (size_t i = 0; i < n; ++i)
              for (size_t j = 0; j < n; ++j) {
                typename OpSpec<F>::DepCoef k;
                k.is_const = false;
                k.dep = 0;
                k.at = j;
                rows[i].push_back({(i + n - j) % n, k});
              }
            return rows;
          },
  });
}

template <template <class> class F>
struct ConvStatement {
  F<std::array<uint32_t, kConv>> kernel;
  F<std::array<GF::Elt, kConv>> y;
};
template <template <class> class F>
struct ConvWitness {
  F<std::array<uint32_t, kConv>> x;
};

inline auto cyclic_conv() {
  return compile<ConvStatement, ConvWitness>(
      compile_profile("cyclic-conv"),
      [](GoldSys &cs, ConvStatement<In> st, ConvWitness<In> w) {
        auto &A = cs.domain(gold_profile(), "A");
        const auto x = A.priv(Subfield<>{}, w.x);
        const auto c = st.kernel.values(A);
        assert_equal(CyclicConv(c)(x), st.y.values(A), "conv");
      },
      "heldout-cyclic-conv");
}

struct ConvInstance {
  ConvStatement<Value> statement;
  ConvWitness<Value> witness;
};
inline ConvInstance conv_instance(uint64_t seed) {
  const GF &f = fields().gf;
  std::mt19937_64 g(seed);
  ConvInstance in;
  std::vector<GF::Elt> c(kConv), x(kConv), y(kConv);
  for (size_t i = 0; i < kConv; ++i) {
    in.statement.kernel[i] = uint32_t(g());
    in.witness.x[i] = uint32_t(g());
    c[i] = f.of_scalar(in.statement.kernel[i]);
    x[i] = f.of_scalar(in.witness.x[i]);
  }
  CyclicConvOp<GF>(f, c).apply(x.data(), y.data());
  for (size_t i = 0; i < kConv; ++i) in.statement.y[i] = y[i];
  return in;
}

}  // namespace proofs::gordiehowe::heldout::custom_ops

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CUSTOM_OPS_H_
