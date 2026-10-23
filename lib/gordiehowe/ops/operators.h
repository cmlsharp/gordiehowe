// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the built-in algebraic linear operators: negacyclic convolution
// and the polynomial matrix-vector product in coefficient or NTT form,
// staged NTTs, and the MAC's chunk convolution. Each is a linear_operator
// (linear.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_OPERATORS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_OPERATORS_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iterator>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "circuits/mac/linear_mac.h"
#include "circuits/ntt/emulated_signature.h"
#include "circuits/ntt/host_ntt.h"
#include "circuits/ntt/ntt_gadget.h"
#include "gordiehowe/core.h"
#include "gordiehowe/linear.h"
#include "gordiehowe/ops/ntt.h"
#include "util/panic.h"

namespace proofs::gordiehowe::ops {
// Negacyclic convolution by a public vector h of length n:
//   (h * x)[j] = sum_{i+k=j} h[i] x[k] - sum_{i+k=j+n} h[i] x[k].
// The transpose is negacyclic convolution by [h[0], -h[n-1], ..., -h[1]].
// Direct O(n^2) evaluation: the reference for the transform-based operator.
template <class F>
class NegacyclicConvReference final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  NegacyclicConvReference(const F &f, std::vector<Elt> h)
      : f_(f), h_(std::move(h)) {}
  size_t rows() const override { return h_.size(); }
  size_t cols() const override { return h_.size(); }
  void apply(const Elt *x, Elt *y) const override { conv(h_, x, y); }
  void transpose_apply(const Elt *y, Elt *x) const override {
    const size_t n = h_.size();
    std::vector<Elt> ht(n);
    ht[0] = h_[0];
    for (size_t i = 1; i < n; ++i) ht[i] = f_.negf(h_[n - i]);
    conv(ht, y, x);
  }

 private:
  void conv(const std::vector<Elt> &h, const Elt *x, Elt *y) const {
    const size_t n = h.size();
    for (size_t j = 0; j < n; ++j) y[j] = f_.zero();
    for (size_t i = 0; i < n; ++i)
      for (size_t k = 0; k < n; ++k) {
        const Elt p = f_.mulf(h[i], x[k]);
        if (i + k < n)
          f_.add(y[i + k], p);
        else
          f_.sub(y[i + k - n], p);
      }
  }
  const F &f_;
  std::vector<Elt> h_;
};

// An operator evaluated in the spectrum of one negacyclic transform: its
// transpose starts with a forward transform of each of its output
// polynomials. TransposeRun shares those transforms between the terms of
// one affine row (native_linear::Relation::extra's sharing: one forward
// transform per output row, one inverse per input polynomial).
template <class F>
class SpectralOperator : public LinearOperator<F> {
 public:
  using Elt = typename F::Elt;
  // The transform, or null when the operator runs its O(n^2) reference.
  virtual const NegacyclicNtt<F> *ntt() const = 0;
  // x = M^T y, given YHAT: the forward transform of each length-n block of
  // y (rows() entries).
  virtual void transpose_from_spectra(const Elt *yhat, Elt *x) const = 0;
};

// The transform of length n over F with root PSI (the scheme root of
// FieldNtt by default), or null when F has none.
template <class F>
std::shared_ptr<const NegacyclicNtt<F>> negacyclic_ntt(
    const F &f, size_t n, std::optional<typename F::Elt> psi = std::nullopt) {
  if constexpr (kFieldNtt<F>) {
    if (!psi) psi = FieldNtt<F>::scheme_psi(f, n);
    if (psi) return std::make_shared<const NegacyclicNtt<F>>(f, n, *psi);
  }
  return nullptr;
}

// PolyMatVec: y_i = sum_j a_ij * x_j in F[X]/(X^n + 1), for a public matrix
// A of K x L polynomials (K*L*n entries, row-major [K][L][n], in FORM),
// input x of L polynomials and output y of K. NegacyclicConv is the case
// K = L = 1, PolyBroadcast the case L = 1.
//
// With a transform: apply runs L forward transforms and K inverse ones,
// transpose_apply K forward and L inverse ones, and the pointwise products
// multiply by base-field scalars when A lies in the base field. The adjoint
// of a_ij is a_ij*(X) = a_ij(X^-1), whose spectrum is a_ij's reversed
// (native_linear's kNtt reading), so one spectrum per entry serves both.
// The constructor transforms a coefficient-form A once per instance (in the
// base field when it lies there). Without a transform, the direct O(n^2)
// reference (coefficient form only).
template <class F>
class PolyMatVecOperator : public SpectralOperator<F> {
 public:
  using Elt = typename F::Elt;

  PolyMatVecOperator(const F &f, size_t K, size_t L, size_t n,
                     const std::vector<Elt> &a, Form form,
                     std::shared_ptr<const NegacyclicNtt<F>> ntt)
      : f_(f), K_(K), L_(L), n_(n), ntt_(std::move(ntt)) {
    check(a.size() == K * L * n, "PolyMatVec: matrix size");
    if (ntt_ != nullptr) {
      if constexpr (kFieldNtt<F>) {
        check(ntt_->n() == n, "PolyMatVec: transform length");
        for (size_t e = 0; e < K * L; ++e)
          spectra_.push_back(
              KernelSpectrum<F>::of(*ntt_, a.data() + e * n, form));
      }
      return;
    }
    check(form == Form::kCoefficients,
          "PolyMatVec: an NTT-form operand needs a transform");
    for (size_t e = 0; e < K * L; ++e)
      reference_.push_back(std::make_unique<NegacyclicConvReference<F>>(
          f, std::vector<Elt>(a.begin() + e * n, a.begin() + (e + 1) * n)));
  }
  size_t rows() const override { return K_ * n_; }
  size_t cols() const override { return L_ * n_; }
  const NegacyclicNtt<F> *ntt() const override { return ntt_.get(); }

  void apply(const Elt *x, Elt *y) const override {
    if (ntt_ == nullptr) {
      reference(x, y, false);
      return;
    }
    if constexpr (kFieldNtt<F>) {
      std::vector<std::vector<Elt>> xhat(L_);
      for (size_t j = 0; j < L_; ++j) {
        xhat[j].assign(x + j * n_, x + (j + 1) * n_);
        ntt_->forward(xhat[j]);
      }
      std::vector<Elt> acc(n_);
      for (size_t i = 0; i < K_; ++i) {
        std::fill(acc.begin(), acc.end(), f_.zero());
        for (size_t j = 0; j < L_; ++j)
          spectra_[i * L_ + j].mul_add(f_, xhat[j].data(), acc.data(), n_,
                                       false);
        ntt_->inverse(acc);
        std::copy(acc.begin(), acc.end(), y + i * n_);
      }
    }
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    if (ntt_ == nullptr) {
      reference(y, x, true);
      return;
    }
    if constexpr (kFieldNtt<F>) {
      std::vector<Elt> yhat(y, y + K_ * n_), b(n_);
      for (size_t i = 0; i < K_; ++i) {
        std::copy(yhat.begin() + i * n_, yhat.begin() + (i + 1) * n_,
                  b.begin());
        ntt_->forward(b);
        std::copy(b.begin(), b.end(), yhat.begin() + i * n_);
      }
      transpose_from_spectra(yhat.data(), x);
    }
  }
  void transpose_from_spectra(const Elt *yhat, Elt *x) const override {
    if constexpr (kFieldNtt<F>) {
      check(ntt_ != nullptr, "PolyMatVec: spectra without a transform");
      std::vector<Elt> acc(n_);
      for (size_t j = 0; j < L_; ++j) {
        std::fill(acc.begin(), acc.end(), f_.zero());
        for (size_t i = 0; i < K_; ++i)
          spectra_[i * L_ + j].mul_add(f_, yhat + i * n_, acc.data(), n_,
                                       true);
        ntt_->inverse(acc);
        std::copy(acc.begin(), acc.end(), x + j * n_);
      }
    }
  }

 private:
  // y = A x (or x = A^T y) by the references, block by block.
  void reference(const Elt *in, Elt *out, bool transpose) const {
    const size_t no = transpose ? L_ : K_, ni = transpose ? K_ : L_;
    std::vector<Elt> t(n_);
    for (size_t o = 0; o < no; ++o) {
      for (size_t k = 0; k < n_; ++k) out[o * n_ + k] = f_.zero();
      for (size_t i = 0; i < ni; ++i) {
        const auto &op = transpose ? reference_[i * L_ + o]
                                   : reference_[o * L_ + i];
        if (transpose)
          op->transpose_apply(in + i * n_, t.data());
        else
          op->apply(in + i * n_, t.data());
        for (size_t k = 0; k < n_; ++k) f_.add(out[o * n_ + k], t[k]);
      }
    }
  }

  const F &f_;
  size_t K_, L_, n_;
  std::shared_ptr<const NegacyclicNtt<F>> ntt_;
  std::vector<KernelSpectrum<F>> spectra_;
  std::vector<std::unique_ptr<NegacyclicConvReference<F>>> reference_;
};

// Negacyclic convolution by a public polynomial h: the NTT operator of
// PolyMatVec at K = L = 1, with the scheme root (any root gives the same
// coefficient-form operator), or the reference when F has no transform of
// length n.
template <class F>
class NegacyclicConvOperator final : public PolyMatVecOperator<F> {
 public:
  NegacyclicConvOperator(const F &f, const std::vector<typename F::Elt> &h)
      : PolyMatVecOperator<F>(f, 1, 1, h.size(), h, Form::kCoefficients,
                              negacyclic_ntt(f, h.size())) {}
};

// The transposes of the terms of one affine row, run with the forward
// transforms of the row's multipliers shared: a term whose last operator is
// spectral starts from the cached spectrum of its row's multipliers under
// that transform. One instance serves one accumulation (one multiplier
// vector).
template <class F>
class TransposeRun {
 public:
  using Elt = typename F::Elt;
  using Ops = std::vector<std::shared_ptr<const LinearOperator<F>>>;

  // (ops.back() ... ops.front())^T applied to LAM, the OUT_N multipliers of
  // the term's row.
  std::vector<Elt> run(const Ops &ops, const Elt *lam, size_t out_n) {
    size_t k = ops.size();
    return run_to(ops, lam, out_n, k);
  }
  // A += scale (ops.back() ... ops.front())^T LAM, A of the term's input
  // length: the first operator's transpose accumulates into A directly
  // (LinearOperator::transpose_accumulate).
  void accumulate(const F &f, const Ops &ops, const Elt *lam, size_t out_n,
                  const Elt &scale, Elt *A) {
    size_t k = ops.size();
    if (k == 0) {
      for (size_t j = 0; j < out_n; ++j) f.add(A[j], f.mulf(scale, lam[j]));
      return;
    }
    // Every operator but the first; a spectral last operator may take it.
    std::vector<Elt> y = run_to(ops, lam, out_n, k, 1);
    if (k == 0) {
      for (size_t j = 0; j < y.size(); ++j) f.add(A[j], f.mulf(scale, y[j]));
      return;
    }
    ops[0]->transpose_accumulate(f, y.data(), scale, A);
  }
  size_t forward_transforms() const { return transforms_; }

 private:
  // Transposes ops[K-1] down to ops[KEEP] from LAM, leaving K at KEEP (at
  // KEEP - 1 when a spectral operator ends the chain at KEEP - 1).
  std::vector<Elt> run_to(const Ops &ops, const Elt *lam, size_t out_n,
                          size_t &k, size_t keep = 0) {
    std::vector<Elt> y(lam, lam + out_n);
    if constexpr (kFieldNtt<F>) {
      if (k == 0) return y;
      const auto *sp = dynamic_cast<const SpectralOperator<F> *>(ops[k - 1].get());
      if (sp != nullptr && sp->ntt() != nullptr) {
        const auto &yhat = forward(*sp->ntt(), lam, out_n);
        std::vector<Elt> x(sp->cols());
        sp->transpose_from_spectra(yhat.data(), x.data());
        y = std::move(x);
        --k;
      }
    }
    while (k > keep) {
      --k;
      std::vector<Elt> x(ops[k]->cols());
      ops[k]->transpose_apply(y.data(), x.data());
      y = std::move(x);
    }
    return y;
  }

  struct Entry {
    const Elt *lam;
    size_t n;
    const NegacyclicNtt<F> *ntt;
    std::vector<Elt> yhat;
  };
  const std::vector<Elt> &forward(const NegacyclicNtt<F> &ntt, const Elt *lam,
                                  size_t out_n) {
    for (const auto &e : cache_)
      if (e.lam == lam && e.n == out_n && e.ntt->same(ntt)) return e.yhat;
    Entry e{lam, out_n, &ntt, std::vector<Elt>(lam, lam + out_n)};
    if constexpr (kFieldNtt<F>) {
      const size_t n = ntt.n();
      std::vector<Elt> b(n);
      for (size_t at = 0; at < out_n; at += n) {
        std::copy(e.yhat.begin() + at, e.yhat.begin() + at + n, b.begin());
        ntt.forward(b);
        std::copy(b.begin(), b.end(), e.yhat.begin() + at);
        ++transforms_;
      }
    }
    cache_.push_back(std::move(e));
    return cache_.back().yhat;
  }
  std::vector<Entry> cache_;
  size_t transforms_ = 0;
};

namespace poly_detail {
template <class F>
void put_elt(std::vector<uint8_t> &out, const F &f, const typename F::Elt &x) {
  uint8_t b[F::kBytes];
  f.to_bytes_field(b, x);
  out.insert(out.end(), b, b + F::kBytes);
}
// The transform a spectral operator over F of length n instantiates with,
// for an operand in FORM: a kNtt operand requires one, and fixes its root.
template <class F>
std::optional<typename F::Elt> spectral_root(const F &f, size_t n, Form form,
                                             std::optional<typename F::Elt> psi,
                                             const std::string &who) {
  if (form == Form::kCoefficients) return psi;
  if constexpr (kFieldNtt<F>) {
    if (!psi) psi = FieldNtt<F>::scheme_psi(f, n);
    if (psi) {
      if (!f.in_subfield(*psi) ||
          linear_mac::power(f, *psi, n) != f.mone())
        fail(who + ": psi is not a primitive 2n-th root of the base field");
      return psi;
    }
  }
  fail(who + ": an NTT-form operand needs a transform of length " +
       std::to_string(n) + " over the field");
}
// The spec of PolyMatVec over a public node A of K*L*n entries.
template <class F>
Op<F> poly_mat_vec(std::string name, Ref<F> a, size_t K, size_t L, Form form,
                   std::optional<typename F::Elt> psi, bool legacy_params,
                   std::optional<Bound> entry_bound = std::nullopt) {
  if (K == 0 || L == 0 || a.n == 0 || a.n % (K * L) != 0)
    fail(name + ": the operand's length is not K*L*n");
  const size_t n = a.n / (K * L);
  const F *f = a.f;
  psi = spectral_root(*f, n, form, psi, name);
  using V = std::vector<typename F::Elt>;
  LinearOpDef<F> d{
      .name = std::move(name),
      .rows = K * n,
      .cols = L * n,
      .deps = depends_on(a),
      .make = [K, L, n, form, psi](const F &f, const V &v) {
        return std::make_shared<PolyMatVecOperator<F>>(
            f, K, L, n, v, form, negacyclic_ntt(f, n, psi));
      },
  };
  // Coefficient-form NegacyclicConv keeps its parameterless digest.
  if (!legacy_params) {
    put_u64(d.params, K);
    put_u64(d.params, L);
    put_u64(d.params, n);
    put_u64(d.params, static_cast<uint64_t>(form));
    d.out_dims = {K, n};
  }
  if (form == Form::kNtt) put_elt(d.params, *f, *psi);
  if (entry_bound) {
    // Coefficients below B: an integer matrix whose rows' absolute values
    // sum to at most L n (B - 1) (each output coefficient reads every input
    // coefficient once, negated past the wrap).
    const Bound B = *entry_bound;
    if (form != Form::kCoefficients)
      fail(d.name + ": an entry bound needs the coefficient form");
    if (B < 1 || B > (Bound(1) << 62))
      fail(d.name + ": the entry bound is not in [1, 2^62]");
    put_str(d.params, "entry_bound");
    put_bound(d.params, B);
    d.abs_row_sum = Bound(L) * Bound(n) * (B - 1);
    d.bound_terms = {{"entryBound", B},
                     {"K", Bound(K)},
                     {"L", Bound(L)},
                     {"n", Bound(n)},
                     {"absRowSum", d.abs_row_sum}};
    d.make = [K, L, n, form, psi, B, nm = d.name](const F &f, const V &v) {
      for (const auto &x : v)
        if (!subfield_contains(f, x) || nat_of(f, x) >= B)
          throw std::runtime_error(nm + ": a public coefficient is not an "
                                   "integer below its entry bound " +
                                   bound_str(B));
      return std::make_shared<PolyMatVecOperator<F>>(
          f, K, L, n, v, form, negacyclic_ntt(f, n, psi));
    };
  }
  return linear_operator<F>(std::move(d));
}
// The dims of an operator's public operand: rank RANK, a missing leading
// axis read as 1 (a [n] handle is one polynomial).
template <class F>
std::vector<size_t> operand_dims(const Ref<F> &a, size_t rank,
                                 const std::string &who) {
  auto d = a.dims();
  if (d.size() > rank)
    fail(who + ": the operand has rank " + std::to_string(d.size()) +
         ", at most " + std::to_string(rank) + " expected");
  while (d.size() < rank) d.insert(d.begin(), 1);
  return d;
}
}  // namespace poly_detail

// The coefficients of a public coefficient-form operand of PolyMatVec or
// PolyBroadcast are canonical integers below BOUND (EntryBound{q} for keys
// reduced mod q): the operator then bounds its rows for interval
// propagation (OpSpec::abs_row_sum), its digest records the bound, and
// instantiation refuses a coefficient outside it.
struct EntryBound {
  Bound bound;
};

// A public polynomial given by its spectrum: evaluations at psi^(2 brv(k)+1)
// (ntt.h), psi the scheme root of FieldNtt unless given. Spectrum{key} takes
// a public handle (an operator parameter: a committed key is a C++ compile
// error).
template <class F>
struct Spectrum {
  Ref<F> key;
  std::optional<typename F::Elt> psi;
  template <class T, class P>
  Spectrum(Ref<F, T, P> k,  // NOLINT
           std::optional<typename F::Elt> p = std::nullopt)
      : key(k), psi(p) {
    check_operator_parameter<P>();
  }
};
template <class F, class T, class P>
Spectrum(Ref<F, T, P>) -> Spectrum<F>;
template <class F, class T, class P>
Spectrum(Ref<F, T, P>, typename F::Elt) -> Spectrum<F>;

// Negacyclic convolution by a public polynomial h of length n:
//   (h * x)[j] = sum_{i+k=j} h[i] x[k] - sum_{i+k=j+n} h[i] x[k],
// by NTT over any field with a transform of length n (ntt.h), and by the
// O(n^2) reference otherwise.
template <class F, class T, class P>
Op<F> NegacyclicConv(Ref<F, T, P> h) {
  check_operator_parameter<P>();
  return poly_detail::poly_mat_vec<F>("negacyclic_conv", Ref<F>(h), 1, 1,
                                      Form::kCoefficients, std::nullopt, true);
}
// The same with h's coefficients below EB.bound (EntryBound): interval
// propagation reads the operator.
template <class F, class T, class P>
Op<F> NegacyclicConv(Ref<F, T, P> h, EntryBound eb) {
  check_operator_parameter<P>();
  return poly_detail::poly_mat_vec<F>("negacyclic_conv", Ref<F>(h), 1, 1,
                                      Form::kCoefficients, std::nullopt, true,
                                      eb.bound);
}
// The same with h given in NTT form: no transform of h at instantiation,
// and the root enters the digest.
template <class F>
Op<F> NegacyclicConv(Spectrum<F> h) {
  return poly_detail::poly_mat_vec<F>("negacyclic_conv", h.key, 1, 1,
                                      Form::kNtt, h.psi, true);
}
// PolyMatVec(a, form): [L][n] -> [K][n], y_i = sum_j a_ij * x_j, for a
// public matrix A of shape [K][L][n] in FORM. On x of shape [..., L, n] it
// batches over the leading axes.
template <class F, class T, class P>
Op<F> PolyMatVec(Ref<F, T, P> a, Form form,
                 std::optional<typename F::Elt> psi = std::nullopt) {
  check_operator_parameter<P>();
  const auto d = poly_detail::operand_dims<F>(a, 3, "PolyMatVec");
  return poly_detail::poly_mat_vec<F>("poly_mat_vec", Ref<F>(a), d[0], d[1],
                                      form, psi, false);
}
// PolyBroadcast(t, form): [n] -> [K][n], y_i = t_i * x, for a public vector
// of K polynomials, shape [K][n], in FORM.
template <class F, class T, class P>
Op<F> PolyBroadcast(Ref<F, T, P> t, Form form,
                    std::optional<typename F::Elt> psi = std::nullopt) {
  check_operator_parameter<P>();
  const auto d = poly_detail::operand_dims<F>(t, 2, "PolyBroadcast");
  return poly_detail::poly_mat_vec<F>("poly_broadcast", Ref<F>(t), d[0], 1,
                                      form, psi, false);
}
// The same two in coefficient form, the operand's coefficients below
// EB.bound (EntryBound): interval propagation reads the operator.
template <class F, class T, class P>
Op<F> PolyMatVec(Ref<F, T, P> a, EntryBound eb) {
  check_operator_parameter<P>();
  const auto d = poly_detail::operand_dims<F>(a, 3, "PolyMatVec");
  return poly_detail::poly_mat_vec<F>("poly_mat_vec", Ref<F>(a), d[0], d[1],
                                      Form::kCoefficients, std::nullopt, false,
                                      eb.bound);
}
template <class F, class T, class P>
Op<F> PolyBroadcast(Ref<F, T, P> t, EntryBound eb) {
  check_operator_parameter<P>();
  const auto d = poly_detail::operand_dims<F>(t, 2, "PolyBroadcast");
  return poly_detail::poly_mat_vec<F>("poly_broadcast", Ref<F>(t), d[0], 1,
                                      Form::kCoefficients, std::nullopt, false,
                                      eb.bound);
}

// ------------------------------------------------------ staged transforms --

// Stage boundaries of an in-circuit transform: bit s requests a layer
// boundary (ntt_gadget::share) after butterfly stage s. Without boundaries
// the compiler folds the butterfly network into the layer that reads it, n^2
// terms per transform (ntt_gadget.h).
struct Stages {
  // A boundary every PERIOD stages, from stage 0 (ntt_gadget::stage_mask).
  static Stages every(size_t period) { return Stages{period, 0, false}; }
  // An explicit mask.
  static Stages masked(uint64_t mask) { return Stages{0, mask, true}; }
  uint64_t mask(size_t n) const {
    return explicit_mask ? bits : ntt_gadget::stage_mask(n, period);
  }
  size_t period = 2;
  uint64_t bits = 0;
  bool explicit_mask = false;
};

// The spectrum order of a staged transform.
//  - kScheme: a_hat[k] = a(psi^(2 brv(k) + 1)), the order of ntt.h, by
//    Cooley-Tukey butterflies with zetas[i] = psi^brv(i) and no separate
//    twist (FIPS 204 Algorithm 41 at psi = 1753; falcon_ntt_ref at
//    falcon_root_2n). The ML-DSA native ring's staged_ntt.
//  - kNatural: a_hat[k] = a(psi^(2k + 1)), by ntt_gadget::transform with the
//    psi twist and natural order (the carrier rings).
enum class NttOrder : uint8_t { kScheme = 0, kNatural = 1 };

// A staged negacyclic transform of length n with root psi: its circuit
// (forward), its host evaluation (apply), and the transpose.
template <class F>
struct StagedNtt {
  using Elt = typename F::Elt;
  const F *f = nullptr;
  size_t n = 0;
  Elt psi;
  NttOrder order = NttOrder::kScheme;
  uint64_t mask = 0;

  // The circuit: A (n wires, coefficients) becomes its spectrum, with a
  // boundary after each stage the mask names.
  template <class LC>
  void forward(const LC &lc, std::vector<typename LC::EltW> &a) const {
    check(a.size() == n, "staged NTT operand size");
    if (order == NttOrder::kNatural) {
      ntt_gadget::Sharing sh;
      sh.forward = mask;
      ntt_gadget::transform(lc, a, f->mulf(psi, psi), /*inverse=*/false, sh,
                            psi);
      return;
    }
    const size_t logn = ntt_log2(n);
    uint64_t m = mask;
    size_t z = 1;
    for (size_t len = n / 2; len; len /= 2) {
      for (size_t start = 0; start < n; start += 2 * len) {
        const Elt zeta = linear_mac::power(*f, psi, ntt_brv(z, logn));
        ++z;
        for (size_t j = start; j < start + len; ++j) {
          const auto u = a[j];
          const auto zv = lc.mul(zeta, a[j + len]);
          a[j] = lc.add(u, zv);
          a[j + len] = lc.sub(u, zv);
        }
      }
      if (m & 1) ntt_gadget::share_all(lc, a);
      m >>= 1;
    }
  }
  // Host forward transform, in this transform's order.
  void apply(std::vector<Elt> &a) const {
    if constexpr (kFieldNtt<F>) {
      NegacyclicNtt<F>(*f, n, psi).forward(a);
      if (order == NttOrder::kNatural) permute(a);
    } else {
      fail("staged NTT: no host transform over this field");
    }
  }
  // x = M^T y for M the transform matrix, M[k][i] = z_k^i (z_k the k-th
  // evaluation point): x_0 = n (M^-1 y)_0 and x_i = -n (M^-1 y)_(n-i), since
  // z_k^n = -1.
  void transpose(std::vector<Elt> &y) const {
    if constexpr (kFieldNtt<F>) {
      if (order == NttOrder::kNatural) permute(y);
      NegacyclicNtt<F>(*f, n, psi).inverse(y);
      const Elt nn = f->of_scalar(static_cast<uint64_t>(n));
      std::vector<Elt> x(n);
      x[0] = f->mulf(nn, y[0]);
      for (size_t i = 1; i < n; ++i) x[i] = f->negf(f->mulf(nn, y[n - i]));
      y = std::move(x);
    } else {
      fail("staged NTT: no host transform over this field");
    }
  }

 private:
  // Scheme order <-> natural order: the bit reversal (an involution).
  void permute(std::vector<Elt> &a) const {
    const size_t logn = ntt_log2(n);
    for (size_t i = 0; i < n; ++i) {
      const size_t j = ntt_brv(i, logn);
      if (i < j) std::swap(a[i], a[j]);
    }
  }
};

template <class F>
class StagedNttOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  explicit StagedNttOperator(std::shared_ptr<const StagedNtt<F>> t)
      : t_(std::move(t)) {}
  size_t rows() const override { return t_->n; }
  size_t cols() const override { return t_->n; }
  void apply(const Elt *x, Elt *y) const override {
    std::vector<Elt> a(x, x + t_->n);
    t_->apply(a);
    std::copy(a.begin(), a.end(), y);
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    std::vector<Elt> a(y, y + t_->n);
    t_->transpose(a);
    std::copy(a.begin(), a.end(), x);
  }

 private:
  std::shared_ptr<const StagedNtt<F>> t_;
};

// Ntt(f, n, psi, stages, order): the staged negacyclic transform of length
// n as an operator. Affine rows evaluate it on the host. A circuit reads it
// only through ntt_gadget's staged butterflies (expand_operator in expr.h,
// and SpectralProduct, SpectralMatVec, assert_spectral in spectral.h); a
// dense expansion through OpSpec::emit is refused at compile with a
// CompileError.
template <class F>
Op<F> Ntt(const F &f, size_t n, typename F::Elt psi, Stages st,
          NttOrder order = NttOrder::kScheme) {
  if (n < 2 || !ntt_detail::power_of_two(n))
    fail("Ntt: the length is not a power of two");
  if (!f.in_subfield(psi) || linear_mac::power(f, psi, n) != f.mone())
    fail("Ntt: psi is not a primitive 2n-th root of the base field");
  auto t = std::make_shared<StagedNtt<F>>();
  t->f = &f;
  t->n = n;
  t->psi = psi;
  t->order = order;
  t->mask = st.mask(n);
  if ((t->mask >> ntt_log2(n)) != 0) fail("Ntt: a boundary past the last stage");
  std::vector<uint8_t> params;
  put_u64(params, n);
  put_u64(params, static_cast<uint64_t>(order));
  put_u64(params, t->mask);
  poly_detail::put_elt(params, f, psi);
  return linear_operator<F>({
      .name = "ntt",
      .params = std::move(params),
      .rows = n,
      .cols = n,
      .make = [t](const F &) {
        return std::make_shared<StagedNttOperator<F>>(t);
      },
      .emit = [n]() -> typename OpSpec<F>::SparseRows {
        fail("staged transform 'ntt' (length " + std::to_string(n) +
             ") would expand as a dense matrix through OpSpec::emit; a "
             "circuit reads it through its staged butterflies "
             "(SpectralProduct, SpectralMatVec, assert_spectral)");
      },
      .staged = t,
      .field = &f,
  });
}
// The scheme transform of F at length n: Ntt at FieldNtt's scheme root, in
// scheme order (FIPS 204 over the ML-DSA field, falcon_ntt_ref over the
// Falcon field).
template <class F>
Op<F> SchemeNtt(const F &f, size_t n, Stages st) {
  std::optional<typename F::Elt> psi;
  if constexpr (kFieldNtt<F>) psi = FieldNtt<F>::scheme_psi(f, n);
  if (!psi) fail("SchemeNtt: no transform of this length over the field");
  return Ntt(f, n, *psi, st, NttOrder::kScheme);
}

// MACConv(r): the integer convolution by the chunk powers r_c of the binary
// field M = GF(2)[x]/(phi) of w bits, the paper's Conv(r) (def:macconv).
// Input: nch*w values X[c*w + i], the coefficient of x^i in chunk c (the
// polynomial basis of M). Output: w integer accumulators
//   acc = reduce(sum_c X_c * R_c),
// where R_c is the 0/1 coefficient vector of r_c, * is the product of
// integer polynomials (degree <= 2w-2), and reduce replaces each monomial
// x^k with k >= w, once, by the 0/1 coefficient vector of x^k mod phi: it
// adds a[k] to a[b] for each b in the support of x^k mod phi. The matrix
// entry for chunk c, input i and row b is
//   #{j : R_c[j] = 1, i + j = b} + #{j : R_c[j] = 1, i + j >= w, b in
//   supp(x^(i+j) mod phi)},
// at most w, so for 0/1 inputs acc[b] mod 2 = bit_b(sum_c X_c * r_c).

// The taps of M: the support of x^w reduced in M.
template <class MF>
std::vector<size_t> mac_taps(const MF &mf) {
  const auto x = mf.of_scalar_field(0b10);
  auto p = mf.one();
  for (size_t i = 0; i < MF::kBits; ++i) p = mf.mulf(p, x);
  std::vector<size_t> taps;
  for (size_t b = 0; b < MF::kBits; ++b)
    if (p[b]) taps.push_back(b);
  return taps;
}

// The reduction table of M: entry k - w, for k = w..2w-2, is the support of
// x^k mod phi, ascending, for phi = x^w + sum_{d in taps} x^d. It multiplies
// x^w mod phi by x in GF(2)[x]/(phi) w - 2 times.
inline std::vector<std::vector<size_t>> mac_reduction(
    size_t w, const std::vector<size_t> &taps) {
  std::vector<uint8_t> v(w, 0);
  for (size_t d : taps) v[d] = 1;
  std::vector<std::vector<size_t>> red;
  red.reserve(w - 1);
  for (size_t k = w; k <= 2 * w - 2; ++k) {
    if (k > w) {
      const uint8_t top = v[w - 1];
      for (size_t b = w - 1; b > 0; --b) v[b] = v[b - 1];
      v[0] = 0;
      if (top)
        for (size_t d : taps) v[d] ^= 1;
    }
    std::vector<size_t> support;
    for (size_t b = 0; b < w; ++b)
      if (v[b]) support.push_back(b);
    red.push_back(std::move(support));
  }
  return red;
}

// reduce over the integers, in place; a has 2w-1 entries and keeps w. RED is
// mac_reduction(w, taps).
inline void mac_reduce(std::vector<uint64_t> &a, size_t w,
                       const std::vector<std::vector<size_t>> &red) {
  for (size_t k = w; k <= 2 * w - 2; ++k)
    for (size_t b : red[k - w]) a[b] += a[k];
  a.resize(w);
}

// reduce over a field F, in place; a has at least 2w-1 entries and keeps w.
template <class F>
void mac_reduce(const F &f, std::vector<typename F::Elt> &a, size_t w,
                const std::vector<std::vector<size_t>> &red) {
  for (size_t k = w; k <= 2 * w - 2; ++k)
    for (size_t b : red[k - w]) f.add(a[b], a[k]);
  a.resize(w);
}

// The transpose of reduce over F: 2w entries, y[b] at b < w, at k = w..2w-2
// the sum of y[b] over the support of x^k mod phi, and 0 at 2w-1.
template <class F>
std::vector<typename F::Elt> mac_transpose_reduce(
    const F &f, const typename F::Elt *y, size_t w,
    const std::vector<std::vector<size_t>> &red) {
  std::vector<typename F::Elt> a(2 * w, f.zero());
  std::copy(y, y + w, a.begin());
  for (size_t k = w; k <= 2 * w - 2; ++k)
    for (size_t b : red[k - w]) f.add(a[k], y[b]);
  return a;
}

// The integer accumulators reduce(sum_c X_c * R_c) of 0/1 inputs: X holds
// nch chunks of w values (zero past the input), R the chunk powers. These are
// the values of MACConv(r)(X) on 0/1 inputs, computed with no field
// arithmetic: coefficient k of X_c * R_c is the popcount of X_c AND the
// reversal of R_c shifted by k, over 64-bit words (the prover's generator).
// Every accumulator must lie below LIMIT (the characteristic of the field
// that receives them, which would otherwise reduce it): a larger one is a
// std::runtime_error, raised after the sums. The inputs' bits enter by
// shifts and the popcount is ct::popcount's (no table, no library call).
template <class MF>
std::vector<uint64_t> mac_integer_accumulators(
    const std::vector<uint8_t> &x, const std::vector<typename MF::Elt> &r,
    const std::vector<size_t> &taps, Bound limit = kBoundMax) {
  constexpr size_t w = MF::kBits, nw = w / 64;
  static_assert(w % 64 == 0, "the MAC width is a multiple of 64 bits");
  std::vector<uint64_t> sum(2 * w - 1, 0);
  uint64_t xb[nw], pad[3 * nw];
  auto word_at = [&pad](size_t pos) {
    const size_t i = pos >> 6, sh = pos & 63;
    return sh == 0 ? pad[i] : (pad[i] >> sh) | (pad[i + 1] << (64 - sh));
  };
  for (size_t c = 0; c < r.size(); ++c) {
    for (size_t q = 0; q < nw; ++q) xb[q] = 0;
    for (size_t i = 0; i < w; ++i)
      xb[i >> 6] |= ct::nonzero(x.at(c * w + i)) << (i & 63);
    // The reversal rr[t] = R_c[w - 1 - t], at bits [64 nw, 128 nw) of PAD.
    for (size_t q = 0; q < 3 * nw; ++q) pad[q] = 0;
    for (size_t t = 0; t < w; ++t)
      if (r[c][w - 1 - t]) {
        const size_t at = 64 * nw + t;
        pad[at >> 6] |= uint64_t(1) << (at & 63);
      }
    // sum_i X_i R_(k-i) = sum_i X_i rr_(w-1-k+i).
    for (size_t k = 0; k < 2 * w - 1; ++k) {
      const size_t off = 64 * nw + w - 1 - k;
      uint64_t cnt = 0;
      for (size_t q = 0; q < nw; ++q)
        cnt += ct::popcount(xb[q] & word_at(off + 64 * q));
      sum[k] += cnt;
    }
  }
  mac_reduce(sum, w, mac_reduction(w, taps));
  uint64_t ok = 1;
  // A limit beyond 128 bits exceeds every 64-bit sum (a public choice).
  const bool wide = !limit.fits128();
  const NatInt ln = wide ? NatInt(0) : static_cast<NatInt>(limit);
  for (size_t b = 0; b < w; ++b) ok &= wide ? 1 : ct::lt128(NatInt(sum[b]), ln);
  if (!ok)
    throw std::runtime_error(
        "mac_integer_accumulators: an accumulator is not below " +
        bound_str(limit));
  return sum;
}

// The reduced columns of one chunk power: col[i][b] = reduce(x^i * R)[b], the
// columns of Conv(r). RED is mac_reduction(w, taps).
template <class MF>
std::vector<std::vector<uint64_t>> mac_columns(
    const typename MF::Elt &r, const std::vector<std::vector<size_t>> &red) {
  const size_t w = MF::kBits;
  std::vector<std::vector<uint64_t>> col(w);
  for (size_t i = 0; i < w; ++i) {
    std::vector<uint64_t> a(2 * w - 1, 0);
    for (size_t j = 0; j < w; ++j) a[i + j] = r[j];
    mac_reduce(a, w, red);
    col[i] = std::move(a);
  }
  return col;
}

// convMax: the largest row sum of one chunk's matrix over 0/1 inputs, at the
// all-ones chunk power, which dominates every other entrywise.
template <class MF>
uint64_t mac_conv_max(const MF &mf) {
  const size_t w = MF::kBits;
  auto ones = mf.zero();
  auto xb = mf.one();
  for (size_t b = 0; b < w; ++b) {
    mf.add(ones, xb);
    xb = mf.mulf(xb, mf.of_scalar_field(0b10));
  }
  const auto col = mac_columns<MF>(ones, mac_reduction(w, mac_taps(mf)));
  uint64_t best = 0;
  for (size_t b = 0; b < w; ++b) {
    uint64_t row = 0;
    for (size_t i = 0; i < w; ++i) row += col[i][b];
    if (row > best) best = row;
  }
  return best;
}

// The accumulator bound nch * convMax + 1 of a MAC over nch chunks.
template <class MF>
uint64_t mac_acc_max(const MF &mf, size_t nch) {
  return nch * mac_conv_max(mf) + 1;
}

// Direct O(nch * w^2) evaluation: the reference for the NTT operator.
template <class F, class MF>
class MACConvReference final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  MACConvReference(const F &f, const MF &mf,
                   const std::vector<typename MF::Elt> &r)
      : f_(f), nch_(r.size()) {
    const size_t w = MF::kBits;
    const auto red = mac_reduction(w, mac_taps(mf));
    m_.assign(nch_ * w * w, f.zero());
    for (size_t c = 0; c < nch_; ++c) {
      const auto col = mac_columns<MF>(r[c], red);
      for (size_t i = 0; i < w; ++i)
        for (size_t b = 0; b < w; ++b)
          m_[(c * w + i) * w + b] = f.of_scalar(col[i][b]);
    }
  }
  size_t rows() const override { return MF::kBits; }
  size_t cols() const override { return nch_ * MF::kBits; }
  void apply(const Elt *x, Elt *y) const override {
    const size_t w = MF::kBits;
    for (size_t b = 0; b < w; ++b) y[b] = f_.zero();
    for (size_t j = 0; j < nch_ * w; ++j)
      for (size_t b = 0; b < w; ++b)
        f_.add(y[b], f_.mulf(m_[j * w + b], x[j]));
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    const size_t w = MF::kBits;
    for (size_t j = 0; j < nch_ * w; ++j) {
      x[j] = f_.zero();
      for (size_t b = 0; b < w; ++b)
        f_.add(x[j], f_.mulf(m_[j * w + b], y[b]));
    }
  }

 private:
  const F &f_;
  size_t nch_;
  std::vector<Elt> m_;
};

// The same operator by cyclic NTTs of length 2w (host_ntt::Plan), with
// mac_reduce after the inverse transform and mac_transpose_reduce before the
// forward one. The constructor computes, once per instance and in the base
// field where the 0/1 kernels and the twiddles lie, the spectrum of each R_c
// and of its reversal rev[(2w - k) mod 2w] = R_c[k], and the reduction table. apply runs one forward transform per chunk
// and one inverse; transpose_apply one forward and one inverse per chunk.
// Every field with a base-field root of order 2w runs it (the carriers and
// the native fields over F_q, e.g. Falcon's order-512 root of F_q); other
// fields use the reference.
template <class F, class MF>
class MACConvOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;
  static constexpr size_t W = MF::kBits;

 public:
  MACConvOperator(const F &f, const MF &mf,
                  const std::vector<typename MF::Elt> &r)
      : f_(f), nch_(r.size()), acc_max_(mac_acc_max(mf, r.size())) {
    if constexpr (kFieldNtt<F>) {
      if (build(mf, r)) return;
    }
    reference_ = std::make_unique<MACConvReference<F, MF>>(f, mf, r);
  }
  size_t rows() const override { return W; }
  size_t cols() const override { return nch_ * W; }
  // Every accumulator of 0/1 inputs is below this bound.
  uint64_t acc_max() const { return acc_max_; }
  void apply(const Elt *x, Elt *y) const override {
    if (reference_) {
      reference_->apply(x, y);
      return;
    }
    if constexpr (kFieldNtt<F>) {
      constexpr size_t N = 2 * W;
      std::vector<Elt> sum(N, f_.zero()), a(N);
      for (size_t c = 0; c < nch_; ++c) {
        std::copy(x + c * W, x + (c + 1) * W, a.begin());
        std::fill(a.begin() + W, a.end(), f_.zero());
        plan_->transform(a, false);
        const auto &sp = forward_[c];
        for (size_t k = 0; k < N; ++k) f_.add(sum[k], f_.mulf(a[k], sp[k]));
      }
      plan_->transform(sum, true);
      mac_reduce(f_, sum, W, red_);
      std::copy(sum.begin(), sum.begin() + W, y);
    }
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    if (reference_) {
      reference_->transpose_apply(y, x);
      return;
    }
    if constexpr (kFieldNtt<F>) {
      constexpr size_t N = 2 * W;
      auto lifted = mac_transpose_reduce(f_, y, W, red_);
      plan_->transform(lifted, false);
      std::vector<Elt> a(N);
      for (size_t c = 0; c < nch_; ++c) {
        const auto &sp = reversed_[c];
        for (size_t k = 0; k < N; ++k) a[k] = f_.mulf(lifted[k], sp[k]);
        plan_->transform(a, true);
        std::copy(a.begin(), a.begin() + W, x + c * W);
      }
    }
  }

 private:
  using Scalar = typename FieldNtt<F>::Scalar;

  // False when the base field has no root of order 2w.
  bool build(const MF &mf, const std::vector<typename MF::Elt> &r) {
    if constexpr (kFieldNtt<F>) {
      constexpr size_t N = 2 * W;
      using Base = typename FieldNtt<F>::Base;
      red_ = mac_reduction(W, mac_taps(mf));
      // A primitive 2w-th root in the base field. Any one gives the same
      // cyclic convolution.
      const auto root = FieldNtt<F>::root(f_, N);
      if (!root) return false;
      plan_ = std::make_shared<const host_ntt::Plan<F>>(f_, N, *root);
      const Base &bf = FieldNtt<F>::base(f_);
      const host_ntt::Plan<Base> kernel(bf, N, FieldNtt<F>::scalar(*root));
      for (size_t c = 0; c < nch_; ++c) {
        std::vector<Scalar> fwd(N, bf.zero()), rev(N, bf.zero());
        for (size_t k = 0; k < W; ++k) {
          const Scalar bit = r[c][k] ? bf.one() : bf.zero();
          fwd[k] = bit;
          rev[(N - k) % N] = bit;
        }
        kernel.transform(fwd, false);
        kernel.transform(rev, false);
        forward_.push_back(std::move(fwd));
        reversed_.push_back(std::move(rev));
      }
      return true;
    }
    return false;
  }

  const F &f_;
  size_t nch_;
  uint64_t acc_max_;
  std::shared_ptr<const host_ntt::Plan<F>> plan_;
  // The reduction table of M (mac_reduction).
  std::vector<std::vector<size_t>> red_;
  // Kernel spectra by chunk.
  std::vector<std::vector<Scalar>> forward_, reversed_;
  std::unique_ptr<MACConvReference<F, MF>> reference_;
};

template <class F, class MF, class T, class P>
Op<F> MACConv(const F &f, Ref<MF, T, P> r) {
  check_operator_parameter<P>();
  std::vector<uint8_t> params;
  put_u64(params, MF::kBits);
  put_u64(params, r.n);
  const MF *mf = r.f;
  return linear_operator<F>({
      .name = "mac_conv",
      .params = std::move(params),
      .rows = MF::kBits,
      .cols = r.n * MF::kBits,
      .deps = depends_on(r),
      // The chunk powers lie in M, another field: read them from the args.
      .make = [mf](const F &f, const OpArgs &a) {
        return std::make_shared<MACConvOperator<F, MF>>(f, *mf, a.get<MF>(0));
      },
      // Each row of a chunk's matrix sums to at most convMax at any chunk
      // power (the all-ones power dominates entrywise).
      .row_sum = Bound(r.n) * mac_conv_max(*r.f),
      .field = &f,
  });
}

// The acyclic convolution by a public h of LH coefficients on x of LX:
// y_i = sum_{a+b=i} x_a h_b, LX + LH - 1 rows. It is the top-left block of
// the negacyclic convolution of length M (a power of two at least
// LX + LH - 1, so no product wraps), which runs by NTT when F has one.
template <class F>
class AcyclicConvOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  AcyclicConvOperator(const F &f, size_t lx, std::vector<Elt> h, size_t M)
      : f_(f), lx_(lx), lh_(h.size()), M_(M),
        inner_(f, (h.resize(M, f.zero()), h)) {}
  size_t rows() const override { return lx_ + lh_ - 1; }
  size_t cols() const override { return lx_; }
  void apply(const Elt *x, Elt *y) const override {
    std::vector<Elt> u(M_, f_.zero()), v(M_);
    std::copy(x, x + lx_, u.begin());
    inner_.apply(u.data(), v.data());
    std::copy(v.begin(), v.begin() + long(rows()), y);
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    std::vector<Elt> u(M_, f_.zero()), v(M_);
    std::copy(y, y + rows(), u.begin());
    inner_.transpose_apply(u.data(), v.data());
    std::copy(v.begin(), v.begin() + long(lx_), x);
  }

 private:
  const F &f_;
  size_t lx_, lh_, M_;
  NegacyclicConvOperator<F> inner_;
};

// AcyclicConv(h, lx, eb): the acyclic convolution by the public h (a [lh]
// handle) on vectors of LX coefficients. With EB, h's coefficients are
// canonical integers below EB.bound (instantiation refuses others), so the
// matrix is nonnegative with rows summing to at most min(lx, lh) (B - 1)
// (OpSpec::row_sum) for interval propagation.
template <class F, class T, class P>
Op<F> AcyclicConv(Ref<F, T, P> h, size_t lx,
                  std::optional<EntryBound> eb = std::nullopt) {
  check_operator_parameter<P>();
  const size_t lh = h.n;
  if (lx == 0 || lh == 0) fail("AcyclicConv: an empty operand");
  size_t M = 1;
  while (M < lx + lh - 1) M *= 2;
  std::vector<uint8_t> params;
  put_u64(params, lx);
  put_u64(params, lh);
  Bound B = 0;
  if (eb) {
    B = eb->bound;
    if (B < 1 || B > (Bound(1) << 62))
      fail("AcyclicConv: the entry bound is not in [1, 2^62]");
    put_str(params, "entry_bound");
    put_bound(params, B);
  }
  using V = std::vector<typename F::Elt>;
  LinearOpDef<F> d{
      .name = "acyclic_conv",
      .params = std::move(params),
      .rows = lx + lh - 1,
      .cols = lx,
      .deps = depends_on(Ref<F>(h)),
      .make = [lx, M, B](const F &f, const V &v) {
        if (B != 0)
          for (const auto &x : v)
            if (!subfield_contains(f, x) || nat_of(f, x) >= B)
              throw std::runtime_error(
                  "acyclic_conv: a public coefficient is not an integer "
                  "below its entry bound " + bound_str(B));
        return std::make_shared<AcyclicConvOperator<F>>(f, lx, v, M);
      },
  };
  if (B != 0) {
    d.row_sum = Bound(std::min(lx, lh)) * (B - 1);
    d.bound_terms = {{"entryBound", B},
                     {"terms", Bound(std::min(lx, lh))},
                     {"rowSum", d.row_sum}};
  }
  return linear_operator<F>(std::move(d));
}

// A constant integer matrix of ROWS x COLS, sparse rows of (column,
// coefficient), applied by its rows. It has a circuit expansion.
template <class F>
class SparseOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  using Rows = typename OpSpec<F>::SparseRows;
  SparseOperator(const F &f, size_t cols, std::shared_ptr<const Rows> rows)
      : f_(f), cols_(cols), rows_(std::move(rows)) {}
  size_t rows() const override { return rows_->size(); }
  size_t cols() const override { return cols_; }
  void apply(const Elt *x, Elt *y) const override {
    for (size_t i = 0; i < rows_->size(); ++i) {
      Elt s = f_.zero();
      for (const auto &[c, a] : (*rows_)[i]) f_.add(s, f_.mulf(a, x[c]));
      y[i] = s;
    }
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    for (size_t c = 0; c < cols_; ++c) x[c] = f_.zero();
    for (size_t i = 0; i < rows_->size(); ++i)
      for (const auto &[c, a] : (*rows_)[i]) f_.add(x[c], f_.mulf(a, y[i]));
  }

 private:
  const F &f_;
  size_t cols_;
  std::shared_ptr<const Rows> rows_;
};

// The operator NAME of ROWS (nonnegative integer coefficients below 2^63)
// over COLS inputs; its parameters are the rows. Its row bound is the
// largest row sum (interval propagation).
template <class F>
Op<F> sparse_matrix(
    const F &f, std::string name, size_t cols,
    const std::vector<std::vector<std::pair<size_t, uint64_t>>> &rows) {
  using Rows = typename OpSpec<F>::SparseRows;
  auto er = std::make_shared<Rows>(rows.size());
  std::vector<uint8_t> params;
  put_u64(params, cols);
  put_u64(params, rows.size());
  Bound row_sum = 0;
  for (size_t i = 0; i < rows.size(); ++i) {
    put_u64(params, rows[i].size());
    Bound s = 0;
    for (const auto &[c, a] : rows[i]) {
      if (c >= cols) fail("sparse_matrix '" + name + "': a column past COLS");
      put_u64(params, c);
      put_u64(params, a);
      (*er)[i].push_back({c, f.of_scalar(a)});
      s += Bound(a);
    }
    row_sum = std::max(row_sum, s);
  }
  return linear_operator<F>({
      .name = std::move(name),
      .params = std::move(params),
      .rows = rows.size(),
      .cols = cols,
      .make = [cols, er](const F &g) {
        return std::make_shared<SparseOperator<F>>(g, cols, er);
      },
      .emit = [er]() { return *er; },
      .row_sum = row_sum < Bound::pow2(kBoundCapBits) ? row_sum : 0,
      .field = &f,
  });
}

// sparse_matrix with coefficients below 2^kBoundCapBits (Bound), for a field whose
// characteristic exceeds them: the carry groups' 2^(w j) of wide limbs in
// Fp128. Its parameters mark the wide entries.
template <class F>
Op<F> sparse_matrix_wide(
    const F &f, std::string name, size_t cols,
    const std::vector<std::vector<std::pair<size_t, Bound>>> &rows) {
  using Rows = typename OpSpec<F>::SparseRows;
  auto er = std::make_shared<Rows>(rows.size());
  std::vector<uint8_t> params;
  put_str(params, "wide");
  put_u64(params, cols);
  put_u64(params, rows.size());
  Bound row_sum = 0;
  for (size_t i = 0; i < rows.size(); ++i) {
    put_u64(params, rows[i].size());
    for (const auto &[c, a] : rows[i]) {
      if (c >= cols) fail("sparse_matrix '" + name + "': a column past COLS");
      if (a >= Bound::pow2(kBoundCapBits) || !characteristic_above(f, a))
        fail("sparse_matrix '" + name + "': a coefficient is not below "
             "2^" + std::to_string(kBoundCapBits) + " and the characteristic");
      put_u64(params, c);
      put_bound(params, a);
      (*er)[i].push_back({c, elt_of_nat(f, a)});
    }
  }
  for (const auto &r : rows) {
    Bound s = 0;
    for (const auto &[c, a] : r) s = bound_add(s, a);
    row_sum = std::max(row_sum, s);
  }
  return linear_operator<F>({
      .name = std::move(name),
      .params = std::move(params),
      .rows = rows.size(),
      .cols = cols,
      .make = [cols, er](const F &g) {
        return std::make_shared<SparseOperator<F>>(g, cols, er);
      },
      .emit = [er]() { return *er; },
      .row_sum = row_sum < Bound::pow2(kBoundCapBits) ? row_sum : 0,
      .field = &f,
  });
}

// INTT_n: the inverse of the scheme-order negacyclic transform of length n
// with root PSI (NegacyclicNtt). Its transpose: for M the forward matrix,
// M^T = n R M^-1 with (R y)_0 = y_0, (R y)_i = -y_(n-i) (StagedNtt::
// transpose), so (M^-1)^T y = M (R y) / n. Affine rows only (no circuit
// expansion).
template <class F>
class InverseNttOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  InverseNttOperator(const F &f, size_t n, const Elt &psi)
      : f_(f), ntt_(f, n, psi), ninv_(f.invertf(f.of_scalar(uint64_t(n)))) {}
  size_t rows() const override { return ntt_.n(); }
  size_t cols() const override { return ntt_.n(); }
  void apply(const Elt *x, Elt *y) const override {
    std::vector<Elt> v(x, x + ntt_.n());
    ntt_.inverse(v);
    std::copy(v.begin(), v.end(), y);
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    const size_t n = ntt_.n();
    std::vector<Elt> v(n);
    v[0] = y[0];
    for (size_t i = 1; i < n; ++i) v[i] = f_.negf(y[n - i]);
    ntt_.forward(v);
    for (size_t i = 0; i < n; ++i) x[i] = f_.mulf(ninv_, v[i]);
  }

 private:
  const F &f_;
  NegacyclicNtt<F> ntt_;
  Elt ninv_;
};

template <class F>
Op<F> InverseNtt(const F &f, size_t n, const typename F::Elt &psi) {
  std::vector<uint8_t> params;
  put_u64(params, n);
  poly_detail::put_elt(params, f, psi);
  return linear_operator<F>({
      .name = "inverse_ntt",
      .params = std::move(params),
      .rows = n,
      .cols = n,
      .make = [n, psi](const F &g) {
        return std::make_shared<InverseNttOperator<F>>(g, n, psi);
      },
      .field = &f,
  });
}

// ------------------------------------------------- public row products --

namespace row_dot_internal {

// A small-prime extension whose elements are coordinate arrays of base
// scalars (Fp24_6, Fp14_n, NativeWide): ExtCoefTable's kernel.
template <class F, class = void>
struct ExtCoef : std::false_type {};
template <class F>
struct ExtCoef<
    F, std::void_t<decltype(F::kDegree),
                   decltype(std::declval<const F &>().base_field().from_montgomery(
                       std::declval<typename F::Elt>().e[0])),
                   decltype(std::declval<typename F::Elt &>().e[0] =
                                std::declval<const F &>().base_field().of_scalar(
                                    uint64_t{0}))>>
    : std::bool_constant<(F::kDegree > 1)> {};
// The Goldilocks fields' and the generic prime field's prescaled dot
// product over Nat<1> entries.
template <class T, class = void>
struct HasE : std::false_type {};
template <class T>
struct HasE<T, std::void_t<decltype(std::declval<T>().e)>> : std::true_type {};
template <class T, class = void>
struct HasN : std::false_type {};
template <class T>
struct HasN<T, std::void_t<decltype(std::declval<T>().n)>> : std::true_type {};
template <class F, class = void>
struct PrescaledDot : std::false_type {};
template <class F>
struct PrescaledDot<F, std::void_t<typename F::NatScaledForDot>>
    : std::bool_constant<HasE<typename F::NatScaledForDot>::value ||
                         HasN<typename F::NatScaledForDot>::value> {};

// The canonical integer of X when it is a prime-field element of at most
// 64 bits (its subfield bytes, little-endian); false otherwise.
template <class F>
bool narrow_u64(const F &f, const typename F::Elt &x, uint64_t &out,
                bool typed = false) {
  if (!typed && !subfield_contains(f, x)) return false;
  if constexpr (domain_subfield<F>::kBytes <= 8) {
    uint8_t b[8] = {};
    subfield_to_bytes(f, b, x);
    out = 0;
    for (size_t i = domain_subfield<F>::kBytes; i-- > 0;) out = (out << 8) | b[i];
    return true;
  } else {
    const Bound v = nat_of(f, x);
    out = uint64_t(v);
    return (v >> 64) == 0;
  }
}

// d_j = <rows[j], G> for the R rows of width W, with the narrowest kernel
// the field and the rows allow: base-field coefficient sums with one
// reduction per row in a small-prime extension (ExtCoefTable's), the
// prescaled dot of the Goldilocks fields, field products otherwise. A row
// entry outside the prime field (or above 64 bits) falls back to field
// products. TYPED says the rows are values of a prime-field type (Bit, or
// Subfield of a domain whose designated subfield is the prime field),
// checked where they are computed, so no entry is checked again. Every
// value here is public.
template <class F>
std::vector<typename F::Elt> row_dots(const F &f, const typename F::Elt *rows,
                                      size_t R, size_t W,
                                      const typename F::Elt *G,
                                      bool typed = false) {
  using Elt = typename F::Elt;
  std::vector<Elt> d(R, f.zero());
  if constexpr (ExtCoef<F>::value) {
    const Bound q = field_characteristic(f);
    constexpr size_t D = F::kDegree;
    const Bound m = q - 1;
    const auto &base = f.base_field();
    // A prime-field element is its first coordinate (checked on the first
    // row against the canonical integer).
    bool ok = q <= (Bound(1) << 32) && m * m * Bound(W) < (Bound(1) << 64);
    for (size_t i = 0; i < W && ok; ++i) {
      uint64_t x = 0;
      ok = narrow_u64(f, rows[i], x) &&
           base.from_montgomery(rows[i].e[0]).u64()[0] == x;
    }
    if (ok) {
      std::vector<uint32_t> coef(W * D);
      for (size_t i = 0; i < W; ++i)
        for (size_t t = 0; t < D; ++t)
          coef[i * D + t] = uint32_t(base.from_montgomery(G[i].e[t]).u64()[0]);
      // A row's entries as base residues, read once into a narrow buffer;
      // an entry with another nonzero coordinate is outside the prime field.
      std::vector<uint32_t> row(W);
      for (size_t j = 0; j < R && ok; ++j) {
        const Elt *rj = rows + j * W;
        for (size_t i = 0; i < W; ++i) {
          row[i] = uint32_t(base.from_montgomery(rj[i].e[0]).u64()[0]);
          if (!typed)
            for (size_t t = 1; t < D; ++t) ok = ok && rj[i].e[t] == base.zero();
        }
        uint64_t s[D] = {};
        for (size_t i = 0; i < W; ++i) {
          const uint64_t x = row[i];
          for (size_t t = 0; t < D; ++t) s[t] += x * coef[i * D + t];
        }
        Elt e{};
        for (size_t t = 0; t < D; ++t)
          e.e[t] = base.of_scalar(uint64_t(s[t] % uint64_t(q)));
        d[j] = e;
      }
      if (ok) return d;
      d.assign(R, f.zero());
    }
  } else if constexpr (PrescaledDot<F>::value) {
    std::vector<typename F::NatScaledForDot> gs(W);
    for (size_t i = 0; i < W; ++i) gs[i] = f.prescale_for_dot(G[i]);
    std::vector<Nat<1>> row(W);
    bool ok = true;
    for (size_t j = 0; j < R && ok; ++j) {
      for (size_t i = 0; i < W; ++i) {
        uint64_t x = 0;
        ok = narrow_u64(f, rows[j * W + i], x, typed) && ok;
        row[i] = Nat<1>(x);
      }
      d[j] = f.dot(W, row.data(), gs.data());
    }
    if (ok) return d;
    d.assign(R, f.zero());
  }
  for (size_t j = 0; j < R; ++j)
    for (size_t i = 0; i < W; ++i) f.add(d[j], f.mulf(rows[j * W + i], G[i]));
  return d;
}
}  // namespace row_dot_internal

// y_j = <rows_j, x> for a public matrix of R rows of W entries, applied by
// row_dot_internal::row_dots. ROWS points at the values of the operator's
// dependency in the run that instantiated it, which outlives the operator
// (instantiate), so the matrix is never copied. TYPED says its entries are
// values of a prime-field type, checked where they are supplied or
// computed.
template <class F>
class RowDotOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  RowDotOperator(const F &f, const Elt *rows, size_t R, size_t W, bool typed)
      : f_(f), rows_(rows), R_(R), W_(W), typed_(typed) {}
  size_t rows() const override { return R_; }
  size_t cols() const override { return W_; }
  void apply(const Elt *x, Elt *y) const override {
    const std::vector<Elt> d =
        row_dot_internal::row_dots(f_, rows_, R_, W_, x, typed_);
    std::copy(d.begin(), d.end(), y);
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    for (size_t i = 0; i < W_; ++i) x[i] = f_.zero();
    for (size_t j = 0; j < R_; ++j)
      for (size_t i = 0; i < W_; ++i)
        f_.add(x[i], f_.mulf(rows_[j * W_ + i], y[j]));
  }

 private:
  const F &f_;
  const Elt *rows_;
  size_t R_, W_;
  bool typed_;
};

// RowDot(rows): the matrix-vector product by the public ROWS ([R, ...], a
// row the trailing axes): y_j = <rows_j, x>, R outputs from the row width
// W inputs. Rows of a prime-field type (Bit, or Subfield<> of a field whose
// designated subfield is the prime field) are read as such, without a check
// of each entry. Affine rows and the host evaluate it; a circuit does not
// expand it.
template <class F, class T, class P>
Op<F> RowDot(Ref<F, T, P> rows) {
  check_operator_parameter<P>();
  const size_t R = rows.dims().at(0);
  if (R == 0 || rows.n % R != 0) fail("RowDot: a matrix of no rows");
  const size_t W = rows.n / R;
  constexpr bool kTyped = !F::kCharacteristicTwo &&
                          domain_subfield<F>::kDegree == 1 &&
                          (is_bit_v<T> || std::is_same_v<T, Subfield<>>);
  std::vector<uint8_t> params;
  put_u64(params, R);
  put_u64(params, W);
  using V = std::vector<typename F::Elt>;
  return linear_operator<F>({
      .name = "row_dot",
      .params = std::move(params),
      .rows = R,
      .cols = W,
      .deps = depends_on(Ref<F>(rows)),
      .make = [R, W, typed = kTyped](const F &f, const V &v) {
        return std::make_shared<RowDotOperator<F>>(f, v.data(), R, W, typed);
      },
  });
}

// The transpose of the negacyclic transform of length n with root PSI in
// natural order: x = V^T y with V[m][i] = psi^((2m + 1) i), so
// x_i = sum_m psi^((2m + 1) i) y_m. Over a field with transforms it is
// StagedNtt's transpose (one inverse transform); otherwise the O(n^2) sums.
template <class F>
class NttTransposeOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  NttTransposeOperator(const F &f, size_t n, const Elt &psi)
      : f_(f), n_(n), psi_(psi) {}
  size_t rows() const override { return n_; }
  size_t cols() const override { return n_; }
  void apply(const Elt *y, Elt *x) const override {
    std::vector<Elt> a(y, y + n_);
    if constexpr (kFieldNtt<F>) {
      staged().transpose(a);
    } else {
      a = direct(a, true);
    }
    std::copy(a.begin(), a.end(), x);
  }
  void transpose_apply(const Elt *x, Elt *y) const override {
    std::vector<Elt> a(x, x + n_);
    if constexpr (kFieldNtt<F>) {
      staged().apply(a);
    } else {
      a = direct(a, false);
    }
    std::copy(a.begin(), a.end(), y);
  }

 private:
  StagedNtt<F> staged() const {
    StagedNtt<F> t;
    t.f = &f_;
    t.n = n_;
    t.psi = psi_;
    t.order = NttOrder::kNatural;
    return t;
  }
  // V^T a (TRANSPOSE) or V a, by the definition.
  std::vector<Elt> direct(const std::vector<Elt> &a, bool transpose) const {
    std::vector<Elt> out(n_, f_.zero());
    for (size_t m = 0; m < n_; ++m) {
      // z = psi^(2m + 1), and V[m][i] = z^i.
      Elt z = psi_;
      for (size_t k = 0; k < 2 * m; ++k) z = f_.mulf(z, psi_);
      Elt zi = f_.one();
      for (size_t i = 0; i < n_; ++i) {
        if (transpose)
          f_.add(out[i], f_.mulf(zi, a[m]));
        else
          f_.add(out[m], f_.mulf(zi, a[i]));
        zi = f_.mulf(zi, z);
      }
    }
    return out;
  }

  const F &f_;
  size_t n_;
  Elt psi_;
};

// NttTranspose(f, n, psi): V^T for V the natural-order negacyclic transform
// of length n with root PSI (psi^n = -1), a constant matrix. A record
// digest sum_k a(psi^(2k+1)) g_k of a polynomial a is <a, V^T g>.
template <class F>
Op<F> NttTranspose(const F &f, size_t n, const typename F::Elt &psi) {
  if (n < 2 || !ntt_detail::power_of_two(n))
    fail("NttTranspose: the length is not a power of two");
  std::vector<uint8_t> params;
  put_u64(params, n);
  poly_detail::put_elt(params, f, psi);
  return linear_operator<F>({
      .name = "ntt_transpose",
      .params = std::move(params),
      .rows = n,
      .cols = n,
      .make = [n, psi](const F &g) {
        return std::make_shared<NttTransposeOperator<F>>(g, n, psi);
      },
      .field = &f,
  });
}

}  // namespace proofs::gordiehowe::ops

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_OPERATORS_H_
