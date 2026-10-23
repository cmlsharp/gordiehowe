// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: affine expressions and linear operators, the mechanism.
//
// An affine expression Lin<F> is a sum of terms scale * (op_k ... op_1)(v),
// where v is any node of field F and each op is a linear operator with
// apply and transpose_apply. Operators may depend on public values (the
// statement, challenges, public messages); they are instantiated from those
// values when the constraint rows are built, by both parties.
// linear_operator defines one; the structural operators the expression
// surface reads (Diagonal, ScaleBy, ConstDiagonal, Sum, ZeroExtend, Gather,
// batching, FromDigits) are here, and the algebraic ones (NegacyclicConv,
// PolyMatVec, the NTTs, MACConv) are in ops/operators.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LINEAR_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LINEAR_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iterator>
#include <memory>
#include <mutex>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "util/panic.h"

namespace proofs::gordiehowe {

namespace ops {
// A staged transform (ops/operators.h), which a circuit expands by its
// butterflies.
template <class F>
struct StagedNtt;
}  // namespace ops

// A concrete matrix M of size rows x cols over F.
template <class F>
class LinearOperator {
 public:
  using Elt = typename F::Elt;
  virtual ~LinearOperator() = default;
  virtual size_t rows() const = 0;
  virtual size_t cols() const = 0;
  // y = M x; x has cols() elements, y receives rows().
  virtual void apply(const Elt *x, Elt *y) const = 0;
  // x = M^T y; y has rows() elements, x receives cols().
  virtual void transpose_apply(const Elt *y, Elt *x) const = 0;
  // A += scale M^T y, A of cols() elements. An operator with few nonzero
  // entries per row (Gather, ZeroExtend) touches only the coordinates its
  // rows read, so a term reading a few coordinates of a long value costs
  // its rows, not the value's length.
  virtual void transpose_accumulate(const F &f, const Elt *y,
                                    const Elt &scale, Elt *A) const {
    std::vector<Elt> x(cols());
    transpose_apply(y, x.data());
    for (size_t j = 0; j < x.size(); ++j)
      if (x[j] != f.zero()) f.add(A[j], f.mulf(scale, x[j]));
  }
};

// The symbolic operator: a name and parameters (for the system digest), its
// shape, the public nodes it reads, and its instantiation from their values.
template <class F>
struct OpSpec {
  std::string name;
  std::vector<uint8_t> params;
  size_t rows = 0, cols = 0;
  std::vector<size_t> deps;
  // MAKE receives the values of DEPS, in order (OpArgs::get<F>(k)).
  std::function<std::shared_ptr<const LinearOperator<F>>(const OpArgs &)> make;
  // Optional circuit expansion of an operator without dependencies: its
  // constant matrix as sparse rows (column, coefficient), so that a circuit
  // reads a derived view that applies it (design pass 3, the budget needle).
  using SparseRows =
      std::vector<std::vector<std::pair<size_t, typename F::Elt>>>;
  std::function<SparseRows()> emit;
  // Optional, for an operator whose matrix the dependencies fix: the matrix
  // as sparse rows (column, coefficient), each coefficient a constant or
  // coordinate AT of dependency DEP (deps[DEP]). It describes the operator
  // as data (the realized program's `.linear` rows with `Coef.node`); the
  // prover and verifier apply MAKE's operator.
  struct DepCoef {
    bool is_const = true;
    typename F::Elt c{};
    size_t dep = 0, at = 0;
  };
  using DepRows = std::vector<std::vector<std::pair<size_t, DepCoef>>>;
  std::function<DepRows()> dep_rows;
  // A staged transform (Ntt): circuits expand it by its butterflies, never
  // through EMIT, which refuses it.
  std::shared_ptr<const ops::StagedNtt<F>> staged;
  // The output's dims when not flat [rows] (PolyMatVec: [K][n]).
  std::vector<size_t> out_dims;
  // Interval propagation (range.h, mod.h): when nonzero, the matrix has
  // nonnegative integer entries for every value of the parameters, and each
  // row sums to at most ROW_SUM, so inputs in [0, a] give outputs in
  // [0, a * ROW_SUM]. It does not enter the description: the operator's
  // name and parameters fix it.
  Bound row_sum = 0;
  // The same for a matrix of integer entries of either sign: when nonzero,
  // the absolute values of each row sum to at most ABS_ROW_SUM, so inputs
  // in [-a, a] give outputs in [-a * ABS_ROW_SUM, a * ABS_ROW_SUM]
  // (PolyMatVec over a public operand with an EntryBound).
  Bound abs_row_sum = 0;
  // The terms of that bound, by name, for the plan export (PolyMatVec's
  // entryBound, K, L, n); empty when the bound is the row sum alone.
  std::vector<std::pair<std::string, Bound>> bound_terms;
};

namespace internal {
// The lock of every run's operator map (instantiate). One for all fields:
// the domains of one run, of different fields, share the map.
inline std::mutex &operators_mutex() {
  static std::mutex mu;
  return mu;
}
}  // namespace internal

// Instantiates SPEC from the values of its declared dependencies only (so
// MAKE reads nothing else, a pad least of all), and checks the operator's
// shape against the declared one: a clear runtime error otherwise. The
// operator is built at its first use in the run V and shared by every later
// use, so each party (each with its own run) builds it, with any kernel
// spectra, once per proof.
template <class F>
std::shared_ptr<const LinearOperator<F>> instantiate(const OpSpec<F> &spec,
                                                     const ValueReader &v) {
  // The domains of a run may prove or verify on threads of their own
  // (parallel_domains) and share V's operator map: the map is read and
  // written under a lock, and an operator is built outside it (each spec
  // belongs to one domain, so no two threads build the same one).
  std::mutex &mu = internal::operators_mutex();
  {
    std::lock_guard<std::mutex> lock(mu);
    const auto it = v.operators.find(&spec);
    if (it != v.operators.end() && it->second)
      return std::static_pointer_cast<const LinearOperator<F>>(it->second);
  }
  OpArgs deps;
  for (size_t d : spec.deps) {
    const auto [tag, x] = v.elements(d);
    deps.push(tag, x);
  }
  auto op = spec.make(deps);
  if (op == nullptr || op->rows() != spec.rows || op->cols() != spec.cols)
    throw std::runtime_error(
        "operator '" + spec.name + "' declares " + std::to_string(spec.rows) +
        "x" + std::to_string(spec.cols) + " but instantiates as " +
        (op == nullptr ? std::string("nothing")
                       : std::to_string(op->rows()) + "x" +
                             std::to_string(op->cols())));
  std::lock_guard<std::mutex> lock(mu);
  auto &slot = v.operators[&spec];
  if (slot) return std::static_pointer_cast<const LinearOperator<F>>(slot);
  slot = op;
  return op;
}

template <class F>
struct Term {
  typename F::Elt scale;
  // Applied in order: chain[0] first.
  std::vector<std::shared_ptr<const OpSpec<F>>> chain;
  size_t node = SIZE_MAX;
  size_t in_n = 0;  // length of the node
  size_t out_n() const { return chain.empty() ? in_n : chain.back()->rows; }
};

template <class F>
struct Lin {
  const F *f = nullptr;
  size_t n = 0;
  std::vector<Term<F>> terms;
  // The expression's shape (empty: rank 1, [n]). Operators act on the last
  // axis and batch over the leading ones.
  std::vector<size_t> shape;
  // The graph of the first handle it reads, through which a predicate on
  // it finds its system (predicates.h); null for no handle.
  Graph *g = nullptr;
  std::vector<size_t> dims() const {
    return shape.empty() ? std::vector<size_t>{n} : shape;
  }

  Lin() = default;
  // implicit: a handle is the expression 1 * v. A bit view has no committed
  // coordinate, so an affine expression never reads one: a CircuitOnly
  // handle is a C++ compile error here, and an erased handle on a bit view
  // the CompileError of the domain's compile.
  template <class T, class P>
  Lin(Ref<F, T, P> r) : f(r.f), n(r.n), shape(r.shape), g(r.g) {  // NOLINT
    static_assert(!is_bytes_v<T>,
                  "an affine expression reads a Bytes statement: read it "
                  "through a public computation");
    static_assert(!std::is_same_v<P, CircuitOnly>,
                  "an affine expression reads a bit view: bit views have no "
                  "committed coordinates, so read them in a circuit "
                  "constraint");
    terms.push_back(Term<F>{r.f->one(), {}, r.id, r.n});
  }
  // The expression methods and views (expr.h) on this affine expression
  // read as an expression.
  auto sum() const { return as_expr(*this).sum(); }
  auto sum(size_t axis) const { return as_expr(*this).sum(axis); }
  auto prod() const { return as_expr(*this).prod(); }
  auto prod(size_t axis) const { return as_expr(*this).prod(axis); }
  auto rotate(long k, size_t axis) const {
    return as_expr(*this).rotate(k, axis);
  }
  auto reindex(const std::vector<size_t> &idx) const {
    return as_expr(*this).reindex(idx);
  }
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  auto reindex(const K &idx) const {
    return as_expr(*this).reindex(idx);
  }
  auto reindex(const std::vector<size_t> &idx, size_t axis) const {
    return as_expr(*this).reindex(idx, axis);
  }
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  auto reindex(const K &idx, size_t axis) const {
    return as_expr(*this).reindex(idx, axis);
  }
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  auto operator[](const K &idx) const {
    return as_expr(*this).reindex(idx);
  }
  auto slice(size_t b, size_t e, size_t axis = 0) const {
    return as_expr(*this).slice(b, e, axis);
  }
  auto at(size_t axis, size_t i) const { return as_expr(*this).at(axis, i); }
  auto at(size_t i) const { return as_expr(*this).at(0, i); }
  auto operator[](size_t i) const { return as_expr(*this)[i]; }
  template <class Y>
  auto concat(const Y &y, size_t axis = 0) const {
    return as_expr(*this).concat(y, axis);
  }
  // The integers of the digit vectors on the last axis in BASE, least
  // significant first: [..., k] -> [...], through FromDigits. BASE is an
  // integer (the operator then carries its row sum for interval
  // propagation) or an element of F.
  template <class B>
  Lin from_digits(const B &base) const {
    static_assert(std::is_integral_v<B> || std::is_same_v<B, typename F::Elt>,
                  "from_digits: the base is an integer or an element of the "
                  "field");
    if constexpr (std::is_integral_v<B>) {
      return lin_from_digits(*this, uint64_t(base));
    } else {
      return lin_from_digits_elt(*this, base);
    }
  }
  // Bit words [..., w] as integers of width w (expr.h's Word).
  auto from_bits() const { return word_of(*this); }

  // Node ids this expression reads, including operator parameters.
  std::vector<size_t> deps() const {
    std::vector<size_t> d;
    for (const auto &t : terms) {
      d.push_back(t.node);
      for (const auto &op : t.chain)
        d.insert(d.end(), op->deps.begin(), op->deps.end());
    }
    return d;
  }
};

// Handles and expressions mix in + and -, and a field element scales either
// from either side.
template <class X>
struct IsExpr : std::false_type {};
template <class F, class T, class P>
struct IsExpr<Ref<F, T, P>> : std::true_type {
  using field = F;
};
template <class F>
struct IsExpr<Lin<F>> : std::true_type {
  using field = F;
};
template <class X>
using ExprField = typename IsExpr<std::decay_t<X>>::field;
template <class X>
constexpr bool kIsExpr = IsExpr<std::decay_t<X>>::value;

template <class X, class = std::enable_if_t<kIsExpr<X>>>
Lin<ExprField<X>> as_lin(const X &x) {
  return Lin<ExprField<X>>(x);
}

template <class F>
Lin<F> broadcast_scalar(Lin<F> x, const std::vector<size_t> &dims);
template <class F>
Lin<F> broadcast_to(Lin<F> x, const std::vector<size_t> &dims);

template <class X, class Y,
          class = std::enable_if_t<kIsExpr<X> && kIsExpr<Y>>>
Lin<ExprField<X>> operator+(const X &x, const Y &y) {
  static_assert(std::is_same_v<ExprField<X>, ExprField<Y>>,
                "an affine expression adds values of one field");
  Lin<ExprField<X>> a = as_lin(x);
  Lin<ExprField<X>> b = as_lin(y);
  // A scalar broadcasts over the other side's shape; other shapes
  // broadcast by NumPy's rule.
  if (a.n != b.n && a.n == 1) a = broadcast_scalar(a, b.dims());
  if (a.n != b.n && b.n == 1) b = broadcast_scalar(b, a.dims());
  if (a.n != b.n) {
    const auto out = broadcast_shape(a.dims(), b.dims(), "+");
    if (a.dims() != out) a = broadcast_to(a, out);
    if (b.dims() != out) b = broadcast_to(b, out);
  }
  check(a.n == b.n, "Lin: length mismatch in +");
  a.terms.insert(a.terms.end(), b.terms.begin(), b.terms.end());
  if (a.shape.empty()) a.shape = b.shape;
  if (a.g == nullptr) a.g = b.g;
  return a;
}
template <class X, class = std::enable_if_t<kIsExpr<X>>>
Lin<ExprField<X>> operator*(const typename ExprField<X>::Elt &k,
                            const X &x) {
  Lin<ExprField<X>> a = as_lin(x);
  for (auto &t : a.terms) t.scale = a.f->mulf(k, t.scale);
  return a;
}
template <class X, class = std::enable_if_t<kIsExpr<X>>>
Lin<ExprField<X>> operator*(const X &x,
                            const typename ExprField<X>::Elt &k) {
  return k * x;
}
template <class X, class = std::enable_if_t<kIsExpr<X>>>
Lin<ExprField<X>> operator-(const X &x) {
  Lin<ExprField<X>> a = as_lin(x);
  return a.f->mone() * a;
}
template <class X, class Y,
          class = std::enable_if_t<kIsExpr<X> && kIsExpr<Y>>>
Lin<ExprField<X>> operator-(const X &x, const Y &y) {
  return x + (-y);
}

// A handle on an operator spec; op(x) composes it after x.
template <class F>
std::shared_ptr<const OpSpec<F>> batched(std::shared_ptr<const OpSpec<F>> op,
                                         size_t b);

// A handle on an operator spec; op(x) composes it after x. On x of shape
// [..., cols] with leading axes of B coordinates in all, it acts on each
// slice of the last axis (the block-diagonal operator, batched(op, B)), and
// the result has shape [..., rows] (the last axis dropped when rows = 1).
// An operator whose input spans several trailing axes (PolyMatVec reads
// [L][n]) batches over the axes before them, and its output has the shape
// OpSpec::out_dims when it names one.
template <class F, class T>
struct Expr;
template <class F>
struct Op {
  std::shared_ptr<const OpSpec<F>> spec;
  // The operator on a value of N coordinates with dims D: the spec itself,
  // or batched over D's leading axes; and the output's dims.
  std::pair<std::shared_ptr<const OpSpec<F>>, std::vector<size_t>> fit(
      const std::vector<size_t> &d, size_t n) const {
    std::shared_ptr<const OpSpec<F>> s = spec;
    const std::vector<size_t> one =
        spec->out_dims.empty() ? std::vector<size_t>{spec->rows}
                               : spec->out_dims;
    std::vector<size_t> out = one;
    if (n != spec->cols) {
      // The trailing axes the operator reads.
      size_t k = d.size(), span = 1;
      while (k > 0 && span < spec->cols) span *= d[--k];
      check(k >= 1 && span == spec->cols,
            "operator applied to a vector of the wrong length");
      s = batched(spec, n / spec->cols);
      out.assign(d.begin(), d.begin() + long(k));
      if (spec->rows != 1) out.insert(out.end(), one.begin(), one.end());
    }
    return {s, out};
  }
  template <class X, class = std::enable_if_t<kIsExpr<X>>>
  Lin<F> operator()(const X &e) const {
    Lin<F> x = as_lin(e);
    auto [s, out] = fit(x.dims(), x.n);
    for (auto &t : x.terms) t.chain.push_back(s);
    x.n = s->rows;
    x.shape = out;
    return x;
  }
  // On an expression (expr.h): an expression, affine when X is, its
  // constant term carried through the operator.
  template <class T>
  auto operator()(const Expr<F, T> &x) const;
};

// An operator's parameters are public values, which both parties hold: a
// handle placed Committed or CircuitOnly is a C++ compile error.
template <class P>
constexpr void check_operator_parameter() {
  static_assert(std::is_same_v<P, Public> || std::is_same_v<P, AnyPlace>,
                "an operator's parameter is a public value");
}

// ---------------------------------------------------- defining operators --

// The public values a linear operator's matrix depends on (depends_on(...)):
// a committed dependency is a C++ compile error. FIELD is the first
// dependency of the operator's field, if any.
template <class F>
struct OpDeps {
  std::vector<size_t> ids;
  const F *field = nullptr;
  OpDeps() = default;
  template <class... R>
  OpDeps(Deps<R...> d) : ids(d.ids()) {  // NOLINT
    static_assert((IsRef<R>::value && ...),
                  "linear_operator: a dependency is a value handle");
    static_assert(((std::is_same_v<typename R::place_tag, Public> ||
                    std::is_same_v<typename R::place_tag, AnyPlace>) &&
                   ...),
                  "linear_operator: the matrix depends on public values "
                  "only");
    std::apply(
        [&](const auto &...r) {
          (
              [&](const auto &x) {
                using G = typename std::decay_t<decltype(x)>::field_type;
                if constexpr (std::is_same_v<G, F>)
                  if (field == nullptr) field = x.f;
              }(r),
              ...);
        },
        d.refs);
  }
};

// How a linear operator is built from its dependencies' values, once per
// proof by each party: MAKE(f), MAKE(f, v_1) or MAKE(f, v_1, v_2), the v_k
// the values (std::vector<Elt>) of dependencies of the operator's field F;
// or MAKE(f, args), reading dependency k as args.get<G>(k) (a dependency of
// another field G). It returns the operator (a std::shared_ptr to a
// LinearOperator<F>).
template <class F>
class OpMake {
 public:
  using Fn = std::function<std::shared_ptr<const LinearOperator<F>>(
      const F &, const OpArgs &)>;
  OpMake() = default;
  template <class M,
            class = std::enable_if_t<!std::is_same_v<std::decay_t<M>, OpMake>>>
  OpMake(M m) : fn_(wrap(std::move(m))) {}  // NOLINT
  std::shared_ptr<const LinearOperator<F>> operator()(const F &f,
                                                      const OpArgs &a) const {
    return fn_(f, a);
  }
  explicit operator bool() const { return bool(fn_); }

 private:
  using V = std::vector<typename F::Elt>;
  template <class M>
  static Fn wrap(M m) {
    if constexpr (std::is_invocable_v<const M &, const F &>) {
      return [m](const F &f, const OpArgs &) { return m(f); };
    } else if constexpr (std::is_invocable_v<const M &, const F &,
                                             const V &>) {
      return [m](const F &f, const OpArgs &a) { return m(f, a.get<F>(0)); };
    } else if constexpr (std::is_invocable_v<const M &, const F &, const V &,
                                             const V &>) {
      return [m](const F &f, const OpArgs &a) {
        return m(f, a.get<F>(0), a.get<F>(1));
      };
    } else {
      static_assert(std::is_invocable_v<const M &, const F &, const OpArgs &>,
                    "linear_operator: make takes the field and the "
                    "dependencies' values (const std::vector<Elt>&, at most "
                    "two), or the field and an OpArgs");
      return [m](const F &f, const OpArgs &a) { return m(f, a); };
    }
  }
  Fn fn_;
};

// A linear operator's definition (linear_operator): M : F^cols -> F^rows,
// its matrix fixed by public values and applied by a fast algorithm.
//   name, params   identify the operator in the system digest;
//   rows, cols     its shape, and out_dims the output's dims when not
//                  [rows]; applied to a value with more coordinates it acts
//                  on the trailing axes and batches over the leading ones;
//   deps           the public values the matrix depends on;
//   make           builds the operator from their values (OpMake);
//   emit           (optional) the constant matrix as sparse rows, which lets
//                  a predicate placed in the GKR circuit use the operator;
//   staged         (optional) a staged transform the circuit expands by its
//                  butterflies, in place of emit;
//   dep_rows       (optional) the matrix as sparse rows whose coefficients
//                  are constants or coordinates of the dependencies, the
//                  operator's description as data (OpSpec::dep_rows), for an
//                  operator with no name in the realized program's schema;
//   row_sum, abs_row_sum, bound_terms
//                  (optional) interval propagation's bounds of an integer
//                  matrix (OpSpec);
//   field          the field object, when no dependency lies in F.
template <class F>
struct LinearOpDef {
  std::string name;
  std::vector<uint8_t> params = {};
  size_t rows = 0, cols = 0;
  std::vector<size_t> out_dims = {};
  OpDeps<F> deps = {};
  OpMake<F> make = {};
  std::function<typename OpSpec<F>::SparseRows()> emit = {};
  std::shared_ptr<const ops::StagedNtt<F>> staged = {};
  std::function<typename OpSpec<F>::DepRows()> dep_rows = {};
  Bound row_sum = 0, abs_row_sum = 0;
  std::vector<std::pair<std::string, Bound>> bound_terms = {};
  const F *field = nullptr;
};

// The operator a definition describes, as an Op: op(x) applies it.
template <class F>
Op<F> linear_operator(LinearOpDef<F> d) {
  const F *f = d.field != nullptr ? d.field : d.deps.field;
  if (f == nullptr)
    fail("linear_operator '" + d.name + "': no field object; give .field "
         "or a dependency of the operator's field");
  if (!d.make) fail("linear_operator '" + d.name + "': no make");
  auto s = std::make_shared<OpSpec<F>>();
  s->name = std::move(d.name);
  s->params = std::move(d.params);
  s->rows = d.rows;
  s->cols = d.cols;
  s->out_dims = std::move(d.out_dims);
  s->deps = std::move(d.deps.ids);
  s->make = [mk = std::move(d.make), f](const OpArgs &a) { return mk(*f, a); };
  s->emit = std::move(d.emit);
  s->staged = std::move(d.staged);
  s->dep_rows = std::move(d.dep_rows);
  s->row_sum = d.row_sum;
  s->abs_row_sum = d.abs_row_sum;
  s->bound_terms = std::move(d.bound_terms);
  return Op<F>{s};
}

// ---------------------------------------------------------------- kinds --

// Elementwise multiplication by a public vector d (length n), or by a public
// scalar broadcast to n coordinates.
template <class F>
class DiagonalOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  DiagonalOperator(const F &f, std::vector<Elt> d) : f_(f), d_(std::move(d)) {}
  size_t rows() const override { return d_.size(); }
  size_t cols() const override { return d_.size(); }
  void apply(const Elt *x, Elt *y) const override {
    for (size_t i = 0; i < d_.size(); ++i) y[i] = f_.mulf(d_[i], x[i]);
  }
  void transpose_apply(const Elt *y, Elt *x) const override { apply(y, x); }

 private:
  const F &f_;
  std::vector<Elt> d_;
};

template <class F, class T, class P>
Op<F> Diagonal(Ref<F, T, P> d) {
  check_operator_parameter<P>();
  return linear_operator<F>({
      .name = "diagonal",
      .rows = d.n,
      .cols = d.n,
      .deps = depends_on(d),
      .make = [](const F &f, const std::vector<typename F::Elt> &v) {
        return std::make_shared<DiagonalOperator<F>>(f, v);
      },
  });
}

// Broadcast a public scalar c (a node of length 1) over n coordinates.
template <class F, class T, class P>
Op<F> ScaleBy(Ref<F, T, P> c, size_t n) {
  check_operator_parameter<P>();
  check(c.n == 1, "ScaleBy: the scale is a scalar");
  std::vector<uint8_t> params;
  put_u64(params, n);
  return linear_operator<F>({
      .name = "scale",
      .params = std::move(params),
      .rows = n,
      .cols = n,
      .deps = depends_on(c),
      .make = [n](const F &f, const std::vector<typename F::Elt> &v) {
        return std::make_shared<DiagonalOperator<F>>(
            f, std::vector<typename F::Elt>(n, v[0]));
      },
  });
}

// Elementwise multiplication by constants D of the system (a lifted C++
// array times an affine expression): the constants are the parameters, so
// they enter the digest, and a circuit expands the diagonal.
template <class F>
Op<F> ConstDiagonal(const F &f, std::vector<typename F::Elt> d) {
  std::vector<uint8_t> params;
  put_u64(params, d.size());
  for (const auto &x : d) {
    uint8_t b[F::kBytes];
    f.to_bytes_field(b, x);
    params.insert(params.end(), b, b + F::kBytes);
  }
  const size_t n = d.size();
  return linear_operator<F>({
      .name = "const_diagonal",
      .params = std::move(params),
      .rows = n,
      .cols = n,
      .make =
          [d](const F &g) {
            return std::make_shared<DiagonalOperator<F>>(g, d);
          },
      .emit =
          [d]() {
            typename OpSpec<F>::SparseRows rows(d.size());
            for (size_t i = 0; i < d.size(); ++i) rows[i].push_back({i, d[i]});
            return rows;
          },
      .field = &f,
  });
}

// Sum(n): the 1 x n all-ones row, y = sum_i x_i. It has a circuit expansion,
// so a circuit (the range lowering's fraction tree) reads a view through it.
template <class F>
class SumOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  SumOperator(const F &f, size_t n) : f_(f), n_(n) {}
  size_t rows() const override { return 1; }
  size_t cols() const override { return n_; }
  void apply(const Elt *x, Elt *y) const override {
    y[0] = f_.zero();
    for (size_t i = 0; i < n_; ++i) f_.add(y[0], x[i]);
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    for (size_t i = 0; i < n_; ++i) x[i] = y[0];
  }

 private:
  const F &f_;
  size_t n_;
};

template <class F>
Op<F> Sum(const F &f, size_t n);
// The sum of the coordinates of V, its field and length taken from V.
template <class F>
Lin<F> Sum(const Lin<F> &v) {
  return Sum(*v.f, v.n)(v);
}
template <class F, class T, class P>
Lin<F> Sum(Ref<F, T, P> v) {
  return Sum(*v.f, v.n)(v);
}
template <class F>
Op<F> Sum(const F &f, size_t n) {
  std::vector<uint8_t> params;
  put_u64(params, n);
  const F *pf = &f;
  return linear_operator<F>({
      .name = "sum",
      .params = std::move(params),
      .rows = 1,
      .cols = n,
      .make =
          [n](const F &f) { return std::make_shared<SumOperator<F>>(f, n); },
      .emit =
          [pf, n]() {
            typename OpSpec<F>::SparseRows rows(1);
            for (size_t i = 0; i < n; ++i) rows[0].push_back({i, pf->one()});
            return rows;
          },
      .row_sum = n,
      .field = &f,
  });
}

// ZeroExtend(n, m): x of n elements followed by m - n zeros (the MAC's last
// chunk). It has a circuit expansion.
template <class F>
class ZeroExtendOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  ZeroExtendOperator(const F &f, size_t n, size_t m) : f_(f), n_(n), m_(m) {}
  size_t rows() const override { return m_; }
  size_t cols() const override { return n_; }
  void apply(const Elt *x, Elt *y) const override {
    for (size_t i = 0; i < m_; ++i) y[i] = i < n_ ? x[i] : f_.zero();
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    for (size_t i = 0; i < n_; ++i) x[i] = y[i];
  }
  void transpose_accumulate(const F &f, const Elt *y, const Elt &scale,
                            Elt *A) const override {
    for (size_t i = 0; i < n_; ++i) f.add(A[i], f.mulf(scale, y[i]));
  }

 private:
  const F &f_;
  size_t n_, m_;
};

template <class F>
Op<F> ZeroExtend(const F &f, size_t n, size_t m) {
  if (m < n)
    throw CompileError("ZeroExtend: the output is shorter than the input");
  std::vector<uint8_t> params;
  put_u64(params, n);
  put_u64(params, m);
  const F *pf = &f;
  return linear_operator<F>({
      .name = "zero_extend",
      .params = std::move(params),
      .rows = m,
      .cols = n,
      .make =
          [n, m](const F &f) {
            return std::make_shared<ZeroExtendOperator<F>>(f, n, m);
          },
      .emit =
          [pf, n, m]() {
            typename OpSpec<F>::SparseRows rows(m);
            for (size_t i = 0; i < n; ++i) rows[i].push_back({i, pf->one()});
            return rows;
          },
      .row_sum = 1,
      .field = &f,
  });
}

// Gather(idx, m): y[i] = x[idx[i]] for x of m elements, and y[i] = 0 where
// idx[i] is kGatherNone. Each row has at most one entry, a one: the
// matrix of a concatenation or a wiring permutation (Domain::concat,
// Domain::gather). It has a circuit expansion.
constexpr size_t kGatherNone = SIZE_MAX;
template <class F>
class GatherOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  GatherOperator(const F &f, std::vector<size_t> idx, size_t m)
      : f_(f), idx_(std::move(idx)), m_(m) {}
  size_t rows() const override { return idx_.size(); }
  size_t cols() const override { return m_; }
  void apply(const Elt *x, Elt *y) const override {
    for (size_t i = 0; i < idx_.size(); ++i)
      y[i] = idx_[i] == kGatherNone ? f_.zero() : x[idx_[i]];
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    for (size_t j = 0; j < m_; ++j) x[j] = f_.zero();
    for (size_t i = 0; i < idx_.size(); ++i)
      if (idx_[i] != kGatherNone) f_.add(x[idx_[i]], y[i]);
  }
  void transpose_accumulate(const F &f, const Elt *y, const Elt &scale,
                            Elt *A) const override {
    for (size_t i = 0; i < idx_.size(); ++i)
      if (idx_[i] != kGatherNone) f.add(A[idx_[i]], f.mulf(scale, y[i]));
  }

 private:
  const F &f_;
  std::vector<size_t> idx_;
  size_t m_;
};

template <class F>
Op<F> Gather(const F &f, std::vector<size_t> idx, size_t m) {
  for (size_t j : idx)
    if (j != kGatherNone && j >= m)
      throw CompileError("Gather: an index past the input");
  std::vector<uint8_t> params;
  put_u64(params, m);
  put_u64(params, idx.size());
  for (size_t j : idx) put_u64(params, j == kGatherNone ? m : j);
  const F *pf = &f;
  const size_t rows = idx.size();
  return linear_operator<F>({
      .name = "gather",
      .params = std::move(params),
      .rows = rows,
      .cols = m,
      .make =
          [idx, m](const F &f) {
            return std::make_shared<GatherOperator<F>>(f, idx, m);
          },
      .emit =
          [pf, idx]() {
            typename OpSpec<F>::SparseRows rows(idx.size());
            for (size_t i = 0; i < idx.size(); ++i)
              if (idx[i] != kGatherNone) rows[i].push_back({idx[i], pf->one()});
            return rows;
          },
      .row_sum = 1,
      .field = &f,
  });
}

// batched(op, B): op on each of B consecutive slices (block diagonal).
template <class F>
class BatchedOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;

 public:
  BatchedOperator(std::shared_ptr<const LinearOperator<F>> op, size_t b)
      : op_(std::move(op)), b_(b) {}
  size_t rows() const override { return b_ * op_->rows(); }
  size_t cols() const override { return b_ * op_->cols(); }
  void apply(const Elt *x, Elt *y) const override {
    for (size_t k = 0; k < b_; ++k)
      op_->apply(x + k * op_->cols(), y + k * op_->rows());
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    for (size_t k = 0; k < b_; ++k)
      op_->transpose_apply(y + k * op_->rows(), x + k * op_->cols());
  }

 private:
  std::shared_ptr<const LinearOperator<F>> op_;
  size_t b_;
};

template <class F>
std::shared_ptr<const OpSpec<F>> batched(std::shared_ptr<const OpSpec<F>> op,
                                         size_t b) {
  auto s = std::make_shared<OpSpec<F>>();
  s->name = "batched";
  put_u64(s->params, b);
  put_str(s->params, op->name);
  put_u64(s->params, op->params.size());
  s->params.insert(s->params.end(), op->params.begin(), op->params.end());
  s->rows = b * op->rows;
  s->cols = b * op->cols;
  s->deps = op->deps;
  s->row_sum = op->row_sum;
  s->abs_row_sum = op->abs_row_sum;
  s->bound_terms = op->bound_terms;
  s->make = [op, b](const OpArgs &a) {
    return std::make_shared<BatchedOperator<F>>(op->make(a), b);
  };
  // A staged transform batches as one transform per block
  // (expand_operator, expr.h).
  s->staged = op->staged;
  if (op->emit && !op->staged) {
    s->emit = [op, b]() {
      const auto one = op->emit();
      typename OpSpec<F>::SparseRows rows;
      for (size_t k = 0; k < b; ++k)
        for (const auto &r : one) {
          auto rr = r;
          for (auto &[c, a] : rr) c += k * op->cols;
          rows.push_back(std::move(rr));
        }
      return rows;
    };
  }
  return s;
}

// A scalar expression broadcast to DIMS: Gather with every index 0.
template <class F>
Lin<F> broadcast_scalar(Lin<F> x, const std::vector<size_t> &dims) {
  size_t n = 1;
  for (size_t d : dims) n *= d;
  Lin<F> y = Gather(*x.f, std::vector<size_t>(n, 0), 1)(x);
  y.shape = dims;
  return y;
}
// X broadcast to DIMS by NumPy's rule: Gather with broadcast_map's
// indices.
template <class F>
Lin<F> broadcast_to(Lin<F> x, const std::vector<size_t> &dims) {
  auto idx = broadcast_map(dims, x.dims(), "broadcast");
  size_t n = 1;
  for (size_t d : dims) n *= d;
  const auto g = Gather(*x.f, std::move(idx), x.n).spec;
  for (auto &t : x.terms) t.chain.push_back(g);
  x.n = n;
  x.shape = dims;
  return x;
}

// FromDigits(k, base): y = sum_l base^l x[l] over k digits, least
// significant first. It has a circuit expansion.
template <class F>
Op<F> FromDigits(const F &f, size_t k, const typename F::Elt &base) {
  std::vector<typename F::Elt> w(k);
  if (k) w[0] = f.one();
  for (size_t l = 1; l < k; ++l) w[l] = f.mulf(w[l - 1], base);
  std::vector<uint8_t> params;
  put_u64(params, k);
  {
    uint8_t b[F::kBytes];
    f.to_bytes_field(b, base);
    params.insert(params.end(), b, b + F::kBytes);
  }
  // A base equal to 1 doubled s times (1 + 1, then x + x; s in [1, 16]) is
  // applied by Horner's rule with s doublings per digit: additions only,
  // the same sum.
  unsigned shift = 0;
  if (k > 1) {
    typename F::Elt c = f.one();
    for (unsigned s = 1; s <= 16 && shift == 0; ++s) {
      c = f.addf(c, c);
      if (base == c) shift = s;
    }
  }
  struct Dot final : LinearOperator<F> {
    const F *f;
    std::vector<typename F::Elt> w;
    unsigned shift = 0;
    size_t rows() const override { return 1; }
    size_t cols() const override { return w.size(); }
    void apply(const typename F::Elt *x, typename F::Elt *y) const override {
      y[0] = f->zero();
      if (shift != 0) {
        for (size_t l = w.size(); l-- > 0;) {
          for (unsigned s = 0; s < shift; ++s) y[0] = f->addf(y[0], y[0]);
          f->add(y[0], x[l]);
        }
        return;
      }
      for (size_t l = 0; l < w.size(); ++l) f->add(y[0], f->mulf(w[l], x[l]));
    }
    void transpose_apply(const typename F::Elt *y,
                         typename F::Elt *x) const override {
      for (size_t l = 0; l < w.size(); ++l) x[l] = f->mulf(w[l], y[0]);
    }
  };
  return linear_operator<F>({
      .name = "from_digits",
      .params = std::move(params),
      .rows = 1,
      .cols = k,
      .make =
          [w, shift](const F &f) {
            auto d = std::make_shared<Dot>();
            d->f = &f;
            d->w = w;
            d->shift = shift;
            return d;
          },
      .emit =
          [w]() {
            typename OpSpec<F>::SparseRows rows(1);
            for (size_t l = 0; l < w.size(); ++l) rows[0].push_back({l, w[l]});
            return rows;
          },
      .field = &f,
  });
}
// The integers of the digit vectors on the last axis of E in BASE
// (x.from_digits(base)): [..., k] -> [...].
template <class F>
Lin<F> lin_from_digits(const Lin<F> &e, uint64_t base) {
  const auto &f = *e.f;
  const size_t k = e.dims().back();
  // An integer base gives nonnegative integer entries: the row sums to
  // sum_l base^l (interval propagation; none past 2^kBoundCapBits).
  auto spec = std::make_shared<OpSpec<F>>(
      *FromDigits(f, k, f.of_scalar(base)).spec);
  Bound w = 1, rs = 0;
  const Bound cap = Bound::pow2(kBoundCapBits);
  for (size_t l = 0; l < k && rs < cap; ++l) {
    rs += w;
    w = w < cap / (base + 1) ? w * base : cap;
  }
  spec->row_sum = rs < cap ? rs : 0;
  return Op<F>{spec}(e);
}
// The integers in BASE of the handle DIGITS read with the dims DIMS (its
// coordinates in order, the last axis the digits): lin_from_digits of the
// handle under those dims, with no view node.
template <class F, class T, class P>
Lin<F> lin_limbs(const Ref<F, T, P> &digits, std::vector<size_t> dims,
                 uint64_t base) {
  Lin<F> d(digits);
  size_t n = 1;
  for (size_t x : dims) n *= x;
  if (n != d.n) fail("lin_limbs: the dims do not hold the digits");
  d.shape = std::move(dims);
  return lin_from_digits(d, base);
}
// The same in a field-element BASE: no row sum.
template <class F>
Lin<F> lin_from_digits_elt(const Lin<F> &e, const typename F::Elt &base) {
  return FromDigits(*e.f, e.dims().back(), base)(e);
}

// Evaluate an expression on host values (prover side, and public offsets).
template <class F>
std::vector<typename F::Elt> eval_lin(const Lin<F> &e, const ValueReader &v) {
  const F &f = *e.f;
  std::vector<typename F::Elt> out(e.n, f.zero());
  std::vector<typename F::Elt> x, y;
  for (const auto &t : e.terms) {
    // The term's operator chain reads the node's elements in place.
    const typename F::Elt *xp = v.template get<F>(t.node).data();
    for (const auto &spec : t.chain) {
      y.resize(spec->rows);
      instantiate(*spec, v)->apply(xp, y.data());
      x.swap(y);
      xp = x.data();
    }
    // A unit scale adds the term (mulf(1, x) is x).
    if (t.scale == f.one()) {
      for (size_t i = 0; i < e.n; ++i) f.add(out[i], xp[i]);
    } else {
      for (size_t i = 0; i < e.n; ++i) f.add(out[i], f.mulf(t.scale, xp[i]));
    }
  }
  return out;
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LINEAR_H_
