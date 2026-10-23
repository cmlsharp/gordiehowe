// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the expression DAG.
//
// An expression Expr<F, T> is a node of a DAG over values of one field F:
// affine leaves (Lin<F>: handles, scalings, operators), constants, sums,
// products, sums and products of coordinates (of all of them, or along an
// axis), views (rotate, reindex, slice, concat: index maps over their
// operands), and Logic's gadgets as builders (the comparisons < <= == !=,
// any, all, mux), plus materialize, an explicit layer boundary.
// T is the C++ type of its values (Bit, Subfield<S>, Field), so the
// builders and assert_true take Bit expressions only. + and * broadcast by
// NumPy's rule (shapes aligned on the trailing axes, each axis equal, 1 or
// missing). A handle is an Expr of its type (core.h's Ref derives from
// it), and plain C++ integers and arrays of them lift to constants of the
// other operand's field.
//
// An expression is never committed. A C++ variable bound to one (auto y =
// e) names its node, and every predicate that reads y reads that node.
// Nothing is expanded into monomials. A circuit emits the DAG node by node
// with Logic's representation c0 + c1 x of a value (Logic::BitW), each
// shared node once, so a non-affine expression's intermediate results are
// circuit wires. The builders call Logic's balanced implementations
// themselves (lt_reduce, eq_reduce, the balanced AND/OR trees, mux), a
// product of coordinates is a balanced tree of multiplications, and a
// chain such as a * b * c * d is one balanced tree. The same emitter over
// Logic's EvaluationBackend evaluates an expression on host values, so the
// host and the circuit compute one function.
//
// A predicate (Domain::assert_zero, assert_true) holds an expression;
// the domain places it when it compiles (domain.h): affine rows, quadratic
// triples, a field batch or the domain's circuit, reading its degree
// (expr_degree).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXPR_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXPR_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <set>
#include <unordered_set>
#include <string>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ops/operators.h"

namespace proofs::gordiehowe {

enum class ExprOp : uint8_t {
  kLin = 0,     // an affine leaf (Lin<F>, no constant term)
  kConst = 1,   // constants, one per coordinate
  kAdd = 2,     // a + b
  kScale = 3,   // k a, k a constant
  kMul = 4,     // a b, coordinatewise
  kSum = 5,     // sums of coordinates: of all of them (w = 0, a scalar), or
                // of each group of w along the last axis
  kBroadcast = 6,  // A repeated over a shape: coordinate i reads A's i mod n
  kNot = 7,     // Bit: 1 - a
  kAnd = 8,     // Bit: a b
  kOr = 9,      // Bit: a + b - a b
  kXor = 10,    // Bit: a + b - 2 a b
  kMux = 11,    // c ? t : e
  kLt = 12,     // Bit words [..., w]: a < b (Logic::lt)
  kLeq = 13,    // a <= b (Logic::leq)
  kEq = 14,     // a == b (Logic::eq)
  // 15 is unused.
  kAny = 16,    // OR over the last axis
  kAll = 17,    // AND over the last axis
  kMaterialize = 18,  // a layer boundary (ntt_gadget::share)
  kProd = 19,   // products of each group of w coordinates along the last
                // axis: balanced trees of multiplications
  kGather = 20,  // a view: coordinate i is coordinate idx[i] of the kids'
                 // coordinates, concatenated in order
  kApply = 21,  // a linear operator (apply) applied to the kid
  kConv = 22,   // conv(a, b): the acyclic convolutions of a [..., la] and
                // b [..., lb] along the last axis, [..., la + lb - 1]
};

// How the compiler realizes conv(x, y) (compiler/conv.h): kAuto lets the
// placement rule choose by the domain's rates; a pin fixes one of the two
// forms (the values are those of the system description).
//   kDirect  C committed, C_i = sum_{a+b=i} x_a y_b in the circuit
//   kBatch   z = NTT_M(x) NTT_M(y) committed and proved by one field batch
//            over the affine views NTT_M(x), C = INTT_M(z)
enum class ConvRealization : uint8_t {
  kAuto = 0,
  kDirect = 1,
  kBatch = 3,
};
inline const char *conv_realization_name(ConvRealization r) {
  switch (r) {
    case ConvRealization::kDirect:
      return "direct";
    case ConvRealization::kBatch:
      return "batch";
    default:
      return "auto";
  }
}

// Whether an expression of type T in field F is marked as bits in its
// description: a Bit, or in characteristic 2 a Subfield<GF<1>>, which is
// GF(2) and stored as a Bit.
template <class F, class T>
constexpr bool marks_bits_v =
    is_bit_v<T> ||
    (F::kCharacteristicTwo && std::is_same_v<T, Subfield<GF<1>>>);

// An immutable index array, shared by every view with the same entries: a
// loop of rounds builds the same rotations and index maps once per round,
// and each copy would hold its own entries.
class IndexArray {
 public:
  IndexArray() : p_(empty()) {}
  IndexArray(std::vector<size_t> v)  // NOLINT
      : p_(intern(std::move(v))) {}
  size_t size() const { return p_->v.size(); }
  size_t operator[](size_t i) const { return p_->v[i]; }
  size_t at(size_t i) const { return p_->v.at(i); }
  auto begin() const { return p_->v.begin(); }
  auto end() const { return p_->v.end(); }
  const std::vector<size_t> &vec() const { return p_->v; }
  // The entries' SHA-256, which a description writes in place of them.
  const std::array<uint8_t, kSHA256DigestSize> &digest() const {
    return p_->digest;
  }
  // Equal arrays share one object.
  const void *id() const { return p_.get(); }

 private:
  struct Rep {
    std::vector<size_t> v;
    std::array<uint8_t, kSHA256DigestSize> digest{};
  };
  static std::shared_ptr<const Rep> empty() {
    static const std::shared_ptr<const Rep> e = make({});
    return e;
  }
  static std::shared_ptr<const Rep> make(std::vector<size_t> v) {
    auto r = std::make_shared<Rep>();
    r->v = std::move(v);
    SHA256 sha;
    sha.Update8(r->v.size());
    for (size_t x : r->v) sha.Update8(x);
    sha.DigestData(r->digest.data());
    return r;
  }
  static std::shared_ptr<const Rep> intern(std::vector<size_t> v) {
    static std::mutex mu;
    static std::map<std::array<uint8_t, kSHA256DigestSize>,
                    std::weak_ptr<const Rep>>
        cache;
    auto r = make(std::move(v));
    std::lock_guard<std::mutex> lock(mu);
    auto it = cache.find(r->digest);
    if (it != cache.end()) {
      if (auto old = it->second.lock(); old && old->v == r->v) return old;
    }
    // Drop expired entries now and then, so the cache stays small.
    if (cache.size() > 4096)
      for (auto i = cache.begin(); i != cache.end();)
        i = i->second.expired() ? cache.erase(i) : std::next(i);
    cache[r->digest] = r;
    return r;
  }
  std::shared_ptr<const Rep> p_;
};

// A value of an expression node's structure, computed once on first use
// (by any thread) and kept with the node; a copy of the node starts
// without it, since the copy's structure may change.
template <class T>
class StructureMemo {
 public:
  StructureMemo() = default;
  StructureMemo(const StructureMemo &) {}
  StructureMemo &operator=(const StructureMemo &) { return *this; }
  template <class Make>
  const T &get(Make make) const {
    std::call_once(once_, [&] { value_ = std::make_unique<const T>(make()); });
    return *value_;
  }

 private:
  mutable std::once_flag once_;
  mutable std::unique_ptr<const T> value_;
};

template <class F>
struct ExprNode;
// The coordinates of a gather resolved through the gathers below it: the
// operands it reaches that are not gathers (BASE), and per coordinate its
// operand (WHICH) and the coordinate there (AT).
template <class F>
struct GatherSources {
  std::vector<const ExprNode<F> *> base;
  std::vector<uint32_t> which;
  std::vector<size_t> at;
};

template <class F>
struct ExprNode {
  using Elt = typename F::Elt;
  ExprOp op = ExprOp::kLin;
  const F *f = nullptr;
  size_t n = 0;
  std::vector<size_t> shape;  // dims (empty: [n])
  std::vector<std::shared_ptr<const ExprNode>> kids;
  Lin<F> lin;          // kLin
  std::vector<Elt> c;  // kConst: n values; kScale: the factor
  size_t w = 0;        // builders: bits per word (the last axis); kSum and
                       // kProd: the group
  bool imm = false;    // comparisons against the constant
  uint64_t value = 0;  // VALUE
  IndexArray idx;      // kGather
  std::shared_ptr<const OpSpec<F>> apply;  // kApply
  // kConv: the realization its pin fixes (kAuto: the compiler's rule).
  std::shared_ptr<ConvRealization> conv_pin;
  // Derived properties.
  bool bit = false;         // the values are 0 or 1 (logic results)
  bool logic = false;       // contains a builder or materialize
  bool structured = false;  // a leaf applies an operator a circuit cannot
                            // expand (OpSpec::emit absent or refused, or
                            // public dependencies)
  std::string structured_op;
  // The name of the public value the compiler lifts this node into
  // (Expr::named, compiler/public_expr.h); it is not part of the
  // description.
  std::string label;
  std::vector<size_t> dims() const {
    return shape.empty() ? std::vector<size_t>{n} : shape;
  }
  // A shared kConst (shared_constant): the values' SHA-256, which a
  // description writes in place of them.
  std::array<uint8_t, kSHA256DigestSize> cdigest{};
  bool has_cdigest = false;
  // Whether DirectEval takes the expression rooted here (-1: not yet
  // asked). A memo of the structure, not part of the description.
  mutable int8_t direct = -1;
  // kGather: its coordinates' sources (DirectEval), a memo of the
  // structure, not part of the description.
  StructureMemo<GatherSources<F>> gather_sources;
};

// Constants of at least this many coordinates are shared between equal
// lifts and described by their digest.
constexpr size_t kSharedConstant = 64;

// Where a predicate lands (Domain::assert_zero, assert_true). kAuto
// lets the domain place it when it compiles:
//   affine rows        an affine expression (Lin plus constants), and
//                      every predicate that reads a structured operator;
//   otherwise the cheapest admissible target by the profile's measured
//   rates (placement.h):
//   quadratic triples  a b - c with a, b, c committed phase-0 Field cells;
//   field batch        a polynomial of degree at most 2 in relatively packed
//                      phase-0 subfield cells (quadratic_form);
//   circuit            anything.
// Batched relations the application declares stay explicit (batch).
enum class Placement : uint8_t {
  kAuto = 0,
  kAffine = 1,
  kQuadratic = 2,
  kCircuit = 3,
  kBatch = 4,
};
inline const char *placement_name(Placement p) {
  switch (p) {
    case Placement::kAffine:
      return "affine rows";
    case Placement::kQuadratic:
      return "quadratic triples";
    case Placement::kCircuit:
      return "circuit";
    case Placement::kBatch:
      return "field batch";
    default:
      return "auto";
  }
}
// A declared predicate: pin(where) fixes its placement before compile. A
// predicate the compiler realizes by a lowering of its own (a cross-field
// equality, assert_mod) has no placement, and pinning it is a
// CompileError.
class Predicate {
 public:
  Predicate() = default;
  explicit Predicate(std::shared_ptr<Placement> p) : p_(std::move(p)) {}
  // The predicate WHAT, which has no placement.
  static Predicate unplaced(std::string what) {
    Predicate p;
    p.unplaced_ = std::move(what);
    return p;
  }
  const Predicate &pin(Placement where) const {
    if (p_ == nullptr)
      fail(unplaced_ + " has no placement to pin: its lowering realizes it");
    *p_ = where;
    return *this;
  }
  Placement pinned() const { return p_ ? *p_ : Placement::kAuto; }

 private:
  std::shared_ptr<Placement> p_;
  std::string unplaced_;
};

// Whether a circuit can expand operator OP: it has no dependencies, and a
// circuit expansion, its constant matrix (OpSpec::emit) or a staged
// transform's butterflies.
template <class F>
bool circuit_expandable(const OpSpec<F> &op) {
  return op.deps.empty() && (op.staged != nullptr || op.emit != nullptr);
}

// The circuit expansion of OP on the wires W, with the Logic object LC: a
// staged transform's butterflies (one transform per block of a batched
// one), or the sparse rows of its constant matrix.
template <class F, class LC>
std::vector<typename LC::EltW> expand_operator(
    const LC &lc, const OpSpec<F> &op,
    const std::vector<typename LC::EltW> &w) {
  if (op.staged != nullptr) {
    const size_t n = op.staged->n;
    if (n == 0 || w.size() % n != 0 || op.rows != w.size())
      fail("the staged transform '" + op.name + "' reads " +
           std::to_string(w.size()) + " wires");
    std::vector<typename LC::EltW> out;
    out.reserve(w.size());
    for (size_t at = 0; at < w.size(); at += n) {
      std::vector<typename LC::EltW> a(w.begin() + long(at),
                                       w.begin() + long(at + n));
      op.staged->forward(lc, a);
      out.insert(out.end(), a.begin(), a.end());
    }
    return out;
  }
  const auto rows = op.emit();
  std::vector<typename LC::EltW> out(rows.size());
  for (size_t r = 0; r < rows.size(); ++r) {
    if (rows[r].empty()) {
      out[r] = lc.konst(lc.elt(0));
      continue;
    }
    for (size_t k = 0; k < rows[r].size(); ++k) {
      const auto &[c, a] = rows[r][k];
      const auto x = a == lc.one() ? w.at(c) : lc.mul(a, w.at(c));
      out[r] = k == 0 ? x : lc.add(out[r], x);
    }
  }
  return out;
}

template <class F>
using ExprPtr = std::shared_ptr<const ExprNode<F>>;

namespace expr_internal {

using const_internal::const_flatten;
using const_internal::ConstLeafType;
using const_internal::index_array;

template <class F>
std::shared_ptr<ExprNode<F>> node(ExprOp op, const F *f, size_t n,
                                  std::vector<size_t> shape) {
  auto e = std::make_shared<ExprNode<F>>();
  e->op = op;
  e->f = f;
  e->n = n;
  e->shape = std::move(shape);
  return e;
}
template <class F>
void inherit(ExprNode<F> &e) {
  for (const auto &k : e.kids) {
    e.logic |= k->logic;
    if (k->structured && !e.structured) {
      e.structured = true;
      e.structured_op = k->structured_op;
    }
  }
}
template <class F>
ExprPtr<F> leaf(Lin<F> l) {
  auto e = node<F>(ExprOp::kLin, l.f, l.n, l.shape);
  for (const auto &t : l.terms)
    for (const auto &op : t.chain)
      if (!circuit_expandable(*op) && !e->structured) {
        e->structured = true;
        e->structured_op = op->name;
      }
  e->lin = std::move(l);
  return e;
}
template <class F>
ExprPtr<F> constant(const F *f, std::vector<typename F::Elt> c,
                    std::vector<size_t> shape) {
  auto e = node<F>(ExprOp::kConst, f, c.size(), std::move(shape));
  e->c = std::move(c);
  return e;
}
// C, a kConst of at least kSharedConstant coordinates, as the node of an
// equal constant lifted before, if one is alive: a loop of rounds lifts its
// round constants once per round.
template <class F>
ExprPtr<F> shared_constant(ExprPtr<F> c) {
  if (c->op != ExprOp::kConst || c->n < kSharedConstant) return c;
  auto d = std::make_shared<ExprNode<F>>(*c);
  {
    SHA256 sha;
    sha.Update8(d->c.size());
    for (const auto &x : d->c) {
      uint8_t b[F::kBytes];
      d->f->to_bytes_field(b, x);
      sha.Update(b, F::kBytes);
    }
    sha.DigestData(d->cdigest.data());
    d->has_cdigest = true;
  }
  static std::mutex mu;
  static std::map<std::array<uint8_t, kSHA256DigestSize + 1>,
                  std::vector<std::weak_ptr<const ExprNode<F>>>>
      cache;
  std::array<uint8_t, kSHA256DigestSize + 1> key{};
  std::copy(d->cdigest.begin(), d->cdigest.end(), key.begin());
  key[kSHA256DigestSize] = d->bit ? 1 : 0;
  std::lock_guard<std::mutex> lock(mu);
  if (cache.size() > 4096)
    for (auto i = cache.begin(); i != cache.end();) {
      auto &v = i->second;
      v.erase(std::remove_if(v.begin(), v.end(),
                             [](const auto &w) { return w.expired(); }),
              v.end());
      i = v.empty() ? cache.erase(i) : std::next(i);
    }
  auto &slot = cache[key];
  for (const auto &w : slot)
    if (auto old = w.lock())
      if (old->f == d->f && old->dims() == d->dims() && old->c == d->c)
        return old;
  ExprPtr<F> out = d;
  slot.push_back(out);
  return out;
}
template <class F>
ExprPtr<F> gather_node(std::vector<ExprPtr<F>> kids, std::vector<size_t> idx,
                       std::vector<size_t> dims);
// A broadcast to DIMS (NumPy's rule): a scalar repeated (kBroadcast), or a
// view of A whose length-1 and missing axes repeat (kGather).
template <class F>
ExprPtr<F> broadcast(ExprPtr<F> a, const std::vector<size_t> &dims,
                     const char *what = "broadcast") {
  if (a->n != 1) {
    auto idx = broadcast_map(dims, a->dims(), what);
    return gather_node<F>({std::move(a)}, std::move(idx), dims);
  }
  size_t n = 1;
  for (size_t d : dims) n *= d;
  auto e = node<F>(ExprOp::kBroadcast, a->f, n, dims);
  e->bit = a->bit;
  e->kids = {std::move(a)};
  inherit(*e);
  return e;
}
// A and B over one shape: a scalar side is broadcast, and other shapes
// broadcast by NumPy's rule (aligned on the trailing axes, each axis pair
// equal or one of them 1 or missing).
template <class F>
void conform(ExprPtr<F> &a, ExprPtr<F> &b, const char *what) {
  if (a->n == b->n) return;
  if (a->n == 1) {
    a = broadcast(a, b->dims(), what);
    return;
  }
  if (b->n == 1) {
    b = broadcast(b, a->dims(), what);
    return;
  }
  const auto out = broadcast_shape(a->dims(), b->dims(), what);
  if (a->dims() != out) a = broadcast(a, out, what);
  if (b->dims() != out) b = broadcast(b, out, what);
}
template <class F>
ExprPtr<F> binary(ExprOp op, ExprPtr<F> a, ExprPtr<F> b, const char *what) {
  conform(a, b, what);
  auto e = node<F>(op, a->f, a->n, a->shape.empty() ? b->shape : a->shape);
  e->kids = {std::move(a), std::move(b)};
  inherit(*e);
  return e;
}
template <class F>
ExprPtr<F> scale(ExprPtr<F> a, const typename F::Elt &k) {
  auto e = node<F>(ExprOp::kScale, a->f, a->n, a->shape);
  e->c = {k};
  e->kids = {std::move(a)};
  inherit(*e);
  return e;
}
template <class F>
ExprPtr<F> logic(ExprOp op, std::vector<ExprPtr<F>> kids, size_t n,
                 std::vector<size_t> shape) {
  auto e = node<F>(op, kids.at(0)->f, n, std::move(shape));
  e->kids = std::move(kids);
  e->bit = true;
  inherit(*e);
  e->logic = true;
  return e;
}
// conv(A, B) along the last axis: A [..., la] and B [..., lb] with the
// same leading axes (or B of rank 1, shared by every row of A), out
// [..., la + lb - 1].
template <class F>
ExprPtr<F> conv_node(ExprPtr<F> a, ExprPtr<F> b) {
  const auto da = a->dims();
  const auto db = b->dims();
  const size_t la = da.back();
  const size_t lb = db.back();
  if (la == 0 || lb == 0) fail("conv: an empty operand");
  const std::vector<size_t> lead_a(da.begin(), da.end() - 1);
  const std::vector<size_t> lead_b(db.begin(), db.end() - 1);
  if (lead_b != lead_a) {
    if (!lead_b.empty())
      fail("conv: the operands' leading axes differ");
    std::vector<size_t> want = lead_a;
    want.push_back(lb);
    b = broadcast(b, want, "conv");
  }
  std::vector<size_t> out = lead_a;
  out.push_back(la + lb - 1);
  size_t n = 1;
  for (size_t d : out) n *= d;
  auto e = node<F>(ExprOp::kConv, a->f, n, out);
  e->kids = {std::move(a), std::move(b)};
  e->conv_pin = std::make_shared<ConvRealization>(ConvRealization::kAuto);
  inherit(*e);
  return e;
}

}  // namespace expr_internal

// An expression of field F whose values have type T.
template <class F, class T = Field>
struct Expr {
  using field_type = F;
  using type_tag = T;
  ExprPtr<F> node;

  Expr() = default;
  explicit Expr(ExprPtr<F> p) : node(std::move(p)) {}
  // A handle (bit views and circuit-only values included: a circuit reads
  // them; an affine placement checks its leaves when the domain compiles):
  // a new leaf, so that each conversion is its own node, as the system
  // digest describes it.
  template <class P>
  Expr(const Ref<F, T, P> &r)  // NOLINT
      : node(handle_node(r)) {
    static_assert(!is_bytes_v<T>,
                  "an expression reads a Bytes statement: read it through a "
                  "public computation");
  }
  // An affine expression (Field).
  template <class U = T, class = std::enable_if_t<is_field_v<U>>>
  Expr(const Lin<F> &l)  // NOLINT
      : node(expr_internal::leaf(l)) {}
  // An expression of another type, read as Field (or as an untracked
  // type).
  template <class U, class = std::enable_if_t<!std::is_same_v<U, T> &&
                                              (is_field_v<T> ||
                                               is_any_type_v<T>)>>
  Expr(const Expr<F, U> &e) : node(e.node) {}  // NOLINT
  // A handle of another type, read as Field.
  template <class U, class P,
            class = std::enable_if_t<!std::is_same_v<U, T> &&
                                     (is_field_v<T> || is_any_type_v<T>)>>
  Expr(const Ref<F, U, P> &r)  // NOLINT
      : Expr(Expr<F, U>(r)) {}

  const F *f() const { return node->f; }
  size_t size() const { return node->n; }
  std::vector<size_t> dims() const { return node->dims(); }

  // The affine leaf of a handle (no static check on its placement).
  template <class U, class P>
  static Lin<F> handle_lin(const Ref<F, U, P> &r) {
    Lin<F> l;
    l.f = r.f;
    l.n = r.n;
    l.shape = r.shape;
    l.g = r.g;
    l.terms.push_back(Term<F>{r.f->one(), {}, r.id, r.n});
    return l;
  }
  // The leaf node of a handle of type U: its affine leaf, marked Bit when
  // U is Bit, or Subfield<GF<1>> in characteristic 2 (GF(2), stored as a
  // Bit), so both tags describe the same node alike.
  template <class U, class P>
  static ExprPtr<F> handle_node(const Ref<F, U, P> &r) {
    auto e = expr_internal::node<F>(ExprOp::kLin, r.f, r.n, r.shape);
    e->lin = handle_lin(r);
    e->bit = marks_bits_v<F, U>;
    return e;
  }

  // ------------------------------------------------------- methods --
  // (Defined below, after the builders they use.)

  // The sum of every coordinate (a scalar), or the sums along AXIS (the
  // axis dropped). Degree: X's.
  auto sum() const;
  auto sum(size_t axis) const;
  // The product of every coordinate (a scalar), or the products along
  // AXIS: balanced trees of multiplications. Degree: X's times the number
  // of factors.
  auto prod() const;
  auto prod(size_t axis) const;
  // Bit: c ? t : e, coordinatewise (T and E handles, expressions or
  // constants; a scalar side, or a side missing leading axes, broadcasts).
  template <class X, class Y>
  auto mux(const X &t, const Y &e) const;
  // Bit: the OR and the AND along AXIS (balanced trees; the axis dropped).
  auto any(size_t axis) const;
  auto all(size_t axis) const;

  // Views: index maps of this expression's coordinates (no node is
  // committed, and a circuit reads the operand's wires).
  // out[i] = x[i - k] along AXIS, cyclically: a positive K moves the
  // entries toward higher indices (NumPy's roll, Keccak's ROT).
  auto rotate(long k, size_t axis) const;
  // A general index map (NumPy's fancy indexing of the flattened value):
  // entry j is flat coordinate IDX[j], and the view has IDX's shape (a
  // public index array: a std::vector, or a std::array or C array of any
  // rank); x[idx] is the same view. With an axis, the indices IDX (rank 1)
  // of AXIS.
  auto reindex(const std::vector<size_t> &idx) const;
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  auto reindex(const K &idx) const;
  auto reindex(const std::vector<size_t> &idx, size_t axis) const;
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  auto reindex(const K &idx, size_t axis) const;
  template <class K, class = std::enable_if_t<kIsConstArray<K>>>
  auto operator[](const K &idx) const {
    return reindex(idx);
  }
  // Indices [B, E) of AXIS.
  auto slice(size_t b, size_t e, size_t axis = 0) const;
  // Index I of AXIS, the axis dropped; x[i] and x.at(i) on the leading
  // axis.
  auto at(size_t axis, size_t i) const;
  auto at(size_t i) const;
  auto operator[](size_t i) const;
  auto reshape(const Shape &s) const;
  auto flat() const;
  // This expression followed by Y along AXIS (the other axes agree).
  template <class Y>
  auto concat(const Y &y, size_t axis = 0) const;
  // The integers of the digit vectors on the last axis in BASE, least
  // significant first: [..., k] -> [...], as sum_l BASE^l x[..., l]. BASE
  // is an integer or an element of F (in characteristic 2, x8 packs eight
  // bits into one element of GF(2^8)).
  template <class B>
  auto from_digits(const B &base) const;
  // Bit words [..., w] as integers of width w (Word).
  auto from_bits() const;

  // This expression, its public value named NM: when every leaf is public
  // and the compiler evaluates it outside the circuit
  // (compiler/public_expr.h), the value it lifts is NM. A copy of the node,
  // so the expression it names is unchanged.
  Expr named(const std::string &nm) const {
    auto n = std::make_shared<ExprNode<F>>(*node);
    n->label = nm;
    return Expr(ExprPtr<F>(std::move(n)));
  }
};

// ------------------------------------------------------------ traits --

template <class X>
struct IsExprT : std::false_type {};
template <class F, class T>
struct IsExprT<Expr<F, T>> : std::true_type {};
template <class X>
constexpr bool kIsExprT = IsExprT<std::decay_t<X>>::value;

// An integer of known width (x.from_bits()): Bit words [..., w], least
// significant bit first, read as the integers [...] below 2^w. Its value is
// x.from_digits(2), and the comparisons (< <= == !=) read its bits.
template <class F>
struct Word {
  using field_type = F;
  ExprPtr<F> bits;  // [..., w]
  size_t width = 0;
  ExprPtr<F> value;  // [...]
  std::vector<size_t> dims() const { return value->dims(); }
};
template <class X>
struct IsWord : std::false_type {};
template <class F>
struct IsWord<Word<F>> : std::true_type {};
template <class X>
constexpr bool kIsWord = IsWord<std::decay_t<X>>::value;

// Handles, affine expressions and expressions: what the predicates and
// builders take.
template <class X, class = void>
struct PolyOf {
  static constexpr bool value = false;
};
template <class F, class T, class P>
struct PolyOf<Ref<F, T, P>> {
  static constexpr bool value = true;
  using field = F;
  using type = std::conditional_t<is_any_type_v<T>, Field, T>;
};
template <class F>
struct PolyOf<Lin<F>> {
  static constexpr bool value = true;
  using field = F;
  using type = Field;
};
template <class F, class T>
struct PolyOf<Expr<F, T>> {
  static constexpr bool value = true;
  using field = F;
  using type = std::conditional_t<is_any_type_v<T>, Field, T>;
};
template <class F>
struct PolyOf<Word<F>> {
  static constexpr bool value = true;
  using field = F;
  using type = Field;
};
template <class X>
constexpr bool kIsPoly = PolyOf<std::decay_t<X>>::value;
template <class X>
using PolyField = typename PolyOf<std::decay_t<X>>::field;
template <class X>
using PolyType = typename PolyOf<std::decay_t<X>>::type;

// The expression of a handle, an affine expression or an expression.
template <class X, class = std::enable_if_t<kIsPoly<X>>>
Expr<PolyField<X>, PolyType<X>> as_expr(const X &x) {
  using F = PolyField<X>;
  using T = PolyType<X>;
  if constexpr (kIsExprT<X>) {
    return Expr<F, T>(x.node);
  } else if constexpr (kIsWord<X>) {
    return Expr<F, T>(x.value);
  } else if constexpr (IsRef<std::decay_t<X>>::value) {
    if constexpr (std::is_same_v<typename std::decay_t<X>::type_tag, T>) {
      return Expr<F, T>(x);
    } else {
      return Expr<F, T>(Expr<F, T>::handle_lin(x));
    }
  } else {
    return Expr<F, T>(x);
  }
}
template <class X>
ExprPtr<PolyField<X>> expr_node(const X &x) {
  return as_expr(x).node;
}

// The type of a + b and of a b: a Subfield type when both sides have it,
// Bit for a product of Bits, and for a sum or difference of Bits in
// characteristic 2 (where + is XOR), Field otherwise.
template <class T, class U>
using SumType =
    std::conditional_t<std::is_same_v<T, U> && is_subfield_v<T>, T, Field>;
template <class F, class T, class U>
using SumTypeIn = std::conditional_t<F::kCharacteristicTwo && is_bit_v<T> &&
                                         is_bit_v<U>,
                                     Bit, SumType<T, U>>;
template <class T, class U>
using ProductType =
    std::conditional_t<std::is_same_v<T, U> && (is_subfield_v<T> || is_bit_v<T>),
                       T, Field>;
namespace expr_internal {
// E with the Bit flag when R is Bit (a sum of Bits in characteristic 2),
// or GF(2) (marks_bits_v).
template <class R, class F>
ExprPtr<F> typed(ExprPtr<F> e) {
  if (!marks_bits_v<F, R> || e->bit) return e;
  auto b = std::make_shared<ExprNode<F>>(*e);
  b->bit = true;
  return b;
}
}  // namespace expr_internal

// A constant of F: an integer (its canonical element, negated when
// negative), whose absolute value lies below the characteristic, or an
// element. An integer outside that range is a CompileError.
template <class F, class K>
typename F::Elt constant_of(const F &f, const K &k) {
  if constexpr (std::is_same_v<K, bool>) {
    return k ? f.one() : f.zero();
  } else if constexpr (std::is_integral_v<K>) {
    bool neg = false;
    uint64_t mag = uint64_t(k);
    if constexpr (std::is_signed_v<K>) {
      if (k < 0) {
        neg = true;
        mag = uint64_t(-(k + 1)) + 1;
      }
    }
    if (!characteristic_above(f, Bound(mag)))
      fail("the constant " + std::string(neg ? "-" : "") +
           std::to_string(mag) +
           " lies outside the field's integers (its absolute value is not "
           "below the characteristic " +
           bound_str(field_characteristic(f)) + ")");
    return neg ? f.negf(f.of_scalar(mag)) : f.of_scalar(mag);
  } else {
    return k;
  }
}
template <class X, class K, class = void>
struct IsConstantOf : std::false_type {};
template <class X, class K>
struct IsConstantOf<X, K, std::enable_if_t<kIsPoly<X>>>
    : std::bool_constant<std::is_integral_v<K> ||
                         std::is_same_v<std::decay_t<K>,
                                        typename PolyField<X>::Elt>> {};
template <class X, class K>
constexpr bool kIsConstantOf = IsConstantOf<X, K>::value;

namespace expr_internal {
// VALUES (integers, or field elements) as a constant node of F with DIMS
// (the array's own shape when empty).
template <class F, class K>
ExprPtr<F> lift_array(const F &f, const K &values,
                      std::vector<size_t> dims = {}) {
  std::vector<typename F::Elt> c;
  std::vector<size_t> own;
  if constexpr (kIsConstArray<K>) {
    std::vector<ConstLeafType<K>> v;
    const_flatten(values, 0, own, v);
    for (const auto &x : v) c.push_back(constant_of(f, x));
  } else {
    for (const auto &x : values) c.push_back(constant_of(f, x));
    own = {c.size()};
  }
  if (dims.empty()) dims = own;
  size_t n = 1;
  for (size_t d : dims) n *= d;
  if (n != c.size())
    fail("constant: " + std::to_string(c.size()) +
         " values for a shape of " + std::to_string(n));
  return shared_constant<F>(constant<F>(&f, std::move(c), std::move(dims)));
}
// VALUES, each 0 or 1, as a Bit constant (a scalar for an integer).
template <class F, class K>
ExprPtr<F> lift_bits(const F &f, const K &values, std::vector<size_t> dims,
                     const char *what) {
  std::vector<uint64_t> v;
  std::vector<size_t> own;
  if constexpr (std::is_integral_v<K>) {
    if (values != 0 && values != 1)
      fail(std::string(what) + ": the constant " + std::to_string(values) +
           " is not a bit");
    v.push_back(uint64_t(values));
    own = {1};
  } else {
    std::vector<ConstLeafType<K>> x;
    const_flatten(values, 0, own, x);
    for (const auto &b : x) {
      if (b != 0 && b != 1)
        fail(std::string(what) + ": the constant " + std::to_string(b) +
             " is not a bit");
      v.push_back(uint64_t(b));
    }
  }
  if (dims.empty()) dims = own;
  auto e = std::make_shared<ExprNode<F>>(*lift_array(f, v, dims));
  e->bit = true;
  return shared_constant<F>(std::move(e));
}
template <class X, class K>
constexpr bool kArrayPair = kIsPoly<X> && kIsConstArray<K>;
}  // namespace expr_internal
// ---------------------------------------------------------- arithmetic --

namespace expr_internal {
// An expression or a word (x.from_bits(), read as its value) on either
// side: v - b.from_bits() with v and b handles is an expression.
template <class X, class Y>
constexpr bool kExprPair =
    kIsPoly<X> && kIsPoly<Y> &&
    (kIsExprT<X> || kIsExprT<Y> || kIsWord<X> || kIsWord<Y>);
}  // namespace expr_internal

// a + b and a - b with an expression on either side (a handle plus a handle
// stays an affine Lin, operators.h).
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kExprPair<X, Y>>>
Expr<PolyField<X>, SumTypeIn<PolyField<X>, PolyType<X>, PolyType<Y>>>
operator+(const X &x, const Y &y) {
  static_assert(std::is_same_v<PolyField<X>, PolyField<Y>>,
                "an expression adds values of one field");
  using R = SumTypeIn<PolyField<X>, PolyType<X>, PolyType<Y>>;
  return Expr<PolyField<X>, R>(expr_internal::typed<R>(
      expr_internal::binary(ExprOp::kAdd, expr_node(x), expr_node(y), "+")));
}
// -x: in characteristic 2 a Bit stays a Bit (-x = x).
template <class X, class = std::enable_if_t<kIsExprT<X>>>
Expr<PolyField<X>, SumTypeIn<PolyField<X>, PolyType<X>, PolyType<X>>>
operator-(const X &x) {
  using R = SumTypeIn<PolyField<X>, PolyType<X>, PolyType<X>>;
  const auto &f = *x.f();
  return Expr<PolyField<X>, R>(
      expr_internal::typed<R>(expr_internal::scale(x.node, f.mone())));
}
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kExprPair<X, Y>>>
Expr<PolyField<X>, SumTypeIn<PolyField<X>, PolyType<X>, PolyType<Y>>>
operator-(const X &x, const Y &y) {
  static_assert(std::is_same_v<PolyField<X>, PolyField<Y>>,
                "an expression subtracts values of one field");
  using R = SumTypeIn<PolyField<X>, PolyType<X>, PolyType<Y>>;
  const auto yn = expr_node(y);
  return Expr<PolyField<X>, R>(expr_internal::typed<R>(
      expr_internal::binary(ExprOp::kAdd, expr_node(x),
                            expr_internal::scale(yn, yn->f->mone()), "-")));
}
// a b, coordinatewise, for any two of handles, affine expressions and
// expressions.
template <class X, class Y,
          class = std::enable_if_t<kIsPoly<X> && kIsPoly<Y>>>
Expr<PolyField<X>, ProductType<PolyType<X>, PolyType<Y>>> operator*(
    const X &x, const Y &y) {
  static_assert(std::is_same_v<PolyField<X>, PolyField<Y>>,
                "an expression multiplies values of one field");
  auto e = expr_internal::binary(ExprOp::kMul, expr_node(x), expr_node(y), "*");
  if constexpr (marks_bits_v<PolyField<X>, PolyType<X>> &&
                marks_bits_v<PolyField<X>, PolyType<Y>>) {
    auto b = std::make_shared<ExprNode<PolyField<X>>>(*e);
    b->bit = true;
    e = b;
  }
  return Expr<PolyField<X>, ProductType<PolyType<X>, PolyType<Y>>>(e);
}

// conv(x, y): the acyclic convolution of x [..., lx] and y [..., ly] along
// the last axis, [..., lx + ly - 1], coefficient i the sum of x_a y_b over
// a + b = i (y of rank 1 is shared by every row of x). A bilinear node of
// degree deg x + deg y; interval propagation bounds coefficient i by its
// terms' products and their count (compiler/range.h). The compiler
// realizes it (compiler/conv.h) by the placement rule, or as pin(r) fixes
// (ConvRealization). With a public operand it is the affine public
// convolution (ops/operators.h: conv(x, h, EntryBound)).
namespace expr_internal {
template <class X>
constexpr bool kPublicRef = false;
template <class F, class T>
constexpr bool kPublicRef<Ref<F, T, Public>> = true;
}  // namespace expr_internal
template <class F>
struct ConvExpr : Expr<F, Field> {
  explicit ConvExpr(ExprPtr<F> p) : Expr<F, Field>(std::move(p)) {}
  // Fixes the realization (kAuto restores the placement rule).
  const ConvExpr &pin(ConvRealization r) const {
    *this->node->conv_pin = r;
    return *this;
  }
};
template <class F>
struct IsExprT<ConvExpr<F>> : std::true_type {};
template <class F>
struct PolyOf<ConvExpr<F>> {
  static constexpr bool value = true;
  using field = F;
  using type = Field;
};
template <class X, class Y,
          class = std::enable_if_t<
              kIsPoly<X> && kIsPoly<Y> &&
              !expr_internal::kPublicRef<std::decay_t<X>> &&
              !expr_internal::kPublicRef<std::decay_t<Y>>>>
ConvExpr<PolyField<X>> conv(const X &x, const Y &y) {
  static_assert(std::is_same_v<PolyField<X>, PolyField<Y>>,
                "conv: both operands lie in one field");
  static_assert(!PolyField<X>::kCharacteristicTwo,
                "conv: integer convolutions exist in odd characteristic");
  return ConvExpr<PolyField<X>>(
      expr_internal::conv_node(expr_node(x), expr_node(y)));
}

// conv(x, h) with h public: the affine public convolution
// AcyclicConv(h, lx)(x), [..., lx] -> [..., lx + lh - 1]; with EntryBound
// the operator carries its row bound, so interval propagation bounds the
// result (without one, h's coefficients may be anything below p and the
// operator bounds no row).
template <class X, class F, class T,
          class = std::enable_if_t<kIsPoly<X> &&
                                   std::is_same_v<PolyField<X>, F>>>
auto conv(const X &x, const Ref<F, T, Public> &h, ops::EntryBound eb) {
  const size_t lx = as_expr(x).dims().back();
  return ops::AcyclicConv(h, lx, eb)(x);
}
template <class X, class F, class T,
          class = std::enable_if_t<kIsPoly<X> &&
                                   std::is_same_v<PolyField<X>, F>>>
auto conv(const X &x, const Ref<F, T, Public> &h) {
  const size_t lx = as_expr(x).dims().back();
  return ops::AcyclicConv(h, lx)(x);
}

// Constants without wrapping: an integer or a field element on either side.
// k x of a handle or an affine expression stays affine (Lin) for an
// integer k, as an element k already does (operators.h).
template <class X, class K,
          class = std::enable_if_t<kIsPoly<X> && std::is_integral_v<K>>>
auto operator*(K k, const X &x) {
  const auto &f = *as_expr(x).f();
  if constexpr (kIsExprT<X>) {
    return Expr<PolyField<X>, Field>(
        expr_internal::scale(x.node, constant_of(f, k)));
  } else {
    return constant_of(f, k) * x;
  }
}
template <class X, class K,
          class = std::enable_if_t<kIsPoly<X> && std::is_integral_v<K>>>
auto operator*(const X &x, K k) {
  return k * x;
}
template <class X, class = std::enable_if_t<kIsExprT<X>>>
Expr<PolyField<X>, Field> operator*(const typename PolyField<X>::Elt &k,
                                    const X &x) {
  return Expr<PolyField<X>, Field>(expr_internal::scale(x.node, k));
}
template <class X, class = std::enable_if_t<kIsExprT<X>>>
Expr<PolyField<X>, Field> operator*(const X &x,
                                    const typename PolyField<X>::Elt &k) {
  return k * x;
}
namespace expr_internal {
template <class X, class K>
ExprPtr<PolyField<X>> plus_constant(const X &x, const K &k, bool negate_x) {
  using F = PolyField<X>;
  auto a = expr_node(x);
  const F &f = *a->f;
  if (negate_x) a = scale(a, f.mone());
  auto c = constant<F>(&f, {constant_of(f, k)}, {});
  return binary(ExprOp::kAdd, a, c, "+");
}
// The type of a lifted constant K of F: in characteristic 2 an integer
// constant is 0 or 1 (constant_of refuses others), a Bit; otherwise, and
// for a field element, Field.
template <class F, class K>
using LiftType =
    std::conditional_t<F::kCharacteristicTwo &&
                           std::is_integral_v<ConstLeafType<K>>,
                       Bit, Field>;
// The types of x + k and x k for a constant K: in characteristic 2 a Bit
// plus a bit constant is their XOR, a Bit.
template <class X, class K>
using PlusConstType =
    SumTypeIn<PolyField<X>, PolyType<X>, LiftType<PolyField<X>, K>>;
template <class X, class K>
using TimesConstType = ProductType<PolyType<X>, LiftType<PolyField<X>, K>>;
}  // namespace expr_internal
template <class X, class K,
          class = std::enable_if_t<kIsPoly<X> && kIsConstantOf<X, K>>>
Expr<PolyField<X>, expr_internal::PlusConstType<X, K>> operator+(const X &x,
                                                                 const K &k) {
  using R = expr_internal::PlusConstType<X, K>;
  return Expr<PolyField<X>, R>(
      expr_internal::typed<R>(expr_internal::plus_constant(x, k, false)));
}
template <class X, class K,
          class = std::enable_if_t<kIsPoly<X> && kIsConstantOf<X, K>>>
Expr<PolyField<X>, expr_internal::PlusConstType<X, K>> operator+(const K &k,
                                                                 const X &x) {
  return x + k;
}
template <class X, class K,
          class = std::enable_if_t<kIsPoly<X> && kIsConstantOf<X, K>>>
Expr<PolyField<X>, expr_internal::PlusConstType<X, K>> operator-(const X &x,
                                                                 const K &k) {
  using F = PolyField<X>;
  using R = expr_internal::PlusConstType<X, K>;
  const auto a = expr_node(x);
  const F &f = *a->f;
  const auto c = expr_internal::constant<F>(&f, {f.negf(constant_of(f, k))}, {});
  return Expr<F, R>(
      expr_internal::typed<R>(expr_internal::binary(ExprOp::kAdd, a, c, "+")));
}
template <class X, class K,
          class = std::enable_if_t<kIsPoly<X> && kIsConstantOf<X, K>>>
Expr<PolyField<X>, expr_internal::PlusConstType<X, K>> operator-(const K &k,
                                                                 const X &x) {
  using R = expr_internal::PlusConstType<X, K>;
  return Expr<PolyField<X>, R>(
      expr_internal::typed<R>(expr_internal::plus_constant(x, k, true)));
}
// x + k, x - k and x * k (either side) for a plain C++ array K: a constant
// of X's field in K's shape, broadcast like any operand.
template <class X, class K,
          std::enable_if_t<expr_internal::kArrayPair<X, K>, int> = 0>
Expr<PolyField<X>, expr_internal::PlusConstType<X, K>> operator+(const X &x,
                                                                 const K &k) {
  using R = expr_internal::PlusConstType<X, K>;
  const auto a = expr_node(x);
  return Expr<PolyField<X>, R>(expr_internal::typed<R>(expr_internal::binary(
      ExprOp::kAdd, a, expr_internal::lift_array(*a->f, k), "+")));
}
template <class X, class K,
          std::enable_if_t<expr_internal::kArrayPair<X, K>, int> = 0>
Expr<PolyField<X>, expr_internal::PlusConstType<X, K>> operator+(const K &k,
                                                                 const X &x) {
  return x + k;
}
template <class X, class K,
          std::enable_if_t<expr_internal::kArrayPair<X, K>, int> = 0>
Expr<PolyField<X>, expr_internal::PlusConstType<X, K>> operator-(const X &x,
                                                                 const K &k) {
  using R = expr_internal::PlusConstType<X, K>;
  const auto a = expr_node(x);
  const auto c = expr_internal::lift_array(*a->f, k);
  return Expr<PolyField<X>, R>(expr_internal::typed<R>(expr_internal::binary(
      ExprOp::kAdd, a, expr_internal::scale(c, a->f->mone()), "-")));
}
template <class X, class K,
          std::enable_if_t<expr_internal::kArrayPair<X, K>, int> = 0>
Expr<PolyField<X>, expr_internal::PlusConstType<X, K>> operator-(const K &k,
                                                                 const X &x) {
  using R = expr_internal::PlusConstType<X, K>;
  const auto a = expr_node(x);
  return Expr<PolyField<X>, R>(expr_internal::typed<R>(
      expr_internal::binary(ExprOp::kAdd, expr_internal::lift_array(*a->f, k),
                            expr_internal::scale(a, a->f->mone()), "-")));
}
template <class X, class K,
          std::enable_if_t<expr_internal::kArrayPair<X, K>, int> = 0>
Expr<PolyField<X>, expr_internal::TimesConstType<X, K>> operator*(const X &x,
                                                                  const K &k) {
  using R = expr_internal::TimesConstType<X, K>;
  const auto a = expr_node(x);
  return Expr<PolyField<X>, R>(expr_internal::typed<R>(expr_internal::binary(
      ExprOp::kMul, a, expr_internal::lift_array(*a->f, k), "*")));
}
template <class X, class K,
          std::enable_if_t<expr_internal::kArrayPair<X, K>, int> = 0>
Expr<PolyField<X>, expr_internal::TimesConstType<X, K>> operator*(const K &k,
                                                                  const X &x) {
  return x * k;
}

// VALUES (integers or elements of F: a std::vector, or an array of any
// rank) as a constant expression of F with shape SHAPE (VALUES' own shape
// when SHAPE is empty). Like a constant lifted from an operand, it belongs
// to no domain and enters the system digest with the predicate that reads
// it; D.constant(values) declares a value of domain D instead.
template <class F, class K>
Expr<F, Field> constant(const F &f, const K &values, Shape shape = {}) {
  return Expr<F, Field>(expr_internal::lift_array(f, values, shape.dims));
}

// X read as a Bit expression, unchecked: no Boolean check is added. The
// caller states in a comment why the Bit operations it applies are sound,
// for example that every coordinate is 0 or 1, or that the operation is
// exact on any value (all() is a tree of products).
template <class X, class = std::enable_if_t<kIsPoly<X>>>
Expr<PolyField<X>, Bit> unchecked_bit(const X &x) {
  return Expr<PolyField<X>, Bit>(expr_node(x));
}

// An explicit layer boundary: each coordinate of X passes through one
// linear node (ntt_gadget::share), so the circuit compiler does not fold X
// into the layer that reads it. The compiler adds no boundary of its own.
// A materialized expression is placed in the circuit.
template <class X, class = std::enable_if_t<kIsPoly<X>>>
Expr<PolyField<X>, PolyType<X>> materialize(const X &x) {
  auto a = expr_node(x);
  auto e = expr_internal::node(ExprOp::kMaterialize, a->f, a->n, a->shape);
  e->bit = a->bit;
  e->kids = {a};
  expr_internal::inherit(*e);
  e->logic = true;
  return Expr<PolyField<X>, PolyType<X>>(e);
}

// --------------------------------------------------------------- logic --
// Bit expressions keep Logic's c0 + c1 x representation; each gate is
// Logic's own.

template <class X, class = void>
struct IsBitPoly : std::false_type {};
template <class X>
struct IsBitPoly<X, std::enable_if_t<kIsPoly<X>>>
    : std::bool_constant<is_bit_v<PolyType<X>>> {};
template <class X>
constexpr bool kIsBitPoly = IsBitPoly<X>::value;

template <class X, class = std::enable_if_t<kIsBitPoly<X>>>
Expr<PolyField<X>, Bit> operator!(const X &x) {
  auto a = expr_node(x);
  return Expr<PolyField<X>, Bit>(
      expr_internal::logic<PolyField<X>>(ExprOp::kNot, {a}, a->n, a->shape));
}
// ~b is !b, 1 - b.
template <class X, class = std::enable_if_t<kIsBitPoly<X>>>
Expr<PolyField<X>, Bit> operator~(const X &x) {
  return !x;
}
namespace expr_internal {
// A plain C++ bit constant: an integer or an array of them, each 0 or 1.
template <class K>
constexpr bool kBitConst = std::is_integral_v<K> || kIsConstArray<K>;
// A gate's operand of field F: a Bit expression or handle, or a bit
// constant.
template <class F, class Y>
ExprPtr<F> bit_operand(const F &f, const Y &y, const char *what) {
  if constexpr (kIsPoly<Y>) {
    static_assert(std::is_same_v<PolyField<Y>, F>,
                  "a gate reads values of one field");
    return expr_node(y);
  } else {
    return lift_bits(f, y, {}, what);
  }
}
template <class X, class Y>
Expr<PolyField<X>, Bit> gate(ExprOp op, const X &x, const Y &y,
                             const char *what) {
  ExprPtr<PolyField<X>> a = expr_node(x);
  ExprPtr<PolyField<X>> b = bit_operand(*a->f, y, what);
  conform(a, b, what);
  const auto shape = a->shape.empty() ? b->shape : a->shape;
  const size_t n = a->n;
  return Expr<PolyField<X>, Bit>(logic<PolyField<X>>(op, {a, b}, n, shape));
}
template <class X, class Y>
constexpr bool kGatePair =
    kIsBitPoly<X> && (kIsBitPoly<Y> || kBitConst<std::remove_cvref_t<Y>>);
template <class X, class Y>
constexpr bool kConstGatePair =
    kBitConst<std::remove_cvref_t<X>> && kIsBitPoly<Y>;
}  // namespace expr_internal
// a & b, a | b and a ^ b on Bit values; either side may be a bit constant
// (an integer or an array of them).
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kGatePair<X, Y>>>
Expr<PolyField<X>, Bit> operator&(const X &x, const Y &y) {
  return expr_internal::gate(ExprOp::kAnd, x, y, "&");
}
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kGatePair<X, Y>>>
Expr<PolyField<X>, Bit> operator|(const X &x, const Y &y) {
  return expr_internal::gate(ExprOp::kOr, x, y, "|");
}
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kGatePair<X, Y>>>
Expr<PolyField<X>, Bit> operator^(const X &x, const Y &y) {
  return expr_internal::gate(ExprOp::kXor, x, y, "^");
}
template <class K, class X,
          class = std::enable_if_t<expr_internal::kConstGatePair<K, X>>,
          class = void>
Expr<PolyField<X>, Bit> operator&(const K &k, const X &x) {
  return x & k;
}
template <class K, class X,
          class = std::enable_if_t<expr_internal::kConstGatePair<K, X>>,
          class = void>
Expr<PolyField<X>, Bit> operator|(const K &k, const X &x) {
  return x | k;
}
template <class K, class X,
          class = std::enable_if_t<expr_internal::kConstGatePair<K, X>>,
          class = void>
Expr<PolyField<X>, Bit> operator^(const K &k, const X &x) {
  return x ^ k;
}

namespace expr_internal {
// A comparison of the words on the last axis of A ([..., w], least
// significant bit first) with B (the same shape) or a constant.
template <class F>
ExprPtr<F> compare(ExprOp op, ExprPtr<F> a, ExprPtr<F> b, bool imm,
                   uint64_t value, const char *what) {
  const auto d = a->dims();
  const size_t w = d.back();
  if (w == 0) fail(std::string(what) + ": words of no bits");
  if (imm && w < 64 && (value >> w) != 0)
    fail(std::string(what) + ": the constant " + std::to_string(value) +
         " has more than " + std::to_string(w) + " bits");
  if (!imm && b->dims() != d)
    fail(std::string(what) + ": the operands' shapes differ");
  std::vector<size_t> out(d.begin(), d.end() - 1);
  if (out.empty()) out = {1};
  size_t n = 1;
  for (size_t x : out) n *= x;
  std::vector<ExprPtr<F>> kids = {std::move(a)};
  if (!imm) kids.push_back(std::move(b));
  auto e = logic<F>(op, std::move(kids), n, out);
  auto m = std::make_shared<ExprNode<F>>(*e);
  m->w = w;
  m->imm = imm;
  m->value = value;
  return m;
}
}  // namespace expr_internal

namespace expr_internal {
// X compared with Y: a Word, an integer constant, or an array of integers
// (one per integer of X).
template <class X, class Y>
constexpr bool kWordPair =
    kIsWord<X> &&
    (kIsWord<Y> || std::is_integral_v<Y> || kIsConstArray<Y>);
// OP on the bits of A and Y, a Word of A's width and shape or an integer
// constant below 2^width.
template <class F, class Y>
ExprPtr<F> compare_words(ExprOp op, const Word<F> &a, const Y &y,
                         const char *what) {
  if constexpr (std::is_integral_v<Y>) {
    return compare<F>(op, a.bits, nullptr, true, uint64_t(y), what);
  } else if constexpr (kIsConstArray<Y>) {
    // The integers' bits, least significant first, in A's bits' shape.
    std::vector<ConstLeafType<Y>> ints;
    std::vector<size_t> own;
    const_flatten(y, 0, own, ints);
    std::vector<uint64_t> bits;
    for (const auto &v : ints) {
      const uint64_t u = uint64_t(v);
      if (a.width < 64 && (u >> a.width) != 0)
        fail(std::string(what) + ": the constant " + std::to_string(u) +
             " has more than " + std::to_string(a.width) + " bits");
      for (size_t l = 0; l < a.width; ++l)
        bits.push_back(l < 64 ? (u >> l) & 1 : 0);
    }
    return compare<F>(op, a.bits,
                      lift_bits(*a.bits->f, bits, a.bits->dims(), what), false,
                      0, what);
  } else {
    static_assert(std::is_same_v<typename Y::field_type, F>,
                  "a comparison reads values of one field");
    if (y.width != a.width)
      fail(std::string(what) + ": integers of " + std::to_string(a.width) +
           " and " + std::to_string(y.width) + " bits");
    return compare<F>(op, a.bits, y.bits, false, 0, what);
  }
}
}  // namespace expr_internal

// x < y, x <= y, x == y and x != y, element-wise on integers of a known
// width (Word, from x.from_bits()): Bit expressions of the integers' shape.
// Y is a Word of X's width and shape or an integer constant. Each is
// Longfellow's comparator on the bits: < is Logic::lt (lt_reduce, a
// balanced reduction of depth log w), <= is Logic::leq (not y < x), == is
// Logic::eq (eq_reduce, a balanced AND), and != is the negation of ==.
// Values of no known width have no comparison (a C++ compile error).
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kWordPair<X, Y>>>
Expr<typename X::field_type, Bit> operator<(const X &x, const Y &y) {
  using F = typename X::field_type;
  return Expr<F, Bit>(
      expr_internal::compare_words<F>(ExprOp::kLt, x, y, "<"));
}
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kWordPair<X, Y>>>
Expr<typename X::field_type, Bit> operator<=(const X &x, const Y &y) {
  using F = typename X::field_type;
  return Expr<F, Bit>(
      expr_internal::compare_words<F>(ExprOp::kLeq, x, y, "<="));
}
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kWordPair<X, Y>>>
Expr<typename X::field_type, Bit> operator==(const X &x, const Y &y) {
  using F = typename X::field_type;
  return Expr<F, Bit>(
      expr_internal::compare_words<F>(ExprOp::kEq, x, y, "=="));
}
template <class X, class Y,
          class = std::enable_if_t<expr_internal::kWordPair<X, Y>>>
Expr<typename X::field_type, Bit> operator!=(const X &x, const Y &y) {
  return !(x == y);
}

namespace expr_internal {
// OP over the last axis of X: [..., w] -> [...].
template <class F>
ExprPtr<F> reduce(ExprOp op, ExprPtr<F> x) {
  const auto d = x->dims();
  std::vector<size_t> out(d.begin(), d.end() - 1);
  if (out.empty()) out = {1};
  size_t n = 1;
  for (size_t k : out) n *= k;
  auto e = logic<F>(op, {x}, n, out);
  auto m = std::make_shared<ExprNode<F>>(*e);
  m->w = d.back();
  return m;
}
// OP coordinatewise over KIDS, broadcast to one shape: the last kid's when
// the kids that are not scalars have one length, NumPy's broadcast of
// their shapes otherwise.
template <class F>
ExprPtr<F> across(ExprOp op, const char *what, std::vector<ExprPtr<F>> kids) {
  size_t n = 1;
  bool one_length = true;
  std::vector<size_t> shape;
  for (const auto &k : kids) {
    if (k->n == 1) continue;
    if (n != 1 && k->n != n) one_length = false;
    n = k->n;
    shape = k->dims();
  }
  if (!one_length) {
    shape = {};
    for (const auto &k : kids)
      if (k->n != 1) shape = broadcast_shape(shape, k->dims(), what);
    n = 1;
    for (size_t d : shape) n *= d;
  }
  for (auto &k : kids)
    if (k->n != n) k = broadcast(k, shape, what);
  return logic<F>(op, std::move(kids), n, shape);
}

inline size_t count_of(const std::vector<size_t> &d) {
  size_t n = 1;
  for (size_t x : d) n *= x;
  return n;
}
// A view of KIDS with dims DIMS: coordinate i is coordinate IDX[i] of the
// kids' coordinates, concatenated in order.
template <class F>
ExprPtr<F> gather_node(std::vector<ExprPtr<F>> kids, std::vector<size_t> idx,
                       std::vector<size_t> dims) {
  size_t total = 0;
  bool bit = true;
  for (const auto &k : kids) {
    total += k->n;
    bit = bit && k->bit;
  }
  for (size_t j : idx)
    if (j >= total)
      fail("gather: index " + std::to_string(j) + " past the " +
           std::to_string(total) + " coordinates");
  if (count_of(dims) != idx.size())
    fail("a view of " + std::to_string(idx.size()) +
         " coordinates has a shape of another size");
  auto e = node<F>(ExprOp::kGather, kids.at(0)->f, idx.size(), std::move(dims));
  e->bit = bit;
  e->kids = std::move(kids);
  e->idx = std::move(idx);
  inherit(*e);
  return e;
}
template <class F>
ExprPtr<F> view(ExprPtr<F> a, ViewMap v) {
  return gather_node<F>({std::move(a)}, std::move(v.idx), std::move(v.dims));
}
// A with AXIS moved last (a view), or A when AXIS is last.
template <class F>
ExprPtr<F> axis_last(ExprPtr<F> a, size_t axis, const char *what) {
  const auto d = a->dims();
  view_maps::check_axis(d, axis, what);
  if (axis + 1 == d.size()) return a;
  return view(std::move(a), view_maps::axis_last(d, axis));
}
// OP (kSum or kProd) of each group of W coordinates along the last axis of
// A, with dims OUT.
template <class F>
ExprPtr<F> grouped(ExprOp op, ExprPtr<F> a, size_t w,
                   std::vector<size_t> out) {
  if (w == 0) fail("a sum or product over an empty axis");
  auto e = node<F>(op, a->f, a->n / w, std::move(out));
  e->w = w;
  e->bit = op == ExprOp::kProd && a->bit;
  e->kids = {std::move(a)};
  inherit(*e);
  return e;
}
// An operand of mux: a handle or expression, or a constant (a scalar).
template <class F, class X>
ExprPtr<F> operand(const F &f, const X &x) {
  if constexpr (kIsPoly<X>) {
    static_assert(std::is_same_v<PolyField<X>, F>,
                  "mux reads values of one field");
    return expr_node(x);
  } else if constexpr (kIsConstArray<X>) {
    return lift_array(f, x);
  } else {
    static_assert(std::is_integral_v<X> ||
                      std::is_same_v<std::decay_t<X>, typename F::Elt>,
                  "mux: an operand is a handle, an expression or a "
                  "constant");
    return constant<F>(&f, {constant_of(f, x)}, {});
  }
}
template <class X, class = void>
struct OperandTypeOf {
  using type = Field;
};
template <class X>
struct OperandTypeOf<X, std::enable_if_t<kIsPoly<X>>> {
  using type = PolyType<X>;
};
template <class X>
using OperandType = typename OperandTypeOf<X>::type;
}  // namespace expr_internal

// ------------------------------------------------------------ methods --

template <class F, class T>
auto Expr<F, T>::sum() const {
  auto e = expr_internal::node(ExprOp::kSum, node->f, 1, {});
  e->kids = {node};
  expr_internal::inherit(*e);
  using R = std::conditional_t<F::kCharacteristicTwo && is_bit_v<T>, Bit, Field>;
  return Expr<F, R>(expr_internal::typed<R>(ExprPtr<F>(e)));
}
template <class F, class T>
auto Expr<F, T>::sum(size_t axis) const {
  const auto d = dims();
  view_maps::check_axis(d, axis, "sum");
  if (d.size() == 1) return sum();
  std::vector<size_t> out = d;
  out.erase(out.begin() + long(axis));
  using R = std::conditional_t<F::kCharacteristicTwo && is_bit_v<T>, Bit, Field>;
  return Expr<F, R>(expr_internal::typed<R>(expr_internal::grouped(
      ExprOp::kSum, expr_internal::axis_last(node, axis, "sum"), d[axis],
      out)));
}
template <class F, class T>
auto Expr<F, T>::prod() const {
  if (node->n == 0) fail("prod: no coordinates");
  return Expr<F, ProductType<T, T>>(
      expr_internal::grouped<F>(ExprOp::kProd, node, node->n, {}));
}
template <class F, class T>
auto Expr<F, T>::prod(size_t axis) const {
  const auto d = dims();
  view_maps::check_axis(d, axis, "prod");
  if (d.size() == 1) return prod();
  std::vector<size_t> out = d;
  out.erase(out.begin() + long(axis));
  return Expr<F, ProductType<T, T>>(expr_internal::grouped(
      ExprOp::kProd, expr_internal::axis_last(node, axis, "prod"), d[axis],
      out));
}
template <class F, class T>
template <class X, class Y>
auto Expr<F, T>::mux(const X &t, const Y &e) const {
  static_assert(is_bit_v<T>, "mux: the condition is a Bit");
  using TT = expr_internal::OperandType<X>;
  using TE = expr_internal::OperandType<Y>;
  using R = std::conditional_t<std::is_same_v<TT, TE>, TT, Field>;
  const F &f = *node->f;
  auto m = expr_internal::across<F>(
      ExprOp::kMux, "mux",
      {node, expr_internal::operand(f, t), expr_internal::operand(f, e)});
  auto r = std::make_shared<ExprNode<F>>(*m);
  r->bit = is_bit_v<TT> && is_bit_v<TE>;
  r->logic = true;
  return Expr<F, R>(r);
}
template <class F, class T>
auto Expr<F, T>::any(size_t axis) const {
  static_assert(is_bit_v<T>, "any: reads Bit values");
  return Expr<F, Bit>(expr_internal::reduce(
      ExprOp::kAny, expr_internal::axis_last(node, axis, "any")));
}
template <class F, class T>
auto Expr<F, T>::all(size_t axis) const {
  static_assert(is_bit_v<T>, "all: reads Bit values");
  return Expr<F, Bit>(expr_internal::reduce(
      ExprOp::kAll, expr_internal::axis_last(node, axis, "all")));
}
template <class F, class T>
auto Expr<F, T>::rotate(long k, size_t axis) const {
  return Expr<F, T>(
      expr_internal::view(node, view_maps::rotate(dims(), k, axis)));
}
template <class F, class T>
auto Expr<F, T>::reindex(const std::vector<size_t> &idx) const {
  return Expr<F, T>(expr_internal::view(
      node, view_maps::reindex({node->n}, idx, 0)));
}
template <class F, class T>
auto Expr<F, T>::reindex(const std::vector<size_t> &idx, size_t axis) const {
  return Expr<F, T>(
      expr_internal::view(node, view_maps::reindex(dims(), idx, axis)));
}
template <class F, class T>
template <class K, class>
auto Expr<F, T>::reindex(const K &idx) const {
  auto [flat, shape] = expr_internal::index_array(idx);
  ViewMap v = view_maps::reindex({node->n}, flat, 0);
  v.dims = std::move(shape);
  return Expr<F, T>(expr_internal::view(node, std::move(v)));
}
template <class F, class T>
template <class K, class>
auto Expr<F, T>::reindex(const K &idx, size_t axis) const {
  const auto [flat, shape] = expr_internal::index_array(idx);
  if (shape.size() != 1)
    fail("reindex along an axis: the index array has rank " +
         std::to_string(shape.size()) + ", not 1");
  return reindex(flat, axis);
}
template <class F, class T>
auto Expr<F, T>::at(size_t i) const {
  return at(0, i);
}
template <class F, class T>
auto Expr<F, T>::slice(size_t b, size_t e, size_t axis) const {
  return Expr<F, T>(
      expr_internal::view(node, view_maps::slice(dims(), axis, b, e)));
}
template <class F, class T>
auto Expr<F, T>::at(size_t axis, size_t i) const {
  return Expr<F, T>(expr_internal::view(node, view_maps::at(dims(), axis, i)));
}
template <class F, class T>
auto Expr<F, T>::operator[](size_t i) const {
  return at(0, i);
}
template <class F, class T>
auto Expr<F, T>::reshape(const Shape &s) const {
  if (s.size() != node->n)
    throw CompileError("reshape: " + std::to_string(s.size()) +
                       " coordinates, the expression has " +
                       std::to_string(node->n));
  ViewMap v{s.dims, std::vector<size_t>(node->n)};
  for (size_t i = 0; i < node->n; ++i) v.idx[i] = i;
  return Expr<F, T>(expr_internal::view(node, std::move(v)));
}
template <class F, class T>
auto Expr<F, T>::flat() const {
  return reshape(Shape(node->n));
}
template <class F, class T>
template <class Y>
auto Expr<F, T>::concat(const Y &y, size_t axis) const {
  static_assert(kIsPoly<Y> && std::is_same_v<PolyField<Y>, F>,
                "concat: the parts are values of one field");
  using R = std::conditional_t<std::is_same_v<T, PolyType<Y>>, T, Field>;
  auto b = expr_node(y);
  ViewMap v = view_maps::concat(dims(), b->dims(), axis);
  return Expr<F, R>(expr_internal::gather_node<F>(
      {node, std::move(b)}, std::move(v.idx), std::move(v.dims)));
}
template <class F, class T>
template <class B>
auto Expr<F, T>::from_digits(const B &base) const {
  static_assert(std::is_integral_v<B> || std::is_same_v<B, typename F::Elt>,
                "from_digits: the base is an integer or an element of the "
                "field");
  const auto d = dims();
  const size_t k = d.back();
  const F &f = *node->f;
  typename F::Elt b;
  if constexpr (std::is_integral_v<B>) {
    b = f.of_scalar(uint64_t(base));
  } else {
    b = base;
  }
  std::vector<typename F::Elt> w(k);
  if (k) w[0] = f.one();
  for (size_t l = 1; l < k; ++l) w[l] = f.mulf(w[l - 1], b);
  const Expr<F, Field> powers(expr_internal::constant<F>(&f, std::move(w), {k}));
  return (Expr<F, Field>(node) * powers).sum(d.size() - 1);
}
template <class F, class T>
auto Expr<F, T>::from_bits() const {
  static_assert(is_bit_v<T>, "from_bits: reads Bit words");
  Word<F> w;
  w.bits = node;
  w.width = dims().back();
  w.value = from_digits(2).node;
  return w;
}
// A linear operator on an expression: a kApply node. Affine when X is
// (affine_form carries X's constant term through the operator), and read
// by a circuit through the operator's expansion only (structured
// otherwise).
template <class F>
template <class T>
auto Op<F>::operator()(const Expr<F, T> &x) const {
  auto [s, out] = fit(x.dims(), x.size());
  auto e = expr_internal::node(ExprOp::kApply, x.f(), s->rows, out);
  e->apply = s;
  e->kids = {x.node};
  expr_internal::inherit(*e);
  if (!circuit_expandable(*s) && !e->structured) {
    e->structured = true;
    e->structured_op = s->name;
  }
  return Expr<F, Field>(e);
}
// x.from_bits() of a handle or an affine expression: the value is the
// affine from_digits(2), the bits the operand.
template <class F, class T, class P>
Word<F> word_of(const Ref<F, T, P> &r) {
  static_assert(is_bit_v<T>, "from_bits: reads Bit words");
  Word<F> w;
  w.bits = Expr<F, Bit>(r).node;
  w.width = r.dims().back();
  w.value = Expr<F, Field>(r.from_digits(2)).node;
  return w;
}
template <class F>
Word<F> word_of(const Lin<F> &l) {
  Word<F> w;
  w.bits = Expr<F, Field>(l).node;
  w.width = l.dims().back();
  w.value = Expr<F, Field>(l.from_digits(2)).node;
  return w;
}

// --------------------------------------------------------------- emit --

// Emits expressions with the Logic object LC: over a compiler backend it
// builds gates, over the evaluation backend it computes values. TERM gives
// the values of one affine term (its node through its operators, before
// its scale). Each node is emitted once per emitter.
template <class F, class LC>
class ExprEmitter {
 public:
  using Elt = typename F::Elt;
  using EltW = typename LC::EltW;
  using BitW = typename LC::BitW;
  using TermFn = std::function<std::vector<EltW>(const Term<F> &)>;

  // APPLY gives a linear operator's outputs on its inputs' wires; by default
  // its circuit expansion (expand_operator).
  using ApplyFn = std::function<std::vector<EltW>(const OpSpec<F> &,
                                                  const std::vector<EltW> &)>;
  ExprEmitter(const LC &lc, TermFn term, ApplyFn apply = nullptr)
      : lc_(lc), term_(std::move(term)), apply_(std::move(apply)) {
    if (!apply_)
      apply_ = [pl = &lc](const OpSpec<F> &op, const std::vector<EltW> &w) {
        return expand_operator<F>(*pl, op, w);
      };
  }

  // Lean views: a gather reads through the gathers below it to their
  // first other node, and reads a plain leaf (one term, no operator) there
  // without emitting it whole, so a view of a few coordinates of a large
  // node holds only those. Gathers build no gates, so the gates are the
  // same; only the order in which TERM is called may differ.
  void lean_views(bool on) { lean_ = on; }

  const std::vector<BitW> &operator()(const ExprPtr<F> &e) {
    auto it = memo_.find(e.get());
    if (it != memo_.end()) return it->second;
    std::vector<BitW> v = emit(*e);
    // A lean-view emitter (predicate_terms) is short-lived and keeps its
    // memo whole.
    if (!lean_) forget_kids(*e);
    return memo_.emplace(e.get(), std::move(v)).first->second;
  }

  // One wire per coordinate (c0 + c1 x evaluated; x itself when c0 = 0 and
  // c1 = 1).
  EltW wire(const BitW &b) const {
    if (b.c0 == lc_.zero() && b.c1 == lc_.one()) return b.x;
    return lc_.eval(b);
  }
  // E = 0 at every coordinate.
  void assert_zero(const ExprPtr<F> &e) {
    for (const auto &b : (*this)(e)) lc_.assert0(wire(b));
  }
  // E = 1 at every coordinate (Logic::assert1).
  void assert_true(const ExprPtr<F> &e) {
    for (const auto &b : (*this)(e)) lc_.assert1(b);
  }

  // a + b and a b in the c0 + c1 x representation, without a gate for a
  // zero coefficient: Logic's addv and mulv, which build every term.
  BitW add(const BitW &a, const BitW &b) const {
    const Elt c0 = lc_.addf(a.c0, b.c0);
    if (a.c1 == lc_.zero()) return BitW(c0, b.c1, b.x);
    if (b.c1 == lc_.zero()) return BitW(c0, a.c1, a.x);
    EltW x;
    if (a.c1 == lc_.one() && b.c1 == lc_.one()) {
      x = lc_.add(a.x, b.x);
    } else if (a.c1 == lc_.one() && b.c1 == lc_.mone()) {
      x = lc_.sub(a.x, b.x);
    } else if (a.c1 == lc_.one()) {
      x = lc_.axpy(a.x, b.c1, b.x);
    } else if (b.c1 == lc_.one()) {
      x = lc_.axpy(b.x, a.c1, a.x);
    } else {
      x = lc_.add(lc_.ax(a.c1, a.x), lc_.ax(b.c1, b.x));
    }
    return BitW(c0, lc_.one(), x);
  }
  BitW mul(const BitW &a, const BitW &b) const {
    if (a.c1 == lc_.zero())
      return BitW(lc_.mulf(a.c0, b.c0), lc_.mulf(a.c0, b.c1), b.x);
    if (b.c1 == lc_.zero()) return mul(b, a);
    const Elt k = lc_.mulf(a.c1, b.c1);
    EltW x = k == lc_.one() ? lc_.mul(a.x, b.x) : lc_.mul(k, a.x, b.x);
    if (a.c0 != lc_.zero()) x = lc_.axpy(x, lc_.mulf(a.c0, b.c1), b.x);
    if (b.c0 != lc_.zero()) x = lc_.axpy(x, lc_.mulf(a.c1, b.c0), a.x);
    return BitW(lc_.mulf(a.c0, b.c0), lc_.one(), x);
  }

 private:
  BitW konst(const Elt &c) const {
    return BitW(c, lc_.zero(), lc_.konst(lc_.one()));
  }
  // Coordinate I of gather X (lean views).
  BitW view_at(const ExprNode<F> &x, size_t i) {
    const ExprNode<F> *y = &x;
    const ExprPtr<F> *yp = nullptr;
    size_t j = i;
    while (y->op == ExprOp::kGather && !memo_.count(y)) {
      size_t q = y->idx[j], k = 0;
      while (q >= y->kids[k]->n) q -= y->kids[k++]->n;
      yp = &y->kids[k];
      y = yp->get();
      j = q;
    }
    const bool plain = y->op == ExprOp::kLin && y->lin.terms.size() == 1 &&
                       y->lin.terms[0].chain.empty() && !memo_.count(y);
    if (!plain) return (*this)(*yp)[j];
    const Term<F> &t = y->lin.terms[0];
    auto it = leaf_wires_.find(y);
    if (it == leaf_wires_.end()) {
      std::vector<EltW> w = term_(t);
      if (w.size() != y->n) fail("an expression term has the wrong length");
      it = leaf_wires_.emplace(y, std::move(w)).first;
    }
    return BitW(lc_.zero(), t.scale, it->second[j]);
  }
  // -a in the c0 + c1 x representation: no gate.
  BitW negate(const BitW &a) const {
    return BitW(lc_.mulf(lc_.mone(), a.c0), lc_.mulf(lc_.mone(), a.c1), a.x);
  }
  // A balanced sum of V[i0, i1).
  BitW total(const std::vector<BitW> &v, size_t i0, size_t i1) const {
    if (i1 <= i0) return konst(lc_.zero());
    if (i1 == i0 + 1) return v[i0];
    const size_t im = i0 + (i1 - i0) / 2;
    return add(total(v, i0, im), total(v, im, i1));
  }
  // A balanced product of V[i0, i1): ceil(log2 (i1 - i0)) layers of
  // multiplications, pairing neighbours level by level and carrying an odd
  // last factor up (the grand product of the library's earlier circuit
  // closures), so the last factors, a filtered product's later and deeper
  // ones, take the shorter paths.
  BitW product(const std::vector<BitW> &v, size_t i0, size_t i1) const {
    if (i1 <= i0) return konst(lc_.one());
    std::vector<BitW> w(v.begin() + long(i0), v.begin() + long(i1));
    while (w.size() > 1) {
      std::vector<BitW> nx;
      nx.reserve((w.size() + 1) / 2);
      for (size_t i = 0; i + 1 < w.size(); i += 2)
        nx.push_back(mul(w[i], w[i + 1]));
      if (w.size() % 2 != 0) nx.push_back(w.back());
      w = std::move(nx);
    }
    return w[0];
  }

  // Chains of an associative, commutative operation (+, *, and on Bits &,
  // | and ^): E's operands, with each operand of E's operation that has no
  // other use flattened into the chain, emitted as one balanced tree per
  // coordinate, so a * b * c * d has depth 2. A node with another use (a
  // second parent, or a C++ variable that holds it: shared_ptr's use count)
  // or one already emitted stays a leaf, emitted once.
  void chain_leaves(const ExprNode<F> &e, ExprOp op,
                    std::vector<const ExprPtr<F> *> &leaves) const {
    for (const auto &k : e.kids) {
      if (k->op == op && k.use_count() == 1 && !memo_.count(k.get()))
        chain_leaves(*k, op, leaves);
      else
        leaves.push_back(&k);
    }
  }
  BitW combine(ExprOp op, const BitW &a, const BitW &b) const {
    switch (op) {
      case ExprOp::kAdd:
        return add(a, b);
      case ExprOp::kMul:
        return mul(a, b);
      case ExprOp::kAnd:
        return lc_.land(a, b);
      case ExprOp::kOr:
        return lc_.lor(a, b);
      default:
        return lc_.lxor(a, b);
    }
  }
  BitW tree(ExprOp op, const std::vector<const std::vector<BitW> *> &v,
            size_t i, size_t j0, size_t j1) const {
    if (j1 == j0 + 1) return (*v[j0])[i];
    const size_t jm = j0 + (j1 - j0) / 2;
    return combine(op, tree(op, v, i, j0, jm), tree(op, v, i, jm, j1));
  }
  std::vector<BitW> chain(const ExprNode<F> &e) {
    std::vector<const ExprPtr<F> *> leaves;
    chain_leaves(e, e.op, leaves);
    std::vector<const std::vector<BitW> *> v;
    for (const ExprPtr<F> *k : leaves) v.push_back(&(*this)(*k));
    std::vector<BitW> out;
    out.reserve(e.n);
    for (size_t i = 0; i < e.n; ++i)
      out.push_back(tree(e.op, v, i, 0, v.size()));
    return out;
  }

  // Erases, once E is emitted, the memo entries of the kids only E holds
  // (use count 1): nothing reaches them but through E, whose wires are
  // memoized, so theirs are never read again. A kid that a chain flattened
  // into E was never memoized; its own kids are visited in its place.
  void forget_kids(const ExprNode<F> &e) {
    for (const auto &k : e.kids) {
      if (k.use_count() != 1) continue;
      auto it = memo_.find(k.get());
      if (it != memo_.end())
        memo_.erase(it);
      else
        forget_kids(*k);
    }
  }

  std::vector<BitW> emit(const ExprNode<F> &e) {
    std::vector<BitW> out;
    out.reserve(e.n);
    switch (e.op) {
      case ExprOp::kLin: {
        out.assign(e.n, konst(lc_.zero()));
        bool first = true;
        for (const auto &t : e.lin.terms) {
          const std::vector<EltW> w = term_(t);
          if (w.size() != e.n) fail("an expression term has the wrong length");
          for (size_t i = 0; i < e.n; ++i) {
            const BitW b(lc_.zero(), t.scale, w[i]);
            out[i] = first ? b : add(out[i], b);
          }
          first = false;
        }
        break;
      }
      case ExprOp::kConst:
        for (const Elt &c : e.c) out.push_back(konst(c));
        break;
      case ExprOp::kAdd:
        out = chain(e);
        break;
      case ExprOp::kScale: {
        const auto &a = (*this)(e.kids[0]);
        for (const auto &x : a) out.push_back(lc_.rebase(lc_.zero(), e.c[0], x));
        break;
      }
      case ExprOp::kMul:
        out = chain(e);
        break;
      case ExprOp::kSum: {
        const auto &a = (*this)(e.kids[0]);
        if (e.w == 0) {
          out.push_back(total(a, 0, a.size()));
        } else {
          for (size_t k = 0; k < e.n; ++k)
            out.push_back(total(a, k * e.w, (k + 1) * e.w));
        }
        break;
      }
      case ExprOp::kProd: {
        const auto &a = (*this)(e.kids[0]);
        for (size_t k = 0; k < e.n; ++k)
          out.push_back(product(a, k * e.w, (k + 1) * e.w));
        break;
      }
      case ExprOp::kBroadcast: {
        const auto &a = (*this)(e.kids[0]);
        out.assign(e.n, a.at(0));
        break;
      }
      case ExprOp::kApply: {
        std::vector<EltW> w;
        for (const auto &b : (*this)(e.kids[0])) w.push_back(wire(b));
        for (const auto &x : apply_(*e.apply, w))
          out.push_back(BitW(lc_.zero(), lc_.one(), x));
        break;
      }
      case ExprOp::kGather: {
        if (lean_) {
          for (size_t i = 0; i < e.n; ++i) out.push_back(view_at(e, i));
          break;
        }
        std::vector<const BitW *> at;
        for (const auto &k : e.kids)
          for (const auto &x : (*this)(k)) at.push_back(&x);
        for (size_t j : e.idx) out.push_back(*at.at(j));
        break;
      }
      case ExprOp::kNot: {
        for (const auto &x : (*this)(e.kids[0])) out.push_back(lc_.lnot(x));
        break;
      }
      case ExprOp::kAnd:
      case ExprOp::kOr:
      case ExprOp::kXor:
        out = chain(e);
        break;
      case ExprOp::kMux: {
        // Bits: Logic::mux, c t + (1 - c) e, whose two products share a
        // layer. Field values: e + c (t - e), one product (one step of a
        // multiplexer tree), a constant side folded into the coefficients.
        const auto &c = (*this)(e.kids[0]);
        const auto &t = (*this)(e.kids[1]);
        const auto &f = (*this)(e.kids[2]);
        for (size_t i = 0; i < e.n; ++i) {
          if (e.bit) {
            out.push_back(lc_.mux(c[i], t[i], f[i]));
            continue;
          }
          const BitW d = add(t[i], negate(f[i]));
          out.push_back(add(f[i], mul(c[i], d)));
        }
        break;
      }
      case ExprOp::kLt:
      case ExprOp::kLeq:
      case ExprOp::kEq: {
        const size_t w = e.w;
        const auto &a = (*this)(e.kids[0]);
        std::vector<BitW> bc(w);
        if (e.imm) lc_.bits(w, bc.data(), e.value);
        for (size_t k = 0; k < e.n; ++k) {
          const BitW *pa = &a[k * w];
          const BitW *pb = bc.data();
          if (!e.imm) pb = &(*this)(e.kids[1])[k * w];
          out.push_back(e.op == ExprOp::kLt    ? lc_.lt(w, pa, pb)
                        : e.op == ExprOp::kLeq ? lc_.leq(w, pa, pb)
                                               : lc_.eq(w, pa, pb));
        }
        break;
      }
      case ExprOp::kAny:
      case ExprOp::kAll: {
        const bool any = e.op == ExprOp::kAny;
        const size_t w = e.w;
        const auto &a = (*this)(e.kids[0]);
        for (size_t k = 0; k < e.n; ++k) {
          auto at = [&](size_t j) { return a[k * w + j]; };
          out.push_back(any ? lc_.lor(0, w, at) : lc_.land(0, w, at));
        }
        break;
      }
      case ExprOp::kConv: {
        // Coefficient i of row r: the balanced sum of x_a y_{i-a}.
        const auto &a = (*this)(e.kids[0]);
        const auto &b = (*this)(e.kids[1]);
        const size_t la = e.kids[0]->dims().back();
        const size_t lb = e.kids[1]->dims().back();
        const size_t lo = la + lb - 1;
        for (size_t k = 0; k < e.n; ++k) {
          const size_t r = k / lo, i = k % lo;
          std::vector<BitW> terms;
          for (size_t u = i + 1 > lb ? i + 1 - lb : 0; u < la && u <= i; ++u)
            terms.push_back(mul(a[r * la + u], b[r * lb + i - u]));
          out.push_back(total(terms, 0, terms.size()));
        }
        break;
      }
      case ExprOp::kMaterialize: {
        for (const auto &x : (*this)(e.kids[0])) {
          // ntt_gadget::share: one linear node that keeps the operand.
          const EltW s = lc_.axpy(lc_.konst(lc_.zero()), lc_.one(), wire(x));
          out.push_back(BitW(lc_.zero(), lc_.one(), s));
        }
        break;
      }
    }
    if (out.size() != e.n) fail("an expression node has the wrong length");
    return out;
  }

  const LC &lc_;
  TermFn term_;
  ApplyFn apply_;
  std::map<const ExprNode<F> *, std::vector<BitW>> memo_;
  // Lean views (lean_views): the wires of the plain leaves gathers read.
  bool lean_ = false;
  std::map<const ExprNode<F> *, std::vector<EltW>> leaf_wires_;
};

// The values of E on host values V by direct field arithmetic, node by
// node, for expressions of affine leaves without operators, constants, +,
// scaling, *, sums, products, broadcasts, views and the gates: each node's
// values are the polynomial the emitter's Logic forms compute (~a = 1 - a,
// a & b = a b, a | b = a + b - a b, a ^ b = a + b - 2 a b, c.mux(t, e) =
// e + c (t - e)), so the values are the same. A view's coordinate is
// resolved through the views below it to the node that computes it, and a
// plain leaf (one term of scale 1) is read in place: a view of a large
// value, or a view of a view of it, costs its own size. admits() says
// whether DirectEval takes E (memoized on the nodes); eval_expr runs the
// emitter otherwise. No branch reads a value.
template <class F>
class DirectEval {
 public:
  using Elt = typename F::Elt;
  DirectEval(const F &f, const ValueReader &v) : f_(f), v_(v) {}

  static bool admits(const ExprNode<F> &e) {
    if (e.direct >= 0) return e.direct != 0;
    bool ok = true;
    switch (e.op) {
      case ExprOp::kLin:
        for (const auto &t : e.lin.terms) ok = ok && t.chain.empty();
        break;
      case ExprOp::kConst:
      case ExprOp::kAdd:
      case ExprOp::kScale:
      case ExprOp::kMul:
      case ExprOp::kSum:
      case ExprOp::kProd:
      case ExprOp::kBroadcast:
      case ExprOp::kGather:
      case ExprOp::kNot:
      case ExprOp::kAnd:
      case ExprOp::kOr:
      case ExprOp::kXor:
      case ExprOp::kMux:
      case ExprOp::kMaterialize:
        break;
      default:
        ok = false;
    }
    for (const auto &k : e.kids) ok = ok && admits(*k);
    e.direct = ok ? 1 : 0;
    return ok;
  }

  // The values of node E.
  const std::vector<Elt> &operator()(const ExprNode<F> *e) {
    auto it = memo_.find(e);
    if (it != memo_.end()) return it->second;
    std::vector<Elt> out = eval(*e);
    if (out.size() != e->n) fail("an expression node has the wrong length");
    return memo_.emplace(e, std::move(out)).first->second;
  }

 private:
  // A plain leaf's stored values (one term of scale 1), read in place.
  const std::vector<Elt> *plain(const ExprNode<F> &e) const {
    if (e.op != ExprOp::kLin || e.lin.terms.size() != 1) return nullptr;
    const Term<F> &t = e.lin.terms[0];
    if (!t.chain.empty() || !(t.scale == f_.one())) return nullptr;
    const auto &x = v_.template get<F>(t.node);
    return x.size() == e.n ? &x : nullptr;
  }
  // Coordinate I of node E: through views and broadcasts to a plain leaf's
  // stored value or a computed node's.
  const Elt &at(const ExprNode<F> *e, size_t i) {
    for (;;) {
      if (e->op == ExprOp::kGather) {
        size_t j = e->idx[i];
        const ExprNode<F> *k = nullptr;
        for (const auto &c : e->kids) {
          if (j < c->n) {
            k = c.get();
            break;
          }
          j -= c->n;
        }
        if (k == nullptr) fail("a view reads past its operands");
        e = k;
        i = j;
        continue;
      }
      if (e->op == ExprOp::kBroadcast) {
        e = e->kids[0].get();
        i = 0;
        continue;
      }
      if (const std::vector<Elt> *x = plain(*e)) return (*x)[i];
      return (*this)(e)[i];
    }
  }
  std::vector<Elt> eval(const ExprNode<F> &e) {
    const F &f = f_;
    std::vector<Elt> out;
    switch (e.op) {
      case ExprOp::kLin: {
        out.assign(e.n, f.zero());
        for (const auto &t : e.lin.terms) {
          const auto &x = v_.template get<F>(t.node);
          if (x.size() != e.n) fail("an expression term has the wrong length");
          for (size_t i = 0; i < e.n; ++i) f.add(out[i], f.mulf(t.scale, x[i]));
        }
        break;
      }
      case ExprOp::kConst:
        out = e.c;
        break;
      case ExprOp::kAdd:
      case ExprOp::kMul:
      case ExprOp::kAnd:
      case ExprOp::kOr:
      case ExprOp::kXor: {
        out = (*this)(e.kids[0].get());
        for (size_t q = 1; q < e.kids.size(); ++q) {
          const auto &b = (*this)(e.kids[q].get());
          for (size_t i = 0; i < e.n; ++i) out[i] = gate(e.op, out[i], b[i]);
        }
        break;
      }
      case ExprOp::kScale: {
        out = (*this)(e.kids[0].get());
        for (auto &x : out) x = f.mulf(e.c[0], x);
        break;
      }
      case ExprOp::kSum:
      case ExprOp::kProd: {
        const auto &a = (*this)(e.kids[0].get());
        const size_t w = e.w == 0 ? a.size() : e.w;
        for (size_t k = 0; k < e.n; ++k) {
          Elt s = e.op == ExprOp::kSum ? f.zero() : f.one();
          for (size_t i = k * w; i < (k + 1) * w; ++i)
            s = e.op == ExprOp::kSum ? f.addf(s, a[i]) : f.mulf(s, a[i]);
          out.push_back(s);
        }
        break;
      }
      case ExprOp::kBroadcast:
        out.assign(e.n, at(&e, 0));
        break;
      case ExprOp::kGather: {
        // The coordinates through the gathers below this one, resolved
        // once per node (resolve_gather); each operand they reach once per
        // evaluation (a plain leaf's values in place, a computed node's
        // memoized), a broadcast through at(). A view of a large value, or
        // a view of a view of it, costs its own size. The memo's values
        // stay where they are while it grows.
        const GatherSources<F> &gs =
            e.gather_sources.get([&] { return resolve_gather(e); });
        std::vector<const std::vector<Elt> *> src(gs.base.size(), nullptr);
        for (size_t k = 0; k < gs.base.size(); ++k) {
          const ExprNode<F> *c = gs.base[k];
          if (c->op == ExprOp::kBroadcast) continue;
          src[k] = plain(*c);
          if (src[k] == nullptr) src[k] = &(*this)(c);
        }
        out.reserve(e.n);
        for (size_t i = 0; i < e.n; ++i) {
          const size_t k = gs.which[i];
          out.push_back(src[k] != nullptr ? (*src[k])[gs.at[i]]
                                          : at(gs.base[k], gs.at[i]));
        }
        break;
      }
      case ExprOp::kNot: {
        out = (*this)(e.kids[0].get());
        for (auto &x : out) x = f.subf(f.one(), x);
        break;
      }
      case ExprOp::kMux: {
        const auto &c = (*this)(e.kids[0].get());
        const auto &t = (*this)(e.kids[1].get());
        const auto &g = (*this)(e.kids[2].get());
        for (size_t i = 0; i < e.n; ++i)
          out.push_back(f.addf(g[i], f.mulf(c[i], f.subf(t[i], g[i]))));
        break;
      }
      case ExprOp::kMaterialize:
        out = (*this)(e.kids[0].get());
        break;
      default:
        fail("DirectEval: an operation it does not take");
    }
    return out;
  }
  // Gather E's coordinates resolved through the gathers below it.
  static GatherSources<F> resolve_gather(const ExprNode<F> &e) {
    GatherSources<F> gs;
    std::unordered_map<const ExprNode<F> *, uint32_t> index;
    gs.which.reserve(e.n);
    gs.at.reserve(e.n);
    for (size_t i0 = 0; i0 < e.n; ++i0) {
      const ExprNode<F> *x = &e;
      size_t i = i0;
      while (x->op == ExprOp::kGather) {
        size_t j = x->idx[i];
        const ExprNode<F> *k = nullptr;
        for (const auto &c : x->kids) {
          if (j < c->n) {
            k = c.get();
            break;
          }
          j -= c->n;
        }
        if (k == nullptr) fail("a view reads past its operands");
        x = k;
        i = j;
      }
      const auto [it, fresh] = index.emplace(x, uint32_t(gs.base.size()));
      if (fresh) gs.base.push_back(x);
      gs.which.push_back(it->second);
      gs.at.push_back(i);
    }
    return gs;
  }
  Elt gate(ExprOp op, const Elt &a, const Elt &b) const {
    const F &f = f_;
    switch (op) {
      case ExprOp::kAdd:
        return f.addf(a, b);
      case ExprOp::kMul:
      case ExprOp::kAnd:
        return f.mulf(a, b);
      case ExprOp::kOr:
        return f.subf(f.addf(a, b), f.mulf(a, b));
      default: {
        const Elt ab = f.mulf(a, b);
        return f.subf(f.addf(a, b), f.addf(ab, ab));
      }
    }
  }

  const F &f_;
  const ValueReader &v_;
  std::unordered_map<const ExprNode<F> *, std::vector<Elt>> memo_;
};

// The values of E on host values V: DirectEval when it takes E, otherwise
// the emitter over Logic's evaluation backend, which computes with field
// operations only. Neither branches on a value: the choice reads the
// expression's structure.
template <class F>
std::vector<typename F::Elt> eval_expr(const ExprPtr<F> &e,
                                       const ValueReader &v) {
  if (DirectEval<F>::admits(*e)) {
    DirectEval<F> d(*e->f, v);
    return d(e.get());
  }
  using EB = EvaluationBackend<F>;
  using EL = Logic<F, EB>;
  const F &f = *e->f;
  const EB eb(f, /*panic_on_assertion_failure=*/false);
  const EL el(&eb, f);
  ExprEmitter<F, EL> em(el, [&](const Term<F> &t) {
    std::vector<typename F::Elt> x = v.template get<F>(t.node);
    for (const auto &spec : t.chain) {
      std::vector<typename F::Elt> y(spec->rows);
      instantiate(*spec, v)->apply(x.data(), y.data());
      x = std::move(y);
    }
    std::vector<typename EB::V> out;
    out.reserve(x.size());
    for (const auto &y : x) out.push_back(typename EB::V(y));
    return out;
  }, [&](const OpSpec<F> &spec, const std::vector<typename EB::V> &w) {
    // The operator instantiated from public values, as affine rows read it.
    std::vector<typename F::Elt> x, y(spec.rows);
    for (const auto &u : w) x.push_back(u.elt());
    instantiate(spec, v)->apply(x.data(), y.data());
    std::vector<typename EB::V> out;
    for (const auto &u : y) out.push_back(typename EB::V(u));
    return out;
  });
  std::vector<typename F::Elt> out;
  for (const auto &b : em(e)) out.push_back(el.eval(b).elt());
  return out;
}

// ------------------------------------------------------------ analysis --

// The node ids an expression reads: its leaves' nodes and their
// operators' parameters.
template <class F>
void expr_deps(const ExprPtr<F> &e, std::vector<size_t> &out) {
  // The nodes visited: a list while it is short (a predicate's expression
  // has a few dozen nodes), a set past that.
  constexpr size_t kShort = 64;
  std::vector<const ExprNode<F> *> few;
  std::unordered_set<const ExprNode<F> *> many;
  auto visit = [&](const ExprNode<F> *x) {
    if (many.empty()) {
      if (std::find(few.begin(), few.end(), x) != few.end()) return false;
      few.push_back(x);
      if (few.size() > kShort) many.insert(few.begin(), few.end());
      return true;
    }
    return many.insert(x).second;
  };
  std::vector<const ExprNode<F> *> st = {e.get()};
  while (!st.empty()) {
    const ExprNode<F> *x = st.back();
    st.pop_back();
    if (!visit(x)) continue;
    if (x->op == ExprOp::kLin)
      for (const auto &t : x->lin.terms) {
        out.push_back(t.node);
        for (const auto &op : t.chain)
          out.insert(out.end(), op->deps.begin(), op->deps.end());
      }
    if (x->op == ExprOp::kApply)
      out.insert(out.end(), x->apply->deps.begin(), x->apply->deps.end());
    for (const auto &k : x->kids) st.push_back(k.get());
  }
}
template <class F>
std::vector<size_t> expr_deps(const ExprPtr<F> &e) {
  std::vector<size_t> out;
  expr_deps(e, out);
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
  return out;
}
// The graph of the first handle E reads (a leaf's affine expression), or
// null when E reads none: a predicate finds its system through it.
template <class F>
Graph *graph_of(const ExprPtr<F> &e) {
  std::vector<const ExprNode<F> *> stack = {e.get()};
  std::set<const ExprNode<F> *> seen;
  while (!stack.empty()) {
    const ExprNode<F> *x = stack.back();
    stack.pop_back();
    if (x == nullptr || !seen.insert(x).second) continue;
    if (x->op == ExprOp::kLin && x->lin.g != nullptr) return x->lin.g;
    for (const auto &k : x->kids) stack.push_back(k.get());
  }
  return nullptr;
}

// ------------------------------------------------- depends_on entries --

// An expression in depends_on (core.h's DepEntry): it depends on the nodes
// its leaves read, and a closure receives its values, which the host
// computes with the emitter (eval_expr) once per run.
template <class F, class T>
struct ExprDep {
  using field_type = F;
  using type_tag = T;
  using place_tag = AnyPlace;
  ExprPtr<F> node;
  const F *f = nullptr;
  std::vector<size_t> dims() const { return node->dims(); }
  std::vector<size_t> ids() const { return expr_deps(node); }
};
template <class F, class T>
struct IsExprDep<ExprDep<F, T>> : std::true_type {};
template <class R>
struct DepEntry<R, std::enable_if_t<kIsPoly<R> && !IsRef<R>::value>> {
  using type = ExprDep<PolyField<R>, PolyType<R>>;
  static type of(const R &r) {
    const auto e = expr_node(r);
    return type{e, e->f};
  }
};
// The values of a depends_on entry R of a field: a handle's node, or an
// expression's values, evaluated once per run and kept in the store's
// records.
template <class R>
const std::vector<typename R::field_type::Elt> &dep_values(
    const ValueReader &v, const R &r) {
  using G = typename R::field_type;
  using V = std::vector<typename G::Elt>;
  if constexpr (IsExprDep<R>::value) {
    auto &cell = v.records[r.node.get()];
    if (!cell) cell = std::make_shared<V>(eval_expr(r.node, v));
    return *std::static_pointer_cast<V>(cell);
  } else {
    return v.template get<G>(r.id);
  }
}

// An affine form Lin + C of an expression (C one constant per
// coordinate), when it has one: sums, scalings by constants, sums of
// coordinates and broadcasts of affine expressions, and products of an
// affine expression by a uniform constant or by a lone public value
// (Diagonal, or ScaleBy for a scalar). PUBLIC_NODE says whether a node is
// a public value; READABLE whether an affine row reads it.
template <class F>
struct AffineForm {
  Lin<F> lin;  // may have no terms
  std::vector<typename F::Elt> c;
  // Constants through operators that depend on public values (an operator
  // applied to an affine expression with a constant term): each is
  // scale (chain ... )(values), whose values the operators' instantiation
  // gives per statement, as affine rows instantiate them.
  struct ConstTerm {
    typename F::Elt scale;
    std::vector<std::shared_ptr<const OpSpec<F>>> chain;
    std::vector<typename F::Elt> values;
  };
  std::vector<ConstTerm> kc;
};
template <class F>
std::optional<AffineForm<F>> affine_form(
    const ExprPtr<F> &e, const std::function<bool(size_t)> &public_node,
    const std::function<bool(size_t)> &readable) {
  using Elt = typename F::Elt;
  const F &f = *e->f;
  auto empty = [&](size_t n, std::vector<size_t> shape) {
    AffineForm<F> a;
    a.lin.f = &f;
    a.lin.n = n;
    a.lin.shape = std::move(shape);
    a.c.assign(n, f.zero());
    return a;
  };
  auto uniform = [](const std::vector<Elt> &c) {
    for (const auto &x : c)
      if (x != c[0]) return false;
    return true;
  };
  auto scaled = [&](AffineForm<F> a, const Elt &k) {
    for (auto &t : a.lin.terms) t.scale = f.mulf(k, t.scale);
    for (auto &x : a.c) x = f.mulf(k, x);
    for (auto &t : a.kc) t.scale = f.mulf(k, t.scale);
    return a;
  };
  // The constants of A through SPEC, which maps them to N coordinates:
  // computed now when SPEC reads no public value, carried in kc otherwise.
  auto through = [&](const AffineForm<F> &a, std::shared_ptr<const OpSpec<F>> spec,
                     AffineForm<F> &r) {
    for (auto t : a.kc) {
      t.chain.push_back(spec);
      r.kc.push_back(std::move(t));
    }
    bool zero = true;
    for (const auto &c : a.c) zero &= c == f.zero();
    if (zero) return;
    if (spec->deps.empty()) {
      std::vector<Elt> y(spec->rows);
      spec->make(OpArgs{})->apply(a.c.data(), y.data());
      for (size_t i = 0; i < y.size(); ++i) f.add(r.c[i], y[i]);
      return;
    }
    r.kc.push_back({f.one(), {spec}, a.c});
  };
  std::function<std::optional<AffineForm<F>>(const ExprNode<F> &)> go =
      [&](const ExprNode<F> &x) -> std::optional<AffineForm<F>> {
    switch (x.op) {
      case ExprOp::kLin: {
        for (const auto &t : x.lin.terms)
          if (!readable(t.node)) return std::nullopt;
        AffineForm<F> a = empty(x.n, x.shape);
        a.lin = x.lin;
        return a;
      }
      case ExprOp::kConst: {
        AffineForm<F> a = empty(x.n, x.shape);
        a.c = x.c;
        return a;
      }
      case ExprOp::kAdd: {
        auto a = go(*x.kids[0]);
        auto b = go(*x.kids[1]);
        if (!a || !b) return std::nullopt;
        a->lin.terms.insert(a->lin.terms.end(), b->lin.terms.begin(),
                            b->lin.terms.end());
        if (a->lin.shape.empty()) a->lin.shape = b->lin.shape;
        for (size_t i = 0; i < x.n; ++i) f.add(a->c[i], b->c[i]);
        a->kc.insert(a->kc.end(), b->kc.begin(), b->kc.end());
        return a;
      }
      case ExprOp::kScale: {
        auto a = go(*x.kids[0]);
        if (!a) return std::nullopt;
        return scaled(std::move(*a), x.c[0]);
      }
      case ExprOp::kMul: {
        auto a = go(*x.kids[0]);
        auto b = go(*x.kids[1]);
        if (!a || !b) return std::nullopt;
        for (int side = 0; side < 2; ++side) {
          AffineForm<F> &k = side == 0 ? *a : *b;
          AffineForm<F> &o = side == 0 ? *b : *a;
          if (k.lin.terms.empty() && k.kc.empty() && uniform(k.c))
            return scaled(std::move(o), k.c[0]);
        }
        // Constants of the system, one per coordinate (a lifted C++ array),
        // times an affine expression: its terms and constants through
        // ConstDiagonal.
        for (int side = 0; side < 2; ++side) {
          const AffineForm<F> &k = side == 0 ? *a : *b;
          const AffineForm<F> &o = side == 0 ? *b : *a;
          if (!k.lin.terms.empty() || !k.kc.empty()) continue;
          const auto diag = ConstDiagonal(f, k.c).spec;
          AffineForm<F> r = empty(x.n, x.shape);
          for (auto t : o.lin.terms) {
            t.chain.push_back(diag);
            r.lin.terms.push_back(std::move(t));
          }
          for (size_t i = 0; i < x.n; ++i) r.c[i] = f.mulf(k.c[i], o.c[i]);
          for (auto t : o.kc) {
            t.chain.push_back(diag);
            r.kc.push_back(std::move(t));
          }
          return r;
        }
        // A lone public value (one term, no operator, possibly broadcast
        // from a scalar) times an affine expression, no constant on either
        // side: Diagonal, or ScaleBy for a scalar.
        for (int side = 0; side < 2; ++side) {
          const ExprNode<F> *p = x.kids[side].get();
          bool scalar = false;
          if (p->op == ExprOp::kBroadcast) {
            p = p->kids[0].get();
            scalar = true;
          }
          if (p->op != ExprOp::kLin || p->lin.terms.size() != 1 ||
              !p->lin.terms[0].chain.empty() ||
              !public_node(p->lin.terms[0].node))
            continue;
          const AffineForm<F> &o = side == 0 ? *b : *a;
          bool zero = true;
          for (const auto &c : o.c) zero &= c == f.zero();
          if (!zero || !o.kc.empty() || o.lin.terms.empty()) continue;
          for (const auto &t : o.lin.terms)
            if (public_node(t.node)) return std::nullopt;
          const Term<F> &t = p->lin.terms[0];
          if (!scalar && t.in_n != x.n) return std::nullopt;
          const Ref<F> pr{t.node, t.in_n, &f, nullptr, {}};
          AffineForm<F> r = empty(x.n, x.shape);
          r.lin = scalar ? ScaleBy(pr, x.n)(o.lin) : Diagonal(pr)(o.lin);
          for (auto &u : r.lin.terms) u.scale = f.mulf(t.scale, u.scale);
          r.lin.shape = x.shape;
          return r;
        }
        return std::nullopt;
      }
      case ExprOp::kSum: {
        auto a = go(*x.kids[0]);
        if (!a) return std::nullopt;
        if (x.w == 0) {
          AffineForm<F> r = empty(1, {});
          if (!a->lin.terms.empty()) r.lin = Sum(a->lin);
          r.lin.shape = {};
          for (const auto &c : a->c) f.add(r.c[0], c);
          for (auto t : a->kc) {
            t.chain.push_back(Sum(f, x.kids[0]->n).spec);
            r.kc.push_back(std::move(t));
          }
          return r;
        }
        // The sums of groups of w along the last axis: Sum batched over
        // the leading axes.
        AffineForm<F> r = empty(x.n, x.shape);
        if (!a->lin.terms.empty()) {
          a->lin.shape = x.kids[0]->dims();
          r.lin = Sum(f, x.w)(a->lin);
          r.lin.shape = x.shape;
        }
        for (size_t k = 0; k < x.n; ++k)
          for (size_t j = 0; j < x.w; ++j) f.add(r.c[k], a->c[k * x.w + j]);
        const auto sum = Sum(f, x.w).fit(x.kids[0]->dims(), x.kids[0]->n).first;
        for (auto t : a->kc) {
          t.chain.push_back(sum);
          r.kc.push_back(std::move(t));
        }
        return r;
      }
      case ExprOp::kBroadcast: {
        auto a = go(*x.kids[0]);
        if (!a) return std::nullopt;
        AffineForm<F> r = empty(x.n, x.shape);
        if (!a->lin.terms.empty()) {
          // A lone public scalar broadcast stays one term; Lin has no
          // public broadcast of its own, so the Gather operator carries it.
          r.lin = broadcast_scalar(a->lin, x.dims());
        }
        r.c.assign(x.n, a->c.at(0));
        for (auto t : a->kc) {
          t.chain.push_back(Gather(f, std::vector<size_t>(x.n, 0), 1).spec);
          r.kc.push_back(std::move(t));
        }
        return r;
      }
      case ExprOp::kGather: {
        // Each kid's terms through the Gather of the coordinates the view
        // reads from it (kGatherNone elsewhere).
        AffineForm<F> r = empty(x.n, x.shape);
        r.lin.terms.clear();
        size_t at = 0;
        std::vector<std::pair<size_t, size_t>> where(x.n);  // kid, coordinate
        std::vector<size_t> first;
        for (const auto &k : x.kids) {
          first.push_back(at);
          at += k->n;
        }
        for (size_t i = 0; i < x.n; ++i) {
          const size_t j = x.idx[i];
          size_t k = 0;
          while (k + 1 < first.size() && first[k + 1] <= j) ++k;
          where[i] = {k, j - first[k]};
        }
        for (size_t k = 0; k < x.kids.size(); ++k) {
          auto a = go(*x.kids[k]);
          if (!a) return std::nullopt;
          std::vector<size_t> idx(x.n, kGatherNone);
          bool any = false;
          for (size_t i = 0; i < x.n; ++i)
            if (where[i].first == k) {
              idx[i] = where[i].second;
              r.c[i] = a->c.at(where[i].second);
              any = true;
            }
          if (!any || (a->lin.terms.empty() && a->kc.empty())) continue;
          const auto g = Gather(f, std::move(idx), x.kids[k]->n).spec;
          for (auto t : a->lin.terms) {
            t.chain.push_back(g);
            r.lin.terms.push_back(std::move(t));
          }
          for (auto t : a->kc) {
            t.chain.push_back(g);
            r.kc.push_back(std::move(t));
          }
        }
        return r;
      }
      case ExprOp::kApply: {
        // The operator on the terms, and on the constants (through).
        auto a = go(*x.kids[0]);
        if (!a) return std::nullopt;
        AffineForm<F> r = empty(x.n, x.shape);
        r.lin.terms.clear();
        for (auto t : a->lin.terms) {
          t.chain.push_back(x.apply);
          r.lin.terms.push_back(std::move(t));
        }
        through(*a, x.apply, r);
        return r;
      }
      default:
        return std::nullopt;
    }
  };
  return go(*e);
}

// A screen in front of affine_form for the expressions of one graph: false
// when E certainly has no affine form, without building one. affine_form
// builds each operand's form before it looks at a product, so a product of
// two affine operands costs their full forms, and a view of a large value
// costs a vector of that value's size; the screen decides those predicates
// from the expression's structure. A node's result is kept for every later
// expression that shares it (the nodes stay alive while the screen is in
// use). The rules follow affine_form's cases: a leaf needs every term
// READABLE; a product needs one operand without terms (a constant) or a
// lone public value (PUBLIC_NODE), so two operands that both certainly have
// terms reject it; a view has terms when an operand it reads does; any
// other operation has no affine form.
template <class F>
class AffineScreen {
 public:
  AffineScreen(std::function<bool(size_t)> public_node,
               std::function<bool(size_t)> readable)
      : public_node_(std::move(public_node)), readable_(std::move(readable)) {}
  bool possible(const ExprNode<F> &e) { return visit(e).possible; }

 private:
  struct Facts {
    // affine_form may succeed on the node.
    bool possible = false;
    // Its form, when there is one, certainly has a term.
    bool terms = false;
  };
  bool lone_public(const ExprNode<F> &x) const {
    const ExprNode<F> *p = &x;
    if (p->op == ExprOp::kBroadcast) p = p->kids[0].get();
    return p->op == ExprOp::kLin && p->lin.terms.size() == 1 &&
           p->lin.terms[0].chain.empty() && public_node_(p->lin.terms[0].node);
  }
  Facts visit(const ExprNode<F> &x) {
    auto it = memo_.find(&x);
    if (it != memo_.end()) return it->second;
    const Facts r = facts(x);
    memo_.emplace(&x, r);
    return r;
  }
  Facts facts(const ExprNode<F> &x) {
    switch (x.op) {
      case ExprOp::kLin: {
        for (const auto &t : x.lin.terms)
          if (!readable_(t.node)) return {};
        return {true, !x.lin.terms.empty()};
      }
      case ExprOp::kConst:
        return {true, false};
      case ExprOp::kAdd: {
        const Facts a = visit(*x.kids[0]);
        const Facts b = visit(*x.kids[1]);
        return {a.possible && b.possible, a.terms || b.terms};
      }
      case ExprOp::kScale:
      case ExprOp::kSum:
      case ExprOp::kBroadcast:
      case ExprOp::kApply:
        return visit(*x.kids[0]);
      case ExprOp::kMul: {
        const Facts a = visit(*x.kids[0]);
        const Facts b = visit(*x.kids[1]);
        if (!a.possible || !b.possible) return {};
        if (a.terms && b.terms && !lone_public(*x.kids[0]) &&
            !lone_public(*x.kids[1]))
          return {};
        return {true, a.terms || b.terms};
      }
      case ExprOp::kGather: {
        // The operands the view reads (affine_form drops the others' terms);
        // every operand must have a form.
        std::vector<size_t> first;
        size_t at = 0;
        for (const auto &k : x.kids) {
          first.push_back(at);
          at += k->n;
        }
        std::vector<bool> read(x.kids.size(), false);
        for (size_t i = 0; i < x.n; ++i) {
          const size_t j = x.idx[i];
          const size_t k =
              size_t(std::upper_bound(first.begin(), first.end(), j) -
                     first.begin()) - 1;
          read[k] = true;
        }
        Facts r{true, false};
        for (size_t k = 0; k < x.kids.size(); ++k) {
          const Facts a = visit(*x.kids[k]);
          if (!a.possible) return {};
          r.terms = r.terms || (read[k] && a.terms);
        }
        return r;
      }
      default:
        return {};
    }
  }
  std::function<bool(size_t)> public_node_;
  std::function<bool(size_t)> readable_;
  std::unordered_map<const ExprNode<F> *, Facts> memo_;
};

// The degree of E as a polynomial in its leaves' values, which placement
// reads (an affine leaf has degree 1, a constant 0): a sum, a view, a sum
// of coordinates or a broadcast takes its operands' largest, a product
// adds, a product of w coordinates multiplies by w, and !b, a & b, a | b,
// a ^ b and c.mux(t, e) follow their polynomials (1 - b, a b, a + b - a b,
// a + b - 2 a b, e + c (t - e)). The comparisons, any and all
// are kCircuitDegree: Logic builds them, so only the circuit places them.
constexpr size_t kCircuitDegree = SIZE_MAX;
// The same with the degree of each affine leaf given by LEAF and each
// operator node adding OP's (the degree of its matrix in what it reads):
// the degree in one challenge counts the leaves that read it.
template <class F>
size_t expr_degree(const ExprPtr<F> &e,
                   const std::function<size_t(const Lin<F> &)> &leaf,
                   const std::function<size_t(const OpSpec<F> &)> &op) {
  auto plus = [](size_t a, size_t b) {
    return a > kCircuitDegree - b ? kCircuitDegree : a + b;
  };
  auto times = [](size_t a, size_t b) {
    return b != 0 && a > kCircuitDegree / b ? kCircuitDegree : a * b;
  };
  std::map<const ExprNode<F> *, size_t> memo;
  std::function<size_t(const ExprNode<F> &)> go =
      [&](const ExprNode<F> &x) -> size_t {
    auto it = memo.find(&x);
    if (it != memo.end()) return it->second;
    size_t d = 0;
    switch (x.op) {
      case ExprOp::kLin:
        d = leaf(x.lin);
        break;
      case ExprOp::kConst:
        d = 0;
        break;
      case ExprOp::kAdd:
      case ExprOp::kGather:
        for (const auto &k : x.kids) d = std::max(d, go(*k));
        break;
      case ExprOp::kApply:
        d = plus(go(*x.kids[0]), op(*x.apply));
        break;
      case ExprOp::kScale:
      case ExprOp::kSum:
      case ExprOp::kBroadcast:
      case ExprOp::kMaterialize:
      case ExprOp::kNot:
        d = go(*x.kids[0]);
        break;
      case ExprOp::kMul:
      case ExprOp::kConv:
      case ExprOp::kAnd:
      case ExprOp::kOr:
      case ExprOp::kXor:
        d = plus(go(*x.kids[0]), go(*x.kids[1]));
        break;
      case ExprOp::kMux:
        d = plus(go(*x.kids[0]), std::max(go(*x.kids[1]), go(*x.kids[2])));
        break;
      case ExprOp::kProd:
        d = times(go(*x.kids[0]), x.w);
        break;
      case ExprOp::kLt:
      case ExprOp::kLeq:
      case ExprOp::kEq:
      case ExprOp::kAny:
      case ExprOp::kAll:
        // A comparison of operands of degree 0 (constants, or values that
        // do not read the variable counted) is a constant.
        for (const auto &k : x.kids)
          if (go(*k) != 0) d = kCircuitDegree;
        break;
    }
    memo[&x] = d;
    return d;
  };
  return go(*e);
}
template <class F>
size_t expr_degree(const ExprPtr<F> &e) {
  return expr_degree<F>(
      e, [](const Lin<F> &l) -> size_t { return l.terms.empty() ? 0 : 1; },
      [](const OpSpec<F> &) -> size_t { return 0; });
}

// deg_c of a node's value at each coordinate, for the challenge C: 1 for C; the
// recorded degrees of a public expression or a public view
// (Node::challenge_degrees), each coordinate's its own; at every coordinate the
// largest of its sources' for a derived view; and 0 for a statement value, a
// constant, a value the prover chooses or a message. A public closure that
// reads C has no known degree (kCircuitDegree); (Pub-chal) leaves only the core
// realizations' closures, over their own challenges.
inline CoordDegrees node_coord_degrees(const std::vector<Node> &N, size_t id,
                                       size_t c) {
  const Node &n = N.at(id);
  if (id == c) return CoordDegrees::uniform(n.n, 1);
  if (n.kind == Kind::kPublicCompute && (n.expression || public_view(n))) {
    for (const auto &[ch, deg] : n.challenge_degrees)
      if (ch == c) return deg;
    return CoordDegrees::uniform(n.n, 0);
  }
  if (n.kind == Kind::kDerived) {
    size_t d = 0;
    for (size_t x : n.deps)
      d = std::max(d, node_coord_degrees(N, x, c).max());
    return CoordDegrees::uniform(n.n, d);
  }
  if (n.kind == Kind::kPublicCompute) {
    const std::vector<size_t> r = challenges_read(N, n.deps);
    return CoordDegrees::uniform(
        n.n, std::binary_search(r.begin(), r.end(), c) ? kCircuitDegree : 0);
  }
  return CoordDegrees::uniform(n.n, 0);
}

// The degrees of the public view whose coordinate i reads SRC[i] = (node,
// index), or zero for kZeroCoordinate, in each challenge its sources read:
// each coordinate the degree of the coordinate it reads.
inline std::vector<std::pair<size_t, CoordDegrees>> view_coord_degrees(
    const std::vector<Node> &N,
    const std::vector<std::pair<size_t, size_t>> &src,
    const std::vector<size_t> &deps) {
  std::vector<std::pair<size_t, CoordDegrees>> out;
  for (size_t c : challenges_read(N, deps)) {
    std::map<size_t, CoordDegrees> of;
    std::vector<size_t> v(src.size(), 0);
    for (size_t i = 0; i < src.size(); ++i) {
      const auto [id, k] = src[i];
      if (id == kZeroCoordinate) continue;
      auto it = of.find(id);
      if (it == of.end())
        it = of.emplace(id, node_coord_degrees(N, id, c)).first;
      v[i] = it->second.at(k);
    }
    out.push_back({c, CoordDegrees::of(std::move(v))});
  }
  return out;
}

// deg_c(E) at each coordinate of E, for the challenge C over the nodes N. A
// leaf's coordinate has the degree of the node coordinate it reads, through the
// views of its chain, plus, per other operator of the chain, the largest degree
// of the operator's parameters; + takes the coordinatewise largest and a
// product adds; a view (reindex, slice, at, concat, reshape, broadcast) gives
// each coordinate the degree of the coordinate it reads; a sum takes the
// largest of its group and prod adds its group's; an operator node gives each
// output the largest degree of its input plus the largest of its parameters; a
// comparison, any or all of an operand of nonzero degree has kCircuitDegree.
template <class F>
CoordDegrees challenge_coord_degrees(const ExprPtr<F> &e, size_t c,
                                     const std::vector<Node> &N) {
  auto plus = [](size_t a, size_t b) {
    return a > kCircuitDegree - b ? kCircuitDegree : a + b;
  };
  auto times = [](size_t a, size_t b) {
    return b != 0 && a > kCircuitDegree / b ? kCircuitDegree : a * b;
  };
  std::unordered_map<size_t, CoordDegrees> nodes;
  auto node_deg = [&](size_t id) -> const CoordDegrees & {
    auto it = nodes.find(id);
    if (it == nodes.end())
      it = nodes.emplace(id, node_coord_degrees(N, id, c)).first;
    return it->second;
  };
  auto op_degree = [&](const OpSpec<F> &op) -> size_t {
    size_t d = 0;
    for (size_t x : op.deps) d = std::max(d, node_deg(x).max());
    return d;
  };
  // FN(a_i, b_i) at each coordinate of N, a side of one coordinate read at
  // every coordinate.
  auto zip = [](const CoordDegrees &a, const CoordDegrees &b, size_t n,
                auto fn) {
    if (a.v.empty() && b.v.empty())
      return CoordDegrees::uniform(n, fn(a.u, b.u));
    std::vector<size_t> v(n);
    for (size_t i = 0; i < n; ++i)
      v[i] = fn(a.at(a.n == 1 ? 0 : i), b.at(b.n == 1 ? 0 : i));
    return CoordDegrees::of(std::move(v));
  };
  auto larger = [](size_t a, size_t b) { return std::max(a, b); };
  // OP applied to X: a gather without parameters moves each coordinate's
  // degree to the rows that read it; any other operator gives every row
  // X's largest plus the largest degree of its parameters.
  auto through = [&](const OpSpec<F> &op, const CoordDegrees &x) {
    if (op.name == "gather" && op.deps.empty() && op.emit &&
        !x.v.empty() && x.n == op.cols) {
      const auto rows = op.emit();
      std::vector<size_t> v(rows.size(), 0);
      for (size_t i = 0; i < rows.size(); ++i)
        for (const auto &[j, k] : rows[i]) v[i] = std::max(v[i], x.at(j));
      return CoordDegrees::of(std::move(v));
    }
    return CoordDegrees::uniform(op.rows, plus(x.max(), op_degree(op)));
  };
  std::unordered_map<const ExprNode<F> *, CoordDegrees> memo;
  std::function<const CoordDegrees &(const ExprNode<F> &)> go =
      [&](const ExprNode<F> &x) -> const CoordDegrees & {
    auto it = memo.find(&x);
    if (it != memo.end()) return it->second;
    CoordDegrees d = CoordDegrees::uniform(x.n, 0);
    switch (x.op) {
      case ExprOp::kLin:
        for (const auto &t : x.lin.terms) {
          CoordDegrees td = node_deg(t.node);
          for (const auto &op : t.chain) td = through(*op, td);
          if (td.n != x.n) td = CoordDegrees::uniform(x.n, td.max());
          d = zip(d, td, x.n, larger);
        }
        break;
      case ExprOp::kConst:
        break;
      case ExprOp::kAdd:
        for (const auto &k : x.kids) d = zip(d, go(*k), x.n, larger);
        break;
      case ExprOp::kApply: {
        const CoordDegrees &a = go(*x.kids[0]);
        d = a.n == x.apply->cols
                ? through(*x.apply, a)
                : CoordDegrees::uniform(
                      x.n, plus(a.max(), op_degree(*x.apply)));
        if (d.n != x.n) d = CoordDegrees::uniform(x.n, d.max());
        break;
      }
      case ExprOp::kScale:
      case ExprOp::kMaterialize:
      case ExprOp::kNot:
        d = go(*x.kids[0]);
        break;
      case ExprOp::kSum:
      case ExprOp::kProd: {
        const CoordDegrees &a = go(*x.kids[0]);
        const bool prod = x.op == ExprOp::kProd;
        const size_t w = x.w == 0 ? a.n : x.w;
        if (a.v.empty()) {
          d = CoordDegrees::uniform(x.n, prod ? times(a.u, w) : a.u);
          break;
        }
        std::vector<size_t> v(x.n, 0);
        for (size_t g = 0; g < x.n; ++g)
          for (size_t i = g * w; i < (g + 1) * w; ++i)
            v[g] = prod ? plus(v[g], a.at(i)) : std::max(v[g], a.at(i));
        d = CoordDegrees::of(std::move(v));
        break;
      }
      case ExprOp::kBroadcast:
        d = CoordDegrees::uniform(x.n, go(*x.kids[0]).at(0));
        break;
      case ExprOp::kGather: {
        bool uniform = true;
        for (const auto &k : x.kids) {
          const CoordDegrees &a = go(*k);
          uniform = uniform && a.v.empty() && a.u == go(*x.kids[0]).u;
        }
        if (uniform) {
          d = CoordDegrees::uniform(x.n, go(*x.kids[0]).u);
          break;
        }
        std::vector<size_t> all;
        for (const auto &k : x.kids) {
          const CoordDegrees &a = go(*k);
          for (size_t i = 0; i < a.n; ++i) all.push_back(a.at(i));
        }
        std::vector<size_t> v(x.n, 0);
        for (size_t i = 0; i < x.n; ++i)
          if (x.idx[i] != kGatherNone) v[i] = all.at(x.idx[i]);
        d = CoordDegrees::of(std::move(v));
        break;
      }
      case ExprOp::kMul:
      case ExprOp::kAnd:
      case ExprOp::kOr:
      case ExprOp::kXor:
        for (const auto &k : x.kids) d = zip(d, go(*k), x.n, plus);
        break;
      case ExprOp::kConv: {
        const size_t a = go(*x.kids[0]).max(), b = go(*x.kids[1]).max();
        d = CoordDegrees::uniform(x.n, plus(a, b));
        break;
      }
      case ExprOp::kMux:
        d = zip(go(*x.kids[0]),
                zip(go(*x.kids[1]), go(*x.kids[2]), x.n, larger), x.n, plus);
        break;
      case ExprOp::kLt:
      case ExprOp::kLeq:
      case ExprOp::kEq:
      case ExprOp::kAny:
      case ExprOp::kAll:
        // A comparison of operands of degree 0 (constants, or values that
        // do not read the variable counted) is a constant.
        for (const auto &k : x.kids)
          if (go(*k).max() != 0) d = CoordDegrees::uniform(x.n, kCircuitDegree);
        break;
    }
    return memo.emplace(&x, std::move(d)).first->second;
  };
  return go(*e);
}

// deg_c(E), the largest degree among E's coordinates.
template <class F>
size_t challenge_degree(const ExprPtr<F> &e, size_t c,
                        const std::vector<Node> &N) {
  return challenge_coord_degrees(e, c, N).max();
}

// (challenge, deg_c(E) at each coordinate) for every challenge E reads,
// directly or through public computations and views, in increasing
// challenge order.
template <class F>
std::vector<std::pair<size_t, CoordDegrees>> challenge_coord_degrees(
    const ExprPtr<F> &e, const std::vector<Node> &N) {
  std::vector<std::pair<size_t, CoordDegrees>> out;
  for (size_t c : challenges_read(N, expr_deps(e)))
    out.push_back({c, challenge_coord_degrees(e, c, N)});
  return out;
}

// (challenge, deg_c(E)) for every challenge E reads, directly or through
// public computations and derived views, in increasing challenge order.
template <class F>
std::vector<std::pair<size_t, size_t>> challenge_degrees(
    const ExprPtr<F> &e, const std::vector<Node> &N) {
  std::vector<std::pair<size_t, size_t>> out;
  for (size_t c : challenges_read(N, expr_deps(e)))
    out.push_back({c, challenge_degree(e, c, N)});
  return out;
}

// a b = c with A, B and C single handles: the elementwise quadratic triple
// of an expression k (a b - c) or k (c - a b), k a nonzero constant.
struct TripleForm {
  size_t a = 0, b = 0, c = 0;
};
template <class F>
std::optional<TripleForm> triple_form(const ExprPtr<F> &e) {
  using Elt = typename F::Elt;
  const F &f = *e->f;
  // The summands of E with their constant factors.
  std::vector<std::pair<Elt, const ExprNode<F> *>> parts;
  std::function<bool(const ExprNode<F> &, const Elt &)> split =
      [&](const ExprNode<F> &x, const Elt &k) {
        if (x.op == ExprOp::kAdd)
          return split(*x.kids[0], k) && split(*x.kids[1], k);
        if (x.op == ExprOp::kScale) return split(*x.kids[0], f.mulf(k, x.c[0]));
        parts.push_back({k, &x});
        return true;
      };
  if (!split(*e, f.one()) || parts.size() != 2) return std::nullopt;
  // A single handle: one term, no operator; its scale.
  auto single = [](const ExprNode<F> &x) -> std::optional<std::pair<size_t, Elt>> {
    if (x.op != ExprOp::kLin || x.lin.terms.size() != 1 ||
        !x.lin.terms[0].chain.empty() || x.lin.terms[0].in_n != x.n)
      return std::nullopt;
    return std::make_pair(x.lin.terms[0].node, x.lin.terms[0].scale);
  };
  for (int m = 0; m < 2; ++m) {
    const auto &[km, pm] = parts[m];
    const auto &[kc, pc] = parts[1 - m];
    if (pm->op != ExprOp::kMul) continue;
    const auto a = single(*pm->kids[0]);
    const auto b = single(*pm->kids[1]);
    const auto c = single(*pc);
    if (!a || !b || !c) continue;
    if (pm->kids[0]->n != e->n || pm->kids[1]->n != e->n) continue;
    // km sa sb (a b) + kc sc c = 0 is a b = c when km sa sb = -kc sc.
    const Elt lhs = f.mulf(km, f.mulf(a->second, b->second));
    const Elt rhs = f.negf(f.mulf(kc, c->second));
    if (lhs != rhs || lhs == f.zero()) continue;
    return TripleForm{a->first, b->first, c->first};
  }
  return std::nullopt;
}

// A coordinatewise polynomial of degree at most 2 in single handles: leaves
// that read one whole node with no operator (Lin terms, their scales folded
// in), uniform constants, sums, constant scalings and products. A field
// batch reads it (FieldRelation over the leaves, the constant monomial on a
// constant operand). MONOS: sorted leaf indices (empty for the constant)
// with their coefficients, each index list once.
template <class F>
struct QuadraticForm {
  struct Mono {
    std::vector<unsigned> ops;
    typename F::Elt k;
  };
  std::vector<size_t> leaves;
  std::vector<Mono> monos;
  unsigned degree() const {
    size_t d = 0;
    for (const auto &m : monos) d = std::max(d, m.ops.size());
    return unsigned(d);
  }
  bool has_constant() const {
    for (const auto &m : monos)
      if (m.ops.empty()) return true;
    return false;
  }
};
template <class F>
std::optional<QuadraticForm<F>> quadratic_form(const ExprPtr<F> &e) {
  using Elt = typename F::Elt;
  using Poly = std::map<std::vector<unsigned>, Elt>;
  const F &f = *e->f;
  QuadraticForm<F> q;
  std::map<size_t, unsigned> leaf_of;
  auto leaf = [&](size_t id) {
    auto it = leaf_of.find(id);
    if (it != leaf_of.end()) return it->second;
    const unsigned k = unsigned(q.leaves.size());
    q.leaves.push_back(id);
    leaf_of[id] = k;
    return k;
  };
  auto add_to = [&](Poly &p, const std::vector<unsigned> &m, const Elt &k) {
    auto [it, fresh] = p.emplace(m, k);
    if (!fresh) f.add(it->second, k);
  };
  bool ok = true;
  std::function<Poly(const ExprNode<F> &)> go = [&](const ExprNode<F> &x) {
    Poly p;
    if (!ok) return p;
    switch (x.op) {
      case ExprOp::kLin:
        for (const auto &t : x.lin.terms) {
          if (!t.chain.empty() || t.in_n != e->n) {
            ok = false;
            return p;
          }
          add_to(p, {leaf(t.node)}, t.scale);
        }
        return p;
      case ExprOp::kConst:
        for (const auto &c : x.c)
          if (c != x.c.at(0)) ok = false;
        if (ok && x.c.at(0) != f.zero()) add_to(p, {}, x.c[0]);
        return p;
      case ExprOp::kAdd: {
        p = go(*x.kids[0]);
        for (const auto &[m, k] : go(*x.kids[1])) add_to(p, m, k);
        return p;
      }
      case ExprOp::kScale:
        for (const auto &[m, k] : go(*x.kids[0])) add_to(p, m, f.mulf(x.c[0], k));
        return p;
      case ExprOp::kBroadcast:
        // A broadcast constant; a broadcast cell is no coordinatewise leaf.
        p = go(*x.kids[0]);
        for (const auto &[m, k] : p)
          if (!m.empty()) ok = false;
        return p;
      case ExprOp::kMul: {
        const Poly a = go(*x.kids[0]);
        const Poly b = go(*x.kids[1]);
        for (const auto &[ma, ka] : a)
          for (const auto &[mb, kb] : b) {
            std::vector<unsigned> m = ma;
            m.insert(m.end(), mb.begin(), mb.end());
            if (m.size() > 2) {
              ok = false;
              return p;
            }
            std::sort(m.begin(), m.end());
            add_to(p, m, f.mulf(ka, kb));
          }
        return p;
      }
      default:
        ok = false;
        return p;
    }
  };
  if (e->n == 0) return std::nullopt;
  const Poly p = go(*e);
  if (!ok) return std::nullopt;
  for (const auto &[m, k] : p)
    if (k != f.zero()) q.monos.push_back({m, k});
  if (q.monos.empty() || q.leaves.empty()) return std::nullopt;
  return q;
}

// Description bytes of an expression (the system digest): each node once,
// children before parents, by its index in that order. The node count
// comes first; the nodes are written in place after it.
template <class F>
void describe_expr(const ExprPtr<F> &e,
                   const std::function<std::vector<uint8_t>(const Lin<F> &)>
                       &describe_lin,
                   std::vector<uint8_t> &out) {
  using N = ExprNode<F>;
  // Each written node's index: a list while it is short (a predicate's
  // expression has a few dozen nodes), a map past that.
  constexpr size_t kShort = 64;
  std::vector<std::pair<const N *, size_t>> few;
  std::unordered_map<const N *, size_t> many;
  size_t count = 0;
  auto index_of = [&](const N *x) -> long {
    if (many.empty()) {
      for (const auto &[p, i] : few)
        if (p == x) return long(i);
      return -1;
    }
    auto it = many.find(x);
    return it == many.end() ? -1 : long(it->second);
  };
  auto record = [&](const N *x) {
    const size_t k = count++;
    if (!many.empty()) {
      many.emplace(x, k);
      return;
    }
    few.push_back({x, k});
    if (few.size() > kShort) many.insert(few.begin(), few.end());
  };
  auto write = [&](const N &x) {
    put_u64(out, uint64_t(x.op));
    put_u64(out, x.n);
    put_u64(out, x.kids.size());
    for (const auto &k : x.kids) put_u64(out, uint64_t(index_of(k.get())));
    put_u64(out, x.w);
    // Flags: 1 imm, 4 bit (2 is unused).
    put_u64(out, (x.imm ? 1 : 0) | (x.bit ? 4 : 0));
    put_u64(out, x.value);
    if (x.op == ExprOp::kGather) {
      // The index map by its digest: views of one shape share it.
      put_u64(out, x.idx.size());
      out.insert(out.end(), x.idx.digest().begin(), x.idx.digest().end());
    }
    if (x.op == ExprOp::kApply) {
      put_str(out, x.apply->name);
      put_u64(out, x.apply->params.size());
      out.insert(out.end(), x.apply->params.begin(), x.apply->params.end());
      put_u64(out, x.apply->rows);
      put_u64(out, x.apply->cols);
      put_u64(out, x.apply->deps.size());
      for (size_t d : x.apply->deps) put_u64(out, d);
    }
    put_u64(out, x.c.size());
    if (x.op == ExprOp::kConst && x.has_cdigest) {
      // A shared constant by its digest.
      out.insert(out.end(), x.cdigest.begin(), x.cdigest.end());
    } else if (!x.c.empty()) {
      const size_t at = out.size();
      out.resize(at + x.c.size() * F::kBytes);
      for (size_t i = 0; i < x.c.size(); ++i)
        x.f->to_bytes_field(out.data() + at + i * F::kBytes, x.c[i]);
    }
    if (x.op == ExprOp::kLin) {
      const auto d = describe_lin(x.lin);
      put_u64(out, d.size());
      out.insert(out.end(), d.begin(), d.end());
    }
  };
  const size_t count_at = out.size();
  put_u64(out, 0);
  // Post-order: each node once its kids are written, the kids in order.
  std::vector<std::pair<const N *, size_t>> stack = {{e.get(), 0}};
  while (!stack.empty()) {
    const N *x = stack.back().first;
    const size_t next = stack.back().second;
    if (next == 0 && index_of(x) >= 0) {
      stack.pop_back();
      continue;
    }
    if (next < x->kids.size()) {
      ++stack.back().second;
      const N *k = x->kids[next].get();
      if (index_of(k) < 0) stack.push_back({k, 0});
      continue;
    }
    write(*x);
    record(x);
    stack.pop_back();
  }
  for (size_t i = 0; i < 8; ++i) out[count_at + i] = (count >> (8 * i)) & 0xff;
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXPR_H_
