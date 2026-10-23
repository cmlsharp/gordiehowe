// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe expression surface tests (gordiehowe_test binary): the
// methods (sum, prod, mux, any, all), the comparisons, chains, NumPy
// broadcasting, the views (rotate, reindex, slice, concat), lifted C++
// constants and index arrays, handles as expressions, expressions in
// depends_on, uncommitted expressions, staged operators in circuit-placed
// predicates, and their errors.

#include "gordiehowe/tests/gordiehowe_test.h"

namespace proofs::gordiehowe {
namespace {

using CB = CompilerBackend<AF>;
using LG = Logic<AF, CB>;
using BitW = LG::BitW;
using Set = FieldSet<SHA384, AF>;

Vec ints(std::initializer_list<uint64_t> l) {
  Vec out;
  for (uint64_t x : l) out.push_back(env().af.of_scalar(x));
  return out;
}
// The host values of E with node k's values V[k].
Vec eval(const ExprPtr<AF> &e, const std::vector<Vec> &v) {
  ValueStore<Set> s(v.size());
  for (size_t k = 0; k < v.size(); ++k) s.v[k] = Set::template wrap<AF>(v[k]);
  return eval_expr(e, s);
}
// The id and layer count of the circuit asserting each root zero, the
// leaves read as inputs (LEN[k] coordinates of node k).
struct Built {
  std::vector<uint8_t> id;
  size_t layers = 0, terms = 0;
};
Built build(const std::vector<size_t> &len,
            const std::function<void(const LG &,
                                     const std::vector<std::vector<size_t>> &)>
                &body) {
  const AF &f = env().af;
  QuadCircuit<AF> q(f);
  const CB cb(&q);
  const LG lc(&cb, f);
  std::vector<std::vector<size_t>> in(len.size());
  for (size_t k = 0; k < len.size(); ++k)
    for (size_t i = 0; i < len[k]; ++i) in[k].push_back(lc.eltw_input());
  body(lc, in);
  auto circ = q.mkcircuit(/*nc=*/1);
  Built b;
  b.id.resize(SHA384::kDigestSize);
  ::proofs::circuit_id<AF, SHA384>(b.id.data(), *circ, f);
  b.layers = circ->nl;
  b.terms = circ->nterms();
  return b;
}
void assert_zero_via_emitter(const LG &lc,
                             const std::vector<std::vector<size_t>> &in,
                             const std::vector<ExprPtr<AF>> &roots) {
  ExprEmitter<AF, LG> em(lc, [&](const Term<AF> &t) { return in[t.node]; });
  for (const auto &r : roots) em.assert_zero(r);
}
// A dishonest witness: the prover refuses it, or its proof fails.
template <class Prep>
bool rejected(Prep &prep, const Assignment &w) {
  SecureRandomEngine rng;
  ProveOptions opt;
  opt.require_satisfied = false;
  try {
    return !prep.verify(prep.prove(w, rng, opt));
  } catch (const std::runtime_error &) {
    return true;
  }
}
bool has(const std::string &report, const std::string &want) {
  return report.find(want) != std::string::npos;
}
// The CompileError of F, or "".
std::string error_of(const std::function<void()> &f) {
  try {
    f();
  } catch (const CompileError &e) {
    return e.what();
  }
  return "";
}

// The comparisons read integers of a known width (Word, x.from_bits()):
// Bit arrays and Field values have none, a C++ compile error.
template <class X, class Y, class = void>
struct HasLess : std::false_type {};
template <class X, class Y>
struct HasLess<X, Y,
               std::void_t<decltype(std::declval<X>() < std::declval<Y>())>>
    : std::true_type {};
template <class X, class Y, class = void>
struct HasEq : std::false_type {};
template <class X, class Y>
struct HasEq<X, Y,
             std::void_t<decltype(std::declval<X>() == std::declval<Y>())>>
    : std::true_type {};
using BitRef = Ref<AF, Bit, Committed>;
static_assert(!HasLess<BitRef, BitRef>::value);
static_assert(!HasLess<BitRef, int>::value);
static_assert(!HasEq<Expr<AF, Bit>, int>::value);
static_assert(!HasLess<Expr<AF, Field>, Expr<AF, Field>>::value);
static_assert(HasLess<Word<AF>, Word<AF>>::value);
static_assert(HasEq<Word<AF>, int>::value);

// ------------------------------------------------------------- prod --

// x.prod() is a balanced tree of multiplications: the circuit equals
// Logic's balanced product (Logic::mul over [0, n)), of depth
// ceil(log2 n); x.prod(axis) is one tree per group; the host values are the
// products; the degree is n times the operand's.
TEST(GordieHoweExprOps, ProdIsABalancedTree) {
  const AF &f = env().af;
  constexpr size_t n = 8;
  const Ref<AF, Subfield<>, Committed> x{0, n, &f, nullptr, {n}};
  const Ref<AF, Subfield<>, Committed> y{1, n, &f, nullptr, {2, 4}};
  const auto p = x.prod();
  static_assert(std::is_same_v<decltype(p)::type_tag, Subfield<>>);
  const Built via = build({n, n}, [&](const LG &lc, const auto &in) {
    assert_zero_via_emitter(lc, in, {p.node});
  });
  const Built direct = build({n, n}, [&](const LG &lc, const auto &in) {
    lc.assert0(lc.mul(0, n, [&](size_t i) { return in[0][i]; }));
  });
  EXPECT_EQ(via.id, direct.id);
  // log2(8) = 3 layers of products (the assertion reads the last).
  EXPECT_EQ(via.layers, 3u);
  // Along an axis: [2][4] -> [4] by axis 0, [2] by axis 1.
  EXPECT_EQ(y.prod(0).dims(), (std::vector<size_t>{4}));
  EXPECT_EQ(y.prod(1).dims(), (std::vector<size_t>{2}));
  const Vec xv = ints({1, 2, 3, 4, 5, 6, 7, 8});
  EXPECT_EQ(eval(p.node, {xv, xv})[0], f.of_scalar(40320));
  EXPECT_EQ(eval(y.prod(0).node, {xv, xv}), ints({5, 12, 21, 32}));
  EXPECT_EQ(eval(y.prod(1).node, {xv, xv}), ints({24, 1680}));
  EXPECT_EQ(expr_degree(p.node), n);
  EXPECT_EQ(expr_degree((x * x).prod().node), 2 * n);
  EXPECT_EQ(expr_degree(y.prod(0).node), 2u);
  EXPECT_EQ(expr_degree(x.sum().node), 1u);
  EXPECT_EQ(expr_degree((x - 3).prod().node), n);
}

// The grand-product multiset check: delta drawn by challenge(), and
// assert_equal((delta - v).prod(), (delta - p).prod()) placed in the
// circuit (degree n). A permutation of p proves; another vector is
// rejected; a pin to a field batch is refused.
struct GrandProduct {
  static constexpr size_t n = 8;
  Sys s{"gh-grand-product"};
  Ref<AF, Subfield<>, Committed> v;
  Ref<AF, Subfield<>, Public> p;
  Predicate perm;
  explicit GrandProduct(Placement pin = Placement::kAuto) {
    auto &A = s.domain(env().profile(), "A");
    v = A.priv(Subfield{}, "v", n);
    p = A.pub(Subfield{}, "p", n);
    auto delta = A.challenge("delta");
    perm = assert_equal((delta - v).prod(), (delta - p).prod(), "perm");
    if (pin != Placement::kAuto) perm.pin(pin);
  }
};
TEST(GordieHoweExprOps, GrandProductMultisetCheck) {
  GrandProduct g;
  auto c = compile(g.s);
  const std::string r = c->report();
  EXPECT_TRUE(has(r, "assert_zero 'perm' n=1: circuit (degree 8)")) << r;
  Assignment st;
  st.set(g.p, ints({3, 1, 4, 1, 5, 9, 2, 6}));
  auto prep = c->prepare(st);
  Assignment w;
  w.set(g.v, ints({9, 6, 5, 4, 3, 2, 1, 1}));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  // Not a permutation: 1 replaced by 7, and a repeated 9 for the two 1s.
  Assignment bad;
  bad.set(g.v, ints({9, 6, 5, 4, 3, 2, 1, 7}));
  EXPECT_TRUE(rejected(prep, bad));
  Assignment bad2;
  bad2.set(g.v, ints({9, 6, 5, 4, 3, 2, 9, 1}));
  EXPECT_TRUE(rejected(prep, bad2));
  // A degree-8 predicate is not admissible for a field batch.
  const std::string e =
      error_of([] { (void)compile(GrandProduct(Placement::kBatch).s); });
  EXPECT_NE(e.find("'perm' is pinned to a field batch, but it is of degree 8"),
            std::string::npos)
      << e;
}

// ----------------------------------------------------------- chains --

// A chain of one associative, commutative operation is one balanced tree:
// a * b * c * d has depth 2 (Logic's mul(mul(a, b), mul(c, d))), and eight
// factors depth 3. A node with another use (here a C++ variable) stays a
// leaf and is emitted once. Sums and XOR chains evaluate as before.
TEST(GordieHoweExprOps, ChainsAreBalanced) {
  const AF &f = env().af;
  std::vector<Ref<AF, Subfield<>, Committed>> v;
  for (size_t k = 0; k < 8; ++k) v.push_back({k, 1, &f, nullptr, {1}});
  const std::vector<size_t> len(8, 1);
  // The roots are built first: a chain's inner products have no other
  // holder by the time the circuit is emitted, as in a declared predicate.
  const ExprPtr<AF> p4 = (v[0] * v[1] * v[2] * v[3]).node;
  const ExprPtr<AF> p8 =
      (v[0] * v[1] * v[2] * v[3] * v[4] * v[5] * v[6] * v[7]).node;
  const Built four = build(len, [&](const LG &lc, const auto &in) {
    assert_zero_via_emitter(lc, in, {p4});
  });
  const Built direct = build(len, [&](const LG &lc, const auto &in) {
    const size_t ab = lc.mul(in[0][0], in[1][0]);
    const size_t cd = lc.mul(in[2][0], in[3][0]);
    lc.assert0(lc.mul(ab, cd));
  });
  EXPECT_EQ(four.id, direct.id);
  EXPECT_EQ(four.layers, 2u);
  const Built eight = build(len, [&](const LG &lc, const auto &in) {
    assert_zero_via_emitter(lc, in, {p8});
  });
  EXPECT_EQ(eight.layers, 3u);
  // ab is held by a variable: a leaf of the chain, emitted once and read
  // by both predicates.
  const auto ab = v[0] * v[1];
  const ExprPtr<AF> q1 = (ab * v[2] * v[3]).node, q2 = (ab - v[4]).node;
  const Built shared = build(len, [&](const LG &lc, const auto &in) {
    assert_zero_via_emitter(lc, in, {q1, q2});
  });
  const Built shared_direct = build(len, [&](const LG &lc, const auto &in) {
    const size_t m = lc.mul(in[0][0], in[1][0]);
    const size_t cd = lc.mul(in[2][0], in[3][0]);
    lc.assert0(lc.mul(m, cd));
    lc.assert0(lc.sub(m, in[4][0]));
  });
  EXPECT_EQ(shared.id, shared_direct.id);
  std::vector<Vec> vals;
  for (uint64_t k = 0; k < 8; ++k) vals.push_back(ints({k + 2}));
  EXPECT_EQ(eval((v[0] * v[1] * v[2] * v[3] * v[4]).node, vals),
            ints({2 * 3 * 4 * 5 * 6}));
  EXPECT_EQ(eval((v[0] + v[1] * v[2] + v[3] - v[4] + 7).node, vals),
            ints({2 + 12 + 5 - 6 + 7}));
  const Ref<AF, Bit, Committed> b0{0, 1, &f, nullptr, {1}};
  const Ref<AF, Bit, Committed> b1{1, 1, &f, nullptr, {1}};
  const Ref<AF, Bit, Committed> b2{2, 1, &f, nullptr, {1}};
  const std::vector<Vec> bits = {ints({1}), ints({1}), ints({0})};
  EXPECT_EQ(eval((b0 ^ b1 ^ b2 ^ b0).node, bits), ints({1}));
  EXPECT_EQ(eval((b0 | b2 | b2).node, bits), ints({1}));
  EXPECT_EQ(eval((b0 & b1 & b2).node, bits), ints({0}));
}

// ------------------------------------------------ views, broadcasting --

// The views on expressions are index maps: no gate, the operand's wires.
// rotate is out[i] = x[i - k]; slice, at, x[i], reshape, reindex and concat
// read the coordinates they name; sum(axis), any(axis) and all(axis)
// reduce one axis; + and * broadcast a missing leading axis.
TEST(GordieHoweExprOps, ViewsAndAxes) {
  const AF &f = env().af;
  const Ref<AF, Subfield<>, Committed> x{0, 6, &f, nullptr, {2, 3}};
  const Ref<AF, Subfield<>, Committed> y{1, 3, &f, nullptr, {3}};
  const Ref<AF, Bit, Committed> b{2, 6, &f, nullptr, {2, 3}};
  const Vec xv = ints({1, 2, 3, 4, 5, 6}), yv = ints({10, 20, 30});
  const Vec bv = ints({1, 0, 1, 1, 1, 1});
  const std::vector<Vec> v = {xv, yv, bv};
  const auto xe = as_expr(x);
  auto at = [&](const auto &e) { return eval(e.node, v); };
  EXPECT_EQ(at(xe.rotate(1, 1)), ints({3, 1, 2, 6, 4, 5}));
  EXPECT_EQ(at(xe.rotate(-1, 1)), ints({2, 3, 1, 5, 6, 4}));
  EXPECT_EQ(at(xe.rotate(1, 0)), ints({4, 5, 6, 1, 2, 3}));
  EXPECT_EQ(at(xe.slice(1, 3, 1)), ints({2, 3, 5, 6}));
  EXPECT_EQ(at(xe[1]), ints({4, 5, 6}));
  EXPECT_EQ(at(xe.at(1, 2)), ints({3, 6}));
  EXPECT_EQ(at(xe.reindex({5, 0, 0})), ints({6, 1, 1}));
  const std::vector<size_t> perm = {5, 0, 0};
  EXPECT_EQ(at(xe[perm]), ints({6, 1, 1}));
  EXPECT_EQ(at(xe[std::array<size_t, 2>{4, 2}]), ints({5, 3}));
  EXPECT_EQ(at(xe.at(1)), ints({4, 5, 6}));
  EXPECT_EQ(at(xe.reindex({2, 0}, 1)), ints({3, 1, 6, 4}));
  EXPECT_EQ(at(xe.reshape(Shape{3, 2})[2]), ints({5, 6}));
  EXPECT_EQ(at(xe.flat()), xv);
  EXPECT_EQ(at(xe[0].concat(y)), ints({1, 2, 3, 10, 20, 30}));
  EXPECT_EQ(at(xe.concat(y.reshape(Shape{1, 3}))[2]), yv);
  EXPECT_EQ(at(xe.concat(xe, 1)[0]), ints({1, 2, 3, 1, 2, 3}));
  EXPECT_EQ(xe.concat(xe, 1).dims(), (std::vector<size_t>{2, 6}));
  // Sums along an axis.
  EXPECT_EQ(at(x.sum(0)), ints({5, 7, 9}));
  EXPECT_EQ(at(x.sum(1)), ints({6, 15}));
  EXPECT_EQ(at(x.sum()), ints({21}));
  // OR and AND along an axis.
  EXPECT_EQ(at(b.all(1)), ints({0, 1}));
  EXPECT_EQ(at(b.all(0)), ints({1, 0, 1}));
  EXPECT_EQ(at((~b).any(0)), ints({0, 1, 0}));
  // Broadcasting: y [3] over x [2][3], in + and *.
  EXPECT_EQ(at(xe + y), ints({11, 22, 33, 14, 25, 36}));
  EXPECT_EQ(at(x * y), ints({10, 40, 90, 40, 100, 180}));
  EXPECT_EQ((x * y).dims(), (std::vector<size_t>{2, 3}));
  // A view emits no gate: the circuit of (x x).rotate(1, 1) - x equals the
  // one with the rotated wires read directly.
  const Built via = build({6, 3, 6}, [&](const LG &lc, const auto &in) {
    assert_zero_via_emitter(lc, in, {((x * x).rotate(1, 1) - x).node});
  });
  const Built direct = build({6, 3, 6}, [&](const LG &lc, const auto &in) {
    const size_t src[6] = {2, 0, 1, 5, 3, 4};
    std::vector<size_t> sq(6), d(6);
    for (size_t i = 0; i < 6; ++i) sq[i] = lc.mul(in[0][i], in[0][i]);
    for (size_t i = 0; i < 6; ++i) d[i] = lc.sub(sq[src[i]], in[0][i]);
    for (size_t i = 0; i < 6; ++i) lc.assert0(d[i]);
  });
  EXPECT_EQ(via.id, direct.id);
}

// The errors: shapes that do not broadcast, a bad axis, words of other
// shapes, a constant wider than the words, an index past the coordinates,
// parts that do not concatenate.
TEST(GordieHoweExprOps, ShapeErrors) {
  const AF &f = env().af;
  const Ref<AF, Subfield<>, Committed> x{0, 6, &f, nullptr, {2, 3}};
  const Ref<AF, Subfield<>, Committed> y2{1, 2, &f, nullptr, {2}};
  const Ref<AF, Bit, Committed> a{2, 16, &f, nullptr, {2, 8}};
  const Ref<AF, Bit, Committed> b{3, 8, &f, nullptr, {8}};
  const auto xe = as_expr(x);
  EXPECT_NE(error_of([&] { (void)(xe + y2); }).find("do not broadcast"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)(x * y2); }).find("do not broadcast"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)xe.rotate(1, 2); }).find("rotate: no axis 2"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)x.sum(2); }).find("sum: no axis 2"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)(a.from_bits() < 300); }).find("more than 8 bits"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)xe.reindex({6}); }).find("index 6 past"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)xe.concat(y2, 0); }).find("ranks differ"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)xe.reshape(Shape{4}); }).find("reshape"),
            std::string::npos);
}

// ------------------------------------------------- lifted constants --

// Plain C++ integers and arrays lift to constants of the other operand's
// field in +, -, *, the gates, the comparisons and mux, broadcast like any
// operand; values outside the field's integers, and non-bits in a gate,
// are refused.
TEST(GordieHoweExprOps, LiftedConstants) {
  const AF &f = env().af;
  const Ref<AF, Subfield<>, Committed> x{0, 6, &f, nullptr, {2, 3}};
  const Ref<AF, Bit, Committed> b{1, 6, &f, nullptr, {2, 3}};
  const Ref<AF, Bit, Committed> c{2, 1, &f, nullptr, {1}};
  const std::vector<Vec> v = {ints({1, 2, 3, 4, 5, 6}),
                              ints({1, 0, 1, 1, 1, 0}), ints({1})};
  auto at = [&](const auto &e) { return eval(e.node, v); };
  const std::vector<uint64_t> k3 = {10, 20, 30};
  const std::array<int, 3> m3 = {1, -1, 2};
  EXPECT_EQ(at(x + k3), ints({11, 22, 33, 14, 25, 36}));
  EXPECT_EQ(at(k3 - x), ints({9, 18, 27, 6, 15, 24}));
  Vec neg = ints({1, 0, 6, 4, 0, 12});
  f.sub(neg[1], f.of_scalar(2));
  f.sub(neg[4], f.of_scalar(5));
  EXPECT_EQ(at(x * m3), neg);
  EXPECT_EQ(at(b ^ std::vector<int>{1, 1, 0}), ints({0, 1, 1, 0, 0, 0}));
  EXPECT_EQ(at(b & 1), ints({1, 0, 1, 1, 1, 0}));
  EXPECT_EQ(at(1 | b), ints({1, 1, 1, 1, 1, 1}));
  EXPECT_EQ(at(b.from_bits() < std::vector<uint64_t>{6, 3}), ints({1, 0}));
  EXPECT_EQ(at(b.from_bits() == std::vector<uint64_t>{5, 3}), ints({1, 1}));
  EXPECT_EQ(at(c.mux(k3, 7)), ints({10, 20, 30}));
  // Out of range: 2^64 - 1 exceeds Goldilocks' p; 2 is no bit.
  EXPECT_NE(error_of([&] {
              (void)(x + std::vector<uint64_t>{UINT64_MAX, 0, 0});
            }).find("lies outside the field's integers"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)(b ^ std::vector<int>{2, 0, 0}); })
                .find("the constant 2 is not a bit"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)(b.from_bits() < std::vector<uint64_t>{8, 0}); })
                .find("has more than 3 bits"),
            std::string::npos);
}

// A lifted constant is part of the relation: its values enter the
// predicate's description, so two systems that differ only in one have
// different digests. A constant standing alone is the domain's
// (D.constant).
TEST(GordieHoweExprOps, LiftedConstantsEnterTheDigest) {
  // Mode 0: in a circuit predicate; 1: standing alone; 2: an affine
  // product (ConstDiagonal's parameters).
  auto digest = [](uint64_t k, int mode) {
    Sys s("gh-lifted-constant");
    auto &A = s.domain(env().profile(), "A");
    auto x = A.priv(Subfield{}, "x", 3);
    auto y = A.priv(Subfield{}, "y", 3);
    if (mode == 1)
      assert_equal(y, A.constant(std::vector<uint64_t>{1, 2, k}), "y");
    else if (mode == 2)
      assert_equal(x * std::array<uint64_t, 3>{1, 2, k}, y, "y");
    else
      assert_equal(x * x + std::vector<uint64_t>{1, 2, k}, y, "y");
    assert_zero(x * y - y, "x");
    return compile(s)->digest();
  };
  for (int mode = 0; mode < 3; ++mode) {
    EXPECT_EQ(digest(3, mode), digest(3, mode)) << mode;
    EXPECT_NE(digest(3, mode), digest(4, mode)) << mode;
  }
}

// --------------------------------------------- NumPy semantics, typing --

// Broadcasting stretches length-1 axes as well as missing ones (NumPy's
// rule), in expressions and in affine expressions; reindex without an axis
// reads flat coordinates.
TEST(GordieHoweExprOps, BroadcastingStretchesUnitAxes) {
  const AF &f = env().af;
  const Ref<AF, Subfield<>, Committed> x{0, 6, &f, nullptr, {2, 3}};
  const Ref<AF, Subfield<>, Committed> col{1, 2, &f, nullptr, {2, 1}};
  const Ref<AF, Subfield<>, Committed> row{2, 3, &f, nullptr, {1, 3}};
  const std::vector<Vec> v = {ints({1, 2, 3, 4, 5, 6}), ints({10, 100}),
                              ints({1, 2, 3})};
  auto at = [&](const auto &e) { return eval(e.node, v); };
  EXPECT_EQ(at(x * col), ints({10, 20, 30, 400, 500, 600}));
  EXPECT_EQ((col * row).dims(), (std::vector<size_t>{2, 3}));
  EXPECT_EQ(at(col * row), ints({10, 20, 30, 100, 200, 300}));
  // Affine: x + col is a Lin through Gather.
  const auto lin = x + col;
  static_assert(std::is_same_v<std::decay_t<decltype(lin)>, Lin<AF>>);
  EXPECT_EQ(lin.dims(), (std::vector<size_t>{2, 3}));
  EXPECT_EQ(at(as_expr(lin)), ints({11, 12, 13, 104, 105, 106}));
  EXPECT_EQ(at(as_expr(x).reindex({5, 1})), ints({6, 2}));
  EXPECT_NE(error_of([&] { (void)(x * row.reshape(Shape{3, 1})); })
                .find("do not broadcast"),
            std::string::npos);
}

// In characteristic 2, + is XOR: a sum or difference of Bits, and a sum of
// Bit coordinates, is a Bit expression. In odd characteristic it is Field.
TEST(GordieHoweExprOps, CharacteristicTwoSumsAreBits) {
  using MSet = FieldSet<SHA384, MF>;
  const MF &mf = env().mf;
  const Ref<MF, Bit, Committed> a{0, 3, &mf, nullptr, {3}};
  const Ref<MF, Bit, Committed> b{1, 3, &mf, nullptr, {3}};
  const auto s = as_expr(a) + b;
  static_assert(std::is_same_v<decltype(s)::type_tag, Bit>);
  static_assert(std::is_same_v<decltype(as_expr(a) - b)::type_tag, Bit>);
  static_assert(std::is_same_v<decltype(a.sum())::type_tag, Bit>);
  static_assert(std::is_same_v<decltype((~a).sum(0))::type_tag, Bit>);
  const Ref<AF, Bit, Committed> c{0, 3, &env().af, nullptr, {3}};
  static_assert(std::is_same_v<decltype(as_expr(c) + c)::type_tag, Field>);
  static_assert(std::is_same_v<decltype(c.sum())::type_tag, Field>);
  ValueStore<MSet> vs(2);
  vs.v[0] = MSet::template wrap<MF>({mf.one(), mf.zero(), mf.one()});
  vs.v[1] = MSet::template wrap<MF>({mf.one(), mf.one(), mf.zero()});
  EXPECT_EQ(eval_expr(s.node, vs),
            (std::vector<MElt>{mf.zero(), mf.one(), mf.one()}));
  EXPECT_EQ(eval_expr(a.sum().node, vs), (std::vector<MElt>{mf.zero()}));
  EXPECT_TRUE(s.node->bit);
}

// A handle converts to an expression of its type: Expr<F, Bit> e = handle,
// and a function taking Expr<F, Bit> takes a Bit handle.
TEST(GordieHoweExprOps, HandlesConvertToExpressions) {
  const AF &f = env().af;
  const Ref<AF, Bit, Committed> b{0, 2, &f, nullptr, {2}};
  static_assert(std::is_convertible_v<Ref<AF, Bit, Committed>, Expr<AF, Bit>>);
  static_assert(std::is_convertible_v<Ref<MF, Bit, Public>, Expr<MF, Bit>>);
  const Expr<AF, Bit> e = b;
  auto negate = [](const Expr<AF, Bit> &x) { return ~x; };
  EXPECT_EQ(eval(negate(b).node, {ints({1, 0})}), ints({0, 1}));
  EXPECT_EQ(eval(e.node, {ints({1, 0})}), ints({1, 0}));
}

// A linear operator applies to an affine expression with a constant term:
// the constant goes through the operator, per statement when the operator
// reads public values (Diagonal(k)), at once otherwise (Sum). The system
// proves and rejects a wrong value.
TEST(GordieHoweExprOps, OperatorsCarryConstants) {
  const AF &f = env().af;
  Sys s("gh-operator-constants");
  auto &A = s.domain(env().profile(), "A");
  auto x = A.priv(Subfield{}, "x", 4);
  auto y = A.priv(Subfield{}, "y", 4);
  auto t = A.priv(Subfield{}, "t", 1);
  auto z = A.priv(Subfield{}, "z", 4);
  auto k = A.pub(Field{}, "k", 4);
  assert_equal(x * x, z, "square");
  assert_equal(Diagonal(k)(x - 3), y, "diag");
  assert_equal(Sum(f, 4)(x + 1), t, "sum");
  auto c = compile(s);
  const std::string r = c->report();
  EXPECT_TRUE(has(r, "assert_zero 'diag' n=4: affine rows")) << r;
  EXPECT_TRUE(has(r, "assert_zero 'sum' n=1: affine rows")) << r;
  Assignment st;
  st.set(k, ints({2, 3, 5, 7}));
  auto prep = c->prepare(st);
  // y = k (x - 3), t = sum (x + 1).
  Assignment w;
  w.set(x, ints({4, 5, 6, 7})).set(y, ints({2, 6, 15, 28}));
  w.set(t, ints({26})).set(z, ints({16, 25, 36, 49}));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  Assignment bad;
  bad.set(x, ints({4, 5, 6, 7})).set(y, ints({2, 6, 15, 29}));
  bad.set(t, ints({26})).set(z, ints({16, 25, 36, 49}));
  EXPECT_TRUE(rejected(prep, bad));
  Assignment bad2;
  bad2.set(x, ints({4, 5, 6, 7})).set(y, ints({2, 6, 15, 28}));
  bad2.set(t, ints({22})).set(z, ints({16, 25, 36, 49}));
  EXPECT_TRUE(rejected(prep, bad2));
}

// ------------------------------------------- placement in a system --

// Each form in one system, placed and proved: sums along an axis and a
// broadcast sum are affine rows; a rotated product, a product along an
// axis, a concatenation of a product and a value, a gate and a
// comparison are circuit constraints; assert_equal returns a pinnable
// predicate. Each placement rejects a wrong value.
struct FormsSystem {
  Sys s{"gh-expr-forms"};
  Ref<AF, Subfield<>, Committed> x, y, z, w, q, r, pr, cc, rt;
  Ref<AF, Bit, Committed> a, b, c;
  FormsSystem() {
    auto &A = s.domain(env().profile(), "A");
    x = A.priv(Subfield{}, "x", Shape{2, 3});
    y = A.priv(Subfield{}, "y", 3);
    z = A.priv(Subfield{}, "z", 3);
    w = A.priv(Subfield{}, "w", Shape{2, 3});
    q = A.priv(Subfield{}, "q", 2);
    r = A.priv(Subfield{}, "r", Shape{2, 3});
    pr = A.priv(Subfield{}, "pr", 3);
    cc = A.priv(Subfield{}, "cc", 6);
    rt = A.priv(Subfield{}, "rt", Shape{2, 2});
    a = A.priv(Bit{}, "a", Shape{2, 4});
    b = A.priv(Bit{}, "b", Shape{2, 4});
    c = A.priv(Bit{}, "c", Shape{2, 4});
    assert_equal(x.sum(0), z, "sum0");
    assert_equal(x.sum(1), q, "sum1");
    assert_equal(x.rotate(1, 1).reindex({2, 0}, 1), rt, "reindex");
    assert_equal(x + y, w, "bcast");
    assert_equal((x * x).rotate(1, 1), r, "rotate");
    assert_equal(x.prod(0), pr, "prod0");
    assert_equal((x[0] * y).concat(y), cc, "concat");
    assert_equal(a & b, c, "and").pin(Placement::kCircuit);
    assert_true((c.from_bits() <= a.from_bits()) &
                      (c.from_bits() <= b.from_bits()),
                  "le");
    assert_true(((a & b).from_bits() == c.from_bits()).all(0), "eq");
  }
  Assignment witness(const std::string &wrong = "") const {
    // x = [[1 2 3] [4 5 6]], y = [10 20 30]; a = [5 9], b = [7 12] as
    // 4-bit words, c = a & b = [5 8].
    std::map<std::string, Vec> val = {
        {"x", ints({1, 2, 3, 4, 5, 6})},
        {"y", ints({10, 20, 30})},
        {"z", ints({5, 7, 9})},
        {"q", ints({6, 15})},
        {"w", ints({11, 22, 33, 14, 25, 36})},
        {"r", ints({9, 1, 4, 36, 16, 25})},
        {"pr", ints({4, 10, 18})},
        {"cc", ints({10, 40, 90, 10, 20, 30})},
        {"rt", ints({2, 3, 5, 6})},
        {"a", ints({1, 0, 1, 0, 1, 0, 0, 1})},
        {"b", ints({1, 1, 1, 0, 0, 0, 1, 1})},
        {"c", ints({1, 0, 1, 0, 0, 0, 0, 1})}};
    if (!wrong.empty()) {
      auto &e = val.at(wrong);
      if (wrong == "c") {
        e[0] = env().af.zero();  // 4
      } else {
        env().af.add(e[1], env().af.one());
      }
    }
    Assignment wa;
    wa.set(x, val["x"]).set(y, val["y"]).set(z, val["z"]).set(q, val["q"]);
    wa.set(w, val["w"]).set(r, val["r"]).set(pr, val["pr"]).set(cc, val["cc"]);
    wa.set(rt, val["rt"]);
    wa.set(a, val["a"]).set(b, val["b"]).set(c, val["c"]);
    return wa;
  }
};
TEST(GordieHoweExprOps, FormsPlaceAndProve) {
  FormsSystem t;
  auto c = compile(t.s);
  const std::string r = c->report();
  for (const char *want : {
           "assert_zero 'sum0' n=3: affine rows (affine)",
           "assert_zero 'sum1' n=2: affine rows (affine)",
           "assert_zero 'reindex' n=4: affine rows (affine)",
           "assert_zero 'bcast' n=6: affine rows (affine)",
           // rotate's square reads x once (2 operands), concat's form has
           // 3: two groups.
           "assert_zero 'rotate' n=6: circuit",
           "assert_zero 'concat' n=6: circuit",
           "assert_zero 'prod0' n=3: circuit",
           "assert_zero 'and' n=8: circuit (pinned)",
           "assert_true 'le' n=2: circuit (Logic gadgets)",
           "assert_true 'eq' n=1: circuit (Logic gadgets)",
       })
    EXPECT_TRUE(has(r, want)) << want << "\n" << r;
  auto prep = c->prepare(Assignment());
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(t.witness(), rng)));
  for (const char *wrong : {"z", "q", "w", "r", "pr", "cc", "rt", "c"})
    EXPECT_TRUE(rejected(prep, t.witness(wrong))) << wrong;
}

// The predicates are free functions: each finds its system through the
// handles it reads, so two systems over one field object keep their own
// predicates; sc.name(nm) names a predicate in the scope sc and sc.name()
// gives it sc's default name; a predicate on constants alone is a
// CompileError; and a predicate the compiler lowers by itself refuses a
// pin.
TEST(GordieHoweExprOps, FreePredicatesFindTheirSystem) {
  Sys s1{"gh-free-1"}, s2{"gh-free-2"};
  auto &A1 = s1.domain(env().profile(), "A");
  auto &A2 = s2.domain(env().profile(), "A");
  const auto x1 = A1.priv(Subfield{}, "x", 3);
  const auto x2 = A2.priv(Subfield{}, "x", 3);
  const auto sc = s2.scope("g");
  assert_zero(x1 * x1 - x1);
  assert_zero(x2 * x2 - x2, sc.name("named"));
  assert_zero(x2 * x2 - x2, sc.name());
  assert_mod(x2, x2, 7681, sc.name("m"));
  EXPECT_EQ(A1.predicates().size(), 1u);
  ASSERT_EQ(A2.predicates().size(), 2u);
  EXPECT_EQ(A1.predicates()[0].name, "assert_zero.0");
  EXPECT_EQ(A2.predicates()[0].name, "g.named");
  EXPECT_EQ(A2.predicates()[1].name, "g.assert_zero.1");
  EXPECT_THROW(assert_zero(A1.constant(std::vector<int>{1, 2})), CompileError);
  EXPECT_THROW(assert_mod(x2, x2, 7681).pin(Placement::kCircuit),
               CompileError);
}

// ------------------------------------------ uncommitted expressions --

// auto y = x * x names one node: a circuit emits it once however many
// predicates read it (the emitter's wires for y are the ones both
// predicates read), and nothing commits it.
TEST(GordieHoweExprOps, BoundExpressionIsEmittedOnce) {
  const AF &f = env().af;
  const Ref<AF, Subfield<>, Committed> x{0, 4, &f, nullptr, {4}};
  const Ref<AF, Subfield<>, Committed> z{1, 4, &f, nullptr, {4}};
  const auto y = x * x;
  (void)build({4, 4}, [&](const LG &lc, const auto &in) {
    ExprEmitter<AF, LG> em(lc, [&](const Term<AF> &t) { return in[t.node]; });
    const std::vector<BitW> *first = &em(y.node);
    em.assert_zero((y * x - z).node);
    em.assert_zero((y - z).node);
    EXPECT_EQ(&em(y.node), first);
    EXPECT_EQ(em(y.node).size(), 4u);
  });

  // In a system: y is read by two circuit predicates, both pinned, and only
  // x, z and c3 are committed.
  Sys s("gh-bound-expression");
  auto &A = s.domain(env().profile(), "A");
  auto xs = A.priv(Subfield{}, "x", 4);
  auto zs = A.priv(Subfield{}, "z", 4);
  auto c3 = A.priv(Subfield{}, "c3", 4);
  const auto ys = xs * xs;
  assert_equal(ys * xs, c3, "cube").pin(Placement::kCircuit);
  assert_equal(ys, zs, "square").pin(Placement::kCircuit);
  auto c = compile(s);
  const std::string r = c->report();
  EXPECT_TRUE(has(r, "assert_zero 'cube' n=4: circuit (pinned)")) << r;
  EXPECT_TRUE(has(r, "assert_zero 'square' n=4: circuit (pinned)")) << r;
  auto prep = c->prepare(Assignment());
  Assignment w;
  w.set(xs, ints({1, 2, 3, 4})).set(zs, ints({1, 4, 9, 16}));
  w.set(c3, ints({1, 8, 27, 64}));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  Assignment bad;
  bad.set(xs, ints({1, 2, 3, 4})).set(zs, ints({1, 4, 9, 17}));
  bad.set(c3, ints({1, 8, 27, 64}));
  EXPECT_TRUE(rejected(prep, bad));
}

// A staged transform expands in a circuit-placed predicate by its
// butterflies; an operator without a circuit expansion (public
// dependencies) is refused there, by name.
TEST(GordieHoweExprOps, StagedOperatorInCircuit) {
  const AF &f = env().af;
  constexpr size_t n = 8;
  const auto ntt = ops::Ntt(f, n, *ops::FieldNtt<AF>::scheme_psi(f, n),
                            ops::Stages::every(2));
  Sys s("gh-staged-circuit");
  auto &A = s.domain(env().profile(), "A");
  auto x = A.priv(Subfield{}, "x", n);
  auto xh = A.priv(Subfield{}, "xh", n);
  auto sq = A.priv(Subfield{}, "sq", n);
  assert_equal(ntt(x), xh, "ntt").pin(Placement::kCircuit);
  assert_equal(ntt(x) * xh, sq, "ntt-square");
  auto c = compile(s);
  const std::string r = c->report();
  EXPECT_TRUE(has(r, "assert_zero 'ntt' n=8: circuit (pinned)")) << r;
  EXPECT_TRUE(has(r, "assert_zero 'ntt-square' n=8: circuit")) << r;
  const Vec xv = ints({1, 2, 3, 4, 5, 6, 7, 8});
  Vec hv(n), sv(n);
  ops::StagedNttOperator<AF>(ntt.spec->staged).apply(xv.data(), hv.data());
  for (size_t i = 0; i < n; ++i) sv[i] = f.mulf(hv[i], hv[i]);
  auto prep = c->prepare(Assignment());
  Assignment w;
  w.set(x, xv).set(xh, hv).set(sq, sv);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  Vec hb = hv;
  f.add(hb[3], f.one());
  Assignment bad;
  bad.set(x, xv).set(xh, hb).set(sq, sv);
  EXPECT_TRUE(rejected(prep, bad));
  // Diagonal reads a public value: no circuit expansion.
  const std::string e = error_of([] {
    Sys t("gh-structured-circuit");
    auto &B = t.domain(env().profile(), "B");
    auto u = B.priv(Subfield{}, "u", 4);
    auto k = B.pub(Field{}, "k", 4);
    assert_equal(Diagonal(k)(u) * u, u, "d");
    (void)compile(t);
  });
  EXPECT_NE(e.find("reads the structured operator 'diagonal'"),
            std::string::npos)
      << e;
}

// ------------------------------------------ handles as expressions --

// A handle is an Expr of its type, so a function template taking
// Expr<F, Bit> (by value or by reference) takes a Bit handle with F
// deduced, and its leaf follows the handle's shape (reshape).
template <class F>
Expr<F, Bit> flip(Expr<F, Bit> a) {
  return ~a;
}
template <class F>
std::vector<size_t> dims_of(const Expr<F, Bit> &a) {
  return a.dims();
}
TEST(GordieHoweExprOps, HandlesDeduceAsExpressions) {
  const AF &f = env().af;
  const Ref<AF, Bit, Committed> b{0, 4, &f, nullptr, {4}};
  EXPECT_EQ(eval(flip(b).node, {ints({1, 0, 0, 1})}), ints({0, 1, 1, 0}));
  EXPECT_EQ(dims_of(b), (std::vector<size_t>{4}));
  EXPECT_EQ(dims_of(b.reshape(Shape{2, 2})), (std::vector<size_t>{2, 2}));
  const Ref<MF, Bit, Public> m{0, 2, &env().mf, nullptr, {2}};
  static_assert(std::is_same_v<decltype(flip(m)), Expr<MF, Bit>>);
  // An Expr variable takes a handle, and a handle assigned to it.
  Expr<AF, Bit> x = b;
  x = x & b;
  EXPECT_EQ(eval(x.node, {ints({1, 0, 1, 1})}), ints({1, 0, 1, 1}));
}

// ---------------------------------------- expressions in depends_on --

// depends_on takes expressions: a priv value computed from x x + k (the
// vector and the elementwise closure forms), a pub value from k + 1. The
// value depends on the expression's leaves (its phase is theirs), and the
// closure receives the expression's values. A pub value whose expression
// reads a committed value is refused, naming it.
TEST(GordieHoweExprOps, DependsOnExpressions) {
  Sys s("gh-depends-on-expression");
  auto &A = s.domain(env().profile(), "A");
  auto x = A.priv(Subfield{}, "x", 4);
  auto k = A.pub(Subfield{}, "k", 4);
  auto y = A.priv(Subfield{}, "y", 4, depends_on(x * x + k),
                  [](const Tensor<AElt> &v) { return v.vec(); });
  auto z = A.priv(Field{}, "z", 4, depends_on(x * 2, k),
                  [](const AElt &a, const AElt &b) {
                    return env().af.addf(a, b);
                  });
  auto p = A.pub(Subfield{}, "p", 4, depends_on(k + 1), Computes{"copy"},
                 [](const std::vector<AElt> &v) { return v; });
  // p = k + 1 holds when y = x x + k does.
  assert_equal(y + 1, x * x + p, "y");
  assert_equal(z, 2 * x + k, "z");
  auto c = compile(s);
  Assignment st;
  st.set(k, ints({1, 2, 3, 4}));
  auto prep = c->prepare(st);
  Assignment w;
  w.set(x, ints({5, 6, 7, 8}));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  const std::string e = error_of([] {
    Sys t("gh-depends-on-committed");
    auto &B = t.domain(env().profile(), "B");
    auto u = B.priv(Subfield{}, "u", 2);
    (void)B.pub(Subfield{}, "q", 2, depends_on(u + 1), Computes{"copy"},
                [](const std::vector<AElt> &v) { return v; });
  });
  EXPECT_NE(e.find("which is not a public value"), std::string::npos) << e;
}

// ------------------------------------- C++ arrays: constants, indices --

// A C array or nested std::array of any rank lifts with its own shape
// (kRoundConstant[i] of shape [5][5][64] in Keccak), and an index array
// of any rank and integer type gives a view of its shape, on expressions,
// affine expressions and handles.
TEST(GordieHoweExprOps, ArraysOfAnyRank) {
  const AF &f = env().af;
  const Ref<AF, Subfield<>, Committed> x{0, 6, &f, nullptr, {2, 3}};
  const std::vector<Vec> v = {ints({1, 2, 3, 4, 5, 6})};
  auto at = [&](const auto &e) { return eval(e.node, v); };
  constexpr int kC[2][3] = {{10, 20, 30}, {40, 50, 60}};
  EXPECT_EQ((x + kC).dims(), (std::vector<size_t>{2, 3}));
  EXPECT_EQ(at(x + kC), ints({11, 22, 33, 44, 55, 66}));
  // kC[1] is rank 1, broadcast over x's leading axis.
  EXPECT_EQ(at(x * kC[1]), ints({40, 100, 180, 160, 250, 360}));
  const std::array<std::array<uint8_t, 3>, 2> nested = {{{1, 1, 1}, {2, 2, 2}}};
  EXPECT_EQ(at(x - nested), ints({0, 1, 2, 2, 3, 4}));
  // Index arrays: entry j is flat x[idx[j]], shaped like idx.
  constexpr uint16_t kIdx[2][2] = {{5, 0}, {1, 4}};
  const auto xe = as_expr(x);
  EXPECT_EQ(xe[kIdx].dims(), (std::vector<size_t>{2, 2}));
  EXPECT_EQ(at(xe[kIdx]), ints({6, 1, 2, 5}));
  EXPECT_EQ(at(xe.reindex(std::array<uint32_t, 3>{2, 2, 0})), ints({3, 3, 1}));
  EXPECT_EQ(at(xe.reindex(std::vector<int>{2, 0}, 1)), ints({3, 1, 6, 4}));
  EXPECT_EQ(at((x + x)[kIdx]), ints({12, 2, 4, 10}));
  EXPECT_NE(error_of([&] { (void)xe.reindex(std::vector<int>{-1}); })
                .find("negative index -1"),
            std::string::npos);
  EXPECT_NE(error_of([&] { (void)xe.reindex(kIdx, 1); }).find("rank 2, not 1"),
            std::string::npos);
  // On handles, in a system: views of the index array's shape.
  Sys s("gh-index-arrays");
  auto &A = s.domain(env().profile(), "A");
  auto xs = A.priv(Subfield{}, "x", Shape{2, 3});
  auto ws = A.priv(Subfield{}, "w", Shape{2, 2});
  auto rs = A.priv(Subfield{}, "r", Shape{2, 2});
  EXPECT_EQ(xs[kIdx].dims(), (std::vector<size_t>{2, 2}));
  EXPECT_EQ(A.constant(kC).dims(), (std::vector<size_t>{2, 3}));
  assert_equal(xs[kIdx], ws, "w");
  assert_equal(xs.reindex(std::array<uint8_t, 2>{2, 0}, 1), rs, "r");
  auto cs = A.priv(Subfield{}, "c", Shape{2, 3});
  assert_equal(xs * kC, cs, "c");
  // The domain's circuit: one product.
  auto sq = A.priv(Subfield{}, "sq", Shape{2, 2});
  assert_equal(xs[kIdx] * ws, sq, "sq");
  auto c = compile(s);
  // A constant array times a value is affine (ConstDiagonal).
  EXPECT_TRUE(has(c->report(), "assert_zero 'c' n=6: affine rows")) << c->report();
  auto prep = c->prepare(Assignment());
  Assignment w;
  w.set(xs, ints({1, 2, 3, 4, 5, 6})).set(ws, ints({6, 1, 2, 5}));
  w.set(rs, ints({3, 1, 6, 4})).set(cs, ints({10, 40, 90, 160, 250, 360}));
  w.set(sq, ints({36, 1, 4, 25}));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  Assignment bad = w;
  bad.set(ws, ints({6, 1, 2, 6}));
  EXPECT_TRUE(rejected(prep, bad));
}

// In characteristic 2 an integer constant is 0 or 1: a Bit plus a bit
// constant (a scalar or an array) is their XOR, a Bit expression. In odd
// characteristic the sum is Field.
TEST(GordieHoweExprOps, CharacteristicTwoConstantsAreBits) {
  using MSet = FieldSet<SHA384, MF>;
  const MF &mf = env().mf;
  const Ref<MF, Bit, Committed> a{0, 3, &mf, nullptr, {3}};
  static_assert(std::is_same_v<decltype(a + 1)::type_tag, Bit>);
  static_assert(std::is_same_v<decltype(1 - a)::type_tag, Bit>);
  static_assert(
      std::is_same_v<decltype(a + std::array<int, 3>{})::type_tag, Bit>);
  static_assert(std::is_same_v<decltype(a * std::vector<int>{})::type_tag, Bit>);
  const Ref<AF, Bit, Committed> b{0, 3, &env().af, nullptr, {3}};
  static_assert(std::is_same_v<decltype(b + 1)::type_tag, Field>);
  ValueStore<MSet> vs(1);
  vs.v[0] = MSet::template wrap<MF>({mf.one(), mf.zero(), mf.one()});
  const auto s = a + std::array<int, 3>{1, 1, 0};
  EXPECT_TRUE(s.node->bit);
  EXPECT_EQ(eval_expr(s.node, vs),
            (std::vector<MElt>{mf.zero(), mf.one(), mf.one()}));
  EXPECT_EQ(eval_expr((a + 1).node, vs),
            (std::vector<MElt>{mf.zero(), mf.one(), mf.zero()}));
  EXPECT_NE(error_of([&] { (void)(a + 2); }).find("lies outside"),
            std::string::npos);
}

// from_digits takes a field element base as well as an integer: with the
// element of the integer, the two agree, on handles (affine, FromDigits)
// and on expressions; in characteristic 2 the base x packs bits as the
// polynomial sum_l x^l b_l.
TEST(GordieHoweExprOps, FromDigitsInAnElementBase) {
  const AF &f = env().af;
  const Ref<AF, Subfield<>, Committed> d{0, 6, &f, nullptr, {2, 3}};
  const std::vector<Vec> v = {ints({1, 2, 3, 4, 5, 6})};
  const AElt ten = f.of_scalar(10);
  EXPECT_EQ(eval(as_expr(d.from_digits(ten)).node, v), ints({321, 654}));
  EXPECT_EQ(eval(as_expr(d.from_digits(10)).node, v), ints({321, 654}));
  EXPECT_EQ(eval((d * d).from_digits(ten).node, v), ints({941, 3866}));
  using MSet = FieldSet<SHA384, MF>;
  const MF &mf = env().mf;
  const Ref<MF, Bit, Committed> bits{0, 8, &mf, nullptr, {8}};
  ValueStore<MSet> vs(1);
  std::vector<MElt> bv(8, mf.zero());
  bv[1] = mf.one();
  bv[3] = mf.one();
  vs.v[0] = MSet::template wrap<MF>(bv);
  const MElt x = mf.of_scalar(2);
  // x + x^3.
  const MElt want = mf.addf(x, mf.mulf(x, mf.mulf(x, x)));
  EXPECT_EQ(eval_expr(as_expr(bits.from_digits(x)).node, vs),
            (std::vector<MElt>{want}));
}

}  // namespace
}  // namespace proofs::gordiehowe
