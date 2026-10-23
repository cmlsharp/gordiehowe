// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_test binary): the expression
// builders, constant folding, placement and materialize.

#include "gordiehowe/tests/gordiehowe_test.h"

namespace proofs::gordiehowe {
namespace {

// --------------------------------------------------------- expressions --

// The builders are Logic's own gadgets: the circuit that the comparisons
// (< <= == !=), any, all, mux and the gates build from expressions has the
// id of the circuit Logic builds directly (lt_reduce, eq_reduce, the
// balanced OR and AND trees), in both
// characteristics. The host evaluation of each builder matches integer
// arithmetic on random words.
template <class G>
void builders_match_logic(const G &g) {
  using CB = CompilerBackend<G>;
  using L = Logic<G, CB>;
  using BitW = typename L::BitW;
  constexpr size_t W = 6;
  constexpr uint64_t K = 37;
  // Leaves: a, b (words of W bits), c (a bit), x, y (field values), read
  // by node id.
  const Ref<G, Bit, Committed> a{0, W, &g, nullptr, {W}};
  const Ref<G, Bit, Committed> b{1, W, &g, nullptr, {W}};
  const Ref<G, Bit, Committed> c{2, 1, &g, nullptr, {1}};
  const Ref<G, Field, Committed> x{3, 1, &g, nullptr, {1}};
  const Ref<G, Field, Committed> y{4, 1, &g, nullptr, {1}};
  const size_t len[5] = {W, W, 1, 1, 1};
  // a and b as integers of W bits, which the comparisons read.
  const auto aw = a.from_bits(), bw = b.from_bits();
  // The expressions, in output order.
  std::vector<ExprPtr<G>> exprs = {
      (aw < bw).node,         (aw < K).node,     (aw <= bw).node,
      (aw <= K).node,         (aw == bw).node,   (aw == K).node,
      a.any(0).node,          a.all(0).node,     (a | b).node,
      (a & b & a).node,       c.mux(a, b).node,  c.mux(x, y).node,
      (!c).node,              (a & b).node,      (a | b).node,
      (a ^ b).node,           (aw != bw).node,   (aw != K).node,
      c.mux(x, 1).node};
  auto build = [&](bool via_expr) {
    QuadCircuit<G> q(g);
    const CB cb(&q);
    const L lc(&cb, g);
    std::vector<std::vector<size_t>> in(5);
    for (size_t k = 0; k < 5; ++k)
      for (size_t i = 0; i < len[k]; ++i) in[k].push_back(lc.eltw_input());
    std::vector<BitW> outs;
    if (via_expr) {
      ExprEmitter<G, L> em(lc, [&](const Term<G> &t) { return in[t.node]; });
      for (const auto &e : exprs)
        for (const auto &v : em(e)) outs.push_back(v);
    } else {
      auto bits = [&](size_t k) {
        std::vector<BitW> v;
        for (size_t w : in[k]) v.push_back(BitW(w, g));
        return v;
      };
      const auto A = bits(0), B = bits(1);
      const BitW C = bits(2)[0];
      std::vector<BitW> kb(W);
      lc.bits(W, kb.data(), K);
      outs.push_back(lc.lt(W, A.data(), B.data()));
      outs.push_back(lc.lt(W, A.data(), kb.data()));
      outs.push_back(lc.leq(W, A.data(), B.data()));
      outs.push_back(lc.leq(W, A.data(), kb.data()));
      outs.push_back(lc.eq(W, A.data(), B.data()));
      outs.push_back(lc.eq(W, A.data(), kb.data()));
      outs.push_back(lc.lor(0, W, [&](size_t j) { return A[j]; }));
      outs.push_back(lc.land(0, W, [&](size_t j) { return A[j]; }));
      for (size_t i = 0; i < W; ++i) outs.push_back(lc.lor(A[i], B[i]));
      // a & b & a is one chain, a balanced tree over (a, b, a).
      for (size_t i = 0; i < W; ++i)
        outs.push_back(lc.land(A[i], lc.land(B[i], A[i])));
      // Bits: Logic's mux. Field values: e + c (t - e), one product.
      for (size_t i = 0; i < W; ++i) outs.push_back(lc.mux(C, A[i], B[i]));
      const size_t d = g.mone() == g.one() ? lc.add(in[3][0], in[4][0])
                                           : lc.sub(in[3][0], in[4][0]);
      outs.push_back(BitW(lc.add(in[4][0], lc.mul(in[2][0], d)), g));
      outs.push_back(lc.lnot(C));
      for (size_t i = 0; i < W; ++i) outs.push_back(lc.land(A[i], B[i]));
      for (size_t i = 0; i < W; ++i) outs.push_back(lc.lor(A[i], B[i]));
      for (size_t i = 0; i < W; ++i) outs.push_back(lc.lxor(A[i], B[i]));
      outs.push_back(lc.lnot(lc.eq(W, A.data(), B.data())));
      outs.push_back(lc.lnot(lc.eq(W, A.data(), kb.data())));
      // c ? x : 1 is 1 + c (x - 1): the constant stays a coefficient.
      const size_t cx = lc.axpy(lc.mul(in[2][0], in[3][0]), lc.mone(),
                                in[2][0]);
      outs.push_back(BitW(lc.one(), lc.one(), cx));
    }
    for (const auto &o : outs) lc.assert0(o);
    auto circ = q.mkcircuit(/*nc=*/1);
    std::vector<uint8_t> id(SHA384::kDigestSize);
    ::proofs::circuit_id<G, SHA384>(id.data(), *circ, g);
    return std::make_pair(id, circ->nterms());
  };
  const auto direct = build(false), via = build(true);
  EXPECT_EQ(direct.first, via.first);
  EXPECT_EQ(direct.second, via.second);

  // The host evaluation, on random inputs.
  using Set = FieldSet<SHA384, G>;
  std::mt19937_64 rng(11);
  auto word = [](const std::vector<typename G::Elt> &v, size_t at, size_t w,
                 const G &f) {
    uint64_t u = 0;
    for (size_t i = 0; i < w; ++i) u |= uint64_t(v[at + i] == f.one()) << i;
    return u;
  };
  for (size_t trial = 0; trial < 64; ++trial) {
    const uint64_t ua = rng() % 64, ub = trial < 4 ? ua : rng() % 64;
    const bool uc = rng() & 1;
    ValueStore<Set> v(5);
    auto bitv = [&](uint64_t u, size_t w) {
      std::vector<typename G::Elt> out;
      for (size_t i = 0; i < w; ++i) out.push_back((u >> i) & 1 ? g.one() : g.zero());
      return out;
    };
    v.v[0] = Set::template wrap<G>(bitv(ua, W));
    v.v[1] = Set::template wrap<G>(bitv(ub, W));
    v.v[2] = Set::template wrap<G>(bitv(uc, 1));
    v.v[3] = Set::template wrap<G>({g.of_scalar(1234)});
    v.v[4] = Set::template wrap<G>({g.of_scalar(5678)});
    auto at = [&](size_t k) { return eval_expr(exprs[k], v); };
    EXPECT_EQ(at(0)[0], ua < ub ? g.one() : g.zero());
    EXPECT_EQ(at(1)[0], ua < K ? g.one() : g.zero());
    EXPECT_EQ(at(2)[0], ua <= ub ? g.one() : g.zero());
    EXPECT_EQ(at(3)[0], ua <= K ? g.one() : g.zero());
    EXPECT_EQ(at(4)[0], ua == ub ? g.one() : g.zero());
    EXPECT_EQ(at(5)[0], ua == K ? g.one() : g.zero());
    EXPECT_EQ(at(6)[0], ua != 0 ? g.one() : g.zero());
    EXPECT_EQ(at(7)[0], ua == 63 ? g.one() : g.zero());
    EXPECT_EQ(word(at(8), 0, W, g), ua | ub);
    EXPECT_EQ(word(at(9), 0, W, g), ua & ub);
    EXPECT_EQ(word(at(10), 0, W, g), uc ? ua : ub);
    EXPECT_EQ(at(11)[0], g.of_scalar(uc ? 1234 : 5678));
    EXPECT_EQ(at(12)[0], uc ? g.zero() : g.one());
    EXPECT_EQ(word(at(13), 0, W, g), ua & ub);
    EXPECT_EQ(word(at(14), 0, W, g), ua | ub);
    EXPECT_EQ(word(at(15), 0, W, g), ua ^ ub);
    EXPECT_EQ(at(16)[0], ua != ub ? g.one() : g.zero());
    EXPECT_EQ(at(17)[0], ua != K ? g.one() : g.zero());
    EXPECT_EQ(at(18)[0], g.of_scalar(uc ? 1234 : 1));
  }
}
TEST(GordieHoweExpr, BuildersMatchLogic) {
  builders_match_logic(AF());
  builders_match_logic(MF());
}

// Arithmetic stays in Logic's c0 + c1 x form: constants and scalings fold
// into the coefficients (no gate), and a product is one gate per
// coordinate. Integer constants convert through the field.
TEST(GordieHoweExpr, ArithmeticFoldsConstants) {
  const AF &f = env().af;
  using CB = CompilerBackend<AF>;
  using L = Logic<AF, CB>;
  const Ref<AF, Subfield<>, Committed> u{0, 2, &f, nullptr, {2}};
  const Ref<AF, Subfield<>, Committed> w{1, 2, &f, nullptr, {2}};
  QuadCircuit<AF> q(f);
  const CB cb(&q);
  const L lc(&cb, f);
  std::vector<std::vector<size_t>> in(2);
  for (auto &x : in)
    for (size_t i = 0; i < 2; ++i) x.push_back(lc.eltw_input());
  ExprEmitter<AF, L> em(lc, [&](const Term<AF> &t) { return in[t.node]; });
  const auto e = 7 - 3 * (u + 5);  // -3 u - 8: one term, no gate
  const auto &v = em(e.node);
  EXPECT_EQ(v[0].c0, f.negf(f.of_scalar(8)));
  EXPECT_EQ(v[0].c1, f.negf(f.of_scalar(3)));
  EXPECT_EQ(v[0].x, in[0][0]);
  const auto &p = em((u * w + 2).node);
  EXPECT_EQ(p[1].c0, f.of_scalar(2));
  EXPECT_EQ(p[1].c1, f.one());
  // Typed results: a product of Bits is a Bit; a Subfield sum stays one.
  static_assert(std::is_same_v<decltype((u * w).sum())::type_tag, Field>);
  static_assert(
      std::is_same_v<decltype(u * w)::type_tag, Subfield<>>);
}

// bit_from_unchecked over a non-affine expression: a circuit reads it
// through the expression, a generator reads its host value, the report
// lists it, and no affine row reads it.
TEST(GordieHoweExpr, BitFromUncheckedExpression) {
  const AF &f = env().af;
  Sys cs("gh-unchecked-expr");
  auto &A = cs.domain(env().profile(), "A");
  auto x = A.priv(Subfield{}, "x", 4);
  auto u = A.bit_from_unchecked("u", x * x);  // x in {0, 1}
  static_assert(std::is_same_v<decltype(u), Ref<AF, Bit, CircuitOnly>>);
  auto gu = A.priv(Field{}, "gu", 4, depends_on(u), [](const Vec &v) { return v; });
  // u is circuit-only: the equality reads it through its expression.
  assert_equal(u, x, "u = x").pin(Placement::kCircuit);
  cs.affine("gu = x", gu - x);
  auto c = compile(cs);
  EXPECT_NE(c->report().find("unchecked Bit 'u' n=4"), std::string::npos)
      << c->report();
  auto prep = c->prepare(Assignment());
  for (bool cheat : {false, true}) {
    Assignment w;
    Vec xv = {f.zero(), f.one(), f.one(), f.zero()};
    if (cheat) xv[2] = f.of_scalar(2);  // u = 4 != x
    w.set(x, xv);
    ProveOptions opt;
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    EXPECT_EQ(prep.verify(prep.prove(w, rng, opt)), !cheat) << cheat;
  }
  // An affine row cannot read it.
  Sys t("gh-unchecked-expr-affine");
  auto &B = t.domain(env().profile(), "B");
  auto y = B.priv(Subfield{}, "y", 4);
  auto v = B.bit_from_unchecked("v", y * y);
  t.affine("v = y", Ref<AF>(v) - y);
  assert_zero(y[0] * y[1], "y").pin(Placement::kCircuit);
  try {
    compile(t);
    ADD_FAILURE() << "an affine row read an expression value";
  } catch (const CompileError &e) {
    EXPECT_NE(std::string(e.what()).find("defined by a non-affine expression"),
              std::string::npos)
        << e.what();
  }
}

// assert_zero and assert_true placed by cost: affine rows for affine
// expressions (constants included, a public value times an affine
// expression through Diagonal), every constraint that reads a structured
// operator in affine rows, quadratic triples for a b - c on Field cells,
// the circuit for the rest; a pin overrides. The system proves, and each
// placement rejects a wrong value.
struct PredicateSystem {
  Sys cs{"gh-predicates"};
  Ref<AF, Subfield<>, Committed> x, y, z, t, c3;
  Ref<AF, Field, Committed> u, v, w, w2;
  Ref<AF, Bit, Committed> bits, one;
  Ref<AF, Field, Public> k;
  PredicateSystem() {
    const AF &af = env().af;
    auto &A = cs.domain(env().profile(), "A");
    x = A.priv(Subfield{}, "x", 4);
    y = A.priv(Subfield{}, "y", 4);
    z = A.priv(Subfield{}, "z", 4);
    t = A.priv(Subfield{}, "t", 4);
    c3 = A.priv(Subfield{}, "c3", 4);
    u = A.priv(Field{}, "u", 4);
    v = A.priv(Field{}, "v", 4);
    w = A.priv(Field{}, "w", 4);
    w2 = A.priv(Field{}, "w2", 4);
    bits = A.priv(Bit{}, "bits", Shape{4, 3});
    one = A.priv(Bit{}, "one", 4);
    k = A.pub(Field{}, "k", 4);
    assert_zero(x + 5 - y, "affine");
    assert_zero(u * v - w, "triple");
    assert_zero(w2 - v * u, "triple-c").pin(Placement::kCircuit);
    assert_zero(x * x - z, "circ");
    assert_zero(Diagonal(k)(x) - t, "structured");
    assert_zero(k * x - t, "public-product");
    assert_true(bits.from_bits() < 6, "lt");
    assert_true(one, "bit");
    assert_zero(materialize(x * x) * x - c3, "materialized");
  }
  Assignment statement() const {
    const AF &af = env().af;
    Assignment st;
    st.set(k, Vec{af.of_scalar(1), af.of_scalar(2), af.of_scalar(3),
                  af.of_scalar(4)});
    return st;
  }
  Assignment witness(const std::string &wrong = "") const {
    const AF &af = env().af;
    auto vec = [&](std::initializer_list<uint64_t> l) {
      Vec out;
      for (uint64_t x : l) out.push_back(af.of_scalar(x));
      return out;
    };
    std::map<std::string, Vec> val = {
        {"x", vec({2, 3, 4, 5})},       {"y", vec({7, 8, 9, 10})},
        {"z", vec({4, 9, 16, 25})},     {"t", vec({2, 6, 12, 20})},
        {"c3", vec({8, 27, 64, 125})},  {"u", vec({3, 5, 7, 11})},
        {"v", vec({2, 2, 2, 2})},       {"w", vec({6, 10, 14, 22})},
        {"w2", vec({6, 10, 14, 22})},   {"one", vec({1, 1, 1, 1})},
        // 1, 2, 3, 5: below 6.
        {"bits", vec({1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1})}};
    if (!wrong.empty()) {
      auto &e = val.at(wrong)[1];
      // A different value, or (bits) the word 6.
      e = wrong == "bits" ? af.zero() : af.addf(e, af.one());
      if (wrong == "bits") {
        val.at("bits")[3] = af.zero();
        val.at("bits")[4] = af.one();
        val.at("bits")[5] = af.one();
      }
    }
    Assignment wa;
    wa.set(x, val["x"]).set(y, val["y"]).set(z, val["z"]).set(t, val["t"]);
    wa.set(c3, val["c3"]).set(u, val["u"]).set(v, val["v"]).set(w, val["w"]);
    wa.set(w2, val["w2"]).set(bits, val["bits"]).set(one, val["one"]);
    return wa;
  }
};

TEST(GordieHoweExpr, PlacementAndPinning) {
  PredicateSystem t;
  auto c = compile(t.cs);
  const std::string r = c->report();
  for (const char *want : {
           "assert_zero 'affine' n=4: affine rows (affine)",
           "assert_zero 'triple' n=4: quadratic triples (cheapest; ",
           "assert_zero 'triple-c' n=4: circuit (pinned)",
           "assert_zero 'circ' n=4: circuit (default; ",
           "assert_zero 'structured' n=4: affine rows (reads the structured "
           "operator 'diagonal')",
           "assert_zero 'public-product' n=4: affine rows (affine)",
           "assert_true 'lt' n=4: circuit (Logic gadgets)",
           "assert_true 'bit' n=4: affine rows (affine)",
           "assert_zero 'materialized' n=4: circuit",
           // affine, structured, public-product, bit: 4 rows each.
           "affine_rows=16 quadratic=5",
       })
    EXPECT_NE(r.find(want), std::string::npos) << want << "\n" << r;
  auto prep = c->prepare(t.statement());
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(t.witness(), rng)));
  // A wrong value of each placement's input: affine (y), triple (w; the
  // honest prover's quadratic check aborts, so it is skipped),
  // circuit (z, w2, bits, c3), structured and public product (t).
  for (const char *wrong : {"y", "z", "w2", "bits", "c3", "t"}) {
    ProveOptions opt;
    opt.require_satisfied = false;
    EXPECT_FALSE(prep.verify(prep.prove(t.witness(wrong), rng, opt))) << wrong;
  }
}

// The placement errors: a pin away from affine rows for a constraint that
// reads a structured operator, a structured operator in a non-affine
// expression, a pin the expression does not fit, and operands of two
// domains.
TEST(GordieHoweExpr, PlacementErrors) {
  auto error = [](const std::function<void(Sys &, Ref<AF, Subfield<>, Committed>,
                                           Ref<AF, Subfield<>, Committed>,
                                           Ref<AF, Field, Public>)> &decl) {
    Sys cs("gh-predicate-errors");
    auto &A = cs.domain(env().profile(), "A");
    auto x = A.priv(Subfield{}, "x", 4);
    auto z = A.priv(Subfield{}, "z", 4);
    auto k = A.pub(Field{}, "k", 4);
    assert_zero(x[0] * x[1], "c").pin(Placement::kCircuit);
    decl(cs, x, z, k);
    try {
      compile(cs);
    } catch (const CompileError &e) {
      return std::string(e.what());
    }
    return std::string();
  };
  auto expect = [](const std::string &err, const char *want) {
    EXPECT_NE(err.find(want), std::string::npos) << want << " / " << err;
  };
  expect(error([](Sys &cs, auto x, auto z, auto k) {
           assert_zero(Diagonal(k)(x) - z, "p").pin(Placement::kCircuit);
         }),
         "assert_zero 'p' reads the structured operator 'diagonal', which a "
         "circuit cannot expand, so it is pinned to affine rows; the pin to "
         "circuit is refused");
  expect(error([](Sys &cs, auto x, auto z, auto k) {
           assert_zero(Diagonal(k)(x) * x - z, "p");
         }),
         "so it is pinned to affine rows, but it is not affine");
  expect(error([](Sys &cs, auto x, auto z, auto) {
           assert_zero(x * x - z, "p").pin(Placement::kAffine);
         }),
         "assert_zero 'p' is pinned to affine rows but is not affine");
  expect(error([](Sys &cs, auto x, auto z, auto) {
           assert_zero(x * x - z, "p").pin(Placement::kQuadratic);
         }),
         "is pinned to quadratic triples but is not a b - c on committed "
         "phase-0 Field cells");
  // One domain per field: a second domain of a field is a CompileError, so
  // a predicate's field names its domain.
  Sys cs("gh-predicate-domains");
  cs.domain(env().profile(), "A");
  EXPECT_THROW(cs.domain(env().profile(), "B"), CompileError);
}

// materialize emits ntt_gadget::share on each coordinate, so the circuit
// equals the one Logic builds with share by hand.
TEST(GordieHoweExpr, MaterializeIsShare) {
  const AF &f = env().af;
  using CB = CompilerBackend<AF>;
  using L = Logic<AF, CB>;
  const Ref<AF, Subfield<>, Committed> x{0, 2, &f, nullptr, {2}};
  const Ref<AF, Subfield<>, Committed> y{1, 2, &f, nullptr, {2}};
  auto build = [&](int mode) {
    QuadCircuit<AF> q(f);
    const CB cb(&q);
    const L lc(&cb, f);
    std::vector<std::vector<size_t>> in(2);
    for (auto &w : in)
      for (size_t i = 0; i < 2; ++i) w.push_back(lc.eltw_input());
    if (mode == 0) {  // by hand
      for (size_t i = 0; i < 2; ++i) {
        const size_t s = ntt_gadget::share(lc, lc.mul(in[0][i], in[0][i]));
        lc.assert0(lc.sub(lc.mul(s, in[0][i]), in[1][i]));
      }
    } else {
      ExprEmitter<AF, L> em(lc, [&](const Term<AF> &t) { return in[t.node]; });
      em.assert_zero((materialize(x * x) * x - y).node);
    }
    auto circ = q.mkcircuit(/*nc=*/1);
    std::vector<uint8_t> id(SHA384::kDigestSize);
    ::proofs::circuit_id<AF, SHA384>(id.data(), *circ, f);
    return id;
  };
  EXPECT_EQ(build(0), build(1));
}

}  // namespace
}  // namespace proofs::gordiehowe
