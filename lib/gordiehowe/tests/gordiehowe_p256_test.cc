// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe over the P-256 base field F_p256: a
// prime, unpacked domain whose designated subfield is the field itself.
//
//   P256Domain.SmallSystem      affine rows, quadratic triples, a circuit
//                               predicate, a Bit cell and a field batch
//                               prove, verify and reject tampering, at
//                               original and at list-radius Ligero
//   P256Domain.SkipCharacteristic  the field skip's points are distinct
//   P256Domain.DISABLED_Micro   the per-cell commit, per-term GKR and
//                               per-instance field-batch rates

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <random>
#include <string>
#include <tuple>
#include <vector>

#include "gordiehowe/examples/p256/p256_testing.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using namespace examples::mdoc::p256_testing;  // NOLINT

// A small system in one F_p256 domain: x + 5 = y (affine rows), u v = w
// (quadratic triples, pinned), x^2 = z (a circuit predicate), a Bit advice cell
// (its Boolean check), and the
// field batch a b c = d over the Subfield table T. R = x[0] + z[0] is a
// public value.
struct SmallSystem {
  static constexpr size_t kN = 37;
  Sys cs{"gh-p256-small"};
  Ref<F, Subfield<>, Committed> x, y, z, T;
  Ref<F, Field, Committed> u, v, w;
  Ref<F, Bit, Committed> b;
  Ref<F, Field, Public> r;
  explicit SmallSystem(const Profile &p) {
    auto &A = cs.domain(p, "A");
    x = A.priv(Subfield{}, "x", 4);
    y = A.priv(Subfield{}, "y", 4);
    z = A.priv(Subfield{}, "z", 4);
    u = A.priv(Field{}, "u", 4);
    v = A.priv(Field{}, "v", 4);
    w = A.priv(Field{}, "w", 4);
    b = A.priv(Bit{}, "b", 3, depends_on(u), [](const Vec &) {
      return Vec{fp().one(), fp().zero(), fp().one()};
    });
    T = A.priv(Subfield{}, "T", 4 * kN);
    r = A.pub(Field{}, "r", 1);
    assert_zero(x + 5 - y, "affine");
    // Pinned: F_p256's rates would place it in the circuit.
    assert_zero(u * v - w, "triple").pin(Placement::kQuadratic);
    assert_zero(x * x - z, "circ").pin(Placement::kCircuit);
    assert_zero(x.reindex({0}) + z.reindex({0}) - r, "public");
    compiler::FieldRelation<F> abc{"abc-d", 4,
                         {{fp().one(), {0, 1, 2}}, {fp().mone(), {3}}}};
    cs.batch("abc", std::vector<Ref<F, Subfield<>, Committed>>{T}, abc,
            compiler::AffineOperandMap<F>::columns(fp(), "columns", 4, kN), 4);
  }
  Assignment statement(const Vec &xv, const Vec &zv) const {
    Assignment st;
    st.set(r, Vec{fp().addf(xv[0], zv[0])});
    return st;
  }
};

void small_system(bool list_radius) {
  const F &f = fp();
  auto build = [](const Profile &p) { return std::make_unique<SmallSystem>(p); };
  std::unique_ptr<SmallSystem> h;
  std::unique_ptr<Compiled> c;
  if (list_radius) {
    std::tie(h, c) = compile_at_list_radius(build);
    // (1367, 341) over F_p256 at the classical target 2^-113.5 (rate 4).
    EXPECT_EQ(c->compiled_domain(0).plan().t, 108u) << tableau(*c);
  } else {
    h = build(profile());
    c = compile(h->cs);
  }
  const SmallSystem &t = *h;
  const std::string rep = c->report();
  for (const char *want : {
           "assert_zero 'affine' n=4: affine rows (affine)",
           "assert_zero 'triple' n=4: quadratic triples",
           "assert_zero 'circ' n=4: circuit (pinned)",
           "field skip: abc-d, degree 3 in 4 operands, 37 instances, width 4, "
           "skip domain 10 consecutive integers",
       })
    EXPECT_NE(rep.find(want), std::string::npos) << want << "\n" << rep;
  std::mt19937_64 g(11);
  const Vec xv = random_vec(4, g), uv = random_vec(4, g), vv = random_vec(4, g);
  Vec yv(4), zv(4), wv(4);
  for (size_t i = 0; i < 4; ++i) {
    yv[i] = f.addf(xv[i], f.of_scalar(5));
    zv[i] = f.mulf(xv[i], xv[i]);
    wv[i] = f.mulf(uv[i], vv[i]);
  }
  Vec tv = random_vec(4 * SmallSystem::kN, g);
  constexpr size_t n = SmallSystem::kN;
  for (size_t i = 0; i < n; ++i)
    tv[3 * n + i] = f.mulf(f.mulf(tv[i], tv[n + i]), tv[2 * n + i]);
  auto witness = [&](const std::string &wrong) {
    Vec x2 = xv, y2 = yv, z2 = zv, u2 = uv, t2 = tv;
    if (wrong == "y") f.add(y2[2], f.one());
    if (wrong == "z") f.add(z2[1], f.one());
    if (wrong == "T") f.add(t2[3 * n + 17], f.one());
    Assignment a;
    a.set(t.x, x2).set(t.y, y2).set(t.z, z2).set(t.u, u2).set(t.v, vv);
    a.set(t.w, wv).set(t.T, t2);
    return a;
  };
  auto prep = c->prepare(t.statement(xv, zv));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(witness(""), rng)));
  // A value off each placement: affine (y), circuit (z), the field batch
  // (T). The triple is checked by the honest prover, and a Bit
  // value by the prover's type check.
  for (const char *wrong : {"y", "z", "T"}) {
    ProveOptions opt;
    opt.require_satisfied = false;
    EXPECT_FALSE(prep.verify(prep.prove(witness(wrong), rng, opt))) << wrong;
  }
  // A wrong statement.
  auto bad = c->prepare(t.statement(xv, yv));
  ProveOptions opt;
  opt.require_satisfied = false;
  EXPECT_FALSE(bad.verify(bad.prove(witness(""), rng, opt)));
}
TEST(P256Domain, SmallSystem) { small_system(false); }
TEST(P256Domain, SmallSystemListRadius) { small_system(true); }

// The field-generic skip's characteristic condition: its D (w - 1) + 1
// points 0, 1, ... are distinct elements of F_p256 for every width the
// skip takes, since p exceeds 2^255. The characteristic is exact: it
// exceeds p - 1 and not p.
TEST(P256Domain, SkipCharacteristic) {
  EXPECT_TRUE(characteristic_above(fp(), Bound::pow2(255)));
  const Bound p = field_characteristic(fp());
  EXPECT_TRUE(characteristic_above(fp(), p - 1));
  EXPECT_FALSE(characteristic_above(fp(), p));
  compiler::FieldRelation<F> sq{
      "x^2-y", 2, {{fp().one(), {0, 0}}, {fp().mone(), {1}}}};
  std::vector<compiler::FieldBatchPart<F>> parts = {
      {sq, compiler::AffineOperandMap<F>::columns(fp(), "columns", 2, 8)}};
  for (unsigned width : {2u, 4u, 16u, 64u})
    EXPECT_EQ(compiler::field_batch_error(fp(), parts, width), "") << width;
}

// ------------------------------------------------------------- benches --
// Each system at its list-radius tableau (compile_at_list_radius).

// Commit cost per committed cell: N Field cells, one circuit predicate on
// the first three.
struct CellsSystem {
  Sys cs{"gh-p256-cells"};
  Ref<F, Field, Committed> x;
  CellsSystem(const Profile &p, size_t n) {
    auto &A = cs.domain(p, "A");
    x = A.priv(Field{}, "x", n);
    assert_zero(x.reindex({0}) * x.reindex({1}) - x.reindex({2}), "one")
        .pin(Placement::kCircuit);
  }
};
void cells(size_t n) {
  std::mt19937_64 g(n);
  auto [h, c] = compile_at_list_radius(
      [n](const Profile &p) { return std::make_unique<CellsSystem>(p, n); });
  Vec xv = random_vec(n, g);
  xv[2] = fp().mulf(xv[0], xv[1]);
  Assignment w;
  w.set(h->x, xv);
  report("P256_MICRO", "cells", n, *c, measure(*c, Assignment{}, w));
}

// GKR cost per quad term: 256 cells, all ones, and M circuit predicates
// x_a x_b - x_c over random index triples (one product and one linear term
// each, depth 1).
struct TermsSystem {
  static constexpr size_t kCells = 256;
  Sys cs{"gh-p256-terms"};
  Ref<F, Subfield<>, Committed> x;
  TermsSystem(const Profile &p, size_t m) {
    std::mt19937_64 g(m);
    auto &A = cs.domain(p, "A");
    x = A.priv(Subfield{}, "x", kCells);
    std::vector<size_t> ia(m), ib(m), ic(m);
    for (size_t i = 0; i < m; ++i) {
      ia[i] = g() % kCells;
      ib[i] = g() % kCells;
      ic[i] = g() % kCells;
    }
    assert_zero(x.reindex(ia) * x.reindex(ib) - x.reindex(ic), "products")
        .pin(Placement::kCircuit);
  }
};
void terms(size_t m) {
  auto [h, c] = compile_at_list_radius(
      [m](const Profile &p) { return std::make_unique<TermsSystem>(p, m); });
  Assignment w;
  w.set(h->x, Vec(TermsSystem::kCells, fp().one()));
  report("P256_MICRO", "terms", m, *c, measure(*c, Assignment{}, w));
}

// Field batch cost per instance: N instances of a b - c (degree 2) or
// a b c - d (degree 3) over a column table, one circuit predicate on the
// table's first instance, skip width 4.
compiler::FieldRelation<F> product_relation(unsigned degree) {
  const F &f = fp();
  compiler::FieldRelation<F> rel{
      degree == 2 ? "ab-c" : "abc-d", degree + 1, {}};
  std::vector<unsigned> factors;
  for (unsigned j = 0; j < degree; ++j) factors.push_back(j);
  rel.monomials = {{f.one(), factors}, {f.mone(), {degree}}};
  return rel;
}
struct BatchSystem {
  Sys cs{"gh-p256-batch"};
  Ref<F, Subfield<>, Committed> T;
  BatchSystem(const Profile &p, size_t n, unsigned degree) {
    auto &A = cs.domain(p, "A");
    T = A.priv(Subfield{}, "T", (degree + 1) * n);
    // Instance 0's a b = c.
    assert_zero(T.reindex({0}) * T.reindex({n}) - T.reindex({2 * n}), "one")
        .pin(Placement::kCircuit);
    cs.batch(
        "rel", std::vector<Ref<F, Subfield<>, Committed>>{T},
        product_relation(degree),
        compiler::AffineOperandMap<F>::columns(fp(), "columns", degree + 1, n),
        4);
  }
};
void batch(size_t n, unsigned degree) {
  const F &f = fp();
  std::mt19937_64 g(n + degree);
  const unsigned k = degree + 1;
  auto [h, c] = compile_at_list_radius([n, degree](const Profile &p) {
    return std::make_unique<BatchSystem>(p, n, degree);
  });
  Vec tv = random_vec(k * n, g);
  // Instance 0 also satisfies the circuit predicate: c = a b.
  if (degree == 3) tv[2 * n] = f.mulf(tv[0], tv[n]);
  for (size_t i = 0; i < n; ++i) {
    Elt p = f.one();
    for (unsigned j = 0; j < degree; ++j) f.mul(p, tv[j * n + i]);
    tv[degree * n + i] = p;
  }
  Assignment w;
  w.set(h->T, tv);
  const char *what = degree == 2 ? "batch2" : "batch3";
  report("P256_MICRO", what, n, *c, measure(*c, Assignment{}, w));
  // The masked zerocheck alone (field_skip.h): the prover's skip and
  // rounds, and the verifier's terminal row, at the same width.
  compiler::MaskedFieldSkip<F> sk(f, product_relation(degree), n, 4);
  std::vector<Vec> ops(n);
  for (size_t i = 0; i < n; ++i)
    for (unsigned j = 0; j < k; ++j) ops[i].push_back(tv[j * n + i]);
  Vec pads(sk.layout.count, f.zero());
  SecureRandomEngine rng;
  sk.fill_pads(pads.data(), rng);
  std::vector<double> pv, vv;
  for (size_t r = 0; r < reps(); ++r) {
    static const uint8_t kLabel[] = "p256-zerocheck";
    BasicProofSeed<P::ProtocolHash> seed;
    std::memset(seed.bytes, 0, sizeof(seed.bytes));
    BasicTranscript<P::ProtocolHash> tp(kLabel, sizeof(kLabel) - 1, seed);
    auto tc = tp.clone();
    auto t0 = Clock::now();
    const auto proof = sk.prove(ops, tc, pads.data());
    pv.push_back(ms_since(t0));
    t0 = Clock::now();
    auto ctx = sk.rows_of(proof, tp, 0);
    (void)sk.instance_weights(ctx);
    vv.push_back(ms_since(t0));
  }
  std::printf("P256_MICRO %s_zerocheck size=%zu prove=%.3f verify=%.3f "
              "pads=%zu messages=%zu\n",
              what, n, median(pv), median(vv), sk.layout.count,
              sk.message_elts());
  std::fflush(stdout);
}

// GH_P256_MICRO selects cells, terms, batch (default all).
TEST(P256Domain, DISABLED_Micro) {
  const char *e = std::getenv("GH_P256_MICRO");
  const std::string which = e != nullptr ? e : "cells,terms,batch";
  if (which.find("cells") != std::string::npos)
    for (size_t n : {2048, 8192, 32768}) cells(n);
  if (which.find("terms") != std::string::npos)
    for (size_t m : {16384, 65536, 262144}) terms(m);
  if (which.find("batch") != std::string::npos)
    for (unsigned d : {2u, 3u})
      for (size_t n : {256, 1024, 4096}) batch(n, d);
}

}  // namespace
}  // namespace proofs::gordiehowe
