// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe batched form tests (gordiehowe_test binary): an atom read
// twice is one operand. A square of a handle, of
// a view, of a view of a product and of a broadcast product read one
// operand, and so does a view read by two monomials; different views, and
// equal views that are different nodes (which the plan export writes as
// two expressions), stay apart. In a system the batches verify, and a
// wrong witness or a changed operand word is rejected.

#include "gordiehowe/tests/gordiehowe_test.h"

namespace proofs::gordiehowe {
namespace {

using Set = FieldSet<SHA384, AF>;
using compiler::batch_form;
using compiler::BatchForm;

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
// Q(atoms) coordinatewise, the atoms evaluated on V.
Vec eval_form(const BatchForm<AF> &q, const std::vector<Vec> &v) {
  const AF &f = env().af;
  std::vector<Vec> ops;
  for (const auto &a : q.atoms) ops.push_back(eval(a, v));
  Vec out(q.n, f.zero());
  for (const auto &m : q.monos)
    for (size_t i = 0; i < q.n; ++i) {
      AElt t = m.coeff;
      for (unsigned j : m.ops) f.mul(t, ops[j][i]);
      f.add(out[i], t);
    }
  return out;
}
// E's form, and that it states E on V.
BatchForm<AF> form_of(const ExprPtr<AF> &e, const std::vector<Vec> &v) {
  std::string why;
  auto q = batch_form<AF>(e, why, 64, /*pad_affine=*/true);
  EXPECT_TRUE(q.has_value()) << why;
  if (!q) return BatchForm<AF>{};
  EXPECT_EQ(eval_form(*q, v), eval(e, v));
  return *q;
}

struct Handles {
  const AF &f = env().af;
  Ref<AF, Subfield<>, Committed> x{0, 6, &f, nullptr, {6}};
  Ref<AF, Subfield<>, Committed> y{1, 3, &f, nullptr, {3}};
  Ref<AF, Subfield<>, Committed> z{2, 3, &f, nullptr, {3}};
  Ref<AF, Subfield<>, Committed> w{3, 6, &f, nullptr, {2, 3}};
  Ref<AF, Subfield<>, Committed> s{4, 1, &f, nullptr, {1}};
  std::vector<Vec> v = {ints({1, 2, 3, 4, 5, 6}), ints({7, 8, 9}),
                        ints({10, 11, 12}), ints({2, 3, 5, 7, 11, 13}),
                        ints({17})};
};

// Each use of a handle is its own node (as in a predicate), and views of
// these detached handles are expression views (gathers).
//
// A square reads one operand: of a handle (y y, two nodes of y), of a view
// node, of a view of a product ((x x)[0:3], the gathered factors), of a
// product broadcast by a view (y y over w's rows) and of a broadcast
// scalar (s s over w).
TEST(GordieHoweBatchForm, SquaresReadOneOperand) {
  Handles h;
  const auto hsq = form_of((h.y * h.y - h.z).node, h.v);
  EXPECT_EQ(hsq.atoms.size(), 2u);
  ASSERT_EQ(hsq.monos.size(), 2u);
  EXPECT_EQ(hsq.monos[0].ops, (std::vector<unsigned>{0, 0}));
  const auto lo = as_expr(h.x).slice(0, 3);
  const auto gsq = form_of((lo * lo - h.y).node, h.v);
  EXPECT_EQ(gsq.atoms.size(), 2u);
  const auto vsq = form_of(((h.x * h.x).slice(0, 3) - h.y).node, h.v);
  EXPECT_EQ(vsq.atoms.size(), 2u);
  ASSERT_EQ(vsq.monos.size(), 2u);
  EXPECT_EQ(vsq.monos[0].ops, (std::vector<unsigned>{0, 0}));
  const auto bsq = form_of((h.w - h.y * h.y).node, h.v);
  EXPECT_EQ(bsq.atoms.size(), 2u);
  EXPECT_EQ(bsq.n, 6u);
  const auto ssq = form_of((h.w - h.s * h.s).node, h.v);
  EXPECT_EQ(ssq.atoms.size(), 2u);
  EXPECT_EQ(ssq.n, 6u);
}

// A view read by two monomials is one operand: one view node, and the
// gathered factors of x in two views of products.
TEST(GordieHoweBatchForm, SharedViewIsOneOperand) {
  Handles h;
  const auto hi = as_expr(h.x).slice(3, 6);
  const auto two = form_of((hi * h.y + hi * h.z - h.y).node, h.v);
  // x[3:6], y, z and the affine part.
  EXPECT_EQ(two.atoms.size(), 4u);
  auto Y2 = [&] { return as_expr(h.y).concat(h.y); };
  auto Z2 = [&] { return as_expr(h.z).concat(h.z); };
  const auto views =
      form_of(((h.x * Y2()).slice(0, 3) + (h.x * Z2()).slice(0, 3)).node, h.v);
  // x[0:3], (y y)[0:3] and (z z)[0:3].
  EXPECT_EQ(views.atoms.size(), 3u);
}

// Different views of one handle, one view of two handles, a handle and
// its multiple, and equal views that are two nodes are different
// operands.
TEST(GordieHoweBatchForm, DifferentViewsStayApart) {
  Handles h;
  auto X = [&] { return as_expr(h.x); };
  const auto halves = form_of((X().slice(0, 3) * X().slice(3, 6)).node, h.v);
  ASSERT_FALSE(halves.monos.empty());
  EXPECT_EQ(halves.monos[0].ops, (std::vector<unsigned>{0, 1}));
  const auto lo = X().slice(0, 3);
  const auto rot = form_of((lo * lo.rotate(1, 0) - h.y).node, h.v);
  EXPECT_EQ(rot.atoms.size(), 3u);
  // x[0:3] and w.flat()[0:3]: one index map on two atoms (wf is one node).
  const auto wf = as_expr(h.w).flat();
  const auto other =
      form_of(((h.x * h.x).slice(0, 3) - (wf * wf).slice(0, 3)).node, h.v);
  EXPECT_EQ(other.atoms.size(), 2u);
  EXPECT_EQ(other.monos.size(), 2u);
  const auto scaled = form_of((h.y * h.y - (2 * h.y) * h.y).node, h.v);
  EXPECT_EQ(scaled.atoms.size(), 2u);
  const auto nodes = form_of(
      (X().slice(0, 3) * h.y - X().reindex({0, 1, 2}) * h.z).node, h.v);
  EXPECT_EQ(nodes.atoms.size(), 4u);
}

// The forms in a system, each pinned to a batch: with lo = x[0:3] and
// hi = x[3:6] (views of a handle, each a handle of its own),
//   gsq     lo lo = y                 2 operands (lo, y)
//   vsq     2 (x x)[3:6] = v          2 operands (x[3:6], v)
//   bsq     w = z z, z over w's rows  2 operands (z broadcast, w)
//   two     hi y + hi z = u           4 operands (hi, y, z, u)
//   halves  lo hi = p                 3 operands (lo, hi, p)
// The proof verifies; a wrong witness, and a batch whose reduction reads
// changed operand words, are rejected.
struct SquareSystem {
  Sys s{"gh-batch-form-squares"};
  Ref<AF, Subfield<>, Committed> x, y, v, z, w, u, p;
  SquareSystem() {
    auto &A = s.domain(env().profile(), "A");
    x = A.priv(Subfield{}, "x", 6);
    y = A.priv(Subfield{}, "y", 3);
    v = A.priv(Subfield{}, "v", 3);
    z = A.priv(Subfield{}, "z", 3);
    w = A.priv(Subfield{}, "w", Shape{2, 3});
    u = A.priv(Subfield{}, "u", 3);
    p = A.priv(Subfield{}, "p", 3);
    const auto lo = x.slice(0, 3);
    const auto hi = x.slice(3, 6);
    assert_zero(lo * lo - y, "gsq").pin(Placement::kBatch);
    assert_zero(2 * (x * x).slice(3, 6) - v, "vsq").pin(Placement::kBatch);
    assert_zero(w - z * z, "bsq").pin(Placement::kBatch);
    assert_zero(hi * y + hi * z - u, "two").pin(Placement::kBatch);
    assert_zero(lo * hi - p, "halves").pin(Placement::kBatch);
  }
  Assignment witness(uint64_t y0 = 1) const {
    Assignment a;
    a.set(x, ints({1, 2, 3, 4, 5, 6}));
    a.set(y, ints({y0, 4, 9}));
    a.set(v, ints({32, 50, 72}));
    a.set(z, ints({2, 3, 4}));
    a.set(w, ints({4, 9, 16, 4, 9, 16}));
    a.set(u, ints({4 * (1 + 2), 5 * (4 + 3), 6 * (9 + 4)}));
    a.set(p, ints({4, 10, 18}));
    return a;
  }
};
// The operand count the report gives batch NAME, or 0.
size_t operands(const std::string &r, const std::string &name) {
  const size_t at = r.find("  batch " + name + ": ");
  if (at == std::string::npos) return 0;
  const std::string tag = "Q degree 2 in ";
  const size_t q = r.find(tag, at);
  if (q == std::string::npos) return 0;
  return std::stoul(r.substr(q + tag.size()));
}
TEST(GordieHoweBatchForm, SquaresProveAndReject) {
  SquareSystem t;
  auto c = compile(t.s);
  const std::string r = c->report();
  EXPECT_EQ(operands(r, "gsq"), 2u) << r;
  EXPECT_EQ(operands(r, "vsq"), 2u) << r;
  EXPECT_EQ(operands(r, "bsq"), 2u) << r;
  EXPECT_EQ(operands(r, "two"), 4u) << r;
  EXPECT_EQ(operands(r, "halves"), 3u) << r;
  auto prep = c->prepare(Assignment{});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(t.witness(), rng)));
  auto rejects = [&](const Assignment &w, ProveOptions opt) {
    opt.require_satisfied = false;
    try {
      return !prep.verify(prep.prove(w, rng, opt));
    } catch (const std::runtime_error &) {
      return true;
    }
  };
  // y[0] = 2 against lo[0]^2 = 1.
  EXPECT_TRUE(rejects(t.witness(2), ProveOptions{}));
  // Each batch's reduction reading changed operand words, the committed
  // words honest. (A table may hold words no instance reads, so every
  // word changes.)
  for (size_t b = 0; b < 5; ++b) {
    bool hit = false;
    ProveOptions opt;
    opt.batch_words = [&](size_t d, size_t bb, SysValue &words) {
      if (d != 0 || bb != b) return;
      for (auto &x : std::get<Vec>(words)) env().af.add(x, env().af.one());
      hit = true;
    };
    EXPECT_TRUE(rejects(t.witness(), opt)) << "batch " << b;
    EXPECT_TRUE(hit) << "batch " << b;
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
