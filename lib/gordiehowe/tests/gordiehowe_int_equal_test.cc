// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: interval propagation through products and convolutions,
// assert_int_equal, and the realizations of conv(x, y), over Goldilocks^4.
//
//   GordieHoweIntEqual.Intervals       product, conv, operator, constant,
//                                      digit-sum, statement-bound and
//                                      unbounded intervals
//   GordieHoweIntEqual.WrapNamesTerm   a side that can wrap around p fails
//                                      compilation, its widest term named
//   GordieHoweIntEqual.ProveVerify     an honest proof, a wrong value
//                                      rejected
//   GordieHoweIntEqual.PrimeOnExtension
//                                      DomainProfile::prime = kField on
//                                      Goldilocks^4 fails compilation
//   GordieHoweIntEqual.ModZero         assert_mod(l, r, 0) is the same
//                                      system as assert_int_equal(l, r),
//                                      and takes a pin
//   GordieHoweIntEqual.ProductMod      assert_mod over a product side,
//                                      m >= 2: its committed quotient,
//                                      certificates and record, an honest
//                                      proof, a wrong quotient and a wrong
//                                      residue rejected; the realized
//                                      program's source mod_m with its
//                                      productMod derivation, which the
//                                      C++ check accepts and refuses
//                                      mutated
//   GordieHoweOpInterval.Primitives    int_interval's product, acyclic and
//                                      negacyclic intervals against the
//                                      extremes over every vertex and
//                                      random interior points
//   GordieHoweOpInterval.Operators     each operator kind's own interval
//                                      (OpSpec::interval) against its
//                                      instantiated matrix on random
//                                      operands of the given intervals
//   GordieHoweIntEqual.SlackDerived    Slack requests: the maximum the
//                                      integer equality derives, an honest
//                                      proof, a negative value rejected,
//                                      an unread Slack request refused
//   GordieHoweIntEqual.RootsAndViews   the two-root interval rule and a
//                                      view's interval
//   GordieHoweRange.ProverChecksRequests
//                                      a witness that violates only a range
//                                      request is refused by the prover's
//                                      check before proving; without the
//                                      check the verifier rejects its proof
//   GordieHoweConv.Operators           InverseNtt's transpose, the batch's
//                                      operand map adjoint, AcyclicConv
//                                      against the schoolbook product
//   GordieHoweConv.Realizations        each realization (direct, batch,
//                                      the rule without rates) of
//                                      conv(x, y) and of conv over rows of
//                                      one value (squares among them)
//                                      against the schoolbook reference:
//                                      honest proofs, a wrong result and a
//                                      wrong committed product rejected
//   GordieHoweConv.NonAffine           conv inside a non-affine predicate:
//                                      the batch commits C with the affine
//                                      rows C = INTT(z)[0, lo); a wrong C,
//                                      z or result rejected
//   GordieHoweConv.Rates               the placement rule's choice under
//                                      rates that make the circuit or the
//                                      batch cheap
//   GordieHoweConv.PublicOperand       conv(x, h, EntryBound), h public
//   GordieHoweConv.ProgramExport       the realized program of each
//                                      realization: conv exported as its
//                                      source expression (two views, their
//                                      product, .sum), checked against the
//                                      schoolbook product
//   GordieHoweConv.DenseOperatorExport a public operator given as code
//                                      exported as .rowDot over a constant
//                                      of its matrix, batched

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <random>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/compile_error_testing.h"
#include "algebra/fp14.h"
#include "algebra/fp14_n.h"
#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/reed_solomon_extension_n.h"
#include "algebra/reed_solomon_fp.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/derivation_check.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/compiler/program_builder.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

using AF = Fp64G4;
using AElt = AF::Elt;
using AV = std::vector<AElt>;
using RSA = BasicFpReedSolomon<AF>;
using HF = GF2_256<>;
using GF = GF2_128<>;
using NF = Fp14_9;

// The field set of gordiehowe_mod_test (its instances, SETS mod).
using Sys = ConstraintSystem<SHA384, AF, HF, GF, NF>;
using SysValue = Sys::Value;
using Assignment = Sys::Assignment;
using ProveOptions = Sys::ProveOptions;
using CompiledSystem = Sys::Compiled;

struct Env {
  AF af;
  RSA rsa{af};
  DomainProfile<AF, RSA::Factory, SHA384> a_profile() const {
    DomainProfile<AF, RSA::Factory, SHA384> p;
    p.f = &af;
    p.rsf = &rsa.factory();
    p.field_name = "Goldilocks^4";
    p.rate = 4;
    p.nreq = 64;
    const RSA *r = &rsa;
    p.block_enc = [r](const Circuit<AF> &, size_t nw, size_t nq) {
      return r->block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
    };
    return p;
  }
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}
const AF &af() { return env().af; }

CompileProfile table_profile() {
  CompileProfile c;
  c.name = "int-equal-1024";
  return c;
}

size_t id_of(const Sys &cs, const std::string &name) {
  const auto &N = cs.graph().nodes;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == name) return i;
  ADD_FAILURE() << "no node " << name;
  return SIZE_MAX;
}
bool has(const std::string &report, const std::string &want) {
  if (report.find(want) != std::string::npos) return true;
  ADD_FAILURE() << "missing: " << want << "\n" << report;
  return false;
}
bool honest(const CompiledSystem &c, const Assignment &w) {
  auto prep = c.prepare({});
  SecureRandomEngine rng;
  return prep.verify(prep.prove(w, rng));
}
// The cheating prover under TAMPER is refused by its own satisfaction
// check, or completes and the verifier rejects.
template <class Tamper>
bool rejected(const CompiledSystem &c, const Assignment &w, Tamper tamper) {
  auto prep = c.prepare({});
  ProveOptions opt;
  opt.tamper = tamper;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  std::vector<uint8_t> proof;
  try {
    proof = prep.prove(w, rng, opt);
  } catch (const std::runtime_error &) {
    return true;
  }
  return !prep.verify(proof);
}
// Adds one to coordinate I of node ID.
auto add_one(size_t id, size_t i) {
  return [id, i](size_t at, SysValue &x) {
    if (at != id) return;
    auto &v = std::get<AV>(x);
    af().add(v.at(i), af().one());
  };
}
AV values(const std::vector<uint64_t> &v) {
  AV out;
  for (uint64_t x : v) out.push_back(af().of_scalar(x));
  return out;
}
// The schoolbook convolution of rows of X ([B][lx]) and Y ([B][ly]).
std::vector<uint64_t> schoolbook(const std::vector<uint64_t> &x,
                                 const std::vector<uint64_t> &y, size_t lx,
                                 size_t ly) {
  const size_t B = x.size() / lx, lo = lx + ly - 1;
  std::vector<uint64_t> c(B * lo, 0);
  for (size_t r = 0; r < B; ++r)
    for (size_t a = 0; a < lx; ++a)
      for (size_t b = 0; b < ly; ++b)
        c[r * lo + a + b] += x[r * lx + a] * y[r * ly + b];
  return c;
}

// ------------------------------------------------------------ intervals --

TEST(GordieHoweIntEqual, Intervals) {
  Sys cs("gh-int-intervals");
  auto &A = cs.domain(env().a_profile(), "A");
  // a in [0, 7]; b in [-3, 4] (b + 3 below 8); u without a request.
  const auto a = A.priv(Subfield{}, "a", 4);
  const auto b = A.priv(Subfield{}, "b", 4);
  const auto u = A.priv(Subfield{}, "u", 4);
  assert_range(a, 8, "a");
  const auto three = A.constant("three", AV(4, af().of_scalar(3)));
  assert_range(b + three, 8, "b");
  const Bound p = field_characteristic(af());
  const Graph &g = cs.graph();
  const auto in_prime = compiler::range_internal::prime_node(A, g);
  auto iv = [&](const auto &x, std::string *why = nullptr) {
    std::string w;
    const auto r = compiler::range_internal::expr_interval(
        af(), p, false, g, expr_node(x),
        [&](size_t id) {
          return compiler::range_internal::request_bound(A, g, p, id);
        },
        w, &in_prime);
    if (why != nullptr) *why = w;
    return r;
  };
  using I = compiler::range_internal::Interval;
  EXPECT_EQ(iv(a), (I{0, 7}));
  EXPECT_EQ(iv(b), (I{-3, 4}));
  // Products by their endpoints.
  EXPECT_EQ(iv(a * b), (I{-21, 28}));
  EXPECT_EQ(iv(b * b), (I{-12, 16}));
  // conv: between 1 and 4 products.
  EXPECT_EQ(iv(conv(a, b)), (I{-84, 112}));
  EXPECT_EQ(iv(conv(a, a)), (I{0, 196}));
  // Constant multiples and constants.
  EXPECT_EQ(iv(-3 * as_expr(a) + 5), (I{-16, 5}));
  EXPECT_EQ(iv(as_expr(a).sum()), (I{0, 28}));
  // A sum of an operand times constants (from_digits of a product): each
  // group sums the operand's interval times its own constant, [-21, 28]
  // times 1 and 16, not twice the largest power.
  EXPECT_EQ(iv((a * b).reshape(Shape{2, 2}).from_digits(16)), (I{-357, 476}));
  // An operator's row bound: rows summing to 3 and 4.
  const auto op = ops::sparse_matrix(af(), "rows", 4, {{{0, 1}, {1, 2}}, {{2, 4}}});
  EXPECT_EQ(iv(op(as_expr(a) * as_expr(a))), (I{0, 196}));
  // A public operand with its entry bound: rows sum to 3 * 3.
  const auto h = A.constant("h", AV(3, af().of_scalar(3)));
  EXPECT_EQ(iv(conv(a, h, ops::EntryBound{4})), (I{0, 63}));
  // Without one the operator's own interval reads h's entries (the
  // constant's, all 3): the same rows. A kernel of either sign bounds
  // nothing.
  EXPECT_EQ(iv(conv(a, h)), (I{0, 63}));
  std::string why;
  const auto hs = A.constant("hs", AV{af().of_scalar(3), af().negf(af().one()),
                                      af().of_scalar(2)});
  EXPECT_FALSE(iv(conv(a, hs), &why).has_value());
  has(why, "bounds no interval");
  // A prime-field value without a request: [0, p - 1], its square
  // [0, (p - 1)^2] exactly, and its fifth power beyond the cap 2^300.
  EXPECT_EQ(iv(u), (I{0, SignedInt(p - 1)}));
  EXPECT_EQ(iv(as_expr(u) * as_expr(u)),
            (I{0, SignedInt(p - 1) * SignedInt(p - 1)}));
  const auto u5 =
      as_expr(u) * as_expr(u) * as_expr(u) * as_expr(u) * as_expr(u);
  EXPECT_FALSE(iv(u5, &why).has_value());
  has(why, "exceeds 2^300");
  EXPECT_FALSE(iv(as_expr(a).prod(), &why).has_value());
  has(why, "product of coordinates");
  // A statement value with the declared bound 100 (v := stmt(100)):
  // [0, 99], and its square within the cap.
  const auto st = A.pub(Subfield{}, "st", 4).bounded(100);
  EXPECT_EQ(iv(st), (I{0, 99}));
  EXPECT_EQ(iv(as_expr(st) * as_expr(st)), (I{0, 9801}));
  EXPECT_EQ(iv(a + st), (I{0, 106}));
}

// kField would give every Goldilocks^4 value [0, p - 1], though only the
// subfield's lie in the prime field: refused at compilation.
TEST(GordieHoweIntEqual, PrimeOnExtension) {
  Sys cs("gh-int-prime-ext");
  auto prof = env().a_profile();
  prof.prime = Space::kField;
  auto &A = cs.domain(prof, "A");
  const auto a = A.priv(Subfield{}, "a", 2);
  assert_range(a, 8, "a");
  const std::string err = compile_error(cs, table_profile());
  has(err, "domain A declares its field prime (DomainProfile::prime = "
           "kField), but the field has degree 4 over its prime field");
}

// ---------------------------------------------------- assert_int_equal --

// a in [0, 2^33): a a reaches 2^66 > p, so a a = c cannot be read over
// the integers. The compile fails at the predicate, naming a a.
TEST(GordieHoweIntEqual, WrapNamesTerm) {
  Sys cs("gh-int-wrap");
  auto &A = cs.domain(env().a_profile(), "A");
  const auto a = A.priv(Subfield{}, "a", 2);
  const auto c = A.priv(Subfield{}, "c", 2);
  assert_range(a, Bound(1) << 33, "a");
  assert_range(c, 1024, "c");
  assert_int_equal(a * a + 1, c, "square");
  const std::string err = compile_error(cs, table_profile());
  std::printf("INT_EQUAL_WRAP %s\n", err.c_str());
  has(err, "assert_int_equal 'square': the sides can wrap around p");
  has(err, "the widest term is '(a) * (a)' of the left side");
}

// a, b below 2^10, c = a b below 2^20: assert_int_equal(a b, c) holds
// over the integers. A wrong c is rejected.
TEST(GordieHoweIntEqual, ProveVerify) {
  Sys cs("gh-int-prove");
  auto &A = cs.domain(env().a_profile(), "A");
  const auto a = A.priv(Subfield{}, "a", 4);
  const auto b = A.priv(Subfield{}, "b", 4);
  const auto c = A.priv(Subfield{}, "c", 4, depends_on(a, b),
                        [](const AElt &x, const AElt &y) {
                          return af().mulf(x, y);
                        });
  assert_range(a, 1024, "a");
  assert_range(b, 1024, "b");
  assert_range(c, Bound(1) << 20, "c");
  assert_int_equal(a * b, c, "product");
  auto comp = compile(cs, table_profile());
  const std::string r = comp->report();
  has(r, "assert_int_equal 'product': lhs in [0, 1046529], rhs in [0, "
         "1048575]");
  has(r, "certify:product.noWrap");
  Assignment w;
  w.set(a, values({3, 1023, 0, 77}));
  w.set(b, values({5, 1023, 9, 100}));
  EXPECT_TRUE(honest(*comp, w));
  EXPECT_TRUE(rejected(*comp, w, add_one(c.id, 1)));
}

// assert_int_equal(l, r) is assert_mod(l, r, 0): the same system digest
// and report, and a pin fixes the placement.
TEST(GordieHoweIntEqual, ModZero) {
  struct Built {
    std::unique_ptr<Sys> cs;
    Ref<AF, Subfield<>, Committed> a, b, c;
  };
  auto build = [](bool alias, Placement pin) {
    Built out;
    out.cs = std::make_unique<Sys>("gh-int-mod-zero");
    auto &A = out.cs->domain(env().a_profile(), "A");
    out.a = A.priv(Subfield{}, "a", 4);
    out.b = A.priv(Subfield{}, "b", 4);
    out.c = A.priv(Subfield{}, "c", 4, depends_on(out.a, out.b),
                   [](const AElt &x, const AElt &y) {
                     return af().mulf(x, y);
                   });
    assert_range(out.a, 1024, "a");
    assert_range(out.b, 1024, "b");
    assert_range(out.c, Bound(1) << 20, "c");
    const Predicate p = alias ? assert_int_equal(out.a * out.b, out.c, "product")
                              : assert_mod(out.a * out.b, out.c, 0, "product");
    if (pin != Placement::kAuto) p.pin(pin);
    return out;
  };
  Built s1 = build(true, Placement::kAuto);
  Built s2 = build(false, Placement::kAuto);
  auto c1 = compile(*s1.cs, table_profile());
  auto c2 = compile(*s2.cs, table_profile());
  EXPECT_EQ(c1->digest(), c2->digest());
  EXPECT_EQ(c1->report(), c2->report());
  has(c2->report(), "assert_int_equal 'product': lhs in [0, 1046529]");
  has(c2->report(), "certify:product.noWrap");
  // A pin fixes the placement of the m = 0 form; the proof is honest and a
  // wrong product is rejected.
  Built s3 = build(false, Placement::kCircuit);
  auto c3 = compile(*s3.cs, table_profile());
  Assignment w;
  w.set(s3.a, values({3, 1023, 0, 77}));
  w.set(s3.b, values({5, 1023, 9, 100}));
  EXPECT_TRUE(honest(*c3, w));
  EXPECT_TRUE(rejected(*c3, w, add_one(s3.c.id, 1)));
}

// The derivation of product-form predicate PID of P (certificates C0)
// checks; every mutation of its productMod step or of the predicate is
// refused: a premise dropped, two premises swapped, a premise replaced by
// another fact, R's or lhs's interval widened past p, the modulus made p
// or another, the form changed, the quotient's range premise cut to its
// lhs.
void expect_product_mutants(const ir::Program &P, const ir::Certificates &c0,
                            size_t pid) {
  auto refused = [&](const ir::Program &p, ir::Certificates c) {
    compiler::DerivChecker check(p, c);
    return check.check(pid);
  };
  ASSERT_EQ(refused(P, c0), "");
  const auto &d0 = c0.derivations.at(pid);
  const size_t last = d0.size() - 1;
  const size_t np = d0[last].premises.size();
  ASSERT_GE(np, 3u);
  auto with = [&](auto edit) {
    ir::Certificates c = c0;
    edit(c.derivations[pid]);
    return refused(P, c);
  };
  EXPECT_NE(with([](auto &d) { d.back().premises.pop_back(); }), "");
  EXPECT_NE(with([](auto &d) { d.back().premises.erase(d.back().premises.begin()); }), "");
  EXPECT_NE(with([](auto &d) { std::swap(d.back().premises[0], d.back().premises[1]); }), "");
  EXPECT_NE(with([](auto &d) { std::swap(d.back().premises[1], d.back().premises[2]); }), "");
  EXPECT_NE(with([](auto &d) { d.back().premises[2] = d.back().premises[0]; }), "");
  EXPECT_NE(with([](auto &d) { d.back().premises.push_back(d.back().premises[0]); }), "");
  // An interval premise widened past p.
  const std::string p = P.fields.at(P.domains.at(P.predicates[pid].domain).field).characteristic;
  for (size_t k : {size_t(1), np - 1}) {
    EXPECT_NE(with([&](auto &d) {
                const size_t at = d.back().premises[k];
                ASSERT_EQ(d[at].rule, ir::DStep::kIvlExpr);
                d[at].ints = {"-" + p, p};
              }),
              "")
        << "premise " << k;
  }
  // The predicate's modulus, form or quotient changed.
  auto with_pred = [&](auto edit) {
    ir::Program p2 = P;
    edit(p2.predicates[pid]);
    return refused(p2, c0);
  };
  EXPECT_NE(with_pred([&](ir::Predicate &q) { q.q = p; }), "");
  EXPECT_NE(with_pred([](ir::Predicate &q) { q.q = "1"; }), "");
  EXPECT_NE(with_pred([](ir::Predicate &q) {
              q.mod.form = q.mod.form == ir::ModForm::kProduct
                               ? ir::ModForm::kSpectralProduct
                               : ir::ModForm::kProduct;
            }),
            "");
  EXPECT_NE(with_pred([](ir::Predicate &q) { q.mod.form = ir::ModForm::kOneDigit; }), "");
  EXPECT_NE(with_pred([](ir::Predicate &q) { q.mod.quotient = q.lhs; }), "");
  EXPECT_NE(with_pred([](ir::Predicate &q) { std::swap(q.lhs, q.rhs); }), "");
}

// assert_mod(a b, c, 97) with a, b below 1024 and c below 97: the product
// form commits the quotient below floor(1023^2 / 97) + 1, states one predicate,
// and records its plan record; an honest proof verifies, and a wrong
// quotient or a wrong residue is rejected.
TEST(GordieHoweIntEqual, ProductMod) {
  Sys cs("gh-int-mod-product");
  auto &A = cs.domain(env().a_profile(), "A");
  const auto a = A.priv(Subfield{}, "a", 4);
  const auto b = A.priv(Subfield{}, "b", 4);
  const auto c = A.priv(Subfield{}, "c", 4, depends_on(a, b),
                        [](const AElt &x, const AElt &y) {
                          uint64_t ok = 1;
                          const Bound v = nat_of_ct(af(), af().mulf(x, y), ok);
                          return af().of_scalar(uint64_t(v % 97));
                        });
  assert_range(a, 1024, "a");
  assert_range(b, 1024, "b");
  assert_range(c, 97, "c");
  assert_mod(a * b, c, 97, "product");
  auto comp = compile(cs, table_profile());
  const std::string r = comp->report();
  has(r, "assert_mod 'product': lhs in [0, 1046529], rhs in [0, 96], m = 97, "
         "quotient in [0, 10788]; a committed quotient 'product.q' below "
         "10789");
  has(r, "certify:product.leftSpan");
  has(r, "certify:product.rightSpan");
  has(r, "certify:product.cap");
  ASSERT_EQ(comp->records().product_mod_equalities.size(), 1u);
  const auto &e = comp->records().product_mod_equalities[0];
  EXPECT_EQ(e.qmax, Bound(10788));
  EXPECT_FALSE(e.spectral);
  Assignment w;
  w.set(a, values({3, 1023, 0, 77}));
  w.set(b, values({5, 1023, 9, 100}));
  EXPECT_TRUE(honest(*comp, w));
  EXPECT_TRUE(rejected(*comp, w, add_one(id_of(cs, "product.q"), 1)));
  EXPECT_TRUE(rejected(*comp, w, add_one(c.id, 2)));
  // The realized program states the source mod_97 (a b) c, its target the
  // predicate's equation, its quotient owned by it; the plan holds no
  // separate record.
  const compiler::ExportMeta meta{"product", "wide", "c0ffee", "run-0", 0};
  const std::string plan = compiler::export_lean_plan(*comp, meta);
  EXPECT_EQ(plan.find("productModEqualities"), std::string::npos);
  const auto prog = compiler::build_program(*comp, meta);
  for (const auto &x : compiler::program_errors(prog)) ADD_FAILURE() << x;
  for (const auto &x : compiler::module_errors(prog)) ADD_FAILURE() << x;
  // Its derivation: productMod from ivl lhs, nat Q and ivl R, which the
  // C++ check accepts, and refuses mutated.
  ir::Certificates c0;
  const ir::Program P = compiler::build_ir(*comp, c0);
  size_t pid = SIZE_MAX;
  for (size_t i = 0; i < P.predicates.size(); ++i)
    if (P.predicates[i].name == "product") pid = i;
  ASSERT_NE(pid, SIZE_MAX);
  const ir::Predicate &q = P.predicates[pid];
  EXPECT_EQ(q.body, ir::Predicate::kMod);
  EXPECT_EQ(q.q, "97");
  EXPECT_EQ(q.mod.form, ir::ModForm::kProduct);
  EXPECT_EQ(q.mod.qmax, "10788");
  ASSERT_TRUE(q.mod.target.has_value());
  EXPECT_EQ(c0.deriv_gaps.at(pid), "");
  ASSERT_FALSE(c0.derivations.at(pid).empty());
  EXPECT_EQ(c0.derivations[pid].back().rule, ir::DStep::kProductMod);
  EXPECT_EQ(c0.derivations[pid].back().premises.size(), 3u);
  expect_product_mutants(P, c0, pid);
}

// x and y nonnegative below 100 honestly (Slack), c = x + y below 200:
// the integer equality derives their common maximum, the planner may
// establish any bound up to it, an honest proof verifies, and a negative
// x (p - 1, with y = c + 1) is rejected. A Slack request no integer
// equality reads fails the range lowering.
TEST(GordieHoweIntEqual, SlackDerived) {
  Sys cs("gh-int-slack");
  auto &A = cs.domain(env().a_profile(), "A");
  const auto x = A.priv(Subfield{}, "x", 4);
  const auto y = A.priv(Subfield{}, "y", 4);
  const auto c = A.priv(Subfield{}, "c", 4, depends_on(x, y),
                        [](const AElt &u, const AElt &v) {
                          return af().addf(u, v);
                        });
  assert_range(x, 100, Slack{}, "x");
  assert_range(y, 100, Slack{}, "y");
  assert_range(c, 200, "c");
  assert_int_equal(x + y, c, "sum");
  auto comp = compile(cs, table_profile());
  const std::string r = comp->report();
  // 2 (m - 1) - 0 < p: m = (p + 1) / 2, capped at p - 100 + 100.
  const Bound p = field_characteristic(af());
  const Bound m = 100 + ((p - 1) / 2 - 99);
  has(r, "assert_int_equal 'sum': the Slack request 'x' below 100 may "
         "establish any bound up to " + bound_str(m));
  has(r, "certify:sum.noWrap");
  const auto &rx = comp->realization("x");
  EXPECT_GE(rx.established, Bound(100));
  EXPECT_LE(rx.established, m);
  Assignment w;
  w.set(x, values({3, 99, 0, 50}));
  w.set(y, values({5, 99, 7, 0}));
  EXPECT_TRUE(honest(*comp, w));
  // x = -1, y = 8: the field equation holds with c = 7, x's range does
  // not.
  Assignment bad;
  AV xs = values({3, 99, 0, 50});
  xs[2] = af().negf(af().one());
  bad.set(x, xs);
  bad.set(y, values({5, 99, 8, 0}));
  EXPECT_TRUE(rejected(*comp, bad, [](size_t, SysValue &) {}));

  Sys cs2("gh-int-slack-unread");
  auto &A2 = cs2.domain(env().a_profile(), "A");
  const auto z = A2.priv(Subfield{}, "z", 4);
  assert_range(z, 100, Slack{}, "z");
  has(compile_error(cs2, table_profile()),
      "range request 'z' of domain A (Slack): no assert_int_equal reading "
      "its value derived its maximum");
}

// A value without a request that a two-root predicate constrains: x in
// {m, 97 - m} with m below 50 lies in [0, 97] (the hull of [0, 49] and
// [48, 97]), which assert_int_equal reads. A factor that reads x twice
// over gives no interval. A view takes the hull of its sources'.
TEST(GordieHoweIntEqual, RootsAndViews) {
  Sys cs("gh-int-roots");
  auto &A = cs.domain(env().a_profile(), "A");
  const auto m = A.priv(Subfield{}, "m", 4);
  const auto x = A.priv(Subfield{}, "x", 4);
  const auto u = A.priv(Subfield{}, "u", 4);
  const auto y = A.priv(Subfield{}, "y", 4);
  assert_range(m, 50, "m");
  assert_range(y, 99, "y");
  assert_zero((m - x) * (m - (97 - x)), "roots");
  assert_zero((m - 2 * u) * (m - u), "double");
  assert_int_equal(x + 1, y, "shift");
  const Bound p = field_characteristic(af());
  const Graph &g = cs.graph();
  auto bound = [&](size_t id) {
    return compiler::range_internal::request_bound(A, g, p, id);
  };
  using I = compiler::range_internal::Interval;
  EXPECT_EQ(compiler::range_internal::root_hull(A, g, p, x.id, bound),
            (I{0, 97}));
  EXPECT_FALSE(compiler::range_internal::root_hull(A, g, p, u.id, bound));
  const auto v = gather(std::vector<Ref<AF, Subfield<>, Committed>>{m, y},
                        {Coord{0, 1}, Coord::zero(), Coord{1, 2}});
  EXPECT_EQ(bound(v.id), (I{0, 98}));
  auto comp = compile(cs, table_profile());
  has(comp->report(), "assert_int_equal 'shift': lhs in [1, 98], rhs in "
                      "[0, 98]");
}

// Vanishing products of more than two roots: a hand-written chain
// (b + 1) b (b - 1) (b - 2) puts b in [-1, 2]; a balanced tree of
// (z - m), m < 8, behind a nonzero scaling puts z in [0, 7]; Expr::prod over
// (w - c), c in {3, 5, 9}, puts w in [3, 9]; and two views of v (its
// halves), each a product (v_j - 0) ... (v_j - 3), put v in [0, 3]. A view
// covering half of q bounds nothing, and a factor with no root form
// (t t + 1) leaves t without an interval.
TEST(GordieHoweIntEqual, RootsOfProducts) {
  Sys cs("gh-int-roots-products");
  auto &A = cs.domain(env().a_profile(), "A");
  const auto b = A.priv(Subfield{}, "b", 4);
  const auto z = A.priv(Subfield{}, "z", 4);
  const auto w = A.priv(Subfield{}, "w", 4);
  const auto v = A.priv(Subfield{}, "v", 4);
  const auto q = A.priv(Subfield{}, "q", 4);
  const auto t = A.priv(Subfield{}, "t", 4);
  const Expr<AF> eb = b;
  assert_zero((eb + 1) * eb * (eb - 1) * (eb - 2), "b");
  std::vector<Expr<AF>> level;
  for (size_t m = 0; m < 8; ++m) level.push_back(Expr<AF>(z) - m);
  while (level.size() > 1) {
    std::vector<Expr<AF>> next;
    for (size_t i = 0; i < level.size(); i += 2)
      next.push_back(level[i] * level[i + 1]);
    level = next;
  }
  assert_zero(af().of_scalar(5) * level[0], "z");
  const auto cs3 = constant(af(), AV{af().of_scalar(3), af().of_scalar(5),
                                     af().of_scalar(9)});
  const Expr<AF> wc = Expr<AF>(w).reshape(Shape{4, 1}) - cs3;
  assert_zero(wc.prod(1), "w");
  for (size_t h = 0; h < 2; ++h) {
    const Expr<AF> vh = v.slice(2 * h, 2 * h + 2);
    assert_zero(vh * (vh - 1) * (vh - 2) * (vh - 3),
                "v" + std::to_string(h));
  }
  const Expr<AF> qh = q.slice(0, 2);
  assert_zero(qh * (qh - 1) * (qh - 2), "q");
  const Expr<AF> et = t;
  assert_zero((et * et + 1) * (et - 1), "t");
  const Bound p = field_characteristic(af());
  const Graph &g = cs.graph();
  auto bound = [&](size_t id) {
    return compiler::range_internal::request_bound(A, g, p, id);
  };
  using I = compiler::range_internal::Interval;
  auto hull = [&](size_t id) {
    return compiler::range_internal::root_hull(A, g, p, id, bound);
  };
  EXPECT_FALSE(hull(b.id));
  EXPECT_EQ(hull(z.id), (I{0, 7}));
  EXPECT_EQ(hull(w.id), (I{3, 9}));
  EXPECT_EQ(hull(v.id), (I{0, 3}));
  EXPECT_FALSE(hull(q.id));
  EXPECT_FALSE(hull(t.id));
  // b's roots are -1 .. 2: a negative root bounds nothing.
  const auto b1 = A.priv(Subfield{}, "b1", 4);
  const Expr<AF> e1 = b1;
  assert_zero(e1 * (e1 - 1) * (e1 - 2) * (e1 - 3), "b1");
  EXPECT_EQ(hull(b1.id), (I{0, 3}));
}

// ------------------------------------------------------------ ranges --

// x in [0, 1000) and y = x + 1: x = 1010 violates the range request alone
// (y = x + 1 still holds). The prover's check names the request before any
// domain proves; a prover that skips its checks completes a proof the
// verifier rejects.
TEST(GordieHoweRange, ProverChecksRequests) {
  Sys cs("gh-range-prover-check");
  auto &A = cs.domain(env().a_profile(), "A");
  const auto x = A.priv(Subfield{}, "x", 4);
  const auto y = A.priv(Subfield{}, "y", 4, depends_on(x),
                        [](const AElt &v) { return af().addf(v, af().one()); });
  assert_range(x, 1000, "x");
  assert_equal(y, x + 1, "y");
  auto comp = compile(cs, table_profile());
  Assignment good;
  good.set(x, values({0, 1, 500, 999}));
  EXPECT_TRUE(honest(*comp, good));
  Assignment bad;
  bad.set(x, values({0, 1, 1010, 999}));
  auto prep = comp->prepare({});
  SecureRandomEngine rng;
  std::string why;
  try {
    prep.prove(bad, rng);
  } catch (const std::runtime_error &e) {
    why = e.what();
  }
  has(why, "prover: the range request 'x' does not hold");
  ProveOptions opt;
  opt.require_satisfied = false;
  std::vector<uint8_t> proof;
  EXPECT_NO_THROW(proof = prep.prove(bad, rng, opt));
  EXPECT_FALSE(prep.verify(proof));
}

// ------------------------------------------------------------- conv --

TEST(GordieHoweConv, Operators) {
  const AF &f = af();
  const size_t n = 64;
  const auto psi = ops::FieldNtt<AF>::root(f, 2 * n);
  ASSERT_TRUE(psi.has_value());
  std::mt19937_64 g(5);
  auto rnd = [&](size_t k) {
    AV v(k);
    for (auto &x : v) x = f.of_scalar(g() >> 2);
    return v;
  };
  // <y, M^-1 x> = <(M^-1)^T y, x>, and INTT inverts the transform.
  {
    const ops::InverseNttOperator<AF> op(f, n, *psi);
    const AV x = rnd(n), y = rnd(n);
    AV mx(n), ty(n);
    op.apply(x.data(), mx.data());
    op.transpose_apply(y.data(), ty.data());
    AElt l = f.zero(), r = f.zero();
    for (size_t i = 0; i < n; ++i) {
      f.add(l, f.mulf(y[i], mx[i]));
      f.add(r, f.mulf(ty[i], x[i]));
    }
    EXPECT_EQ(l, r);
    ops::NegacyclicNtt<AF> ntt(f, n, *psi);
    auto z = x;
    ntt.forward(z);
    AV back(n);
    op.apply(z.data(), back.data());
    EXPECT_EQ(back, x);
  }
  // sum_t w_t sum_j u_j L_j(W, t) = constant + <a, W> for the operand
  // map's adjoint a, with two tables and with one shared.
  for (bool shared : {false, true}) {
    const size_t M = 32, la = 12, lb = shared ? 12 : 9, R = 3;
    const auto rt = ops::FieldNtt<AF>::root(f, 2 * M);
    ASSERT_TRUE(rt.has_value());
    typename compiler::SpectralConvMap<AF>::Side sa{0, R, la, {0, 1, 2}};
    typename compiler::SpectralConvMap<AF>::Side sb{shared ? 0 : R * la, R,
                                                    lb, {0, 1, 0}};
    const size_t z_at = shared ? R * la : R * la + R * lb;
    const compiler::SpectralConvMap<AF> map(f, M, *rt, sa, sb, z_at,
                                            z_at + 3 * M);
    const AV w = rnd(map.words()), wt = rnd(map.instances()), u = rnd(3);
    const auto opv = map.apply(f, w);
    AElt lhs = f.zero();
    for (size_t t = 0; t < opv.size(); ++t)
      for (size_t j = 0; j < 3; ++j)
        f.add(lhs, f.mulf(wt[t], f.mulf(u[j], opv[t][j])));
    AV a;
    AElt k;
    map.adjoint(f, wt, u, a, k);
    AElt rhs = k;
    for (size_t i = 0; i < w.size(); ++i) f.add(rhs, f.mulf(a[i], w[i]));
    EXPECT_EQ(lhs, rhs) << "shared=" << shared;
    // The operands are the transforms of the rows (zero-padded).
    ops::NegacyclicNtt<AF> ntt(f, M, *rt);
    AV row(M, f.zero());
    std::copy(w.begin() + long(sb.at + 0 * lb), w.begin() + long(sb.at + lb),
              row.begin());
    ntt.forward(row);
    EXPECT_EQ(opv[2 * M + 5][1], row[5]);
  }
  // AcyclicConv against the schoolbook product, and its transpose.
  {
    Sys cs("gh-acyclic");
    auto &A = cs.domain(env().a_profile(), "A");
    const std::vector<uint64_t> hv = {3, 1, 4, 1, 5};
    AV h = values(hv);
    const auto hc = A.constant("h", h);
    const auto op = ops::AcyclicConv(hc, 7, ops::EntryBound{8});
    const auto mat = std::make_shared<ops::AcyclicConvOperator<AF>>(f, 7, h, 16);
    EXPECT_EQ(op.spec->rows, 11u);
    EXPECT_EQ(op.spec->cols, 7u);
    const std::vector<uint64_t> xv = {2, 7, 1, 8, 2, 8, 1};
    AV y(11);
    mat->apply(values(xv).data(), y.data());
    EXPECT_EQ(y, values(schoolbook(xv, hv, 7, 5)));
    const AV yy = rnd(11), xx = rnd(7);
    AV my(11), tx(7);
    mat->apply(xx.data(), my.data());
    mat->transpose_apply(yy.data(), tx.data());
    AElt l = f.zero(), r = f.zero();
    for (size_t i = 0; i < 11; ++i) f.add(l, f.mulf(yy[i], my[i]));
    for (size_t i = 0; i < 7; ++i) f.add(r, f.mulf(tx[i], xx[i]));
    EXPECT_EQ(l, r);
    EXPECT_EQ(op.spec->row_sum, Bound(5 * 7));
  }
}

const ConvRealization kRealizations[] = {
    ConvRealization::kDirect, ConvRealization::kBatch, ConvRealization::kAuto};

// Rates under which the circuit (CIRCUIT) or the batch costs 1 per unit
// and the other 1000. Every packing chain these tests weigh costs the
// same, so each tree keeps its default chain.
compiler::PlacementRates cheap_rates(bool circuit) {
  compiler::PlacementRates r;
  r.source = "synthetic";
  for (const std::vector<size_t> &c : std::vector<std::vector<size_t>>{
           {1, 4}, {1, 2, 4}, {16, 128}, {16, 32, 128}, {16, 64, 128}})
    r.stage.chains.push_back({c, 1, 1, 1, 1, 1, 1});
  r.gkr_term = circuit ? 1 : 1000;
  r.commit_sub = 1;
  r.commit_full = 1;
  r.triple = 1e6;
  const double b = circuit ? 1000 : 1;
  r.batch = {{compiler::BatchEval::kSubfield, b, b, b, b, b, b, b, b}};
  return r;
}

// conv(x, y) = c over the integers under realization R, x [3][5] and
// y [3][4] digits below 16 (ROWS: x and y rows of one value X [3][5],
// rows {0, 1, 2} and {0, 1, 0}: two squares), against the schoolbook
// product c, committed by its generator. NONAFFINE states
// (conv(x, y) - c)^2 = 0 in place of the integer equality; RATES, when
// set, are A's.
struct ConvSys {
  Sys cs;
  Ref<AF> x, y, c;
  std::vector<uint64_t> xv, yv;
  ConvSys(ConvRealization r, bool rows, bool nonaffine = false,
          const compiler::PlacementRates *rates = nullptr)
      : cs(std::string("gh-conv-") + conv_realization_name(r) +
           (rows ? "-rows" : "") + (nonaffine ? "-nonaffine" : "")) {
    auto p = env().a_profile();
    if (rates) p.rates = *rates;
    auto &A = cs.domain(p, "A");
    xv = {1, 15, 3, 9, 0, 7, 7, 2, 15, 4, 5, 11, 0, 13, 6};
    yv = rows ? std::vector<uint64_t>{} : std::vector<uint64_t>{
                                              8, 1, 15, 2, 3, 3, 14, 9,
                                              6, 0, 12, 15};
    x = A.priv(Subfield{}, "x", Shape{3, 5});
    assert_range(x, 16, "x");
    Expr<AF> ex = Expr<AF>(x), ey;
    size_t ly = 4;
    if (rows) {
      ex = Expr<AF>(x).reindex(std::vector<size_t>{0, 1, 2}, 0);
      ey = Expr<AF>(x).reindex(std::vector<size_t>{0, 1, 0}, 0);
      ly = 5;
    } else {
      y = A.priv(Subfield{}, "y", Shape{3, 4});
      assert_range(y, 16, "y");
      ey = Expr<AF>(y);
    }
    const size_t lo = 5 + ly - 1;
    auto gen = [ly](const std::vector<uint64_t> &a) {
      std::vector<uint64_t> b;
      for (size_t r : {0, 1, 0})
        b.insert(b.end(), a.begin() + long(r * 5),
                 a.begin() + long((r + 1) * 5));
      return schoolbook(a, b, 5, ly);
    };
    if (rows) {
      c = A.priv(Subfield{}, "c", Shape{3, lo}, depends_on(x), gen);
    } else {
      c = A.priv(Subfield{}, "c", Shape{3, lo}, depends_on(x, y),
                 [](const std::vector<uint64_t> &a,
                    const std::vector<uint64_t> &b) {
                   return schoolbook(a, b, 5, 4);
                 });
    }
    assert_range(c, 1024, "c");
    if (nonaffine) {
      const Expr<AF> d = conv(ex, ey).pin(r) - c;
      assert_zero(d * d, "conv");
    } else {
      assert_int_equal(conv(ex, ey).pin(r), c, "conv");
    }
  }
  Assignment witness() const {
    Assignment w;
    w.set(x, values(xv));
    if (!yv.empty()) w.set(y, values(yv));
    return w;
  }
};

TEST(GordieHoweConv, Realizations) {
  for (bool rows : {false, true}) {
    for (ConvRealization r : kRealizations) {
      const std::string nm =
          std::string(conv_realization_name(r)) + (rows ? " rows" : "");
      ConvSys s(r, rows);
      auto comp = compile(s.cs, table_profile());
      const std::string rep = comp->report();
      // Under unit rates (no measured ones): the batch where it beats the
      // direct form, the default, by more than the margin (97 against 108
      // units), the direct form on rows (193 against 82).
      const ConvRealization want =
          r != ConvRealization::kAuto ? r
          : rows                      ? ConvRealization::kDirect
                                      : ConvRealization::kBatch;
      has(rep, std::string("conv 'conv.conv': [3] x (5 * ") +
                   (rows ? "5) -> 9, M = 16, " : "4) -> 8, M = 8, ") +
                   conv_realization_name(want));
      const Assignment w = s.witness();
      EXPECT_TRUE(honest(*comp, w)) << nm;
      EXPECT_TRUE(rejected(*comp, w, add_one(s.c.id, 4))) << nm;
      const bool batch = want == ConvRealization::kBatch;
      const size_t id = id_of(s.cs, batch ? "conv.conv.z" : "conv.conv.c");
      EXPECT_TRUE(rejected(*comp, w, add_one(id, 3))) << nm;
    }
  }
}

// conv inside a non-affine predicate, (conv(x, y) - c)^2 = 0: the batch
// commits C with the affine rows C = INTT(z)[0, lo), and the predicate
// reads C. A wrong result c, a wrong C and a wrong z are rejected; the
// direct form commits C as before. The pinned batch is the batch.
// The realized program of conv(x, y) = c under each realization: the
// export succeeds and passes the program's checks, and conv(x, y) is
// exported as its source expression, two views of B (lx + ly - 1) lx
// coordinates (x[b][t] and y[b][k - t], the zero coordinate outside
// 0 <= k - t < ly), their product summed over t (`.sum lx`). The views'
// index maps, read back from the program, give the schoolbook product.
TEST(GordieHoweConv, ProgramExport) {
  for (bool rows : {false, true}) {
    for (ConvRealization r : kRealizations) {
      const std::string nm =
          std::string(conv_realization_name(r)) + (rows ? " rows" : "");
      ConvSys s(r, rows);
      auto comp = compile(s.cs, table_profile());
      const compiler::ExportMeta meta{"conv", "wide", "c0ffee", "run-0", 0};
      compiler::ProgramData p;
      ASSERT_NO_THROW(p = compiler::build_program(*comp, meta)) << nm;
      examples::check_program(p);
      const size_t B = 3, lx = 5, ly = rows ? 5 : 4, lo = lx + ly - 1;
      std::vector<size_t> ia, ib;
      for (size_t b = 0; b < B; ++b)
        for (size_t k = 0; k < lo; ++k)
          for (size_t t = 0; t < lx; ++t) {
            const bool in = t <= k && k - t < ly;
            ia.push_back(in ? b * lx + t : B * lx);
            ib.push_back(in ? b * ly + (k - t) : B * ly);
          }
      const auto &maps = p.index_maps;
      EXPECT_NE(std::find(maps.begin(), maps.end(), ia), maps.end()) << nm;
      EXPECT_NE(std::find(maps.begin(), maps.end(), ib), maps.end()) << nm;
      EXPECT_NE(p.text.find(".apply (.sum 5)"), std::string::npos) << nm;
      // The views over x and y (rows: rows {0, 1, 2} and {0, 1, 0} of x),
      // each followed by its zero coordinate, summed over t.
      std::vector<uint64_t> yv = s.yv;
      if (rows)
        for (size_t q : {0, 1, 0})
          for (size_t j = 0; j < lx; ++j) yv.push_back(s.xv[q * lx + j]);
      std::vector<uint64_t> xz = s.xv, yz = yv;
      xz.push_back(0);
      yz.push_back(0);
      std::vector<uint64_t> got(B * lo, 0);
      for (size_t i = 0; i < ia.size(); ++i) got[i / lx] += xz[ia[i]] * yz[ib[i]];
      EXPECT_EQ(got, schoolbook(s.xv, yv, lx, ly)) << nm;
    }
  }
}

// A public operator with no schema name and no sparse rows (a matrix
// given as code, as pq_mdoc.h's FipsNtt) is exported as `.rowDot M R W`,
// M a constant of its R W entries in row-major order; applied to x [2][3]
// it is batched (`.batched 2`).
class DenseTestOperator final : public LinearOperator<AF> {
 public:
  static constexpr uint64_t kM[3][3] = {{1, 2, 0}, {0, 1, 5}, {7, 0, 1}};
  size_t rows() const override { return 3; }
  size_t cols() const override { return 3; }
  void apply(const AElt *x, AElt *y) const override {
    for (size_t r = 0; r < 3; ++r) {
      y[r] = af().zero();
      for (size_t c = 0; c < 3; ++c)
        af().add(y[r], af().mulf(af().of_scalar(kM[r][c]), x[c]));
    }
  }
  void transpose_apply(const AElt *y, AElt *x) const override {
    for (size_t c = 0; c < 3; ++c) {
      x[c] = af().zero();
      for (size_t r = 0; r < 3; ++r)
        af().add(x[c], af().mulf(af().of_scalar(kM[r][c]), y[r]));
    }
  }
};

TEST(GordieHoweConv, DenseOperatorExport) {
  Sys cs("gh-dense-op-export");
  auto &A = cs.domain(env().a_profile(), "A");
  const auto x = A.priv(Subfield{}, "x", Shape{2, 3});
  const auto y = A.priv(Subfield{}, "y", Shape{2, 3});
  const Op<AF> m = linear_operator<AF>({
      .name = "dense_test",
      .rows = 3,
      .cols = 3,
      .make = [](const AF &) { return std::make_shared<DenseTestOperator>(); },
      .field = &af(),
  });
  assert_equal(m(x), y, "dense");
  auto comp = compile(cs, table_profile());
  const compiler::ExportMeta meta{"dense", "wide", "c0ffee", "run-0", 0};
  compiler::ProgramData p;
  ASSERT_NO_THROW(p = compiler::build_program(*comp, meta));
  examples::check_program(p);
  EXPECT_NE(p.text.find("(.batched 2 (.rowDot "), std::string::npos) << p.text;
  EXPECT_NE(p.text.find(" 3 3))"), std::string::npos) << p.text;
  const std::vector<std::string> want = {"1", "2", "0", "0", "1",
                                         "5", "7", "0", "1"};
  bool found = false;
  for (const auto &v : p.values) found = found || (v.kind == "constant" && v.entries == want);
  EXPECT_TRUE(found) << "no constant holding the matrix";
}

TEST(GordieHoweConv, NonAffine) {
  for (bool rows : {false, true}) {
    for (ConvRealization r : kRealizations) {
      const std::string nm =
          std::string(conv_realization_name(r)) + (rows ? " rows" : "");
      ConvSys s(r, rows, true);
      auto comp = compile(s.cs, table_profile());
      const std::string rep = comp->report();
      // Unit rates: the direct form where the rule decides.
      const bool batch = r == ConvRealization::kBatch;
      has(rep, std::string("M = ") + (rows ? "16, " : "8, ") +
                   (batch ? "batch with C committed" : "direct"));
      const Assignment w = s.witness();
      EXPECT_TRUE(honest(*comp, w)) << nm;
      EXPECT_TRUE(rejected(*comp, w, add_one(s.c.id, 4))) << nm;
      EXPECT_TRUE(rejected(*comp, w, add_one(id_of(s.cs, "conv.conv.c"), 3)))
          << nm;
      if (batch)
        EXPECT_TRUE(
            rejected(*comp, w, add_one(id_of(s.cs, "conv.conv.z"), 3)))
            << nm;
    }
  }
}

// The placement rule's choice by A's rates: the direct form, the default,
// where the circuit is cheap, the batch, named cheapest, where the batch
// is, each with the candidates' costs in the report; a pin overrides the
// rates.
TEST(GordieHoweConv, Rates) {
  for (bool circuit : {true, false}) {
    for (bool nonaffine : {false, true}) {
      const compiler::PlacementRates rates = cheap_rates(circuit);
      ConvSys s(ConvRealization::kAuto, false, nonaffine, &rates);
      auto comp = compile(s.cs, table_profile());
      const std::string rep = comp->report();
      has(rep, std::string("M = 8, ") + (circuit ? "direct" : "batch") +
                   (circuit || !nonaffine ? "" : " with C committed") +
                   (circuit ? " (default: " : " (cheapest: "));
      const Assignment w = s.witness();
      EXPECT_TRUE(honest(*comp, w)) << circuit << nonaffine;
      EXPECT_TRUE(rejected(*comp, w, add_one(s.c.id, 4)))
          << circuit << nonaffine;
      ConvSys pinned(circuit ? ConvRealization::kBatch
                             : ConvRealization::kDirect,
                     false, nonaffine, &rates);
      has(compile(pinned.cs, table_profile())->report(),
          std::string("M = 8, ") + (circuit ? "batch" : "direct"));
    }
  }
}

// conv(x, h) with h public and its entry bound: the affine public
// convolution, no realization.
TEST(GordieHoweConv, PublicOperand) {
  Sys cs("gh-conv-public");
  auto &A = cs.domain(env().a_profile(), "A");
  const std::vector<uint64_t> hv = {3, 1, 4, 1, 5};
  const auto h = A.constant("h", values(hv));
  const auto x = A.priv(Subfield{}, "x", Shape{2, 6});
  assert_range(x, 16, "x");
  const auto c = A.priv(Subfield{}, "c", Shape{2, 10}, depends_on(x),
                        [hv](const std::vector<uint64_t> &a) {
                          std::vector<uint64_t> hh;
                          for (int r = 0; r < 2; ++r)
                            hh.insert(hh.end(), hv.begin(), hv.end());
                          return schoolbook(a, hh, 6, 5);
                        });
  assert_range(c, 1024, "c");
  assert_int_equal(conv(x, h, ops::EntryBound{6}), c, "pub");
  auto comp = compile(cs, table_profile());
  const std::string rep = comp->report();
  EXPECT_EQ(rep.find("conv '"), std::string::npos) << rep;
  has(rep, "assert_int_equal 'pub': lhs in [0, 375]");
  Assignment w;
  w.set(x, values({1, 2, 3, 4, 5, 6, 15, 0, 15, 0, 15, 15}));
  EXPECT_TRUE(honest(*comp, w));
  EXPECT_TRUE(rejected(*comp, w, add_one(c.id, 7)));
}


// --------------------------------------------------- operator intervals --

int64_t pick(std::mt19937_64 &g, int64_t lo, int64_t hi) {
  return lo + int64_t(g() % uint64_t(hi - lo + 1));
}
AElt elt_of(int64_t x) {
  return x >= 0 ? af().of_scalar(uint64_t(x)) : af().negf(af().of_scalar(uint64_t(-x)));
}
// The centred integer of a base-field element of small magnitude.
int64_t centred_of(const AElt &e) {
  const Bound p = field_characteristic(af());
  const Bound x = nat_of(af(), e);
  return x <= (p - 1) / 2 ? int64_t(uint64_t(x)) : -int64_t(uint64_t(p - x));
}
bool within(int64_t v, const IntInterval &iv) {
  return SignedInt(v) >= iv.first && SignedInt(v) <= iv.second;
}

// int_interval's product, acyclic and negacyclic intervals are the
// extremes over the operands' vertices (their every assignment of ends),
// and hold every random interior point.
TEST(GordieHoweOpInterval, Primitives) {
  namespace ii = int_interval;
  std::mt19937_64 g(11);
  for (int trial = 0; trial < 60; ++trial) {
    const int64_t a0 = pick(g, -9, 9), a1 = pick(g, a0, 12);
    const int64_t b0 = pick(g, -9, 9), b1 = pick(g, b0, 12);
    const IntInterval A{a0, a1}, B{b0, b1};
    // a b.
    {
      const auto P = ii::product(A, B, 300);
      ASSERT_TRUE(P);
      int64_t lo = a0 * b0, hi = lo;
      for (int64_t u : {a0, a1})
        for (int64_t v : {b0, b1}) {
          lo = std::min(lo, u * v);
          hi = std::max(hi, u * v);
        }
      EXPECT_EQ(*P, (IntInterval{lo, hi}));
    }
    // The negacyclic product h x of length n <= 3 over every vertex, and
    // the acyclic convolution of lengths la, lb <= 3.
    for (size_t n = 1; n <= 3; ++n) {
      const auto N = ii::negacyclic(n, A, B, 300);
      ASSERT_TRUE(N);
      int64_t lo = 0, hi = 0;
      bool first = true;
      for (uint64_t mask = 0; mask < (uint64_t(1) << (2 * n)); ++mask) {
        std::vector<int64_t> h(n), x(n);
        for (size_t j = 0; j < n; ++j) {
          h[j] = (mask >> j) & 1 ? a1 : a0;
          x[j] = (mask >> (n + j)) & 1 ? b1 : b0;
        }
        for (size_t i = 0; i < n; ++i) {
          int64_t c = 0;
          for (size_t j = 0; j < n; ++j) {
            const size_t k = (i + n - j) % n;
            c += j <= i ? h[j] * x[k] : -h[j] * x[k];
          }
          lo = first ? c : std::min(lo, c);
          hi = first ? c : std::max(hi, c);
          first = false;
        }
      }
      EXPECT_EQ(*N, (IntInterval{lo, hi})) << "n = " << n;
      for (size_t la = 1; la <= 3; ++la) {
        const size_t lb = n;
        const auto C = ii::acyclic(std::min(la, lb), A, B, 300);
        ASSERT_TRUE(C);
        int64_t clo = 0, chi = 0;
        bool cf = true;
        for (uint64_t mask = 0; mask < (uint64_t(1) << (la + lb)); ++mask) {
          std::vector<int64_t> u(la), v(lb), c(la + lb - 1, 0);
          for (size_t j = 0; j < la; ++j) u[j] = (mask >> j) & 1 ? a1 : a0;
          for (size_t j = 0; j < lb; ++j) v[j] = (mask >> (la + j)) & 1 ? b1 : b0;
          for (size_t x = 0; x < la; ++x)
            for (size_t y = 0; y < lb; ++y) c[x + y] += u[x] * v[y];
          for (int64_t z : c) {
            clo = cf ? z : std::min(clo, z);
            chi = cf ? z : std::max(chi, z);
            cf = false;
          }
        }
        EXPECT_EQ(*C, (IntInterval{clo, chi})) << "la = " << la << ", lb = " << lb;
      }
    }
  }
  // Past the cap: none.
  EXPECT_FALSE(ii::product({0, SignedInt(1) << 200}, {0, SignedInt(1) << 200}, 300));
  EXPECT_FALSE(ii::negacyclic(4, {0, SignedInt(1) << 150}, {0, SignedInt(1) << 150}, 300));
}

// Each operator kind's own interval (OpSpec::interval, given its operand's
// and its dependency's intervals) holds its instantiated matrix applied to
// random operands drawn from them, ends included: NegacyclicConv,
// PolyMatVec and PolyBroadcast in coefficient form with and without an
// entry bound, AcyclicConv with and without one (a kernel of either sign
// bounds nothing), a sparse matrix by its row sum; FromDigits without a
// declared row sum bounds nothing.
TEST(GordieHoweOpInterval, Operators) {
  Sys cs("gh-op-intervals");
  auto &A = cs.domain(env().a_profile(), "A");
  const size_t n = 4;
  const auto h = A.pub(Subfield{}, "h", n);
  const auto a = A.pub(Subfield{}, "a", Shape{2, 3, n});
  const auto t = A.pub(Subfield{}, "t", Shape{3, n});
  const auto k = A.pub(Subfield{}, "k", 5);
  struct Case {
    std::string what;
    Op<AF> op;
    IntInterval H;
    bool bounded;
  };
  const std::vector<Case> cases = {
      {"negacyclic_conv", ops::NegacyclicConv(h), {-3, 5}, true},
      {"negacyclic_conv entry", ops::NegacyclicConv(h, ops::EntryBound{6}), {0, 5}, true},
      {"poly_mat_vec", ops::PolyMatVec(a, ops::Form::kCoefficients), {-2, 4}, true},
      {"poly_mat_vec entry", ops::PolyMatVec(a, ops::EntryBound{5}), {0, 4}, true},
      {"poly_broadcast", ops::PolyBroadcast(t, ops::Form::kCoefficients), {0, 7}, true},
      {"poly_broadcast entry", ops::PolyBroadcast(t, ops::EntryBound{8}), {0, 7}, true},
      {"acyclic_conv", ops::AcyclicConv(k, 6), {0, 9}, true},
      {"acyclic_conv entry", ops::AcyclicConv(k, 6, ops::EntryBound{10}), {0, 9}, true},
      {"acyclic_conv signed", ops::AcyclicConv(k, 6), {-1, 3}, false},
      {"from_digits unbounded", FromDigits(af(), 3, af().of_scalar(5)), {0, 0}, false},
      {"sparse", ops::sparse_matrix(af(), "rows", 4, {{{0, 2}, {3, 1}}, {{1, 7}}, {}}),
       {0, 0}, true},
  };
  std::mt19937_64 g(3);
  const IntInterval X{-4, 6};
  for (const auto &c : cases) {
    const OpSpec<AF> &op = *c.op.spec;
    const auto iv = op.interval(X, [&](size_t) { return std::optional(c.H); }, 300);
    if (!c.bounded) {
      EXPECT_FALSE(iv) << c.what;
      continue;
    }
    ASSERT_TRUE(iv) << c.what;
    for (int trial = 0; trial < 200; ++trial) {
      std::vector<AV> deps;
      OpArgs args;
      for (size_t dk = 0; dk < op.deps.size(); ++dk) {
        AV v;
        for (size_t j = 0; j < cs.graph().nodes.at(op.deps[dk]).n; ++j)
          v.push_back(elt_of(trial < 2 ? int64_t(trial ? c.H.second : c.H.first)
                                       : pick(g, int64_t(c.H.first), int64_t(c.H.second))));
        deps.push_back(std::move(v));
      }
      for (const auto &v : deps) args.push(field_tag<AF>(), &v);
      const auto m = op.make(args);
      AV x(op.cols), y(op.rows);
      for (auto &e : x)
        e = elt_of(trial < 4 ? (trial % 2 ? 6 : -4) : pick(g, -4, 6));
      m->apply(x.data(), y.data());
      for (const auto &e : y)
        ASSERT_TRUE(within(centred_of(e), *iv))
            << c.what << ": " << centred_of(e) << " outside [" << int_str(iv->first)
            << ", " << int_str(iv->second) << "]";
    }
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
