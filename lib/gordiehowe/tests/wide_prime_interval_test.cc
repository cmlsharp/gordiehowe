// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: interval propagation in prime fields with p > 2^127, whose bounds
// and intervals are wide_int.h's fixed-width integers.
//
//   Fp128Interval.Unrequested     an Fp128 value without a request has
//                                 [0, p - 1]; requested values and a wide
//                                 operator coefficient keep theirs
//   Fp128Interval.RequestAtP      assert_range(x, p) gives request_bound
//                                 [0, p - 1], and is implied by the value's
//                                 type with that interval
//   Fp128Interval.IntEqualWrap    assert_int_equal(x + y, z) with x, y
//                                 unrequested fails to compile (x = p - 1,
//                                 y = 1, z = 0 would satisfy it mod p)
//   Fp128Interval.IntEqualAtP     the same with x, y range-checked below p
//   Fp128Interval.RangeAtPProves  assert_range(x, p): x = p - 1 proves
//   P256Interval.Unrequested      an F_p256 value without a request has
//                                 [0, p - 1] (p itself, above 2^255); a
//                                 requested value keeps its interval
//   P256Interval.AboveFloor       intervals above 2^127 (2^200 a, a sum of
//                                 two 2^130 bounds) and an integer
//                                 equality whose span, about 2^131, the
//                                 compiler certifies against p, not the
//                                 floor 2^127
//   P256Interval.RangeAboveFloor  an implied range request in [2^127, p)
//                                 is realized; one reaching p is refused
//   P256Interval.IntEqualWrap     assert_int_equal(x + y, z) with x, y
//                                 unrequested fails to compile; with x, y
//                                 below 2^30 it compiles

#include <cstdio>
#include <memory>
#include <string>
#include <vector>

#include "params/param_sets.h"
#include "gordiehowe/examples/p256/p256_testing.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

using I = compiler::range_internal::Interval;

CompileProfile table_profile() {
  CompileProfile cp;
  cp.name = "wide-prime";
  return cp;
}

bool has(const std::string &text, const std::string &want) {
  if (text.find(want) != std::string::npos) return true;
  ADD_FAILURE() << "missing: " << want << "\n" << text;
  return false;
}

// The interval of X in domain A as assert_int_equal computes it (against
// p itself), or none with WHY.
template <class F, class X>
std::optional<I> int_equal_interval(const F &f, const Domain<F> &A,
                                    const Graph &g, const X &x,
                                    std::string &why) {
  const Bound p = field_characteristic(f);
  const auto in_prime = compiler::range_internal::prime_node(A, g);
  return compiler::range_internal::expr_interval(
      f, p, A.prime == Space::kField, g, expr_node(x),
      [&](size_t id) {
        return compiler::range_internal::request_bound(A, g, p, id);
      },
      why, &in_prime);
}

// --------------------------------------------------------------- Fp128 --

using P = param_sets::ROMParamsFp128;
using E = examples::rsa::Env<P>;
using FSys = E::Sys;
using AF = Fp128<>;
using AV = std::vector<AF::Elt>;

const E &fenv() {
  static const E *e = new E;
  return *e;
}
Domain<AF> &fp128_domain(FSys &cs) {
  return cs.domain(
      examples::domain_profile<P>(fenv().af, fenv().rsa.factory()), "A");
}

TEST(Fp128Interval, Unrequested) {
  const AF &f = fenv().af;
  // Fp128's p exceeds 2^127.
  const Bound p = field_characteristic(f);
  ASSERT_FALSE(characteristic_wide(f));
  ASSERT_GT(p, Bound(1) << 127);
  FSys cs("fp128-iv");
  auto &A = fp128_domain(cs);
  ASSERT_EQ(A.prime, Space::kField);
  const auto u = A.priv(Subfield{}, "u", 1);
  const auto a = A.priv(Subfield{}, "a", 1);
  const auto b = A.priv(Subfield{}, "b", 1);
  assert_range(a, 8, "a");
  assert_range(b, Bound(1) << 100, "b");
  const Graph &g = cs.graph();
  std::string why;
  EXPECT_EQ(int_equal_interval(f, A, g, u, why),
            (I{0, SignedInt(p - 1)}));
  EXPECT_EQ(int_equal_interval(f, A, g, a, why), (I{0, 7}));
  EXPECT_EQ(int_equal_interval(f, A, g, b, why),
            (I{0, (SignedInt(1) << 100) - 1}));
  // A wide sparse_matrix coefficient: 2^100 a, a in [0, 7].
  const auto op =
      ops::sparse_matrix_wide(f, "wide", 1, {{{0, Bound(1) << 100}}});
  EXPECT_EQ(int_equal_interval(f, A, g, op(as_expr(a)), why),
            (I{0, SignedInt(7) << 100}));
  // -a: a negative coefficient's signed representative.
  EXPECT_EQ(int_equal_interval(f, A, g, -1 * as_expr(a), why), (I{-7, 0}));
}

TEST(Fp128Interval, RequestAtP) {
  const AF &f = fenv().af;
  const Bound p = field_characteristic(f);
  FSys cs("fp128-at-p");
  auto &A = fp128_domain(cs);
  const auto x = A.priv(Subfield{}, "x", 1);
  assert_range(x, p, "x");
  const Graph &g = cs.graph();
  size_t id = SIZE_MAX;
  for (size_t i = 0; i < g.nodes.size(); ++i)
    if (g.nodes[i].name == "x") id = i;
  ASSERT_NE(id, SIZE_MAX);
  // N - 1 = p - 1, exact.
  EXPECT_EQ(compiler::range_internal::request_bound(A, g, p, id),
            (I{0, SignedInt(p - 1)}));
  std::string why;
  EXPECT_EQ(int_equal_interval(f, A, g, x, why), (I{0, SignedInt(p - 1)}));
}

// The reviewer's case: x + y can be p, so the compile must fail. Compiled,
// x = p - 1, y = 1, z = 0 satisfies x + y = z mod p although x + y != z.
TEST(Fp128Interval, IntEqualWrap) {
  FSys cs("fp128-wrap");
  auto &A = fp128_domain(cs);
  const auto x = A.priv(Subfield{}, "x", 1);
  const auto y = A.priv(Subfield{}, "y", 1);
  const auto z = A.priv(Subfield{}, "z", 1);
  assert_range(z, 1024, "z");
  assert_int_equal(as_expr(x) + as_expr(y), z, "wrap");
  std::string err;
  try {
    compile(cs, table_profile());
  } catch (const CompileError &e) {
    err = e.what();
  }
  std::printf("FP128_WRAP %s\n", err.c_str());
  has(err, "assert_int_equal 'wrap': the sides can wrap around p");
}

// x, y range-checked below p (implied by type): the same wrap, refused.
TEST(Fp128Interval, IntEqualAtP) {
  const Bound p = field_characteristic(fenv().af);
  FSys cs("fp128-wrap-at-p");
  auto &A = fp128_domain(cs);
  const auto x = A.priv(Subfield{}, "x", 1);
  const auto y = A.priv(Subfield{}, "y", 1);
  const auto z = A.priv(Subfield{}, "z", 1);
  assert_range(x, p, "x");
  assert_range(y, p, "y");
  assert_range(z, 1024, "z");
  assert_int_equal(as_expr(x) + as_expr(y), z, "wrap");
  std::string err;
  try {
    compile(cs, table_profile());
  } catch (const CompileError &e) {
    err = e.what();
  }
  has(err, "assert_int_equal 'wrap': the sides can wrap around p");
}

// assert_range(x, p) is implied by x's type, its interval [0, p - 1]
// printed exactly; x = p - 1 proves.
TEST(Fp128Interval, RangeAtPProves) {
  const AF &f = fenv().af;
  const Bound p = field_characteristic(f);
  FSys cs("fp128-range-p");
  auto &A = fp128_domain(cs);
  const auto x = A.priv(Subfield{}, "x", 1);
  const auto z = A.priv(Subfield{}, "z", 1);
  assert_range(x, p, "x");
  assert_range(z, 1024, "z");
  auto comp = compile(cs, table_profile());
  const std::string r = comp->report();
  has(r, "x: implied (by the value's type), interval [0, " +
             bound_str(p - 1) + "] -> bound " + bound_str(p));
  FSys::Assignment w;
  w.set(x, AV{f.mone()});
  w.set(z, AV{f.of_scalar(1023)});
  auto prep = comp->prepare({});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
}

// -------------------------------------------------------------- F_p256 --

namespace pt = examples::mdoc::p256_testing;

TEST(P256Interval, Unrequested) {
  const auto &f = pt::fp();
  // F_p256's characteristic is a Bound above 2^255, which every lowering
  // compares with.
  const Bound p = field_characteristic(f);
  ASSERT_TRUE(characteristic_wide(f));
  ASSERT_GT(p, Bound(1) << 255);
  pt::Sys cs("p256-iv");
  auto &A = cs.domain(pt::profile(), "A");
  ASSERT_EQ(A.prime, Space::kField);
  const auto u = A.priv(Field{}, "u", 1);
  const auto a = A.priv(Field{}, "a", 1);
  assert_range(a, Bound(1) << 100, "a");
  const Graph &g = cs.graph();
  std::string why;
  EXPECT_EQ(int_equal_interval(f, A, g, u, why),
            (I{0, SignedInt(p - 1)}));
  EXPECT_EQ(int_equal_interval(f, A, g, a, why),
            (I{0, (SignedInt(1) << 100) - 1}));
  EXPECT_EQ(int_equal_interval(f, A, g, as_expr(a) + as_expr(a), why),
            (I{0, (SignedInt(1) << 101) - 2}));
}

TEST(P256Interval, AboveFloor) {
  const auto &f = pt::fp();
  pt::Sys cs("p256-above-floor");
  auto &A = cs.domain(pt::profile(), "A");
  const auto a = A.priv(Field{}, "a", 1);
  // b, c below 2^130 and z below 2^131 as their bits: the range lowering
  // compares with the floor 2^127, the integer equality with p.
  const auto bb = A.priv(Bit{}, "bb", 130);
  const auto cb = A.priv(Bit{}, "cb", 130);
  const auto zb = A.priv(Bit{}, "zb", 131);
  assert_range(a, 8, "a");
  const auto b = as_expr(bb.from_digits(2));
  const auto c = as_expr(cb.from_digits(2));
  const auto z = as_expr(zb.from_digits(2));
  const Graph &g = cs.graph();
  std::string why;
  // 2^200 a, a in [0, 7]: a wide coefficient.
  const pt::Elt k =
      f.to_montgomery(Fp256Nat(std::array<uint64_t, 4>{0, 0, 0, 256}));
  EXPECT_EQ(int_equal_interval(f, A, g, k * as_expr(a), why),
            (I{0, SignedInt(7) << 200}));
  EXPECT_EQ(int_equal_interval(f, A, g, b + c, why),
            (I{0, (SignedInt(1) << 131) - 2}));
  // b + c = z over the integers: the span 2^131 - 1 exceeds the floor
  // 2^127 and lies below p.
  assert_int_equal(b + c, z, "wide");
  auto comp = compile(cs, table_profile());
  has(comp->report(), "assert_int_equal 'wide': lhs in [0, " +
                          bound_str((Bound(1) << 131) - 2) + "], rhs in [0, " +
                          bound_str((Bound(1) << 131) - 1) + "]");
  has(comp->report(), "span " + bound_str((Bound(1) << 131) - 1) + " < p = " +
                          bound_str(field_characteristic(f)));
}

// A range request on an F_p256 value whose interval lies between 2^127
// and p is realized (implied by the interval of 200 bits' integer); one
// whose interval reaches p (257 bits) is refused.
TEST(P256Interval, RangeAboveFloor) {
  {
    pt::Sys cs("p256-range-above-floor");
    auto &A = cs.domain(pt::profile(), "A");
    const auto bb = A.priv(Bit{}, "bb", 200);
    // One looked-up request, so that the domain's LogUp challenge tests
    // a value.
    assert_range(A.priv(Field{}, "a", 1), 8, "a");
    assert_range_implied(as_expr(bb.from_digits(2)), Bound(1) << 200,
                         MaxBound{Bound(1) << 200}, "wide");
    auto comp = compile(cs, table_profile());
    has(comp->report(), "wide: implied, interval [0, " +
                            bound_str((Bound(1) << 200) - 1) + "] -> bound " +
                            bound_str(Bound(1) << 200));
  }
  {
    pt::Sys cs("p256-range-at-p");
    auto &A = cs.domain(pt::profile(), "A");
    const auto cb = A.priv(Bit{}, "cb", 257);
    assert_range(A.priv(Field{}, "a", 1), 8, "a");
    assert_range_implied(as_expr(cb.from_digits(2)), Bound(1) << 257,
                         MaxBound{Bound(1) << 257}, "over");
    std::string err;
    try {
      compile(cs, table_profile());
    } catch (const CompileError &e) {
      err = e.what();
    }
    std::printf("P256_RANGE_AT_P %s\n", err.c_str());
    has(err, "'over'");
  }
}

TEST(P256Interval, IntEqualWrap) {
  {
    pt::Sys cs("p256-wrap");
    auto &A = cs.domain(pt::profile(), "A");
    const auto x = A.priv(Field{}, "x", 1);
    const auto y = A.priv(Field{}, "y", 1);
    const auto z = A.priv(Field{}, "z", 1);
    assert_range(z, 1024, "z");
    assert_int_equal(as_expr(x) + as_expr(y), z, "wrap");
    std::string err;
    try {
      compile(cs, table_profile());
    } catch (const CompileError &e) {
      err = e.what();
    }
    has(err, "assert_int_equal 'wrap': the sides can wrap around p");
  }
  {
    pt::Sys cs("p256-sum");
    auto &A = cs.domain(pt::profile(), "A");
    const auto x = A.priv(Field{}, "x", 1);
    const auto y = A.priv(Field{}, "y", 1);
    const auto z = A.priv(Field{}, "z", 1);
    assert_range(x, Bound(1) << 30, "x");
    assert_range(y, Bound(1) << 30, "y");
    assert_range(z, Bound(1) << 31, "z");
    assert_int_equal(as_expr(x) + as_expr(y), z, "sum");
    auto comp = compile(cs, table_profile());
    has(comp->report(), "assert_int_equal 'sum': lhs in [0, " +
                            bound_str((Bound(1) << 31) - 2) + "]");
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
