// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: assert_in (membership.h) in the ML-DSA native field of both
// parameter sets (F_q^6 at the ROM parameters, F_q^11 at the QROM
// parameters) and in F_p256.
//
//   In/<profile>.MultiColumnFixed   a table of 12 rows of arity 3: fixed
//                                   kappa packing, an honest proof, a record
//                                   off the table and a wrong multiplicity
//                                   rejected
//   In/<profile>.ArityBoundary      arity [K : E] packs with kappa, arity
//                                   [K : E] + 1 with gamma
//   In/<profile>.SeveralTables      three tables and a range request in one
//                                   domain: one alpha, one gamma, the plan
//                                   records and charges
//   In/<profile>.TableCap           a 12-row table above a cap of 8 fails
//                                   the compile; the domain's max_table
//                                   admits it with a report warning
//   In/<profile>.RangeIsSugar       assert_in(x, range_table(n)) is the
//                                   system assert_range(x, n) declares
//   In/<profile>.CommittedMemory    a read-only memory: a committed array
//                                   with its addresses as the table, reads
//                                   at private positions; alpha tests the
//                                   array; a wrong read rejected
//   In/<profile>.CommittedTableValue a committed [R, A] value as the table,
//                                   fixed kappa and gamma packing; a record
//                                   off the table rejected
//   InP256.ChallengePacking         F_p256 ([K : E] = 1): arity 2 packs with
//                                   gamma, arity 1 needs no packing

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <set>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "params/param_sets.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/examples/p256/p256_testing.h"
#include "gordiehowe/membership.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

// The examples' profiles and list-radius choices.
using namespace ::proofs::gordiehowe::examples;  // NOLINT

template <class C>
bool has(const C &c, const std::string &s) {
  return c->report().find(s) != std::string::npos;
}

// Proves W against statement ST and verifies; false when the prover
// refuses (CHEATING false) or the verifier rejects. TAMPER, when given,
// changes a generator's output (a cheating prover).
template <class C, class A, class Tm = std::nullptr_t>
bool proves(const C &c, const A &st, const A &w, bool cheating,
            Tm tamper = nullptr) {
  auto prep = c->prepare(st);
  typename std::decay_t<decltype(*c)>::ProveOptions opt;
  opt.require_satisfied = !cheating;
  if constexpr (!std::is_same_v<Tm, std::nullptr_t>) opt.tamper = tamper;
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(w, rng, opt));
  } catch (const std::runtime_error &) {
    return false;
  }
}

template <class P>
struct In : testing::Test {
  using Env = examples::mldsa::Env<P>;
  using Sys = typename Env::Sys;
  using AF = typename Env::AF;
  using Elt = typename AF::Elt;
  using V = std::vector<Elt>;
  static const Env &env() {
    static const Env *e = new Env;
    return *e;
  }
  static const AF &af() { return env().af; }
  static auto profile() {
    return examples::domain_profile<P>(env().af, env().rsa);
  }
  // [K : E]
  static constexpr size_t kKE = ExtensionTraits<AF>::degree;
  // R rows of arity A, entries below 1000, row j distinct from row j'.
  static V rows_of(size_t R, size_t A) {
    V v;
    for (size_t j = 0; j < R; ++j)
      for (size_t k = 0; k < A; ++k)
        v.push_back(af().of_scalar((37 * j + 101 * k + 7 * j * k) % 1000));
    return v;
  }
  // The records PICK of ROWS.
  static V pick(const V &rows, size_t A, const std::vector<size_t> &js) {
    V out;
    for (size_t j : js)
      for (size_t k = 0; k < A; ++k) out.push_back(rows[j * A + k]);
    return out;
  }
  // An element outside the prime field: a + kappa b.
  static Elt ext(uint64_t a, uint64_t b) {
    return af().addf(
        af().of_scalar(a),
        af().mulf(lib::permutation::selection_kappa(af()), af().of_scalar(b)));
  }
};
using Profiles = testing::Types<param_sets::QROMParams, param_sets::ROMParams>;
struct ProfileNames {
  template <class P>
  static std::string GetName(int) {
    return P::kId;
  }
};
TYPED_TEST_SUITE(In, Profiles, ProfileNames);

TYPED_TEST(In, MultiColumnFixed) {
  using T = TestFixture;
  const size_t R = 12, A = 3, n = 5;
  typename T::Sys cs("gh-in-fixed");
  auto &D = cs.domain(T::profile(), "A");
  auto rows = D.pub(Subfield{}, "rows", Shape{R, A});
  auto recs = D.priv(Subfield{}, "recs", Shape{n, A});
  const auto t = in_table(cs, "t", rows);
  assert_in(recs, t, "m");
  const auto c = compile(cs);
  EXPECT_TRUE(has(c, "in t: 1 request (m), 5 records, 12 rows of arity 3, "
                     "fixed kappa packing"))
      << c->report();
  const auto rv = T::rows_of(R, A);
  typename T::Sys::Assignment st;
  st.set(rows, rv);
  typename T::Sys::Assignment w;
  w.set(recs, T::pick(rv, A, {2, 7, 2, 11, 0}));
  EXPECT_TRUE(proves(c, st, w, false));
  // A record off the table: refused by the prover, rejected by the
  // verifier.
  auto off = T::pick(rv, A, {2, 7, 2, 11, 0});
  T::af().add(off[4], T::af().one());
  typename T::Sys::Assignment w2;
  w2.set(recs, off);
  EXPECT_FALSE(proves(c, st, w2, false));
  EXPECT_FALSE(proves(c, st, w2, true));
  // A wrong multiplicity.
  size_t mid = SIZE_MAX;
  for (size_t i = 0; i < cs.graph().nodes.size(); ++i)
    if (cs.graph().nodes[i].name == "t.mult") mid = i;
  ASSERT_NE(mid, SIZE_MAX);
  EXPECT_FALSE(proves(c, st, w, true, [mid](size_t at, auto &x) {
    if (at == mid) T::af().add(std::get<typename T::V>(x)[2], T::af().one());
  }));
}

TYPED_TEST(In, ArityBoundary) {
  using T = TestFixture;
  const size_t R = 8;
  for (size_t A : {T::kKE, T::kKE + 1}) {
    SCOPED_TRACE(A);
    typename T::Sys cs("gh-in-arity");
    auto &D = cs.domain(T::profile(), "A");
    auto rows = D.pub(Subfield{}, "rows", Shape{R, A});
    auto recs = D.priv(Subfield{}, "recs", Shape{3, A});
    assert_in(recs, in_table(cs, "t", rows), "m");
    const auto c = compile(cs);
    if (A == T::kKE) {
      EXPECT_TRUE(has(c, "fixed kappa packing")) << c->report();
    } else {
      EXPECT_TRUE(has(c, "gamma packing (arity " + std::to_string(A) +
                             " > [K : E] = " + std::to_string(T::kKE) + ")"))
          << c->report();
    }
    const auto rv = T::rows_of(R, A);
    typename T::Sys::Assignment st;
    st.set(rows, rv);
    typename T::Sys::Assignment w;
    w.set(recs, T::pick(rv, A, {1, 6, 1}));
    EXPECT_TRUE(proves(c, st, w, false));
    auto off = T::pick(rv, A, {1, 6, 1});
    T::af().add(off[A - 1], T::af().one());
    typename T::Sys::Assignment w2;
    w2.set(recs, off);
    EXPECT_FALSE(proves(c, st, w2, true));
  }
}

TYPED_TEST(In, SeveralTables) {
  using T = TestFixture;
  typename T::Sys cs("gh-in-tables");
  auto &D = cs.domain(T::profile(), "A");
  // t1: subfield rows of arity 2 (fixed kappa), two requests.
  auto rows1 = D.pub(Subfield{}, "rows1", Shape{10, 2});
  auto a = D.priv(Subfield{}, "a", Shape{3, 2});
  auto b = D.priv(Subfield{}, "b", Shape{2, 2});
  // t2: rows outside the prime field, arity 2 (gamma).
  auto rows2 = D.pub(Field{}, "rows2", Shape{6, 2});
  auto c2 = D.priv(Field{}, "c", Shape{4, 2});
  // t3: a constant table of arity 1.
  auto rows3 = D.constant("rows3",
                          {T::af().of_scalar(3), T::af().of_scalar(5),
                           T::af().of_scalar(9)});
  auto d = D.priv(Subfield{}, "d", 4);
  // A range request in the same domain keeps its own lowering and shares
  // alpha:A.
  auto x = D.priv(Subfield{}, "x", 4);
  const auto t1 = in_table(cs, "t1", rows1);
  const auto t2 = in_table(cs, "t2", rows2);
  const auto t3 = in_table(cs, "t3", rows3);
  assert_in(a, t1, "a");
  assert_in(b, t1, cs.scope("other").name("b"));
  assert_in(c2, t2, "c");
  assert_in(d, t3, "d");
  assert_in(x, range_table(100), "x");
  const auto c = compile(cs);
  EXPECT_TRUE(has(c, "in t1: 2 requests (a, other.b), 5 records, 10 rows of "
                     "arity 2, fixed kappa packing"))
      << c->report();
  EXPECT_TRUE(has(c, "in t2: 1 request (c), 4 records, 6 rows of arity 2, "
                     "gamma packing (the rows are not typed subfield values)"))
      << c->report();
  EXPECT_TRUE(has(c, "in t3: 1 request (d), 4 records, 3 rows of arity 1, "
                     "no packing"))
      << c->report();
  size_t alphas = 0, gammas = 0;
  for (const auto &nd : cs.graph().nodes) {
    alphas += nd.name == "alpha:A";
    gammas += nd.name == "in.gamma:A";
  }
  EXPECT_EQ(alphas, 1u);
  EXPECT_EQ(gammas, 1u);
  // The plan records: one assert-in gadget per table, and the charges.
  const auto &rec = cs.graph().records;
  std::vector<std::vector<std::pair<std::string, SignedInt>>> g;
  for (const auto &x : rec.gadgets)
    if (x.kind == "assert-in") g.push_back(x.params);
  ASSERT_EQ(g.size(), 3u);
  auto param = [](const auto &ps, const std::string &k) {
    for (const auto &[n, v] : ps)
      if (n == k) return v;
    return SignedInt(-1);
  };
  EXPECT_EQ(param(g[0], "packing"), 1);
  EXPECT_EQ(param(g[1], "packing"), 2);
  EXPECT_EQ(param(g[2], "packing"), 1);
  EXPECT_EQ(param(g[1], "gammaDegree"), 6);
  EXPECT_EQ(param(g[0], "alphaDegree"), 5 + 10 - 1);
  EXPECT_EQ(param(g[0], "extensionDegree"), __int128(T::kKE));
  Bound ac = 0, gc = 0;
  for (const auto &ch : rec.charges) {
    if (ch.label == "alpha:A") ac = ch.degree;
    if (ch.label == "in.gamma:A") gc = ch.degree;
  }
  // Alpha's charge is the tables' and the range lowering's: per public
  // table n + R - 1 (the cleared identity, no pole), each range table's T
  // and, per group, N + T - 1.
  Bound range_charge = 0;
  std::set<Bound> range_sizes;
  for (const auto &t : D.range_tables()) {
    if (range_sizes.insert(t.table).second)
      range_charge += t.table;
    range_charge += Bound(t.static_needles + t.dynamic_needles) + t.table - 1;
  }
  EXPECT_FALSE(range_sizes.empty());
  EXPECT_EQ(ac, Bound((5 + 9) + (4 + 5) + (4 + 2)) + range_charge);
  EXPECT_EQ(gc, Bound(6));
  // An honest proof, then a record of t2 off its table.
  const auto r1 = T::rows_of(10, 2);
  typename T::V r2;
  for (size_t j = 0; j < 6; ++j) {
    r2.push_back(T::ext(j + 1, 2 * j + 3));
    r2.push_back(T::ext(5 * j, 7));
  }
  typename T::Sys::Assignment st;
  st.set(rows1, r1).set(rows2, r2);
  auto witness = [&](bool wrong) {
    typename T::Sys::Assignment w;
    auto cv = T::pick(r2, 2, {5, 0, 5, 3});
    if (wrong) T::af().add(cv[3], T::af().one());
    w.set(a, T::pick(r1, 2, {0, 9, 4}))
        .set(b, T::pick(r1, 2, {4, 4}))
        .set(c2, cv)
        .set(d, typename T::V{T::af().of_scalar(9), T::af().of_scalar(3),
                              T::af().of_scalar(9), T::af().of_scalar(5)})
        .set(x, typename T::V{T::af().of_scalar(0), T::af().of_scalar(99),
                              T::af().of_scalar(42), T::af().of_scalar(7)});
    return w;
  };
  EXPECT_TRUE(proves(c, st, witness(false), false));
  EXPECT_FALSE(proves(c, st, witness(true), true));
}

// The table cap (RangePolicy::max_table): a public table above it fails
// the compile, naming the table and its rows; the domain's max_table admits
// it, and the report lists it as a warning.
TYPED_TEST(In, TableCap) {
  using T = TestFixture;
  const size_t R = 12, n = 3;
  CompileProfile p;
  p.range.max_table = 8;
  auto build = [&](Bound domain_cap) {
    auto cs = std::make_unique<typename T::Sys>("gh-in-cap");
    auto &D = cs->domain(T::profile(), "A");
    if (domain_cap != 0) D.max_table(domain_cap);
    auto rows = D.pub(Subfield{}, "rows", R);
    auto recs = D.priv(Subfield{}, "recs", n);
    assert_in(recs, in_table(*cs, "t", rows), "m");
    return cs;
  };
  {
    auto cs = build(0);
    try {
      (void)compile(*cs, p);
      ADD_FAILURE() << "a table above the cap compiled";
    } catch (const CompileError &e) {
      const std::string m = e.what();
      EXPECT_NE(m.find("assert_in 't': the table has 12 rows, above the "
                       "table cap 8"),
                std::string::npos)
          << m;
    }
  }
  auto cs = build(16);
  const auto c = compile(*cs, p);
  EXPECT_TRUE(has(c, "warning: public table t has 12 rows, above the cap 8 "
                     "(max_table of domain A)"))
      << c->report();
}

TYPED_TEST(In, RangeIsSugar) {
  using T = TestFixture;
  auto build = [](bool sugar) {
    typename T::Sys cs("gh-in-range");
    auto &D = cs.domain(T::profile(), "A");
    auto x = D.priv(Subfield{}, "x", 8);
    auto y = D.priv(Subfield{}, "y", 8);
    if (sugar) {
      assert_in(x, range_table(300), "x");
      assert_in(y, range_table(2048), "y");
      assert_in(x + 2 * y, range_table(1 << 22), "xy");
      assert_in(y - x, range_table(1 << 22), "yx");
    } else {
      assert_range(x, 300, "x");
      assert_range(y, 2048, "y");
      assert_range(x + 2 * y, 1 << 22, "xy");
      assert_range(y - x, 1 << 22, "yx");
    }
    const auto c = compile(cs);
    return std::make_pair(c->digest(), c->report());
  };
  const auto [d0, r0] = build(false);
  const auto [d1, r1] = build(true);
  EXPECT_EQ(d0, d1);
  EXPECT_EQ(r0, r1);
}

// A read-only memory: the table is (j, mem[j]) for a committed array mem
// of R cells, the expression concatenating the constant addresses with
// mem; the records are reads (address, value) at private positions. The
// circuit reads the rows, so alpha tests mem. An honest proof verifies; a
// read whose value is not the memory's is refused by the prover and
// rejected by the verifier.
TYPED_TEST(In, CommittedMemory) {
  using T = TestFixture;
  const size_t R = 16, n = 6;
  typename T::Sys cs("gh-in-memory");
  auto &D = cs.domain(T::profile(), "A");
  auto mem = D.priv(Subfield{}, "mem", Shape{R});
  auto reads = D.priv(Subfield{}, "reads", Shape{n, 2});
  std::vector<uint64_t> addr(R);
  for (size_t j = 0; j < R; ++j) addr[j] = j;
  const auto memory =
      D.constant(addr, Shape{R, 1}).concat(mem.reshape(Shape{R, 1}), 1);
  assert_in(reads, in_table(cs, "memory", memory), "reads");
  const auto c = compile(cs);
  EXPECT_TRUE(has(c, "in memory: 1 request (reads), 6 records, 16 committed "
                     "rows of arity 2, fixed kappa packing"))
      << c->report();
  // Alpha is drawn after mem, which it tests.
  const auto &N = cs.graph().nodes;
  size_t alpha = SIZE_MAX;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == "alpha:A") alpha = i;
  ASSERT_NE(alpha, SIZE_MAX);
  const auto &tests = c->tests_of(alpha);
  EXPECT_NE(std::find(tests.begin(), tests.end(), mem.id), tests.end());
  EXPECT_EQ(c->phase(mem), 0u);
  EXPECT_EQ(c->phase(alpha), 1u);
  typename T::V mv;
  for (size_t j = 0; j < R; ++j) mv.push_back(T::af().of_scalar(977 * j + 5));
  auto witness = [&](bool wrong) {
    typename T::V r;
    for (size_t j : {3, 15, 3, 0, 9, 7}) {
      r.push_back(T::af().of_scalar(j));
      r.push_back(mv[j]);
    }
    // Address 9 read with address 7's value.
    if (wrong) r[9] = mv[7];
    typename T::Sys::Assignment w;
    w.set(mem, mv).set(reads, r);
    return w;
  };
  typename T::Sys::Assignment st;
  EXPECT_TRUE(proves(c, st, witness(false), false));
  EXPECT_FALSE(proves(c, st, witness(true), false));
  EXPECT_FALSE(proves(c, st, witness(true), true));
}

// A committed table as a value: rows [R, 2] typed Subfield, packed with
// the fixed kappa, and a table of arity [K : E] + 1, packed with gamma. A
// record that is not a row is rejected in both; the counts of the honest
// proof are checked against the committed rows.
TYPED_TEST(In, CommittedTableValue) {
  using T = TestFixture;
  const size_t R = 10;
  for (size_t A : {size_t(2), T::kKE + 1}) {
    SCOPED_TRACE(A);
    typename T::Sys cs("gh-in-committed");
    auto &D = cs.domain(T::profile(), "A");
    auto rows = D.priv(Subfield{}, "rows", Shape{R, A});
    auto recs = D.priv(Subfield{}, "recs", Shape{4, A});
    assert_in(recs, in_table(cs, "t", rows), "m");
    const auto c = compile(cs);
    EXPECT_TRUE(has(c, A == 2 ? std::string("fixed kappa packing")
                              : "gamma packing (arity"))
        << c->report();
    const auto rv = T::rows_of(R, A);
    auto witness = [&](bool wrong) {
      auto r = T::pick(rv, A, {9, 0, 4, 9});
      if (wrong) T::af().add(r[A], T::af().one());
      typename T::Sys::Assignment w;
      w.set(rows, rv).set(recs, r);
      return w;
    };
    typename T::Sys::Assignment st;
    EXPECT_TRUE(proves(c, st, witness(false), false));
    EXPECT_FALSE(proves(c, st, witness(true), false));
    EXPECT_FALSE(proves(c, st, witness(true), true));
  }
}

// ---------------------------------------------------------------- F_p256 --

TEST(InP256, ChallengePacking) {
  using namespace examples::mdoc::p256_testing;
  const F &f = fp();
  Sys cs("gh-in-p256");
  auto &D = cs.domain(profile(), "A");
  auto rows = D.pub(Field{}, "rows", Shape{9, 2});
  auto recs = D.priv(Field{}, "recs", Shape{4, 2});
  auto rows1 = D.pub(Field{}, "rows1", 5);
  auto one = D.priv(Field{}, "one", 3);
  assert_in(recs, in_table(cs, "t", rows), "m");
  assert_in(one, in_table(cs, "u", rows1), "o");
  const auto c = compile(cs);
  EXPECT_TRUE(has(c, "in t: 1 request (m), 4 records, 9 rows of arity 2, "
                     "gamma packing (arity 2 > [K : E] = 1)"))
      << c->report();
  EXPECT_TRUE(has(c, "in u: 1 request (o), 3 records, 5 rows of arity 1, "
                     "no packing"))
      << c->report();
  Vec rv, uv;
  for (size_t j = 0; j < 18; ++j) rv.push_back(f.of_scalar(1000003 * j + 17));
  for (size_t j = 0; j < 5; ++j) uv.push_back(f.of_scalar(31 * j + 2));
  Assignment st;
  st.set(rows, rv).set(rows1, uv);
  auto witness = [&](bool wrong) {
    Vec r;
    for (size_t j : {8, 1, 1, 4}) {
      r.push_back(rv[2 * j]);
      r.push_back(rv[2 * j + 1]);
    }
    // A record whose components lie in two rows, a pair off the table.
    if (wrong) r[1] = rv[3];
    Assignment w;
    w.set(recs, r).set(one, Vec{uv[4], uv[0], uv[4]});
    return w;
  };
  EXPECT_TRUE(proves(c, st, witness(false), false));
  EXPECT_FALSE(proves(c, st, witness(true), false));
  EXPECT_FALSE(proves(c, st, witness(true), true));
}

}  // namespace
}  // namespace proofs::gordiehowe
