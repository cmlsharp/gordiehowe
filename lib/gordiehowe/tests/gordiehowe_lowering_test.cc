// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: the lowerings.
//   - storage binding (bind_view) and its compile checks B1-B5;
//   - range requests: the planner's realizations, the histograms and the
//     fraction tree, interval propagation, the Sum budget needle;
//   - compile(System&, profile).
// gordiehowe_lowering_select_test.cc (same binary) holds ordered selection,
// assert_same_bits (the MAC equality across GF(2^256) and Goldilocks^4, and
// within one domain) and the inventory of a Falcon-shaped skeleton. Each
// lowering proves and verifies on an honest witness and rejects a bad one (out
// of range, unequal, unselected) at prove or verify time.

#include "gordiehowe/tests/gordiehowe_lowering_test.h"

namespace proofs::gordiehowe {
namespace {

// ------------------------------------------------------------ binding --

// A phase-0 advice value bound to digits computed from it alone.
struct BindSys {
  Sys cs{"gh-m3-bind"};
  Domain<AF> *A;
  Ref<AF> x, q, d0, d1;
  explicit BindSys(bool bind = true) {
    A = &cs.domain(env().a_profile(), "A");
    x = A->priv(Subfield{}, "x", 2);
    const AF *pf = &af();
    q = A->priv(Subfield{}, "q", 2, depends_on(x),
                      nat([](const std::vector<NatInt> &x) {
                        return std::vector<NatInt>{x[0] + 4096, x[1]};
                      }));
    auto digit = [](unsigned j) {
      return [j](NatInt q) { return (q >> (11 * j)) % 2048; };
    };
    d0 = A->priv(Subfield{}, "d0", 2, depends_on(q), nat(digit(0)));
    d1 = A->priv(Subfield{}, "d1", 2, depends_on(q), nat(digit(1)));
    if (bind) L::bind_view(*A, q, d0 + pf->of_scalar(2048) * d1,
                           "d0 + 2048*d1");
    // q[0] = x[0] + 4096 and q[1] = x[1] read q through its view.
    auto k = A->constant("k", avec({4096, 0}));
    A->affine("q = x + k", q - x - k);
    L::gkr(*A, "q1 = x1", depends_on(q, x),
           [](const auto &lc, const auto &q, const auto &x) {
             lc.assert_eq(q[1], x[1]);
           });
  }
  Assignment witness() const {
    Assignment w;
    w.set(x, avec({17, 3000}));
    return w;
  }
};

TEST(GordieHoweM3, BindingHasNoCellAndProves) {
  BindSys b;
  BindSys plain(false);
  auto c = compile(b.cs);
  auto c0 = compile(plain.cs);
  // q has no cell: two coordinates fewer.
  EXPECT_EQ(c->coordinates(0) + 2, c0->coordinates(0));
  EXPECT_NE(c->report().find("q: no cell; view d0 + 2048*d1"), std::string::npos)
      << c->report();
  EXPECT_NE(c->digest(), c0->digest());
  EXPECT_TRUE(honest(*c, {}, b.witness()));
  // A wrong digit changes the view, which the rows read.
  EXPECT_TRUE(verifier_rejects(*c, {}, b.witness(), set_at(b.d0.id, 0, af().of_scalar(18))));
  EXPECT_TRUE(verifier_rejects(*c, {}, b.witness(), set_at(b.d1.id, 1, af().of_scalar(0))));
}

TEST(GordieHoweM3, BindingChecks) {
  const AF *pf = &af();
  {
    // B1: a derived value is not bound (through an erased handle; a Bit
    // handle is a C++ compile error).
    BindSys b(false);
    auto dv = b.A->derive("dv", b.q + b.x);
    L::bind_view(*b.A, Ref<AF>(dv), b.d0, "d0");
    EXPECT_NE(core_error(b.cs).find("only phase-0 advice and private inputs "
                                   "are bound"),
              std::string::npos)
        << core_error(b.cs);
  }
  {
    // B3: the view reads a cell not computed from q alone.
    BindSys b(false);
    L::bind_view(*b.A, b.q, b.x, "x");
    EXPECT_NE(core_error(b.cs).find("which is not a phase-0 advice cell of "
                                   "domain A computed from 'q' alone"),
              std::string::npos)
        << core_error(b.cs);
  }
  {
    // B3: an operator in the view.
    BindSys b(false);
    auto h = b.A->pub(Field{}, "h", 2);
    L::bind_view(*b.A, b.q, ops::NegacyclicConv(h)(b.d0), "conv");
    EXPECT_NE(core_error(b.cs).find("the view applies the operator "
                                   "'negacyclic_conv'"),
              std::string::npos)
        << core_error(b.cs);
  }
  {
    // B4: a Subfield value viewed through a Field digit.
    BindSys b(false);
    auto f = b.A->priv(Field{}, "f", 2, depends_on(b.q),
                         [](const AV &v) { return v; });
    L::bind_view(*b.A, b.q, f, "f");
    EXPECT_NE(core_error(b.cs).find("viewed through the Field value 'f'"),
              std::string::npos)
        << core_error(b.cs);
  }
  {
    // B2: a quadratic operand is not bound; one binding per node.
    BindSys b(false);
    auto z = b.A->priv(Field{}, "z", 2, depends_on(b.x),
                         [](const AV &v) { return v; });
    auto zd = b.A->priv(Field{}, "zd", 2, depends_on(z),
                          [](const AV &v) { return v; });
    b.A->quadratic(z, z, zd);
    L::bind_view(*b.A, z, zd, "zd");
    EXPECT_NE(core_error(b.cs).find("it is a quadratic triple operand"),
              std::string::npos)
        << core_error(b.cs);
    BindSys t;
    EXPECT_THROW(L::bind_view(*t.A, t.q, t.d0, "again"), CompileError);
  }
  {
    // B5: a late digit.
    BindSys b(false);
    auto g = b.A->challenge("g", depends_on(b.x));
    auto late = b.A->priv(Subfield{}, "late", 2, depends_on(b.q, g),
                            [](const AV &q, const AV &) { return q; });
    L::bind_view(*b.A, b.q, late, "late");
    EXPECT_NE(core_error(b.cs).find("not a phase-0 advice cell"),
              std::string::npos)
        << core_error(b.cs);
  }
}

// --------------------------------------------------------------- range --

// One request of each realization, x = (5, 200, 1500, 2047):
//   a < 2048                direct
//   q < 2048^2              digits 2, q bound
//   a - 128 hb < 128        two-sided 1 (hb < 16, interval)
//   t < 100                 two-sided 1, t bound
//   u < 12289               two-sided 2, u bound
//   392 - Sum(hb) in [393, p - 7680)   direct through Sum
//   lt < 64, late           direct, dynamic histogram of 64
struct RangeSys {
  Sys cs{"gh-m3-range"};
  Domain<AF> *A;
  Ref<AF> x, a, q, hb, t, u, lt, gamma, fill;
  RangeHandle<AF> ra, rq, rhb, rlow, rt, ru, rbudget, rlt;
  RangeSys() {
    A = &cs.domain(env().a_profile(), "A");
    const AF *pf = &af();
    fill = fill_2048(*A);
    x = A->priv(Subfield{}, "x", 4);
    a = A->priv(Subfield{}, "a", 4, depends_on(x), nat([](NatInt v) { return v; }));
    q = A->priv(Subfield{}, "q", 4, depends_on(x),
                      nat([](NatInt v) { return 1000 * v + 7; }));
    hb = A->priv(Subfield{}, "hb", 4, depends_on(x), nat([](NatInt v) { return v / 128; }));
    t = A->priv(Subfield{}, "t", 4, depends_on(x), nat([](NatInt v) { return v % 100; }));
    u = A->priv(Subfield{}, "u", 4, depends_on(x), nat([](NatInt v) { return 5 * v + 1; }));
    auto c7 = A->constant("seven", AV(4, pf->of_scalar(7)));
    A->affine("q = 1000 x + 7", q - pf->of_scalar(1000) * x - c7);
    gamma = A->challenge("gamma", depends_on(x));
    // Late through gamma, a Field challenge, which nat(...) cannot read.
    lt = A->priv(Subfield{}, "lt", 4, depends_on(x, gamma),
                   [pf](const AV &x, const AV &) {
                     AV out;
                     for (const auto &e : x)
                       out.push_back(elt_of_nat(*pf, nat_of(*pf, e) % 64));
                     return out;
                   });
    ra = assert_range(a, 2048, "a");
    rq = assert_range(q, 2048 * 2048, "q");
    rhb = assert_range(hb, 16, MaxBound{(kP - 128) / 128 + 1}, "hb");
    rlow = assert_range(a - pf->of_scalar(128) * hb, 128, "low");
    rt = assert_range(t, 100, "t");
    ru = assert_range(u, 12289, "u");
    auto J = A->constant("J", AV{pf->of_scalar(392)});
    rbudget = assert_range(J - Sum(hb), 393,
                         MaxBound{kP - 4 * 15}, "budget");
    rlt = assert_range(lt, 64, MaxBound{2048}, "lt");
  }
  Assignment witness() const {
    Assignment w;
    w.set(x, avec({5, 200, 1500, 2047}));
    zero_fill(w, fill);
    return w;
  }
};

TEST(GordieHoweM3, RangeRealizations) {
  RangeSys r;
  auto c = compile(r.cs);
  std::printf("%s", c->report().c_str());
  auto kind = [&](RangeHandle<AF> h) { return c->realization(h).kind; };
  EXPECT_EQ(kind(r.ra), RealizationKind::kDirect);
  EXPECT_EQ(c->proven_bound(r.ra), 2048u);
  EXPECT_EQ(kind(r.rq), RealizationKind::kDigits);
  EXPECT_EQ(c->realization(r.rq).k, 2u);
  EXPECT_TRUE(c->realization(r.rq).bound);
  EXPECT_EQ(c->proven_bound(r.rq), Bound(2048) * 2048);
  EXPECT_EQ(kind(r.rhb), RealizationKind::kDirect);
  EXPECT_EQ(kind(r.rlow), RealizationKind::kTwoSided);
  EXPECT_EQ(c->proven_bound(r.rlow), 128u);
  EXPECT_EQ(kind(r.rt), RealizationKind::kTwoSided);
  EXPECT_EQ(c->proven_bound(r.rt), 100u);
  EXPECT_EQ(kind(r.ru), RealizationKind::kTwoSided);
  EXPECT_EQ(c->realization(r.ru).k, 2u);
  EXPECT_TRUE(c->realization(r.ru).bound);
  EXPECT_EQ(c->proven_bound(r.ru), 12289u);
  EXPECT_EQ(kind(r.rbudget), RealizationKind::kDirect);
  EXPECT_EQ(kind(r.rlt), RealizationKind::kDirect);
  // Needles: the fill, a, low (2), t (2), hb, budget (1 coordinate), q (2),
  // u (4) static; lt dynamic with support 64.
  ASSERT_EQ(r.A->range_tables().size(), 1u);
  const auto &tab = r.A->range_tables().at(0);
  EXPECT_EQ(tab.table, 2048u);
  EXPECT_EQ(tab.static_needles, 4096u + 4u * (1 + 2 + 2 + 1 + 2 + 4) + 1);
  EXPECT_EQ(tab.dynamic_needles, 4u);
  EXPECT_EQ(tab.s_dyn, 64u);
  EXPECT_EQ(c->phase(r.lt), 1u);
  EXPECT_EQ(c->phase(Ref<AF>{tab.alpha, 1, &af(), nullptr}), 2u);
}

TEST(GordieHoweM3, RangeProvesAndRejects) {
  RangeSys r;
  auto c = compile(r.cs);
  const auto w = r.witness();
  EXPECT_TRUE(honest(*c, {}, w));
  const AF &f = af();
  // Out of range: a direct needle (and the two-sided low part).
  EXPECT_TRUE(verifier_rejects(*c, {}, w, set_at(r.a.id, 0, f.of_scalar(3000))));
  EXPECT_TRUE(prover_refuses(*c, {}, w, set_at(r.a.id, 0, f.of_scalar(3000))));
  // The two-sided needles of t at t = 100.
  EXPECT_TRUE(verifier_rejects(*c, {}, w, set_at(r.t.id, 1, f.of_scalar(100))));
  // Two-sided: u = 12289 (its high digits wrap).
  EXPECT_TRUE(verifier_rejects(*c, {}, w, set_at(r.u.id, 2, f.of_scalar(12289))));
  // The two-sided low part: hb one too small makes a - 128 hb >= 128.
  EXPECT_TRUE(verifier_rejects(*c, {}, w, set_at(r.hb.id, 3, f.of_scalar(14))));
  // A wrong digit of the bound q.
  EXPECT_TRUE(verifier_rejects(*c, {}, w,
                        set_at(id_of(r.cs, "range.q.d0"), 0, f.of_scalar(1))));
  // A wrong dynamic multiplicity: one count moved between bins.
  const size_t m1 = r.A->range_tables().at(0).m1;
  EXPECT_TRUE(verifier_rejects(*c, {}, w, [&](size_t at, SysValue &v) {
    if (at != m1) return;
    auto &x = std::get<AV>(v);
    f.add(x[5], f.one());
    f.sub(x[6], f.one());
  }));
  // A wrong static multiplicity.
  const size_t m0 = r.A->range_tables().at(0).m0;
  EXPECT_TRUE(verifier_rejects(*c, {}, w, set_at(m0, 0, f.of_scalar(1000))));
}

// Stream bytes that serve fixed bytes, as a forced challenge stream does.
class FixedBytes : public RandomEngine {
 public:
  explicit FixedBytes(std::vector<uint8_t> b) : b_(std::move(b)) {}
  void bytes(uint8_t *buf, size_t n) override {
    for (size_t i = 0; i < n; ++i) buf[i] = b_.at(at_++);
  }

 private:
  std::vector<uint8_t> b_;
  size_t at_ = 0;
};
// The stream bytes on which rng.elt draws X, checked by drawing from them.
std::vector<uint8_t> draw_bytes(const AElt &x) {
  std::vector<uint8_t> b(AF::kBytes);
  af().to_bytes_field(b.data(), x);
  FixedBytes fb(b);
  EXPECT_EQ(fb.elt(af()), x);
  return b;
}

// alpha:<D> is uniform outside [0, T_max): a stream whose first two draws
// are table points 5 and 2047 is drawn a third time, the weights are
// defined, and the proof verifies.
TEST(GordieHoweM3, RangeAlphaRedrawnOffTable) {
  RangeSys r;
  auto c = compile(r.cs);
  const AF &f = af();
  const auto &tab = r.A->range_tables().at(0);
  const std::string label = r.cs.graph().nodes.at(tab.alpha).name;
  EXPECT_EQ(r.cs.graph().nodes.at(tab.alpha).sampler, "field-minus-tables");
  EXPECT_NE(c->report().find(label + ": drawn outside [0, 2048)"),
            std::string::npos)
      << c->report();
  std::vector<uint8_t> prefix = draw_bytes(f.of_scalar(5));
  const std::vector<uint8_t> second = draw_bytes(f.of_scalar(2047));
  prefix.insert(prefix.end(), second.begin(), second.end());
  c->set_challenge_prefix(label, prefix);
  EXPECT_TRUE(honest(*c, {}, r.witness()));
  const AElt alpha = std::get<AV>(c->drawn_challenge(label)).at(0);
  EXPECT_FALSE(compiler::range_internal::in_range_table(f, alpha, 2048));
  EXPECT_EQ(c->drawn_challenge_bytes(label), 3 * AF::kBytes);
  // The membership test: the table's points, and points off it.
  EXPECT_TRUE(compiler::range_internal::in_range_table(f, f.zero(), 2048));
  EXPECT_TRUE(compiler::range_internal::in_range_table(f, f.of_scalar(2047), 2048));
  EXPECT_FALSE(compiler::range_internal::in_range_table(f, f.of_scalar(2048), 2048));
  EXPECT_FALSE(compiler::range_internal::in_range_table(f, f.mone(), 2048));
  AElt ext = f.of_scalar(3);
  ext.e[1] = f.base_field().one();
  EXPECT_FALSE(compiler::range_internal::in_range_table(f, ext, 2048));
}

// A challenge drawn outside a set that reads a prover-chosen value is a
// compile error: the set must be public and fixed before the challenge.
TEST(GordieHoweM3, ChallengeOutsideReadsPublicValuesOnly) {
  Sys cs("gh-m3-outside");
  auto &A = cs.domain(env().a_profile(), "A");
  auto x = A.priv(Subfield{}, "x", 1);
  auto ch = A.challenge_outside("ch", {x.id}, [](const ValueReader &) {
    return std::function<bool(const AElt &)>([](const AElt &) { return false; });
  });
  L::gkr(A, "ch = x", depends_on(ch, x),
         [](const auto &lc, const auto &c, const auto &x) {
           lc.assert_eq(c[0], x[0]);
         });
  const std::string e = compile_error(cs);
  EXPECT_NE(e.find("is drawn outside a set that reads 'x'"), std::string::npos)
      << e;
}

// The budget needle J - Sum(h): honest, then a sum above J.
TEST(GordieHoweM3, BudgetNeedleThroughSum) {
  Sys cs("gh-m3-budget");
  auto &A = cs.domain(env().a_profile(), "A");
  const AF *pf = &af();
  auto fill = fill_2048(A);
  auto h = A.priv(Subfield{}, "h", 4);
  assert_range(h, 2048, "h");
  auto J = A.constant("J", AV{pf->of_scalar(392)});
  auto rb = assert_range(J - Sum(h), 393, MaxBound{kP - 7680},
                      "budget");
  auto c = compile(cs);
  EXPECT_EQ(c->realization(rb).kind, RealizationKind::kDirect);
  Assignment ok, bad;
  ok.set(h, avec({100, 100, 100, 50}));
  bad.set(h, avec({100, 100, 100, 100}));
  zero_fill(ok, fill);
  zero_fill(bad, fill);
  EXPECT_TRUE(honest(*c, {}, ok));
  EXPECT_TRUE(verifier_rejects(*c, {}, bad, [](size_t, SysValue &) {}));
}

TEST(GordieHoweM3, RangeCompileErrors) {
  const AF *pf = &af();
  {
    // No admissible realization of [3000, 4000] under a policy of direct
    // lookups and a table cap of 2048 rows: the only candidate table, 3000,
    // is above the cap.
    Sys cs("gh-m3-noadm");
    auto &A = cs.domain(env().a_profile(), "A");
    auto v = A.priv(Subfield{}, "v", 1);
    assert_range(v, 3000, MaxBound{4000}, "v");
    CompileProfile p;
    p.name = "direct-capped";
    p.range.kinds = {RealizationKind::kDirect};
    p.range.max_table = 2048;
    const std::string err = compile_error(cs, p);
    EXPECT_NE(err.find("range request 'v' of domain A (n = 3000, m = 4000) has "
                       "no admissible realization"),
              std::string::npos)
        << err;
    EXPECT_NE(err.find("direct T=3000: T above the table cap 2048"),
              std::string::npos)
        << err;
  }
  {
    // The default policy realizes it in three digits of a table of 15
    // rows: n <= N = 15^3 = 3375 <= m.
    Sys cs("gh-m3-digits");
    auto &A = cs.domain(env().a_profile(), "A");
    auto v = A.priv(Subfield{}, "v", 1);
    auto h = assert_range(v, 3000, MaxBound{4000}, "v");
    auto c = compile(cs);
    EXPECT_EQ(c->realization(h).kind, RealizationKind::kDigits);
    EXPECT_EQ(c->realization(h).table, 15u);
    EXPECT_EQ(c->proven_bound(h), 3375u);
  }
  {
    // R1: a request in characteristic 2.
    Sys cs("gh-m3-char2");
    auto &H = cs.domain(env().h_profile(), "H");
    auto v = H.priv(Subfield{}, "v", 1);
    assert_range(v, 2048, "v");
    EXPECT_NE(compile_error(cs).find("range request 'v' in domain H, which has "
                                    "characteristic 2"),
              std::string::npos)
        << compile_error(cs);
  }
  {
    // R7: a needle through an operator without a circuit expansion.
    Sys cs("gh-m3-r7");
    auto &A = cs.domain(env().a_profile(), "A");
    auto k = A.pub(Field{}, "k", 2);
    auto v = A.priv(Subfield{}, "v", 2);
    assert_range(ops::NegacyclicConv(k)(v), 2048, "conv");
    EXPECT_NE(compile_error(cs).find("its needle applies the operator "
                                    "'negacyclic_conv', which has no circuit "
                                    "expansion"),
              std::string::npos)
        << compile_error(cs);
  }
  {
    // R6 at declaration: an empty interval.
    Sys cs("gh-m3-r6");
    auto &A = cs.domain(env().a_profile(), "A");
    auto v = A.priv(Subfield{}, "v", 1);
    EXPECT_THROW(assert_range(v, 10, MaxBound{5}), CompileError);
    EXPECT_THROW(assert_range(v, 0), CompileError);
  }
  {
    // A request left unlowered: compile(const System&) does not lower.
    Sys cs("gh-m3-pending");
    auto &A = cs.domain(env().a_profile(), "A");
    auto v = A.priv(Subfield{}, "v", 1);
    assert_range(v, 2048);
    EXPECT_NE(core_error(cs).find("1 range requests and 0 equalities that are "
                                 "not lowered"),
              std::string::npos)
        << core_error(cs);
  }
}

// Interval propagation: an expression over range-checked values is implied
// (no needles, coordinates or rows) when its integer interval lies within
// the request. The planner searches the terms' realizations for it; when no
// combination implies it, an assert_range falls back to a lookup and a
// assert_range_implied fails naming the members.
TEST(GordieHoweM3, IntervalPropagation) {
  struct Two {
    Sys cs;
    Domain<AF> *A;
    Ref<AF> v, w;
    RangeHandle<AF> hv, hw;
    explicit Two(const char *nm) : cs(nm) {
      A = &cs.domain(env().a_profile(), "A");
      fill_2048(*A);
      v = A->priv(Subfield{}, "v", 1,
                    depends_on(A->priv(Subfield{}, "x", 1)),
                    [](const AV &x) { return x; });
      w = A->priv(Subfield{}, "w", 1);
      hv = assert_range(v, 100, MaxBound{Bound(1) << 22}, "v");
      hw = assert_range(w, 100, MaxBound{Bound(1) << 22}, "w");
    }
  };
  {
    // Both direct (2048) give v + w in [0, 4094]; v two-sided (N = 100)
    // gives [0, 2146], which [200, 3000] admits. (As an assert_range, a
    // lookup of the sum costs less.)
    Two t("gh-m3-implied");
    auto hs = assert_range_implied(t.v + t.w, 200, MaxBound{3000}, "sum");
    auto c = compile(t.cs);
    EXPECT_EQ(c->realization(t.hw).kind, RealizationKind::kDirect);
    EXPECT_EQ(c->realization(t.hv).kind, RealizationKind::kTwoSided);
    EXPECT_EQ(c->proven_bound(t.hv), 100u);
    EXPECT_EQ(c->realization(hs).kind, RealizationKind::kImplied);
    EXPECT_EQ(c->proven_bound(hs), 2147u);
    EXPECT_NE(c->report().find("sum: implied, interval [0, 2146] -> bound "
                               "2147; no needles, coordinates or rows"),
              std::string::npos)
        << c->report();
  }
  {
    // [50, 100] admits no combination (v + w >= 0 spans at least [0, 198]):
    // the sum is looked up, by one complement needle since v + w >= 0, and
    // the report says why.
    Two t("gh-m3-implied-fallback");
    auto hs = assert_range(t.v + t.w, 50, MaxBound{100}, "sum");
    auto c = compile(t.cs);
    EXPECT_EQ(c->realization(t.hv).kind, RealizationKind::kDirect);
    EXPECT_EQ(c->realization(hs).kind, RealizationKind::kComplement);
    EXPECT_NE(c->report().find("not implied: the interval [0, 4094] needs "
                               "N >= 4095, outside [50, 100]"),
              std::string::npos)
        << c->report();
  }
  {
    // assert_range_implied is never looked up.
    Two t("gh-m3-implied-fail");
    assert_range_implied(t.v + t.w, 50, MaxBound{100}, "sum");
    const std::string err = compile_error(t.cs);
    EXPECT_NE(err.find("range request 'sum' of domain A (n = 50, m = 100) is "
                       "implied by no combination of its terms' "
                       "realizations; members:"),
              std::string::npos)
        << err;
    EXPECT_NE(err.find("v: candidate bounds "), std::string::npos) << err;
  }
  {
    // A bound proven outright: x < 2048 gives 3x + 7 in [7, 6148] < 10000,
    // with no lookup; x - 5 has a negative lower end and is looked up.
    Sys cs("gh-m3-implied-outright");
    auto &A = cs.domain(env().a_profile(), "A");
    auto x = A.priv(Subfield{}, "x", 4);
    assert_range(x, 2048, "x");
    auto k7 = A.constant("seven", AV(4, af().of_scalar(7)));
    auto k5 = A.constant("five", AV(4, af().of_scalar(5)));
    auto h3 = assert_range(af().of_scalar(3) * x + k7, 10000, "3x+7");
    auto hm = assert_range(x - k5, 3000, MaxBound{4000}, "x-5");
    auto c = compile(cs);
    EXPECT_EQ(c->realization(h3).kind, RealizationKind::kImplied);
    EXPECT_EQ(c->proven_bound(h3), 10000u);
    EXPECT_NE(c->realization(hm).kind, RealizationKind::kImplied);
    EXPECT_NE(c->report().find("3x+7: implied, interval [7, 6148]"),
              std::string::npos)
        << c->report();
    EXPECT_NE(c->report().find("not implied: the interval [-5, 2042] has a "
                               "negative lower end"),
              std::string::npos)
        << c->report();
    Assignment w;
    w.set(x, avec({5, 9, 100, 2047}));
    EXPECT_TRUE(honest(*c, {}, w));
  }
}

// priv(..., nat(...)) reads canonical integers: a dependency outside the prime field
// and an output of at least p are run-time errors naming the advice (not
// the coordinate: the check runs once, after the conversion).
TEST(GordieHoweM3, AdviceNatErrors) {
  for (bool big : {false, true}) {
    Sys cs("gh-m3-advice-nat");
    auto &A = cs.domain(env().a_profile(), "A");
    auto x = A.priv(Field{}, "x", 1);
    auto y = A.priv(Field{}, "y", 1, depends_on(x),
                          nat([big](NatInt v) { return big ? nat_cast(kP) : v; }));
    assert_equal(x, y, "y = x").pin(Placement::kCircuit);
    auto c = compile(cs);
    auto prep = c->prepare({});
    uint8_t b[AF::kBytes] = {};
    b[8] = 1;  // the coefficient of the first extension basis element
    Assignment w;
    w.set(x, big ? avec({3}) : AV{*af().of_bytes_field(b)});
    SecureRandomEngine rng;
    try {
      prep.prove(w, rng);
      ADD_FAILURE() << "priv(nat) accepted a non-canonical value";
    } catch (const std::runtime_error &e) {
      const std::string want =
          big ? "advice 'y': an output is not below p"
              : "advice 'y': dependency 0 has a coordinate outside the "
                "prime field";
      EXPECT_NE(std::string(e.what()).find(want), std::string::npos)
          << e.what();
    }
  }
}

// A closure whose parameters are integers is read as nat(...): Bound or
// uint64_t, elementwise or vector, in advice and in public computations;
// one over field elements is not. Each generator's output is pinned by a
// predicate, so an honest proof shows the values.
TEST(GordieHoweM3, AdviceIntegersInferred) {
  Sys cs("gh-m3-advice-integers");
  auto &A = cs.domain(env().a_profile(), "A");
  auto k = A.pub(Subfield{}, "k", 4);
  auto x = A.priv(Subfield{}, "x", 4);
  auto a = A.priv(Subfield{}, "a", 4, depends_on(x),
                    [](NatInt v) { return v + 1; });
  auto b = A.priv(Subfield{}, "b", 4, depends_on(x),
                    [](uint64_t v) { return 2 * v; });
  auto c = A.priv(Subfield{}, "c", 4, depends_on(x, k),
                    [](const std::vector<uint64_t> &v,
                       const Tensor<uint64_t> &w) {
                      std::vector<uint64_t> out;
                      for (size_t i = 0; i < v.size(); ++i)
                        out.push_back(v[i] + w[i]);
                      return out;
                    });
  auto d = A.priv(Subfield{}, "d", 1, depends_on(x),
                    [](const Tensor<NatInt> &v) {
                      NatInt t = 0;
                      for (NatInt y : v) t += y * y;
                      return std::vector<NatInt>{t};
                    });
  auto e = A.priv(Subfield{}, "e", 4, depends_on(x),
                    nat([](uint64_t v) { return v + 3; }));
  auto k3 = A.pub(Subfield{}, "k3", 4, depends_on(k),
                             computes("times3", {}),
                             [](const std::vector<uint64_t> &v) {
                               std::vector<uint64_t> out;
                               for (uint64_t y : v) out.push_back(3 * y);
                               return out;
                             });
  assert_zero(a - x - 1, "a");
  assert_zero(b - 2 * x, "b");
  assert_zero(c - x - k, "c");
  assert_zero(d - (x * x).sum(), "d");
  assert_zero(e - x - 3, "e");
  assert_zero(k3 - 3 * x, "k3");
  auto compiled = compile(cs);
  Assignment st, w;
  st.set(k, avec({5, 9, 100, 2047}));
  w.set(x, avec({5, 9, 100, 2047}));
  EXPECT_TRUE(honest(*compiled, st, w));
}


// ------------------------------------------------------------- profile --

TEST(GordieHoweM3, CompileOncePerProfile) {
  RangeSys r;
  auto c1 = compile(r.cs);
  auto c2 = compile(r.cs);
  EXPECT_EQ(c1->digest(), c2->digest());
  CompileProfile other;
  other.name = "other";
  EXPECT_NE(compile_error(r.cs, other).find("was lowered under the profile "
                                           "default v1; it cannot be lowered "
                                           "again under other v1"),
            std::string::npos)
      << compile_error(r.cs, other);
  // A request declared after lowering is not lowered.
  assert_range(r.x, 2048, "late request");
  EXPECT_NE(compile_error(r.cs).find("was lowered; its 1 range requests and 0 "
                                    "equalities declared since are not "
                                    "lowered"),
            std::string::npos)
      << compile_error(r.cs);
  // The profile is part of the digest.
  RangeSys r2;
  CompileProfile renamed;
  renamed.name = "renamed";
  EXPECT_NE(compile(r2.cs, renamed)->digest(), c1->digest());
}

}  // namespace
}  // namespace proofs::gordiehowe
