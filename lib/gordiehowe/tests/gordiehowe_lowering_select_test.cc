// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_lowering_test binary): selection, the
// equalities, the selection and equality pair, and the Falcon skeleton.

#include "gordiehowe/tests/gordiehowe_lowering_test.h"

namespace proofs::gordiehowe {
namespace {

// The cutoff selection (lib/cutoff_select.h).
using namespace ::proofs::gordiehowe::lib::select;  // NOLINT

// ----------------------------------------------------------- selection --

uint32_t sample_at(size_t i) { return uint32_t((i * 7919 + 12345) % 65536); }

HV stream_bits(size_t S, uint32_t (*smp)(size_t)) {
  HV out;
  for (size_t i = 0; i < S; ++i)
    for (size_t j = 0; j < 16; ++j)
      out.push_back((smp(i) >> j) & 1 ? hf().one() : hf().zero());
  return out;
}

struct SelectSys {
  Sys cs{"gh-m3-select"};
  Domain<HF> *H;
  Ref<HF, Bit, Committed> stream;
  CutoffSelection<HF> sel;
  SelectSys(size_t S, size_t n, uint32_t cutoff) {
    H = &cs.domain(env().h_profile(), "H");
    stream = H->priv(Bit{}, "stream", 16 * S);
    sel = select_first_n(cs, *H, stream, Cutoff{cutoff}, lib::select::Count{n});
  }
};

TEST(GordieHoweM3, SelectionProvesAndRejects) {
  constexpr size_t S = 24, n = 8;
  constexpr uint32_t cutoff = 40000;
  SelectSys t(S, n, cutoff);
  auto c = compile(t.cs);
  EXPECT_EQ(c->phase(t.sel.delta), 1u);
  Assignment w;
  w.set(t.stream, stream_bits(S, sample_at));
  EXPECT_TRUE(honest(*c, {}, w));
  // The accepted candidates, in order.
  std::vector<size_t> acc;
  for (size_t i = 0; i < S; ++i)
    if (sample_at(i) < cutoff) acc.push_back(i);
  ASSERT_GT(acc.size(), n);
  auto raw_of = [&](std::vector<size_t> pick) {
    HV out;
    for (size_t i : pick)
      for (size_t j = 0; j < 16; ++j)
        out.push_back((sample_at(i) >> j) & 1 ? hf().one() : hf().zero());
    return out;
  };
  // Skipping the first accepted sample: raw holds accepted samples 1..n.
  const HV skipped = raw_of(std::vector<size_t>(acc.begin() + 1, acc.begin() + n + 1));
  auto put = [&](size_t id, HV v) {
    return [id, v](size_t at, SysValue &x) {
      if (at == id) std::get<HV>(x) = v;
    };
  };
  EXPECT_TRUE(verifier_rejects(*c, {}, w, put(t.sel.raw.id, skipped)));
  // Two selected samples swapped.
  std::vector<size_t> sw(acc.begin(), acc.begin() + n);
  std::swap(sw[0], sw[1]);
  EXPECT_TRUE(verifier_rejects(*c, {}, w, put(t.sel.raw.id, raw_of(sw))));
  // The saturation flag of the first accepted candidate after the n-th
  // cleared: that candidate is selected too.
  const size_t extra = acc[n] - n;
  EXPECT_TRUE(verifier_rejects(*c, {}, w, [&](size_t at, SysValue &x) {
    if (at == t.sel.full.id) std::get<HV>(x).at(extra) = hf().zero();
  }));
}

TEST(GordieHoweM3, SelectionBudgetIsACompletenessFailure) {
  SelectSys t(24, 20, 1000);
  auto c = compile(t.cs);
  Assignment w;
  w.set(t.stream, stream_bits(24, sample_at));
  auto prep = c->prepare({});
  SecureRandomEngine rng;
  EXPECT_THROW(prep.prove(w, rng), CompletenessFailure);
  Sys cs("gh-m3-select-bad");
  auto &H = cs.domain(env().h_profile(), "H");
  auto st = H.priv(Bit{}, "stream", 16 * 4);
  EXPECT_THROW(select_first_n(cs, H, st, Cutoff{70000}, lib::select::Count{2}),
               CompileError);
  EXPECT_THROW(select_first_n(cs, H, st, Cutoff{100}, lib::select::Count{5}),
               CompileError);
}

// -------------------------------------------------------------- equality --

// X_H: Bit cells of H; X_A: Bit advice of A copying them.
struct MacSys {
  Sys cs{"gh-m3-mac"};
  Domain<HF> *H;
  Domain<AF> *A;
  Ref<HF> xh;
  Ref<AF> xa;
  size_t len;
  MacSys(size_t n, bool h_first) : len(n) {
    H = &cs.domain(env().h_profile(), "H");
    A = &cs.domain(env().a_profile(), "A");
    xh = H->priv(Bit{}, "xh", n);
    const AF *pa = &af();
    const HF *ph = &hf();
    xa = A->priv(Bit{}, "xa", n, depends_on(xh), [pa, ph](const HV &b) {
      AV out;
      for (const auto &e : b) out.push_back(e == ph->one() ? pa->one() : pa->zero());
      return out;
    });
    if (h_first)
      assert_same_bits(xh, xa);
    else
      assert_same_bits(xa, xh);
  }
  Assignment witness() const {
    HV v;
    for (size_t i = 0; i < len; ++i)
      v.push_back((i * 37) % 5 < 2 ? hf().one() : hf().zero());
    Assignment w;
    w.set(xh, v);
    return w;
  }
};

TEST(GordieHoweM3, MacEqualityProvesAndRejects) {
  for (bool h_first : {true, false}) {
    for (size_t n : {512u, 300u}) {
      MacSys m(n, h_first);
      auto c = compile(m.cs);
      // Oriented: the MAC value lives in H whichever order the arguments
      // come in, and T is the first message of phase 1.
      const size_t U = id_of(m.cs, "mac.value");
      EXPECT_EQ(m.cs.graph().nodes[U].domain, 0);
      EXPECT_EQ(c->messages().at(0), U);
      EXPECT_EQ(c->phase(Ref<AF>{U, 1, nullptr, nullptr}), 1u);
      // beta tests X_H, X_A, the blind and its copy.
      // (Inferred: X_H, X_A, the pad of U and its copy.)
      const auto &beta = c->tests_of(id_of(m.cs, "mac.beta"));
      const size_t blind = id_of(m.cs, "mac.blind");
      EXPECT_NE(std::find(beta.begin(), beta.end(), blind), beta.end());
      ASSERT_EQ(beta.size(), 4u);
      EXPECT_EQ(std::count_if(beta.begin(), beta.end(),
                              [&](size_t x) {
                                return m.cs.graph().nodes[x].kind == Kind::kPad;
                              }),
                1);
      // bits(T) names CoefficientBits and the basis.
      const auto &d = m.cs.graph().nodes[id_of(m.cs, "mac.target_bits")].descr;
      EXPECT_NE(std::string(d.begin(), d.end()).find("CoefficientBits"),
                std::string::npos);
      EXPECT_TRUE(honest(*c, {}, m.witness()));
      // A flipped bit on the A side.
      EXPECT_TRUE(verifier_rejects(*c, {}, m.witness(), [&](size_t at, SysValue &x) {
        if (at != m.xa.id) return;
        auto &v = std::get<AV>(x);
        v[7] = v[7] == af().one() ? af().zero() : af().one();
      }));
    }
  }
}

TEST(GordieHoweM3, MacEqualityCompileErrors) {
  // Two domains of one field: refused when the second is declared, so an
  // equality in one field is assert_zero(x - y) in its one domain
  // (assert_same_bits of one field is a C++ compile error).
  auto declare_error = [](auto &&declare) {
    try {
      declare();
    } catch (const CompileError &e) {
      return std::string(e.what());
    }
    return std::string();
  };
  {
    // Odd/odd and binary/binary: a system has one domain per field, so the
    // second domain of a field is refused at its declaration.
    Sys cs("gh-m3-oddodd");
    cs.domain(env().a_profile(), "A");
    std::string err =
        declare_error([&] { cs.domain(env().a_profile(), "B"); });
    EXPECT_NE(err.find("a system has one domain per field"), std::string::npos)
        << err;
    Sys t("gh-m3-binbin");
    t.domain(env().h_profile(), "G");
    err = declare_error([&] { t.domain(env().h_profile(), "H"); });
    EXPECT_NE(err.find("a system has one domain per field"), std::string::npos)
        << err;
  }
  {
    // E2 through erased handles (a typed Field side is a C++ compile
    // error); lengths.
    Sys cs("gh-m3-e2");
    auto &H = cs.domain(env().h_profile(), "H");
    auto &A = cs.domain(env().a_profile(), "A");
    Ref<HF> x = H.priv(Bit{}, "x", 4);
    Ref<AF> y = A.priv(Field{}, "y", 4);
    assert_equal(x, y);
    EXPECT_NE(compile_error(cs).find("'y' has type Field; the MAC equality "
                                    "compares Bit values"),
              std::string::npos)
        << compile_error(cs);
    Sys t("gh-m3-len");
    auto &H2 = t.domain(env().h_profile(), "H");
    auto &A2 = t.domain(env().a_profile(), "A");
    assert_equal(t[H2].priv(Bit{}, "x", 4), t[A2].priv(Bit{}, "y", 5));
    EXPECT_NE(compile_error(t).find("lengths 4 and 5 differ"), std::string::npos);
  }
  {
    // E3: no basis of width 256, and a basis that disagrees with the field.
    MacSys m(256, true);
    CompileProfile p;
    p.name = "no-mac";
    p.mac_bases = {};
    EXPECT_NE(compile_error(m.cs, p).find("names no MAC basis of width 256"),
              std::string::npos);
    MacSys m2(256, true);
    p.name = "wrong-mac";
    p.mac_bases = {MacBasis{256, {10, 5, 3, 0}}};
    EXPECT_NE(compile_error(m2.cs, p).find("differs from the profile's MAC basis"),
              std::string::npos);
  }
}

// Within one domain: assert_zero(x - y), placed by the domain (affine rows,
// or the circuit when a side is a bit view).
TEST(GordieHoweM3, SameDomainEquality) {
  {
    Sys cs("gh-m3-eq-affine");
    auto &A = cs.domain(env().a_profile(), "A");
    auto x = A.priv(Subfield{}, "x", 3);
    auto y = A.priv(Subfield{}, "y", 3, depends_on(x), [](const AV &v) { return v; });
    // A circuit that reads both (x0 x1 = y0 y1), so the domain has a GKR
    // kernel; the equality's rows cover every coordinate.
    assert_equal(x[0] * x[1], y[0] * y[1], "x0 x1 = y0 y1")
        .pin(Placement::kCircuit);
    assert_equal(x, y, "x = y");
    auto c = compile(cs);
    Assignment w;
    w.set(x, avec({1, 2, 3}));
    EXPECT_TRUE(honest(*c, {}, w));
    EXPECT_TRUE(verifier_rejects(*c, {}, w, set_at(y.id, 2, af().of_scalar(4))));
  }
}
TEST(GordieHoweM3, SameDomainEqualityCircuit) {
  {
    Sys cs("gh-m3-eq-circuit");
    auto &H = cs.domain(env().h_profile(), "H");
    auto words = H.priv(Subfield{}, "words", 2);
    auto view = H.bits("view", words);
    auto cells = H.priv(Bit{}, "cells", 32, depends_on(view),
                          [](const HV &v) { return v; });
    // A circuit of H (the equality is placed outside it): w0 w1 = prod.
    const HF *ph = &hf();
    auto prod = H.priv(Subfield{}, "prod", 1, depends_on(words),
                         [ph](const HV &v) { return HV{ph->mulf(v[0], v[1])}; });
    assert_equal(words[0] * words[1], prod[0], "w0 w1 = prod")
        .pin(Placement::kCircuit);
    assert_equal(view, cells, "view = cells");
    auto c = compile(cs);
    Assignment w;
    w.set(words, HV{hf().of_scalar(0x1234), hf().of_scalar(0xbeef)});
    EXPECT_TRUE(honest(*c, {}, w));
    EXPECT_TRUE(verifier_rejects(*c, {}, w, [&](size_t at, SysValue &x) {
      if (at != cells.id) return;
      auto &v = std::get<HV>(x);
      v[3] = v[3] == hf().one() ? hf().zero() : hf().one();
    }));
  }
}


// ------------------------------------------------- selection + equality --

// An H/A pair like Falcon emulated's at a small size: H selects 32
// samples from 40, A holds them as bits, and assert_equal ties the two.
struct PairSys {
  Sys cs{"gh-m3-pair"};
  Domain<HF> *H;
  Domain<AF> *A;
  Ref<HF, Bit, Committed> stream;
  CutoffSelection<HF> sel;
  Ref<AF> c_A;
  PairSys(size_t S, size_t n, uint32_t cutoff) {
    H = &cs.domain(env().h_profile(), "H");
    A = &cs.domain(env().a_profile(), "A");
    stream = H->priv(Bit{}, "stream", 16 * S);
    sel = select_first_n(cs, *H, stream, Cutoff{cutoff}, lib::select::Count{n});
    const AF *pa = &af();
    const HF *ph = &hf();
    c_A = A->priv(Bit{}, "samples", 16 * n, depends_on(sel.raw),
                    [pa, ph](const HV &b) {
                      AV out;
                      for (const auto &e : b)
                        out.push_back(e == ph->one() ? pa->one() : pa->zero());
                      return out;
                    });
    assert_equal(sel.raw, c_A);
  }
};

// assert_same_bits' integer form: 12-bit integers as GF(2^16) words of H
// (their bit view, the high four bits zero) and as Subfield words of A
// (decomposed into Bit cells), the same as the integers' bits.
TEST(GordieHoweM3, SameBitsIntegerForm) {
  Sys cs("gh-m3-same-bits-integers");
  auto &H = cs.domain(env().h_profile(), "H");
  auto &A = cs.domain(env().a_profile(), "A");
  // Both sides are advice of H's input, so the tampers below reach them.
  auto seed = H.priv(Subfield{}, "seed", 5);
  auto xh = H.priv(Subfield{}, "xh", 5, depends_on(seed),
                     [](const HV &v) { return v; });
  const AF *pa = &af();
  const HF *ph = &hf();
  auto xa = A.priv(Subfield{}, "xa", 5, depends_on(seed),
                     [pa, ph](const HV &v) {
                       const auto &sub = SubfieldInfo<HF>::get(*ph, 16);
                       AV out;
                       for (const auto &e : v)
                         out.push_back(pa->of_scalar(sub.bits(*ph, e)));
                       return out;
                     });
  // A's token circuit; H needs none (the MAC's H part is an affine row).
  L::gkr(A, "token", depends_on(xa),
        [](const auto &lc, const auto &x) { lc.assert_eq(x[0], x[0]); });
  assert_same_bits(xh, xa, BitWidth{12});
  auto c = compile(cs);
  HV h;
  for (uint64_t x : {0, 1, 0xabc, 0xfff, 0x5a5}) h.push_back(hf().of_scalar(x));
  Assignment w;
  w.set(seed, h);
  EXPECT_TRUE(honest(*c, {}, w));
  // Another integer on the A side; a high bit of an H word.
  EXPECT_TRUE(verifier_rejects(*c, {}, w, set_at(xa.id, 2, af().of_scalar(0xabd))));
  EXPECT_TRUE(verifier_rejects(*c, {}, w, [&](size_t at, SysValue &x) {
    if (at == xh.id) std::get<HV>(x).at(2) = hf().of_scalar(0x1abc);
  }));
}

TEST(GordieHoweM3, SelectionAndEqualityPair) {
  constexpr size_t S = 40, n = 32;
  constexpr uint32_t cutoff = 61445;
  PairSys t(S, n, cutoff);
  auto c = compile(t.cs);
  EXPECT_EQ(c->phases(), 2u);
  EXPECT_EQ(c->phase(t.sel.delta), 1u);
  EXPECT_EQ(c->messages().at(0), id_of(t.cs, "mac.value"));
  Assignment w;
  w.set(t.stream, stream_bits(S, sample_at));
  EXPECT_TRUE(honest(*c, {}, w));
  // A flipped bit of c_A, and a skipped accepted sample in raw (c_A copies
  // the tampered raw, so only the selection catches it).
  EXPECT_TRUE(verifier_rejects(*c, {}, w, [&](size_t at, SysValue &x) {
    if (at != t.c_A.id) return;
    auto &v = std::get<AV>(x);
    v[100] = v[100] == af().one() ? af().zero() : af().one();
  }));
  std::vector<size_t> acc;
  for (size_t i = 0; i < S; ++i)
    if (sample_at(i) < cutoff) acc.push_back(i);
  ASSERT_GT(acc.size(), n);
  HV skipped;
  for (size_t k = 1; k <= n; ++k)
    for (size_t j = 0; j < 16; ++j)
      skipped.push_back((sample_at(acc[k]) >> j) & 1 ? hf().one() : hf().zero());
  EXPECT_TRUE(verifier_rejects(*c, {}, w, [&](size_t at, SysValue &x) {
    if (at == t.sel.raw.id) std::get<HV>(x) = skipped;
  }));
}

// ------------------------------------------------------------- Falcon --

Bound isqrt(Bound x) {
  Bound lo = 0, hi = Bound(1) << 64;
  while (lo + 1 < hi) {
    const Bound mid = (lo + hi) / 2;
    if (mid * mid <= x)
      lo = mid;
    else
      hi = mid;
  }
  return lo;
}

// A Falcon-shaped skeleton: H selects 512 samples
// of 639, A holds them as 8192 bits with Falcon's requests, shapes and
// bounds (stub closures). The lowering's inventory of A is Falcon emulated's.
TEST(GordieHoweM3, FalconSkeletonInventory) {
  constexpr size_t kN = 512;
  constexpr uint64_t q = 12289;
  PairSys t(639, kN, 5 * q);
  auto &A = *t.A;
  Sys &cs = t.cs;
  const AF *pf = &af();
  auto key = A.pub(Field{}, "key", kN);
  auto s2 = A.priv(Subfield{}, "s2", kN);
  auto stub = [pf](size_t n) {
    return [pf, n](const AV &, const AV &) { return AV(n, pf->zero()); };
  };
  auto s1 = A.priv(Subfield{}, "s1", kN, depends_on(s2, t.c_A), stub(kN));
  auto quot = A.priv(Subfield{}, "quot", kN, depends_on(s2, t.c_A), stub(kN));
  auto mag1 = A.priv(Subfield{}, "mag1", kN, depends_on(s2, t.c_A), stub(kN));
  auto mag2 = A.priv(Subfield{}, "mag2", kN, depends_on(s2, t.c_A), stub(kN));
  auto high2 = A.priv(Subfield{}, "high2", kN, depends_on(s2, t.c_A), stub(kN));
  auto norm = A.priv(Subfield{}, "norm", 1, depends_on(s2, t.c_A), stub(1));
  A.affine("signature", ops::NegacyclicConv(key)(s2) - s1 -
                            pf->of_scalar(q) * quot);
  // mag1 is s1 or q - s1, and norm the sum of the squared magnitudes.
  assert_zero((mag1 - s1) * (mag1 + s1 - pf->of_scalar(q)), "mag1")
      .pin(Placement::kCircuit);
  assert_equal(norm, (mag1 * mag1).sum() + (mag2 * mag2).sum(), "norm")
      .pin(Placement::kCircuit);
  // FalconBounds::derive, d = 128, b = 2048, J = 392.
  const Bound bias2 = 2 * Bound(77315788807ull);
  const Bound beta2 = 34034726;
  auto r_s1 = assert_range(s1, q, "s1");
  auto r_quot = assert_range(quot, (bias2 + q - 1) / q, MaxBound{(kP - 1) / q + 1},
                          "quot");
  auto r_mag1 = assert_range(
      mag1, q / 2 + 1,
      MaxBound{isqrt((kP - 1 - Bound(kN) * 2047 * 2047) / kN) + 1}, "mag1");
  auto r_mag2 = assert_range(mag2, 2048, "mag2");
  auto r_high2 = assert_range(high2, 16, MaxBound{(kP - 128) / 128 + 1}, "high2");
  auto r_low2 = assert_range(mag2 - pf->of_scalar(128) * high2, 128, "low2");
  auto J = A.constant("J", AV{pf->of_scalar(392)});
  auto r_budget = assert_range(J - Sum(high2), 393,
                            MaxBound{kP - kN * 15}, "budget");
  auto r_norm = assert_range(norm, beta2 + 1, "norm");

  auto c = compile(cs);
  std::printf("%s", c->report().c_str());

  auto expect = [&](RangeHandle<AF> h, RealizationKind k, unsigned digits,
                    Bound bound, bool bnd) {
    const auto &r = c->realization(h);
    EXPECT_EQ(r.kind, k) << realization_name(r.kind);
    EXPECT_EQ(r.k, digits);
    EXPECT_EQ(r.established, bound);
    EXPECT_EQ(r.bound, bnd);
  };
  expect(r_s1, RealizationKind::kTwoSided, 2, q, true);
  expect(r_quot, RealizationKind::kDigits, 3, Bound(1) << 33, true);
  expect(r_mag1, RealizationKind::kDigits, 2, Bound(1) << 14, true);
  expect(r_mag2, RealizationKind::kDirect, 0, 2048, false);
  expect(r_high2, RealizationKind::kDirect, 0, 128, false);
  expect(r_low2, RealizationKind::kDirect, 0, 128, false);
  expect(r_budget, RealizationKind::kDirect, 0, 2048, false);
  expect(r_norm, RealizationKind::kTwoSided, 3, beta2 + 1, true);
  // The MAC's digit requests: direct, dynamic, both in the 128-row table.
  // Radix 2^8: low < n_low = 128, high < n_high = floor(32545 / 256) + 1 =
  // 128.
  const auto &reqs = A.requests();
  for (const auto &r : reqs)
    if (r.name == "mac.low" || r.name == "mac.high") {
      EXPECT_EQ(r.realization.kind, RealizationKind::kDirect) << r.name;
      EXPECT_EQ(r.realization.established, 128u) << r.name;
      EXPECT_EQ(r.n, 128u) << r.name;
      EXPECT_EQ(r.m, (kP - 2) / 258 + 1);
    }
  EXPECT_NE(c->report().find("radix B = 128, committed below 128, top "
                             "'mac.high' derived below 128, Dmax = "
                             "71499008020986761; completeness: Qmax = 16272 "
                             "< 16384"),
            std::string::npos)
      << c->report();

  // Challenges: each one's field, samples, declaring lowering and tested
  // values. The budget's completeness probability is Pr[Bin(639,
  // 61445/2^16) < 512].
  EXPECT_NEAR(t.sel.log2_budget_failure, -102.3, 0.05);
  for (const char *want : {
           "challenge select.delta n=1 phase=1 sampler=field field=GF(2^256) "
           "by=select tests=",
           "challenge mac.beta n=1 phase=1 sampler=field field=GF(2^256) "
           "by=mac-equality tests=",
           "challenge alpha:A n=1 phase=2 sampler=field-minus-tables "
           "field=",
       })
    EXPECT_NE(c->report().find(want), std::string::npos) << want;
  // The no-wrap condition 1 + 2(L-1) + 2^8(R-1) < p, implied by L = R =
  // 128.
  EXPECT_NE(c->report().find("mac.nowrap: implied, interval [0, 32766] -> "
                             "bound 32767; no needles, coordinates or rows"),
            std::string::npos)
      << c->report();
  // Section 6's counts: both digits' dynamic needles in the 128-row table,
  // with its late histogram of 128 and its pad; the 2048-row table has no
  // dynamic needles and no late histogram.
  EXPECT_EQ(c->coordinates(A.index), 17286u);
  ASSERT_EQ(A.range_tables().size(), 2u);
  const auto &small = A.range_tables()[0];
  EXPECT_EQ(small.table, 128u);
  EXPECT_EQ(small.static_needles, 4096u);
  EXPECT_EQ(small.dynamic_needles, 512u);
  const auto &tab = A.range_tables()[1];
  EXPECT_EQ(tab.static_needles, 2055u);
  EXPECT_EQ(tab.dynamic_needles, 0u);
  EXPECT_EQ(tab.s_dyn, 0u);
  // Phases: delta and beta in 1, alpha in 2; T, acc, low and the 128-row
  // table's m1 in phase 1, T first.
  EXPECT_EQ(c->phases(), 2u);
  EXPECT_EQ(c->phase(t.sel.delta), 1u);
  EXPECT_EQ(c->phase(Ref<AF>{id_of(cs, "mac.beta"), 1, nullptr, nullptr}), 1u);
  EXPECT_EQ(c->phase(Ref<AF>{tab.alpha, 1, nullptr, nullptr}), 2u);
  const std::vector<size_t> msgs{c->messages().begin(), c->messages().end()};
  ASSERT_EQ(msgs.size(), 4u);
  const std::vector<size_t> want{id_of(cs, "mac.value"), id_of(cs, "mac.acc"),
                                 id_of(cs, "mac.low")};
  EXPECT_EQ(std::vector<size_t>(msgs.begin(), msgs.begin() + 3), want);
  EXPECT_EQ(std::set<size_t>(msgs.begin() + 3, msgs.end()),
            (std::set<size_t>{small.m1}));
}

// A private input bound to the digits of its range request, as ML-DSA's z
// is to its norm digits: z + (B - 1) < 2B - 1 is realized two-sided, and z
// is read through the low digits minus the offset, with no cell.
TEST(GordieHoweM3, PrivateInputBoundToItsDigits) {
  constexpr uint64_t kB = 3000;
  auto build = [](Sys &cs, bool bind) {
    auto &A = cs.domain(env().a_profile(), "A");
    auto z = A.priv(Subfield{}, "z", Shape{2, 3});
    auto off = A.constant("z.offset", AV(6, af().of_scalar(kB - 1)));
    auto h = assert_range(z + off, 2 * kB - 1, "z");
    // A row that reads z: z[0][0] + z[1][2] = w.
    auto w = A.priv(Subfield{}, "w", 1);
    A.affine("w", z.at(0, 0).at(0, 0) + z[1].at(0, 2) - w);
    // A circuit that reads z through its view: z[0][1]^2 = 0.
    L::gkr(A, "z01", depends_on(z), [](const auto &lc, const auto &z) {
      lc.assert0(lc.mul(z(0, 1), z(0, 1)));
    });
    CompileProfile p;
    p.range.bind_digit_views = bind;
    p.name = bind ? "bind" : "no-bind";
    return std::make_tuple(z, w, h, p);
  };
  Sys cs("gh-m3-bind-input"), s0("gh-m3-bind-input-plain");
  auto [z, w, h, p] = build(cs, true);
  auto [z0, w0, h0, p0] = build(s0, false);
  auto c = compile(cs, p);
  auto c0 = compile(s0, p0);
  EXPECT_EQ(c->realization(h).kind, RealizationKind::kTwoSided);
  EXPECT_TRUE(c->realization(h).bound);
  EXPECT_FALSE(c0->realization(h0).bound);
  // z has no cell, and its reconstruction row is gone.
  EXPECT_EQ(c->coordinates(0) + 6, c0->coordinates(0));
  EXPECT_EQ(c->realization(h).k, 3u);
  EXPECT_NE(c->report().find("z: no cell; view d0 + 19*d1 + 19^2*d2 (range) - c"),
            std::string::npos)
      << c->report();
  // z = (-999, 0, 5 | 999, 7, -3), signed: canonical p - 999 etc.
  auto sv = [](int64_t x) {
    return x < 0 ? af().negf(af().of_scalar(uint64_t(-x)))
                 : af().of_scalar(uint64_t(x));
  };
  Assignment wit;
  wit.set(z, AV{sv(-999), sv(0), sv(5), sv(999), sv(7), sv(-3)});
  wit.set(w, AV{sv(-999 - 3)});
  EXPECT_TRUE(honest(*c, {}, wit));
  Assignment wit0;
  wit0.set(z0, AV{sv(-999), sv(0), sv(5), sv(999), sv(7), sv(-3)});
  wit0.set(w0, AV{sv(-1002)});
  EXPECT_TRUE(honest(*c0, {}, wit0));
  // A wrong digit changes z as the rows read it.
  EXPECT_TRUE(verifier_rejects(*c, {}, wit,
                               set_at(id_of(cs, "range.z.d0"), 0,
                                      af().of_scalar(1))));
  // z out of range: the high digits of top - (z + c) wrap, and the
  // two-sided top row (an affine row, which only the verifier checks)
  // fails.
  Assignment big;
  big.set(z, AV{sv(3000), sv(0), sv(5), sv(999), sv(7), sv(-3)});
  big.set(w, AV{sv(3000 - 3)});
  EXPECT_TRUE(verifier_rejects(*c, {}, big, [](size_t, SysValue &) {}));
}

}  // namespace
}  // namespace proofs::gordiehowe
