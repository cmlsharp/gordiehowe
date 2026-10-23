// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: the batched-relation kind in a characteristic-2
// domain (GF(2^256), source subfield GF(2^16)): a custom relation of degree
// 3 over a lane-affine operand map, and the bit views. Each proves,
// verifies, and rejects tampered witnesses and messages. The binary also
// holds gordiehowe_batch_mac_test.cc, gordiehowe_batch_shake_test.cc and
// gordiehowe_batch_words_test.cc.

#include "gordiehowe/tests/gordiehowe_batch_test.h"

namespace proofs::gordiehowe {
namespace {

// ------------------------------------------------------- degree three --

// Q(a, b, c, d) = a b c + d.
struct Cubic : SkipLanes<4> {
  static constexpr unsigned kOperands = 4, kDegree = 3;
  static constexpr size_t kMonomials = 2;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {{0, 1, 2},
                                                         {3, -1, -1}};
};

// Tables X, Y, Z, P of N lanes each (concatenated, 4 words per lane), and
//   a = rotl(X, 3), b = X ^ Y, c = ~Z, d = P,
// so the relation says P = rotl(X, 3) & (X ^ Y) & ~Z.
constexpr size_t kLanes = 37;
std::shared_ptr<const compiler::LaneOperandMap<HF, Cubic>> cubic_map(
    const HF &f) {
  using M = compiler::LaneOperandMap<HF, Cubic>;
  std::array<std::vector<M::Lane>, 4> ops;
  for (size_t l = 0; l < kLanes; ++l) {
    ops[0].push_back({0, {{l, 3}}});
    ops[1].push_back({0, {{l, 0}, {kLanes + l, 0}}});
    ops[2].push_back({~uint64_t(0), {{2 * kLanes + l, 0}}});
    ops[3].push_back({0, {{3 * kLanes + l, 0}}});
  }
  return std::make_shared<const M>(f, "test.cubic", 16 * kLanes, ops);
}

uint64_t rotl(uint64_t x, unsigned r) { return r ? (x << r) | (x >> (64 - r)) : x; }
uint64_t lane_of(const Vec &w, size_t l, const HF &f) {
  uint64_t v = 0;
  for (size_t c = 0; c < 4; ++c) {
    uint8_t b[2];
    f.to_bytes_subfield(b, w[4 * l + c]);
    v |= uint64_t(b[0] | (b[1] << 8)) << (16 * c);
  }
  return v;
}
Vec words_of(const std::vector<uint64_t> &lanes, const HF &f) {
  Vec out;
  for (uint64_t x : lanes)
    for (size_t c = 0; c < 4; ++c) out.push_back(f.of_scalar(uint16_t(x >> (16 * c))));
  return out;
}

struct CubicSystem {
  Sys cs{"gordiehowe-m2-cubic"};
  Domain<HF> *H;
  Ref<HF> first;
  Ref<HF, Subfield<>, Committed> X, Y, Z, P;
  explicit CubicSystem(unsigned width) {
    const HF *pf = &env().hf;
    H = &cs.domain(env().profile(), "H");
    first = H->pub(Field{}, "first", 1);
    X = H->priv(Subfield{}, "X", 4 * kLanes);
    Y = H->priv(Subfield{}, "Y", 4 * kLanes);
    Z = H->priv(Subfield{}, "Z", 4 * kLanes);
    P = H->priv(Subfield{}, "P", 4 * kLanes, depends_on(X, Y, Z),
                  [pf](const Vec &x, const Vec &y, const Vec &z) {
                    std::vector<uint64_t> p(kLanes);
                    for (size_t l = 0; l < kLanes; ++l)
                      p[l] = rotl(lane_of(x, l, *pf), 3) &
                             (lane_of(x, l, *pf) ^ lane_of(y, l, *pf)) &
                             ~lane_of(z, l, *pf);
                    return words_of(p, *pf);
                  });
    // Every domain compiles one GKR kernel: a token circuit.
    L::gkr(*H, "X[0] = first", depends_on(X, first),
           [](const auto &lc, const auto &x, const auto &f) {
             lc.assert_eq(x[0], f[0]);
           });
    H->batch("cubic", {X, Y, Z, P}, Cubic{}, cubic_map(*pf), width);
  }
  Vec lanes(uint64_t seed) const {
    std::mt19937_64 g(seed);
    std::vector<uint64_t> v(kLanes);
    for (auto &x : v) x = g();
    return words_of(v, env().hf);
  }
  Assignment witness() const {
    Assignment w;
    w.set(X, lanes(1)).set(Y, lanes(2)).set(Z, lanes(3));
    return w;
  }
  Assignment statement() const {
    Assignment st;
    st.set(first, Vec{lanes(1)[0]});
    return st;
  }
};

TEST(GordieHoweBatch, LaneMapAdjointMatchesApply) {
  // sum_j u_j L_j(r, s) from the operand bits equals the forms' value on
  // the table, for random points.
  const HF &f = env().hf;
  auto map = cubic_map(f);
  CubicSystem t(16);
  std::vector<uint16_t> host;
  Vec all;
  for (uint64_t seed : {1, 2, 3, 4}) {
    Vec w = t.lanes(seed);
    all.insert(all.end(), w.begin(), w.end());
  }
  for (const auto &x : all) {
    uint8_t b[2];
    f.to_bytes_subfield(b, x);
    host.push_back(uint16_t(b[0] | (b[1] << 8)));
  }
  const auto ops = map->apply(host);
  SecureRandomEngine rng;
  for (unsigned width : {1u, 8u, 16u}) {
    BasicBooleanSkip<HF, Cubic> skip(f, width);
    size_t logn = 0;
    while ((size_t(1) << logn) < kLanes * (64 / width)) ++logn;
    std::vector<HElt> s(logn);
    for (auto &x : s) x = rng.elt(f);
    const HElt r = rng.elt(f);
    std::array<HElt, 4> u;
    for (auto &x : u) x = rng.elt(f);
    std::array<HElt, 4> claims;
    claims.fill(f.zero());
    {
      // Reference: the skip's own multilinear evaluation of the operands.
      auto l = skip.bit_basis(r);
      const size_t nchunk = 64 / width;
      Eqs<HF> eq(logn, size_t(1) << logn, s.data(), f);
      for (size_t i = 0; i < ops.size(); ++i)
        for (size_t c = 0; c < nchunk; ++c)
          for (unsigned j = 0; j < 4; ++j) {
            HElt v = f.zero();
            for (unsigned z = 0; z < width; ++z)
              if ((ops[i][j] >> (c * width + z)) & 1) f.add(v, l[z]);
            f.add(claims[j], f.mulf(v, eq.at(i * nchunk + c)));
          }
    }
    HElt want = f.zero();
    for (unsigned j = 0; j < 4; ++j) f.add(want, f.mulf(u[j], claims[j]));
    const auto forms = map->adjoint(skip, r, s, u);
    HElt got = forms.constant;
    for (size_t k = 0; k < 16; ++k) {
      HElt ip = f.zero();
      for (size_t y = 0; y < forms.stride; ++y)
        f.add(ip, f.mulf(forms.a[k * forms.stride + y], all[y]));
      f.add(got, frobenius(ip, k, f));
    }
    EXPECT_EQ(got, want) << "width " << width;
  }
}

TEST(GordieHoweBatch, CubicProveVerify) {
  for (unsigned width : {1u, 16u}) {
    CubicSystem t(width);
    auto c = compile(t.cs);
    std::printf("%s", c->report().c_str());
    auto prep = c->prepare(t.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(t.witness(), rng);
    std::printf("cubic width %u: proof bytes %zu\n", width, proof.size());
    EXPECT_TRUE(prep.verify(proof));

    // A changed batch message: first skip value or round coefficient, a
    // terminal value, and the last masked measurement.
    const auto sp = c->batch_message_span(0);
    for (size_t at : {sp.offset, sp.offset + sp.length / 2,
                      sp.offset + sp.length - 1}) {
      auto bad = proof;
      bad[at] ^= 1;
      EXPECT_FALSE(prep.verify(bad)) << "message byte " << at - sp.offset;
    }
    // A message tampered before it is absorbed: a skip value (width 16),
    // the first round's coefficients, and a terminal value. Width 16 sends 30 skip
    // values and 8 rounds of 3; width 1 sends none and 12 rounds.
    const size_t skip = width == 16 ? 30 : 0, rounds = width == 16 ? 8 : 12;
    std::vector<size_t> at = {skip, skip + 1, skip + 2, skip + 3 * rounds + 3};
    if (skip) at.push_back(0);
    for (size_t i : at)
      EXPECT_FALSE(tampered_message_accepted(prep, t.witness(), i))
          << "width " << width << " message " << i;
  }
}

TEST(GordieHoweBatch, CubicCheatingTableRejected) {
  const HF &f = env().hf;
  CubicSystem t(16);
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement());
  ProveOptions opt;
  opt.require_satisfied = false;
  const size_t target = t.P.id;
  opt.tamper = [&](size_t id, SysValue &v) {
    if (id != target) return;
    auto &x = std::get<Vec>(v);
    // Flip bit 5 of word 9.
    uint8_t b[2];
    f.to_bytes_subfield(b, x[9]);
    x[9] = f.of_scalar(uint16_t((b[0] | (b[1] << 8)) ^ (1u << 5)));
  };
  SecureRandomEngine rng;
  EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt)));
}

TEST(GordieHoweBatch, RejectsBadTables) {
  {
    // A table of the wrong size.
    Sys cs("short-table");
    auto &H = cs.domain(env().profile(), "H");
    auto X = H.priv(Subfield{}, "X", 8);
    L::gkr(H, "token", depends_on(X),
          [](const auto &lc, const auto &x) { lc.assert_eq(x[0], x[0]); });
    H.batch("cubic", {X}, Cubic{}, cubic_map(env().hf));
    EXPECT_NE(core_error(cs).find("its operand map reads"), std::string::npos)
        << core_error(cs);
  }
  // A relation tag in an odd-characteristic domain (operands are no bits)
  // is a C++ compile error: a FieldRelation realizes it there.
}

// A field without relative packing (GF(2^128) over GF(2^8): no
// ExtensionTraits) commits no Subfield cell, since nothing would check its
// membership. An unpacked domain's Bit cells are field cells with b * b = b.
TEST(GordieHoweBatch, RejectsSubfieldCellWithoutRelativePacking) {
  using G = GF2_128<3>;
  using RS = LCH14ReedSolomonFactory<G>;
  static const G g;
  static const RS rs(g);
  DomainProfile<G, RS, SHA384> p;
  p.f = &g;
  p.rsf = &rs;
  p.field_name = "GF(2^128) over GF(2^8)";
  p.prime = Space::kPrime;
  {
    ConstraintSystem<SHA384, G> cs("unpacked-subfield");
    auto &D = cs.domain(p, "D");
    auto X = D.priv(Subfield{}, "X", 4);
    L::gkr(D, "token", depends_on(X),
          [](const auto &lc, const auto &x) { lc.assert_eq(x[0], x[0]); });
    EXPECT_NE(core_error(cs).find(
                  "'X' is a Subfield cell of domain D, whose field has no "
                  "relative packing"),
              std::string::npos)
        << core_error(cs);
  }
  {
    // A domain that declares no subfield: Bit cells are field cells.
    Sys cs("unpacked-bits");
    auto q = env().profile();
    q.has_subfield = false;
    // Unit rates: 4 triples cost less than 12 quad terms.
    q.rates = compiler::PlacementRates{};
    auto &D = cs.domain(q, "D");
    auto X = D.priv(Bit{}, "X", 4);
    assert_zero(X[0] * X[1], "X0 X1 = 0").pin(Placement::kCircuit);
    auto c = compile(cs);
    EXPECT_NE(c->report().find("packing: none (no subfield cells)"),
              std::string::npos)
        << c->report();
    EXPECT_NE(c->report().find("(bit checks 4)"), std::string::npos)
        << c->report();
  }
}

// In characteristic 2 the prime field is GF(2): a profile that places it
// elsewhere is rejected.
TEST(GordieHoweBatch, RejectsPrimeFieldMismatch) {
  auto p = env().profile();
  p.prime = Space::kSubfield;
  Sys cs("prime-subfield-in-characteristic-2");
  auto &H = cs.domain(p, "H");
  auto X = H.priv(Field{}, "X", 2);
  assert_zero(X[0] * X[1], "X0 X1 = 0").pin(Placement::kCircuit);
  EXPECT_NE(core_error(cs).find("domain H has characteristic 2, so its "
                                  "prime field is GF(2)"),
            std::string::npos)
      << core_error(cs);
}

// A malformed relation or skip width is a compile error, not an abort in the
// skip's constructor.
struct ConstantMonomial : SkipLanes<2> {
  static constexpr unsigned kOperands = 2, kDegree = 2;
  static constexpr size_t kMonomials = 2;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {{0, 1}, {-1, -1}};
};
struct GapMonomial : SkipLanes<3> {
  static constexpr unsigned kOperands = 3, kDegree = 3;
  static constexpr size_t kMonomials = 1;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {{0, -1, 2}};
};
struct Quintic : SkipLanes<5> {
  static constexpr unsigned kOperands = 5, kDegree = 5;
  static constexpr size_t kMonomials = 1;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {{0, 1, 2, 3, 4}};
};
template <class R>
std::string relation_compile_error(unsigned width) {
  Sys cs("bad-relation");
  auto &H = cs.domain(env().profile(), "H");
  auto X = H.priv(Subfield{}, "X", 4);
  assert_zero(X[0] * X[1], "X0 X1 = 0").pin(Placement::kCircuit);
  H.batch("q", {X}, R{},
          std::shared_ptr<const compiler::LaneOperandMap<HF, R>>(), width);
  return core_error(cs);
}
TEST(GordieHoweBatch, RejectsBadRelations) {
  EXPECT_NE(relation_compile_error<ConstantMonomial>(16).find(
                "batched relation 'q': monomial 1 is constant"),
            std::string::npos);
  EXPECT_NE(relation_compile_error<GapMonomial>(16).find(
                "monomial 0 has an operand after a -1 entry"),
            std::string::npos);
  EXPECT_NE(relation_compile_error<Cubic>(128).find(
                "skip width 128 is not a power of two up to 64"),
            std::string::npos);
  EXPECT_NE(relation_compile_error<Cubic>(12).find(
                "skip width 12 is not a power of two up to 64"),
            std::string::npos);
  EXPECT_NE(relation_compile_error<Quintic>(64).find(
                "skip width 64 is too large for degree 5"),
            std::string::npos);
}

// ------------------------------------------------------------ bit views --

TEST(GordieHoweBatch, SubfieldDecoderMatchesSolve) {
  const HF &f = env().hf;
  const compiler::SubfieldDecoder<HF> decode(f);
  for (uint32_t u = 0; u < 65536; u += 7)
    EXPECT_EQ(decode(f.of_scalar(u)), compiler::word_bits(f, f.of_scalar(u)))
        << u;
  EXPECT_EQ(decode(f.of_scalar(65535)), 65535);
}

// Subfield words X, a bit view of some of them, and a circuit asserting each
// viewed bit equals a public bit. Optionally a second circuit reads the
// view; without it the view allocates no wire.
struct ViewSystem {
  Sys cs{"gordiehowe-bit-views"};
  Domain<HF> *H;
  Ref<HF, Subfield<>, Committed> X;
  Ref<HF, Bit, Committed> bits;
  Ref<HF> want, first;
  std::vector<size_t> select = {3, 0, 7};
  explicit ViewSystem(bool read_view = true) {
    const HF *pf = &env().hf;
    H = &cs.domain(env().profile(), "H");
    first = H->pub(Field{}, "first", 1);
    want = H->pub(Field{}, "want", 16 * select.size());
    X = H->priv(Subfield{}, "X", 8);
    bits = H->bits("X.bits", X, select);
    L::gkr(*H, "X[0] = first", depends_on(X, first),
           [](const auto &lc, const auto &x, const auto &f) {
             lc.assert_eq(x[0], f[0]);
           });
    if (read_view)
      L::gkr(*H, "bits = want", depends_on(bits, want),
             [](const auto &lc, const auto &b, const auto &w) {
               for (size_t i = 0; i < b.size(); ++i) lc.assert_eq(b[i], w[i]);
             });
  }
  Vec words() const {
    Vec w;
    for (size_t i = 0; i < 8; ++i)
      w.push_back(env().hf.of_scalar(uint16_t(0x9e37 * (i + 1))));
    return w;
  }
  Assignment witness() const {
    Assignment a;
    a.set(X, words());
    return a;
  }
  // FLIP: the public bit that a cheating prover claims instead.
  Assignment statement(size_t flip = SIZE_MAX) const {
    const HF &f = env().hf;
    const Vec w = words();
    Vec b;
    for (size_t y : select)
      for (size_t j = 0; j < 16; ++j)
        b.push_back((compiler::word_bits(f, w[y]) >> j) & 1 ? f.one()
                                                            : f.zero());
    if (flip < b.size()) f.add(b[flip], f.one());
    Assignment st;
    st.set(first, Vec{w[0]}).set(want, b);
    return st;
  }
};

TEST(GordieHoweBatch, BitViewsReadCanonicalCoordinates) {
  ViewSystem t;
  auto c = compile(t.cs);
  std::printf("%s", c->report().c_str());
  auto prep = c->prepare(t.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(), rng);
  EXPECT_TRUE(prep.verify(proof));
  // A wrong public bit.
  EXPECT_FALSE(c->prepare(t.statement(/*flip=*/19)).verify(proof));
  EXPECT_NE(c->report().find("bit_views=3 words (aliased)"), std::string::npos)
      << c->report();

  // The view allocates no second witness: its 48 wires commit no packed
  // word, since each group of sixteen aliases its word.
  EXPECT_NE(c->report().find("packed_bits=0 (0 words committed, 0 zero)"),
            std::string::npos)
      << c->report();
  ViewSystem u(/*read_view=*/false);
  auto cu = compile(u.cs);
  EXPECT_NE(cu->report().find("bit_views=0 words"), std::string::npos)
      << cu->report();
}

TEST(GordieHoweBatch, BitViewWiresBindToTheWord) {
  // A cheating prover sets a viewed bit's wire to the claimed (wrong) bit, so
  // the circuit holds on its wires; the input claim goes through the word,
  // and the verifier rejects.
  const HF &f = env().hf;
  ViewSystem t;
  auto c = compile(t.cs);
  const size_t flip = 19;
  auto prep = c->prepare(t.statement(flip));
  ProveOptions opt;
  const size_t target = t.bits.id;
  opt.tamper = [&](size_t id, SysValue &v) {
    if (id == target) f.add(std::get<Vec>(v)[flip], f.one());
  };
  SecureRandomEngine rng;
  EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt)));
}

// Bit views composed along the packing tree's path, at D_max = 16: GF(2^32)
// words through one intermediate (GF(2) < GF(2^16) < GF(2^32)) and GF(2^64)
// words through two (GF(2^16) and GF(2^32)), in K = GF(2^256). A circuit
// reads every view bit against public bits, and an affine row reads some
// (its coefficients take the views' basis change). The proof verifies; a
// wrong public bit, a view wire set to the claimed wrong bit (so the
// circuit holds on its wires), and a witness off the affine row are each
// rejected.
struct ComposedViewSystem {
  Sys cs{"gordiehowe-composed-views"};
  Ref<HF, Subfield<GF<32>>, Committed> X;
  Ref<HF, Subfield<GF<64>>, Committed> Y;
  Ref<HF, Bit, Committed> xb, yb;
  Ref<HF> want_x, want_y, t;
  HElt k0, k1;
  std::vector<size_t> sx = {2, 0}, sy = {1, 0};
  ComposedViewSystem() {
    const HF &f = env().hf;
    k0 = f.of_scalar_field(0x1234567ull);
    k1 = f.of_scalar_field(99);
    auto &H = cs.domain(env().profile(), "H");
    want_x = H.pub(Field{}, "want_x", 32 * sx.size());
    want_y = H.pub(Field{}, "want_y", 64 * sy.size());
    t = H.pub(Field{}, "t", 1);
    X = H.priv(Subfield<GF<32>>{}, "X", 3);
    Y = H.priv(Subfield<GF<64>>{}, "Y", 2);
    xb = H.bits("X.bits", X, sx);
    yb = H.bits("Y.bits", Y, sy);
    L::gkr(H, "bits = want", depends_on(xb, yb, want_x, want_y),
          [](const auto &lc, const auto &xb, const auto &yb,
             const auto &wx, const auto &wy) {
            for (size_t i = 0; i < xb.size(); ++i) lc.assert_eq(xb[i], wx[i]);
            for (size_t i = 0; i < yb.size(); ++i) lc.assert_eq(yb[i], wy[i]);
          });
    H.affine("k0 xb37 + yb70 + k1 yb5 + xb3 = t",
             k0 * xb.at(0, 37) + yb.at(0, 70) + k1 * yb.at(0, 5) +
                 xb.at(0, 3) - t);
  }
  Vec xs() const {
    const auto &g = SubfieldInfo<HF>::get(env().hf, 32);
    return {g.word(env().hf, 0x12345678), g.word(env().hf, 0x9abcdef1),
            g.word(env().hf, 0x0f1e2d3c)};
  }
  Vec ys() const {
    const auto &g = SubfieldInfo<HF>::get(env().hf, 64);
    return {g.word(env().hf, 0x0123456789abcdefull),
            g.word(env().hf, 0xfedcba9876543211ull)};
  }
  Assignment witness() const {
    Assignment a;
    a.set(X, xs()).set(Y, ys());
    return a;
  }
  // The canonical bits of the selected words.
  static Vec bits_of(const Vec &w, const std::vector<size_t> &sel, size_t d) {
    const HF &f = env().hf;
    const auto &g = SubfieldInfo<HF>::get(f, d);
    Vec b;
    for (size_t y : sel)
      for (size_t j = 0; j < d; ++j)
        b.push_back((g.bits(f, w[y]) >> j) & 1 ? f.one() : f.zero());
    return b;
  }
  // FLIP_X, FLIP_Y: public bits a cheating prover claims instead.
  Assignment statement(size_t flip_x = SIZE_MAX, size_t flip_y = SIZE_MAX) const {
    const HF &f = env().hf;
    Vec bx = bits_of(xs(), sx, 32), by = bits_of(ys(), sy, 64);
    HElt tv = f.addf(f.mulf(k0, bx[37]), by[70]);
    f.add(tv, f.mulf(k1, by[5]));
    f.add(tv, bx[3]);
    if (flip_x < bx.size()) f.add(bx[flip_x], f.one());
    if (flip_y < by.size()) f.add(by[flip_y], f.one());
    Assignment st;
    st.set(want_x, bx).set(want_y, by).set(t, Vec{tv});
    return st;
  }
};

TEST(GordieHoweBatch, ComposedBitViews) {
  const HF &f = env().hf;
  ComposedViewSystem v;
  auto c = compile(v.cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("GF(2^16) (intermediate): region"), std::string::npos) << r;
  EXPECT_NE(r.find("edge to GF(2^16): squaring-chain masks, degree 16"), std::string::npos)
      << r;
  EXPECT_NE(r.find("edge to GF(2^32): subfield masks, degree 2"), std::string::npos)
      << r;
  EXPECT_NE(r.find("edge to GF(2^64): subfield masks, degree 2"), std::string::npos)
      << r;
  EXPECT_NE(r.find("bit_views=4 words"), std::string::npos) << r;
  auto prep = c->prepare(v.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(v.witness(), rng);
  EXPECT_TRUE(prep.verify(proof));
  // Wrong public bits: one through each intermediate count.
  EXPECT_FALSE(c->prepare(v.statement(45)).verify(proof));
  EXPECT_FALSE(c->prepare(v.statement(SIZE_MAX, 100)).verify(proof));
  // A view wire set to the claimed wrong bit, the circuit holding on its
  // wires: the input claim goes through the word.
  for (size_t which : {0, 1}) {
    SCOPED_TRACE(which);
    const size_t flip = which == 0 ? 45 : 100;
    auto bad = which == 0 ? c->prepare(v.statement(flip))
                          : c->prepare(v.statement(SIZE_MAX, flip));
    ProveOptions opt;
    opt.require_satisfied = false;
    const size_t target = which == 0 ? v.xb.id : v.yb.id;
    opt.tamper = [&](size_t id, SysValue &x) {
      if (id == target) f.add(std::get<Vec>(x)[flip], f.one());
    };
    EXPECT_FALSE(bad.verify(bad.prove(v.witness(), rng, opt)));
  }
  // A word off the affine row (yb70 flipped; the circuit's statement
  // follows the word, the row's does not).
  {
    Assignment w = v.witness();
    Vec y = v.ys();
    f.add(y[0], SubfieldInfo<HF>::get(f, 64).word(f, uint64_t(1) << 6));
    w.set(v.Y, y);
    Assignment st = v.statement();
    st.set(v.want_y, ComposedViewSystem::bits_of(y, v.sy, 64));
    auto off = c->prepare(st);
    EXPECT_FALSE(off.verify(off.prove(w, rng)));
  }
}

// An affine row on packed bits and on a bit view: the bits stay
// packed (no unpacked coordinates, no x(x - 1) checks), the row joins the
// bit node's measurement with the GKR claim, and a witness or statement
// that breaks the row is rejected.
TEST(GordieHoweBatch, AffineRowReadsPackedBits) {
  const HF &f = env().hf;
  Sys cs("gh-affine-bits");
  auto &H = cs.domain(env().profile(), "H");
  auto b = H.priv(Bit{}, "b", 32);
  auto w = H.priv(Subfield{}, "w", 2);
  auto v = H.bits("v", w);
  auto t = H.pub(Field{}, "t", 1);
  // A circuit reads both, so GKR's input claim reads the bit node too.
  L::gkr(H, "b0 b1 + v3 = b2 + v3 (b0 b1 = b2)", depends_on(b, v),
        [](const auto &lc, const auto &b, const auto &v) {
          lc.assert_eq(lc.add(lc.mul(b[0], b[1]), v[3]),
                       lc.add(b[2], v[3]));
        });
  // K coefficients on packed bits and view bits, against a statement.
  const HElt k0 = f.of_scalar_field(0x1234567ull), k1 = f.of_scalar_field(99);
  H.affine("k0 b5 + k1 b17 + k0 v3 + v20 = t",
           k0 * b.at(0, 5) + k1 * b.at(0, 17) + k0 * v.at(0, 3) +
               v.at(0, 20) - t);
  auto c = compile(cs);
  const std::string r = c->report();
  EXPECT_EQ(r.find("unpacked bit cell"), std::string::npos) << r;
  EXPECT_NE(r.find("cell_bit_checks=0"), std::string::npos) << r;
  EXPECT_NE(r.find("packed_bits=32 (2 words committed"), std::string::npos)
      << r;
  Vec bv(32, f.zero());
  for (size_t i : {0, 1, 2, 5, 9}) bv[i] = f.one();
  const Vec wv = {f.of_scalar(0x0008 | 0x0002), f.of_scalar(0x0010)};
  // v3 = bit 3 of w0 = 1, v20 = bit 4 of w1 = 1, b5 = 1, b17 = 0.
  const HElt tv = f.addf(f.addf(k0, k0), f.one());
  Assignment st, wit;
  st.set(t, Vec{tv});
  wit.set(b, bv).set(w, wv);
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  const auto proof = prep.prove(wit, rng);
  EXPECT_TRUE(prep.verify(proof));
  // Another statement.
  Assignment st2;
  st2.set(t, Vec{f.addf(tv, f.one())});
  EXPECT_FALSE(c->prepare(st2).verify(proof));
  // A packed bit off the row (b17 = 1; the circuit still holds).
  Assignment w2 = wit;
  Vec b2 = bv;
  b2[17] = f.one();
  w2.set(b, b2);
  EXPECT_FALSE(prep.verify(prep.prove(w2, rng)));
  // A view bit off the row (v20 = 0; the circuit reads v3 only).
  Assignment w3 = wit;
  w3.set(w, Vec{wv[0], f.zero()});
  EXPECT_FALSE(prep.verify(prep.prove(w3, rng)));
}

// A Bit cell that only an affine row reads, in each PQ profile's hash field
// (GF(2^128) at the ROM parameters, GF(2^256) at the QROM parameters): the bits
// are packed sixteen to a GF(2^16) word with no Boolean check, and the row
// reaches them through the bit node's stage alone. Without a circuit the domain
// runs no GKR, so the row is the stage's only claim; with a circuit that reads
// only a Subfield cell, the GKR input claim does not read the bit node. Either
// way an honest proof verifies, and a wrong statement or a bit off the row is
// rejected.
template <class P>
void affine_only_bits(bool with_circuit) {
  using G = typename P::HashField;
  using PH = typename P::ProtocolHash;
  using E = typename G::Elt;
  using V = std::vector<E>;
  const G f;
  const LCH14ReedSolomonFactory<G> rs(f);
  ConstraintSystem<PH, G> cs("gh-affine-only-bits");
  auto &H = cs.domain(h_profile<G, PH>(f, rs, 4, 64, 0), "H");
  auto b = H.priv(Bit{}, "b", 40);
  auto t = H.pub(Field{}, "t", 1);
  auto w = H.priv(Subfield{}, "w", 2);
  if (with_circuit) {
    L::gkr(H, "w0 = w1", depends_on(w),
           [](const auto &lc, const auto &w) { lc.assert_eq(w[0], w[1]); });
  }
  const E k0 = f.of_scalar_field(0x1234567ull), k1 = f.of_scalar_field(99);
  H.affine("k0 b5 + k1 b17 + b39 = t",
           k0 * b.at(0, 5) + k1 * b.at(0, 17) + b.at(0, 39) - t);
  auto c = compile(cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("cell_bit_checks=0"), std::string::npos) << r;
  EXPECT_EQ(r.find("Boolean checks n="), std::string::npos) << r;
  // 40 bits and 8 zero bits in three words.
  EXPECT_NE(r.find("packed_bits=48 (3 words committed, 8 zero)"),
            std::string::npos)
      << r;
  EXPECT_EQ(r.find("circuit: none (no circuit constraint, no GKR)") ==
                std::string::npos,
            with_circuit)
      << r;
  V bv(40, f.zero());
  for (size_t i : {0, 5, 9, 39}) bv[i] = f.one();
  const V wv = {f.of_scalar(0x0101), f.of_scalar(0x0101)};
  // b5 = 1, b17 = 0, b39 = 1.
  const E tv = f.addf(k0, f.one());
  typename ConstraintSystem<PH, G>::Assignment st, wit;
  st.set(t, V{tv});
  wit.set(b, bv).set(w, wv);
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  const auto proof = prep.prove(wit, rng);
  EXPECT_TRUE(prep.verify(proof));
  // Another statement.
  typename ConstraintSystem<PH, G>::Assignment st2;
  st2.set(t, V{f.addf(tv, f.one())});
  EXPECT_FALSE(c->prepare(st2).verify(proof));
  // A bit off the row: b17 = 1, or b39 = 0.
  typename ConstraintSystem<PH, G>::ProveOptions opt;
  opt.require_satisfied = false;
  for (size_t i : {size_t(17), size_t(39)}) {
    auto w2 = wit;
    V b2 = bv;
    b2[i] = b2[i] == f.one() ? f.zero() : f.one();
    w2.set(b, b2);
    EXPECT_FALSE(prep.verify(prep.prove(w2, rng, opt))) << i;
  }
}

template <class P>
class GordieHoweAffineBitsProfile : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweAffineBitsProfile, param_sets::Profiles,
                 param_sets::ProfileName);
TYPED_TEST(GordieHoweAffineBitsProfile, AffineOnlyBitsNoGkr) {
  affine_only_bits<TypeParam>(/*with_circuit=*/false);
}
TYPED_TEST(GordieHoweAffineBitsProfile, AffineOnlyBitsBesideCircuit) {
  affine_only_bits<TypeParam>(/*with_circuit=*/true);
}

}  // namespace
}  // namespace proofs::gordiehowe
