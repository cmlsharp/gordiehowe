// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_test binary): byte packing, statement
// rows, derived bits, scopes, subfields, packing trees, batches and the
// field skip.

#include "gordiehowe/tests/gordiehowe_test.h"

namespace proofs::gordiehowe {
namespace {

template <class F>
void pack_roundtrip(const F &f, size_t per_element) {
  std::vector<uint8_t> b(100);
  for (size_t i = 0; i < b.size(); ++i) b[i] = uint8_t(37 * i + 11);
  const auto e = pack_bytes(f, b);
  EXPECT_EQ(e.size(), (b.size() + per_element - 1) / per_element);
  const size_t k = pack_bytes_per_coordinate(f);
  std::vector<uint8_t> back;
  for (const auto &x : e) {
    uint8_t buf[F::kBytes];
    f.to_bytes_field(buf, x);
    for (size_t j = 0; j < F::kBytes / F::kSubFieldBytes; ++j)
      for (size_t i = 0; i < k; ++i)
        back.push_back(buf[j * F::kSubFieldBytes + i]);
  }
  back.resize(b.size());
  EXPECT_EQ(back, b);
}
TEST(GordieHowe, BytePacking) {
  pack_roundtrip(env().af, 28);  // 4 Goldilocks coordinates of 7 bytes
  pack_roundtrip(GF2_256<>(), 32);
  pack_roundtrip(GF2_128<>(), 16);
  const Fp14 base(12289);
  const Fp14_9 fq(base, Fp14_9::beta_);
  pack_roundtrip(fq, 9);  // one byte per F_q coordinate
}

// A Bytes statement with a per-row codec, read by a public computation, and
// a field statement with a per-row codec: one malformed row rejects the
// statement, verify() returns false, and rejected_row() names the row.
TEST(GordieHowe, StatementBytesAndRows) {
  const AF &af = env().af;
  Sys cs("gh-statement-bytes");
  auto &A = cs.domain(env().profile(), "A");
  auto pk = A.pub_bytes("pk", Shape{3, 4},
      per_row(computes("first_below", {100}),
              [](const std::vector<uint8_t> &row) { return row[0] < 100; }));
  auto key = A.pub(Subfield{}, "key", Shape{2, 2},
      per_row(computes("below", {50}), [&af](const Tensor<AElt> &row) {
        for (const auto &e : row)
          if (nat_of(af, e) >= 50) return false;
        return true;
      }));
  auto sums = A.pub(Field{}, "sums", 3, depends_on(pk), computes("row_sums"),
                               [&af](const std::vector<uint8_t> &b) {
                                 Vec out(3, af.zero());
                                 for (size_t i = 0; i < 12; ++i)
                                   af.add(out[i / 4], af.of_scalar(b[i]));
                                 return out;
                               });
  auto x = A.priv(Subfield{}, "x", 3);
  auto y = A.priv(Subfield{}, "y", Shape{2, 2});
  A.affine("x = row sums", x - sums);
  A.affine("y = key", y - key);
  assert_zero(x[0] * x[2] - af.of_scalar(200), "x0 x2 = 200")
      .pin(Placement::kCircuit);
  auto c = compile(cs);
  auto vec = [&](std::initializer_list<uint64_t> v) {
    Vec o;
    for (uint64_t a : v) o.push_back(af.of_scalar(a));
    return o;
  };
  const std::vector<uint8_t> bytes = {1, 2, 3, 4, 10, 20, 30, 40, 5, 5, 5, 5};
  Assignment st, w;
  st.set(pk, bytes).set(key, vec({1, 2, 3, 4}));
  w.set(x, vec({10, 100, 20})).set(y, vec({1, 2, 3, 4}));
  auto prep = c->prepare(st);
  EXPECT_EQ(prep.rejected_statement(), "");
  SecureRandomEngine rng;
  const auto proof = prep.prove(w, rng);
  EXPECT_TRUE(prep.verify(proof));
  // Other bytes: the statement absorbs them (packed), so the proof fails.
  auto other = bytes;
  other[11] = 6;
  Assignment st2 = st;
  st2.set(pk, other);
  EXPECT_FALSE(c->prepare(st2).verify(proof));
  // A malformed row of each statement.
  auto bad = bytes;
  bad[4] = 200;
  Assignment b1 = st;
  b1.set(pk, bad);
  auto p1 = c->prepare(b1);
  EXPECT_EQ(p1.rejected_statement(), "pk");
  EXPECT_EQ(p1.rejected_row(), 1u);
  EXPECT_FALSE(p1.verify(proof));
  EXPECT_THROW(p1.prove(w, rng), std::runtime_error);
  Assignment b2 = st;
  b2.set(key, vec({1, 2, 3, 77}));
  auto p2 = c->prepare(b2);
  EXPECT_EQ(p2.rejected_statement(), "key");
  EXPECT_EQ(p2.rejected_row(), 1u);
  EXPECT_FALSE(p2.verify(proof));
}

// derive<Bit>: a derived Bit with a Boolean check the core adds; it reads
// as a Bit (an affine row, a circuit). bit_from_unchecked: the same view
// with no check, listed in the report.
TEST(GordieHowe, DerivedBits) {
  const AF &af = env().af;
  Sys cs("gh-derived-bits");
  auto &A = cs.domain(env().profile(), "A");
  auto a = A.priv(Subfield{}, "a", 3);
  auto b = A.priv(Subfield{}, "b", 3);
  // a - b in {0, 1}.
  auto d = A.derive(Bit{}, "d", a - b);
  auto u = A.bit_from_unchecked("u", a - b);
  assert_equal(d[0], u[0], "d0 u0").pin(Placement::kCircuit);
  auto c = compile(cs);
  EXPECT_NE(c->report().find("derived_bit_checks=3"), std::string::npos)
      << c->report();
  EXPECT_NE(c->report().find("unchecked Bit 'u' n=3: bit_from_unchecked"),
            std::string::npos)
      << c->report();
  auto vec = [&](std::initializer_list<uint64_t> v) {
    Vec o;
    for (uint64_t x : v) o.push_back(af.of_scalar(x));
    return o;
  };
  auto prep = c->prepare({});
  SecureRandomEngine rng;
  Assignment ok;
  ok.set(a, vec({5, 9, 1})).set(b, vec({5, 8, 0}));
  EXPECT_TRUE(prep.verify(prep.prove(ok, rng)));
  // a - b = 2 at coordinate 2: derive<Bit>'s check fails.
  Assignment bad;
  bad.set(a, vec({5, 9, 2})).set(b, vec({5, 8, 0}));
  ProveOptions opt;
  opt.require_satisfied = false;
  EXPECT_FALSE(prep.verify(prep.prove(bad, rng, opt)));
  // Without derive<Bit>, the unchecked view accepts it.
  Sys t("gh-unchecked-bit");
  auto &B = t.domain(env().profile(), "B");
  auto a2 = B.priv(Subfield{}, "a", 3);
  auto b2 = B.priv(Subfield{}, "b", 3);
  auto u2 = B.bit_from_unchecked("u", a2 - b2);
  assert_equal(u2[2] * a2[0], a2[2] * a2[0], "u0").pin(Placement::kCircuit);
  auto ct = compile(t);
  auto pt = ct->prepare({});
  Assignment bad2;
  bad2.set(a2, vec({5, 9, 2})).set(b2, vec({5, 8, 0}));
  EXPECT_TRUE(pt.verify(pt.prove(bad2, rng)));
}

// Scopes: one block declared at the root, in a scope and in a nested
// scope. Names and challenge labels carry the prefix, so the three copies
// do not clash; the scopes' names and parameters enter the digest; the
// report groups node lines by scope.
using SysScope = Scope;
template <class D>
Ref<AF> scoped_block(const SysScope &sc, D &A, const Vec &k) {
  const AF &af = env().af;
  auto x = sc[A].priv(Subfield{}, "x", 2);
  auto key = sc[A].pub(Field{}, "key", 2);
  auto y = sc[A].priv(Field{}, "y", 2, depends_on(x, key),
                                      [&af](const AElt &a, const AElt &b) {
                                        return af.addf(a, b);
                                      });
  auto g = sc[A].challenge("gamma");
  assert_equal(g * y, g * (x + key), sc.name("c")).pin(Placement::kCircuit);
  (void)k;
  return key;
}
TEST(GordieHowe, Scopes) {
  const AF &af = env().af;
  auto build = [&](Sys &cs, uint64_t param) {
    auto &A = cs.domain(env().profile(), "A");
    std::vector<Ref<AF>> keys;
    keys.push_back(scoped_block(cs, A, {}));
    const auto s0 = cs.scope("sig0", computes("member", {param}));
    keys.push_back(scoped_block(s0, A, {}));
    const auto n = s0.scope("norm");
    keys.push_back(scoped_block(n, A, {}));
    return keys;
  };
  Sys cs("gh-scopes");
  const auto keys = build(cs, 1);
  const auto &N = cs.graph().nodes;
  EXPECT_EQ(N[keys[0].id].name, "key");
  EXPECT_EQ(N[keys[1].id].name, "sig0.key");
  EXPECT_EQ(N[keys[2].id].name, "sig0.norm.key");
  auto c = compile(cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("challenge sig0.norm.gamma"), std::string::npos) << r;
  EXPECT_NE(r.find("  scope sig0\n  ["), std::string::npos) << r;
  EXPECT_NE(r.find("  scope sig0.norm\n  ["), std::string::npos) << r;
  // A scope of an existing name.
  EXPECT_THROW((void)cs.scope("sig0"), CompileError);
  // The scope's parameters enter the digest.
  Sys s2("gh-scopes");
  build(s2, 2);
  EXPECT_NE(compile(s2)->digest(), c->digest());
  // The three blocks prove together.
  auto vec = [&](std::initializer_list<uint64_t> v) {
    Vec o;
    for (uint64_t a : v) o.push_back(af.of_scalar(a));
    return o;
  };
  Assignment st, w;
  for (const auto &k : keys) st.set(k, vec({3, 4}));
  for (size_t id = 0; id < N.size(); ++id)
    if (N[id].kind == Kind::kPrivateInput)
      w.set(Ref<AF>{id, 2, &af, nullptr}, vec({5, 6}));
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
}

// System-level constraints take their domain from their operands' field;
// public operands belong to it. A second domain of a field, or a constraint
// that reads no value of a domain, is a CompileError.
TEST(GordieHowe, SystemLevelConstraints) {
  const AF &af = env().af;
  Sys cs("gh-system-constraints");
  auto &A = cs.domain(env().profile(), "A");
  EXPECT_THROW(cs.domain(env().profile(), "B"), CompileError);
  auto x = A.priv(Subfield{}, "x", 2);
  auto z = A.priv(Field{}, "z", 2);
  auto k = A.pub(Field{}, "k", 2);
  cs.affine("x = k", x - k);
  assert_equal(x[0] * x[1], k[0] * k[1], "x0 x1").pin(Placement::kCircuit);
  cs.quadratic(z, z, z);
  auto h = assert_range(x, 2048, "x");
  EXPECT_EQ(h.domain, A.index);
  EXPECT_THROW(cs.affine("k = k", k - k), CompileError);
  auto c = compile(cs);
  auto vec = [&](std::initializer_list<uint64_t> v) {
    Vec o;
    for (uint64_t a : v) o.push_back(af.of_scalar(a));
    return o;
  };
  Assignment st, w;
  st.set(k, vec({3, 4}));
  w.set(x, vec({3, 4})).set(z, vec({1, 0}));
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
}

// Subfields by degree (SubfieldInfo): each basis lies in its subfield, the
// codec round-trips a sample, and the coordinates rebuild the element. The
// designated subfield keeps the field's own basis and codec.
template <class F>
void check_subfield(const F &f, size_t d) {
  const auto &s = SubfieldInfo<F>::get(f, d);
  EXPECT_EQ(s.degree, d);
  EXPECT_EQ(s.basis.size(), d);
  for (const auto &b : s.basis) EXPECT_TRUE(s.contains(f, b)) << d;
  SecureRandomEngine rng;
  for (size_t t = 0; t < 8; ++t) {
    const auto x = s.sample(f, rng);
    EXPECT_TRUE(s.contains(f, x)) << d;
    std::vector<uint8_t> b(s.bytes);
    s.to_bytes(f, b.data(), x);
    EXPECT_EQ(s.of_bytes(f, b.data()), x) << d;
    const auto c = s.coordinates(f, x);
    auto y = f.zero();
    for (size_t i = 0; i < d; ++i) f.add(y, f.mulf(c[i], s.basis[i]));
    EXPECT_EQ(y, x) << d;
  }
  // An element outside a proper subfield.
  if (d < field_degree<F>()) {
    std::vector<uint8_t> raw(F::kBytes);
    for (size_t i = 0; i < raw.size(); ++i) raw[i] = uint8_t(17 * i + 5);
    const auto z = *f.of_bytes_field(raw.data());
    EXPECT_FALSE(s.contains(f, z)) << d;
  }
}

TEST(GordieHowe, SubfieldsByDegree) {
  const GF2_128<> f2;
  for (size_t d : {16, 8, 32, 64}) check_subfield(f2, d);
  EXPECT_EQ(SubfieldInfo<GF2_128<>>::get(f2, 16).basis[3], f2.beta(3));
  const GF2_256<> f3;
  for (size_t d : {16, 32}) check_subfield(f3, d);
  for (size_t d : {1, 2}) check_subfield(env().af, d);
  EXPECT_NE(SubfieldInfo<AF>::unsupported(3), "");
  EXPECT_NE(SubfieldInfo<GF2_128<>>::unsupported(128 + 1), "");
}

// A statement of type Subfield<GF<2>> in Goldilocks^4: its type enters the
// description, a coordinate outside GF(p^2) is a malformed statement, and a
// Subfield<GF<1>> (the designated subfield) is stored as Subfield<>.
TEST(GordieHowe, StatementInADeclaredSubfield) {
  const AF &af = env().af;
  Sys cs("gh-subfield-statement");
  auto &A = cs.domain(env().profile(), "A");
  auto k = A.pub(Subfield<GF<2>>{}, "k", 2);
  auto k1 = A.pub(Subfield<GF<1>>{}, "k1", 1);
  auto x = A.priv(Field{}, "x", 2);
  A.affine("x = k", x - k);
  assert_equal(x[0] - x[1], k1[0], "x0 - x1 = k1").pin(Placement::kCircuit);
  auto c = compile(cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("k1"), std::string::npos);
  const auto &g2 = SubfieldInfo<AF>::get(af, 2);
  const AElt a = af.addf(af.of_scalar(3), af.mulf(af.of_scalar(5), g2.basis[1]));
  const AElt b = af.addf(af.of_scalar(7), af.mulf(af.of_scalar(5), g2.basis[1]));
  Assignment st, w;
  st.set(k, Vec{a, b}).set(k1, Vec{af.subf(a, b)});
  w.set(x, Vec{a, b});
  auto prep = c->prepare(st);
  EXPECT_EQ(prep.rejected_statement(), "");
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  // X is outside GF(p^2): the statement is malformed.
  AElt out = af.zero();
  out.e[1] = af.base_field().one();
  Assignment bad = st;
  bad.set(k, Vec{out, b});
  EXPECT_EQ(c->prepare(bad).rejected_statement(), "k");
}

// The packing planner (tree.h): parents, intermediates, modes and the
// prefix-row test's reach.
TEST(GordieHowe, PackingTreeRule) {
  auto parent = [](const compiler::PackingTree &t, size_t d) {
    const int i = t.node_of(d);
    return i < 0 || t.nodes[size_t(i)].parent < 0
               ? size_t(0)
               : t.nodes[size_t(t.nodes[size_t(i)].parent)].degree;
  };
  // Today's H: GF(2) < GF(2^16) < GF(2^128), squaring-chain masks then
  // subfield masks.
  auto h = compiler::PackingTree::plan(128, 16, true, {16, 1});
  EXPECT_EQ(h.error, "");
  EXPECT_EQ(parent(h, 1), 16u);
  EXPECT_EQ(parent(h, 16), 128u);
  EXPECT_TRUE(h.squaring_chain(h.node_of(1)));
  EXPECT_FALSE(h.squaring_chain(h.node_of(16)));
  // Bits alone: the edge of degree 128 splits at GF(2^16), the even split
  // whose subfield-masks base the prefix-row test covers (GF(2^8) would
  // need a squaring-chain-masks stage over it).
  auto b = compiler::PackingTree::plan(128, 16, true, {1});
  EXPECT_EQ(b.error, "");
  EXPECT_EQ(parent(b, 1), 16u);
  EXPECT_FALSE(b.nodes[size_t(b.node_of(16))].declared);
  EXPECT_EQ(b.split(1, 256), (std::vector<size_t>{1, 16, 256}));
  // Today's A: GF(p) < GF(p^4), subfield masks.
  auto a = compiler::PackingTree::plan(4, 1, false, {1});
  EXPECT_EQ(a.error, "");
  EXPECT_EQ(parent(a, 1), 4u);
  // GF(2^32) declared: GF(2^16) packs into it.
  auto w = compiler::PackingTree::plan(128, 16, true, {1, 32, 16});
  EXPECT_EQ(w.error, "");
  EXPECT_EQ(parent(w, 1), 16u);
  EXPECT_EQ(parent(w, 16), 32u);
  EXPECT_EQ(parent(w, 32), 128u);
  // GF(2^32) without GF(2^16): bits split at GF(2^16) under D_max = 16, and
  // pack straight into GF(2^32) under D_max = 32.
  auto w16 = compiler::PackingTree::plan(128, 16, true, {1, 32});
  EXPECT_EQ(parent(w16, 1), 16u);
  EXPECT_EQ(parent(w16, 16), 32u);
  auto w32 = compiler::PackingTree::plan(128, 16, true, {1, 32}, 32);
  EXPECT_EQ(parent(w32, 1), 32u);
  // GF(2^8) words: the prefix-row test in GF(2^16) does not cover GF(2^8),
  // so its edge uses squaring-chain masks, 8 squarings per Frobenius
  // twist: into K
  // directly (degree 16, 16 masks and 8 * 120 chain cells), or under a
  // declared GF(2^16) (degree 2, 2 masks and 8 chain cells).
  auto e = compiler::PackingTree::plan(128, 16, true, {8});
  EXPECT_EQ(e.error, "");
  EXPECT_EQ(parent(e, 8), 128u);
  EXPECT_TRUE(e.squaring_chain(e.node_of(8)));
  EXPECT_EQ(e.masks(8, 128), 16u);
  EXPECT_EQ(e.chain_cells(8, 128), 960u);
  auto e16 = compiler::PackingTree::plan(128, 16, true, {1, 8, 16});
  EXPECT_EQ(e16.error, "");
  EXPECT_EQ(parent(e16, 1), 8u);
  EXPECT_EQ(parent(e16, 8), 16u);
  EXPECT_TRUE(e16.squaring_chain(e16.node_of(1)));
  EXPECT_TRUE(e16.squaring_chain(e16.node_of(8)));
  EXPECT_FALSE(e16.squaring_chain(e16.node_of(16)));
  EXPECT_EQ(e16.chain_cells(8, 16), 8u);
  EXPECT_EQ(e16.chain_cells(1, 8), 28u);
  // GF(2^4) in GF(2^256): the edge of degree 64 splits evenly at
  // GF(2^32) (8 * 8), a squaring-chain-masks stage over GF(2^4) under a
  // subfield-masks one.
  auto e4 = compiler::PackingTree::plan(256, 16, true, {4});
  EXPECT_EQ(e4.error, "");
  EXPECT_EQ(parent(e4, 4), 32u);
  EXPECT_TRUE(e4.squaring_chain(e4.node_of(4)));
  EXPECT_FALSE(e4.squaring_chain(e4.node_of(32)));
  // In odd characteristic an uncovered base has no squaring-chain masks.
  auto odd = compiler::PackingTree::plan(4, 2, false, {1});
  EXPECT_NE(odd.error.find("need characteristic 2"), std::string::npos)
      << odd.error;
  // GF(q) in GF(q^6) under GF(q^2) and GF(q^3): equal path costs, so the
  // smaller parent.
  auto six = compiler::PackingTree::plan(6, 1, false, {2, 3, 1});
  EXPECT_EQ(six.error, "");
  EXPECT_EQ(parent(six, 1), 2u);
  EXPECT_EQ(parent(six, 2), 6u);
  EXPECT_EQ(parent(six, 3), 6u);
  // The chains the cost-based planner weighs: the
  // default first, then the single edge and each admissible chain through
  // one intermediate; a binary intermediate above GF(2^64) is not
  // realizable.
  using V = std::vector<size_t>;
  using VV = std::vector<V>;
  auto k = compiler::PackingTree::plan(256, 16, true, {1, 16});
  EXPECT_EQ(k.candidates(16, 256),
            (VV{{16, 256}, {16, 32, 256}, {16, 64, 256}}));
  auto f = compiler::PackingTree::plan(20, 1, false, {1});
  EXPECT_EQ(f.candidates(1, 20),
            (VV{{1, 4, 20}, {1, 20}, {1, 2, 20}, {1, 5, 20}, {1, 10, 20}}));
  // A chosen chain replaces the default one.
  auto kc = compiler::PackingTree::plan(256, 16, true, {1, 16}, 16,
                                        {{{16, 256}, V{16, 64, 256}}});
  EXPECT_EQ(kc.error, "");
  EXPECT_EQ(parent(kc, 16), 64u);
  EXPECT_EQ(parent(kc, 64), 256u);
  EXPECT_FALSE(kc.nodes[size_t(kc.node_of(64))].declared);
  EXPECT_EQ(parent(k, 16), 256u);
}

// A domain over GF(2^128) with values in GF(2), GF(2^16) and GF(2^32): the
// tree GF(2) < GF(2^16) < GF(2^32) < K, with a subfield-masks stage between
// the two subfields. A circuit reads all three; the proof verifies and a wrong
// statement fails.
TEST(GordieHowe, ThreeLevelTree) {
  using KF = GF2_128<>;
  using KElt = KF::Elt;
  using KSys = ConstraintSystem<SHA384, KF>;
  const KF kf;
  const LCH14ReedSolomonFactory<KF> krs(kf);
  DomainProfile<KF, LCH14ReedSolomonFactory<KF>, SHA384> p;
  p.f = &kf;
  p.rsf = &krs;
  p.field_name = "GF(2^128)";
  p.rate = 4;
  p.nreq = 64;
  p.has_subfield = true;
  p.prime = Space::kPrime;
  KSys cs("gh-three-level");
  auto &H = cs.domain(p, "H");
  const auto &g32 = SubfieldInfo<KF>::get(kf, 32);
  auto x = H.priv(Subfield<GF<32>>{}, "x", 3);
  auto y = H.priv(Subfield{}, "y", 2);
  auto b = H.priv(Bit{}, "b", 5);
  auto out = H.pub(Field{}, "out", 1);
  assert_equal(x[0] * x[1] + x[2] * y[0] + y[1] + Expr<KF>(b).sum(), out[0],
               "x0 x1 + x2 y0 + y1 + b = out")
      .pin(Placement::kCircuit);
  auto c = compile(cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("GF(2^16): region"), std::string::npos) << r;
  EXPECT_NE(r.find("edge to GF(2^32): subfield masks, degree 2"), std::string::npos)
      << r;
  EXPECT_NE(r.find("GF(2^32): region"), std::string::npos) << r;
  std::vector<KElt> xv = {g32.word(kf, 0x12345678), g32.word(kf, 0x9abcdef1),
                          g32.word(kf, 0x0f0f0f0f)};
  std::vector<KElt> yv = {kf.of_scalar(0x1234), kf.of_scalar(0xbeef)};
  std::vector<KElt> bv = {kf.one(), kf.zero(), kf.one(), kf.one(), kf.zero()};
  KElt o = kf.addf(kf.mulf(xv[0], xv[1]), kf.mulf(xv[2], yv[0]));
  kf.add(o, yv[1]);
  kf.add(o, kf.one());  // three ones
  typename KSys::Assignment st, wit;
  st.set(out, std::vector<KElt>{o});
  wit.set(x, xv).set(y, yv).set(b, bv);
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  const auto proof = prep.prove(wit, rng);
  EXPECT_TRUE(prep.verify(proof));
  typename KSys::Assignment bad = st;
  bad.set(out, std::vector<KElt>{kf.addf(o, kf.one())});
  EXPECT_FALSE(c->prepare(bad).verify(proof));
}

// ThreeLevelTree's system without bits: GF(2^16) < GF(2^32) < K, where only
// the GKR input row reads y's GF(2^16) region, so the GF(2^16) stage routes
// that one row.
struct LoneRowSystem {
  using KF = GF2_128<>;
  using KElt = KF::Elt;
  using KSys = ConstraintSystem<SHA384, KF>;
  const KF kf;
  const LCH14ReedSolomonFactory<KF> krs{kf};
  DomainProfile<KF, LCH14ReedSolomonFactory<KF>, SHA384> p;
  KSys cs{"gh-lone-row"};
  const SubfieldInfo<KF> &g32 = SubfieldInfo<KF>::get(kf, 32);
  Ref<KF, Subfield<GF<32>>, Committed> x;
  Ref<KF, Subfield<>, Committed> y;
  Ref<KF, Field, Public> out;
  decltype(compile(std::declval<KSys &>())) c;

  LoneRowSystem() {
    p.f = &kf;
    p.rsf = &krs;
    p.field_name = "GF(2^128)";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    auto &H = cs.domain(p, "H");
    x = H.priv(Subfield<GF<32>>{}, "x", 3);
    y = H.priv(Subfield{}, "y", 2);
    out = H.pub(Field{}, "out", 1);
    assert_equal(x[0] * x[1] + x[2] * y[0] + y[1], out[0],
                 "x0 x1 + x2 y0 + y1 = out")
        .pin(Placement::kCircuit);
    c = compile(cs);
  }
  std::vector<KElt> xv() const {
    return {g32.word(kf, 0x12345678), g32.word(kf, 0x9abcdef1),
            g32.word(kf, 0x0f0f0f0f)};
  }
  KElt output(const std::vector<KElt> &yv) const {
    const auto x = xv();
    KElt o = kf.addf(kf.mulf(x[0], x[1]), kf.mulf(x[2], yv[0]));
    kf.add(o, yv[1]);
    return o;
  }
};

// A stage that one row reaches runs that row as it is: it writes no label
// and draws no weight, and its point is no stream point of the plan (only
// the root and Ligero's linear test are). The proof verifies, and a wrong
// statement, which makes the lone row (the GKR input row, whose right-hand
// side binds the public output) false, is rejected.
TEST(GordieHowe, LoneRowStageDrawsNoWeight) {
  LoneRowSystem t;
  using KElt = LoneRowSystem::KElt;
  const auto &sp = t.c->compiled_domain(0).plan().stream_points;
  ASSERT_EQ(sp.size(), 2u);
  EXPECT_EQ(sp[0].name, "root");
  EXPECT_EQ(sp[1].name, "ligero.alphal");
  const std::vector<KElt> yv = {t.kf.of_scalar(0x1234), t.kf.of_scalar(0xbeef)};
  const KElt o = t.output(yv);
  typename LoneRowSystem::KSys::Assignment st, wit;
  st.set(t.out, std::vector<KElt>{o});
  wit.set(t.x, t.xv()).set(t.y, yv);
  auto prep = t.c->prepare(st);
  std::vector<size_t> d;
  auto &hooks = t.c->compiled_domain(0).tree_test_hooks();
  hooks.stage_draws = &d;
  SecureRandomEngine rng;
  const auto proof = prep.prove(wit, rng);
  EXPECT_TRUE(prep.verify(proof));
  hooks.stage_draws = nullptr;
  // One stage run proving, one verifying; neither draws.
  EXPECT_EQ(d, (std::vector<size_t>{0, 0}));
  typename LoneRowSystem::KSys::Assignment bad = st;
  bad.set(t.out, std::vector<KElt>{t.kf.addf(o, t.kf.one())});
  EXPECT_FALSE(t.c->prepare(bad).verify(proof));
}

// The stage routing is structural. In LoneRowSystem, with the input row's
// coefficients on y zero (TreeTestHooks::zero_inputs, prover and verifier
// alike; y = 0, so the row still holds) the row still reads y's region: the
// GF(2^16) stage runs it as before, and the proof verifies. (Routing by
// coefficient values would leave the stage no row, and the proof would fail.)
TEST(GordieHowe, StageRoutingIgnoresZeroCoefficients) {
  LoneRowSystem t;
  using KElt = LoneRowSystem::KElt;
  const std::vector<KElt> yv = {t.kf.zero(), t.kf.zero()};
  typename LoneRowSystem::KSys::Assignment st, wit;
  st.set(t.out, std::vector<KElt>{t.output(yv)});
  wit.set(t.x, t.xv()).set(t.y, yv);
  auto prep = t.c->prepare(st);
  // y's circuit inputs.
  std::vector<size_t> y_inputs;
  for (const auto &in : t.c->compiled_domain(0).plan().inputs)
    if (in.id == t.y.id)
      for (size_t i = 0; i < in.n; ++i) y_inputs.push_back(in.at + i);
  ASSERT_EQ(y_inputs.size(), 2u);
  // Each stage's weights, proving and then verifying.
  auto &hooks = t.c->compiled_domain(0).tree_test_hooks();
  auto draws = [&](bool zero) {
    std::vector<size_t> d;
    hooks.zero_inputs = zero ? &y_inputs : nullptr;
    hooks.stage_draws = &d;
    SecureRandomEngine rng;
    const auto proof = prep.prove(wit, rng);
    const size_t proved = d.size();
    EXPECT_TRUE(prep.verify(proof)) << "zero coefficients " << zero;
    hooks.zero_inputs = nullptr;
    hooks.stage_draws = nullptr;
    EXPECT_EQ(proved, 1u);
    EXPECT_EQ(std::vector<size_t>(d.begin(), d.begin() + long(proved)),
              std::vector<size_t>(d.begin() + long(proved), d.end()))
        << "prover and verifier draw alike";
    d.resize(proved);
    return d;
  };
  const auto honest = draws(false);
  EXPECT_EQ(draws(true), honest);
}

// GF(2^8) values in GF(2^128), whose base the prefix-row test in GF(2^16)
// does not cover: a squaring-chain-masks stage with 8 squarings per
// Frobenius twist. Alone they pack into K directly (GF(2^8) <16 K, the
// root's stage); beside Subfield<> values and bits the tree is
// GF(2) <8 GF(2^8) <2 GF(2^16) <8 K (two squaring-chain-masks stages, then
// the subfield-masks root stage). An affine row, a field
// batch (a b + c over GF(2^8) words) and a circuit read the GF(2^8) values.
// The proof verifies; a wrong statement, a value off the affine row and a
// word off the batch's relation are rejected.
TEST(GordieHowe, SquaringChainStageOverGF256) {
  using KF = GF2_128<>;
  using KElt = KF::Elt;
  using KSys = ConstraintSystem<SHA384, KF>;
  using KVec = std::vector<KElt>;
  const KF kf;
  const LCH14ReedSolomonFactory<KF> krs(kf);
  DomainProfile<KF, LCH14ReedSolomonFactory<KF>, SHA384> p;
  p.f = &kf;
  p.rsf = &krs;
  p.field_name = "GF(2^128)";
  p.rate = 4;
  p.nreq = 64;
  p.has_subfield = true;
  p.prime = Space::kPrime;
  const auto &g8 = SubfieldInfo<KF>::get(kf, 8);
  constexpr size_t n = 20;
  for (bool alone : {true, false}) {
    SCOPED_TRACE(alone);
    KSys cs("gh-chain-gf256");
    auto &H = cs.domain(p, "H");
    auto x = H.priv(Subfield<GF<8>>{}, "x", 3);
    auto T = H.priv(Subfield<GF<8>>{}, "T", 3 * n);
    auto out = H.pub(Field{}, "out", 1);
    compiler::FieldRelation<KF> abc{
        "ab+c", 3, {{kf.one(), {0, 1}}, {kf.one(), {2}}}};
    H.batch("words", std::vector<Ref<KF, Subfield<GF<8>>, Committed>>{T}, abc,
            compiler::AffineOperandMap<KF>::columns(kf, "columns", 3, n), 4);
    H.affine("x2 = x0 + x1", x.at(0, 2) - x.at(0, 0) - x.at(0, 1));
    std::vector<Ref<KF, Bit, Committed>> bits;
    std::vector<Ref<KF, Subfield<>, Committed>> ys;
    if (alone) {
      assert_equal(x[0] * x[1] + T[0], out[0], "x0 x1 + T0 = out")
          .pin(Placement::kCircuit);
    } else {
      auto y = H.priv(Subfield{}, "y", 2);
      auto b = H.priv(Bit{}, "b", 12);
      ys.push_back(y);
      bits.push_back(b);
      assert_equal(x[0] * x[1] + T[0] + y[0] * y[1] + Expr<KF>(b).sum(),
                   out[0], "x0 x1 + T0 + y0 y1 + b = out")
          .pin(Placement::kCircuit);
    }
    auto c = compile(cs);
    const std::string r = c->report();
    if (alone) {
      EXPECT_NE(r.find("GF(2^8): region"), std::string::npos) << r;
      EXPECT_NE(r.find("edge to GF(2^128): squaring-chain masks, degree 16"),
                std::string::npos)
          << r;
      EXPECT_NE(r.find("16 masks and 960 chain cells in K (960 quadratic "
                       "constraints; 8 squarings per Frobenius twist"),
                std::string::npos)
          << r;
    } else {
      EXPECT_NE(r.find("edge to GF(2^8): squaring-chain masks, degree 8"), std::string::npos)
          << r;
      EXPECT_NE(r.find("edge to GF(2^16): squaring-chain masks, degree 2"), std::string::npos)
          << r;
      EXPECT_NE(r.find("2 masks and 8 chain cells in K"), std::string::npos)
          << r;
      EXPECT_NE(r.find("edge to GF(2^128): subfield masks, degree 8"),
                std::string::npos)
          << r;
    }
    std::mt19937_64 g(11);
    KVec xv = {g8.word(kf, 0x5a), g8.word(kf, 0xc3), kf.zero()};
    xv[2] = kf.addf(xv[0], xv[1]);
    KVec tv(3 * n);
    for (size_t i = 0; i < n; ++i) {
      tv[i] = g8.word(kf, g() & 0xff);
      tv[n + i] = g8.word(kf, g() & 0xff);
      tv[2 * n + i] = kf.mulf(tv[i], tv[n + i]);  // a b + c = 0
    }
    KVec yv = {kf.of_scalar(0x1234), kf.of_scalar(0xbeef)};
    KVec bv(12);
    for (size_t i = 0; i < 12; ++i) bv[i] = (0x9b5 >> i) & 1 ? kf.one() : kf.zero();
    auto value = [&](const KVec &x, const KVec &t) {
      KElt o = kf.addf(kf.mulf(x[0], x[1]), t[0]);
      if (!alone) {
        kf.add(o, kf.mulf(yv[0], yv[1]));
        for (const auto &e : bv) kf.add(o, e);
      }
      return o;
    };
    auto statement = [&](const KVec &x, const KVec &t) {
      typename KSys::Assignment st;
      st.set(out, KVec{value(x, t)});
      return st;
    };
    auto wit = [&](const KVec &xx, const KVec &tt) {
      typename KSys::Assignment w;
      w.set(x, xx).set(T, tt);
      if (!alone) w.set(ys[0], yv).set(bits[0], bv);
      return w;
    };
    auto prep = c->prepare(statement(xv, tv));
    SecureRandomEngine rng;
    const auto proof = prep.prove(wit(xv, tv), rng);
    EXPECT_TRUE(prep.verify(proof));
    // A wrong statement.
    {
      typename KSys::Assignment bad;
      bad.set(out, KVec{kf.addf(value(xv, tv), kf.one())});
      EXPECT_FALSE(c->prepare(bad).verify(proof));
    }
    typename KSys::ProveOptions opt;
    opt.require_satisfied = false;
    // x2 off the affine row (the circuit and the statement agree).
    {
      KVec xb = xv;
      kf.add(xb[2], g8.word(kf, 1));
      auto pb = c->prepare(statement(xb, tv));
      EXPECT_FALSE(pb.verify(pb.prove(wit(xb, tv), rng, opt)));
    }
    // A word off a b + c = 0.
    {
      KVec tb = tv;
      kf.add(tb[2 * n + 7], g8.word(kf, 1));
      EXPECT_FALSE(prep.verify(prep.prove(wit(xv, tb), rng, opt)));
    }
  }
}

// Goldilocks^4 with values in GF(p) and GF(p^2): GF(p) < GF(p^2) < K, two
// subfield-masks stages.
TEST(GordieHowe, OddTwoLevelTree) {
  const AF &af = env().af;
  Sys cs("gh-odd-two-level");
  auto &A = cs.domain(env().profile(), "A");
  const auto &g2 = SubfieldInfo<AF>::get(af, 2);
  auto x = A.priv(Subfield<GF<2>>{}, "x", 3);
  auto y = A.priv(Subfield{}, "y", 2);
  auto out = A.pub(Field{}, "out", 1);
  assert_equal(x[0] * x[1] + x[2] * y[0] + y[1], out[0],
               "x0 x1 + x2 y0 + y1 = out")
      .pin(Placement::kCircuit);
  A.affine("x2 = x0 + y0", x.at(0, 2) - x.at(0, 0) - y.at(0, 0));
  auto c = compile(cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("GF(p^1): region"), std::string::npos) << r;
  EXPECT_NE(r.find("edge to GF(p^2): subfield masks, degree 2"), std::string::npos)
      << r;
  auto e2 = [&](uint64_t a, uint64_t b) {
    return af.addf(af.of_scalar(a), af.mulf(af.of_scalar(b), g2.basis[1]));
  };
  Vec xv = {e2(3, 5), e2(7, 11), af.addf(e2(3, 5), af.of_scalar(13))};
  Vec yv = {af.of_scalar(13), af.of_scalar(17)};
  AElt o = af.addf(af.mulf(xv[0], xv[1]), af.mulf(xv[2], yv[0]));
  af.add(o, yv[1]);
  Assignment st, wit;
  st.set(out, Vec{o});
  wit.set(x, xv).set(y, yv);
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(wit, rng)));
  // x2 off the affine row: the opening fails.
  Assignment w2 = wit;
  Vec xb = xv;
  xb[2] = af.addf(xb[2], af.one());
  w2.set(x, xb);
  Assignment st2;
  AElt o2 = af.addf(af.mulf(xb[0], xb[1]), af.mulf(xb[2], yv[0]));
  af.add(o2, yv[1]);
  st2.set(out, Vec{o2});
  auto prep2 = c->prepare(st2);
  EXPECT_FALSE(prep2.verify(prep2.prove(w2, rng)));
}

// A late value of a declared subfield E other than the designated one:
// E = GF(2^32) in GF(2^128) (over the designated GF(2^16)). x = c w, with c
// a challenge in GF(2^16) and w a phase-0 GF(2^32) value, is late; its pad
// is uniform in E, committed packed in E's packing-tree node, and its
// message is E's 32 coordinate bits. A circuit and an affine row read x as
// message - pad. The proof verifies; a changed message bit, which stays in
// E, breaks the relation; an honest prover refuses an x outside E.
TEST(GordieHowe, LateValueInBinarySubfield) {
  using KF = GF2_128<>;
  using KElt = KF::Elt;
  using KSys = ConstraintSystem<SHA384, KF>;
  using KVec = std::vector<KElt>;
  const KF kf;
  const LCH14ReedSolomonFactory<KF> krs(kf);
  DomainProfile<KF, LCH14ReedSolomonFactory<KF>, SHA384> p;
  p.f = &kf;
  p.rsf = &krs;
  p.field_name = "GF(2^128)";
  p.rate = 4;
  p.nreq = 64;
  p.has_subfield = true;
  p.prime = Space::kPrime;
  const auto &g32 = SubfieldInfo<KF>::get(kf, 32);
  KSys cs("gh-late-gf32");
  auto &H = cs.domain(p, "H");
  auto w = H.priv(Subfield<GF<32>>{}, "w", 3);
  auto c = H.challenge("c", Subfield{});
  const KF *pk = &kf;
  auto x = H.priv(Subfield<GF<32>>{}, "x", 3, depends_on(c, w),
                  [pk](const KVec &c, const KVec &w) {
                    KVec x(w.size());
                    for (size_t i = 0; i < w.size(); ++i)
                      x[i] = pk->mulf(c[0], w[i]);
                    return x;
                  });
  assert_equal(x, c * w, "x = c w").pin(Placement::kCircuit);
  H.affine("x2 = x0 + x1", x.at(0, 2) - x.at(0, 0) - x.at(0, 1));
  auto comp = compile(cs);
  const std::string r = comp->report();
  EXPECT_TRUE(comp->late(x));
  EXPECT_NE(r.find("space=subfield GF<32> (auto)"), std::string::npos) << r;
  EXPECT_NE(r.find("GF(2^32): region"), std::string::npos) << r;
  EXPECT_EQ(comp->message_span(x).length, 3u * 4u);
  KVec wv = {g32.word(kf, 0x12345678), g32.word(kf, 0x9abcdef1), kf.zero()};
  wv[2] = kf.addf(wv[0], wv[1]);
  typename KSys::Assignment st, wit;
  wit.set(w, wv);
  auto prep = comp->prepare(st);
  SecureRandomEngine rng;
  const auto proof = prep.prove(wit, rng);
  EXPECT_TRUE(prep.verify(proof));
  auto bad = proof;
  bad[comp->message_span(x).offset] ^= 1;
  EXPECT_FALSE(prep.verify(bad));
  // x off E: the prover refuses it.
  typename KSys::ProveOptions opt;
  const size_t xid = x.id;
  opt.tamper = [xid, pk](size_t id, typename KSys::Value &v) {
    if (id != xid) return;
    auto &e = std::get<KVec>(v);
    pk->add(e[0], pk->of_scalar_field(0b10));
  };
  EXPECT_THROW(prep.prove(wit, rng, opt), std::runtime_error);
}

// The same in odd characteristic, E = GF(p^2) in Goldilocks^4 (over the
// designated prime field): the message is E's two prime-field
// coordinates, and a coordinate at or above p is refused when the message
// is decoded.
TEST(GordieHowe, LateValueInOddSubfield) {
  const AF &af = env().af;
  const auto &g2 = SubfieldInfo<AF>::get(af, 2);
  Sys cs("gh-late-gfp2");
  auto &A = cs.domain(env().profile(), "A");
  auto w = A.priv(Subfield<GF<2>>{}, "w", 3);
  auto c = A.challenge("c", Subfield{});
  const AF *pf = &af;
  auto x = A.priv(Subfield<GF<2>>{}, "x", 3, depends_on(c, w),
                  [pf](const Vec &c, const Vec &w) {
                    Vec x(w.size());
                    for (size_t i = 0; i < w.size(); ++i)
                      x[i] = pf->mulf(c[0], w[i]);
                    return x;
                  });
  assert_equal(x, c * w, "x = c w").pin(Placement::kCircuit);
  A.affine("x2 = x0 + x1", x.at(0, 2) - x.at(0, 0) - x.at(0, 1));
  auto comp = compile(cs);
  const std::string r = comp->report();
  EXPECT_TRUE(comp->late(x));
  EXPECT_NE(r.find("space=subfield GF<2> (auto)"), std::string::npos) << r;
  EXPECT_NE(r.find("GF(p^2): region"), std::string::npos) << r;
  const auto span = comp->message_span(x);
  EXPECT_EQ(span.length, 3u * 2u * AF::kSubFieldBytes);
  auto e2 = [&](uint64_t a, uint64_t b) {
    return af.addf(af.of_scalar(a), af.mulf(af.of_scalar(b), g2.basis[1]));
  };
  Vec wv = {e2(3, 5), e2(7, 11), af.zero()};
  wv[2] = af.addf(wv[0], wv[1]);
  Assignment st, wit;
  wit.set(w, wv);
  auto prep = comp->prepare(st);
  SecureRandomEngine rng;
  const auto proof = prep.prove(wit, rng);
  EXPECT_TRUE(prep.verify(proof));
  // A changed coordinate stays in E and breaks the relation.
  auto bad = proof;
  bad[span.offset] ^= 1;
  EXPECT_FALSE(prep.verify(bad));
  // A coordinate at or above p is not an encoding of E.
  auto noncanonical = proof;
  for (size_t i = 0; i < AF::kSubFieldBytes; ++i)
    noncanonical[span.offset + i] = 0xff;
  EXPECT_FALSE(prep.verify(noncanonical));
  ProveOptions opt;
  const size_t xid = x.id;
  opt.tamper = [xid, pf](size_t id, SysValue &v) {
    if (id != xid) return;
    auto &e = std::get<Vec>(v);
    SecureRandomEngine g;
    pf->add(e[0], g.elt(*pf));
  };
  EXPECT_THROW(prep.prove(wit, rng, opt), std::runtime_error);
}

// Batched relations in odd characteristic (batch.h): a degree-3
// relation abc - d over Goldilocks words in Goldilocks^4, and in the same
// domain a merged batch of two relations (u0^2 - u1 and v0 v1 - v2) in one
// zerocheck. The skip domain is the integers 0..D(w-1), and the terminal
// claims open through the packing tree's root stage. A word off a relation
// is rejected.
TEST(GordieHowe, OddCharacteristicBatches) {
  const AF &af = env().af;
  constexpr size_t n = 100, m = 37;
  Sys cs("gh-odd-batch");
  auto &A = cs.domain(env().profile(), "A");
  auto T = A.priv(Subfield{}, "T", 4 * n);  // columns a, b, c, d
  auto U = A.priv(Subfield{}, "U", 2 * m);
  auto V = A.priv(Subfield{}, "V", 3 * m);
  compiler::FieldRelation<AF> abc{
      "abc-d", 4, {{af.one(), {0, 1, 2}}, {af.mone(), {3}}}};
  cs.batch("abc", std::vector<Ref<AF, Subfield<>, Committed>>{T}, abc,
          compiler::AffineOperandMap<AF>::columns(af, "columns", 4, n), 4);
  compiler::FieldRelation<AF> sq{
      "u0^2-u1", 2, {{af.one(), {0, 0}}, {af.mone(), {1}}}};
  compiler::FieldRelation<AF> prod{
      "v0v1-v2", 3, {{af.one(), {0, 1}}, {af.mone(), {2}}}};
  A.batch(
      "merged", std::vector<Ref<AF, Subfield<>, Committed>>{U, V},
      std::vector<compiler::FieldBatchPart<AF>>{
          {sq, compiler::AffineOperandMap<AF>::columns(af, "columns", 2, m)},
          {prod, compiler::AffineOperandMap<AF>::columns(af, "columns", 3, m)}},
      2);
  // A circuit on the first instance (each domain has a GKR kernel).
  assert_equal(T[0] * T[n] * T[2 * n], T[3 * n], "first instance")
      .pin(Placement::kCircuit);
  auto c = compile(cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("field skip: abc-d, degree 3 in 4 operands, 100 instances, "
                   "width 4, skip domain 10 consecutive integers"),
            std::string::npos)
      << r;
  EXPECT_NE(r.find("skip domain of 10 points in GF(p^1)"), std::string::npos)
      << r;
  EXPECT_NE(r.find("field skip: u0^2-u1 + gamma v0v1-v2"), std::string::npos)
      << r;
  std::mt19937_64 g(7);
  auto rnd = [&]() { return af.of_scalar(g() >> 4); };
  Vec t(4 * n), u(2 * m), v(3 * m);
  for (size_t i = 0; i < n; ++i) {
    t[i] = rnd();
    t[n + i] = rnd();
    t[2 * n + i] = rnd();
    t[3 * n + i] = af.mulf(af.mulf(t[i], t[n + i]), t[2 * n + i]);
  }
  for (size_t i = 0; i < m; ++i) {
    u[i] = rnd();
    u[m + i] = af.mulf(u[i], u[i]);
    v[i] = rnd();
    v[m + i] = rnd();
    v[2 * m + i] = af.mulf(v[i], v[m + i]);
  }
  Assignment w;
  w.set(T, t).set(U, u).set(V, v);
  auto prep = c->prepare(Assignment{});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  // A d off abc - d, a u1 off u0^2 - u1, a v2 off v0 v1 - v2.
  for (int which = 0; which < 3; ++which) {
    Assignment bad;
    Vec t2 = t, u2 = u, v2 = v;
    if (which == 0) af.add(t2[3 * n + 41], af.one());
    if (which == 1) af.add(u2[m + 5], af.one());
    if (which == 2) af.add(v2[2 * m + 36], af.one());
    bad.set(T, t2).set(U, u2).set(V, v2);
    ProveOptions opt;
    opt.require_satisfied = false;
    EXPECT_FALSE(prep.verify(prep.prove(bad, rng, opt))) << which;
  }
}

// The masked field skip's algebra (field_skip.h), with zero pads: the
// terminal check row's right-hand side is 0 and the terminal values are
// the instance-weighted operands, in odd characteristic and in
// characteristic 2.
template <class G>
void field_skip_algebra(const G &g, unsigned width, size_t instances,
                        bool masked) {
  using E = typename G::Elt;
  compiler::FieldRelation<G> rel{
      "abc-d", 4, {{g.one(), {0, 1, 2}}, {g.mone(), {3}}}};
  compiler::MaskedFieldSkip<G> sk(g, rel, instances, width);
  std::mt19937_64 rng(3);
  std::vector<std::vector<E>> ops(instances);
  for (auto &o : ops) {
    for (int j = 0; j < 3; ++j) o.push_back(g.of_scalar(rng() & 0xffff));
    o.push_back(g.mulf(g.mulf(o[0], o[1]), o[2]));
  }
  std::vector<E> pads(sk.layout.count, g.zero());
  SecureRandomEngine prng;
  if (masked) sk.fill_pads(pads.data(), prng);
  static const uint8_t kLabel[] = "field-skip-algebra";
  BasicProofSeed<SHA384> seed;
  std::memset(seed.bytes, 0, sizeof(seed.bytes));
  BasicTranscript<SHA384> tp(kLabel, sizeof(kLabel) - 1, seed);
  auto tc = tp.clone();
  const auto proof = sk.prove(ops, tc, pads.data());
  auto ctx = sk.rows_of(proof, tp, 0);
  ASSERT_EQ(ctx.b.size(), 1u);
  E lhs = g.zero();
  for (const auto &t : ctx.a) g.add(lhs, g.mulf(t.k, pads[t.w]));
  EXPECT_EQ(lhs, ctx.b[0]);
  const auto w = sk.instance_weights(ctx);
  for (unsigned j = 0; j < 4; ++j) {
    E v = g.zero();
    for (size_t t = 0; t < instances; ++t) g.add(v, g.mulf(w[t], ops[t][j]));
    EXPECT_EQ(v, g.subf(ctx.terminal[j], pads[sk.layout.terminal + j])) << j;
  }
}
TEST(GordieHowe, FieldSkipAlgebra) {
  for (bool masked : {false, true}) {
    field_skip_algebra(env().af, 4, 37, masked);
    field_skip_algebra(env().mf, 8, 37, masked);
  }
}

// The same with a repeated operand (u0^2) and a coefficient outside the
// prime field, as a merged zerocheck has.
TEST(GordieHowe, FieldSkipAlgebraSquare) {
  const AF &g = env().af;
  using E = AF::Elt;
  E gx = g.zero();
  gx.e[1] = g.base_field().one();
  compiler::FieldRelation<AF> rel{"sq", 5, {{g.one(), {0, 0}}, {g.mone(), {1}},
                                  {gx, {2, 3}}, {g.negf(gx), {4}}}};
  // u0^2 - u1 + X (v0 v1 - v2).
  compiler::MaskedFieldSkip<AF> sk(g, rel, 37, 2);
  std::mt19937_64 rng(3);
  std::vector<std::vector<E>> ops(37);
  for (auto &o : ops) {
    o.push_back(g.of_scalar(rng() & 0xffff));
    o.push_back(g.mulf(o[0], o[0]));
    o.push_back(g.of_scalar(rng() & 0xffff));
    o.push_back(g.of_scalar(rng() & 0xffff));
    o.push_back(g.mulf(o[2], o[3]));
  }
  std::vector<E> pads(sk.layout.count, g.zero());
  SecureRandomEngine prng;
  sk.fill_pads(pads.data(), prng);
  static const uint8_t kLabel[] = "field-skip-algebra";
  BasicProofSeed<SHA384> seed;
  std::memset(seed.bytes, 0, sizeof(seed.bytes));
  BasicTranscript<SHA384> tp(kLabel, sizeof(kLabel) - 1, seed);
  auto tc = tp.clone();
  const auto proof = sk.prove(ops, tc, pads.data());
  auto ctx = sk.rows_of(proof, tp, 0);
  E lhs = g.zero();
  for (const auto &t : ctx.a) g.add(lhs, g.mulf(t.k, pads[t.w]));
  EXPECT_EQ(lhs, ctx.b[0]);
}

// A merged field batch's rows (BatchKernel::reduce) hold on the prover's
// words and pads.
TEST(GordieHowe, FieldBatchRowsHold) {
  const AF &f = env().af;
  using E = AF::Elt;
  constexpr size_t m = 37;
  compiler::FieldRelation<AF> sq{
      "u0^2-u1", 2, {{f.one(), {0, 0}}, {f.mone(), {1}}}};
  compiler::FieldRelation<AF> prod{
      "v0v1-v2", 3, {{f.one(), {0, 1}}, {f.mone(), {2}}}};
  for (size_t parts : {1, 2}) {
    std::vector<compiler::FieldBatchPart<AF>> ps = {
        {sq, compiler::AffineOperandMap<AF>::columns(f, "columns", 2, m)}};
    if (parts == 2)
      ps.push_back(
          {prod, compiler::AffineOperandMap<AF>::columns(f, "columns", 3, m)});
    const auto pkb = compiler::make_field_batch<SHA384>(f, ps, 2, 1);
    const auto &kb = *pkb;
    std::mt19937_64 g(5);
    std::vector<E> words;
    for (size_t i = 0; i < m; ++i) words.push_back(f.of_scalar(g() & 0xfff));
    for (size_t i = 0; i < m; ++i) words.push_back(f.mulf(words[i], words[i]));
    if (parts == 2) {
      for (size_t i = 0; i < 2 * m; ++i) words.push_back(f.of_scalar(g() & 0xfff));
      for (size_t i = 0; i < m; ++i)
        words.push_back(f.mulf(words[2 * m + i], words[3 * m + i]));
    }
    std::vector<E> pads(kb.pads());
    SecureRandomEngine rng;
    kb.fill_pads(pads.data(), rng);
    std::vector<E> w = words;
    w.insert(w.end(), pads.begin(), pads.end());
    static const uint8_t kLabel[] = "field-batch-rows";
    BasicProofSeed<SHA384> seed;
    std::memset(seed.bytes, 0, sizeof(seed.bytes));
    BasicTranscript<SHA384> tp(kLabel, sizeof(kLabel) - 1, seed);
    std::vector<E> msgs;
    const auto rows =
        kb.reduce(tp, msgs, words.size(), &words, pads.data(), {});
    std::vector<E> lhs(rows.b.size(), f.zero());
    for (const auto &t : rows.a) f.add(lhs[t.c], f.mulf(t.k, w[t.w]));
    for (size_t y = 0; y < words.size(); ++y)
      f.add(lhs[rows.form_row], f.mulf(rows.forms->a[y], words[y]));
    for (size_t r = 0; r < rows.b.size(); ++r)
      EXPECT_EQ(lhs[r], rows.b[r]) << parts << " row " << r;
  }
}

// The bit stage's measurement by bit planes (compiler/bit_planes.h) equals
// the products sum_y a[y] w[y] on GF(2^16) words, for random, zero and
// all-ones words, at word counts around the kernel's blocks and tiles.
template <class F>
void bit_plane_dots(const F &f) {
  using Elt = typename F::Elt;
  const compiler::PackingStage<F> st(f, 1, 16);
  const compiler::BitPlaneDots<F> planes(f, st.beta);
  if (!planes.has_kernel()) GTEST_SKIP() << "no GFNI kernel on this target";
  const auto &sub = SubfieldInfo<F>::get(f, 16);
  std::mt19937_64 rng(11);
  auto elt = [&] {
    std::array<uint64_t, F::kBytes / 8> raw;
    for (auto &x : raw) x = rng();
    return f.of_scalar_field(raw);
  };
  for (int pattern = 0; pattern < 3; ++pattern)
    for (size_t n : {1, 7, 8, 9, 63, 64, 65, 255, 256, 257, 1000, 4099}) {
      std::vector<Elt> vals(n + 3, f.zero());
      std::vector<size_t> at(n);
      std::vector<Elt> a(n);
      Elt want = f.zero();
      for (size_t y = 0; y < n; ++y) {
        // Positions in reverse, skipping the first three values.
        at[y] = n + 2 - y;
        const uint64_t u =
            pattern == 0 ? rng() & 0xffff : (pattern == 1 ? 0 : 0xffff);
        vals[at[y]] = sub.word(f, u);
        a[y] = elt();
        f.add(want, f.mulf(a[y], vals[at[y]]));
      }
      std::vector<uint8_t> piv(2 * n);
      planes.pivots(at, vals, 0, n, piv.data());
      EXPECT_EQ(planes.dot(f, a.data(), piv.data(), n), want)
          << "pattern " << pattern << ", " << n << " words";
      // The sums over ranges of the words add up to the sums over all.
      std::array<Elt, compiler::BitPlaneDots<F>::kBits> all, part, sum;
      planes.sums(f, a.data(), piv.data(), n, all.data());
      sum.fill(f.zero());
      for (size_t lo = 0; lo < n; lo += 97) {
        planes.sums(f, a.data(), piv.data(), n, lo, std::min(n, lo + 97),
                    part.data());
        for (size_t i = 0; i < sum.size(); ++i) f.add(sum[i], part[i]);
      }
      EXPECT_EQ(sum, all) << "pattern " << pattern << ", " << n << " words";
    }
}
TEST(GordieHowe, BitPlaneDots128) { bit_plane_dots(GF2_128<>()); }
TEST(GordieHowe, BitPlaneDots256) { bit_plane_dots(GF2_256<>()); }

// A root stage's forms and its Ligero coefficients without forms
// (compiler/stage.h): add_forms against the definition
// a_k[g] = phi^-k(sum_j phi^k(beta*_j) c_{g,j}) by phi_inv, and
// add_coefficients against sum_k w_k a_k[g], for random, partly zero and
// zero coefficients, group counts around the linear maps' blocks of eight,
// and a short last group. On a target without GFNI the maps run on their
// byte tables.
template <class F>
void root_coefficients(const F &f, size_t base) {
  using Elt = typename F::Elt;
  const compiler::PackingStage<F> st(f, base, field_degree<F>());
  ASSERT_TRUE(st.root);
  const size_t d = st.d;
  std::mt19937_64 rng(17 + base);
  auto elt = [&] {
    std::array<uint64_t, F::kBytes / 8> raw;
    for (auto &x : raw) x = rng();
    return f.of_scalar_field(raw);
  };
  for (int pattern = 0; pattern < 3; ++pattern)
    for (size_t ng : {1, 7, 8, 9, 64, 65, 1000})
      for (bool short_last : {false, true}) {
        const size_t ncoord = ng * d - (short_last ? d / 2 : 0);
        std::vector<Elt> c(ncoord, f.zero());
        for (size_t i = 0; i < ncoord; ++i) {
          // Pattern 1 zeros every third group; pattern 2 zeros all.
          const bool zero = pattern == 2 || (pattern == 1 && (i / d) % 3 == 0);
          if (!zero) c[i] = elt();
        }
        std::vector<Elt> w(d);
        for (auto &x : w) x = elt();
        std::vector<Elt> a;
        st.add_forms(f, c.data(), ncoord, ng, a);
        ASSERT_EQ(a.size(), d * ng);
        std::vector<Elt> want(ng, f.zero());
        for (size_t g = 0; g < ng; ++g)
          for (size_t k = 0; k < d; ++k) {
            Elt sum = f.zero();
            for (size_t j = 0; j < d && g * d + j < ncoord; ++j)
              f.add(sum, f.mulf(st.twisted_dual[k * d + j], c[g * d + j]));
            const Elt ak = st.phi_inv(f, sum, k);
            EXPECT_EQ(a[k * ng + g], ak)
                << "form " << k << ", group " << g << " of " << ng;
            f.add(want[g], f.mulf(w[k], ak));
          }
        // add_coefficients adds: start from a random offset.
        std::vector<Elt> v(ng), offset(ng);
        for (size_t g = 0; g < ng; ++g) v[g] = offset[g] = elt();
        st.add_coefficients(f, w.data(), c.data(), ncoord, ng, v.data());
        for (size_t g = 0; g < ng; ++g)
          EXPECT_EQ(f.subf(v[g], offset[g]), want[g])
              << "pattern " << pattern << ", group " << g << " of " << ng
              << (short_last ? ", short last group" : "");
      }
}
TEST(GordieHowe, RootCoefficients128) {
  root_coefficients(GF2_128<>(), 16);
  root_coefficients(GF2_128<>(), 32);
}
TEST(GordieHowe, RootCoefficients256) {
  root_coefficients(GF2_256<>(), 16);
  root_coefficients(GF2_256<>(), 64);
}

// The bit phase's kernels (compiler/bit_planes.h) against their
// definitions: BitPlaneSums' S_b = sum_r e_r t_{r,b} at 8, 16 and 64-bit
// words, and LinearMap's x -> c Frob^-k(x) on random elements, both at
// counts around the kernels' blocks and tiles.
template <class F>
void bit_phase_kernels(const F &f) {
  using Elt = typename F::Elt;
  std::mt19937_64 rng(13);
  auto elt = [&] {
    std::array<uint64_t, F::kBytes / 8> raw;
    for (auto &x : raw) x = rng();
    return f.of_scalar_field(raw);
  };
  for (unsigned bits : {8u, 16u, 64u})
    for (size_t n : {0, 1, 7, 8, 9, 255, 256, 257, 1000}) {
      std::vector<Elt> e(n);
      std::vector<uint64_t> t(n);
      for (size_t r = 0; r < n; ++r) {
        e[r] = elt();
        t[r] = bits == 64 ? rng() : rng() & ((uint64_t(1) << bits) - 1);
      }
      compiler::BitPlaneSums<F> acc(f, bits);
      // Two calls, split unevenly.
      acc.add(e.data(), t.data(), n / 3);
      acc.add(e.data() + n / 3, t.data() + n / 3, n - n / 3);
      for (unsigned b = 0; b < bits; ++b) {
        Elt want = f.zero();
        for (size_t r = 0; r < n; ++r)
          if ((t[r] >> b) & 1) f.add(want, e[r]);
        EXPECT_EQ(acc.get(b), want) << bits << " bits, " << n << " rows, bit " << b;
      }
    }
  const size_t nb = field_degree<F>();
  for (size_t k : {0, 1, 5, 15}) {
    const Elt c = elt();
    const size_t ex = (nb - k) % nb;
    const compiler::LinearMap<F> m(
        f, [&](const Elt &x) { return f.mulf(c, frobenius_power(f, x, ex)); });
    for (size_t n : {1, 7, 8, 9, 100}) {
      std::vector<Elt> x(n), y(n);
      for (auto &v : x) v = elt();
      m.apply(x.data(), y.data(), n);
      for (size_t i = 0; i < n; ++i)
        EXPECT_EQ(y[i], f.mulf(c, frobenius_power(f, x[i], ex)))
            << "k " << k << ", " << n << " elements, element " << i;
    }
  }
}
TEST(GordieHowe, BitPhaseKernels128) { bit_phase_kernels(GF2_128<>()); }
TEST(GordieHowe, BitPhaseKernels256) { bit_phase_kernels(GF2_256<>()); }

}  // namespace
}  // namespace proofs::gordiehowe
