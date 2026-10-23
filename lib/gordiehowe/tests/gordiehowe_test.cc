// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: the operators, phase inference, and an end-to-end
// system over one domain (Goldilocks quartic extension, source subfield
// Goldilocks) that proves and verifies. The binary also holds
// gordiehowe_structure_test.cc, gordiehowe_packing_test.cc and
// gordiehowe_expr_test.cc.

#include "gordiehowe/tests/gordiehowe_test.h"

namespace proofs::gordiehowe {
namespace {

// ----------------------------------------------------------- operators --

TEST(GordieHowe, NegacyclicTransposeIsAdjoint) {
  const AF &af = env().af;
  Vec h(kN), a(kN), b(kN);
  for (size_t i = 0; i < kN; ++i) {
    h[i] = af.of_scalar(3 * i + 1);
    a[i] = af.of_scalar(5 * i + 2);
    b[i] = af.of_scalar(7 * i + 9);
  }
  ops::NegacyclicConvOperator<AF> op(af, h);
  Vec ma(kN), mtb(kN);
  op.apply(a.data(), ma.data());
  op.transpose_apply(b.data(), mtb.data());
  AElt l = af.zero(), r = af.zero();
  for (size_t i = 0; i < kN; ++i) {
    af.add(l, af.mulf(b[i], ma[i]));
    af.add(r, af.mulf(mtb[i], a[i]));
  }
  EXPECT_EQ(l, r);
  // X * X^(n-1) = X^n = -1.
  Vec xs(kN, af.zero()), xn(kN, af.zero()), out(kN);
  xs[1] = af.one();
  xn[kN - 1] = af.one();
  ops::NegacyclicConvOperator<AF> shift(af, xs);
  shift.apply(xn.data(), out.data());
  EXPECT_EQ(out[0], af.mone());
}

TEST(GordieHowe, MACConvParityIsFieldMultiplication) {
  const Env &E = env();
  const AF &af = E.af;
  SecureRandomEngine rng;
  std::vector<MElt> r(kNch);
  for (auto &v : r) v = rng.elt(E.mf);
  Vec X(kNch * MF::kBits);
  std::vector<MElt> chunk(kNch, E.mf.zero());
  for (size_t c = 0; c < kNch; ++c) {
    MElt xi = E.mf.one();
    for (size_t i = 0; i < MF::kBits; ++i) {
      const bool b = ((c * 131 + i * 17) % 7) < 3;
      X[c * MF::kBits + i] = b ? af.one() : af.zero();
      if (b) E.mf.add(chunk[c], xi);
      xi = E.mf.mulf(xi, E.mf.of_scalar_field(0b10));
    }
  }
  MElt want = E.mf.zero();
  for (size_t c = 0; c < kNch; ++c) E.mf.add(want, E.mf.mulf(chunk[c], r[c]));
  ops::MACConvOperator<AF, MF> op(af, E.mf, r);
  Vec acc(MF::kBits);
  op.apply(X.data(), acc.data());
  for (size_t b = 0; b < MF::kBits; ++b) {
    uint8_t bytes[AF::kSubFieldBytes];
    af.to_bytes_subfield(bytes, acc[b]);
    EXPECT_EQ(bytes[0] & 1, want[b]) << b;
  }
  // Adjoint.
  Vec y(MF::kBits), mty(X.size());
  for (size_t b = 0; b < y.size(); ++b) y[b] = af.of_scalar(b * b + 1);
  op.transpose_apply(y.data(), mty.data());
  AElt l = af.zero(), rr = af.zero();
  for (size_t b = 0; b < y.size(); ++b) af.add(l, af.mulf(y[b], acc[b]));
  for (size_t j = 0; j < X.size(); ++j) af.add(rr, af.mulf(mty[j], X[j]));
  EXPECT_EQ(l, rr);
}

// The NTT operators agree with the direct references at the tested sizes, and
// apply and transpose_apply are adjoint: <A x, y> = <x, A^T y>.
template <class F>
void expect_matches_reference(const F &f, const LinearOperator<F> &op,
                              const LinearOperator<F> &ref) {
  ASSERT_EQ(op.rows(), ref.rows());
  ASSERT_EQ(op.cols(), ref.cols());
  SecureRandomEngine rng;
  using E = typename F::Elt;
  std::vector<E> x(op.cols()), y(op.rows());
  for (auto &v : x) v = rng.elt(f);
  for (auto &v : y) v = rng.elt(f);
  std::vector<E> ax(op.rows()), rax(op.rows()), aty(op.cols()),
      raty(op.cols());
  op.apply(x.data(), ax.data());
  ref.apply(x.data(), rax.data());
  op.transpose_apply(y.data(), aty.data());
  ref.transpose_apply(y.data(), raty.data());
  EXPECT_TRUE(ax == rax);
  EXPECT_TRUE(aty == raty);
  E l = f.zero(), r = f.zero();
  for (size_t i = 0; i < y.size(); ++i) f.add(l, f.mulf(ax[i], y[i]));
  for (size_t j = 0; j < x.size(); ++j) f.add(r, f.mulf(x[j], aty[j]));
  EXPECT_EQ(l, r);
}

template <class F>
void negacyclic_matches_reference(size_t n) {
  F f;
  SecureRandomEngine rng;
  std::vector<typename F::Elt> h(n);
  for (auto &v : h) v = rng.elt(f);
  ops::NegacyclicConvOperator<F> op(f, h);
  ops::NegacyclicConvReference<F> ref(f, h);
  expect_matches_reference(f, op, ref);
}

TEST(GordieHowe, NegacyclicNttMatchesReference) {
  negacyclic_matches_reference<Fp64G2>(512);
  negacyclic_matches_reference<Fp64G4>(512);
  negacyclic_matches_reference<Fp64G4>(kN);
}

template <class MF>
void mac_matches_reference(size_t nch) {
  const AF &af = env().af;
  MF mf;
  SecureRandomEngine rng;
  std::vector<typename MF::Elt> r(nch);
  for (auto &v : r) v = rng.elt(mf);
  // Edge cases: chunk powers 0, 1, and the element with every bit set.
  if (nch >= 3) {
    r[0] = mf.zero();
    r[1] = mf.one();
    r[2] = mf.zero();
    auto xb = mf.one();
    for (size_t b = 0; b < MF::kBits; ++b) {
      mf.add(r[2], xb);
      xb = mf.mulf(xb, mf.of_scalar_field(0b10));
    }
  }
  ops::MACConvOperator<AF, MF> op(af, mf, r);
  ops::MACConvReference<AF, MF> ref(af, mf, r);
  expect_matches_reference(af, op, ref);
}

TEST(GordieHowe, MACConvNttMatchesReference) {
  mac_matches_reference<GF2_128<>>(4);
  mac_matches_reference<GF2_256<>>(4);
  mac_matches_reference<GF2_256<>>(32);
}

// The bits of x^k in M, by M's own multiplication.
template <class MF>
std::vector<uint8_t> mac_power_bits(const MF &mf, size_t k) {
  auto v = mf.one();
  for (size_t i = 0; i < k; ++i) v = mf.mulf(v, mf.of_scalar_field(0b10));
  std::vector<uint8_t> out(MF::kBits);
  for (size_t b = 0; b < MF::kBits; ++b) out[b] = uint8_t(v[b]);
  return out;
}

// MACConv is Conv(r) of def:macconv: the integer product sum_c X_c * R_c,
// each monomial x^k with k >= w then replaced, once, by the bits of x^k in
// M, here from M's multiplication and a schoolbook product.
template <class F, class MF>
void mac_matches_definition(size_t nch) {
  constexpr size_t W = MF::kBits;
  F f;
  MF mf;
  SecureRandomEngine rng;
  std::vector<typename MF::Elt> r(nch);
  for (auto &v : r) v = rng.elt(mf);
  std::vector<typename F::Elt> x(nch * W);
  for (auto &v : x) v = rng.elt(f);
  std::vector<typename F::Elt> prod(2 * W - 1, f.zero());
  for (size_t c = 0; c < nch; ++c)
    for (size_t i = 0; i < W; ++i)
      for (size_t j = 0; j < W; ++j)
        if (r[c][j]) f.add(prod[i + j], x[c * W + i]);
  std::vector<typename F::Elt> want(prod.begin(), prod.begin() + W);
  for (size_t k = W; k <= 2 * W - 2; ++k) {
    const auto bits = mac_power_bits(mf, k);
    for (size_t b = 0; b < W; ++b)
      if (bits[b]) f.add(want[b], prod[k]);
  }
  ops::MACConvOperator<F, MF> op(f, mf, r);
  std::vector<typename F::Elt> acc(W);
  op.apply(x.data(), acc.data());
  EXPECT_TRUE(acc == want);
  ops::MACConvReference<F, MF> ref(f, mf, r);
  ref.apply(x.data(), acc.data());
  EXPECT_TRUE(acc == want);
}

TEST(GordieHowe, MACConvIsTheDefinition) {
  mac_matches_definition<Fp64G2, GF2_128<>>(4);
  mac_matches_definition<Fp64G4, GF2_256<>>(4);
  // convMax from the field's taps, and the accumulator bound.
  EXPECT_EQ(ops::mac_conv_max(GF2_128<>()), 504u);
  EXPECT_EQ(ops::mac_conv_max(GF2_256<>()), 1017u);
  EXPECT_EQ(ops::mac_acc_max(GF2_256<>(), 32), 32u * 1017 + 1);
}

// Conv(r) entry for entry against an exact reference of def:macconv
// (an independent Python implementation of the paper's matrix) at three chunk powers:
// all bits set, and two of xorshift64 bits (13, 7, 17) from the seeds
// 0x9E3779B97F4A7C15 + 1 and + 2. For each: the fingerprint sum_{b,j}
// M[b][j] (b w + j + 1), the entry sum, the largest row sum, column sum and
// entry. Every entry of Conv(r) is at most w.
struct ConvExpect {
  uint64_t fingerprint, total, row, column, entry;
};
template <class MF>
void conv_matches_reference(const ConvExpect (&want)[3]) {
  constexpr size_t W = MF::kBits;
  const MF mf;
  const auto red = ops::mac_reduction(W, ops::mac_taps(mf));
  for (int pat = 0; pat < 3; ++pat) {
    uint64_t s = 0x9E3779B97F4A7C15ull + uint64_t(pat);
    std::vector<uint8_t> bytes(MF::kBytes, 0);
    for (size_t i = 0; i < W; ++i) {
      uint64_t bit = 1;
      if (pat != 0) {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        bit = s & 1;
      }
      bytes[i / 8] |= uint8_t(bit << (i % 8));
    }
    const auto r = mf.of_bytes_field(bytes.data()).value();
    const auto col = ops::mac_columns<MF>(r, red);
    ConvExpect got{0, 0, 0, 0, 0};
    std::vector<uint64_t> rows(W, 0);
    for (size_t j = 0; j < W; ++j) {
      uint64_t column = 0;
      for (size_t b = 0; b < W; ++b) {
        const uint64_t m = col[j][b];
        got.fingerprint += m * (b * W + j + 1);
        got.total += m;
        got.entry = std::max(got.entry, m);
        rows[b] += m;
        column += m;
      }
      got.column = std::max(got.column, column);
    }
    got.row = *std::max_element(rows.begin(), rows.end());
    EXPECT_EQ(got.fingerprint, want[pat].fingerprint) << W << " " << pat;
    EXPECT_EQ(got.total, want[pat].total) << W << " " << pat;
    EXPECT_EQ(got.row, want[pat].row) << W << " " << pat;
    EXPECT_EQ(got.column, want[pat].column) << W << " " << pat;
    EXPECT_EQ(got.entry, want[pat].entry) << W << " " << pat;
    EXPECT_LE(got.entry, uint64_t(W));
  }
}
TEST(GordieHowe, MACConvMatchesExactReference) {
  conv_matches_reference<GF2_128<>>({{277502615u, 40832, 504, 528, 7},
                                     {162021775u, 23614, 291, 308, 6},
                                     {144884428u, 21351, 266, 275, 4}});
  conv_matches_reference<GF2_256<>>({{4425336226u, 163580, 1017, 1043, 7},
                                     {2232104450u, 82612, 525, 539, 5},
                                     {2327396914u, 85929, 534, 542, 5}});
}

// The prover's popcount accumulators equal MACConv on 0/1 inputs, with a
// partial last chunk.
template <class F, class MF>
void popcount_matches_macconv(size_t nch, size_t len) {
  constexpr size_t W = MF::kBits;
  F f;
  MF mf;
  SecureRandomEngine rng;
  std::vector<typename MF::Elt> r(nch);
  for (auto &v : r) v = rng.elt(mf);
  std::vector<uint8_t> bits(nch * W, 0);
  std::vector<typename F::Elt> x(nch * W, f.zero());
  std::mt19937 g(5);
  for (size_t i = 0; i < len; ++i) {
    bits[i] = g() & 1;
    x[i] = bits[i] ? f.one() : f.zero();
  }
  ops::MACConvOperator<F, MF> op(f, mf, r);
  std::vector<typename F::Elt> acc(W);
  op.apply(x.data(), acc.data());
  const auto ints =
      ops::mac_integer_accumulators<MF>(bits, r, ops::mac_taps(mf));
  ASSERT_EQ(ints.size(), W);
  for (size_t b = 0; b < W; ++b)
    EXPECT_EQ(f.of_scalar(ints[b]), acc[b]) << b;
}
TEST(GordieHowe, MACPopcountAccumulatorsMatchMACConv) {
  popcount_matches_macconv<Fp64G2, GF2_128<>>(64, 8192);
  popcount_matches_macconv<Fp64G4, GF2_256<>>(32, 8192);
  popcount_matches_macconv<Fp64G4, GF2_256<>>(3, 600);
}

// The MAC accumulators are checked below the odd domain's characteristic
// before conversion: in F_q (q = 12289, Falcon's native field) of_scalar
// would reduce a sum above q. 32 chunks of GF(2^256) reach acc_max = 32545,
// above q; all-ones inputs at the all-ones chunk power give 32 * 1017.
TEST(GordieHowe, MACAccumulatorsBelowTheCharacteristic) {
  using MF2 = GF2_256<>;
  using FQ = Fp14_9;
  const MF2 mf;
  const Fp14 base(12289);
  const FQ fq(base, FQ::beta_);
  const Bound q = field_characteristic(fq);
  ASSERT_EQ(q, Bound(12289));
  constexpr size_t W = MF2::kBits, nch = 32;
  auto ones = mf.zero(), xb = mf.one();
  for (size_t b = 0; b < W; ++b) {
    mf.add(ones, xb);
    xb = mf.mulf(xb, mf.of_scalar_field(0b10));
  }
  const std::vector<MF2::Elt> r(nch, ones);
  const std::vector<uint8_t> x(nch * W, 1);
  const auto sums = ops::mac_integer_accumulators<MF2>(x, r, ops::mac_taps(mf));
  ASSERT_GE(Bound(*std::max_element(sums.begin(), sums.end())), q);
  EXPECT_THROW(ops::mac_integer_accumulators<MF2>(x, r, ops::mac_taps(mf), q),
               std::runtime_error);
  const std::vector<FQ::Elt> blind(W, fq.zero());
  try {
    compiler::mac_accumulator_elements(fq, q, sums, blind);
    ADD_FAILURE() << "an accumulator above q was reduced";
  } catch (const std::runtime_error &e) {
    EXPECT_NE(std::string(e.what()).find("is not below the characteristic "
                                         "12289 of the odd domain"),
              std::string::npos)
        << e.what();
  }
  // Below q, and at q - 1 with the blind bit: accepted; at q: rejected.
  std::vector<uint64_t> small(W, 5);
  small[0] = 12288;
  std::vector<FQ::Elt> bl(W, fq.zero());
  const auto ok = compiler::mac_accumulator_elements(fq, q, small, bl);
  EXPECT_EQ(ok[0], fq.of_scalar(12288));
  EXPECT_EQ(ok[1], fq.of_scalar(5));
  bl[0] = fq.one();
  EXPECT_THROW(compiler::mac_accumulator_elements(fq, q, small, bl),
               std::runtime_error);
  small[0] = 12287;
  EXPECT_EQ(compiler::mac_accumulator_elements(fq, q, small, bl)[0],
            fq.of_scalar(12288));
}

// --------------------------------------------------------------- phases --

TEST(GordieHowe, PhaseInference) {
  TestSystem t;
  auto c = compile(t.cs);
  std::printf("%s", c->report().c_str());
  EXPECT_EQ(c->phases(), 2u);
  for (Ref<AF> r : {Ref<AF>(t.h), Ref<AF>(t.x), t.bits, t.blind, t.y,
                    Ref<AF>(t.z), t.P, t.pcopy})
    EXPECT_EQ(c->phase(r), 0u);
  EXPECT_EQ(c->phase(t.gamma), 1u);
  EXPECT_EQ(c->phase(t.beta), 1u);
  EXPECT_EQ(c->phase(t.r), 1u);
  for (auto r : {t.u, t.T, t.v2, t.acc, t.lowbit, t.w}) EXPECT_EQ(c->phase(r), 1u);
  EXPECT_EQ(c->phase(t.delta), 2u);
  EXPECT_EQ(c->phase(t.e), 2u);
  EXPECT_FALSE(c->late(t.pcopy));
  EXPECT_FALSE(c->late(t.w));  // a derived view is not a message
  EXPECT_TRUE(c->late(t.u));
  EXPECT_TRUE(c->late(t.e));
  const std::vector<size_t> want{t.u.id, t.v2.id, t.acc.id, t.lowbit.id, t.e.id};
  EXPECT_EQ(c->messages(), want);
}

// ------------------------------------------------------------ end to end --

TEST(GordieHowe, ProveVerify) {
  TestSystem t;
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(), rng);
  std::printf("proof bytes: %zu\n", proof.size());
  EXPECT_TRUE(prep.verify(proof));
  const auto proof2 = prep.prove(t.witness(), rng);
  EXPECT_TRUE(prep.verify(proof2));
  EXPECT_NE(proof, proof2);

  // A changed seed, message, or statement is rejected.
  auto bad = proof;
  bad[0] ^= 1;
  EXPECT_FALSE(prep.verify(bad));
  for (auto r : {t.u, t.acc, t.e}) {
    const auto sp = c->message_span(r);
    bad = proof;
    bad[sp.offset + sp.length - 1] ^= 1;
    EXPECT_FALSE(prep.verify(bad));
  }
  TestStatement<Value> other = TestSystem::statement_value();
  for (auto &v : other.h) v = 1;
  EXPECT_FALSE(c->prepare(t.statement(other)).verify(proof));
}

// The same through the relation's struct interface: prove on a Statement
// and a Witness value, verify on the Statement; another statement is
// rejected.
TEST(GordieHowe, RelationProvesOnStructs) {
  TestSystem t;
  const TestStatement<Value> st = TestSystem::statement_value();
  const TestWitness<Value> w = TestSystem::witness_value();
  SecureRandomEngine rng;
  const auto proof = t.rel.prove(st, w, rng);
  EXPECT_TRUE(t.rel.verify(st, proof));
  TestStatement<Value> other = st;
  other.h[3] += 1;
  EXPECT_FALSE(t.rel.verify(other, proof));
}

// List-radius Ligero, with untested and with split masks: honest proofs
// verify, and a changed proof byte is rejected.
TEST(GordieHowe, ListRadiusProveVerify) {
  for (LigeroMasking m : {LigeroMasking::kUntested, LigeroMasking::kSplit}) {
    TestSystem t(/*list_radius=*/true, /*t=*/16, m);
    auto c = compile(t.cs);
    EXPECT_NE(c->report().find(m == LigeroMasking::kSplit
                                   ? " t=16 r=16 masking=split"
                                   : " t=16 r=16 masking=untested"),
              std::string::npos)
        << c->report();
    auto prep = c->prepare(t.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(t.witness(), rng);
    EXPECT_TRUE(prep.verify(proof));
    for (size_t at : {size_t(1), proof.size() / 2, proof.size() - 1}) {
      auto bad = proof;
      bad[at] ^= 1;
      EXPECT_FALSE(prep.verify(bad)) << at;
    }
  }
}

// The same system over the other protocol hash of the PQ profiles.
TEST(GordieHowe, ProveVerifyEitherHash) {
  auto run = [](auto &t) {
    auto c = compile(t.cs);
    auto prep = c->prepare(t.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(t.witness(), rng);
    EXPECT_TRUE(prep.verify(proof));
    auto bad = proof;
    bad[bad.size() / 2] ^= 1;
    EXPECT_FALSE(prep.verify(bad));
  };
  BasicTestSystem<SHA256> rom;
  run(rom);
  BasicTestSystem<SHA384> qrom;
  run(qrom);
}

// A message outside its codec's space is rejected: the late bit's message is
// a Goldilocks element (its pad is uniform over the prime field), and a
// non-canonical encoding (all ones, at least p) does not decode.
TEST(GordieHowe, CodecRejectsNonCanonicalMessage) {
  TestSystem t;
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(), rng);
  ASSERT_TRUE(prep.verify(proof));
  const auto sp = c->message_span(t.lowbit);
  EXPECT_EQ(sp.length, AF::kSubFieldBytes);
  auto bad = proof;
  for (size_t i = 0; i < sp.length; ++i) bad[sp.offset + i] = 0xff;
  EXPECT_FALSE(prep.verify(bad));
}

// A statement value its codec refuses (a coordinate outside the prime
// field, or at least 100) makes verify() return false, before any public
// computation reads it, and the prover refuses it. The codec is part of the
// digest.
TEST(GordieHowe, StatementCodecRejectsMalformedInput) {
  const AF &af = env().af;
  auto build = [&](Sys &cs, bool codec) {
    auto &A = cs.domain(env().profile(), "A");
    Ref<AF> k = codec ? A.pub(Field{}, "key", 2,
                                       computes("below", {100}),
                                       [&af](const Vec &v) {
                                         for (const auto &e : v)
                                           if (!af.in_subfield(e) ||
                                               nat_of(af, e) >= 100)
                                             return false;
                                         return true;
                                       })
                      : A.pub(Field{}, "key", 2);
    // A public computation that would throw on a malformed key.
    auto h = A.pub(Field{}, "h", 2, depends_on(k), computes("check"),
                              [&af](const Vec &v) {
                                for (const auto &e : v)
                                  if (nat_of(af, e) >= 100)
                                    throw std::invalid_argument("malformed");
                                return v;
                              });
    auto x = A.priv(Subfield{}, "x", 2);
    assert_equal(x, h, "x = h").pin(Placement::kCircuit);
    return std::make_pair(k, x);
  };
  Sys cs("gh-statement-codec");
  const auto [k, x] = build(cs, true);
  auto c = compile(cs);
  Assignment st, w;
  st.set(k, Vec{af.of_scalar(7), af.of_scalar(9)});
  w.set(x, Vec{af.of_scalar(7), af.of_scalar(9)});
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  const auto proof = prep.prove(w, rng);
  EXPECT_TRUE(prep.verify(proof));
  EXPECT_EQ(prep.rejected_statement(), "");
  uint8_t xb[AF::kBytes] = {};
  xb[8] = 1;  // the second coordinate over the prime field
  const AElt outside = af.of_bytes_field(xb).value();
  ASSERT_FALSE(af.in_subfield(outside));
  for (const auto &bad : {Vec{af.of_scalar(7), af.of_scalar(100)},
                          Vec{af.of_scalar(7), outside}}) {
    Assignment b;
    b.set(k, bad);
    auto pb = c->prepare(b);
    EXPECT_EQ(pb.rejected_statement(), "key");
    EXPECT_FALSE(pb.verify(proof));
    EXPECT_THROW(pb.prove(w, rng), std::runtime_error);
  }
  Sys s2("gh-statement-codec");
  build(s2, false);
  EXPECT_NE(compile(s2)->digest(), c->digest());
}

// Whether R has bounded(N): a public prime-field value.
template <class R, class = void>
struct CanBound : std::false_type {};
template <class R>
struct CanBound<R, std::void_t<decltype(std::declval<const R &>().bounded(
                       Bound(1)))>> : std::true_type {};
static_assert(CanBound<Ref<AF, Subfield<>, Public>>::value);
static_assert(CanBound<Ref<AF, Subfield<Fq>, Public>>::value);
static_assert(CanBound<Ref<Fp64G, Field, Public>>::value);
// Field of an extension, a Bit, a characteristic-2 field, a committed value.
static_assert(!CanBound<Ref<AF, Field, Public>>::value);
static_assert(!CanBound<Ref<AF, Bit, Public>>::value);
static_assert(!CanBound<Ref<MF, Field, Public>>::value);
static_assert(!CanBound<Ref<MF, Subfield<>, Public>>::value);
static_assert(!CanBound<Ref<AF, Subfield<>, Committed>>::value);

// v := stmt(N): a statement input bounded by 100 and a cached public
// computation of it bounded by 50. A statement with a coordinate outside
// either bound makes verify() return false and the prover refuse it; one
// at N - 1 proves. The bounds are part of the digest. A bound on a public
// computation that is not cached fails compilation, and a bound outside
// [1, p] or a second bound fails at once.
TEST(GordieHowe, StatementBound) {
  const AF &af = env().af;
  auto build = [&](Sys &cs, bool bounds) {
    auto &A = cs.domain(env().profile(), "A");
    auto k = A.pub(Subfield{}, "key", 2);
    auto h = A.pub(Subfield{}, "h", 2, depends_on(k), computes("copy"),
                   [](const Vec &v) { return v; })
                 .cache();
    if (bounds) {
      k.bounded(100);
      h.bounded(50);
    }
    auto x = A.priv(Subfield{}, "x", 2);
    assert_equal(x, h, "x = h").pin(Placement::kCircuit);
    return std::make_tuple(k, h, x);
  };
  Sys cs("gh-statement-bound");
  const auto [k, h, x] = build(cs, true);
  auto c = compile(cs);
  EXPECT_NE(c->report().find("bound=100"), std::string::npos);
  auto statement = [&](uint64_t a, uint64_t b) {
    Assignment st;
    st.set(k, Vec{af.of_scalar(a), af.of_scalar(b)});
    return st;
  };
  auto witness = [&](uint64_t a, uint64_t b) {
    Assignment w;
    w.set(x, Vec{af.of_scalar(a), af.of_scalar(b)});
    return w;
  };
  SecureRandomEngine rng;
  auto prep = c->prepare(statement(7, 49));
  EXPECT_EQ(prep.rejected_statement(), "");
  const auto proof = prep.prove(witness(7, 49), rng);
  EXPECT_TRUE(prep.verify(proof));
  // key at its bound (the cached copy then too), and the copy alone past
  // its own.
  for (const auto &[b, name] : {std::make_pair(uint64_t(100), "key"),
                                std::make_pair(uint64_t(50), "h")}) {
    auto pb = c->prepare(statement(7, b));
    EXPECT_EQ(pb.rejected_statement(), name);
    EXPECT_FALSE(pb.verify(proof));
    EXPECT_THROW(pb.prove(witness(7, b), rng), std::runtime_error);
  }
  // The setup's test hook: a verifier whose cached copy holds p - 1.
  const size_t hid = h.id;
  auto pt = c->prepare(statement(7, 49), [&](size_t id, SysValue &v) {
    if (id == hid) std::get<Vec>(v).at(1) = af.mone();
  });
  EXPECT_EQ(pt.rejected_statement(), "h");
  EXPECT_FALSE(pt.verify(proof));
  Sys s2("gh-statement-bound");
  build(s2, false);
  EXPECT_NE(compile(s2)->digest(), c->digest());

  // A bound on a public computation that is not cached.
  {
    Sys s3("gh-statement-bound-uncached");
    auto &A = s3.domain(env().profile(), "A");
    auto key = A.pub(Subfield{}, "key", 2);
    auto h = A.pub(Subfield{}, "h", 2, depends_on(key), computes("copy"),
                   [](const Vec &v) { return v; });
    h.bounded(50);
    auto y = A.priv(Subfield{}, "y", 2);
    assert_equal(y, h, "y = h").pin(Placement::kCircuit);
    EXPECT_THROW(compile(s3), CompileError);
  }
  // Bounds outside [1, p], and a second bound.
  {
    Sys s4("gh-statement-bound-n");
    auto &A = s4.domain(env().profile(), "A");
    auto key = A.pub(Subfield{}, "key", 2);
    EXPECT_THROW(key.bounded(0), CompileError);
    EXPECT_THROW(key.bounded(field_characteristic(af) + 1), CompileError);
    key.bounded(field_characteristic(af));
    EXPECT_THROW(key.bounded(10), CompileError);
  }
}

// A cached public computation that refuses its statement (StatementRefused,
// as ML-DSA's bounded ExpandA refuses a key): the statement is malformed,
// so verify() returns false and the prover refuses it; the refusal is not
// memoized, and an honest statement still proves afterwards.
TEST(GordieHowe, StatementRefusedByComputation) {
  const AF &af = env().af;
  Sys cs("gh-statement-refused");
  auto &A = cs.domain(env().profile(), "A");
  auto k = A.pub(Subfield{}, "key", 2);
  auto h = A.pub(Subfield{}, "h", 2, depends_on(k), computes("refuse"),
                 [&af](const Vec &v) {
                   for (const auto &e : v)
                     if (nat_of(af, e) >= 100)
                       throw StatementRefused("refused");
                   return v;
                 })
               .cache();
  auto x = A.priv(Subfield{}, "x", 2);
  assert_equal(x, h, "x = h").pin(Placement::kCircuit);
  auto c = compile(cs);
  auto statement = [&](uint64_t a, uint64_t b) {
    Assignment st;
    st.set(k, Vec{af.of_scalar(a), af.of_scalar(b)});
    return st;
  };
  auto witness = [&](uint64_t a, uint64_t b) {
    Assignment w;
    w.set(x, Vec{af.of_scalar(a), af.of_scalar(b)});
    return w;
  };
  SecureRandomEngine rng;
  auto prep = c->prepare(statement(7, 9));
  EXPECT_EQ(prep.rejected_statement(), "");
  const auto proof = prep.prove(witness(7, 9), rng);
  EXPECT_TRUE(prep.verify(proof));
  auto pb = c->prepare(statement(7, 100));
  EXPECT_EQ(pb.rejected_statement(), "h");
  EXPECT_EQ(pb.rejected_row(), SIZE_MAX);
  EXPECT_FALSE(pb.verify(proof));
  EXPECT_THROW(pb.prove(witness(7, 100), rng), std::runtime_error);
  // The same refused statement again: the refusal was not memoized.
  EXPECT_EQ(c->prepare(statement(7, 100)).rejected_statement(), "h");
  auto again = c->prepare(statement(7, 9));
  EXPECT_TRUE(again.verify(again.prove(witness(7, 9), rng)));
}

// A characteristic-2 domain in the core: a late Bit masked by a GF(2) pad
// (one byte in the proof), a late Field value, and a phase-0 Bit vector.
TEST(GordieHowe, CharacteristicTwoProveVerify) {
  using G = GF2_256<>;
  using GV = std::vector<G::Elt>;
  using RSG = LCH14ReedSolomonFactory<G>;
  static const G g;
  static const RSG rs(g);
  DomainProfile<G, RSG, SHA384> p;
  p.f = &g;
  p.rsf = &rs;
  p.field_name = "GF(2^256)";
  p.rate = 4;
  p.nreq = 64;
  using SysG = ConstraintSystem<SHA384, G>;
  SysG cs("gordiehowe-characteristic-2");
  auto &H = cs.domain(p, "H");
  auto x = H.priv(Field{}, "x", 2);
  auto b = H.priv(Bit{}, "b", 16);
  assert_equal(x[1], x[0] * x[0], "x1 = x0^2").pin(Placement::kCircuit);
  auto gamma = H.challenge("gamma", depends_on(x, b));
  const G *pg = &g;
  auto y = H.priv(Field{}, "y", 1, depends_on(x, gamma),
                    [pg](const GV &x, const GV &c) {
                      return GV{pg->mulf(x[0], c[0])};
                    });
  assert_equal(y[0], x[0] * gamma[0], "y = x0 gamma")
      .pin(Placement::kCircuit);
  auto c = H.priv(Bit{}, "c", 1, depends_on(b, gamma),
                    [](const GV &b, const GV &) { return GV{b[3]}; });
  assert_equal(c[0], b[3], "c = b3").pin(Placement::kCircuit);
  auto compiled = compile(cs);
  EXPECT_NE(compiled->report().find("pad(c) @H n=1 space=prime (auto)"),
            std::string::npos)
      << compiled->report();
  auto prep = compiled->prepare(SysG::Assignment{});
  GV xv{g.of_scalar(7), g.mulf(g.of_scalar(7), g.of_scalar(7))}, bv(16);
  for (size_t i = 0; i < 16; ++i) bv[i] = (i % 3 == 0) ? g.one() : g.zero();
  SysG::Assignment w;
  w.set(x, xv).set(b, bv);
  SecureRandomEngine rng;
  const auto proof = prep.prove(w, rng);
  EXPECT_TRUE(prep.verify(proof));
  const auto sp = compiled->message_span(c);
  EXPECT_EQ(sp.length, 1u);
  auto bad = proof;
  bad[sp.offset] = 2;  // not a bit: the GF(2) codec rejects it
  EXPECT_FALSE(prep.verify(bad));
  bad[sp.offset] = proof[sp.offset] ^ 1;  // the other bit: c != b3
  EXPECT_FALSE(prep.verify(bad));
}

// A prover whose generator lies is caught by the constraint kind that
// covers the value.
TEST(GordieHowe, CheatingGeneratorsRejected) {
  const AF &af = env().af;
  for (int which = 0; which < 3; ++which) {
    TestSystem t;
    auto c = compile(t.cs);
    auto prep = c->prepare(t.statement());
    ProveOptions opt;
    opt.require_satisfied = false;
    size_t target = 0;
    switch (which) {
      case 0: target = t.y.id; break;    // affine (negacyclic convolution)
      case 1: target = t.acc.id; break;  // affine (MACConv), late
      default: target = t.u.id; break;   // circuit, late
    }
    opt.tamper = [&](size_t id, SysValue &v) {
      if (id != target) return;
      auto &x = std::get<Vec>(v);
      af.add(x[0], af.one());
    };
    // The prover runs to the end (require_satisfied = false), and the
    // verifier rejects; a prover exception fails the test.
    SecureRandomEngine rng;
    EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt)))
        << "case " << which;
  }
}

// A wrong product in a quadratic triple: the existing Ligero prover checks
// its quadratic rows itself and aborts.
TEST(GordieHowe, CheatingQuadraticTripleAbortsProver) {
  const AF &af = env().af;
  TestSystem t;
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement());
  ProveOptions opt;
  const size_t target = t.z.id;
  opt.tamper = [&](size_t id, SysValue &v) {
    if (id == target) af.add(std::get<Vec>(v)[0], af.one());
  };
  EXPECT_DEATH(
      {
        SecureRandomEngine rng;
        prep.prove(t.witness(), rng, opt);
      },
      "invalid quadratic constraints");
}

}  // namespace
}  // namespace proofs::gordiehowe
