// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#include "zk/zk_packed.h"

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <random>
#include <utility>
#include <vector>

#include "arrays/dense.h"
#include "arrays/eqs.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/prover.h"
#include "util/readbuffer.h"
#include "zk/zk_common.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"
#include "gtest/gtest-death-test.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

using Field = GF2_128<>;
using Elt = Field::Elt;
constexpr size_t kPack = Field::kSubFieldBits;

TEST(ZkPacked, FrobeniusDirection) {
  const Field F;
  SecureRandomEngine rng;
  for (size_t trial = 0; trial < 8; ++trial) {
    Elt x = rng.elt(F);
    // frobenius(x, 1) is the square, not the square root.
    EXPECT_EQ(frobenius(x, 1, F), F.mulf(x, x));
    for (size_t k = 0; k < kPack; ++k) {
      Elt y = frobenius(x, k, F);
      EXPECT_EQ(inverse_frobenius(y, k, F), x);
      EXPECT_EQ(frobenius(inverse_frobenius(x, k, F), k, F), x);
    }
    // x^(2^128) = x in GF(2^128); x^(2^16) = x exactly on the subfield.
    EXPECT_EQ(frobenius(x, Field::kBits, F), x);
    Elt s = rng.subfield_elt(F);
    EXPECT_EQ(frobenius(s, kPack, F), s);
    EXPECT_NE(frobenius(x, kPack, F), x);  // x is outside E whp
  }
}

TEST(ZkPacked, DualBasis) {
  const Field F;
  const PackedBasis<Field> basis(F);
  for (size_t i = 0; i < kPack; ++i) {
    EXPECT_TRUE(F.in_subfield(basis.dual(i)));
    for (size_t j = 0; j < kPack; ++j) {
      Elt t = basis.trace(F.mulf(basis.dual(i), F.beta(j)));
      EXPECT_EQ(t, i == j ? F.one() : F.zero());
    }
    for (size_t k = 0; k < kPack; ++k) {
      EXPECT_EQ(basis.dual_pow(k, i), frobenius(basis.dual(i), k, F));
    }
  }
  // bit() recovers of_scalar()'s bits.
  std::mt19937_64 gen(1);
  for (size_t trial = 0; trial < 64; ++trial) {
    uint64_t u = gen() & 0xffff;
    Elt p = F.of_scalar(u);
    for (size_t i = 0; i < kPack; ++i) {
      EXPECT_EQ(basis.bit(p, i), ((u >> i) & 1) ? F.one() : F.zero());
    }
  }
}

// A circuit shell with only the fields PackedLayout reads.
Circuit<Field> shell(size_t ninputs, size_t npub, size_t boundary,
                     std::vector<std::pair<size_t, size_t>> runs) {
  Circuit<Field> c;
  c.ninputs = ninputs;
  c.npub_in = npub;
  c.subfield_boundary = boundary;
  c.packed_bits = std::move(runs);
  return c;
}

// SUM_{x packed} (eq(g0,x) + alpha eq(g1,x)) b_x  ==  SUM_k z_k^(2^k)
void check_identity(const Field& F, size_t ninputs, size_t npub,
                    size_t boundary,
                    const std::vector<std::pair<size_t, size_t>>& runs,
                    uint64_t seed) {
  const PackedBasis<Field> basis(F);
  const Circuit<Field> c = shell(ninputs, npub, boundary, runs);
  const PackedLayout<Field> layout(c, /*w=*/0);

  size_t logv = 0;
  while ((size_t(1) << logv) < ninputs) ++logv;

  SecureRandomEngine rng;
  std::vector<Elt> g0(logv), g1(logv);
  for (auto& x : g0) x = rng.elt(F);
  for (auto& x : g1) x = rng.elt(F);
  const Elt alpha = rng.elt(F);

  std::mt19937_64 gen(seed);
  std::vector<uint8_t> bits(ninputs, 0);
  for (size_t i = npub; i < ninputs; ++i) bits[i] = gen() & 1;

  // Committed packed vector.
  std::vector<Elt> committed(layout.npacked, F.zero());
  for (size_t Y = 0; Y < layout.group.size(); ++Y) {
    if (layout.group[Y] == PackedLayout<Field>::kNone) continue;
    uint64_t u = 0;
    for (size_t i = 0; i < kPack; ++i) {
      u |= uint64_t(bits[kPack * Y + i]) << i;
    }
    committed[layout.group[Y]] = F.of_scalar(u);
  }

  const auto eq = Eqs<Field>::raw_eq2(logv, ninputs, g0.data(), g1.data(),
                                      alpha, F);
  Elt want = F.zero();
  for (size_t x = 0; x < ninputs; ++x) {
    if (layout.packed(x) && bits[x]) F.add(want, eq[x]);
  }

  const PackedForms<Field> forms(basis, logv, layout.group.size(), g0.data(),
                                 g1.data(), alpha, F);
  Elt got = F.zero();
  for (size_t k = 0; k < kPack; ++k) {
    F.add(got, frobenius(forms.z(k, layout, committed.data(), F), k, F));
  }
  EXPECT_EQ(got, want);

  // Twisting the wrong way breaks it.
  Elt wrong = F.zero();
  for (size_t k = 0; k < kPack; ++k) {
    F.add(wrong,
          inverse_frobenius(forms.z(k, layout, committed.data(), F), k, F));
  }
  EXPECT_NE(wrong, want);
}

TEST(ZkPacked, TwistedFormIdentity) {
  const Field F;
  // One run.
  check_identity(F, 1024, 16, 1024, {{16, 1024}}, 1);
  // Several runs with gaps, unpacked inputs between and after, and an input
  // count that is neither a power of two nor a multiple of the pack width.
  check_identity(F, 1000, 7, 900, {{16, 256}, {288, 512}, {640, 896}}, 2);
  // A single group.
  check_identity(F, 100, 3, 100, {{48, 64}}, 3);
  for (uint64_t s = 4; s < 12; ++s) {
    check_identity(F, 5000 + s, 11, 4800, {{16, 2000}, {2048, 4784}}, s);
  }
}

TEST(ZkPacked, LayoutAlignsPackedRowsToSubfieldRows) {
  // npub = 4.  Subfield inputs [4, 69): unpacked [4, 16), packed [16, 64)
  // (3 groups), unpacked [64, 69).  Full-field inputs [69, 73).
  const Circuit<Field> c = shell(73, 4, 69, {{16, 64}});
  {
    const PackedLayout<Field> L(c, /*w=*/10);
    EXPECT_EQ(L.npacked, 3u);
    EXPECT_EQ(L.nzero, 0u);
    EXPECT_EQ(L.map[4], 3u);
    EXPECT_EQ(L.map[15], 14u);
    EXPECT_EQ(L.map[16], PackedLayout<Field>::kNone);
    EXPECT_EQ(L.map[63], PackedLayout<Field>::kNone);
    EXPECT_EQ(L.map[64], 15u);
    EXPECT_EQ(L.map[68], 19u);
    EXPECT_EQ(L.boundary, 20u);
    EXPECT_EQ(L.map[69], 20u);
    EXPECT_EQ(L.n_witness, 24u);
    EXPECT_EQ(L.subfield_wrows, 2u);
    EXPECT_EQ(L.group[1], 0u);
    EXPECT_EQ(L.group[3], 2u);
    EXPECT_EQ(L.group[0], PackedLayout<Field>::kNone);
  }
  {
    // A row wider than the whole subfield region forces zero padding, so the
    // packed row is a whole subfield row.
    const PackedLayout<Field> L(c, /*w=*/64);
    EXPECT_EQ(L.nzero, 44u);
    EXPECT_EQ(L.boundary, 64u);
    EXPECT_EQ(L.subfield_wrows, 1u);
    EXPECT_EQ(L.map[4], 47u);
  }
}

// ---------------------------------------------------------------------------
// End to end on a small circuit.
//
// Inputs: [0] = 1, public bits [1, 9), then private:
//   A bits [9, 49), scalar s [49, 50), B bits [50, 87), D bits [87, 127),
//   u bit [127, 128) (constrained only Boolean), full-field f [128, 129).
// D = (A & B') ^ pub, and f = s * K.  With packing on, the bit runs are
// [9, 49) and [50, 128), whose aligned interiors [16, 48) and [64, 128) are
// packed; the rest carry deferred Boolean assertions.

using RSFactory = LCH14ReedSolomonFactory<Field>;
constexpr size_t kRate = 4;
constexpr size_t kNreq = 16;
constexpr size_t kNA = 40, kNB = 37;
constexpr size_t kIdxA = 9, kIdxS = 49, kIdxB = 50, kIdxD = 87, kIdxU = 127,
                 kIdxF = 128, kNinputs = 129;

struct Built {
  std::unique_ptr<Circuit<Field>> c;
  size_t deferred = 0;
};

Built build(const Field& F, bool packed) {
  using Backend = CompilerBackend<Field>;
  using LC = Logic<Field, Backend>;
  QuadCircuit<Field> Q(F);
  Backend bk(&Q);
  const LC L(&bk, F);
  auto pubv = L.template vinput<8>();
  Q.private_input();
  if (packed) Q.enable_packed_bits();
  auto A = L.template vinput<kNA>();
  auto s = L.eltw_input();
  auto B = L.template vinput<kNB>();
  auto D = L.template vinput<kNA>();
  auto u = L.input();
  (void)u;
  Q.begin_full_field();
  auto f = L.eltw_input();
  for (size_t i = 0; i < kNA; ++i) {
    auto c = L.lxor(L.land(A[i], B[i % kNB]), pubv[i % 8]);
    L.assert_eq(c, D[i]);
  }
  L.assert_eq(f, L.mul(s, L.konst(F.of_scalar_field(0x1234567))));
  Built b;
  b.c = Q.mkcircuit(1);
  b.deferred = Q.npacked_assertions_;
  return b;
}

using DenseP = std::unique_ptr<Dense<Field>>;

DenseP witness(const Field& F, uint64_t seed) {
  std::mt19937_64 gen(seed);
  auto Wp = std::make_unique<Dense<Field>>(1, kNinputs);
  Dense<Field>& W = *Wp;
  auto bit = [&](uint64_t x) { return (x & 1) ? F.one() : F.zero(); };
  W.v_[0] = F.one();
  std::vector<uint64_t> pub(8), A(kNA), B(kNB);
  for (size_t i = 0; i < 8; ++i) W.v_[1 + i] = bit(pub[i] = gen() & 1);
  for (size_t i = 0; i < kNA; ++i) W.v_[kIdxA + i] = bit(A[i] = gen() & 1);
  const Elt s = F.of_scalar(gen() & 0xffff);
  W.v_[kIdxS] = s;
  for (size_t i = 0; i < kNB; ++i) W.v_[kIdxB + i] = bit(B[i] = gen() & 1);
  for (size_t i = 0; i < kNA; ++i) {
    W.v_[kIdxD + i] = bit((A[i] & B[i % kNB]) ^ pub[i % 8]);
  }
  W.v_[kIdxU] = bit(gen() & 1);
  W.v_[kIdxF] = F.mulf(s, F.of_scalar_field(0x1234567));
  return Wp;
}

DenseP public_part(const Circuit<Field>& c, const Dense<Field>& W) {
  auto pub = std::make_unique<Dense<Field>>(1, c.npub_in);
  for (size_t i = 0; i < c.npub_in; ++i) pub->v_[i] = W.v_[i];
  return pub;
}

// Proves and serializes.
std::vector<uint8_t> prove(const Circuit<Field>& c, const Dense<Field>& W,
                           const Field& F, const RSFactory& rsf) {
  ZkProof<Field> zk(c, kRate, kNreq);
  ZkProver<Field, RSFactory> prover(c, F, rsf);
  SecureRandomEngine rng;
  const ProofSeed sigma = ProofSeed::draw(rng);
  Transcript tp((uint8_t*)"packed", 6, sigma);
  absorb_circuit_statement(tp, c, W, F);
  prover.commit(zk, W, tp, rng);
  EXPECT_TRUE(prover.prove(zk, W, tp));
  std::vector<uint8_t> buf;
  sigma.write(buf);
  zk.write(buf, F);
  return buf;
}

bool verify(const Circuit<Field>& c, const Dense<Field>& pub,
            const std::vector<uint8_t>& buf, const Field& F,
            const RSFactory& rsf, size_t tamper_m = ~size_t(0)) {
  ZkProof<Field> zk(c, kRate, kNreq);
  ReadBuffer rb(buf);
  ProofSeed sigma;
  if (!sigma.read(rb)) return false;
  if (!zk.read(rb, F)) return false;
  if (tamper_m < zk.packed_m.size()) F.add(zk.packed_m[tamper_m], F.one());
  ZkVerifier<Field, RSFactory> v(c, rsf, kRate, kNreq, F);
  Transcript tv((uint8_t*)"packed", 6, sigma);
  absorb_circuit_statement(tv, c, pub, F);
  v.recv_commitment(zk, tv);
  return v.verify(zk, pub, tv);
}

bool evaluates_to_zero(const Circuit<Field>& c, const Dense<Field>& W,
                       const Field& F) {
  Prover<Field> p(F);
  typename Prover<Field>::inputs in;
  auto V = p.eval_circuit(&in, &c, W.clone(), F);
  if (V == nullptr) return false;
  for (size_t i = 0; i < V->n1_; ++i) {
    if (V->v_[i] != F.zero()) return false;
  }
  return true;
}

TEST(ZkPacked, SharedPackedInputsAndDirectProducts) {
  const Field F;
  const RSFactory rsf(F);
  using Backend=CompilerBackend<Field>;
  using LC=Logic<Field,Backend>;
  QuadCircuit<Field> q(F);Backend bk(&q);LC lc(&bk,F);
  q.private_input();
  for(size_t i=1;i<16;++i)lc.eltw_input();
  q.enable_packed_bits();
  auto a=lc.template vinput<16>(), b=lc.template vinput<16>();
  for(size_t i=0;i<16;++i)lc.assert_eq(a[i],b[i]);
  q.begin_full_field();
  for(size_t i=0;i<3;++i)lc.eltw_input();
  auto c=q.mkcircuit(1);
  c->packed_input_aliases={{16,1},{32,1}};
  c->input_products={{48,49,50}};
  circuit_id(c->id,*c,F);
  PackedLayout<Field> layout(*c,23);
  EXPECT_EQ(layout.npacked,0u);
  EXPECT_EQ(layout.group[1],layout.map[1]);
  EXPECT_EQ(layout.group[2],layout.map[1]);
  EXPECT_LT(layout.map[1],layout.subfield_wrows*23);
  Dense<Field> w(1,c->ninputs);w.v_[0]=F.one();
  w.v_[1]=F.of_scalar(0xa55a);
  for(size_t i=0;i<32;++i)w.v_[16+i]=F.of_scalar((0xa55a>>(i%16))&1);
  w.v_[48]=F.of_scalar_field(17);w.v_[49]=F.of_scalar_field(23);
  w.v_[50]=F.mulf(w.v_[48],w.v_[49]);
  auto pub=public_part(*c,w);
  const auto proof = prove(*c,w,F,rsf);
  EXPECT_TRUE(verify(*c,*pub,proof,F,rsf));
  F.add(w.v_[50],F.one());
  EXPECT_DEATH((void)prove(*c,w,F,rsf), "invalid quadratic constraints");
  F.add(w.v_[50],F.one());
  c->input_products[0][2]=49;
  circuit_id(c->id,*c,F);
  EXPECT_FALSE(verify(*c,*pub,proof,F,rsf));
  c->input_products[0][2]=50;
  c->packed_input_aliases[1].second=2;
  circuit_id(c->id,*c,F);
  EXPECT_FALSE(verify(*c,*pub,proof,F,rsf));
}

TEST(ZkPacked, CompilerRunsAndDeferredAssertions) {
  const Field F;
  const Built off = build(F, false);
  const Built on = build(F, true);
  EXPECT_TRUE(off.c->packed_bits.empty());
  EXPECT_EQ(off.deferred, 0u);
  using R = std::pair<size_t, size_t>;
  EXPECT_EQ(on.c->packed_bits, (std::vector<R>{{16, 48}, {64, 128}}));
  // Unpacked marked bits: [9,16), 48, [50,64).
  EXPECT_EQ(on.deferred, 7u + 1u + 14u);
  EXPECT_EQ(on.c->ninputs, kNinputs);
  EXPECT_EQ(off.c->ninputs, kNinputs);
  EXPECT_EQ(on.c->subfield_boundary, kIdxF);
  // Packing is part of the circuit's name.
  EXPECT_NE(0, memcmp(on.c->id, off.c->id, sizeof(on.c->id)));
  // Recompiling the unpacked circuit reproduces its name.
  const Built off2 = build(F, false);
  EXPECT_EQ(0, memcmp(off2.c->id, off.c->id, sizeof(off.c->id)));
}

TEST(ZkPacked, EndToEnd) {
  const Field F;
  const RSFactory rsf(F);
  for (bool packed : {false, true}) {
    const Built b = build(F, packed);
    DenseP Wp = witness(F, 7);
    const Dense<Field>& W = *Wp;
    ASSERT_TRUE(evaluates_to_zero(*b.c, W, F));
    DenseP pubp = public_part(*b.c, W);
    const Dense<Field>& pub = *pubp;
    const auto buf = prove(*b.c, W, F, rsf);
    EXPECT_TRUE(verify(*b.c, pub, buf, F, rsf)) << "packed=" << packed;
    if (packed) {
      ZkProof<Field> zk(*b.c, kRate, kNreq);
      EXPECT_EQ(zk.packed_m.size(), kPack);
      EXPECT_EQ(zk.param.nq, b.c->nl + PackedLayout<Field>::kChain);
      // Tampering with any masked value is caught.
      for (size_t k = 0; k < kPack; ++k) {
        EXPECT_FALSE(verify(*b.c, pub, buf, F, rsf, k)) << "k=" << k;
      }
      // A different public input is caught.
      DenseP pub2 = public_part(*b.c, W);
      F.add(pub2->v_[1], F.one());
      EXPECT_FALSE(verify(*b.c, *pub2, buf, F, rsf));
    }
  }
}

// Every unpacked private bit keeps a Boolean assertion: replacing it by a
// non-bit fails evaluation, including the edge bits of the runs that nothing
// else would reject.
TEST(ZkPacked, UnpackedBitsStayAsserted) {
  const Field F;
  const Elt X = F.of_scalar_field(0b10);
  for (bool packed : {false, true}) {
    const Built b = build(F, packed);
    DenseP W0p = witness(F, 11);
    const Dense<Field>& W0 = *W0p;
    ASSERT_TRUE(evaluates_to_zero(*b.c, W0, F));
    std::unique_ptr<PackedLayout<Field>> L;
    if (packed) L = std::make_unique<PackedLayout<Field>>(*b.c, 0);
    for (size_t i = b.c->npub_in; i < kIdxF; ++i) {
      if (i == kIdxS) continue;
      if (L != nullptr && L->packed(i)) continue;
      DenseP W = W0.clone();
      W->v_[i] = X;
      EXPECT_FALSE(evaluates_to_zero(*b.c, *W, F)) << "input " << i;
    }
    // u is read by nothing but its Boolean assertion.  With packing on it is
    // packed, so the circuit alone accepts a non-bit there; the commitment,
    // which only holds bits, is what rules it out.
    DenseP W = W0.clone();
    W->v_[kIdxU] = X;
    EXPECT_EQ(evaluates_to_zero(*b.c, *W, F), packed);
  }
}

// Replicates ZkProver::commit, but lets the caller corrupt the committed
// vector and choose the subfield boundary the tableau is blinded with.
template <class Corrupt>
std::vector<uint8_t> cheat(const Circuit<Field>& c, const Dense<Field>& W,
                           const Field& F, const RSFactory& rsf,
                           size_t boundary, Corrupt corrupt) {
  ZkProof<Field> zk(c, kRate, kNreq);
  ZkProver<Field, RSFactory> prover(c, F, rsf);
  SecureRandomEngine rng;
  const ProofSeed sigma = ProofSeed::draw(rng);
  Transcript tp((uint8_t*)"packed", 6, sigma);
  absorb_circuit_statement(tp, c, W, F);
  prover.commit_packed_inputs(zk, W);
  corrupt(prover.witness_);
  prover.fill_pad(rng);
  ZkCommon<Field>::setup_lqc(c, prover.lqc_, prover.start_pad_);
  prover.fill_packed_pads(rng);
  ZkCommon<Field>::setup_packed_lqc(c, *prover.layout_, prover.lqc_);
  prover.lp_ = std::make_unique<LigeroProver<Field, RSFactory>>(zk.param);
  prover.lp_->commit(zk.com, tp, &prover.witness_[0], boundary,
                     &prover.lqc_[0], rsf, rng, F);
  prover.prove(zk, W, tp);
  std::vector<uint8_t> buf;
  sigma.write(buf);
  zk.write(buf, F);
  return buf;
}

// The Ligero verifier enforces subfield membership of the packed rows.
TEST(ZkPacked, NonSubfieldPackedRowsRejected) {
  const Field F;
  const RSFactory rsf(F);
  const Built b = build(F, true);
  DenseP Wp = witness(F, 13);
  const Dense<Field>& W = *Wp;
  DenseP pubp = public_part(*b.c, W);
  const Dense<Field>& pub = *pubp;
  const PackedLayout<Field> L(*b.c, ZkProof<Field>(*b.c, kRate, kNreq).param.w);
  auto none = [](std::vector<Elt>&) {};

  // Control: the replica with the honest boundary verifies.
  EXPECT_TRUE(verify(*b.c, pub, cheat(*b.c, W, F, rsf, L.boundary, none), F,
                     rsf));
  // Honest values, rows blinded with full-field randomness: every check but
  // the subfield check passes, and the proof is rejected.
  EXPECT_FALSE(verify(*b.c, pub, cheat(*b.c, W, F, rsf, 0, none), F, rsf));
  // A packed element outside the subfield.
  auto outside = [&](std::vector<Elt>& w) {
    F.add(w[0], F.of_scalar_field(0b10));
  };
  EXPECT_FALSE(verify(*b.c, pub, cheat(*b.c, W, F, rsf, 0, outside), F, rsf));
  // A packed element in the subfield, properly blinded, but encoding bits
  // other than the ones GKR ran on: the input claim no longer matches.
  for (size_t bit = 0; bit < kPack; bit += 5) {
    auto flip = [&](std::vector<Elt>& w) {
      F.add(w[1], F.beta(bit));
    };
    EXPECT_FALSE(verify(*b.c, pub,
                        cheat(*b.c, W, F, rsf, L.boundary, flip), F, rsf))
        << "bit " << bit;
  }
}

// A prover that reveals wrong masked values M_k but absorbs them consistently:
// the transcript and Merkle checks pass, and rejection must come from Ligero's
// linear test.  The verifier's own constraint rows are rebuilt and evaluated
// on the committed witness to show which rows the cheat breaks.
struct WrongM {
  bool ok;                        // full verifier verdict
  std::vector<bool> row_holds;    // [0] input row, [1 + k] masked form k
};

WrongM prove_with_wrong_m(const Circuit<Field>& c, const Dense<Field>& W,
                          const Dense<Field>& pub, const std::vector<Elt>& d,
                          const Field& F, const RSFactory& rsf) {
  ZkProof<Field> zk(c, kRate, kNreq);
  ZkProver<Field, RSFactory> prover(c, F, rsf);
  prover.packed_m_delta_ = d;
  SecureRandomEngine rng;
  const ProofSeed sigma = ProofSeed::draw(rng);
  Transcript tp((uint8_t*)"packed", 6, sigma);
  absorb_circuit_statement(tp, c, W, F);
  prover.commit(zk, W, tp, rng);
  EXPECT_TRUE(prover.prove(zk, W, tp));
  std::vector<uint8_t> buf;
  sigma.write(buf);
  zk.write(buf, F);

  WrongM out;
  out.ok = verify(c, pub, buf, F, rsf);

  // Replay the verifier's transcript and constraint assembly.
  ZkProof<Field> zv(c, kRate, kNreq);
  ReadBuffer rb(buf);
  ProofSeed sigma_v;
  EXPECT_TRUE(sigma_v.read(rb));
  EXPECT_TRUE(zv.read(rb, F));
  const PackedLayout<Field> L(c, zv.param.w);
  Transcript tv((uint8_t*)"packed", 6, sigma_v);
  absorb_circuit_statement(tv, c, pub, F);
  LigeroVerifier<Field, RSFactory>::receive_commitment(zv.com, tv);
  ZkCommon<Field>::initialize_sumcheck_fiat_shamir(tv, c, F);
  std::vector<typename ZkCommon<Field>::Llc> A;
  std::vector<Elt> b;
  std::vector<Elt> m = zv.packed_m;
  typename ZkCommon<Field>::Packed pk;
  pk.layout = &L;
  pk.m = &m;
  const size_t nc = ZkCommon<Field>::verifier_constraints(
      c, pub, zv.proof, nullptr, A, b, tv, L.n_witness, F, nullptr, nullptr,
      &pk);
  std::vector<Elt> lhs(nc, F.zero());
  for (const auto& t : A) F.add(lhs[t.c], F.mulf(t.k, prover.witness_[t.w]));
  const size_t first = nc - (1 + kPack);
  for (size_t r = first; r < nc; ++r) out.row_holds.push_back(lhs[r] == b[r]);
  // The GKR layer rows are untouched by the cheat.
  for (size_t r = 0; r < first; ++r) EXPECT_EQ(lhs[r], b[r]) << "layer row " << r;
  return out;
}

TEST(ZkPacked, WrongMaskedValuesRejected) {
  const Field F;
  const RSFactory rsf(F);
  const Built b = build(F, true);
  DenseP Wp = witness(F, 19);
  DenseP pubp = public_part(*b.c, *Wp);
  SecureRandomEngine rng;

  // Honest control: every packed row holds.
  {
    const WrongM r = prove_with_wrong_m(*b.c, *Wp, *pubp,
                                        std::vector<Elt>(kPack, F.zero()), F,
                                        rsf);
    EXPECT_TRUE(r.ok);
    for (bool h : r.row_holds) EXPECT_TRUE(h);
  }
  // One M_k off by Delta: its masked-form row fails, and so does the input
  // row, which carries M_k^(2^k).
  for (size_t k : {size_t(0), size_t(7), size_t(15)}) {
    std::vector<Elt> d(kPack, F.zero());
    d[k] = rng.elt(F);
    const WrongM r = prove_with_wrong_m(*b.c, *Wp, *pubp, d, F, rsf);
    EXPECT_FALSE(r.ok) << "k=" << k;
    EXPECT_FALSE(r.row_holds[0]) << "k=" << k;
    for (size_t j = 0; j < kPack; ++j) {
      EXPECT_EQ(r.row_holds[1 + j], j != k) << "k=" << k << " j=" << j;
    }
  }
  // All sixteen adjusted with SUM_k Delta_k^(2^k) = 0, so the input row still
  // balances (Frobenius is additive): only the masked-form rows fail.
  {
    std::vector<Elt> d(kPack);
    Elt s = F.zero();
    for (size_t k = 1; k < kPack; ++k) {
      d[k] = rng.elt(F);
      F.add(s, frobenius(d[k], k, F));
    }
    d[0] = s;  // char 2: Delta_0 = SUM_{k>=1} Delta_k^(2^k) cancels them
    const WrongM r = prove_with_wrong_m(*b.c, *Wp, *pubp, d, F, rsf);
    EXPECT_FALSE(r.ok);
    EXPECT_TRUE(r.row_holds[0]);
    for (size_t j = 0; j < kPack; ++j) EXPECT_FALSE(r.row_holds[1 + j]);
  }
}

TEST(ZkPacked, ExtraConstraintsRejected) {
  const Field F;
  const RSFactory rsf(F);
  const Built b = build(F, true);
  DenseP Wp = witness(F, 17);
  const Dense<Field>& W = *Wp;
  DenseP pubp = public_part(*b.c, W);
  const Dense<Field>& pub = *pubp;
  const auto buf = prove(*b.c, W, F, rsf);

  typename ZkCommon<Field>::ExtraConstraints extra;
  extra.gen = [&](std::vector<typename ZkCommon<Field>::Llc>& a,
                  std::vector<Elt>& bb, size_t& ci) {
    a.push_back({ci, 0, F.one()});
    bb.push_back(F.zero());
    ++ci;
  };
  ZkProof<Field> zk(*b.c, kRate, kNreq);
  ReadBuffer rb(buf);
  ProofSeed sigma;
  ASSERT_TRUE(sigma.read(rb));
  ASSERT_TRUE(zk.read(rb, F));
  ZkVerifier<Field, RSFactory> v(*b.c, rsf, kRate, kNreq, F);
  Transcript tv((uint8_t*)"packed", 6, sigma);
  absorb_circuit_statement(tv, *b.c, pub, F, &extra);
  v.recv_commitment(zk, tv);
  EXPECT_FALSE(v.verify(zk, pub, tv, &extra));

  auto prove_with_extra = [&]() {
    ZkProof<Field> zkp(*b.c, kRate, kNreq);
    ZkProver<Field, RSFactory> prover(*b.c, F, rsf);
    SecureRandomEngine rng;
    Transcript tp((uint8_t*)"packed", 6, ProofSeed::draw(rng));
    absorb_circuit_statement(tp, *b.c, W, F, &extra);
    prover.commit(zkp, W, tp, rng);
    prover.prove(zkp, W, tp, &extra);
  };
  EXPECT_DEATH(prove_with_extra(), "extra constraints on a packed circuit");
}

}  // namespace
}  // namespace proofs
