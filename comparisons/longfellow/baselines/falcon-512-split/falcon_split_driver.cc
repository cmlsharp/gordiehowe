// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Falcon-512 proof of possession, split Longfellow-style baseline: a worker of
// common/bench.py.
//
// usage: falcon_split_driver native|emulated narrow
//        falcon_split_driver_wide native|emulated wide
//
// Two circuits, two Ligero proofs:
//   H over upstream's GF(2^128): SHAKE256(nonce || msg) and HashToPoint by
//     compaction routing (falcon_h2p_ptr.h) give the challenge c, 16 bits per
//     coefficient.
//   A over the arm's field: the Falcon verification s1 = c - s2 h (mod q),
//     with h in NTT form public, and the norm bound ||(s1, s2)||^2 <= beta^2
//     and the encoding bound of s2; the native arm (F_12289^k) in the NTT
//     domain with limb range checks (falcon_verify.h), the emulated arm
//     (Goldilocks extension) with lazy reductions mod q (falcon_verify_fp.h)
//     and a binary norm.
//   Binding: c's 8192 bits, cut into 64 chunks of 128 bits, each bound in both
//     circuits by the MAC mac_i = a_v * chunk_i + a_p,i over GF(2^128),
//     computed bit by bit (falcon_mac_baseline.h): a_p committed in both, a_v
//     drawn after both commitments, the tags mac_i sent before the proofs.
// The message, the nonce, the signature s2 and c are private; the public key
// h is public (proof of possession).
//
// The circuits, witnesses and parameters are the fork's
// falcon_baseline_native_e2e_test.cc and falcon_baseline_fp_e2e_test.cc
// (branch mac-bench 8d8e0aa4); the protocol code is upstream's (ZkProver,
// ZkVerifier, Transcript) with the Reed-Solomon encoding of crt_extension_rs.h.
//
// Per trial:
//   witness   = the full witness from the instance (nonce, message, s2, h):
//               HashToPoint and its SHAKE256 block witnesses, the norm,
//               reduction and encoding advice, the crossing chunks and both
//               fills (a detail, outside the totals; the instance itself,
//               a synthetic short signature, is made once)
//   commit_ms = statement absorption + MAC pads + H commit + A commit
//   prove_ms  = MAC key and tags + H prove + A prove
//   verify_ms = statement absorption, both ZkVerifiers' construction and
//               commitments, the MAC key and tags, both verify calls
// With LFB_PROOF_SEED set, the prover's coins (MAC pads, Ligero padding)
// come from a transcript initialized with its value, the same in every
// trial, and each trial prints "LFB_PROOF_SHA256 <hex>", the SHA-256 of the
// two serialized proofs: a byte-identity check across builds.
// details give each half and the fork's verifier definition
// (v_statement + v_h_verify + v_a_verify).
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "arrays/dense.h"
#include "bench_worker.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/mac/mac_reference.h"
#include "circuits/tests/sha3/sha3_circuit.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "crt_extension_rs.h"
#include "subgroup_reed_solomon.h"
#include "falcon_baseline_instance.h"
#include "util/crypto.h"
#include "falcon_baseline_profile.h"
#include "falcon_encoding.h"
#include "falcon_h2p_ptr.h"
#include "falcon_h2p_stream.h"
#include "falcon_hash_to_point.h"
#include "falcon_mac_baseline.h"
#include "falcon_ntt.h"
#include "falcon_ntt_lazy.h"
#include "falcon_range_bits.h"
#include "falcon_verify.h"
#include "falcon_verify_fp.h"
#include "gf2k/lch14_reed_solomon.h"
#include "pq_emulated_field.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/panic.h"
#include "zk/zk_common.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

namespace proofs {
namespace {
using falcon_baseline::LigeroHalf;
constexpr uint64_t Q = falcon_baseline::kFalconQ;
constexpr size_t kCoefficientBits = falcon_baseline::kCoefficientBits;
constexpr size_t kMagBits = falcon_baseline::kMagBits;
constexpr size_t kNormBits = falcon_baseline::kNormBits;

double ms_since(std::chrono::steady_clock::time_point t0) {
  return std::chrono::duration<double, std::milli>(
             std::chrono::steady_clock::now() - t0)
      .count();
}

// The emulated arm's encoder (the fork's pq_fp_rs.h): the subgroup encoder on
// the 2^32-th roots of unity of F_p (subgroup_reed_solomon.h), applied
// componentwise to Goldilocks extension rows by fp_goldilocks.h's and
// fp_goldilocks4.h's wrappers.
template <class Ext> struct GoldilocksRS;
template <> struct GoldilocksRS<Fp64G2> {
  template <class Base> using type = Fp64G2ReedSolomonFactory<Base>;
};
template <> struct GoldilocksRS<Fp64G4> {
  template <class Base> using type = Fp64G4ReedSolomonFactory<Base>;
};

// A ZkProof at h's parameters: block_enc 0 is upstream's power-of-two
// search (the constructors without block_enc).
template <class F>
std::unique_ptr<ZkProof<F>> make_proof(const Circuit<F>& c,
                                       const LigeroHalf& h) {
  if (h.block_enc == 0) {
    return std::make_unique<ZkProof<F>>(c, h.rate, h.nreq);
  }
  return std::make_unique<ZkProof<F>>(c, h.rate, h.nreq, h.block_enc);
}
template <class F, class RSF>
std::unique_ptr<ZkVerifier<F, RSF>> make_verifier(const Circuit<F>& c,
                                                  const RSF& rsf,
                                                  const LigeroHalf& h,
                                                  const F& f) {
  if (h.block_enc == 0) {
    return std::make_unique<ZkVerifier<F, RSF>>(c, rsf, h.rate, h.nreq, f);
  }
  return std::make_unique<ZkVerifier<F, RSF>>(c, rsf, h.rate, h.nreq,
                                              h.block_enc, f);
}

// The statement on the transcript before the commitments: both circuit ids
// and the public inputs fixed before the protocol starts (the constant one
// of H; the constant one and h_hat of A).  The MAC key a_v is a challenge
// and the per-chunk tags are prover messages, absorbed after it.
template <class HF, class AF>
void absorb_statement(Transcript& t, const Circuit<HF>& ce,
                      const Circuit<AF>& ca, const Dense<HF>& pe,
                      const Dense<AF>& pa, size_t na, const HF& hf,
                      const AF& af) {
  t.write(ce.id, sizeof(ce.id));
  t.write(ca.id, sizeof(ca.id));
  t.write(pe.v_[0], hf);
  for (size_t i = 0; i < na; ++i) t.write(pa.v_[i], af);
}

// The H circuit, shared by both arms.
template <class HF, size_t kW>
std::unique_ptr<Circuit<HF>> build_h_circuit(const HF& hf, size_t seed_len,
                                             size_t nbws, size_t S, size_t n,
                                             size_t nch) {
  using HCBK = CompilerBackend<HF>;
  using HLC = Logic<HF, HCBK>;
  using HvW = typename HLC::template bitvec<kW>;
  auto QE_owner = std::make_unique<QuadCircuit<HF>>(hf);
  auto& QE = *QE_owner;
  const HCBK cbkE(&QE);
  const HLC lcE(&cbkE, hf);
  HvW avE;
  for (size_t i = 0; i < kW; ++i) avE[i] = lcE.input();
  std::vector<HvW> tgtE(nch);
  for (auto& t : tgtE)
    for (size_t i = 0; i < kW; ++i) t[i] = lcE.input();
  QE.private_input();
  std::vector<typename HLC::v8> seedw(seed_len);
  for (auto& x : seedw) x = lcE.template vinput<8>();
  std::vector<typename Sha3Circuit<HLC>::BlockWitness> bwwE(nbws);
  for (auto& b : bwwE) b.input(lcE);
  std::vector<typename HLC::template bitvec<kCoefficientBits>> cE(n), posE(n);
  for (auto& x : cE) x = lcE.template vinput<kCoefficientBits>();
  for (auto& x : posE) x = lcE.template vinput<16>();
  std::vector<HvW> apE(nch);
  for (auto& a : apE)
    for (size_t i = 0; i < kW; ++i) a[i] = lcE.input();
  QE.begin_full_field();
  {
    Sha3Circuit<HLC> sha3(lcE);
    std::vector<typename HLC::v8> out;
    sha3.assert_shake256(seedw, 2 * S, out, bwwE);
    auto stream = falcon_h2p_stream_from_bytes(lcE, out, S);
    falcon_h2p_ptr(lcE, stream, cE, posE, kFalconCutoff, n);
    std::vector<HvW> chunks(nch);
    for (auto& ch : chunks)
      for (size_t i = 0; i < kW; ++i) ch[i] = lcE.bit(0);
    for (size_t j = 0; j < n; ++j)
      for (size_t b = 0; b < kCoefficientBits; ++b)
        chunks[(j * kCoefficientBits + b) / kW]
              [(j * kCoefficientBits + b) % kW] = cE[j][b];
    falcon_mac_baseline<kW>(lcE, chunks, avE, apE, tgtE);
  }
  return QE.mkcircuit(1);
}

// The common protocol of both arms, given both circuits, witnesses and
// encoders.  apH_offset/apA_offset index the MAC pads a_p in the witnesses;
// h_hat holds A's public inputs after the constant one.
template <class HF, class MF, class AF, class RSH, class RSA, size_t kW>
struct Protocol {
  const HF& hf;
  const MF& mf;
  const AF& af;
  const RSH& rsh;
  const RSA& rsa;
  const Circuit<HF>& circE;
  const Circuit<AF>& circA;
  Dense<HF>& WE;
  Dense<AF>& WA;
  size_t apH_offset, apA_offset;
  const std::vector<uint64_t>& hhat;
  const std::vector<typename MF::Elt>& cref;
  LigeroHalf lh, la;
  const char* label;
  SecureRandomEngine secure_rng;

  lfb::Trial run() {
    using std::chrono::steady_clock;
    lfb::Trial T;
    const char* proof_seed = std::getenv("LFB_PROOF_SEED");
    std::unique_ptr<Transcript> seeded_rng;
    if (proof_seed != nullptr) {
      seeded_rng = std::make_unique<Transcript>(
          (const uint8_t*)proof_seed, std::strlen(proof_seed));
    }
    RandomEngine& rng = seeded_rng ? static_cast<RandomEngine&>(*seeded_rng)
                                    : static_cast<RandomEngine&>(secure_rng);
    const size_t n = hhat.size(), nch = cref.size();
    std::vector<typename MF::Elt> apv(nch);
    auto zkE = make_proof(circE, lh);
    auto zkA = make_proof(circA, la);
    ZkProver<HF, RSH> pE(circE, hf, rsh);
    ZkProver<AF, RSA> pA(circA, af, rsa);
    Transcript tp((const uint8_t*)label, std::strlen(label));

    auto t0 = steady_clock::now();
    absorb_statement(tp, circE, circA, WE, WA, 1 + n, hf, af);
    const double p_statement = ms_since(t0);
    // Fresh MAC pads per proof (the commitment's randomness: in commit).
    t0 = steady_clock::now();
    for (size_t c = 0; c < nch; ++c) {
      apv[c] = rng.elt(mf);
      for (size_t i = 0; i < kW; ++i)
        WE.v_[apH_offset + c * kW + i] = hf.of_scalar(apv[c][i]);
    }
    const double pads = ms_since(t0);
    t0 = steady_clock::now();
    pE.commit(*zkE, WE, tp, rng);
    const double h_commit = ms_since(t0);
    t0 = steady_clock::now();
    for (size_t c = 0; c < nch; ++c)
      for (size_t i = 0; i < kW; ++i)
        WA.v_[apA_offset + c * kW + i] = af.of_scalar(apv[c][i]);
    pA.commit(*zkA, WA, tp, rng);
    const double a_commit = ms_since(t0);

    t0 = steady_clock::now();
    const typename MF::Elt av = tp.elt(mf);
    auto tgt = falcon_mac_baseline_ref(mf, cref, av, apv);
    // The tags are prover messages: on the transcript before the proofs.
    for (size_t c = 0; c < nch; ++c) tp.write(tgt[c], mf);
    {
      size_t b = 1;
      for (size_t i = 0; i < kW; ++i) WE.v_[b++] = av[i] ? hf.one() : hf.zero();
      for (size_t c = 0; c < nch; ++c)
        for (size_t i = 0; i < kW; ++i)
          WE.v_[b++] = tgt[c][i] ? hf.one() : hf.zero();
    }
    {
      size_t b = 1 + n;
      for (size_t i = 0; i < kW; ++i) WA.v_[b++] = av[i] ? af.one() : af.zero();
      for (size_t c = 0; c < nch; ++c)
        for (size_t i = 0; i < kW; ++i)
          WA.v_[b++] = tgt[c][i] ? af.one() : af.zero();
    }
    const double macs = ms_since(t0);
    t0 = steady_clock::now();
    const bool okE = pE.prove(*zkE, WE, tp);
    const double h_prove = ms_since(t0);
    t0 = steady_clock::now();
    const bool okA = pA.prove(*zkA, WA, tp);
    const double a_prove = ms_since(t0);

    std::vector<uint8_t> bufE, bufA;
    zkE->write(bufE, hf);
    zkA->write(bufA, af);
    T.proof_bytes = bufE.size() + bufA.size() + nch * MF::kBytes;
    if (proof_seed != nullptr) {
      SHA256 sha;
      sha.Update(bufE.data(), bufE.size());
      sha.Update(bufA.data(), bufA.size());
      uint8_t digest[kSHA256DigestSize];
      sha.DigestData(digest);
      std::printf("LFB_PROOF_SHA256 ");
      for (uint8_t b : digest) std::printf("%02x", b);
      std::printf("\n");
      std::fflush(stdout);
    }

    // Verifier.  The tags are the prover's message (recomputed here from the
    // pads, as the fork's test does).
    t0 = steady_clock::now();
    Transcript tv((const uint8_t*)label, std::strlen(label));
    Dense<HF> pubE(1, circE.ninputs);
    Dense<AF> pubA(1, circA.ninputs);
    {
      DenseFiller<HF> f(pubE);
      f.push_back(hf.one());
    }
    {
      DenseFiller<AF> f(pubA);
      f.push_back(af.one());
      for (size_t i = 0; i < n; ++i) f.push_back(af.of_scalar(hhat[i]));
    }
    absorb_statement(tv, circE, circA, pubE, pubA, 1 + n, hf, af);
    const double v_statement = ms_since(t0);
    t0 = steady_clock::now();
    auto vE = make_verifier(circE, rsh, lh, hf);
    auto vA = make_verifier(circA, rsa, la, af);
    vE->recv_commitment(*zkE, tv);
    vA->recv_commitment(*zkA, tv);
    const typename MF::Elt av_v = tv.elt(mf);
    auto tgt_v = falcon_mac_baseline_ref(mf, cref, av_v, apv);
    // The negative check: with LFB_CORRUPT_TAG set, the verifier receives
    // the first tag plus one, and must reject.
    if (std::getenv("LFB_CORRUPT_TAG") != nullptr) {
      tgt_v[0] = mf.addf(tgt_v[0], mf.one());
    }
    for (size_t c = 0; c < nch; ++c) tv.write(tgt_v[c], mf);
    {
      DenseFiller<HF> f(pubE);
      f.push_back(hf.one());
      fill_gf2k<MF, HF>(av_v, f, hf);
      for (size_t c = 0; c < nch; ++c) fill_gf2k<MF, HF>(tgt_v[c], f, hf);
    }
    {
      DenseFiller<AF> f(pubA);
      f.push_back(af.one());
      for (size_t i = 0; i < n; ++i) f.push_back(af.of_scalar(hhat[i]));
      fill_gf2k<MF, AF>(av_v, f, af);
      for (size_t c = 0; c < nch; ++c) fill_gf2k<MF, AF>(tgt_v[c], f, af);
    }
    const double v_setup = ms_since(t0);
    t0 = steady_clock::now();
    const bool vokE = vE->verify(*zkE, pubE, tv);
    const double v_h = ms_since(t0);
    t0 = steady_clock::now();
    const bool vokA = vA->verify(*zkA, pubA, tv);
    const double v_a = ms_since(t0);

    T.commit_ms = p_statement + pads + h_commit + a_commit;
    T.prove_ms = macs + h_prove + a_prove;
    T.verify_ms = v_statement + v_setup + v_h + v_a;
    T.ok = okE && okA && vokE && vokA;
    T.add("p_statement", p_statement);
    T.add("pads", pads);
    T.add("h_commit", h_commit);
    T.add("a_commit", a_commit);
    T.add("macs", macs);
    T.add("h_prove", h_prove);
    T.add("a_prove", a_prove);
    T.add("v_statement", v_statement);
    T.add("v_setup", v_setup);
    T.add("v_h_verify", v_h);
    T.add("v_a_verify", v_a);
    T.add("verify_fork_def", v_statement + v_h + v_a);
    T.add("h_bytes", bufE.size());
    T.add("a_bytes", bufA.size());
    T.add("tag_bytes", nch * MF::kBytes);
    T.add("h_nrow", zkE->param.nrow);
    T.add("h_block", zkE->param.block);
    T.add("h_block_enc", zkE->param.block_enc);
    T.add("a_nrow", zkA->param.nrow);
    T.add("a_block", zkA->param.block);
    T.add("a_block_enc", zkA->param.block_enc);
    return T;
  }
};

// c's bits as 128-bit chunks (the MAC messages), on the host.
template <class MF>
std::vector<typename MF::Elt> crossing_chunks(const MF& mf,
                                              const std::vector<uint64_t>& c,
                                              size_t n, size_t nch,
                                              size_t chunk_bytes) {
  std::vector<typename MF::Elt> cref(nch);
  std::vector<uint8_t> buf((kCoefficientBits * n + 7) / 8, 0);
  for (size_t j = 0; j < n; ++j)
    for (size_t b = 0; b < kCoefficientBits; ++b)
      if ((c[j] >> b) & 1)
        buf[(j * kCoefficientBits + b) / 8] |=
            1u << ((j * kCoefficientBits + b) % 8);
  for (size_t i = 0; i < nch; ++i)
    cref[i] = mf.of_bytes_field(&buf[i * chunk_bytes]).value();
  return cref;
}

// The signed message: nonce and msg from a fixed seed, as in the fork.
struct Instance {
  std::vector<uint8_t> nonce, msg, seed;
  std::mt19937 g{20260915};
  Instance() : nonce(40), msg(32) {
    for (auto& x : nonce) x = (uint8_t)g();
    for (auto& x : msg) x = (uint8_t)g();
    seed = nonce;
    seed.insert(seed.end(), msg.begin(), msg.end());
  }
};

// An s2 coefficient's top magnitude slot holds its encoding high part
// (falcon_encoding_native_bits).
template <class Prm, class ALC>
FalconCoeffWires<ALC> decl_coeff(const ALC& lc, const FalconNormParams& p,
                                 bool high_slot) {
  constexpr size_t kLimb = Prm::kLimbBits;
  FalconCoeffWires<ALC> c;
  c.a_lo.resize(p.La);
  for (size_t l = 0; l < p.La; ++l)
    c.a_lo[l] = high_slot && l + 1 == p.La
                    ? falcon_limb_input<Prm::kHighBits>(lc)
                    : falcon_limb_input<kLimb>(lc);
  c.sq.resize(p.Lq);
  for (auto& x : c.sq) x = falcon_limb_input<kLimb>(lc);
  c.S.resize(p.Ls);
  for (auto& x : c.S) x = falcon_limb_input<kLimb>(lc);
  c.add_carry.resize(p.Ls);
  for (auto& x : c.add_carry) x = lc.eltw_input();
  c.col_carry.resize(p.Lq - 1);
  for (auto& cc : c.col_carry) {
    cc.resize(kFalconCarryLimbs);
    for (auto& x : cc) x = falcon_limb_input<kLimb>(lc);
  }
  return c;
}
template <class Prm, class AF>
void fill_coeff(DenseFiller<AF>& f, const AF& F, const FalconCoeffAdvice& a,
                bool high_slot) {
  constexpr size_t kLimb = Prm::kLimbBits;
  for (size_t l = 0; l < a.a_lo.size(); ++l)
    f.push_back(a.a_lo[l],
                high_slot && l + 1 == a.a_lo.size() ? Prm::kHighBits : kLimb,
                F);
  for (uint64_t x : a.sq) f.push_back(x, kLimb, F);
  for (uint64_t x : a.S) f.push_back(x, kLimb, F);
  for (uint64_t x : a.add_carry) f.push_back(F.of_scalar(x));
  for (auto& cc : a.col_carry)
    for (uint64_t x : cc) f.push_back(x, kLimb, F);
}

// Ordinary binary range checks, with integer squaring in the field (the
// fork's falcon_baseline_fp_e2e_test.cc).  Even before the final bound
// check, 2n * (2^kMagBits-1)^2 < 2^kNormBits, so the sum cannot wrap.
template <class LC>
void assert_binary_norm(
    const LC& lc, const std::vector<typename LC::EltW>& coeffs,
    const std::vector<typename LC::template bitvec<kMagBits>>& magnitudes,
    const typename LC::template bitvec<kNormBits>& total, uint64_t bound) {
  auto sum = lc.konst(uint64_t{0});
  for (size_t i = 0; i < coeffs.size(); ++i) {
    const auto a = lc.as_scalar(magnitudes[i]);
    lc.assert1(lc.leq(kMagBits, magnitudes[i].data(),
                      lc.template vbit<kMagBits>(Q / 2).data()));
    const auto opposite = lc.sub(lc.konst(Q), coeffs[i]);
    lc.assert0(lc.mul(lc.sub(a, coeffs[i]), lc.sub(a, opposite)));
    sum = lc.add(sum, lc.mul(a, a));
  }
  lc.assert_eq(sum, lc.as_scalar(total));
  lc.assert1(lc.leq(kNormBits, total.data(),
                    lc.template vbit<kNormBits>(bound).data()));
}

// The H witness: the constant one, placeholders for a_v and the tags, the
// seed, SHAKE's block witnesses, c, the routing positions, then the pads
// (whose offset is returned).
template <class HF, class MF>
size_t fill_h_witness(Dense<HF>& WE, const HF& hf, const MF& mf,
                      const std::vector<uint8_t>& seed,
                      const std::vector<Sha3Witness::BlockWitness>& shake_bws,
                      const FalconH2PWitness& hw, size_t n, size_t nch) {
  DenseFiller<HF> f(WE);
  f.push_back(hf.one());
  fill_gf2k<MF, HF>(mf.zero(), f, hf);
  for (size_t c = 0; c < nch; ++c) fill_gf2k<MF, HF>(mf.zero(), f, hf);
  for (uint8_t b : seed) f.push_back(b, 8, hf);
  for (auto& bw : shake_bws) Sha3Witness::fill_witness(f, bw, hf);
  for (size_t j = 0; j < n; ++j)
    f.push_back((uint64_t)hw.c[j], kCoefficientBits, hf);
  for (size_t j = 0; j < n; ++j) f.push_back((uint64_t)hw.pos[j], 16, hf);
  const size_t off = f.size();
  for (size_t c = 0; c < nch; ++c) fill_gf2k<MF, HF>(mf.zero(), f, hf);
  return off;
}

// Holds everything a worker keeps between trials.
struct Worker {
  virtual ~Worker() = default;
  virtual lfb::Trial run() = 0;
};

template <class P>
struct NativeWorker : Worker {
  using Prm = falcon_baseline::FalconBaselineNative<P>;
  static constexpr size_t kW = Prm::kW;
  using HF = typename Prm::HashField;
  using MF = typename Prm::MacField;
  using RSH = LCH14ReedSolomonFactory<HF>;
  using AF = typename Prm::Field;
  using ACBK = CompilerBackend<AF>;
  using ALC = Logic<AF, ACBK>;
  using AvW = typename ALC::template bitvec<kW>;
  using EA = typename ALC::EltW;
  using RSA = CrtExtensionReedSolomonFactory<AF, Fp14Crt, 1>;

  const HF hf;
  const MF mf;
  const Fp14 base{Q};
  const AF af{base, AF::beta_};
  const RSH rsh{hf};
  const Fp14Crt base_crt;
  const RSA rsa{base_crt};
  std::unique_ptr<Circuit<HF>> circE;
  std::unique_ptr<Circuit<AF>> circA;
  std::unique_ptr<Dense<HF>> WE;
  std::unique_ptr<Dense<AF>> WA;
  std::vector<uint64_t> hhat;
  std::vector<typename MF::Elt> cref;
  std::unique_ptr<Protocol<HF, MF, AF, RSH, RSA, kW>> proto;
  // The instance (the signed message, its nonce, s2 and h) and the
  // witness's constants, kept for the per-trial witness.
  Instance inst;
  std::vector<uint64_t> s2, zetas;
  FalconNormParams rnp;
  size_t apH = 0, apA = 0;

  // The full witness from the instance: HashToPoint and its SHAKE256 block
  // witnesses, c's NTT, the norm and encoding advice, the crossing chunks,
  // and both fills (WE, WA; the MAC pads are drawn in the protocol).
  // Returns its time (ms).
  double witness() {
    const auto t0 = std::chrono::steady_clock::now();
    const size_t n = falcon_baseline::kFalconN;
    auto hw = falcon_hash_to_point(inst.nonce, inst.msg, n);
    check(hw.n_accepts >= n, "HashToPoint accepts");
    std::vector<Sha3Witness::BlockWitness> shake_bws;
    Sha3Witness::compute_witness_shake256(inst.seed, 2 * hw.S, shake_bws);
    std::vector<uint64_t> chat(n);
    for (size_t i = 0; i < n; ++i) chat[i] = hw.c[i] % Q;
    falcon_ntt_ref(chat, zetas, Q);
    auto wit = falcon_build_witness(s2, hhat, chat, zetas, rnp);
    check(wit.norm.sum_leq_bound, "norm bound");
    const auto enc = falcon_encoding_advice(s2, Q, kFalcon512HighBudget);
    check(enc.encodable, "encodable");
    const size_t nch = Prm::kChunks;
    cref = crossing_chunks(mf, hw.c, n, nch, Prm::kBytes);
    apH = fill_h_witness(*WE, hf, mf, inst.seed, shake_bws, hw, n, nch);
    {
      DenseFiller<AF> f(*WA);
      f.push_back(af.one());
      for (size_t i = 0; i < n; ++i) f.push_back(af.of_scalar(hhat[i]));
      fill_gf2k<MF, AF>(mf.zero(), f, af);
      for (size_t c = 0; c < nch; ++c) fill_gf2k<MF, AF>(mf.zero(), f, af);
      for (size_t j = 0; j < n; ++j)
        f.push_back((uint64_t)hw.c[j], kCoefficientBits, af);
      for (size_t i = 0; i < n; ++i) f.push_back(af.of_scalar(s2[i]));
      for (size_t i = 0; i < 2 * n; ++i)
        fill_coeff<Prm>(f, af, wit.norm.coeff[i], i >= n);
      for (uint64_t x : wit.norm.D) f.push_back(x, Prm::kLimbBits, af);
      for (uint64_t x : wit.norm.D_carry) f.push_back(af.of_scalar(x));
      f.push_back(enc.slack, Prm::kSlackBits, af);
      apA = f.size();
      for (size_t c = 0; c < nch; ++c) fill_gf2k<MF, AF>(mf.zero(), f, af);
      check(f.size() == circA->ninputs, "A witness size");
    }
    return ms_since(t0);
  }

  NativeWorker() {
    const size_t n = falcon_baseline::kFalconN;
    const auto fp = falcon512();
    auto np = falcon_np(fp);
    check(np.B == Prm::kB, "limb base");
    check(np.La == Prm::kLa, "magnitude limbs");
    zetas = falcon_ntt_zetas(n, Q);
    auto hw = falcon_hash_to_point(inst.nonce, inst.msg, n);
    check(hw.n_accepts >= n, "HashToPoint accepts");
    std::vector<Sha3Witness::BlockWitness> shake_bws;
    Sha3Witness::compute_witness_shake256(inst.seed, 2 * hw.S, shake_bws);

    std::vector<uint64_t> cmod(n);
    for (size_t i = 0; i < n; ++i) cmod[i] = hw.c[i] % Q;
    std::vector<uint64_t> chat = cmod;
    falcon_ntt_ref(chat, zetas, Q);
    falcon_baseline_short_instance(chat, zetas, Q, inst.g, s2, hhat);
    rnp = falcon_norm_params(Q, np.B, 2 * n, fp.beta_sq);
    rnp.Wc = Prm::kWc;
    rnp.high_from = n;
    auto wit = falcon_build_witness(s2, hhat, chat, zetas, rnp);
    check(wit.norm.sum_leq_bound, "norm bound");
    const auto enc = falcon_encoding_advice(s2, Q, kFalcon512HighBudget);
    check(enc.encodable, "encodable");

    const size_t nch = Prm::kChunks;
    cref = crossing_chunks(mf, hw.c, n, nch, Prm::kBytes);

    // The witness satisfies the circuit and a zero norm bound rejects it.
    size_t N = 0;
    {
      using EB = EvaluationBackend<AF>;
      using ELC = Logic<AF, EB>;
      EB bk(af, false);
      ELC lc(&bk, af);
      auto W1 = [&](const std::vector<uint64_t>& v) {
        std::vector<typename ELC::EltW> w;
        for (uint64_t x : v) w.push_back(lc.konst(af.of_scalar(x)));
        return w;
      };
      std::vector<FalconCoeffWires<ELC>> cw(wit.norm.coeff.size());
      for (size_t i = 0; i < cw.size(); ++i) {
        const FalconCoeffAdvice& a = wit.norm.coeff[i];
        cw[i].a_lo = W1(a.a_lo);
        cw[i].sq = W1(a.sq);
        cw[i].S = W1(a.S);
        cw[i].add_carry = W1(a.add_carry);
        cw[i].col_carry.resize(a.col_carry.size());
        for (size_t m = 0; m < a.col_carry.size(); ++m)
          cw[i].col_carry[m] = W1(a.col_carry[m]);
      }
      auto hw2 = W1(hhat), ch = W1(chat), s2w0 = W1(s2), D = W1(wit.norm.D),
           Dc = W1(wit.norm.D_carry);
      std::vector<typename ELC::EltW> needles;
      falcon_verify_native(lc, hw2, ch, s2w0, cw, D, Dc, zetas, rnp, needles);
      falcon_encoding_native_bits(lc, cw, n, n,
                                  lc.konst(af.of_scalar(enc.slack)), rnp,
                                  kFalcon512HighBudget);
      check(!bk.assertion_failed(), "honest witness accepted");
      N = needles.size();
      auto bad_bound = rnp;
      bad_bound.beta_sq = 0;
      std::vector<typename ELC::EltW> rejected;
      falcon_verify_native(lc, hw2, ch, s2w0, cw, D, Dc, zetas, bad_bound,
                           rejected);
      check(bk.assertion_failed(), "zero bound rejected");
    }

    circE = build_h_circuit<HF, kW>(hf, inst.seed.size(), shake_bws.size(),
                                    hw.S, n, nch);

    // A circuit.
    {
      auto QA_owner = std::make_unique<QuadCircuit<AF>>(af);
      auto& QA = *QA_owner;
      const ACBK cbkA(&QA);
      const ALC lcA(&cbkA, af);
      std::vector<EA> h_hat(n);
      for (auto& x : h_hat) x = lcA.eltw_input();
      AvW avA;
      for (size_t i = 0; i < kW; ++i) avA[i] = lcA.input();
      std::vector<AvW> tgtA(nch);
      for (auto& t : tgtA)
        for (size_t i = 0; i < kW; ++i) t[i] = lcA.input();
      QA.private_input();
      std::vector<typename ALC::template bitvec<kCoefficientBits>> cA(n);
      for (auto& x : cA) x = lcA.template vinput<kCoefficientBits>();
      std::vector<EA> s2w(n);
      for (auto& x : s2w) x = lcA.eltw_input();
      std::vector<FalconCoeffWires<ALC>> cw(2 * n);
      for (size_t i = 0; i < 2 * n; ++i)
        cw[i] = decl_coeff<Prm>(lcA, rnp, i >= n);
      std::vector<EA> D(rnp.Ls), Dc(rnp.Ls);
      for (auto& x : D) x = falcon_limb_input<Prm::kLimbBits>(lcA);
      for (auto& x : Dc) x = lcA.eltw_input();
      EA slackA = falcon_limb_input<Prm::kSlackBits>(lcA);
      std::vector<AvW> apA(nch);
      for (auto& a : apA)
        for (size_t i = 0; i < kW; ++i) a[i] = lcA.input();
      QA.begin_full_field();
      {
        std::vector<EA> c_hat(n);
        for (size_t i = 0; i < n; ++i) {
          EA v = lcA.konst(uint64_t{0});
          uint64_t w = 1;
          for (size_t b = 0; b < kCoefficientBits; ++b) {
            v = lcA.axpy(v, af.of_scalar(w), lcA.eval(cA[i][b]));
            w = (2 * w) % Q;
          }
          c_hat[i] = v;
        }
        falcon_ntt(lcA, c_hat, zetas, Q);
        std::vector<EA> needles;
        falcon_verify_native(lcA, h_hat, c_hat, s2w, cw, D, Dc, zetas, rnp,
                             needles);
        falcon_encoding_native_bits(lcA, cw, n, n, slackA, rnp,
                                    kFalcon512HighBudget);
        check(needles.size() == N, "needle count");
        std::vector<AvW> chunks(nch);
        for (auto& ch : chunks)
          for (size_t i = 0; i < kW; ++i) ch[i] = lcA.bit(0);
        for (size_t j = 0; j < n; ++j)
          for (size_t b = 0; b < kCoefficientBits; ++b)
            chunks[(j * kCoefficientBits + b) / kW]
                  [(j * kCoefficientBits + b) % kW] = cA[j][b];
        falcon_mac_baseline<kW>(lcA, chunks, avA, apA, tgtA);
      }
      circA = QA.mkcircuit(1);
    }

    WE = std::make_unique<Dense<HF>>(1, circE->ninputs);
    WA = std::make_unique<Dense<AF>>(1, circA->ninputs);
    witness();
    proto.reset(new Protocol<HF, MF, AF, RSH, RSA, kW>{
        hf, mf, af, rsh, rsa, *circE, *circA, *WE, *WA, apH, apA, hhat, cref,
        Prm::kH, Prm::kA, "falcon_basen"});
    lfb::info({{"arm", "native"},
               {"profile", P::kId},
               {"a_field_degree", std::to_string(AF::kDegree)},
               {"h_ninputs", std::to_string(circE->ninputs)},
               {"h_nl", std::to_string(circE->nl)},
               {"a_ninputs", std::to_string(circA->ninputs)},
               {"a_nl", std::to_string(circA->nl)},
               {"needles", std::to_string(N)},
               {"chunks", std::to_string(nch)},
               {"h_ligero", std::to_string(Prm::kH.rate) + "/" +
                                std::to_string(Prm::kH.nreq) + "/" +
                                std::to_string(Prm::kH.block_enc)},
               {"a_ligero", std::to_string(Prm::kA.rate) + "/" +
                                std::to_string(Prm::kA.nreq) + "/" +
                                std::to_string(Prm::kA.block_enc)}});
  }
  lfb::Trial run() override {
    const double w = witness();
    lfb::Trial T = proto->run();
    T.add("witness", w);
    return T;
  }
};

template <class P>
struct EmulatedWorker : Worker {
  using Prm = falcon_baseline::FalconBaselineEmu<P>;
  static constexpr size_t kW = Prm::kW;
  using HF = typename Prm::HashField;
  using MF = typename Prm::MacField;
  using RSH = LCH14ReedSolomonFactory<HF>;
  using AF = typename Prm::Field;
  using ACBK = CompilerBackend<AF>;
  using ALC = Logic<AF, ACBK>;
  using AvW = typename ALC::template bitvec<kW>;
  using EA = typename ALC::EltW;
  using BaseRS = SubgroupReedSolomonFactory<Fp64G>;
  using RSA = typename GoldilocksRS<AF>::template type<BaseRS>;
  static constexpr size_t kLimb = Prm::kLimbBits;

  const HF hf;
  const MF mf;
  const AF af;
  const RSH rsh{hf};
  const BaseRS base_rs{goldilocks_root_2_32(), 32, goldilocks_base()};
  const RSA rsa{base_rs};
  std::unique_ptr<Circuit<HF>> circE;
  std::unique_ptr<Circuit<AF>> circA;
  std::unique_ptr<Dense<HF>> WE;
  std::unique_ptr<Dense<AF>> WA;
  std::vector<uint64_t> hhat;
  std::vector<typename MF::Elt> cref;
  std::unique_ptr<Protocol<HF, MF, AF, RSH, RSA, kW>> proto;
  // The instance (the signed message, its nonce, s2 and h) and the
  // witness's parameters, kept for the per-trial witness.
  Instance inst;
  std::vector<uint64_t> s2;
  FalconFpParams p{};
  size_t apH = 0, apA = 0;

  // The full witness from the instance: HashToPoint and its SHAKE256 block
  // witnesses, the reduction, norm and encoding advice, the crossing
  // chunks, and both fills (WE, WA; the MAC pads are drawn in the
  // protocol).  Returns its time (ms).
  double witness() {
    const auto t0 = std::chrono::steady_clock::now();
    const size_t n = falcon_baseline::kFalconN;
    const uint64_t B = Prm::kB;
    auto hw = falcon_hash_to_point(inst.nonce, inst.msg, n);
    check(hw.n_accepts >= n, "HashToPoint accepts");
    std::vector<Sha3Witness::BlockWitness> shake_bws;
    Sha3Witness::compute_witness_shake256(inst.seed, 2 * hw.S, shake_bws);
    std::vector<uint64_t> c(hw.c.begin(), hw.c.begin() + n);
    auto awit = falcon_fp_build_witness(af, s2, hhat, c, p,
                                        FalconChallengeForm::Coefficients);
    check(awit.norm_leq, "norm bound");
    const auto enc = falcon_encoding_advice(s2, Q, kFalcon512HighBudget);
    check(enc.encodable, "encodable");
    const size_t nch = Prm::kChunks;
    cref = crossing_chunks(mf, hw.c, n, nch, Prm::kBytes);
    apH = fill_h_witness(*WE, hf, mf, inst.seed, shake_bws, hw, n, nch);
    auto fill_red = [&](DenseFiller<AF>& f, const FalconReduceAdvice& a) {
      for (uint64_t x : a.r_lo) f.push_back(x, kLimb, af);
      for (uint64_t x : a.r_hi) f.push_back(x, kLimb, af);
      for (uint64_t x : a.Q_lo) f.push_back(x, kLimb, af);
    };
    {
      DenseFiller<AF> f(*WA);
      f.push_back(af.one());
      for (size_t i = 0; i < n; ++i) f.push_back(af.of_scalar(hhat[i]));
      fill_gf2k<MF, AF>(mf.zero(), f, af);
      for (size_t c2 = 0; c2 < nch; ++c2) fill_gf2k<MF, AF>(mf.zero(), f, af);
      for (size_t j = 0; j < n; ++j)
        f.push_back((uint64_t)hw.c[j], kCoefficientBits, af);
      for (size_t i = 0; i < n; ++i) f.push_back(af.of_scalar(s2[i]));
      for (auto& row : awit.fwd_rw)
        for (size_t i = 0; i < n; ++i) fill_red(f, row[i]);
      for (size_t i = 0; i < n; ++i) fill_red(f, awit.pw_rw[i]);
      for (auto& row : awit.inv_rw)
        for (size_t i = 0; i < n; ++i) fill_red(f, row[i]);
      for (const auto& r : awit.coeff_rw) fill_red(f, r);
      for (size_t i = 0; i < 2 * n; ++i) {
        uint64_t a = 0;
        for (size_t j = awit.a_lo[i].size(); j-- > 0;) a = a * B + awit.a_lo[i][j];
        f.push_back(a, kMagBits, af);
      }
      f.push_back(awit.norm, kNormBits, af);
      f.push_back(enc.slack, Prm::kSlackBits, af);
      apA = f.size();
      for (size_t c2 = 0; c2 < nch; ++c2) fill_gf2k<MF, AF>(mf.zero(), f, af);
      check(f.size() == circA->ninputs, "A witness size");
    }
    return ms_since(t0);
  }

  EmulatedWorker() {
    const size_t n = falcon_baseline::kFalconN;
    const uint64_t B = Prm::kB;
    const size_t La_r = Prm::kLa_r, La_Q = Prm::kLa_Q;
    check_integer_identity<AF>(
        std::log2((double)Q) + La_Q * std::log2((double)B),
        "lazy reduction exceeds the field");
    auto zetas = falcon_ntt_zetas(n, Q);
    auto hw = falcon_hash_to_point(inst.nonce, inst.msg, n);
    check(hw.n_accepts >= n, "HashToPoint accepts");
    std::vector<Sha3Witness::BlockWitness> shake_bws;
    Sha3Witness::compute_witness_shake256(inst.seed, 2 * hw.S, shake_bws);

    p = FalconFpParams{n,
                       Q,
                       falcon_baseline::kFalconBetaSq,
                       B,
                       La_r,
                       La_Q,
                       Prm::kLa_a,
                       Prm::kLa_sum,
                       Prm::kLazyBits,
                       Prm::kLazyMargin};
    std::vector<uint64_t> c(hw.c.begin(), hw.c.begin() + n);
    auto chat = c;
    for (auto& x : chat) x %= Q;
    falcon_ntt_ref(chat, zetas, Q);
    falcon_baseline_short_instance(chat, zetas, Q, inst.g, s2, hhat);
    auto awit = falcon_fp_build_witness(af, s2, hhat, c, p,
                                        FalconChallengeForm::Coefficients);
    check(awit.norm_leq, "norm bound");
    const auto enc = falcon_encoding_advice(s2, Q, kFalcon512HighBudget);
    check(enc.encodable, "encodable");

    const size_t nch = Prm::kChunks;
    cref = crossing_chunks(mf, hw.c, n, nch, Prm::kBytes);

    // The witness satisfies the circuit and a zero norm bound rejects it.
    size_t N = 0;
    {
      using EB = EvaluationBackend<AF>;
      using ELC = Logic<AF, EB>;
      EB bk(af, false);
      ELC lc(&bk, af);
      auto W1 = [&](const std::vector<uint64_t>& v) {
        std::vector<typename ELC::EltW> w;
        for (uint64_t x : v) w.push_back(lc.konst(af.of_scalar(x)));
        return w;
      };
      auto mkred = [&](const FalconReduceAdvice& a) {
        FalconReduceWires<ELC> r;
        r.r_lo = W1(a.r_lo);
        r.r_hi = W1(a.r_hi);
        r.Q_lo = W1(a.Q_lo);
        return r;
      };
      FalconFpWires<ELC> w;
      w.fwd_rw.resize(awit.fwd_rw.size());
      for (size_t s = 0; s < awit.fwd_rw.size(); ++s) {
        w.fwd_rw[s].resize(n);
        for (size_t i = 0; i < n; ++i) w.fwd_rw[s][i] = mkred(awit.fwd_rw[s][i]);
      }
      w.inv_rw.resize(awit.inv_rw.size());
      for (size_t s = 0; s < awit.inv_rw.size(); ++s) {
        w.inv_rw[s].resize(n);
        for (size_t i = 0; i < n; ++i) w.inv_rw[s][i] = mkred(awit.inv_rw[s][i]);
      }
      w.pw_rw.resize(n);
      for (size_t i = 0; i < n; ++i) w.pw_rw[i] = mkred(awit.pw_rw[i]);
      w.coeff_rw.resize(n);
      for (size_t i = 0; i < n; ++i) w.coeff_rw[i] = mkred(awit.coeff_rw[i]);
      std::vector<typename ELC::template bitvec<kMagBits>> magnitudes(2 * n);
      for (size_t i = 0; i < 2 * n; ++i) {
        uint64_t a = 0;
        for (size_t j = awit.a_lo[i].size(); j-- > 0;) a = a * B + awit.a_lo[i][j];
        magnitudes[i] = lc.template vbit<kMagBits>(a);
      }
      auto total = lc.template vbit<kNormBits>(awit.norm);
      std::vector<typename ELC::EltW> needles;
      auto hw2 = W1(hhat), s2w0 = W1(s2), cw = W1(c);
      auto coeffs = falcon_verify_fp_coefficients(
          lc, hw2, cw, s2w0, w, p, needles, FalconChallengeForm::Coefficients);
      assert_binary_norm(lc, coeffs, magnitudes, total, p.beta_sq);
      std::vector<typename ELC::template bitvec<kMagBits>> s2mags(
          magnitudes.begin() + n, magnitudes.end());
      falcon_encoding_emulated_bits(lc, s2mags,
                                    lc.konst(af.of_scalar(enc.slack)),
                                    kFalcon512HighBudget);
      check(!bk.assertion_failed(), "honest witness accepted");
      N = needles.size();
      assert_binary_norm(lc, coeffs, magnitudes, total, 0);
      check(bk.assertion_failed(), "zero bound rejected");
    }

    circE = build_h_circuit<HF, kW>(hf, inst.seed.size(), shake_bws.size(),
                                    hw.S, n, nch);

    // A circuit.
    {
      auto QA_owner = std::make_unique<QuadCircuit<AF>>(af);
      auto& QA = *QA_owner;
      const ACBK cbkA(&QA);
      const ALC lcA(&cbkA, af);
      std::vector<EA> h_hat(n);
      for (auto& x : h_hat) x = lcA.eltw_input();
      AvW avA;
      for (size_t i = 0; i < kW; ++i) avA[i] = lcA.input();
      std::vector<AvW> tgtA(nch);
      for (auto& t : tgtA)
        for (size_t i = 0; i < kW; ++i) t[i] = lcA.input();
      QA.private_input();
      std::vector<typename ALC::v16> cA(n);
      for (auto& x : cA) x = lcA.template vinput<kCoefficientBits>();
      std::vector<EA> s2w(n);
      for (auto& x : s2w) x = lcA.eltw_input();
      auto decl_red = [&]() {
        FalconReduceWires<ALC> r;
        r.r_lo.resize(La_r);
        for (auto& x : r.r_lo) x = falcon_limb_input<kLimb>(lcA);
        r.r_hi.resize(La_r);
        for (auto& x : r.r_hi) x = falcon_limb_input<kLimb>(lcA);
        r.Q_lo.resize(La_Q);
        for (auto& x : r.Q_lo) x = falcon_limb_input<kLimb>(lcA);
        return r;
      };
      FalconFpWires<ALC> vw;
      vw.fwd_rw.resize(awit.fwd_rw.size());
      for (auto& row : vw.fwd_rw) {
        row.resize(n);
        for (auto& x : row) x = decl_red();
      }
      vw.pw_rw.resize(n);
      for (auto& x : vw.pw_rw) x = decl_red();
      vw.inv_rw.resize(awit.inv_rw.size());
      for (auto& row : vw.inv_rw) {
        row.resize(n);
        for (auto& x : row) x = decl_red();
      }
      vw.coeff_rw.resize(n);
      for (auto& x : vw.coeff_rw) x = decl_red();
      std::vector<typename ALC::template bitvec<kMagBits>> magnitudes(2 * n);
      for (auto& a : magnitudes) a = lcA.template vinput<kMagBits>();
      auto total = lcA.template vinput<kNormBits>();
      EA slackA = falcon_limb_input<Prm::kSlackBits>(lcA);
      std::vector<AvW> apA(nch);
      for (auto& a : apA)
        for (size_t i = 0; i < kW; ++i) a[i] = lcA.input();
      QA.begin_full_field();
      {
        std::vector<EA> c_coeff(n);
        for (size_t i = 0; i < n; ++i) c_coeff[i] = lcA.as_scalar(cA[i]);
        std::vector<EA> needles;
        auto coeffs = falcon_verify_fp_coefficients(
            lcA, h_hat, c_coeff, s2w, vw, p, needles,
            FalconChallengeForm::Coefficients);
        assert_binary_norm(lcA, coeffs, magnitudes, total, p.beta_sq);
        std::vector<typename ALC::template bitvec<kMagBits>> s2mags(
            magnitudes.begin() + n, magnitudes.end());
        falcon_encoding_emulated_bits(lcA, s2mags, slackA,
                                      kFalcon512HighBudget);
        check(needles.size() == N, "needle count");
        std::vector<AvW> chunks(nch);
        for (auto& ch : chunks)
          for (size_t i = 0; i < kW; ++i) ch[i] = lcA.bit(0);
        for (size_t j = 0; j < n; ++j)
          for (size_t b = 0; b < kCoefficientBits; ++b)
            chunks[(j * kCoefficientBits + b) / kW]
                  [(j * kCoefficientBits + b) % kW] = cA[j][b];
        falcon_mac_baseline<kW>(lcA, chunks, avA, apA, tgtA);
      }
      circA = QA.mkcircuit(1);
    }

    WE = std::make_unique<Dense<HF>>(1, circE->ninputs);
    WA = std::make_unique<Dense<AF>>(1, circA->ninputs);
    witness();
    proto.reset(new Protocol<HF, MF, AF, RSH, RSA, kW>{
        hf, mf, af, rsh, rsa, *circE, *circA, *WE, *WA, apH, apA, hhat, cref,
        Prm::kH, Prm::kA, "falcon_base"});
    lfb::info({{"arm", "emulated"},
               {"profile", P::kId},
               {"h_ninputs", std::to_string(circE->ninputs)},
               {"h_nl", std::to_string(circE->nl)},
               {"a_ninputs", std::to_string(circA->ninputs)},
               {"a_nl", std::to_string(circA->nl)},
               {"needles", std::to_string(N)},
               {"chunks", std::to_string(nch)},
               {"h_ligero", std::to_string(Prm::kH.rate) + "/" +
                                std::to_string(Prm::kH.nreq) + "/" +
                                std::to_string(Prm::kH.block_enc)},
               {"a_ligero", std::to_string(Prm::kA.rate) + "/" +
                                std::to_string(Prm::kA.nreq) + "/" +
                                std::to_string(Prm::kA.block_enc)}});
  }
  lfb::Trial run() override {
    const double w = witness();
    lfb::Trial T = proto->run();
    T.add("witness", w);
    return T;
  }
};

}  // namespace
}  // namespace proofs

// The narrow executable (falcon_split_driver) serves the narrow profile; the
// wide one (falcon_split_driver_wide, built with baselines/common-wide's hash
// domain) the wide profile.
#if LFB_WIDE_HASH_DOMAIN
using Profile = proofs::falcon_baseline::Wide;
#else
using Profile = proofs::falcon_baseline::Narrow;
#endif

int main(int argc, char** argv) {
  using namespace proofs;
  if (argc != 3 || std::string(argv[2]) != Profile::kId) {
    std::fprintf(stderr, "usage: %s native|emulated %s\n", argv[0],
                 Profile::kId);
    return 2;
  }
  set_log_level(ERROR);
  const std::string arm = argv[1];
  std::unique_ptr<Worker> w;
  if (arm == "native") {
    w = std::make_unique<NativeWorker<Profile>>();
  } else if (arm == "emulated") {
    w = std::make_unique<EmulatedWorker<Profile>>();
  } else {
    std::fprintf(stderr, "unknown arm\n");
    return 2;
  }
  lfb::serve([&]() { return w->run(); });
  return 0;
}
