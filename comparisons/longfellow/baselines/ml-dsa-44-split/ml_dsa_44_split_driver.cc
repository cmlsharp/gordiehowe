// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA proof of possession (ML-DSA-44, -65 or -87), Longfellow-style field
// split: a worker of common/bench.py.
//
// usage: ml_dsa_44_split_driver narrow on|off [MODE] [--param-set SET]
//        ml_dsa_44_split_driver_wide wide on|off [MODE] [--param-set SET]
//
// SET is ml-dsa-44 (the default), ml-dsa-65 or ml-dsa-87 (ml_dsa_sets.h);
// the flag may stand anywhere among the arguments.  The instance is the
// set's benchmark example (ml_dsa_benchmark_example.h).
//
// MODE (optional) runs one trial or check and exits 0 on the expected
// outcome, 1 otherwise:
//   test          three trials: the honest instance must verify, and the
//                 tampered signature and the tampered message (below) must
//                 be rejected;
//   tamper_sig    the instance's signature with the lowest bit of its first
//                 z coefficient flipped, the whole witness recomputed from
//                 it: rejected;
//   tamper_msg    the committed message differs from the signed one in one
//                 bit, the whole witness (mu, c_tilde') recomputed from it:
//                 rejected;
//   tamper        one coefficient of z changed in A's witness only:
//                 rejected;
//   tamper_tag    the first chunk's target changed in H's statement only
//                 (prover and verifier): H rejects;
//   tamper_blind  the first chunk's blind a_p changed in H's witness only:
//                 H rejects;
//   tamper_chunk  one bit of w1_tilde changed in H's witness only (the
//                 first crossing chunk): H rejects;
//   (A's result is printed but not checked: when H's circuit is
//   unsatisfied, ZkProver::prove returns before writing H's proof to the
//   shared transcript, so A's transcript diverges and A rejects too.)
//   check_tags    no proof: A's emulated tag, H's native tag and the host's
//                 agree bit for bit on every honest chunk and on random
//                 chunks, for random a_v and a_p.
//   The tamper_tag, tamper_blind and tamper_chunk modes need macs=on.
//
// One source, two targets: the narrow target is built on upstream alone; the
// wide one (LFB_WIDE_HASH_DOMAIN) additionally sees baselines/common-wide's
// hash domain (GF(2^256), the SHA-384 Merkle tree, Ligero and transcript).
//
// The statement, GordieHowe's proof of possession's: the prover knows a
// message M of private length L <= 32 bytes and an ML-DSA signature on M,
// valid under the public key pk under the public (empty) context.  The
// verifier's public inputs are computed from pk's bytes in verify_ms
// (ml_dsa_host.h's Statement: pkDecode, ExpandA, NTT(2^d t1),
// tr = SHAKE256(pk, 64)).  Two proofs, mdoc-style, on one transcript:
//  - A: the ML-DSA arithmetic over the profile's ML-DSA field (narrow:
//    upstream's GF(q^6); wide: GF(q^11)), MLDSASplitVerify: z's norm, A z -
//    c t1 2^d in the NTT domain, UseHint (with the exact Decompose of
//    ml_dsa_decompose_exact.h), the hint's weight, the w1 encoding.
//  - H: the hashing over the profile's binary field (narrow: upstream's
//    GF(2^128); wide: GF(2^256)), MLDSAHashVerify:
//    mu = SHAKE256(tr || 0 || |ctx| || ctx || M) for M of private length
//    (ml_dsa_mu.h), SampleInBall over the 272-byte stream,
//    c_tilde = SHAKE256(mu || w1_tilde).
// The crossings (w1_tilde, and the (support, sign) bits of the challenge c)
// are cut into w-bit chunks (w = 128 narrow, 256 wide); each chunk carries
// its own affine MAC mac_c = a_v * X_c + a_p[c] over GF(2^w).  A computes
// it bit by bit, emulating GF(2^w) (upstream's Logic::gf2_128_mul; wide,
// common-wide's gf2_256_mul), with a_v, a_p[c] and mac_c as w bits each.  H,
// whose field is GF(2^w), packs X_c into one field element and computes the
// tag with one native multiplication and one addition, with a_v, a_p[c] and
// mac_c as one field element each, as upstream mdoc's MACGF2
// (circuits/mac/mac_circuit.h).  a_v is squeezed after both commitments,
// a_p[c] is a committed blind in each proof, and the targets mac_c are
// revealed as public inputs of both.  With macs=off (the MAC
// ablation, a measurement control, unsound by design) both circuits omit
// the key, the targets, the blinds and the MAC products and checks; the
// crossing bits stay committed and constrained.
//
// The protocol flow is upstream mdoc's (run_mdoc_prover): commit H, commit
// A, squeeze the MAC key, fill the targets into both witnesses, prove H,
// prove A; the targets reach the transcript as public inputs of the proofs
// (ZkProver::prove absorbs them).
//
// Per trial (details: A and H separately):
//   witness   = the full witness from the instance (pk, signature, message,
//               context): ml_dsa_host.h's HostWitness (pk and signature
//               decoding, ExpandA, tr, SampleInBall, the NTTs, w1, mu's and
//               c_tilde's block witnesses), the crossing chunks and both
//               fills (a detail, outside commit_ms and prove_ms)
//   commit_ms = the MAC blinds + H commit + A commit
//   prove_ms  = MAC key and targets + H prove + A prove
//   verify_ms = the statement from pk's bytes, both Reed-Solomon
//               factories' use and ZkVerifier construction, both
//               commitments, the key, the public inputs and both
//               ZkVerifier::verify calls
// The verifier reads both proofs back from their bytes first (the detail
// v_proof_read, outside verify_ms, as the monolith's).  The circuits are
// built once, before PQ_READY; each trial recomputes the witness and draws
// fresh blinds and proof randomness.  prover_setup (the ZkProof and
// ZkProver construction) is a detail outside every total.
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <string>
#include <type_traits>
#include <vector>

#include "arrays/dense.h"
#include "bench_worker.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/mac/mac_reference.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "gf2k/lch14_reed_solomon.h"
#include "ml_dsa_benchmark_example.h"
#include "ml_dsa_decompose_exact.h"
#include "ml_dsa_host.h"
#include "ml_dsa_mu.h"
#include "ml_dsa_sets.h"
#include "ml_dsa_split_bind.h"
#include "ml_dsa_split_circuit.h"
#include "ml_dsa_split_hash_circuit.h"
#include "ml_dsa_split_profile.h"
#if LFB_WIDE_HASH_DOMAIN
#include "ml_dsa_split_bind_256.h"
#include "ml_dsa_split_profile_wide.h"
#endif
#include "ml_dsa_split_tag_check.h"
#include "ml_dsa_split_witness.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/readbuffer.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

namespace proofs {
namespace {
using namespace ml_dsa_baseline;  // NOLINT(build/namespaces)
using ml_dsa_split::LigeroHalf;

const uint8_t kTranscriptInit[] = "mldsa_split";
constexpr size_t kTranscriptInitLen = 11;

// W-bit chunks from a byte-array bit witness (W/8 bytes per chunk).
template <size_t W, class LC, size_t N>
std::vector<typename LC::template bitvec<W>> w1_chunks(
    const std::array<typename LC::v8, N>& w1t) {
  constexpr size_t kBytes = W / 8;
  static_assert(N % kBytes == 0, "w1_tilde must fill whole chunks");
  std::vector<typename LC::template bitvec<W>> chunks(N / kBytes);
  for (size_t c = 0; c < N / kBytes; ++c)
    for (size_t b = 0; b < kBytes; ++b)
      for (size_t j = 0; j < 8; ++j) chunks[c][b * 8 + j] = w1t[kBytes * c + b][j];
  return chunks;
}

// The first 8 bytes of a circuit's id, in hex.
std::string id_hex(const uint8_t id[/*32*/]) {
  char buf[17];
  for (size_t i = 0; i < 8; ++i) std::snprintf(buf + 2 * i, 3, "%02x", id[i]);
  return std::string(buf, 16);
}

template <class F>
std::unique_ptr<ZkProof<F>> make_proof(const Circuit<F>& c, LigeroHalf l) {
  if (l.block_enc == 0) {
    return std::make_unique<ZkProof<F>>(c, l.rate, l.nreq);
  }
  return std::make_unique<ZkProof<F>>(c, l.rate, l.nreq, l.block_enc);
}

template <class F, class RSF>
std::unique_ptr<ZkVerifier<F, RSF>> make_verifier(const Circuit<F>& c,
                                                  const RSF& rsf, LigeroHalf l,
                                                  const F& f) {
  if (l.block_enc == 0) {
    return std::make_unique<ZkVerifier<F, RSF>>(c, rsf, l.rate, l.nreq, f);
  }
  return std::make_unique<ZkVerifier<F, RSF>>(c, rsf, l.rate, l.nreq,
                                              l.block_enc, f);
}

enum class Mode { kServe, kTest, kTamperSig, kTamperMsg, kTamperZ, kTamperTag,
                  kTamperBlind, kTamperChunk, kCheckTags };

// The instance a trial proves: the benchmark example, or a tampered copy.
struct Instance {
  std::vector<uint8_t> pk, sig, msg, ctx;
};

template <class P, class Set>
int run(bool macs, Mode mode) {
  using S = ml_dsa_split::Split<P, typename Set::Reference>;
  using Params = typename S::Params;
  constexpr size_t kW = S::kW, kWBytes = S::kWBytes;
  using Field6 = typename P::AField;
  using CBK6 = CompilerBackend<Field6>;
  using LC6 = Logic<Field6, CBK6>;
  using RSExt = typename P::RSA;
  using HF = typename P::HashField;
  using HCBK = CompilerBackend<HF>;
  using HLC = Logic<HF, HCBK>;
  using RSH = LCH14ReedSolomonFactory<HF>;
  using MF = typename P::MacField;
  using MElt = typename MF::Elt;
  using WordA = typename LC6::template bitvec<kW>;
  using EltWH = typename HLC::EltW;
  using HostWitness = ml_dsa_host::HostWitness<Params>;
  using Statement = ml_dsa_host::Statement<Params>;
  static_assert(std::is_same_v<HF, MF>, "H's field is the MAC field");
  const LigeroHalf kLigeroA = P::kLigeroA, kLigeroH = P::kLigeroH;
  constexpr size_t kMax = ml_dsa_host::kMaxMessageBytes;

  set_log_level(ERROR);
  const auto& ex = ml_dsa_sets::benchmark_example<Set>();
  const Instance honest{ex.pkey, ex.sig, ex.msg, ex.ctx};
  Instance inst = honest;
  const MF mf;
  // The host witness from the instance (pk, signature, message, context):
  // ml_dsa_host.h's HostWitness and the crossing chunks (host): w1_tilde ++
  // (support, sign) bits of c.  Computed once here for the circuits' shapes
  // and again in every trial, timed as the witness (with the fills of WA
  // and WH below).
  std::unique_ptr<HostWitness> wgp;
  bool inst_verified = false;
  std::vector<MElt> chunks_ref;
  std::vector<uint8_t> c_support(ml_dsa::N), c_sign(ml_dsa::N);
  auto host_witness = [&]() {
    wgp = std::make_unique<HostWitness>();
    auto& wg = *wgp;
    check(wg.compute(inst.pk, inst.sig, inst.msg, inst.ctx, &inst_verified),
          "witness");
    chunks_ref.clear();
    for (size_t c = 0; c * kWBytes < wg.w1_tilde_.size(); ++c)
      chunks_ref.push_back(
          mf.of_bytes_field(&wg.w1_tilde_[c * kWBytes]).value());
    uint8_t buf[S::kCBits / 8] = {0};
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      uint64_t val = wg.f_.from_montgomery(wg.c_coeffs_[k]).limb_[0];
      c_support[k] = (val != 0);
      c_sign[k] = (val == ml_dsa::Q - 1);
      if (c_support[k]) buf[(2 * k) / 8] |= 1u << ((2 * k) % 8);
      if (c_sign[k]) buf[(2 * k + 1) / 8] |= 1u << ((2 * k + 1) % 8);
    }
    for (size_t c = 0; c * kWBytes < sizeof(buf); ++c)
      chunks_ref.push_back(mf.of_bytes_field(&buf[c * kWBytes]).value());
  };
  host_witness();
  check(inst_verified, "the benchmark example verifies");

  SecureRandomEngine rng;
  const size_t nch = chunks_ref.size();
  check(nch == S::kChunks, "ML-DSA crossing chunk count");
  const size_t nmac = macs ? nch : 0;
  const size_t kKey = macs ? kW : 0;

  // ---------------- A: the ML-DSA arithmetic ----------------
  const typename P::Fields fields;
  const Field6& f6 = fields.a;
  using VA = MLDSASplitVerify<LC6, Field6, Params>;
  auto QA_owner = std::make_unique<QuadCircuit<Field6>>(f6);
  auto& QA = *QA_owner;
  const CBK6 cbkA(&QA);
  const LC6 lcA(&cbkA, f6);
  VA verifyA(lcA);
  auto pk = std::make_unique<typename VA::Pk>();
  pk->input(lcA);
  WordA avA;
  for (size_t i = 0; i < kKey; ++i) avA[i] = lcA.input();
  std::vector<WordA> tgtA(nmac);
  for (size_t c = 0; c < nmac; ++c)
    for (size_t i = 0; i < kW; ++i) tgtA[c][i] = lcA.input();
  QA.private_input();
  auto sg = std::make_unique<typename VA::SignatureW>();
  sg->input(lcA);
  auto wA = std::make_unique<typename VA::Witness>();
  wA->input(lcA);
  std::vector<WordA> apA(nmac);
  for (size_t c = 0; c < nmac; ++c)
    for (size_t i = 0; i < kW; ++i) apA[c][i] = lcA.input();
  verifyA.assert_valid_signature_split(*pk, *sg, *wA);
  assert_decompose_exact<Params>(lcA, wA->hint_aux_bits_, wA->w1_);
  {
    auto chunks = w1_chunks<kW, LC6>(wA->w1_tilde_);
    // c from committed advice (support_k, sign_k), tied to wA->c_.
    std::vector<WordA> cch(S::kCChunks);
    for (auto& ch : cch)
      for (size_t i = 0; i < kW; ++i) ch[i] = lcA.bit(0);
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      auto support = lcA.input();
      auto signk = lcA.input();
      typename LC6::EltW sup = lcA.eval(support), sgn = lcA.eval(signk);
      typename LC6::EltW ck =
          lcA.sub(sup, lcA.mul(f6.of_scalar(2), lcA.mul(sup, sgn)));
      lcA.assert_eq(wA->c_.coeffs[k], ck);
      cch[(2 * k) / kW][(2 * k) % kW] = support;
      cch[(2 * k + 1) / kW][(2 * k + 1) % kW] = signk;
    }
    chunks.insert(chunks.end(), cch.begin(), cch.end());
    for (size_t c = 0; c < nmac; ++c) {
      std::vector<WordA> one(1, chunks[c]), coef(1, avA);
      lcA.vassert_eq(affine_mac(lcA, one, coef, apA[c]), tgtA[c]);
    }
  }
  QA.begin_full_field();
  auto circA = QA.mkcircuit(1);
  const size_t a_nwires = QA.nwires_;
  QA_owner.reset();

  size_t apA_offset = 0, apH_offset = 0;
  Dense<Field6> WA(1, circA->ninputs);
  auto fill_A = [&](bool tamper_z) {
    const auto& wg = *wgp;
    DenseFiller<Field6> fA(WA);
    fA.push_back(f6.one());
    wg.fill_pk(fA, f6);
    for (size_t i = 0; i < kKey + nmac * kW; ++i) fA.push_back(f6.zero());
    fill_split_A_priv(fA, wg, f6);
    apA_offset = fA.size();
    for (size_t c = 0; c < nmac * kW; ++c) fA.push_back(f6.zero());
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      fA.push_back(c_support[k] ? f6.one() : f6.zero());
      fA.push_back(c_sign[k] ? f6.one() : f6.zero());
    }
    check(fA.size() == circA->ninputs, "A witness size");
    if (tamper_z) {
      // One coefficient of z: the proof must fail.
      WA.v_[circA->npub_in + Params::c_tilde_bytes * 8] = f6.of_scalar(12345);
    }
  };
  fill_A(false);

  // ---------------- H: the hashing ----------------
  const HF hf;
  using VH = MLDSAHashVerify<HLC, HF, Params, kW, ml_dsa_host::kSibBytes>;
  auto QH_owner = std::make_unique<QuadCircuit<HF>>(hf);
  auto& QH = *QH_owner;
  const HCBK cbkH(&QH);
  const HLC lcH(&cbkH, hf);
  VH verifyH(lcH);
  // The MAC key and the targets, one GF(2^w) element each.
  const size_t kKeyH = macs ? 1 : 0;
  EltWH avH{};
  if (macs) avH = lcH.eltw_input();
  std::vector<EltWH> tgtH(nmac);
  for (auto& t : tgtH) t = lcH.eltw_input();
  std::array<typename HLC::v8, 64> trH;
  for (auto& byte : trH) byte = lcH.template vinput<8>();
  std::vector<typename HLC::v8> ctxH(ex.ctx.size());
  for (auto& byte : ctxH) byte = lcH.template vinput<8>();
  QH.private_input();
  std::array<typename HLC::v8, Params::c_tilde_bytes> ct;
  for (size_t i = 0; i < Params::c_tilde_bytes; ++i)
    ct[i] = lcH.template vinput<8>();
  // The message: kMax bytes and their in-message flags [i < L].
  std::vector<typename HLC::v8> msgH(kMax);
  for (auto& byte : msgH) byte = lcH.template vinput<8>();
  std::vector<typename HLC::BitW> flagsH(kMax);
  for (auto& flag : flagsH) flag = lcH.input();
  typename VH::HashWitness wH;
  wH.c_prime_tilde_bws_.resize(Set::kCPrimeTildeBlocks);
  wH.input(lcH);
  std::vector<typename Sha3Circuit<HLC>::BlockWitness> mu_bwsH(
      lfb::shake256_private_length_blocks(ml_dsa_host::kMuPrefixBytes, kMax,
                                          64));
  for (auto& bw : mu_bwsH) bw.input(lcH);
  // The blinds, one full-field element each, after every subfield input.
  QH.begin_full_field();
  std::vector<EltWH> apH(nmac);
  for (auto& a : apH) a = lcH.eltw_input();
  const auto mu = ml_dsa_derive_mu(lcH, trH, ctxH, msgH, flagsH, mu_bwsH);
  auto cchH = verifyH.assert_hash_side(ct, mu, wH);
  {
    auto chunks = w1_chunks<kW, HLC>(wH.w1_tilde_);
    chunks.insert(chunks.end(), cchH.begin(), cchH.end());
    for (size_t c = 0; c < nmac; ++c) {
      lcH.assert_eq(affine_mac_native<HLC, kW>(lcH, chunks[c], avH, apH[c]),
                    tgtH[c]);
    }
  }
  auto circH = QH.mkcircuit(1);
  const size_t h_nwires = QH.nwires_;
  QH_owner.reset();

  Dense<HF> WH(1, circH->ninputs);
  auto fill_H = [&](bool tamper_chunk) {
    auto& wg = *wgp;
    DenseFiller<HF> fH(WH);
    fH.push_back(hf.one());
    for (size_t i = 0; i < kKeyH + nmac; ++i) fH.push_back(hf.zero());
    for (uint8_t byte : wg.tr_) fH.push_back(byte, 8, hf);
    for (uint8_t byte : inst.ctx) fH.push_back(byte, 8, hf);
    if (tamper_chunk) {
      // One crossing bit of H's witness only (w1_tilde, the first chunk).
      wg.w1_tilde_[0] ^= 1;
      fill_split_H<Params>(fH, wg, hf);
      wg.w1_tilde_[0] ^= 1;
    } else {
      fill_split_H<Params>(fH, wg, hf);
    }
    apH_offset = fH.size();
    for (size_t c = 0; c < nmac; ++c) fH.push_back(hf.zero());
    check(fH.size() == circH->ninputs, "H witness size");
  };
  fill_H(false);

  const RSExt& rsextf = fields.rsa;
  const RSH rsfH(hf);
  const size_t pkN =
      Params::K * Params::L * ml_dsa::N + Params::K * ml_dsa::N + 64 * 8;

  {
    auto pa = make_proof(*circA, kLigeroA);
    auto ph = make_proof(*circH, kLigeroH);
    ::lfb::info({{"param_set", Set::kName},
                 {"profile", P::kName},
                 {"macs", macs ? "on" : "off"},
                 {"chunks", std::to_string(nmac)},
                 {"A_ninputs", std::to_string(circA->ninputs)},
                 {"A_npub", std::to_string(circA->npub_in)},
                 {"A_nl", std::to_string(circA->nl)},
                 {"A_nwires", std::to_string(a_nwires)},
                 {"A_nterms", std::to_string(circA->nterms())},
                 {"A_id", id_hex(circA->id)},
                 {"H_ninputs", std::to_string(circH->ninputs)},
                 {"H_npub", std::to_string(circH->npub_in)},
                 {"H_nl", std::to_string(circH->nl)},
                 {"H_nwires", std::to_string(h_nwires)},
                 {"H_nterms", std::to_string(circH->nterms())},
                 {"H_id", id_hex(circH->id)},
                 {"A_rate", std::to_string(kLigeroA.rate)},
                 {"A_nreq", std::to_string(pa->param.nreq)},
                 {"A_block", std::to_string(pa->param.block)},
                 {"A_block_enc", std::to_string(pa->param.block_enc)},
                 {"A_nrow", std::to_string(pa->param.nrow)},
                 {"H_rate", std::to_string(kLigeroH.rate)},
                 {"H_nreq", std::to_string(ph->param.nreq)},
                 {"H_block", std::to_string(ph->param.block)},
                 {"H_block_enc", std::to_string(ph->param.block_enc)},
                 {"H_nrow", std::to_string(ph->param.nrow)}});
  }

  if (mode == Mode::kCheckTags) {
    // The circuits' chunk words: w1_tilde byte b bit j at 8b + j, then the
    // (support, sign) bit of challenge coefficient k at 2k and 2k + 1.
    std::vector<std::array<uint8_t, kW>> words;
    const auto& w1t = wgp->w1_tilde_;
    for (size_t c = 0; c * kWBytes < w1t.size(); ++c) {
      std::array<uint8_t, kW> x{};
      for (size_t b = 0; b < kWBytes; ++b)
        for (size_t j = 0; j < 8; ++j)
          x[8 * b + j] = (w1t[kWBytes * c + b] >> j) & 1;
      words.push_back(x);
    }
    std::vector<std::array<uint8_t, kW>> cw(S::kCChunks);
    for (auto& x : cw) x.fill(0);
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      cw[(2 * k) / kW][(2 * k) % kW] = c_support[k];
      cw[(2 * k + 1) / kW][(2 * k + 1) % kW] = c_sign[k];
    }
    words.insert(words.end(), cw.begin(), cw.end());
    std::vector<MElt> xs = chunks_ref;
    // Random chunks as well, every bit position exercised.
    for (size_t r = 0; r < 64; ++r) {
      const MElt e = rng.elt(mf);
      std::array<uint8_t, kW> x{};
      for (size_t i = 0; i < kW; ++i) x[i] = e[i];
      words.push_back(x);
      xs.push_back(e);
    }
    size_t agree = 0;
    for (size_t c = 0; c < words.size(); ++c) {
      const MElt av = rng.elt(mf), ap = rng.elt(mf);
      agree += tags_agree<Field6, MF, kW>(f6, mf, words[c], xs[c], av, ap);
    }
    std::printf("CHECK_TAGS honest=%zu random=64 agree=%zu of %zu\n", nch,
                agree, words.size());
    return agree == words.size() ? 0 : 1;
  }

  bool last_okH = false, last_okA = false;
  auto trial = [&]() {
    ::lfb::Trial T;
    ::lfb::Marks M;
    host_witness();
    fill_A(mode == Mode::kTamperZ);
    fill_H(mode == Mode::kTamperChunk);
    const double witness_ms = M.mark();
    auto zkA = make_proof(*circA, kLigeroA);
    auto zkH = make_proof(*circH, kLigeroH);
    ZkProver<Field6, RSExt> pA(*circA, f6, rsextf);
    ZkProver<HF, RSH> pH(*circH, hf, rsfH);
    Transcript tp(kTranscriptInit, kTranscriptInitLen);
    const double prover_setup = M.mark();
    // Fresh blinds per trial (the commitment's randomness: in commit).
    std::vector<MElt> ap(nmac);
    for (size_t c = 0; c < nmac; ++c) {
      ap[c] = rng.elt(mf);
      for (size_t i = 0; i < kW; ++i) {
        WA.v_[apA_offset + c * kW + i] = ap[c][i] ? f6.one() : f6.zero();
      }
      WH.v_[apH_offset + c] = ap[c];
    }
    if (mode == Mode::kTamperBlind) {
      // H's blind of the first chunk only.
      WH.v_[apH_offset] = hf.addf(ap[0], hf.one());
    }
    const double blinds = M.mark();
    pH.commit(*zkH, WH, tp, rng);
    const double commitH = M.mark();
    pA.commit(*zkA, WA, tp, rng);
    const double commitA = M.mark();

    // MAC key after both commitments; targets into both statements.
    const MElt av = macs ? tp.elt(mf) : MElt{};
    std::vector<MElt> tgt(nmac);
    for (size_t c = 0; c < nmac; ++c) {
      const std::vector<MElt> one{chunks_ref[c]}, coef{av};
      tgt[c] = affine_mac_ref(mf, one, coef, ap[c]);
    }
    auto putA = [&](size_t base, const MElt& e) {
      for (size_t i = 0; i < kW; ++i) WA.v_[base + i] = e[i] ? f6.one() : f6.zero();
    };
    // H's statement: the key, then the targets, one element each.
    std::vector<MElt> tgtH_stmt = tgt;
    if (mode == Mode::kTamperTag) {
      tgtH_stmt[0] = mf.addf(tgt[0], mf.one());
    }
    if (macs) {
      putA(1 + pkN, av);
      WH.v_[1] = av;
    }
    for (size_t c = 0; c < nmac; ++c) {
      putA(1 + pkN + kW + c * kW, tgt[c]);
      WH.v_[1 + kKeyH + c] = tgtH_stmt[c];
    }
    const double mac_ms = M.mark();
    bool okH = pH.prove(*zkH, WH, tp);
    const double proveH = M.mark();
    bool okA = pA.prove(*zkA, WA, tp);
    const double proveA = M.mark();

    std::vector<uint8_t> bufA, bufH;
    zkA->write(bufA, f6);
    zkH->write(bufH, hf);
    T.proof_bytes = bufA.size() + bufH.size() + nmac * MF::kBytes;

    // ---- verifier ----
    M.mark();
    auto rA = make_proof(*circA, kLigeroA);
    auto rH = make_proof(*circH, kLigeroH);
    ReadBuffer rbA(bufA), rbH(bufH);
    const bool readA = rA->read(rbA, f6);
    const bool readH = rH->read(rbH, hf);
    const double v_read = M.mark();
    // The statement from the key's bytes: A_hat, NTT(2^d t1), tr.
    const Statement st = Statement::of_pk(inst.pk);
    auto vH = make_verifier(*circH, rsfH, kLigeroH, hf);
    auto vA = make_verifier(*circA, rsextf, kLigeroA, f6);
    Transcript tv(kTranscriptInit, kTranscriptInitLen);
    vH->recv_commitment(*rH, tv);
    vA->recv_commitment(*rA, tv);
    const MElt av_v = macs ? tv.elt(mf) : MElt{};
    Dense<HF> pubH(1, circH->ninputs);
    {
      DenseFiller<HF> pf(pubH);
      pf.push_back(hf.one());
      if (macs) pf.push_back(av_v);
      for (size_t c = 0; c < nmac; ++c) pf.push_back(tgtH_stmt[c]);
      for (uint8_t byte : st.key.tr) pf.push_back(byte, 8, hf);
      for (uint8_t byte : inst.ctx) pf.push_back(byte, 8, hf);
      check(pf.size() == circH->npub_in, "H public inputs");
    }
    Dense<Field6> pubA(1, circA->ninputs);
    {
      DenseFiller<Field6> pf(pubA);
      pf.push_back(f6.one());
      st.fill_pk(pf, f6);
      if (macs) fill_gf2k<MF, Field6>(av_v, pf, f6);
      for (size_t c = 0; c < nmac; ++c) fill_gf2k<MF, Field6>(tgt[c], pf, f6);
      check(pf.size() == circA->npub_in, "A public inputs");
    }
    const double vsetup = M.mark();
    bool vokH = readH && vH->verify(*rH, pubH, tv);
    const double verifyH = M.mark();
    bool vokA = readA && vA->verify(*rA, pubA, tv);
    const double verifyA = M.mark();

    T.commit_ms = blinds + commitH + commitA;
    T.prove_ms = mac_ms + proveH + proveA;
    T.verify_ms = vsetup + verifyH + verifyA;
    T.ok = okA && okH && vokA && vokH;
    last_okH = okH && vokH;
    last_okA = okA && vokA;
    T.add("witness", witness_ms);
    T.add("prover_setup", prover_setup);
    T.add("blinds", blinds);
    T.add("A_commit", commitA);
    T.add("A_prove", proveA);
    T.add("A_verify", verifyA);
    T.add("A_bytes", double(bufA.size()));
    T.add("H_commit", commitH);
    T.add("H_prove", proveH);
    T.add("H_verify", verifyH);
    T.add("H_bytes", double(bufH.size()));
    T.add("macs_ms", mac_ms);
    T.add("v_proof_read", v_read);
    T.add("v_setup", vsetup);
    T.add("target_bytes", double(nmac * MF::kBytes));
    T.add("A_rate", double(kLigeroA.rate));
    T.add("A_nreq", double(zkA->param.nreq));
    T.add("A_nrow", double(zkA->param.nrow));
    T.add("A_block", double(zkA->param.block));
    T.add("A_block_enc", double(zkA->param.block_enc));
    T.add("H_rate", double(kLigeroH.rate));
    T.add("H_nreq", double(zkH->param.nreq));
    T.add("H_nrow", double(zkH->param.nrow));
    T.add("H_block", double(zkH->param.block));
    T.add("H_block_enc", double(zkH->param.block_enc));
    return T;
  };

  // The tampered instances: the lowest bit of z[0][0]'s encoding (the byte
  // after c_tilde, sigEncode's BitPack of gamma1 - z), and the message's
  // first bit.
  Instance bad_sig = honest, bad_msg = honest;
  bad_sig.sig[Params::c_tilde_bytes] ^= 1;
  bad_msg.msg[0] ^= 1;
  auto run_on = [&](const Instance& i, const char* name) {
    inst = i;
    const ::lfb::Trial T = trial();
    std::printf("%s: signature verifies %d, proof %s\n", name,
                inst_verified ? 1 : 0, T.ok ? "accepted" : "rejected");
    std::fflush(stdout);
    return T.ok;
  };
  switch (mode) {
    case Mode::kServe:
      ::lfb::serve(trial);
      return 0;
    case Mode::kTest: {
      const bool h = run_on(honest, "honest");
      const bool s = run_on(bad_sig, "tamper_sig");
      const bool m = run_on(bad_msg, "tamper_msg");
      std::printf("TEST %s %s macs=%s: %s\n", Set::kName, P::kName,
                  macs ? "on" : "off", (h && !s && !m) ? "PASS" : "FAIL");
      return (h && !s && !m) ? 0 : 1;
    }
    case Mode::kTamperSig:
      return run_on(bad_sig, "tamper_sig") ? 1 : 0;
    case Mode::kTamperMsg:
      return run_on(bad_msg, "tamper_msg") ? 1 : 0;
    case Mode::kTamperZ: {
      const ::lfb::Trial T = trial();
      std::printf("TAMPER ok=%d (expected 0)\n", T.ok ? 1 : 0);
      return T.ok ? 1 : 0;
    }
    default: {
      // H-only tampering: H must reject.
      check(macs, "the H tamper modes need macs=on");
      const ::lfb::Trial T = trial();
      std::printf("TAMPER_H H=%d A=%d (expected H=0)\n", last_okH ? 1 : 0,
                  last_okA ? 1 : 0);
      return (!last_okH && !T.ok) ? 0 : 1;
    }
  }
}

}  // namespace
}  // namespace proofs

int main(int argc, char** argv) {
  std::vector<std::string> args(argv + 1, argv + argc);
  std::string set = proofs::ml_dsa_sets::MlDsa44::kName;
  if (!proofs::ml_dsa_sets::take_param_set(args, set) || args.size() < 2 ||
      args.size() > 3) {
    std::fprintf(stderr,
                 "usage: %s narrow|wide on|off [MODE] "
                 "[--param-set ml-dsa-44|ml-dsa-65|ml-dsa-87]\n",
                 argv[0]);
    return 2;
  }
  const std::string profile = args[0], macs = args[1];
  using proofs::Mode;
  Mode mode = Mode::kServe;
  if (args.size() > 2) {
    const std::string m = args[2];
    if (m == "test") {
      mode = Mode::kTest;
    } else if (m == "tamper_sig") {
      mode = Mode::kTamperSig;
    } else if (m == "tamper_msg") {
      mode = Mode::kTamperMsg;
    } else if (m == "tamper") {
      mode = Mode::kTamperZ;
    } else if (m == "tamper_tag") {
      mode = Mode::kTamperTag;
    } else if (m == "tamper_blind") {
      mode = Mode::kTamperBlind;
    } else if (m == "tamper_chunk") {
      mode = Mode::kTamperChunk;
    } else if (m == "check_tags") {
      mode = Mode::kCheckTags;
    } else {
      return 2;
    }
  }
  if ((profile != "narrow" && profile != "wide") ||
      (macs != "on" && macs != "off")) {
    return 2;
  }
  const bool on = macs == "on";
#if LFB_WIDE_HASH_DOMAIN
  if (profile != "wide") {
    std::fprintf(stderr, "this target is the wide profile\n");
    return 2;
  }
  using Profile = proofs::ml_dsa_split::Wide;
#else
  if (profile != "narrow") {
    std::fprintf(stderr, "this target is the narrow profile\n");
    return 2;
  }
  using Profile = proofs::ml_dsa_split::Narrow;
#endif
  int rc = 2;
  if (!proofs::ml_dsa_sets::with_param_set(set, [&](auto s) {
        rc = proofs::run<Profile, decltype(s)>(on, mode);
      })) {
    std::fprintf(stderr, "unknown parameter set %s\n", set.c_str());
    return 2;
  }
  return rc;
}
