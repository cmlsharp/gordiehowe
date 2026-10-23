// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Post-quantum mdoc, Longfellow style: a worker of common/bench.py.
//
// usage: pq_mdoc_driver      narrow NATTR      (NATTR in 1, 2, 4)
//        pq_mdoc_driver_wide wide   NATTR
// LFB_NEGATIVE=attr: the first requested attribute's value is changed in
// the statement (the fork's WrongAttributeRejected); every proof must fail.
// LFB_NEGATIVE=tag|blind|chunk: H-only tampering of the first MAC chunk: its
// target in H's statement (prover and verifier), its blind a_p in H's
// witness, or one bit of the issuer's w1_tilde in H's witness.  H must
// reject; each trial prints "NEGATIVE <kind> H=<0|1> A=<0|1>" on stderr.
// (A rejects too: when H's circuit is unsatisfied, ZkProver::prove returns
// before writing H's proof to the shared transcript.)
// LFB_CHECK_TAGS=1: no proof; A's emulated tag, H's native tag and the
// host's agree bit for bit on every honest chunk (random a_v and a_p);
// prints CHECK_TAGS and exits 0 on agreement.
//
// Fork-derived: lib/gordiehowe/examples/pq_mdoc_baseline_test.cc at
// b7dfdb34 (the fork's Longfellow-style baseline of its post-quantum mdoc),
// on upstream's library.  The relation is the fork's:
//
//   H  the hash field (narrow: upstream GF(2^128); wide: common-wide's
//      GF(2^256)), LCH14 Reed-Solomon.  One circuit:
//      - the issuer's mu = SHAKE256(tr_I || 00 00 || TBS) over the 29-block
//        buffer (Sha3Circuit's block relation, every block permuted); the
//        private length L (12 bits) fixes the padding and selects the state
//        of block floor(L / 136);
//      - v7's MSO checks over the PQ MSO: barrel shifts (Routing::shift) at
//        private offsets checked against L; validFrom <= now <= validUntil
//        (Memcmp::leq); the deviceKeyInfo window holding the AKP key
//        {1: 7, 3: -48, -1: pk_D}; valueDigests; per attribute 58 20 || d_a
//        with d_a = SHA-256(item) (FlatSHA256Circuit) and v7's
//        assert_attribute (mdoc_attribute_logic.h);
//      - the device: tr_D and mu_D (Sha3Circuit::assert_shake256); ExpandA
//        as 16 SHAKE128 calls of 5 permutations and RejNTTPoly's selection;
//      - both signatures' hash sides (MLDSAHashVerify::assert_hash_side);
//      - the MAC's H side of every crossing, natively in GF(2^w): the
//        chunk packed into one element, one multiplication by a_v, one
//        addition of a_p (one committed element), as upstream mdoc's
//        MACGF2 (circuits/mac/mac_circuit.h).
//   A  the ML-DSA field (narrow: upstream Fp24_6 with upstream's
//      ReedSolomonExtensionFactory; wide: GF(q^11) with the component-wise
//      CRT encoder).  Two MLDSASplitVerify::assert_valid_signature_split,
//      the issuer's key public and the device's private; the device's A_hat
//      equal to its crossed bits and NTT(2^d t1) equal to the NTT of the
//      crossed t1 bits; the MAC's A side, bit by bit (emulated GF(2^w)).
//   crossings  each signature's w1~ and challenge, the device's A_hat
//      (4096 coefficients of 23 bits) and t1 (1024 of 10 bits), in w-bit
//      chunks (w = 128 narrow, 256 wide) with one affine MAC each.
//
// Removed from the fork's test (fork ZK-stack features): the per-proof seed
// in the transcript and the proof (pq_proof_seed.h), the statement
// absorption before the commitments (absorb_statement), the targets'
// transcript write (the targets are public inputs of both proofs, which
// prove/verify absorb, as upstream mdoc), the optimization options, the
// hash-templated ZK classes, ReedSolomonExtensionNFactory.
//
// Per trial: commit = the MAC pads + H + A commit; prove = the MAC key and
// targets + H + A prove; verify = both ZkVerifiers' construction, both
// commitments, the key, the public inputs and both verify calls.  The
// witness (a detail, outside the totals) is computed per trial from the
// presentation: the private data's parse (instance_of) and witness(); the
// circuits once.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <type_traits>
#include <vector>

#include "arrays/dense.h"
#include "bench_worker.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/bit_plucker.h"
#include "circuits/logic/bit_plucker_encoder.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/logic/memcmp.h"
#include "circuits/logic/routing.h"
#include "circuits/mac/mac_reference.h"
#include "circuits/mdoc/mdoc_constants.h"
#include "circuits/sha/flatsha256_circuit.h"
#include "circuits/sha/flatsha256_witness.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_witness.h"
#include "circuits/tests/sha3/sha3_circuit.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "gf2k/lch14_reed_solomon.h"
#include "mdoc_attribute_logic.h"
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
#include "pq_mdoc_data.h"
#include "pq_mdoc_instance.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

namespace proofs {
namespace pq_mdoc_baseline {
namespace {

using namespace ml_dsa_baseline;  // NOLINT(build/namespaces)
using ml_dsa_split::LigeroHalf;
using Params = ml_dsa::MLDsa44Params;

constexpr size_t kBlocksH = kBlocks, kBuf = kBufBytes, kHead = kHeadBytes,
                 kMso = kMsoBytes, kFirst = kWindowFirst;
constexpr size_t kMaxMso = kMaxMsoBytes;
constexpr size_t kMaxMessage = kMaxMessageBytes;  // 3865
constexpr size_t kIdx = kCborIndexBits;  // 12: offsets and L, as v7
static_assert(kFirst + kMaxMso <= kMso && kMaxMessage < (size_t(1) << kIdx),
              "v7's 12-bit offsets index the longest PQ MSO");
constexpr size_t kPk = kPkBytes;
// ExpandA: SHAKE128, 5 permutations, 280 candidates of 23 bits, 256 kept.
constexpr size_t kEaRate = 168, kEaPerms = 5, kCand = 280, kDeg = 256,
                 kSkip = 24, kCoeffBits = 23, kQ = 8380417;
constexpr size_t kW1Bytes = Params::K * Params::w1_bytes;  // 768
// v7's SHA-256 input packing (kSHAPluckerBits).
constexpr size_t kShaPlucker = 4;
const uint8_t kTranscriptInit[] = "pq_mdoc_split";
constexpr size_t kTranscriptInitLen = 13;

// The fork test's Ligero choices: narrow rate 7, block_enc 4096; wide rate
// 6, 295 columns, block_enc 8192 (the tableau (6145, 1024) those columns are
// the minimum for), both halves. Narrow: 122 columns per half, at the
// GordieHowe post-quantum mDL's per-round level 2^-112.76 (its LogUp round;
// longfellow-zk DEVIATIONS 366) by the round-by-round analysis of
// longfellow-zk's equal-security study (Longfellow's order, untested masks,
// DKT26 counts): H (3187, 455) over GF(2^128) 2^-112.82, A (3187, 455) over
// F_q^6 2^-113.54 (132 as deployed: 2^-113.46 and 2^-122.80).
template <class P>
struct Ligero;
template <>
struct Ligero<ml_dsa_split::Narrow> {
  static constexpr LigeroHalf kA{7, 122, 4096}, kH{7, 122, 4096};
};
#if LFB_WIDE_HASH_DOMAIN
template <>
struct Ligero<ml_dsa_split::Wide> {
  static constexpr LigeroHalf kA{6, 295, 8192}, kH{6, 295, 8192};
};
#endif

// ------------------------------------------------------------- circuits --

// Sha3Circuit's block absorption with any rate (its xorin_block is
// private): state A ^= the rate bytes of BLOCK.
template <class LC>
void xorin(const LC &lc, typename LC::v64 A[5][5],
           const std::vector<typename LC::v8> &block, size_t rate) {
  for (size_t i = 0; i < rate; i += 8) {
    const size_t l = i / 8;
    typename LC::v64 a;
    for (size_t b = 0; b < 8; ++b)
      for (size_t j = 0; j < 8; ++j) a[b * 8 + j] = block[i + b][j];
    A[l % 5][l / 5] = lc.vxor(A[l % 5][l / 5], a);
  }
}
// Byte I (< rate) of state A.
template <class LC>
typename LC::v8 state_byte(const typename LC::v64 A[5][5], size_t i) {
  const size_t l = i / 8;
  typename LC::v8 o;
  for (size_t j = 0; j < 8; ++j) o[j] = A[l % 5][l / 5][8 * (i % 8) + j];
  return o;
}

template <class LC>
struct BaselineH {
  using v8 = typename LC::v8;
  using v64 = typename LC::v64;
  using vind = typename LC::template bitvec<kIdx>;
  using v5 = typename LC::template bitvec<5>;
  using v9 = typename LC::template bitvec<9>;
  using v23 = typename LC::template bitvec<kCoeffBits>;
  using BW = typename Sha3Circuit<LC>::BlockWitness;
  using Flatsha = FlatSHA256Circuit<LC, BitPlucker<LC, kShaPlucker>>;
  using ShaBW = typename Flatsha::BlockWitness;
  using AC = AttributeCheck<LC>;

  const LC &lc;
  explicit BaselineH(const LC &l) : lc(l) {}

  // The issuer's mu over BUF (kBuf bytes) with the private total length L,
  // its 29 block witnesses BWS.
  std::array<v8, 64> varlen_mu(const std::vector<v8> &buf, const vind &L,
                               const std::vector<BW> &bws) const {
    Sha3Circuit<LC> sha3(lc);
    std::vector<std::array<v8, 64>> outs(kBlocksH);
    v64 A[5][5];
    for (size_t x = 0; x < 5; ++x)
      for (size_t y = 0; y < 5; ++y) A[x][y] = lc.template vbit<64>(0);
    for (size_t b = 0; b < kBlocksH; ++b) {
      std::vector<v8> block(buf.begin() + long(b * kRate),
                            buf.begin() + long((b + 1) * kRate));
      xorin(lc, A, block, kRate);
      sha3.keccak_f_1600(A, bws[b]);
      for (size_t i = 0; i < 64; ++i) outs[b][i] = state_byte<LC>(A, i);
    }
    // L lies in [kHead + 7, kMaxMessage].
    lc.assert1(lc.vlt(kHead + kFirst - 1, L));
    lc.assert1(lc.vleq(L, kMaxMessage));
    // G_b = [L >= 136 b], sigma_b = G_b and not G_{b+1}.
    std::vector<typename LC::BitW> G(kBlocksH + 1), sigma(kBlocksH);
    G[0] = lc.bit(1);
    for (size_t b = 1; b < kBlocksH; ++b) G[b] = lc.lnot(lc.vlt(L, b * kRate));
    G[kBlocksH] = lc.bit(0);
    for (size_t b = 0; b < kBlocksH; ++b)
      sigma[b] = lc.land(G[b], lc.lnot(G[b + 1]));
    // The padding, byte by byte.
    for (size_t i = kHead + kFirst; i < kBuf; ++i) {
      const auto lt = lc.vlt(i, L);
      const auto eq = lc.veq(L, i);
      const auto gt = lc.land(lc.lnot(lt), lc.lnot(eq));
      if (i % kRate + 1 < kRate) {
        lc.assert_implies(eq, lc.veq(buf[i], 0x1F));
        lc.assert_implies(gt, lc.veq(buf[i], 0));
      } else {
        const auto s = sigma[i / kRate];
        lc.assert_implies(eq, lc.veq(buf[i], 0x9F));
        lc.assert_implies(lc.land(gt, s), lc.veq(buf[i], 0x80));
        lc.assert_implies(lc.land(gt, lc.lnot(s)), lc.veq(buf[i], 0));
      }
    }
    std::array<v8, 64> mu;
    for (size_t i = 0; i < 64; ++i)
      for (size_t t = 0; t < 8; ++t) {
        auto acc = lc.land(sigma[0], outs[0][i][t]);
        for (size_t b = 1; b < kBlocksH; ++b)
          acc = lc.lxor(acc, lc.land(sigma[b], outs[b][i][t]));
        mu[i][t] = acc;
      }
    return mu;
  }

  // SHAKE128(SEED) squeezed to 5 blocks (840 bytes), one witness per
  // permutation; the seed fits one block.
  std::vector<v8> shake128_5(const std::vector<v8> &seed,
                             const std::vector<BW> &bws) const {
    Sha3Circuit<LC> sha3(lc);
    std::vector<v8> block(200, lc.template vbit<8>(0));
    for (size_t i = 0; i < seed.size(); ++i) block[i] = seed[i];
    block[seed.size()] = lc.template vbit<8>(0x1F);
    block[kEaRate - 1] = lc.vxor(block[kEaRate - 1], lc.template vbit<8>(0x80));
    v64 A[5][5];
    for (size_t x = 0; x < 5; ++x)
      for (size_t y = 0; y < 5; ++y) A[x][y] = lc.template vbit<64>(0);
    xorin(lc, A, block, kEaRate);
    std::vector<v8> out;
    for (size_t p = 0; p < kEaPerms; ++p) {
      if (p > 0)
        for (size_t x = 0; x < 5; ++x)
          for (size_t y = 0; y < 5; ++y)
            A[x][y] = bws[p - 1].a_intermediate[23][x][y];
      sha3.keccak_f_1600(A, bws[p]);
      for (size_t i = 0; i < kEaRate; ++i) out.push_back(state_byte<LC>(A, i));
    }
    return out;
  }

  // RejNTTPoly's selection over the 280 candidates of OUT (840 bytes): the
  // 256 coefficients, given the skips R ([256] 5-bit witnesses).
  std::vector<v23> select(const std::vector<v8> &out,
                          const std::vector<v5> &r) const {
    std::vector<v23> cand(kCand);
    std::vector<typename LC::BitW> acc(kCand);
    for (size_t i = 0; i < kCand; ++i) {
      for (size_t b = 0; b < kCoeffBits; ++b)
        cand[i][b] = out[3 * i + b / 8][b % 8];
      acc[i] = lc.vlt(cand[i], kQ);
    }
    // R_i: the rejections among candidates 0..i-1, 9 bits.
    std::vector<v9> R(kCand);
    R[0] = lc.template vbit<9>(0);
    for (size_t i = 0; i + 1 < kCand; ++i) {
      v9 inc = lc.template vbit<9>(0);
      inc[0] = lc.lnot(acc[i]);
      R[i + 1] = lc.template vadd<9>(R[i], inc);
    }
    std::vector<v23> coeff(kDeg);
    for (size_t j = 0; j < kDeg; ++j) {
      lc.assert1(lc.vleq(r[j], kSkip));
      typename LC::BitW ok = lc.bit(0);
      v23 c = lc.template vbit<kCoeffBits>(0);
      for (size_t d = 0; d <= kSkip; ++d) {
        const auto e = lc.veq(r[j], d);
        ok = lc.lxor(ok, lc.land(e, lc.land(acc[j + d], lc.veq(R[j + d], d))));
        for (size_t b = 0; b < kCoeffBits; ++b)
          c[b] = lc.lxor(c[b], lc.land(e, cand[j + d][b]));
      }
      lc.assert1(ok);
      coeff[j] = c;
    }
    return coeff;
  }
};

// ---------------------------------------------------------------- host --

// Block witnesses of the raw absorb of BUF (whole blocks of RATE bytes).
inline std::vector<Sha3Witness::BlockWitness> raw_witness(
    const std::vector<uint8_t> &buf, size_t rate) {
  uint64_t A[5][5];
  std::memset(A, 0, sizeof(A));
  std::vector<Sha3Witness::BlockWitness> w;
  for (size_t b = 0; b * rate < buf.size(); ++b) {
    Sha3Reference::xorin(A, &buf[b * rate], rate);
    Sha3Witness::BlockWitness bw;
    Sha3Witness::compute_witness_block(A, bw);
    w.push_back(bw);
  }
  return w;
}
// SHAKE128(SEED) to 5 blocks: the witnesses and the output.
inline std::vector<Sha3Witness::BlockWitness> shake128_witness(
    const std::vector<uint8_t> &seed, std::vector<uint8_t> &out) {
  uint64_t A[5][5];
  std::memset(A, 0, sizeof(A));
  uint8_t block[200] = {0};
  std::copy(seed.begin(), seed.end(), block);
  block[seed.size()] ^= 0x1F;
  block[kEaRate - 1] ^= 0x80;
  Sha3Reference::xorin(A, block, kEaRate);
  std::vector<Sha3Witness::BlockWitness> w;
  out.clear();
  for (size_t p = 0; p < kEaPerms; ++p) {
    Sha3Witness::BlockWitness bw;
    Sha3Witness::compute_witness_block(A, bw);
    w.push_back(bw);
    for (size_t i = 0; i < kEaRate; ++i)
      out.push_back(uint8_t(A[(i / 8) % 5][(i / 8) / 5] >> (8 * (i % 8))));
  }
  return w;
}
// The skips of RejNTTPoly over the 840 bytes OUT: r_j = the rejections
// before the j-th accepted candidate (masks, no branch on the data).
inline std::vector<uint64_t> skips(const std::vector<uint8_t> &out) {
  std::vector<uint64_t> r(kDeg, 0);
  uint64_t rej = 0, kept = 0;
  for (size_t i = 0; i < kCand; ++i) {
    const uint64_t c = (uint64_t(out[3 * i]) | uint64_t(out[3 * i + 1]) << 8 |
                        uint64_t(out[3 * i + 2]) << 16) &
                       ((1u << 23) - 1);
    const uint64_t ok = ct::lt(c, kQ);
    for (size_t j = 0; j < kDeg; ++j)
      r[j] = ct::select(ct::mask(ok & ct::eq(j, kept)), rej, r[j]);
    kept += ok;
    rej += ok ^ 1;
  }
  return r;
}

// The bits of byte vectors and MAC chunks.
template <class MF>
typename MF::Elt chunk_of(const MF &mf, const std::vector<uint8_t> &bits,
                          size_t c) {
  std::vector<uint8_t> by(MF::kBytes, 0);
  for (size_t i = 0; i < 8 * MF::kBytes; ++i)
    by[i / 8] |= uint8_t((bits.at(c * 8 * MF::kBytes + i) & 1) << (i % 8));
  return mf.of_bytes_field(by.data()).value();
}
inline void append_bytes_as_bits(std::vector<uint8_t> &bits,
                                 const uint8_t *b, size_t n) {
  for (size_t i = 0; i < 8 * n; ++i) bits.push_back((b[i / 8] >> (i % 8)) & 1);
}

inline double ms_since(std::chrono::steady_clock::time_point t0) {
  return std::chrono::duration<double, std::milli>(
             std::chrono::steady_clock::now() - t0)
      .count();
}

// The first 8 bytes of a circuit's id, in hex.
std::string id_hex(const uint8_t id[/*32*/]) {
  char buf[17];
  for (size_t i = 0; i < 8; ++i) std::snprintf(buf + 2 * i, 3, "%02x", id[i]);
  return std::string(buf, 16);
}

template <class F>
std::unique_ptr<ZkProof<F>> make_proof(const Circuit<F> &c, LigeroHalf l) {
  return std::make_unique<ZkProof<F>>(c, l.rate, l.nreq, l.block_enc);
}

// ----------------------------------------------------------- the system --

template <class P>
struct Baseline {
  static constexpr size_t kW = P::kW, kWBytes = P::kWBytes;
  using AF = typename P::AField;
  using ACBK = CompilerBackend<AF>;
  using ALC = Logic<AF, ACBK>;
  using RSA = typename P::RSA;
  using HF = typename P::HashField;
  using HCBK = CompilerBackend<HF>;
  using HLC = Logic<HF, HCBK>;
  using RSH = LCH14ReedSolomonFactory<HF>;
  using MF = typename P::MacField;
  using MElt = typename MF::Elt;
  using WordA = typename ALC::template bitvec<kW>;
  using WordH = typename HLC::template bitvec<kW>;
  using EltWH = typename HLC::EltW;
  static_assert(std::is_same_v<HF, MF>, "H's field is the MAC field");
  using VA = MLDSASplitVerify<ALC, AF, Params>;
  using VH = MLDSAHashVerify<HLC, HF, Params, kW>;
  using BH = BaselineH<HLC>;
  static constexpr LigeroHalf kLigeroA = Ligero<P>::kA, kLigeroH = Ligero<P>::kH;

  size_t n_attr, tbs_bytes, cross = 16;
  size_t n_w1 = kW1Bytes * 8 / kW, n_c = 2 * ml_dsa::N / kW;
  size_t n_a = 0, n_t1 = 0, nch = 0;
  HF hf;
  const typename P::Fields fields;
  const AF &af = fields.a;
  MF mf;
  std::unique_ptr<Circuit<HF>> circH;
  std::unique_ptr<Circuit<AF>> circA;
  size_t h_nwires = 0, a_nwires = 0;
  // LFB_NEGATIVE's H-only kinds: "tag", "blind", "chunk" (else none).
  std::string negative;
  double compile_ms = 0;

  Baseline(size_t n, size_t tbs) : n_attr(n), tbs_bytes(tbs) {
    n_a = cross * kDeg * kCoeffBits / kW;
    n_t1 = Params::K * ml_dsa::N * 10 / kW;
    nch = 2 * (n_w1 + n_c) + n_a + n_t1;
    const auto t0 = std::chrono::steady_clock::now();
    build_a();
    build_h();
    compile_ms = ms_since(t0);
  }

  // ------------------------------------------------------------- A --
  void build_a() {
    auto Q = std::make_unique<QuadCircuit<AF>>(af);
    const ACBK cbk(Q.get());
    const ALC lc(&cbk, af);
    VA v(lc);
    auto pkI = std::make_unique<typename VA::Pk>();
    pkI->input(lc);
    WordA av;
    for (size_t i = 0; i < kW; ++i) av[i] = lc.input();
    std::vector<WordA> tgt(nch);
    for (auto &t : tgt)
      for (size_t i = 0; i < kW; ++i) t[i] = lc.input();
    Q->private_input();
    auto sig = [&](std::unique_ptr<typename VA::SignatureW> &sg,
                   std::unique_ptr<typename VA::Witness> &w) {
      sg = std::make_unique<typename VA::SignatureW>();
      sg->input(lc);
      w = std::make_unique<typename VA::Witness>();
      w->input(lc);
    };
    // The c ternary advice of a signature, tied to its c_, as chunks.
    auto c_chunks = [&](const typename VA::Witness &w) {
      std::vector<WordA> cch(n_c);
      for (auto &ch : cch)
        for (size_t i = 0; i < kW; ++i) ch[i] = lc.bit(0);
      for (size_t k = 0; k < ml_dsa::N; ++k) {
        auto support = lc.input();
        auto signk = lc.input();
        auto sup = lc.eval(support), sg = lc.eval(signk);
        auto ck = lc.sub(sup, lc.mul(af.of_scalar(2), lc.mul(sup, sg)));
        lc.assert_eq(w.c_.coeffs[k], ck);
        cch[(2 * k) / kW][(2 * k) % kW] = support;
        cch[(2 * k + 1) / kW][(2 * k + 1) % kW] = signk;
      }
      return cch;
    };
    std::unique_ptr<typename VA::SignatureW> sgI, sgD;
    std::unique_ptr<typename VA::Witness> wI, wD;
    sig(sgI, wI);
    const auto cI = c_chunks(*wI);
    auto pkD = std::make_unique<typename VA::Pk>();
    pkD->input(lc);
    sig(sgD, wD);
    const auto cD = c_chunks(*wD);
    // The device key's crossed bits.
    std::vector<typename ALC::BitW> abits(cross * kDeg * kCoeffBits),
        tbits(Params::K * ml_dsa::N * 10);
    for (auto &b : abits) b = lc.input();
    for (auto &b : tbits) b = lc.input();
    std::vector<WordA> ap(nch);
    for (auto &a : ap)
      for (size_t i = 0; i < kW; ++i) a[i] = lc.input();

    v.assert_valid_signature_split(*pkI, *sgI, *wI);
    v.assert_valid_signature_split(*pkD, *sgD, *wD);
    // A_hat[e][k] = sum_b 2^b bit.
    for (size_t e = 0; e < cross; ++e)
      for (size_t k = 0; k < kDeg; ++k) {
        auto x = lc.konst(af.zero());
        for (size_t b = 0; b < kCoeffBits; ++b)
          x = lc.axpy(x, af.of_scalar(uint64_t(1) << b),
                      lc.eval(abits[(e * kDeg + k) * kCoeffBits + b]));
        lc.assert_eq(pkD->a_hat.mat[e / Params::L][e % Params::L].coeffs[k], x);
      }
    // nttt1 = NTT(2^d t1), the split circuit's butterflies.
    for (size_t i = 0; i < Params::K; ++i) {
      std::vector<typename ALC::EltW> p(ml_dsa::N);
      for (size_t k = 0; k < ml_dsa::N; ++k) {
        auto x = lc.konst(af.zero());
        for (size_t b = 0; b < 10; ++b)
          x = lc.axpy(x, af.of_scalar(uint64_t(1) << (b + 13)),
                      lc.eval(tbits[(i * ml_dsa::N + k) * 10 + b]));
        p[k] = x;
      }
      size_t kz = 1;
      for (size_t len = ml_dsa::N / 2; len > 0; len /= 2)
        for (size_t start = 0; start < ml_dsa::N; start += 2 * len) {
          auto zeta = af.of_scalar(ml_dsa::kZetas[kz++]);
          auto nz = af.negf(zeta);
          for (size_t j = start; j < start + len; ++j) {
            auto t = lc.axpy(p[j], zeta, p[j + len]);
            p[j + len] = lc.axpy(p[j], nz, p[j + len]);
            p[j] = t;
          }
        }
      for (size_t k = 0; k < ml_dsa::N; ++k)
        lc.assert_eq(p[k], pkD->nttt1[i].coeffs[k]);
    }
    // The MAC chunks, in the order H builds them.
    std::vector<WordA> ch;
    auto add_w1 = [&](const typename VA::Witness &w) {
      for (size_t c = 0; c < n_w1; ++c) {
        WordA x;
        for (size_t b = 0; b < kWBytes; ++b)
          for (size_t j = 0; j < 8; ++j)
            x[8 * b + j] = w.w1_tilde_[kWBytes * c + b][j];
        ch.push_back(x);
      }
    };
    auto add_bits = [&](const std::vector<typename ALC::BitW> &bits) {
      for (size_t c = 0; c * kW < bits.size(); ++c) {
        WordA x;
        for (size_t i = 0; i < kW; ++i) x[i] = bits[c * kW + i];
        ch.push_back(x);
      }
    };
    add_w1(*wI);
    ch.insert(ch.end(), cI.begin(), cI.end());
    add_w1(*wD);
    ch.insert(ch.end(), cD.begin(), cD.end());
    add_bits(abits);
    add_bits(tbits);
    check(ch.size() == nch, "baseline A: chunk count");
    for (size_t c = 0; c < nch; ++c) {
      std::vector<WordA> one(1, ch[c]), coef(1, av);
      lc.vassert_eq(affine_mac(lc, one, coef, ap[c]), tgt[c]);
    }
    Q->begin_full_field();
    circA = Q->mkcircuit(1);
    a_nwires = Q->nwires_;
  }

  // ------------------------------------------------------------- H --
  void build_h() {
    using v8 = typename HLC::v8;
    auto Q = std::make_unique<QuadCircuit<HF>>(hf);
    const HCBK cbk(Q.get());
    const HLC lc(&cbk, hf);
    BH bh(lc);
    // The MAC key and the targets, one GF(2^w) element each.
    const EltWH av = lc.eltw_input();
    std::vector<EltWH> tgt(nch);
    for (auto &t : tgt) t = lc.eltw_input();
    std::array<v8, 64> trI;
    for (auto &b : trI) b = lc.template vinput<8>();
    std::array<v8, 20> now;
    for (auto &b : now) b = lc.template vinput<8>();
    std::vector<typename BH::AC::OpenedAttribute> oa(n_attr);
    for (auto &o : oa) {
      for (size_t j = 0; j < 32; ++j) o.attr[j] = lc.template vinput<8>();
      for (size_t j = 0; j < 64; ++j) o.v1[j] = lc.template vinput<8>();
      o.len = lc.template vinput<8>();
      o.vlen = lc.template vinput<8>();
    }
    std::vector<v8> tbs(tbs_bytes);
    for (auto &b : tbs) b = lc.template vinput<8>();
    Q->private_input();
    std::vector<v8> in(kMso);
    for (auto &b : in) b = lc.template vinput<8>();
    const auto L = lc.template vinput<kIdx>();
    auto bws = [&](size_t n) {
      std::vector<typename BH::BW> w(n);
      for (auto &x : w) x.input(lc);
      return w;
    };
    const auto mu_bws = bws(kBlocksH);
    typename BH::vind k_from = lc.template vinput<kIdx>(),
                      k_until = lc.template vinput<kIdx>(),
                      k_dev = lc.template vinput<kIdx>(),
                      k_vd = lc.template vinput<kIdx>();
    struct Attr {
      std::vector<v8> bytes;
      std::vector<typename BH::ShaBW> sha;
      typename BH::vind k;
      typename BH::AC::SaltedHash sh;
    };
    std::vector<Attr> at(n_attr);
    for (auto &a : at) {
      a.bytes.resize(128);
      for (auto &b : a.bytes) b = lc.template vinput<8>();
      a.sha.resize(2);
      for (auto &s : a.sha) s.input(lc);
      a.k = lc.template vinput<kIdx>();
      a.sh.i1 = lc.template vinput<kIdx>();
      a.sh.i2 = lc.template vinput<kIdx>();
      a.sh.i3 = lc.template vinput<kIdx>();
      for (size_t j = 0; j < 4; ++j) a.sh.l[j] = lc.template vinput<kIdx>();
      a.sh.perm = lc.template vinput<8>();
    }
    const auto tr_bws = bws((kPk + 136) / 136);
    const auto mud_bws = bws((64 + 2 + tbs_bytes + 136) / 136);
    std::vector<std::vector<typename BH::BW>> ea_bws(cross);
    for (auto &w : ea_bws) w = bws(kEaPerms);
    std::vector<std::vector<typename BH::v5>> skip(cross);
    for (auto &r : skip) {
      r.resize(kDeg);
      for (auto &x : r) x = lc.template vinput<5>();
    }
    auto hash_side_inputs = [&](std::array<v8, Params::c_tilde_bytes> &ct,
                                typename VH::HashWitness &w) {
      for (auto &b : ct) b = lc.template vinput<8>();
      w.c_prime_tilde_bws_.resize(7);
      w.input(lc);
    };
    std::array<v8, Params::c_tilde_bytes> ctI, ctD;
    auto wIp = std::make_unique<typename VH::HashWitness>();
    auto wDp = std::make_unique<typename VH::HashWitness>();
    auto &wI = *wIp;
    auto &wD = *wDp;
    hash_side_inputs(ctI, wI);
    hash_side_inputs(ctD, wD);
    // The blinds, one full-field element each, after every subfield input.
    Q->begin_full_field();
    std::vector<EltWH> ap(nch);
    for (auto &a : ap) a = lc.eltw_input();

    // 1. The issuer's mu over tr_I || 00 00 || cose_prefix || MSO.
    std::vector<v8> buf;
    for (auto &b : trI) buf.push_back(b);
    buf.push_back(lc.template vbit<8>(0));
    buf.push_back(lc.template vbit<8>(0));
    for (uint8_t c : cose_prefix()) buf.push_back(lc.template vbit<8>(c));
    buf.insert(buf.end(), in.begin(), in.end());
    const auto muI = bh.varlen_mu(buf, L, mu_bws);

    // 2. v7's windows by barrel shifts from MSO byte 7, offsets below L.
    Routing<HLC> r(lc);
    const Memcmp<HLC> cmp(lc);
    typename BH::Flatsha sha(lc);
    const typename BH::AC ac(lc);
    const v8 zz = lc.template vbit<8>(0);
    const v8 *mso = &in[kFirst];
    auto check_index = [&](const typename BH::vind &k) {
      lc.assert1(lc.vlt(k, L));
    };
    auto assert_bytes = [&](const v8 *b, const std::vector<uint8_t> &want) {
      for (size_t i = 0; i < want.size(); ++i) lc.vassert_eq(b[i], want[i]);
    };
    std::vector<v8> cb(kMaxMso);
    const size_t kf = valid_from_key().size(), ku = valid_until_key().size();
    check_index(k_from);
    r.shift(k_from, kf + 20, &cb[0], kMaxMso, mso, zz, 3);
    assert_bytes(&cb[0], valid_from_key());
    lc.assert1(cmp.leq(20, &cb[kf], &now[0]));
    check_index(k_until);
    r.shift(k_until, ku + 20, &cb[0], kMaxMso, mso, zz, 3);
    assert_bytes(&cb[0], valid_until_key());
    lc.assert1(cmp.leq(20, &now[0], &cb[ku]));
    const size_t kd = device_key_info_key().size();
    check_index(k_dev);
    r.shift(k_dev, kd + kPk, &cb[0], kMaxMso, mso, zz, 3);
    assert_bytes(&cb[0], device_key_info_key());
    const std::vector<v8> pk(cb.begin() + long(kd),
                             cb.begin() + long(kd + kPk));
    check_index(k_vd);
    r.shift(k_vd, 13, &cb[0], kMaxMso, mso, zz, 3);
    assert_bytes(&cb[0], value_digests_key());
    for (size_t a = 0; a < n_attr; ++a) {
      check_index(at[a].k);
      r.shift(at[a].k, 34, &cb[0], kMaxMso, mso, zz, 3);
      assert_bytes(&cb[0], digest_key());
      typename HLC::v256 mm;
      for (size_t j = 0; j < 256; ++j) mm[j] = cb[2 + (255 - j) / 8][j % 8];
      const auto two = lc.template vbit<8>(2);
      sha.assert_message_hash(2, two, at[a].bytes.data(), mm, at[a].sha.data());
      const auto len_bits = sha.find_len_bits(2, at[a].bytes.data(), two);
      ac.assert_attribute(128, at[a].bytes.data(), at[a].sh, oa[a], len_bits);
    }

    // 3. The device: tr_D, mu_D, ExpandA.
    Sha3Circuit<HLC> sha3(lc);
    std::vector<v8> trD;
    sha3.assert_shake256(pk, 64, trD, tr_bws);
    std::vector<v8> mu_in(trD.begin(), trD.end());
    mu_in.push_back(lc.template vbit<8>(0));
    mu_in.push_back(lc.template vbit<8>(0));
    mu_in.insert(mu_in.end(), tbs.begin(), tbs.end());
    std::vector<v8> muDv;
    sha3.assert_shake256(mu_in, 64, muDv, mud_bws);
    std::array<v8, 64> muD;
    std::copy(muDv.begin(), muDv.end(), muD.begin());
    std::vector<typename HLC::BitW> abits;
    for (size_t e = 0; e < cross; ++e) {
      std::vector<v8> seed(pk.begin(), pk.begin() + 32);
      seed.push_back(lc.template vbit<8>(e % Params::L));
      seed.push_back(lc.template vbit<8>(e / Params::L));
      const auto out = bh.shake128_5(seed, ea_bws[e]);
      const auto coeff = bh.select(out, skip[e]);
      for (const auto &c : coeff)
        for (size_t b = 0; b < kCoeffBits; ++b) abits.push_back(c[b]);
    }
    std::vector<typename HLC::BitW> tbits;
    for (size_t i = 8 * 32; i < 8 * kPk; ++i) tbits.push_back(pk[i / 8][i % 8]);

    // 4. Both signatures' hash sides, then the MAC chunks.
    VH vh(lc);
    const auto cI = vh.assert_hash_side(ctI, muI, wI);
    const auto cD = vh.assert_hash_side(ctD, muD, wD);
    std::vector<WordH> ch;
    auto add_w1 = [&](const typename VH::HashWitness &w) {
      for (size_t c = 0; c < n_w1; ++c) {
        WordH x;
        for (size_t b = 0; b < kWBytes; ++b)
          for (size_t j = 0; j < 8; ++j)
            x[8 * b + j] = w.w1_tilde_[kWBytes * c + b][j];
        ch.push_back(x);
      }
    };
    auto add_bits = [&](const std::vector<typename HLC::BitW> &bits) {
      for (size_t c = 0; c * kW < bits.size(); ++c) {
        WordH x;
        for (size_t i = 0; i < kW; ++i) x[i] = bits[c * kW + i];
        ch.push_back(x);
      }
    };
    add_w1(wI);
    ch.insert(ch.end(), cI.begin(), cI.end());
    add_w1(wD);
    ch.insert(ch.end(), cD.begin(), cD.end());
    add_bits(abits);
    add_bits(tbits);
    check(ch.size() == nch, "baseline H: chunk count");
    for (size_t c = 0; c < nch; ++c) {
      lc.assert_eq(affine_mac_native<HLC, kW>(lc, ch[c], av, ap[c]), tgt[c]);
    }
    circH = Q->mkcircuit(1);
    h_nwires = Q->nwires_;
  }

  // ------------------------------------------------------- witness --
  struct Witness {
    std::unique_ptr<Dense<HF>> WH;
    std::unique_ptr<Dense<AF>> WA;
    std::vector<MElt> chunks;  // the crossed values, host side
    std::vector<uint8_t> bits;  // the same, as the circuits' chunk bits
    size_t ap_h = 0, ap_a = 0;
  };

  Witness witness(const data::Presentation &x, const Instance &in) const {
    using ml_dsa_witness_t = ml_dsa_witness<Params>;
    Witness W;
    const auto &doc = x.doc;
    auto wgI = std::make_unique<ml_dsa_witness_t>();
    auto wgD = std::make_unique<ml_dsa_witness_t>();
    check(wgI->compute_witness(doc.issuer.pk, doc.issuer_sig, doc.tbs, {}),
          "baseline: issuer signature");
    check(wgD->compute_witness(doc.device.pk, x.device_sig, x.device_tbs, {}),
          "baseline: device signature");
    // The crossed values, host side, in chunk order.
    std::vector<uint8_t> bits;
    auto w1 = [&](const ml_dsa_witness_t &w) {
      append_bytes_as_bits(bits, w.w1_tilde_.data(), w.w1_tilde_.size());
    };
    auto cbits = [&](const ml_dsa_witness_t &w) {
      for (size_t k = 0; k < ml_dsa::N; ++k) {
        const uint64_t v = w.f_.from_montgomery(w.c_coeffs_[k]).limb_[0];
        bits.push_back(v != 0);
        bits.push_back(v == ml_dsa::Q - 1);
      }
    };
    w1(*wgI);
    cbits(*wgI);
    w1(*wgD);
    cbits(*wgD);
    // ExpandA's outputs and skips, and A_hat's bits.
    std::vector<std::vector<Sha3Witness::BlockWitness>> ea_bws(cross);
    std::vector<std::vector<uint64_t>> skip(cross);
    std::vector<uint8_t> abits;
    for (size_t e = 0; e < cross; ++e) {
      std::vector<uint8_t> seed(doc.device.pk.begin(),
                                doc.device.pk.begin() + 32);
      seed.push_back(uint8_t(e % Params::L));
      seed.push_back(uint8_t(e / Params::L));
      std::vector<uint8_t> out;
      ea_bws[e] = shake128_witness(seed, out);
      skip[e] = skips(out);
      const auto &poly = wgD->ref_pk_.a_hat[e / Params::L][e % Params::L];
      for (size_t k = 0; k < kDeg; ++k) {
        const uint64_t v = wgD->f_.from_montgomery(poly[k]).limb_[0];
        for (size_t b = 0; b < kCoeffBits; ++b) abits.push_back((v >> b) & 1);
      }
    }
    bits.insert(bits.end(), abits.begin(), abits.end());
    std::vector<uint8_t> tbits;
    for (size_t i = 8 * 32; i < 8 * kPk; ++i)
      tbits.push_back((doc.device.pk[i / 8] >> (i % 8)) & 1);
    bits.insert(bits.end(), tbits.begin(), tbits.end());
    for (size_t c = 0; c < nch; ++c) W.chunks.push_back(chunk_of(mf, bits, c));
    W.bits = std::move(bits);

    // A.
    W.WA = std::make_unique<Dense<AF>>(1, circA->ninputs);
    {
      DenseFiller<AF> f(*W.WA);
      f.push_back(af.one());
      wgI->fill_pk(f, af);
      for (size_t i = 0; i < kW * (1 + nch); ++i) f.push_back(af.zero());
      auto sig = [&](const ml_dsa_witness_t &w) {
        fill_split_A_priv(f, w, af);
        for (size_t k = 0; k < ml_dsa::N; ++k) {
          const uint64_t v = w.f_.from_montgomery(w.c_coeffs_[k]).limb_[0];
          f.push_back(v != 0 ? af.one() : af.zero());
          f.push_back(v == ml_dsa::Q - 1 ? af.one() : af.zero());
        }
      };
      sig(*wgI);
      wgD->fill_pk(f, af);
      sig(*wgD);
      for (uint8_t b : abits) f.push_back(b ? af.one() : af.zero());
      for (uint8_t b : tbits) f.push_back(b ? af.one() : af.zero());
      W.ap_a = f.size();
      for (size_t i = 0; i < kW * nch; ++i) f.push_back(af.zero());
      check(f.size() == circA->ninputs, "baseline A: witness size");
    }
    // H.
    W.WH = std::make_unique<Dense<HF>>(1, circH->ninputs);
    {
      DenseFiller<HF> f(*W.WH);
      f.push_back(hf.one());
      for (size_t i = 0; i < 1 + nch; ++i) f.push_back(hf.zero());
      for (uint8_t b : wgI->tr_) f.push_back(b, 8, hf);
      for (uint8_t b : in.statement.now) f.push_back(b, 8, hf);
      for (const auto &a : in.statement.attributes) {
        for (uint8_t b : a.id) f.push_back(b, 8, hf);
        for (uint8_t b : a.value) f.push_back(b, 8, hf);
        f.push_back(a.id_len, 8, hf);
        f.push_back(a.value_len, 8, hf);
      }
      for (uint8_t b : in.statement.device_tbs) f.push_back(b, 8, hf);
      // Private.
      for (uint8_t b : in.data.mso) f.push_back(b, 8, hf);
      f.push_back(in.data.length, kIdx, hf);
      std::vector<uint8_t> buf(kBuf, 0);
      std::copy(wgI->tr_.begin(), wgI->tr_.end(), buf.begin());
      std::copy(cose_prefix().begin(), cose_prefix().end(), buf.begin() + 66);
      std::copy(in.data.mso.begin(), in.data.mso.end(),
                buf.begin() + long(kHead));
      Sha3Witness::fill_witness(f, raw_witness(buf, kRate), hf);
      for (size_t k = 0; k < 4; ++k) f.push_back(in.data.offsets[k], kIdx, hf);
      BitPluckerEncoder<HF, kShaPlucker> enc(hf);
      for (size_t a = 0; a < n_attr; ++a) {
        const auto &it = in.data.items[a];
        for (uint8_t b : it.bytes) f.push_back(b, 8, hf);
        const auto &item = doc.items.at(x.requested[a]);
        uint8_t nb = 0;
        uint8_t padded[128];
        FlatSHA256Witness::BlockWitness sbw[2];
        FlatSHA256Witness::transform_and_witness_message(
            item.bytes.size(), item.bytes.data(), 2, nb, padded, sbw);
        check(std::equal(padded, padded + 128, it.bytes.begin()),
              "baseline: the item's padding");
        for (const auto &bw : sbw) {
          for (size_t k = 0; k < 48; ++k)
            f.push_back(enc.mkpacked_v32(bw.outw[k]));
          for (size_t k = 0; k < 64; ++k) {
            f.push_back(enc.mkpacked_v32(bw.oute[k]));
            f.push_back(enc.mkpacked_v32(bw.outa[k]));
          }
          for (size_t k = 0; k < 8; ++k) f.push_back(enc.mkpacked_v32(bw.h1[k]));
        }
        f.push_back(in.data.offsets[4 + a], kIdx, hf);
        for (size_t v : {it.i1, it.i2, it.i3, it.l[0], it.l[1], it.l[2], it.l[3]})
          f.push_back(v, kIdx, hf);
        f.push_back(it.perm, 8, hf);
      }
      std::vector<Sha3Witness::BlockWitness> trw, muw;
      Sha3Witness::compute_witness_shake256(doc.device.pk, 64, trw);
      Sha3Witness::fill_witness(f, trw, hf);
      std::vector<uint8_t> mu_in(wgD->tr_.begin(), wgD->tr_.end());
      mu_in.push_back(0);
      mu_in.push_back(0);
      mu_in.insert(mu_in.end(), x.device_tbs.begin(), x.device_tbs.end());
      Sha3Witness::compute_witness_shake256(mu_in, 64, muw);
      Sha3Witness::fill_witness(f, muw, hf);
      for (const auto &w : ea_bws) Sha3Witness::fill_witness(f, w, hf);
      for (const auto &r : skip)
        for (uint64_t v : r) f.push_back(v, 5, hf);
      auto hash_side = [&](const ml_dsa_witness_t &w) {
        for (size_t i = 0; i < Params::c_tilde_bytes; ++i)
          f.push_back(w.c_tilde_[i], 8, hf);
        for (size_t i = 0; i < Params::tau; ++i) {
          f.push_back(w.j_vals_[i], 8, hf);
          f.push_back(w.j_k_indices_[i], 16, hf);
        }
        Sha3Witness::fill_witness(f, w.shake_bws_, hf);
        for (size_t s = 0; s < Params::tau; ++s)
          for (size_t k = 0; k <= s; ++k)
            f.push_back(w.position_trace_[s][k], 8, hf);
        // LFB_NEGATIVE=chunk: one bit of the issuer's w1_tilde, H only.
        const bool flip = negative == "chunk" && &w == wgI.get();
        for (size_t i = 0; i < w.w1_tilde_.size(); ++i)
          f.push_back(w.w1_tilde_[i] ^ ((flip && i == 0) ? 1 : 0), 8, hf);
        for (const auto &bw : w.c_prime_tilde_bws_)
          Sha3Witness::fill_witness(f, bw, hf);
      };
      hash_side(*wgI);
      hash_side(*wgD);
      W.ap_h = f.size();
      for (size_t i = 0; i < nch; ++i) f.push_back(hf.zero());
      check(f.size() == circH->ninputs, "baseline H: witness size");
    }
    return W;
  }

  // ------------------------------------------- prove and verify --
  lfb::Trial run(const data::Presentation &x, const Instance &in,
                 SecureRandomEngine &rng) const {
    lfb::Trial T;
    // The full witness from the instance: the private data parsed from the
    // presentation (instance_of: the MSO buffer, the window offsets, the
    // padded items) under the statement IN, then witness().
    const auto tw = std::chrono::steady_clock::now();
    Instance parsed = instance_of(x);
    parsed.statement = in.statement;
    Witness W = witness(x, parsed);
    T.add("witness", ms_since(tw));
    const RSA &rsa = fields.rsa;
    const RSH rsh(hf);
    const size_t macH = 1 + 1 + nch;
    const size_t pkN = Params::K * Params::L * ml_dsa::N +
                       Params::K * ml_dsa::N + 64 * 8;
    auto zkA = make_proof(*circA, kLigeroA);
    auto zkH = make_proof(*circH, kLigeroH);
    ZkProver<AF, RSA> pA(*circA, af, rsa);
    ZkProver<HF, RSH> pH(*circH, hf, rsh);
    Transcript tp(kTranscriptInit, kTranscriptInitLen);
    auto &WH = *W.WH;
    auto &WA = *W.WA;
    // The MAC pads (the commitment's randomness: in commit).
    lfb::Marks M;
    std::vector<MElt> ap(nch);
    for (size_t c = 0; c < nch; ++c) {
      ap[c] = rng.elt(mf);
      for (size_t i = 0; i < kW; ++i) {
        WA.v_[W.ap_a + c * kW + i] = ap[c][i] ? af.one() : af.zero();
      }
      WH.v_[W.ap_h + c] = ap[c];
    }
    if (negative == "blind") {
      WH.v_[W.ap_h] = hf.addf(ap[0], hf.one());
    }
    const double pads = M.mark();
    pH.commit(*zkH, WH, tp, rng);
    const double commitH = M.mark();
    pA.commit(*zkA, WA, tp, rng);
    const double commitA = M.mark();
    const MElt av = tp.elt(mf);
    std::vector<MElt> tgt(nch);
    for (size_t c = 0; c < nch; ++c) {
      tgt[c] = affine_mac_ref(mf, {W.chunks[c]}, {av}, ap[c]);
    }
    auto put = [&](auto &dense, const auto &F, size_t base, const MElt &e) {
      for (size_t i = 0; i < kW; ++i)
        dense.v_[base + i] = e[i] ? F.one() : F.zero();
    };
    // H's statement: the key, then the targets, one element each.
    std::vector<MElt> tgtH = tgt;
    if (negative == "tag") {
      tgtH[0] = mf.addf(tgt[0], mf.one());
    }
    WH.v_[1] = av;
    put(WA, af, 1 + pkN, av);
    for (size_t c = 0; c < nch; ++c) {
      WH.v_[2 + c] = tgtH[c];
      put(WA, af, 1 + pkN + kW + c * kW, tgt[c]);
    }
    const double mac_ms = M.mark();
    const bool okH = pH.prove(*zkH, WH, tp);
    const double proveH = M.mark();
    const bool okA = pA.prove(*zkA, WA, tp);
    const double proveA = M.mark();
    std::vector<uint8_t> bufA, bufH;
    zkA->write(bufA, af);
    zkH->write(bufH, hf);
    T.proof_bytes = bufA.size() + bufH.size() + nch * MF::kBytes;

    // Verify: the verifier's statement (the prover's public inputs with the
    // MAC key and targets cleared), its ZkVerifiers, the commitments, a_v,
    // the targets, then H and A.
    Dense<HF> pubH(1, circH->ninputs);
    Dense<AF> pubA(1, circA->ninputs);
    for (size_t i = 0; i < circH->npub_in; ++i) pubH.v_[i] = WH.v_[i];
    for (size_t i = 0; i < circA->npub_in; ++i) pubA.v_[i] = WA.v_[i];
    for (size_t i = 1; i < macH; ++i) pubH.v_[i] = hf.zero();
    for (size_t i = 1 + pkN; i < circA->npub_in; ++i) pubA.v_[i] = af.zero();
    M.mark();
    ZkVerifier<HF, RSH> vH(*circH, rsh, kLigeroH.rate, kLigeroH.nreq,
                           kLigeroH.block_enc, hf);
    ZkVerifier<AF, RSA> vA(*circA, rsa, kLigeroA.rate, kLigeroA.nreq,
                           kLigeroA.block_enc, af);
    Transcript tv(kTranscriptInit, kTranscriptInitLen);
    vH.recv_commitment(*zkH, tv);
    vA.recv_commitment(*zkA, tv);
    const MElt av_v = tv.elt(mf);
    pubH.v_[1] = av_v;
    put(pubA, af, 1 + pkN, av_v);
    for (size_t c = 0; c < nch; ++c) {
      pubH.v_[2 + c] = tgtH[c];
      put(pubA, af, 1 + pkN + kW + c * kW, tgt[c]);
    }
    const double vsetup = M.mark();
    const bool vokH = vH.verify(*zkH, pubH, tv);
    const double verifyH = M.mark();
    const bool vokA = vA.verify(*zkA, pubA, tv);
    const double verifyA = M.mark();

    T.commit_ms = pads + commitH + commitA;
    T.prove_ms = mac_ms + proveH + proveA;
    T.verify_ms = vsetup + verifyH + verifyA;
    T.ok = okH && okA && vokH && vokA;
    if (!negative.empty()) {
      std::fprintf(stderr, "NEGATIVE %s H=%d A=%d\n", negative.c_str(),
                   (okH && vokH) ? 1 : 0, (okA && vokA) ? 1 : 0);
    }
    T.add("pads", pads);
    T.add("A_commit", commitA);
    T.add("A_prove", proveA);
    T.add("A_verify", verifyA);
    T.add("A_bytes", double(bufA.size()));
    T.add("H_commit", commitH);
    T.add("H_prove", proveH);
    T.add("H_verify", verifyH);
    T.add("H_bytes", double(bufH.size()));
    T.add("macs_ms", mac_ms);
    T.add("v_setup", vsetup);
    T.add("target_bytes", double(nch * MF::kBytes));
    T.add("A_nrow", double(zkA->param.nrow));
    T.add("A_block", double(zkA->param.block));
    T.add("H_nrow", double(zkH->param.nrow));
    T.add("H_block", double(zkH->param.block));
    return T;
  }
};

const data::Document &document() {
  static const data::Document d =
      data::issue(data::keygen(1), data::keygen(2));
  return d;
}

template <class P>
int serve_profile(size_t n) {
  set_log_level(ERROR);
  const auto x = data::present(document(), data::bench_request(n));
  auto in = instance_of(x);
  const char *neg = std::getenv("LFB_NEGATIVE");
  const std::string neg_kind = neg != nullptr ? neg : "";
  const bool negative = neg_kind == "attr";
  const bool negative_h =
      neg_kind == "tag" || neg_kind == "blind" || neg_kind == "chunk";
  if (negative) {
    // The fork's WrongAttributeRejected: element 5 with the value false.
    data::Element e = document().elements.at(5);
    e.value = {0xF4};
    in.statement.attributes[0] = statement_of(e);
  }
  Baseline<P> b(n, in.statement.device_tbs.size());
  if (negative_h) b.negative = neg_kind;
  lfb::info({{"profile", P::kName},
             {"attrs", std::to_string(n)},
             {"negative", (negative || negative_h) ? neg_kind : "none"},
             {"chunks", std::to_string(b.nch)},
             {"compile_ms", std::to_string(b.compile_ms)},
             {"H_ninputs", std::to_string(b.circH->ninputs)},
             {"H_npub", std::to_string(b.circH->npub_in)},
             {"H_nl", std::to_string(b.circH->nl)},
             {"H_nwires", std::to_string(b.h_nwires)},
             {"H_nterms", std::to_string(b.circH->nterms())},
             {"H_id", id_hex(b.circH->id)},
             {"A_ninputs", std::to_string(b.circA->ninputs)},
             {"A_npub", std::to_string(b.circA->npub_in)},
             {"A_nl", std::to_string(b.circA->nl)},
             {"A_nwires", std::to_string(b.a_nwires)},
             {"A_nterms", std::to_string(b.circA->nterms())},
             {"A_id", id_hex(b.circA->id)}});
  SecureRandomEngine rng;
  const char *check_tags = std::getenv("LFB_CHECK_TAGS");
  if (check_tags != nullptr && std::string(check_tags) == "1") {
    using MF = typename P::MacField;
    constexpr size_t kW = P::kW;
    const auto W = b.witness(x, in);
    size_t agree = 0;
    for (size_t c = 0; c < b.nch; ++c) {
      std::array<uint8_t, kW> word{};
      for (size_t i = 0; i < kW; ++i) word[i] = W.bits.at(c * kW + i);
      const auto av = rng.elt(b.mf), ap = rng.elt(b.mf);
      agree += tags_agree<typename P::AField, MF, kW>(b.af, b.mf, word,
                                                      W.chunks[c], av, ap);
    }
    std::printf("CHECK_TAGS honest=%zu agree=%zu\n", b.nch, agree);
    return agree == b.nch ? 0 : 1;
  }
  lfb::serve([&]() { return b.run(x, in, rng); });
  return 0;
}

}  // namespace
}  // namespace pq_mdoc_baseline
}  // namespace proofs

int main(int argc, char **argv) {
  if (argc != 3) {
    std::fprintf(stderr, "usage: %s narrow|wide NATTR\n", argv[0]);
    return 2;
  }
  const std::string profile = argv[1];
  const size_t n = std::strtoull(argv[2], nullptr, 10);
  if (n != 1 && n != 2 && n != 4) return 2;
#if LFB_WIDE_HASH_DOMAIN
  if (profile != "wide") {
    std::fprintf(stderr, "this target is the wide profile\n");
    return 2;
  }
  return proofs::pq_mdoc_baseline::serve_profile<proofs::ml_dsa_split::Wide>(n);
#else
  if (profile != "narrow") {
    std::fprintf(stderr, "this target is the narrow profile\n");
    return 2;
  }
  return proofs::pq_mdoc_baseline::serve_profile<proofs::ml_dsa_split::Narrow>(
      n);
#endif
}
