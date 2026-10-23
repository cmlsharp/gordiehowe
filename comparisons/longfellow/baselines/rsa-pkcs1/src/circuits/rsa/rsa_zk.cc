// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// RSA-2048 PKCS#1 v1.5 (SHA-256) proof of possession with upstream
// Longfellow, structured as circuits/mdoc/mdoc_zk.cc: a hash circuit over
// GF(2^128) and a signature circuit over Fp256 (P-256's base field, as
// mdoc's signature circuit) or Fp128 (2^128 - 2^108 + 1), linked by MACs of
// the digest. The message has a private length up to the relation's
// maximum n_m (rsa_hash.h); MSG below is n_m, and the timed message is n_m
// bytes long. Ligero at mdoc v7's rate 7, block_enc chosen per circuit as
// circuit_maker.cc's optimize() does; the opened columns per circuit below.
//
// Usage:
//   rsa_zk test                 honest proofs and the rejections at the
//                               default layout; circuit-level checks of
//                               tampered witnesses at the default layout and
//                               the BitPlucker layout
//   rsa_zk bench REPS           warm-up, then REPS interleaved trials of
//                               every (field, message length) at the default
//                               layout; one line per trial
//   rsa_zk stats                circuit sizes at the default layout
//   rsa_zk plan N_M T...        the hash circuit's tableau at n_m = N_M
//                               bytes and T opened columns (block_enc by
//                               the search at T)
//   rsa_zk plansig FIELD T...   the signature circuit's tableau over FIELD
//                               (Fp128 or Fp256) at the default layout
//   rsa_zk worker FIELD MSG [RANGE LOGN W]
//                               one System served to common/bench.py; FIELD
//                               is Fp128 or Fp256; RANGE is vanish
//                               (digit values, vanishing polynomial) or
//                               pluck (BitPlucker digits); the default is
//                               the field's default layout

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <memory>
#include <string>
#include <type_traits>
#include <vector>

#include "algebra/convolution.h"
#include "algebra/fp2.h"
#include "algebra/fp_p128.h"
#include "algebra/reed_solomon.h"
#include "arrays/dense.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/mac/mac_circuit.h"
#include "circuits/mac/mac_reference.h"
#include "circuits/mac/mac_witness.h"
#include "circuits/rsa/rsa_hash.h"
#include "circuits/rsa/rsa_shape.h"
#include "circuits/rsa/rsa_signature.h"
#include "circuits/rsa/rsa_vectors.h"
#include "circuits/rsa/rsa_witness.h"
#include "circuits/sha/flatsha256_witness.h"
#include "ec/p256.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "ligero/ligero_param.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/prover_layers.h"
#include "util/log.h"
#include "util/readbuffer.h"
#include "zk/zk_common.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

// longfellow-baselines: the worker mode of common/bench.py.
#include "bench_worker.h"

namespace proofs {
namespace {

namespace vec = ::proofs::gordiehowe::examples::rsa::vectors;

using f_128 = GF2_128<>;
using gf2k = f_128::Elt;
using RSFh = LCH14ReedSolomonFactory<f_128>;

// mdoc v7's rate (mdoc_zk.h's kLigeroRatev7) for every circuit.
constexpr size_t kRate = 7;
// The opened columns: the least t meeting the GordieHowe ROM per-round
// target 2^-113.5 by the round-by-round analysis of longfellow-zk's
// equal-security study (Longfellow's order, untested masks, DKT26 counts),
// on the tableau (N, k) the block_enc search gives at that t
// (N = block_enc - (2k - 1), k = block). The Fp128 signature circuit 139,
// (7196, 1028) at 2^-113.74 (138: 2^-112.91); the Fp256 signature circuit
// 124, (6699, 957) at 2^-113.60 (123: 2^-112.69); the hash circuit over
// GF(2^128) at n_m = 64 B (2 blocks) 120, (1799, 257) at 2^-113.50 (119:
// 2^-113.15), and at n_m = 2 KB (33 blocks) 138, (4088, 584) at 2^-114.08
// (137: 2^-113.24).
constexpr size_t kNreqSig128 = 139;
constexpr size_t kNreqSig256 = 124;
constexpr size_t kNreqHash64 = 120;
constexpr size_t kNreqHash2k = 138;
size_t hash_nreq(size_t n_m) {
  check(n_m == 64 || n_m == 2048, "hash columns are set for n_m = 64 and 2048");
  return n_m == 2048 ? kNreqHash2k : kNreqHash64;
}
constexpr size_t kTranscriptVersion = 7;
const uint8_t kSeed[] = "rsa-pkcs1-proof-of-possession";

using Clock = std::chrono::steady_clock;
double ms_since(Clock::time_point t0) {
  return std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
}

// mdoc_zk.cc's root of unity for the Fp256^2 FFT.
static constexpr char kRootX[] =
    "112649224146410281873500457609690258373018840430489408729223714171582664"
    "680802";
static constexpr char kRootY[] =
    "84087994358540907695740461427818660560182168997182378749313018254450460212"
    "908";

// The block_enc of the smallest proof (circuit_maker.cc's optimize()), over
// every block_enc from 100 to 2^17.
template <class Field>
size_t best_block_enc(const Circuit<Field>& c, size_t nreq) {
  LigeroParam<Field> lp((c.ninputs - c.npub_in) + ZkCommon<Field>::pad_size(c),
                        c.nl, kRate, nreq);
  size_t best = lp.block_enc;
  size_t min_size = lp.layout(best);
  for (size_t e = 100; e <= (1 << 17); e++) {
    size_t sz = lp.layout(e);
    if (sz < min_size) {
      min_size = sz;
      best = e;
    }
  }
  return best;
}

// Each configuration: the signature field, its Reed-Solomon factory, the
// bits of its characteristic (the no-wrap bound of rsa_shape.h is
// 2^(kCharBits - 3)) and its opened columns.
struct P256Cfg {
  using Field = Fp256Base;
  using F2 = Fp2<Fp256Base>;
  using Conv = FFTExtConvolutionFactory<Fp256Base, F2>;
  using RSF = ReedSolomonFactory<Fp256Base, Conv>;
  static constexpr const char* kName = "Fp256";
  static constexpr size_t kCharBits = 256;
  static constexpr size_t kNreq = kNreqSig256;
  const Field& f;
  F2 f2;
  Conv conv;
  RSF rsf;
  P256Cfg()
      : f(p256_base),
        f2(p256_base),
        conv(p256_base, f2, f2.of_string(kRootX, kRootY), 1ull << 31),
        rsf(conv, p256_base) {}
};

struct P128Cfg {
  using Field = Fp128<true>;
  using Conv = FFTConvolutionFactory<Field>;
  using RSF = ReedSolomonFactory<Field, Conv>;
  static constexpr const char* kName = "Fp128";
  static constexpr size_t kCharBits = 128;
  static constexpr size_t kNreq = kNreqSig128;
  Field f;
  Conv conv;
  RSF rsf;
  // zk_test.cc's root of unity of order 2^32.
  P128Cfg()
      : f(),
        conv(f, f.of_string("164956748514267535023998284330560247862"),
             1ull << 32),
        rsf(conv, f) {}
};

struct CircuitStats {
  size_t depth, nl, wires, terms, ninput, npub;
};

template <class Field>
CircuitStats stats_of(const QuadCircuit<Field>& Q, const Circuit<Field>& c) {
  return {Q.depth_, c.nl, Q.nwires_, Q.nquad_terms_, Q.ninput_, c.npub_in};
}

gf2k generate_mac_key(Transcript& t) {
  f_128 gf;
  uint8_t buf[f_128::kBytes];
  t.bytes(buf, f_128::kBytes);
  return gf.of_bytes_field(buf).value();
}

// ------------------------------------------------------------ circuits --

// Hash circuit inputs: [1][mac0][mac1][a_v] | e (256 bits), the message,
// the SHA-256 block witnesses | (full field) a_p[2].
constexpr size_t kHashMacIndex = 1;

std::unique_ptr<Circuit<f_128>> make_hash_circuit(size_t n, const f_128& Fs,
                                                  CircuitStats& st) {
  using CB = CompilerBackend<f_128>;
  using LC = Logic<f_128, CB>;
  using EltW = LC::EltW;
  using v256 = LC::v256;
  using MacGF2 = MACGF2<CB, BitPlucker<LC, kMACPluckerBits>>;
  QuadCircuit<f_128> Q(Fs);
  const CB cbk(&Q);
  const LC lc(&cbk, Fs);
  EltW mac[3];
  for (auto& m : mac) m = lc.eltw_input();
  Q.private_input();
  v256 e = lc.template vinput<256>();
  RsaHash<LC>::Witness w(n);
  w.input(lc);
  Q.begin_full_field();
  MacGF2::Witness macw;
  macw.input(lc);
  RsaHash<LC> h(lc);
  h.assert_message_hash(e, w);
  MacGF2 mc(lc);
  mc.verify_mac(&mac[0], mac[2], e, macw);
  auto c = Q.mkcircuit(1);
  st = stats_of(Q, *c);
  return c;
}

// Signature circuit inputs: [1][N: L limbs][mac0, mac1, a_v: 128 bits
// each] | the MAC witness, x, q, carries.
template <class Field, size_t LOGN, bool PLUCK>
std::unique_ptr<Circuit<Field>> make_sig_circuit(const RsaShape& sh,
                                                 const Field& F,
                                                 CircuitStats& st) {
  using CB = CompilerBackend<Field>;
  using LC = Logic<Field, CB>;
  using EltW = typename LC::EltW;
  using v128 = typename LC::v128;
  QuadCircuit<Field> Q(F);
  const CB cbk(&Q);
  const LC lc(&cbk, F);
  std::vector<EltW> N(sh.L);
  for (auto& x : N) x = lc.eltw_input();
  v128 mac[3];
  for (auto& m : mac) m = lc.template vinput<128>();
  Q.private_input();
  typename RsaSignature<LC, LOGN, PLUCK>::Witness w;
  w.input(lc, sh);
  RsaSignature<LC, LOGN, PLUCK> rs(lc, sh);
  rs.assert_signature(N, mac, mac[2], w);
  auto c = Q.mkcircuit(1);
  st = stats_of(Q, *c);
  return c;
}

// ------------------------------------------------------------- systems --

struct Trial {
  double witness, h_commit, s_commit, mac, h_prove, s_prove, serialize;
  double v_read, v_h, v_s;
  size_t bytes, h_bytes, s_bytes;
  bool prover_ok, verified;
};

const char* range_name(bool pluck) { return pluck ? "pluck" : "vanish"; }

template <class Cfg, size_t LOGN, bool PLUCK>
struct System {
  using Field = typename Cfg::Field;
  using Elt = typename Field::Elt;
  const Cfg& cfg;
  const f_128 Fs;
  const RSFh rsf_h;
  // n_m: the relation's maximum message length.
  size_t n;
  RsaShape sh;
  std::unique_ptr<Circuit<f_128>> ch;
  std::unique_ptr<Circuit<Field>> cs;
  CircuitStats st_h, st_s;
  // The hash circuit's opened columns at this message length.
  size_t nreq_h;
  size_t be_h, be_s;
  double compile_h_ms, compile_s_ms;

  System(const Cfg& c, size_t msg_len, size_t w)
      : cfg(c), Fs(), rsf_h(Fs), n(msg_len), nreq_h(hash_nreq(msg_len)) {
    sh = RsaShape::derive(w, Cfg::kCharBits, LOGN);
    auto t0 = Clock::now();
    ch = make_hash_circuit(n, Fs, st_h);
    compile_h_ms = ms_since(t0);
    t0 = Clock::now();
    cs = make_sig_circuit<Field, LOGN, PLUCK>(sh, cfg.f, st_s);
    compile_s_ms = ms_since(t0);
    be_h = best_block_enc(*ch, nreq_h);
    be_s = best_block_enc(*cs, Cfg::kNreq);
  }

  size_t sig_mac_index() const { return 1 + sh.L; }

  // Fills both witnesses (MAC tags and a_v zero) for the message msg (of
  // any length up to n_m) and returns a_p. A nonnegative flip_digest_bit
  // flips that bit of D (little-endian) in wt, so the signature circuit's
  // digest bits and the tags computed from wt are those of the flipped
  // digest. A nonnegative nb_override replaces the block count, and a
  // nonnegative set_byte sets that byte of the padded buffer to 1. A
  // non-null raw replaces the buffer by raw (64 n_m-block bytes, hashed
  // as it is, without padding), with the digest D its chaining value at
  // block nb_override (the circuit-level padding tests).
  bool fill(Dense<f_128>& Wh, Dense<Field>& Ws,
            const std::vector<uint8_t>& msg, const uint8_t* sig,
            const uint8_t* nmod, gf2k ap[2], RsaWitness& wt,
            SecureRandomEngine& rng, int flip_digest_bit = -1,
            int nb_override = -1, int set_byte = -1,
            const std::vector<uint8_t>* raw = nullptr) {
    const Field& F = cfg.f;
    wt = rsa_witness(sh, msg.data(), msg.size(), sig, nmod);
    if (flip_digest_bit >= 0) {
      wt.d_le[flip_digest_bit / 8] ^= uint8_t(1u << (flip_digest_bit % 8));
    }
    MACReference<f_128> mac_ref;
    mac_ref.sample(ap, 2, &rng);

    // The relation's nb_max blocks: the padded message, then zeros
    // (mdoc_witness.h's use of transform_and_witness_message), and the
    // message's block count nb.
    const size_t nb_max = rsa_sha_blocks(n);
    std::vector<uint8_t> in(64 * nb_max);
    std::vector<FlatSHA256Witness::BlockWitness> bw(nb_max);
    uint8_t numb;
    FlatSHA256Witness::transform_and_witness_message(
        msg.size(), msg.data(), nb_max, numb, in.data(), bw.data());
    if (nb_override >= 0) numb = uint8_t(nb_override);
    if (set_byte >= 0) in[set_byte] = 1;
    if (raw != nullptr) {
      check(raw->size() == in.size() && numb >= 1 && numb <= nb_max,
            "raw buffer");
      in = *raw;
      static const uint32_t kIv[8] = {0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u,
                                      0xa54ff53au, 0x510e527fu, 0x9b05688cu,
                                      0x1f83d9abu, 0x5be0cd19u};
      const uint32_t* H = kIv;
      for (size_t b = 0; b < nb_max; ++b) {
        uint32_t words[16];
        for (size_t i = 0; i < 16; ++i) {
          const uint8_t* p = &in[64 * b + 4 * i];
          words[i] = (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16) |
                     (uint32_t(p[2]) << 8) | uint32_t(p[3]);
        }
        FlatSHA256Witness::transform_and_witness_block(
            words, H, bw[b].outw, bw[b].oute, bw[b].outa, bw[b].h1);
        H = bw[b].h1;
      }
      // D little-endian: word 7's low byte first.
      for (size_t j = 0; j < 8; ++j) {
        for (size_t q = 0; q < 4; ++q) {
          wt.d_le[4 * (7 - j) + q] = uint8_t(bw[numb - 1].h1[j] >> (8 * q));
        }
      }
    }

    DenseFiller<f_128> hf(Wh);
    hf.push_back(Fs.one());
    for (size_t i = 0; i < 3; ++i) hf.push_back(Fs.zero());
    for (size_t i = 0; i < 32; ++i) hf.push_back(wt.d_le[i], 8, Fs);
    hf.push_back(numb, 8, Fs);
    for (uint8_t x : in) hf.push_back(x, 8, Fs);
    BitPluckerEncoder<f_128, kRsaSHAPluckerBits> enc(Fs);
    for (const auto& b : bw) {
      for (size_t k = 0; k < 48; ++k) hf.push_back(enc.mkpacked_v32(b.outw[k]));
      for (size_t k = 0; k < 64; ++k) {
        hf.push_back(enc.mkpacked_v32(b.oute[k]));
        hf.push_back(enc.mkpacked_v32(b.outa[k]));
      }
      for (size_t k = 0; k < 8; ++k) hf.push_back(enc.mkpacked_v32(b.h1[k]));
    }
    MacGF2Witness mgw;
    mgw.compute_witness(ap);
    mgw.fill_witness(hf);
    check(hf.size() == ch->ninputs, "hash witness size");

    DenseFiller<Field> sf(Ws);
    sf.push_back(F.one());
    for (const Elt& v : rsa_modulus_limbs(sh, nmod, F)) sf.push_back(v);
    for (size_t i = 0; i < 3 * 128; ++i) sf.push_back(F.zero());
    MacWitness<Field> mw(F, Fs);
    mw.compute_witness(ap, wt.d_le);
    mw.fill_witness(sf);
    for (const auto& row : wt.x_)
      for (const auto& v : row) rsa_fill_bits<Field, LOGN, PLUCK>(sf, v, F);
    for (const auto& row : wt.q_)
      for (const auto& v : row) rsa_fill_bits<Field, LOGN, PLUCK>(sf, v, F);
    for (const auto& row : wt.c_)
      for (const auto& v : row) rsa_fill_bits<Field, LOGN, PLUCK>(sf, v, F);
    check(sf.size() == cs->ninputs, "signature witness size");
    return wt.satisfied;
  }

  // Proves for the key pmod and verifies against vmod; tamper 1 flips a
  // bit of the first MAC tag in the proof, tamper 2 a byte in the middle
  // of the signature circuit's proof. Returns the timings.
  Trial run(const std::vector<uint8_t>& msg, const uint8_t* sig,
            const uint8_t* pmod,
            const uint8_t* vmod, int tamper = 0) {
    const Field& F = cfg.f;
    Trial tr{};
    SecureRandomEngine rng;
    auto Wh = Dense<f_128>(1, ch->ninputs);
    auto Ws = Dense<Field>(1, cs->ninputs);
    gf2k ap[2];
    RsaWitness wt;
    auto t0 = Clock::now();
    fill(Wh, Ws, msg, sig, pmod, ap, wt, rng);
    tr.witness = ms_since(t0);

    Transcript tp(kSeed, sizeof(kSeed), kTranscriptVersion);
    ZkProof<f_128> hz(*ch, kRate, nreq_h, be_h);
    ZkProof<Field> sz(*cs, kRate, Cfg::kNreq, be_s);
    ZkProver<f_128, RSFh> hp(*ch, Fs, rsf_h);
    ZkProver<Field, typename Cfg::RSF> sp(*cs, F, cfg.rsf);
    t0 = Clock::now();
    hp.commit(hz, Wh, tp, rng);
    tr.h_commit = ms_since(t0);
    t0 = Clock::now();
    sp.commit(sz, Ws, tp, rng);
    tr.s_commit = ms_since(t0);

    t0 = Clock::now();
    gf2k av = generate_mac_key(tp);
    gf2k macs[2];
    MACReference<f_128> mac_ref;
    mac_ref.compute(macs, av, ap, wt.d_le);
    {
      size_t si = sig_mac_index(), hi = kHashMacIndex;
      const gf2k tags[3] = {macs[0], macs[1], av};
      for (const gf2k& m : tags) {
        for (size_t j = 0; j < f_128::kBits; ++j) {
          Ws.v_[si++] = m[j] ? F.one() : F.zero();
        }
        Wh.v_[hi++] = m;
      }
    }
    tr.mac = ms_since(t0);

    t0 = Clock::now();
    const bool ok_h = hp.prove(hz, Wh, tp);
    tr.h_prove = ms_since(t0);
    t0 = Clock::now();
    const bool ok_s = sp.prove(sz, Ws, tp);
    tr.s_prove = ms_since(t0);
    tr.prover_ok = ok_h && ok_s;
    if (!tr.prover_ok) return tr;

    // [2 MACs][hash proof][signature proof], as mdoc_zk.cc.
    t0 = Clock::now();
    std::vector<uint8_t> buf;
    uint8_t tmp[f_128::kBytes];
    for (const gf2k& m : macs) {
      Fs.to_bytes_field(tmp, m);
      buf.insert(buf.end(), tmp, tmp + f_128::kBytes);
    }
    size_t b0 = buf.size();
    hz.write(buf, Fs);
    size_t b1 = buf.size();
    sz.write(buf, F);
    tr.serialize = ms_since(t0);
    tr.bytes = buf.size();
    tr.h_bytes = b1 - b0;
    tr.s_bytes = buf.size() - b1;

    if (tamper == 1) buf[0] ^= 1;
    if (tamper == 2) buf[b1 + (buf.size() - b1) / 2] ^= 1;
    tr.verified = verify(buf, vmod, tr);
    return tr;
  }

  bool verify(const std::vector<uint8_t>& proof, const uint8_t* vmod,
              Trial& tr) {
    const Field& F = cfg.f;
    if (!rsa_key_ok(vmod)) return false;
    auto t0 = Clock::now();
    ReadBuffer rb(proof);
    gf2k macs[2];
    for (auto& m : macs) {
      auto v = Fs.of_bytes_field(rb.next(f_128::kBytes));
      if (!v.has_value()) return false;
      m = v.value();
    }
    ZkProof<f_128> hz(*ch, kRate, nreq_h, be_h);
    ZkProof<Field> sz(*cs, kRate, Cfg::kNreq, be_s);
    if (!hz.read(rb, Fs) || !sz.read(rb, F) || rb.remaining() != 0) {
      return false;
    }
    tr.v_read = ms_since(t0);

    t0 = Clock::now();
    ZkVerifier<f_128, RSFh> hv(*ch, rsf_h, kRate, nreq_h, be_h, Fs);
    Transcript tv(kSeed, sizeof(kSeed), kTranscriptVersion);
    hv.recv_commitment(hz, tv);
    double vh = ms_since(t0);
    t0 = Clock::now();
    ZkVerifier<Field, typename Cfg::RSF> sv(*cs, cfg.rsf, kRate, Cfg::kNreq,
                                            be_s, F);
    sv.recv_commitment(sz, tv);
    gf2k av = generate_mac_key(tv);
    // The verifier's public inputs.
    auto ph = Dense<f_128>(1, ch->npub_in);
    auto ps = Dense<Field>(1, cs->npub_in);
    DenseFiller<f_128> hf(ph);
    DenseFiller<Field> sf(ps);
    hf.push_back(Fs.one());
    sf.push_back(F.one());
    for (const Elt& v : rsa_modulus_limbs(sh, vmod, F)) sf.push_back(v);
    const gf2k tags[3] = {macs[0], macs[1], av};
    for (const gf2k& m : tags) {
      hf.push_back(m);
      fill_gf2k<f_128, Field>(m, sf, F);
    }
    check(hf.size() == ch->npub_in && sf.size() == cs->npub_in,
          "public input size");
    double vs = ms_since(t0);
    t0 = Clock::now();
    bool ok_h = hv.verify(hz, ph, tv);
    tr.v_h = vh + ms_since(t0);
    t0 = Clock::now();
    bool ok_s = sv.verify(sz, ps, tv);
    tr.v_s = vs + ms_since(t0);
    return ok_h && ok_s;
  }

  // The hash circuit's tableau at t opened columns: block_enc by the
  // search at t, N = block_enc - (2k - 1) query positions, k = block.
  void print_hash_tableau(size_t t) const {
    const size_t e = best_block_enc(*ch, t);
    ZkProof<f_128> hz(*ch, kRate, t, e);
    const size_t k = hz.param.block;
    printf("TABLEAU circuit=hash n_m=%zu t=%zu block_enc=%zu block=%zu N=%zu "
           "k=%zu\n",
           n, t, e, k, e - (2 * k - 1), k);
    fflush(stdout);
  }

  // The signature circuit's tableau at t opened columns, as the hash's.
  void print_sig_tableau(size_t t) const {
    const size_t e = best_block_enc(*cs, t);
    ZkProof<Field> sz(*cs, kRate, t, e);
    const size_t k = sz.param.block;
    printf("TABLEAU circuit=sig field=%s t=%zu block_enc=%zu block=%zu N=%zu "
           "k=%zu\n",
           Cfg::kName, t, e, k, e - (2 * k - 1), k);
    fflush(stdout);
  }

  void print_plan(const char* tag) const {
    ZkProof<f_128> hz(*ch, kRate, nreq_h, be_h);
    ZkProof<Field> sz(*cs, kRate, Cfg::kNreq, be_s);
    printf(
        "PLAN %s field=%s msg=%zu range=%s w=%zu logn=%zu L=%zu Lq=%zu "
        "K=%zu k=%zu G=%zu bc=%zu log2V=%.2Lf committed_bits=%zu "
        "committed_digits=%zu\n",
        tag, Cfg::kName, n, range_name(PLUCK), sh.w, LOGN, sh.L, sh.Lq, sh.K, sh.k, sh.G, sh.bc,
        sh.log2_v, sh.committed_bits(), sh.committed_bits() / LOGN);
    printf(
        "CIRCUIT %s field=%s msg=%zu range=%s w=%zu logn=%zu circuit=hash "
        "nreq=%zu depth=%zu "
        "layers=%zu wires=%zu terms=%zu inputs=%zu public=%zu block_enc=%zu "
        "block=%zu nrow=%zu compile_ms=%.1f\n",
        tag, Cfg::kName, n, range_name(PLUCK), sh.w, LOGN, nreq_h, st_h.depth, st_h.nl, st_h.wires,
        st_h.terms, st_h.ninput, st_h.npub, be_h, hz.param.block,
        hz.param.nrow, compile_h_ms);
    printf(
        "CIRCUIT %s field=%s msg=%zu range=%s w=%zu logn=%zu circuit=sig "
        "nreq=%zu depth=%zu "
        "layers=%zu wires=%zu terms=%zu inputs=%zu public=%zu block_enc=%zu "
        "block=%zu nrow=%zu compile_ms=%.1f\n",
        tag, Cfg::kName, n, range_name(PLUCK), sh.w, LOGN,
        Cfg::kNreq, st_s.depth, st_s.nl, st_s.wires,
        st_s.terms, st_s.ninput, st_s.npub, be_s, sz.param.block,
        sz.param.nrow, compile_s_ms);
    fflush(stdout);
  }

  void print_trial(const char* tag, size_t rep, const Trial& t) const {
    printf(
        "TRIAL %s field=%s msg=%zu range=%s w=%zu logn=%zu rep=%zu "
        "witness=%.3f "
        "h_commit=%.3f s_commit=%.3f mac=%.3f h_prove=%.3f s_prove=%.3f "
        "prover=%.3f serialize=%.3f v_read=%.3f v_h=%.3f v_s=%.3f "
        "verify=%.3f bytes=%zu h_bytes=%zu s_bytes=%zu ok=%d\n",
        tag, Cfg::kName, n, range_name(PLUCK), sh.w, LOGN, rep, t.witness, t.h_commit,
        t.s_commit, t.mac, t.h_prove, t.s_prove,
        t.h_commit + t.s_commit + t.mac + t.h_prove + t.s_prove, t.serialize,
        t.v_read, t.v_h, t.v_s, t.v_h + t.v_s, t.bytes, t.h_bytes, t.s_bytes,
        int(t.prover_ok && t.verified));
    fflush(stdout);
  }
};

std::vector<uint8_t> message(size_t n) {
  std::vector<uint8_t> m(n);
  for (size_t j = 0; j < n; ++j) m[j] = uint8_t((31 * j + 7) % 256);
  return m;
}
// The signatures of message(n) for the lengths rsa_vectors.h covers.
const uint8_t* signature(size_t n) {
  switch (n) {
    case 13:
      return vec::kSig13;
    case 64:
      return vec::kSig64;
    case 1000:
      return vec::kSig1000;
    case 2048:
      return vec::kSig2048;
  }
  check(false, "no test vector at this message length");
  return nullptr;
}

// ---------------------------------------------------------------- modes --

int failures = 0;
void expect(bool c, const std::string& what) {
  printf("%s %s\n", c ? "PASS" : "FAIL", what.c_str());
  fflush(stdout);
  if (!c) ++failures;
}

template <class Cfg, size_t LOGN, bool PLUCK>
void test_system(const Cfg& cfg, size_t n, size_t w) {
  System<Cfg, LOGN, PLUCK> sys(cfg, n, w);
  sys.print_plan("test");
  const std::string nm = std::string(Cfg::kName) + " msg=" +
                         std::to_string(n) + " w=" + std::to_string(w) +
                         " logn=" + std::to_string(LOGN) + " " +
                         range_name(PLUCK) + ": ";
  const auto m = message(n);
  const uint8_t* s = signature(n);
  {
    // The host witness reproduces EM: x_16 x_0 = q N + EM.
    RsaWitness wt = rsa_witness(sys.sh, m.data(), n, s, vec::kN);
    expect(wt.satisfied, nm + "honest witness satisfied");
    const uint8_t* em = n == 64 ? vec::kEm64 : vec::kEm2048;
    expect(memcmp(wt.digest, em + 224, 32) == 0, nm + "digest = EM tail");
  }
  Trial t = sys.run(m, s, vec::kN, vec::kN);
  expect(t.prover_ok && t.verified, nm + "honest proof verifies");
  {
    std::vector<uint8_t> s2(s, s + 256);
    s2[100] ^= 0x10;
    expect(!rsa_witness(sys.sh, m.data(), n, s2.data(), vec::kN).satisfied,
           nm + "tampered s: no witness");
    Trial u = sys.run(m, s2.data(), vec::kN, vec::kN);
    expect(!u.prover_ok, nm + "tampered s: prover rejects (circuit unsatisfied)");
  }
  {
    auto m2 = m;
    m2[3] ^= 1;
    expect(!rsa_witness(sys.sh, m2.data(), n, s, vec::kN).satisfied,
           nm + "tampered m: no witness");
    Trial u = sys.run(m2, s, vec::kN, vec::kN);
    expect(!u.prover_ok, nm + "tampered m: prover rejects (circuit unsatisfied)");
  }
  {
    Trial u = sys.run(m, s, vec::kN2, vec::kN2);
    expect(!u.prover_ok, nm + "prover on N2: prover rejects (circuit unsatisfied)");
    Trial x = sys.run(m, s, vec::kN, vec::kN2);
    expect(x.prover_ok && !x.verified,
           nm + "verifier on N2: honest proof for N rejected");
  }
  {
    Trial u = sys.run(m, s, vec::kN, vec::kN, 1);
    expect(u.prover_ok && !u.verified, nm + "MAC tag flipped: rejected");
    Trial v = sys.run(m, s, vec::kN, vec::kN, 2);
    expect(v.prover_ok && !v.verified,
           nm + "signature proof byte flipped: rejected");
  }
  {
    // A message shorter than n_m: its private block count is below the
    // buffer's.
    const size_t len = n == 64 ? 13 : 1000;
    Trial u = sys.run(message(len), signature(len), vec::kN, vec::kN);
    expect(u.prover_ok && u.verified,
           nm + "message of " + std::to_string(len) +
               " bytes (private length below n_m): verifies");
  }
}

// ------------------------------------------- circuit-level witness tests --

// Whether every output of c (the assert0 wires) is zero at the inputs W.
template <class Field>
bool satisfied(const Circuit<Field>& c, const Dense<Field>& W,
               const Field& F) {
  typename ProverLayers<Field>::inputs in;
  ProverLayers<Field> pl(F);
  auto V = pl.eval_circuit(&in, &c, W.clone(), F);
  if (V == nullptr) return false;
  for (size_t i = 0; i < V->n1_; ++i) {
    if (V->v_[i] != F.zero()) return false;
  }
  return true;
}

// Signature-circuit witnesses changed in one committed element, evaluated
// on the circuit (no proof): each change must leave an assertion nonzero.
// The tags are those of a fixed a_v, so the MAC check holds for the
// digest the witness carries.
template <class Cfg, size_t LOGN, bool PLUCK>
struct WitnessTests {
  using Field = typename Cfg::Field;
  using Elt = typename Field::Elt;
  System<Cfg, LOGN, PLUCK>& sys;
  const Field& F;
  const BitPluckerEncoder<Field, (LOGN > 1 ? LOGN : 2)> enc;

  explicit WitnessTests(System<Cfg, LOGN, PLUCK>& s)
      : sys(s), F(s.cfg.f), enc(s.cfg.f) {}

  // The signature witness for (msg, sig, N) with the tags under a_v =
  // 12345; flip_digest_bit as System::fill.
  void build(Dense<Field>& Ws, const std::vector<uint8_t>& msg,
             const uint8_t* sig, int flip_digest_bit = -1) {
    auto Wh = Dense<f_128>(1, sys.ch->ninputs);
    gf2k ap[2];
    RsaWitness wt;
    SecureRandomEngine rng;
    sys.fill(Wh, Ws, msg, sig, vec::kN, ap, wt, rng, flip_digest_bit);
    gf2k av = sys.Fs.of_scalar(12345);
    gf2k macs[2];
    MACReference<f_128> mac_ref;
    mac_ref.compute(macs, av, ap, wt.d_le);
    size_t si = sys.sig_mac_index();
    const gf2k tags[3] = {macs[0], macs[1], av};
    for (const gf2k& m : tags) {
      for (size_t j = 0; j < f_128::kBits; ++j) {
        Ws.v_[si++] = m[j] ? F.one() : F.zero();
      }
    }
  }

  // The committed element of digit value v.
  Elt digit(uint64_t v) const {
    if constexpr (LOGN > 1 && PLUCK) {
      return enc.encode(v);
    } else {
      return F.of_scalar(v);
    }
  }
  // Replaces the digit at i by another allowed digit.
  void change_digit(Dense<Field>& W, size_t i) const {
    W.v_[i] = W.v_[i] == digit(0) ? digit(1) : digit(0);
  }
  bool allowed(const Elt& e) const {
    for (uint64_t d = 0; d < (uint64_t(1) << LOGN); ++d) {
      if (e == digit(d)) return true;
    }
    return false;
  }

  size_t per_limb() const { return sys.sh.w / LOGN; }
  size_t per_carry() const { return sys.sh.bc / LOGN; }
  // The digits are the last inputs: x, then q, then the carries.
  size_t off_x() const {
    return sys.cs->ninputs -
           kRsaRows * ((sys.sh.L + sys.sh.Lq) * per_limb() +
                       (sys.sh.G - 1) * per_carry());
  }
  size_t off_q() const { return off_x() + kRsaRows * sys.sh.L * per_limb(); }
  size_t off_c() const { return off_q() + kRsaRows * sys.sh.Lq * per_limb(); }
};

template <class Cfg, size_t LOGN, bool PLUCK>
void witness_tests(const Cfg& cfg, size_t w) {
  using Field = typename Cfg::Field;
  using Elt = typename Field::Elt;
  System<Cfg, LOGN, PLUCK> sys(cfg, 64, w);
  WitnessTests<Cfg, LOGN, PLUCK> T(sys);
  const Field& F = cfg.f;
  const Circuit<Field>& C = *sys.cs;
  const auto m = message(64);
  const uint8_t* s = vec::kSig64;
  const std::string nm = std::string(Cfg::kName) + " w=" + std::to_string(w) +
                         " logn=" + std::to_string(LOGN) + " " +
                         range_name(PLUCK) + " circuit: ";

  auto base = Dense<Field>(1, C.ninputs);
  T.build(base, m, s);
  expect(satisfied(C, base, F), nm + "honest witness satisfied");
  {
    // Row 0, carry 3, digit 1.
    auto W = base.clone();
    T.change_digit(*W, T.off_c() + 3 * T.per_carry() + 1);
    expect(!satisfied(C, *W, F), nm + "carry digit changed: unsatisfied");
  }
  {
    // Row 5, quotient limb 0, low digit.
    auto W = base.clone();
    T.change_digit(*W, T.off_q() + 5 * sys.sh.Lq * T.per_limb());
    expect(!satisfied(C, *W, F), nm + "quotient digit changed: unsatisfied");
  }
  {
    // x_1, limb 3, low digit.
    auto W = base.clone();
    T.change_digit(*W, T.off_x() + 1 * sys.sh.L * T.per_limb() +
                           3 * T.per_limb());
    expect(!satisfied(C, *W, F), nm + "x_1 limb changed: unsatisfied");
  }
  // x_1's digit 7 set to elements outside the allowed set: 2^LOGN (the
  // next integer), 2^20, 977 and -1.
  const Elt off_set[4] = {F.of_scalar(uint64_t(1) << LOGN),
                          F.of_scalar(uint64_t(1) << 20), F.of_scalar(977),
                          F.negf(F.one())};
  const char* off_name[4] = {"2^logn", "2^20", "977", "-1"};
  for (size_t v = 0; v < 4; ++v) {
    if (T.allowed(off_set[v])) {
      printf("INFO %s%s is an allowed digit encoding, not tested\n",
             nm.c_str(), off_name[v]);
      continue;
    }
    auto W = base.clone();
    W->v_[T.off_x() + 1 * sys.sh.L * T.per_limb() + 7] = off_set[v];
    expect(!satisfied(C, *W, F),
           nm + "digit " + off_name[v] + ": unsatisfied");
  }
  {
    // Digest bit 10 flipped in the digest bits only, with the tags of the
    // honest digest: the MAC check fails.
    auto W = Dense<Field>(1, C.ninputs);
    T.build(W, m, s);
    auto Wf = Dense<Field>(1, C.ninputs);
    T.build(Wf, m, s, 10);
    const size_t si = sys.sig_mac_index();
    for (size_t j = 0; j < 3 * f_128::kBits; ++j) {
      Wf.v_[si + j] = W.v_[si + j];
    }
    expect(!satisfied(C, Wf, F),
           nm + "digest bit flipped, honest tags: unsatisfied");
  }
  {
    // Digest bit 10 flipped with the tags recomputed for the flipped
    // digest: the MAC check holds and the row x_16 x_0 = q N + EM fails.
    auto W = Dense<Field>(1, C.ninputs);
    T.build(W, m, s, 10);
    expect(!satisfied(C, W, F),
           nm + "digest bit flipped, tags recomputed: unsatisfied");
  }
}

// Hash-circuit witnesses changed in the private length's encoding,
// evaluated on the circuit (no proof): n_m = 64 (two blocks) and a 13-byte
// message (nb = 1), the tags under a_v = 12345. The hash circuit does not
// depend on the signature field or layout.
template <class Cfg, size_t LOGN, bool PLUCK>
void hash_witness_tests(const Cfg& cfg, size_t w) {
  System<Cfg, LOGN, PLUCK> sys(cfg, 64, w);
  const auto m = message(13);
  const uint8_t* s = signature(13);
  const std::string nm = "hash circuit n_m=64 msg=13: ";
  auto holds = [&](int nb_override, int set_byte,
                   const std::vector<uint8_t>* raw = nullptr) {
    auto Wh = Dense<f_128>(1, sys.ch->ninputs);
    auto Ws = Dense<typename Cfg::Field>(1, sys.cs->ninputs);
    gf2k ap[2];
    RsaWitness wt;
    SecureRandomEngine rng;
    sys.fill(Wh, Ws, m, s, vec::kN, ap, wt, rng, -1, nb_override, set_byte,
             raw);
    gf2k av = sys.Fs.of_scalar(12345);
    gf2k macs[2];
    MACReference<f_128> mac_ref;
    mac_ref.compute(macs, av, ap, wt.d_le);
    size_t hi = kHashMacIndex;
    const gf2k tags[3] = {macs[0], macs[1], av};
    for (const gf2k& t : tags) Wh.v_[hi++] = t;
    return satisfied(*sys.ch, Wh, sys.Fs);
  };
  expect(holds(-1, -1), nm + "honest witness (nb = 1 of 2) satisfied");
  expect(!holds(-1, 64 + 5), nm + "nonzero byte past block nb: unsatisfied");
  expect(!holds(2, -1), nm + "nb = 2: unsatisfied");
  expect(!holds(0, -1), nm + "nb = 0: unsatisfied");
  expect(!holds(-1, 20), nm + "byte of block nb changed: unsatisfied");
  // Buffers hashed as they are, the digest their chaining value at block
  // nb, so only the padding check can refuse them. The honest padded
  // buffer of the 13-byte message first (it must hold), then three with
  // bad padding.
  std::vector<uint8_t> buf(128);
  std::vector<FlatSHA256Witness::BlockWitness> bw(2);
  uint8_t numb;
  FlatSHA256Witness::transform_and_witness_message(13, m.data(), 2, numb,
                                                   buf.data(), bw.data());
  expect(holds(1, -1, &buf), nm + "honest buffer hashed raw: satisfied");
  auto bad = buf;
  // The length field: 13 bytes is 104 bits; 112 claims 14.
  bad[63] = 112;
  expect(!holds(1, -1, &bad),
         nm + "length field 14 bytes (digest consistent): unsatisfied");
  bad = buf;
  bad[13] = 0;
  expect(!holds(1, -1, &bad),
         nm + "0x80 marker cleared (digest consistent): unsatisfied");
  bad = buf;
  bad[30] = 1;
  expect(!holds(1, -1, &bad),
         nm + "nonzero byte after the marker (digest consistent): unsatisfied");
  // A buffer of two blocks whose second block is a full block of padding
  // that the 13-byte message does not need: nb = 2, length field 104.
  bad.assign(128, 0);
  for (size_t i = 0; i < 13; ++i) bad[i] = m[i];
  bad[13] = 0x80;
  bad[127] = 104;
  expect(!holds(2, -1, &bad),
         nm + "padding one block too long (digest consistent): unsatisfied");
}

// The default layout: digits of RSA_LOGN* bits range checked by the
// vanishing polynomial (RSA_PLUCK* = 0) or BitPlucker (RSA_PLUCK* = 1),
// limbs of RSA_W* bits. The defaults are per field.
#ifndef RSA_LOGN128
#define RSA_LOGN128 4
#endif
#ifndef RSA_W128
#define RSA_W128 16
#endif
#ifndef RSA_PLUCK128
#define RSA_PLUCK128 0
#endif
#ifndef RSA_LOGN256
#define RSA_LOGN256 4
#endif
#ifndef RSA_W256
#define RSA_W256 32
#endif
#ifndef RSA_PLUCK256
#define RSA_PLUCK256 0
#endif
constexpr size_t kLogn128 = RSA_LOGN128, kW128 = RSA_W128;
constexpr size_t kLogn256 = RSA_LOGN256, kW256 = RSA_W256;
constexpr bool kPluck128 = RSA_PLUCK128, kPluck256 = RSA_PLUCK256;

// The layouts of the circuit-level tests besides the default: the
// BitPlucker layout the vanishing polynomial replaced, and each digit width
// of the vanishing polynomial at its fastest limb width per field.
struct TestLayout {
  bool pluck;
  size_t logn, w128, w256;
};
constexpr TestLayout kTestLayouts[] = {
    {true, 2, 16, 32},
    {false, 2, 16, 32},
    {false, 3, 18, 33},
    {false, 4, 16, 32},
};

// Calls f(integral_constant<size_t, LOGN>, bool_constant<PLUCK>) for the
// runtime layout; 2 if there is no such layout.
template <class F>
int with_layout(bool pluck, size_t logn, F&& f) {
  using std::false_type;
  using std::integral_constant;
  using std::true_type;
  if (!pluck) {
    switch (logn) {
      case 1:
        return f(integral_constant<size_t, 1>{}, false_type{});
      case 2:
        return f(integral_constant<size_t, 2>{}, false_type{});
      case 3:
        return f(integral_constant<size_t, 3>{}, false_type{});
      case 4:
        return f(integral_constant<size_t, 4>{}, false_type{});
    }
  } else {
    switch (logn) {
      case 2:
        return f(integral_constant<size_t, 2>{}, true_type{});
      case 3:
        return f(integral_constant<size_t, 3>{}, true_type{});
      case 4:
        return f(integral_constant<size_t, 4>{}, true_type{});
    }
  }
  return 2;
}

// longfellow-baselines: one System as a worker of common/bench.py
// (common/bench_worker.h).  commit = hash + signature commit; prove = the
// MAC step + hash + signature prove; verify = v_h + v_s, as print_trial
// sums them.
template <class Cfg, size_t LOGN, bool PLUCK>
int serve_system(const Cfg& cfg, size_t n, size_t w) {
  System<Cfg, LOGN, PLUCK> sys(cfg, n, w);
  sys.print_plan("worker");
  const auto m = message(n);
  const uint8_t* s = signature(n);
  lfb::info({{"field", Cfg::kName},
             {"msg", std::to_string(n)},
             {"range", range_name(PLUCK)},
             {"w", std::to_string(w)},
             {"logn", std::to_string(LOGN)},
             {"h_nreq", std::to_string(sys.nreq_h)},
             {"s_nreq", std::to_string(Cfg::kNreq)}});
  lfb::serve([&]() {
    const Trial t = sys.run(m, s, vec::kN, vec::kN);
    lfb::Trial T;
    T.commit_ms = t.h_commit + t.s_commit;
    T.prove_ms = t.mac + t.h_prove + t.s_prove;
    T.verify_ms = t.v_h + t.v_s;
    T.proof_bytes = t.bytes;
    T.ok = t.prover_ok && t.verified;
    T.add("witness", t.witness);
    T.add("h_commit", t.h_commit);
    T.add("s_commit", t.s_commit);
    T.add("mac", t.mac);
    T.add("h_prove", t.h_prove);
    T.add("s_prove", t.s_prove);
    T.add("serialize", t.serialize);
    T.add("v_read", t.v_read);
    T.add("v_h", t.v_h);
    T.add("v_s", t.v_s);
    T.add("h_bytes", double(t.h_bytes));
    T.add("s_bytes", double(t.s_bytes));
    return T;
  });
  return 0;
}

}  // namespace
}  // namespace proofs

int main(int argc, char** argv) {
  using namespace proofs;
  set_log_level(ERROR);
  const std::string mode = argc > 1 ? argv[1] : "test";
  const size_t reps = argc > 2 ? strtoul(argv[2], nullptr, 10) : 9;
  P128Cfg c128;
  P256Cfg c256;
  if (mode == "test") {
    for (size_t n : {size_t(64), size_t(2048)}) {
      test_system<P128Cfg, kLogn128, kPluck128>(c128, n, kW128);
      test_system<P256Cfg, kLogn256, kPluck256>(c256, n, kW256);
    }
    witness_tests<P128Cfg, kLogn128, kPluck128>(c128, kW128);
    hash_witness_tests<P128Cfg, kLogn128, kPluck128>(c128, kW128);
    witness_tests<P256Cfg, kLogn256, kPluck256>(c256, kW256);
    for (const TestLayout& t : kTestLayouts) {
      const bool is_default128 =
          t.pluck == kPluck128 && t.logn == kLogn128 && t.w128 == kW128;
      const bool is_default256 =
          t.pluck == kPluck256 && t.logn == kLogn256 && t.w256 == kW256;
      with_layout(t.pluck, t.logn, [&](auto lg, auto pl) {
        constexpr size_t LOGN = decltype(lg)::value;
        constexpr bool PLUCK = decltype(pl)::value;
        if (!is_default128) witness_tests<P128Cfg, LOGN, PLUCK>(c128, t.w128);
        if (!is_default256) witness_tests<P256Cfg, LOGN, PLUCK>(c256, t.w256);
        return 0;
      });
    }
    printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
  }
  if (mode == "stats" || mode == "bench") {
    System<P128Cfg, kLogn128, kPluck128> a64(c128, 64, kW128),
        a2k(c128, 2048, kW128);
    System<P256Cfg, kLogn256, kPluck256> b64(c256, 64, kW256),
        b2k(c256, 2048, kW256);
    a64.print_plan("bench");
    a2k.print_plan("bench");
    b64.print_plan("bench");
    b2k.print_plan("bench");
    if (mode == "stats") return 0;
    const auto m64 = message(64), m2k = message(2048);
    for (size_t r = 0; r <= reps; ++r) {
      const char* tag = r == 0 ? "warmup" : "bench";
      a64.print_trial(tag, r, a64.run(m64, vec::kSig64, vec::kN,
                                      vec::kN));
      b64.print_trial(tag, r, b64.run(m64, vec::kSig64, vec::kN,
                                      vec::kN));
      a2k.print_trial(tag, r, a2k.run(m2k, vec::kSig2048, vec::kN,
                                      vec::kN));
      b2k.print_trial(tag, r, b2k.run(m2k, vec::kSig2048, vec::kN,
                                      vec::kN));
    }
    return 0;
  }
  if (mode == "plan" && argc >= 4) {
    const System<P128Cfg, kLogn128, kPluck128> sys(
        c128, strtoul(argv[2], nullptr, 10), kW128);
    for (int i = 3; i < argc; ++i) {
      sys.print_hash_tableau(strtoul(argv[i], nullptr, 10));
    }
    return 0;
  }
  if (mode == "plansig" && argc >= 4) {
    const std::string f = argv[2];
    if (f == "Fp128") {
      const System<P128Cfg, kLogn128, kPluck128> sys(c128, 64, kW128);
      for (int i = 3; i < argc; ++i) {
        sys.print_sig_tableau(strtoul(argv[i], nullptr, 10));
      }
      return 0;
    }
    if (f == "Fp256") {
      const System<P256Cfg, kLogn256, kPluck256> sys(c256, 64, kW256);
      for (int i = 3; i < argc; ++i) {
        sys.print_sig_tableau(strtoul(argv[i], nullptr, 10));
      }
      return 0;
    }
    return 2;
  }
  // worker Fp128|Fp256 MSG_BYTES [vanish|pluck LOGN W]: one layout, served
  // to common/bench.py; without the optional arguments, the field's default
  // layout.
  if (mode == "worker" && (argc == 4 || argc == 7)) {
    const std::string f = argv[2];
    const size_t n = strtoul(argv[3], nullptr, 10);
    if (n != 64 && n != 2048) return 2;
    if (f != "Fp128" && f != "Fp256") return 2;
    bool pluck = false;
    size_t logn = kLogn128, w = kW128;
    if (f == "Fp128") {
      pluck = kPluck128;
    } else {
      pluck = kPluck256;
      logn = kLogn256;
      w = kW256;
    }
    if (argc >= 7) {
      const std::string r = argv[4];
      if (r != "vanish" && r != "pluck") return 2;
      pluck = r == "pluck";
      logn = strtoul(argv[5], nullptr, 10);
      w = strtoul(argv[6], nullptr, 10);
    }
    return with_layout(pluck, logn, [&](auto lg, auto pl) {
      constexpr size_t LOGN = decltype(lg)::value;
      constexpr bool PLUCK = decltype(pl)::value;
      if (f == "Fp128") {
        return serve_system<P128Cfg, LOGN, PLUCK>(c128, n, w);
      }
      return serve_system<P256Cfg, LOGN, PLUCK>(c256, n, w);
    });
  }
  fprintf(stderr, "unknown mode %s\n", mode.c_str());
  return 2;
}
