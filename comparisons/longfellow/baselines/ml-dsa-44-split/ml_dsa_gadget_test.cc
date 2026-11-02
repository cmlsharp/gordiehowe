// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: checks of the ML-DSA baselines' gadgets on concrete
// assignments, evaluated with upstream's EvaluationBackend (every assertion
// of the circuit is evaluated; an assignment is accepted when none fails).
// Exits 0 when every case behaves as expected.
//
//  1. common/shake256_private_length.h, in GF(2^128) and in Fp24_6, at
//     prefixes of 0, 40 (Falcon's nonce), 66 (ML-DSA's tr || 0 || 0), 102
//     (the last that fits a 32-byte maximum) and 202 bytes (a full prefix
//     block), outputs of 64 and 300 bytes, MAX = 32: at every length L in
//     [0, MAX] the honest assignment is accepted and its output is
//     Sha3Reference's SHAKE256(prefix || M); a changed message byte below L,
//     the flags of length L - 1 or L + 1, and non-monotone flags are
//     rejected; a changed byte at or past L is accepted (it is not hashed).
//  2. UseHint (MLDSASplitVerify::assert_use_hint_single, upstream's gadget)
//     with and without ml_dsa_decompose_exact.h, at ML-DSA-44, -65 and -87:
//     Decompose's and UseHint's honest assignments at the interval edges
//     and at random w' are accepted by both; at w' = (2 r1 + 1) gamma2 the
//     assignment (r1 + 1, r0 = -gamma2), whose UseHint output differs from
//     FIPS 204's, is accepted by the gadget alone and rejected with the
//     exact Decompose.
//  3. SampleInBall over the 272-byte stream, at each set and 64 seeds: the
//     hash side's gadget (MLDSAHashVerify, SibBytes = 272) and the
//     monolith's (assert_sample_in_ball_stream) accept the host witness and
//     yield FIPS 204's c (upstream's reference SampleInBall); a selected
//     position moved to the next stream byte and a wrong c are rejected.

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "algebra/fp24.h"
#include "algebra/fp24_6.h"
#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_circuit.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "circuits/tests/sha3/sha3_circuit.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "circuits/tests/sha3/sha3_slicing.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "gf2k/gf2_128.h"
#include "ml_dsa_decompose_exact.h"
#include "ml_dsa_host.h"
#include "ml_dsa_monolith_verify.h"
#include "ml_dsa_sets.h"
#include "ml_dsa_split_circuit.h"
#include "ml_dsa_split_hash_circuit.h"
#include "shake256_private_length.h"

namespace proofs {
namespace {

size_t g_cases = 0, g_failures = 0;

void expect(bool got, bool want, const std::string& what) {
  ++g_cases;
  if (got != want) {
    ++g_failures;
    std::printf("FAIL %s: %s, expected %s\n", what.c_str(),
                got ? "accepted" : "rejected", want ? "accepted" : "rejected");
  }
}

template <class F>
struct Eval {
  using BK = EvaluationBackend<F>;
  using LC = Logic<F, BK>;
  const F& f;
  BK bk;
  LC lc;
  explicit Eval(const F& f_) : f(f_), bk(f_, false), lc(&bk, f_) {}
  // Whether no assertion failed since the last call.
  bool accepted() { return !bk.assertion_failed(); }
  bool bit_of(const typename LC::BitW& b) {
    return lc.eval(b).elt() == f.one();
  }
  uint8_t byte_of(const typename LC::v8& v) {
    uint8_t x = 0;
    for (size_t j = 0; j < 8; ++j) x |= uint8_t(bit_of(v[j])) << j;
    return x;
  }
};

// The block witness H as constant wires, appended to BWS (block witnesses
// of wires are large: they stay off the stack).
template <class LC>
void konst_bw(const LC& lc, const Sha3Witness::BlockWitness& h,
              std::vector<typename Sha3Circuit<LC>::BlockWitness>& bws) {
  bws.emplace_back();
  auto& bw = bws.back();
  for (size_t round = 0; round < 24; ++round) {
    if (!sha3_slice_at(round)) continue;
    for (size_t x = 0; x < 5; ++x)
      for (size_t y = 0; y < 5; ++y)
        bw.a_intermediate[round][x][y] =
            lc.template vbit<64>(h.a_intermediate[round][x][y]);
  }
}

// ------------------------------------------------- 1. private length --

enum class MsgTamper { kNone, kByteIn, kByteOut, kShorter, kLonger, kHole };

template <class F>
void private_length_case(const F& f, const char* fname, size_t prefix_len,
                         size_t len, size_t outlen, MsgTamper t) {
  constexpr size_t kMax = 32;
  std::vector<uint8_t> prefix(prefix_len), msg(len);
  for (size_t i = 0; i < prefix_len; ++i) prefix[i] = uint8_t(7 * i + 3);
  for (size_t i = 0; i < len; ++i) msg[i] = uint8_t(13 * i + 101);
  std::vector<Sha3Witness::BlockWitness> hbws;
  lfb::shake256_private_length_witness(prefix, msg, kMax, outlen, hbws);
  std::vector<uint8_t> ref(outlen), in = prefix;
  in.insert(in.end(), msg.begin(), msg.end());
  Sha3Reference::shake256Hash(in.data(), in.size(), ref.data(), outlen);

  std::vector<uint8_t> padded = lfb::shake256_padded_message(msg, kMax);
  for (size_t i = len; i < kMax; ++i) padded[i] = uint8_t(0xA5 ^ i);
  std::vector<uint8_t> flags = lfb::shake256_in_message(len, kMax);
  bool want = true;
  switch (t) {
    case MsgTamper::kNone:
      break;
    case MsgTamper::kByteIn:
      padded[len / 2] ^= 0x10;
      want = false;
      break;
    case MsgTamper::kByteOut:
      padded[len] ^= 0x01;
      break;
    case MsgTamper::kShorter:
      flags[len - 1] = 0;
      want = false;
      break;
    case MsgTamper::kLonger:
      flags[len] = 1;
      want = false;
      break;
    case MsgTamper::kHole:
      flags[0] = 0;
      want = false;
      break;
  }
  Eval<F> e(f);
  auto& lc = e.lc;
  std::vector<typename Eval<F>::LC::v8> pw, mw;
  for (uint8_t b : prefix) pw.push_back(lc.template vbit<8>(b));
  for (uint8_t b : padded) mw.push_back(lc.template vbit<8>(b));
  std::vector<typename Eval<F>::LC::BitW> fw;
  for (uint8_t b : flags) fw.push_back(lc.bit(b));
  std::vector<typename Sha3Circuit<typename Eval<F>::LC>::BlockWitness> bws;
  for (const auto& b : hbws) konst_bw(lc, b, bws);
  std::vector<typename Eval<F>::LC::v8> out;
  lfb::assert_shake256_private_length(lc, pw, mw, fw, outlen, out, bws);
  bool ok = e.accepted();
  if (t == MsgTamper::kNone || t == MsgTamper::kByteOut) {
    for (size_t i = 0; i < outlen; ++i) ok = ok && e.byte_of(out[i]) == ref[i];
  }
  expect(ok, want,
         std::string("private length ") + fname + " prefix " +
             std::to_string(prefix_len) + " L " + std::to_string(len) +
             " out " + std::to_string(outlen) + " tamper " +
             std::to_string(int(t)));
}

template <class F>
void private_length_tests(const F& f, const char* fname) {
  for (size_t prefix : {0, 40, 66, 102, 202}) {
    for (size_t outlen : {64, 300}) {
      for (size_t len = 0; len <= 32; ++len) {
        private_length_case(f, fname, prefix, len, outlen, MsgTamper::kNone);
        if (len > 0) {
          private_length_case(f, fname, prefix, len, outlen, MsgTamper::kByteIn);
          private_length_case(f, fname, prefix, len, outlen, MsgTamper::kShorter);
        }
        if (len < 32) {
          private_length_case(f, fname, prefix, len, outlen, MsgTamper::kByteOut);
          private_length_case(f, fname, prefix, len, outlen, MsgTamper::kLonger);
        }
        if (len >= 2) {
          private_length_case(f, fname, prefix, len, outlen, MsgTamper::kHole);
        }
      }
    }
  }
}

// ------------------------------------------------------- 2. UseHint --

// The gadget's honest assignment for w' = R and the hint H (upstream's
// witness encoding, ml_dsa_host.h).
template <class Params>
struct HintAssignment {
  uint64_t r1, aux, hinted;
};
template <class Params>
HintAssignment<Params> honest_hint(uint64_t r, bool h) {
  auto [r1, r0] = ml_dsa::Decompose<Params>(static_cast<int32_t>(r));
  (void)r0;
  const int64_t g2 = Params::gamma_2;
  int64_t delta = (int64_t(r) - int64_t(r1) * 2 * g2) % int64_t(ml_dsa::Q);
  if (delta > int64_t(ml_dsa::Q) / 2) delta -= ml_dsa::Q;
  const uint64_t R = uint64_t(delta + g2), s = delta > 0 ? 0 : 1;
  return {uint64_t(r1), R | (s << Params::r0_bits),
          uint64_t(ml_dsa::UseHint<Params>(h, static_cast<int32_t>(r)))};
}

template <class Params>
bool hint_accepts(const Fp24_6& f6, uint64_t r, bool h,
                  const HintAssignment<Params>& a, bool exact) {
  using E = Eval<Fp24_6>;
  E e(f6);
  auto& lc = e.lc;
  ml_dsa_baseline::MLDSASplitVerify<E::LC, Fp24_6, Params> v(lc);
  const auto he = lc.konst(f6.of_scalar(h ? 1 : 0));
  const auto re = lc.konst(f6.of_scalar(r));
  const auto r1e = lc.konst(f6.of_scalar(a.r1));
  const auto r1b = lc.template vbit<Params::r1_bits>(a.r1);
  const auto auxb = lc.template vbit<Params::r0_bits + 1>(a.aux);
  const auto hinted = lc.konst(f6.of_scalar(a.hinted));
  const auto hintedb = lc.template vbit<Params::r1_bits>(a.hinted);
  v.assert_use_hint_single(he, re, r1e, r1b, auxb, hinted, hintedb);
  if (exact) {
    ml_dsa_baseline::assert_decompose_exact_single<Params>(lc, auxb, r1e);
  }
  return e.accepted();
}

template <class Set>
void use_hint_tests(const Fp24_6& f6) {
  using Params = typename Set::Reference;
  const uint64_t q = ml_dsa::Q, g2 = Params::gamma_2;
  std::vector<uint64_t> rs = {0, 1, g2 - 1, g2, g2 + 1, 2 * g2 - 1, 2 * g2,
                              3 * g2, q - 1 - g2, q - g2, q - g2 + 1, q - 2, q - 1};
  std::mt19937_64 rng(Set::kK);
  for (size_t i = 0; i < 200; ++i) rs.push_back(rng() % q);
  for (uint64_t r : rs) {
    for (bool h : {false, true}) {
      const auto a = honest_hint<Params>(r, h);
      const std::string w = std::string(Set::kName) + " UseHint honest r " +
                            std::to_string(r) + " h " + std::to_string(h);
      expect(hint_accepts<Params>(f6, r, h, a, false), true, w + " (gadget)");
      expect(hint_accepts<Params>(f6, r, h, a, true), true, w + " (exact)");
    }
  }
  // The second split (r1 + 1, -gamma2) of w' = (2 r1 + 1) gamma2.
  for (uint64_t r1 : {uint64_t(0), uint64_t(1), uint64_t(Params::M - 2)}) {
    const uint64_t r = (2 * r1 + 1) * g2;
    for (bool h : {false, true}) {
      const uint64_t m = Params::M;
      // c = h (1 - 2 s) with s = 1: -h.
      const uint64_t hinted = (r1 + 1 + m - (h ? 1 : 0)) % m;
      const HintAssignment<Params> bad{r1 + 1, uint64_t(1) << Params::r0_bits,
                                       hinted};
      const uint64_t fips = ml_dsa::UseHint<Params>(h, static_cast<int32_t>(r));
      const std::string w = std::string(Set::kName) + " UseHint second split r " +
                            std::to_string(r) + " h " + std::to_string(h) +
                            " output " + std::to_string(hinted) + " (FIPS " +
                            std::to_string(fips) + ")";
      expect(hinted != fips, true, w + ": outputs differ");
      expect(hint_accepts<Params>(f6, r, h, bad, false), true, w + " (gadget)");
      expect(hint_accepts<Params>(f6, r, h, bad, true), false, w + " (exact)");
    }
  }
}

// ------------------------------------------------- 3. SampleInBall --

enum class SibTamper { kNone, kMoveK, kWrongC };

template <class Set>
void sample_in_ball_case(const GF2_128<>& gf, const Fp24_6& f6,
                         const std::array<uint8_t, Set::kCTildeBytes>& rho,
                         SibTamper t) {
  using Params = typename Set::Reference;
  ml_dsa_host::SibTrace<Params> tr;
  if (!ml_dsa_host::sample_in_ball_witness<Params>(rho, tr)) return;
  const ml_dsa::Rq ref = ml_dsa::SampleInBall<Params>(rho);
  const Fp24& fq = ml_dsa::Fq();
  for (size_t k = 0; k < ml_dsa::N; ++k)
    if (!(ref[k] == tr.c[k])) {
      expect(false, true, std::string(Set::kName) + " host c = reference c");
      return;
    }
  std::array<uint16_t, Params::tau> kk = tr.k;
  if (t == SibTamper::kMoveK) kk[Params::tau / 2] += 1;
  const std::string w = std::string(Set::kName) + " SampleInBall tamper " +
                        std::to_string(int(t));

  // The hash side's gadget in GF(2^128): its (support, sign) bits.
  {
    using E = Eval<GF2_128<>>;
    E e(gf);
    auto& lc = e.lc;
    using VH = ml_dsa_baseline::MLDSAHashVerify<E::LC, GF2_128<>, Params, 128,
                                                ml_dsa_host::kSibBytes>;
    VH v(lc);
    typename VH::SampleInBallWitness sw;
    for (const auto& b : tr.bws) konst_bw(lc, b, sw.shake_bws);
    sw.position_trace.resize(Params::tau);
    for (size_t s = 0; s < Params::tau; ++s) {
      sw.j_vals[s] = lc.template vbit<8>(tr.j[s]);
      sw.j_k_indices[s] = lc.template vbit<16>(kk[s]);
      for (size_t k = 0; k <= s; ++k)
        sw.position_trace[s].push_back(lc.template vbit<8>(tr.trace[s][k]));
    }
    std::array<typename E::LC::v8, Params::c_tilde_bytes> rw;
    for (size_t i = 0; i < rho.size(); ++i) rw[i] = lc.template vbit<8>(rho[i]);
    const auto chunks = v.assert_sample_in_ball(rw, sw);
    bool ok = e.accepted();
    bool same = true;
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      const uint64_t val = fq.from_montgomery(ref[k]).limb_[0];
      const bool sup = e.bit_of(chunks[(2 * k) / 128][(2 * k) % 128]);
      const bool sgn = e.bit_of(chunks[(2 * k + 1) / 128][(2 * k + 1) % 128]);
      same = same && sup == (val != 0) && sgn == (val == ml_dsa::Q - 1);
    }
    expect(ok && (same || t == SibTamper::kWrongC), t != SibTamper::kMoveK,
           w + " (hash side)");
  }
  // The monolith's gadget in Fp24_6: c as field elements.
  {
    using E = Eval<Fp24_6>;
    E e(f6);
    auto& lc = e.lc;
    using V = MLDSAVerify<E::LC, Fp24_6, Params>;
    auto swp = std::make_unique<typename V::SampleInBallWitness>();
    auto& sw = *swp;
    std::vector<typename Sha3Circuit<E::LC>::BlockWitness> first, extra;
    konst_bw(lc, tr.bws[0], first);
    sw.shake_bws = first[0];
    for (size_t b = 1; b < tr.bws.size(); ++b) konst_bw(lc, tr.bws[b], extra);
    sw.position_trace.resize(Params::tau);
    for (size_t s = 0; s < Params::tau; ++s) {
      sw.j_vals[s] = lc.template vbit<8>(tr.j[s]);
      sw.j_k_indices[s] = lc.template vbit<16>(kk[s]);
      for (size_t k = 0; k <= s; ++k)
        sw.position_trace[s].push_back(lc.template vbit<8>(tr.trace[s][k]));
    }
    std::array<typename E::LC::v8, Params::c_tilde_bytes> rw;
    for (size_t i = 0; i < rho.size(); ++i) rw[i] = lc.template vbit<8>(rho[i]);
    std::array<typename E::LC::EltW, ml_dsa::N> cw;
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      uint64_t val = fq.from_montgomery(ref[k]).limb_[0];
      if (t == SibTamper::kWrongC && k == tr.j[0]) val = (val + 1) % ml_dsa::Q;
      cw[k] = lc.konst(f6.of_scalar(val));
    }
    ml_dsa_baseline::assert_sample_in_ball_stream<E::LC, Params,
                                                  ml_dsa_host::kSibBytes>(
        lc, rw, cw, sw, extra);
    expect(e.accepted(), t == SibTamper::kNone, w + " (monolith)");
  }
}

template <class Set>
void sample_in_ball_tests(const GF2_128<>& gf, const Fp24_6& f6) {
  std::mt19937_64 rng(1000 + Set::kK);
  for (size_t n = 0; n < 64; ++n) {
    std::array<uint8_t, Set::kCTildeBytes> rho;
    for (auto& b : rho) b = uint8_t(rng());
    for (SibTamper t : {SibTamper::kNone, SibTamper::kMoveK, SibTamper::kWrongC})
      sample_in_ball_case<Set>(gf, f6, rho, t);
  }
}

}  // namespace
}  // namespace proofs

int main() {
  using namespace proofs;  // NOLINT(build/namespaces)
  const GF2_128<> gf;
  const Fp24_6 f6(ml_dsa::Fq(), 7);
  private_length_tests(gf, "GF(2^128)");
  private_length_tests(f6, "Fp24_6");
  std::printf("private length: %zu cases, %zu failures\n", g_cases, g_failures);
  use_hint_tests<ml_dsa_sets::MlDsa44>(f6);
  use_hint_tests<ml_dsa_sets::MlDsa65>(f6);
  use_hint_tests<ml_dsa_sets::MlDsa87>(f6);
  std::printf("+ UseHint: %zu cases, %zu failures\n", g_cases, g_failures);
  sample_in_ball_tests<ml_dsa_sets::MlDsa44>(gf, f6);
  sample_in_ball_tests<ml_dsa_sets::MlDsa65>(gf, f6);
  sample_in_ball_tests<ml_dsa_sets::MlDsa87>(gf, f6);
  std::printf("+ SampleInBall: %zu cases, %zu failures\n", g_cases, g_failures);
  std::printf("GADGET TESTS %s\n", g_failures == 0 ? "PASS" : "FAIL");
  return g_failures == 0 ? 0 : 1;
}
