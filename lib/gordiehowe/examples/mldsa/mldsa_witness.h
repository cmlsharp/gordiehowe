// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code of the ML-DSA relations, which their
// generators call: the integer computations of verification (NTT,
// Decompose, UseHint, SampleInBall, w') without branching on a witness
// value (ct.h), and the decoded signature. It also holds the key's
// decoding and tr, public values both parties compute. A function that
// depends on the parameter set takes it as its first template parameter S
// (mldsa_params.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_WITNESS_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/sample_in_ball_witness.h"
#include "gordiehowe/lib/select.h"
#include "circuits/ntt/falcon_ntt.h"

namespace proofs::gordiehowe::examples::mldsa {

// Integer witness computations, branch-free on witness values (ct.h):
// reductions by the compile-time q, masks for every data-dependent choice.

namespace host {

using Poly = std::array<uint64_t, kN>;

inline uint64_t mod_q(uint64_t x) { return x % kQ; }

// FIPS 204 Algorithms 41 (NTT) and 42 (NTT^-1): falcon_ntt_ref's loops
// with FIPS 204's zetas, at the compile-time q.
inline void ntt(Poly &w) { falcon_ntt_ref<kQ>(w, ml_dsa::kZetas); }
inline void intt(Poly &w) { falcon_intt_ref<kQ>(w, ml_dsa::kZetas); }
// ntt (or intt, INVERSE) of each polynomial of V, a flat [count][N]
// vector, in place.
inline void ntt_each(std::vector<uint64_t> &v, bool inverse = false) {
  Poly p;
  for (size_t e = 0; e < v.size() / kN; ++e) {
    std::copy(v.begin() + long(e * kN), v.begin() + long((e + 1) * kN),
              p.begin());
    if (inverse)
      intt(p);
    else
      ntt(p);
    std::copy(p.begin(), p.end(), v.begin() + long(e * kN));
  }
}
inline void intt_each(std::vector<uint64_t> &v) { ntt_each(v, true); }

// FIPS 204 Algorithm 36 (Decompose) by the reference implementation's
// arithmetic for S's gamma2, (q - 1)/88 or (q - 1)/32: r = r1 2 gamma2 + r0
// with r0 in (-gamma2, gamma2], or r1 = 0 and r0 in [-gamma2, 0] at the
// top.
struct Decomposed {
  int64_t r1, r0;
};
template <class S>
Decomposed decompose(uint64_t r) {
  static_assert(S::kGamma2 == (kQ - 1) / 88 || S::kGamma2 == (kQ - 1) / 32);
  const int64_t a = int64_t(r);
  int64_t a1 = (a + 127) >> 7;
  if constexpr (S::kGamma2 == (kQ - 1) / 88) {
    a1 = (a1 * 11275 + (int64_t(1) << 23)) >> 24;
    a1 ^= ((43 - a1) >> 63) & a1;
  } else {
    a1 = (a1 * 1025 + (int64_t(1) << 21)) >> 22;
    a1 &= 15;
  }
  int64_t a0 = a - a1 * 2 * int64_t(S::kGamma2);
  a0 -= ((int64_t(kQ - 1) / 2 - a0) >> 63) & int64_t(kQ);
  return {a1, a0};
}

// UseHint's output and the interval witness of the relation:
// y = UseHint(h, r); nonpositive = [r0 <= 0];
// endpoint = nonpositive and r1 = 0; offset = R + endpoint - 1 when
// nonpositive, R - gamma2 - 1 otherwise, for R = r0 + gamma2; slack =
// gamma2 - 1 + endpoint - offset.
struct Hinted {
  uint64_t y, nonpositive, offset, slack;
};
template <class S>
Hinted use_hint(uint64_t h, uint64_t r) {
  const Decomposed d = decompose<S>(r);
  const uint64_t r1 = uint64_t(d.r1);
  // r0 > 0
  const uint64_t pos = uint64_t(-d.r0) >> 63;
  const uint64_t up = ct::select(ct::mask(ct::eq(r1, S::kM - 1)), 0, r1 + 1);
  const uint64_t down = ct::select(ct::mask(ct::eq(r1, 0)), S::kM - 1, r1 - 1);
  Hinted o;
  o.y = ct::select(ct::mask(h & 1), ct::select(ct::mask(pos), up, down), r1);
  o.nonpositive = pos ^ 1;
  const uint64_t R = uint64_t(d.r0 + int64_t(S::kGamma2));
  const uint64_t endpoint = o.nonpositive & ct::eq(r1, 0);
  o.offset = ct::select(ct::mask(o.nonpositive), R + endpoint - 1,
                        R - S::kGamma2 - 1);
  o.slack = S::kGamma2 - 1 + endpoint - o.offset;
  return o;
}

// FIPS 204 Algorithm 29 (SampleInBall) on the kSibBytes S of its SHAKE256
// stream (272 bytes, at least FIPS 204 Appendix C's 221): c in {0, 1, q - 1},
// obliviously: the selection is select.h's host::select_first with
// SampleInBall's threshold (256 - tau + selected so far), the swaps
// sample_in_ball.h's sample_in_ball_host::swaps, whose cells 0, 1, 2 are
// 0, 1, q - 1.
template <class S>
Poly sample_in_ball_on(const std::array<uint8_t, kSibBytes> &s) {
  std::vector<uint32_t> v(kSibBytes - kSignBytes);
  for (size_t i = 0; i < v.size(); ++i) v[i] = s[kSignBytes + i];
  const auto o = sample_in_ball_host::select(v, S::kTau);
  std::vector<uint64_t> j(o.raw.begin(), o.raw.end());
  std::vector<uint64_t> signs(S::kTau);
  for (size_t t = 0; t < S::kTau; ++t) signs[t] = (s[t / 8] >> (t % 8)) & 1;
  const auto tr = sample_in_ball_host::swaps(j, signs, kN);
  Poly c;
  for (size_t k = 0; k < kN; ++k)
    c[k] = ct::select(ct::mask(ct::eq(tr.cells[k], 2)), kQ - 1, tr.cells[k]);
  return c;
}

// SampleInBall of C_TILDE: sample_in_ball_on of SHAKE256(C_TILDE, kSibBytes).
template <class S>
Poly sample_in_ball(const std::vector<uint8_t> &c_tilde) {
  std::array<uint8_t, kSibBytes> s;
  Sha3Reference::shake256Hash(c_tilde.data(), c_tilde.size(), s.data(),
                              s.size());
  return sample_in_ball_on<S>(s);
}

// tr = SHAKE256(PK, 64) (FIPS 204 Algorithm 8, line 6), of the key's
// bytes, a public value.
inline std::vector<uint8_t> key_hash(const std::vector<uint8_t> &pk) {
  std::vector<uint8_t> t(kTrBytes);
  Sha3Reference::shake256Hash(pk.data(), pk.size(), t.data(), t.size());
  return t;
}

// NTT(2^d t1) of T1 [K][N] (canonical coefficients), [K][N].
template <class S>
std::vector<uint64_t> t1_hat(const std::vector<uint64_t> &t1) {
  std::vector<uint64_t> out(S::kK * kN);
  for (size_t i = 0; i < S::kK; ++i) {
    Poly th;
    for (size_t k = 0; k < kN; ++k) th[k] = mod_q(t1[i * kN + k] << kD);
    ntt(th);
    for (size_t k = 0; k < kN; ++k) out[i * kN + k] = th[k];
  }
  return out;
}

// The challenge polynomial c = support - 2 sign (0, 1 or q - 1) from the
// challenge's (support, sign) bits C_BITS [N][2], without branching on
// them.
inline Poly challenge_coefficients(const std::vector<uint64_t> &c_bits) {
  Poly c;
  for (size_t i = 0; i < kN; ++i)
    c[i] = ct::select(ct::mask(c_bits[2 * i + 1]), kQ - 1, c_bits[2 * i]);
  return c;
}

// w' = NTT^-1(A_hat o NTT(z) - NTT(c) o T1_HAT) (FIPS 204 Algorithm 8,
// line 9), [K][N] from A_HAT [K][L][N] and T1_HAT = NTT(2^d t1) [K][N]
// (spectra), Z [L][N], all canonical, and the challenge's (support, sign)
// bits C_BITS [N][2].
template <class S>
std::vector<uint64_t> w_prime_spectral(const std::vector<uint64_t> &a_hat,
                                       const std::vector<uint64_t> &t1_hat,
                                       const std::vector<uint64_t> &z,
                                       const std::vector<uint64_t> &c_bits) {
  const Poly c = challenge_coefficients(c_bits);
  std::array<Poly, S::kL> zh;
  for (size_t j = 0; j < S::kL; ++j) {
    for (size_t k = 0; k < kN; ++k) zh[j][k] = z[j * kN + k];
    ntt(zh[j]);
  }
  Poly ch = c;
  ntt(ch);
  std::vector<uint64_t> w(S::kK * kN);
  for (size_t i = 0; i < S::kK; ++i) {
    Poly acc;
    for (size_t k = 0; k < kN; ++k) {
      uint64_t x = kQ - mod_q(ch[k] * t1_hat[i * kN + k]);
      for (size_t j = 0; j < S::kL; ++j)
        x = mod_q(x + a_hat[(i * S::kL + j) * kN + k] * zh[j][k]);
      acc[k] = x;
    }
    intt(acc);
    for (size_t k = 0; k < kN; ++k) w[i * kN + k] = acc[k];
  }
  return w;
}

// w' of A_HAT [K][L][N] (spectra) and T1 [K][N] in coefficient form.
template <class S>
std::vector<uint64_t> w_prime(const std::vector<uint64_t> &a_hat,
                              const std::vector<uint64_t> &t1,
                              const std::vector<uint64_t> &z,
                              const std::vector<uint64_t> &c_bits) {
  return w_prime_spectral<S>(a_hat, t1_hat<S>(t1), z, c_bits);
}

// The key's public parts (pkDecode, public: it may branch).
inline std::vector<uint64_t> canonical(const ml_dsa::Rq &p) {
  std::vector<uint64_t> out(kN);
  for (size_t k = 0; k < kN; ++k)
    out[k] = ml_dsa::Fq().from_montgomery(p[k]).limb_[0];
  return out;
}
// ExpandA(rho) of the key PK, [K][L][N], each RejNTTPoly call bounded at
// BLOCKS SHAKE128 blocks (ml_dsa::RejNTTPolyBounded: 6 blocks, 1008
// bytes, 336 candidates, as FIPS 204 Appendix C permits). A key with fewer
// than 256 acceptances in a call is a malformed statement
// (StatementRefused), which a uniform rho gives with probability 2^-542.9
// at ML-DSA-44's 16 calls (expand_a.h), below 2^-540 at ML-DSA-87's 56. A
// BLOCKS other than ml_dsa::kRejNTTPolyBlocks is for tests.
template <class S>
std::vector<uint64_t> expand_a_within(const std::vector<uint8_t> &pk,
                                      size_t blocks) {
  if (pk.size() < 32) throw StatementRefused("ExpandA: key too short");
  const std::vector<uint8_t> rho(pk.begin(), pk.begin() + 32);
  const auto a_hat =
      ml_dsa::ExpandABounded<typename S::Reference>(rho, blocks);
  if (!a_hat.has_value())
    throw StatementRefused("ExpandA: fewer than 256 acceptances");
  std::vector<uint64_t> out;
  for (size_t i = 0; i < S::kK; ++i)
    for (size_t j = 0; j < S::kL; ++j) {
      const auto p = canonical((*a_hat)[i][j]);
      out.insert(out.end(), p.begin(), p.end());
    }
  return out;
}
// ExpandA(rho) of the key PK, bounded, [K][L][N] (spectra).
template <class S>
std::vector<uint64_t> expand_a(const std::vector<uint8_t> &pk) {
  return expand_a_within<S>(pk, ml_dsa::kRejNTTPolyBlocks);
}
// ExpandA(rho) in coefficient form, [K][L][N]: NTT^-1 of each spectrum.
template <class S>
std::vector<uint64_t> expand_a_coefficients(const std::vector<uint8_t> &pk) {
  std::vector<uint64_t> out = expand_a<S>(pk);
  intt_each(out);
  return out;
}
// t1 of the key PK, [K][N] (pkDecode's step 3, without ExpandA).
template <class S>
std::vector<uint64_t> decode_t1(const std::vector<uint8_t> &pk) {
  constexpr size_t kT1Bytes = kN * 10 / 8;
  if (pk.size() < 32 + S::kK * kT1Bytes)
    throw StatementRefused("pkDecode: key too short");
  const auto &fq = ml_dsa::Fq();
  std::vector<uint64_t> out;
  for (size_t i = 0; i < S::kK; ++i) {
    const auto at = pk.begin() + long(32 + i * kT1Bytes);
    const auto t1 = ml_dsa::SimpleBitUnpack(
        std::vector<uint8_t>(at, at + long(kT1Bytes)), 1023);
    for (size_t k = 0; k < kN; ++k)
      out.push_back(fq.from_montgomery(t1[k]).limb_[0]);
  }
  return out;
}

}  // namespace host


// The decoded signature: c~, z (canonical in [0, q)) and the hint bits.
struct Signature {
  std::vector<uint8_t> c_tilde;
  // [L][N]
  std::vector<uint64_t> z;
  // [K][N]
  std::vector<uint8_t> h;
};

// The centered integer of a canonical coefficient X in [0, q), branch-free.
inline int32_t centered(uint64_t x) {
  const uint64_t neg = ct::lt(kQ / 2, x);
  return int32_t(int64_t(x) - int64_t(ct::select(ct::mask(neg), kQ, 0)));
}

}  // namespace proofs::gordiehowe::examples::mldsa

namespace proofs::gordiehowe::examples::mldsa::emulated {


namespace host {

using examples::mldsa::host::Poly;

// The F_q residue of a signed coefficient Z of the carrier (characteristic
// P; z below zero is P - |z|, |z| < q), without a branch.
inline uint64_t residue(uint64_t z, uint64_t p) {
  const uint64_t neg = ct::lt(p / 2, z);
  return ct::select(ct::mask(neg), kQ - (p - z), z);
}

// w' of examples::mldsa::host::w_prime from A in coefficient form
// ([K][L][N], public: its NTT may branch) and Z the carrier's signed
// coefficients.
template <class S>
std::vector<uint64_t> w_prime(const std::vector<uint64_t> &a,
                              const std::vector<uint64_t> &t1,
                              const std::vector<uint64_t> &z,
                              const std::vector<uint64_t> &c_bits,
                              uint64_t p) {
  std::vector<uint64_t> a_hat = a;
  examples::mldsa::host::ntt_each(a_hat);
  std::vector<uint64_t> zq(z.size());
  for (size_t i = 0; i < z.size(); ++i) zq[i] = residue(z[i], p);
  return examples::mldsa::host::w_prime<S>(a_hat, t1, zq, c_bits);
}

}  // namespace host


}  // namespace proofs::gordiehowe::examples::mldsa::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_WITNESS_H_
