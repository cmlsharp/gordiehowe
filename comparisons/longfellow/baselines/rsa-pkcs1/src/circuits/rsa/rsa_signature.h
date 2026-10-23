// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// RSA-2048 PKCS#1 v1.5 (SHA-256) signature circuit over a prime field,
// in the style of circuits/mdoc/mdoc_signature.h.
//
// Public: N as L limbs of w bits, the two MACs of the digest and a_v as
// 128 bits each (as mdoc's signature circuit takes them).
// Private: the MAC witness (a_p and the digest bits, packed as mdoc's MAC
// witness), x_0 = s, x_1, ..., x_16 (L limbs each), the 17 quotients
// (Lq limbs each) and the carries (G - 1 per row).
//
// The circuit checks
//   x_b^2 = q_b N + x_{b+1}   for b < 16,
//   x_16 x_0 = q_16 N + EM,
// with EM = 0x00 01 FF..FF 00 || DigestInfo || D, whose limbs are affine in
// the digest bits, and the MACs of D under a_p + a_v. Every limb, quotient
// limb and carry is a sum of committed LOGN-bit digits, sum_i 2^(LOGN i) d_i,
// each digit range checked by one of two methods:
//   PLUCK = false: d is the digit's value, and the circuit asserts the
//     vanishing polynomial of {0, ..., 2^LOGN - 1} at d (LOGN = 1: d^2 = d);
//   PLUCK = true: d is upstream's BitPlucker encoding, split into LOGN
//     asserted bits whose weighted sum is the digit's value.

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_SIGNATURE_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_SIGNATURE_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/logic/bit_plucker.h"
#include "circuits/mac/mac_circuit.h"
#include "circuits/rsa/rsa_shape.h"

namespace proofs {

// The vanishing polynomial of {0, ..., 2^LOGN - 1} at d, as a balanced
// product tree. With M = 2^LOGN - 1, the roots pair as j and M - j, and
//   (d - j)(d - M + j) = u + j (M - j),   u = d^2 - M d,
// so the polynomial is the product of the 2^(LOGN-1) factors u + j (M - j)
// for j < 2^(LOGN-1): LOGN = 2 gives u (u + 2); LOGN = 4 gives the factors
// u + {0, 14, 26, 36, 44, 50, 54, 56}. Its roots in a prime field of more
// than 2^LOGN elements are exactly 0, ..., M.
template <class Logic, size_t LOGN>
typename Logic::EltW rsa_digit_vanishing(const Logic& lc,
                                         const typename Logic::EltW& d) {
  using EltW = typename Logic::EltW;
  constexpr uint64_t kM = (uint64_t(1) << LOGN) - 1;
  constexpr size_t kFactors = size_t(1) << (LOGN - 1);
  const EltW dd = lc.mul(d, d);
  const EltW md = lc.mul(lc.elt(kM), d);
  const EltW u = lc.sub(dd, md);
  std::vector<EltW> f(kFactors);
  for (size_t j = 0; j < kFactors; ++j) {
    f[j] = lc.add(u, lc.konst(uint64_t(j) * (kM - j)));
  }
  return lc.mul(0, kFactors, [&](size_t j) { return f[j]; });
}

// A number of nbits bits (a multiple of LOGN) held as committed digits.
template <class Logic, size_t LOGN, bool PLUCK>
class RsaRangedInput {
 public:
  using Field = typename Logic::Field;
  using Elt = typename Field::Elt;
  using EltW = typename Logic::EltW;
  using BitW = typename Logic::BitW;

  explicit RsaRangedInput(const Logic& lc) : lc_(lc), bp_(lc) {}

  // Allocates the digits, range checks them and returns their value.
  EltW input(size_t nbits) const {
    if constexpr (LOGN == 1 || PLUCK) {
      return input_bits(nbits);
    } else {
      return input_digits(nbits);
    }
  }

 private:
  // Digits d_i with the vanishing polynomial asserted; the value is
  // sum_i 2^(LOGN i) d_i.
  EltW input_digits(size_t nbits) const {
    const size_t nd = nbits / LOGN;
    std::vector<EltW> terms(nd);
    Elt scale = lc_.one();
    for (size_t i = 0; i < nd; ++i) {
      const EltW d = lc_.eltw_input();
      lc_.assert0(rsa_digit_vanishing<Logic, LOGN>(lc_, d));
      terms[i] = lc_.mul(scale, d);
      for (size_t t = 0; t < LOGN; ++t) lc_.f_.add(scale, scale);
    }
    return lc_.add(0, nd, [&](size_t i) { return terms[i]; });
  }

  // Committed bits (LOGN = 1) or plucked digits; the value is
  // sum_i 2^i b_i.
  EltW input_bits(size_t nbits) const {
    std::vector<BitW> b(nbits);
    if constexpr (LOGN == 1) {
      for (size_t i = 0; i < nbits; ++i) {
        b[i] = lc_.input();
      }
    } else {
      for (size_t i = 0; i < nbits; i += LOGN) {
        EltW e = lc_.eltw_input();
        auto bits = bp_.pluck(e);
        for (size_t j = 0; j < LOGN; ++j) {
          b[i + j] = bits[j];
        }
      }
    }
    std::vector<EltW> terms(nbits);
    Elt two_i = lc_.one();
    for (size_t i = 0; i < nbits; ++i) {
      terms[i] = lc_.mul(two_i, lc_.eval(b[i]));
      lc_.f_.add(two_i, two_i);
    }
    return lc_.add(0, nbits, [&](size_t i) { return terms[i]; });
  }

  const Logic& lc_;
  BitPlucker<Logic, (LOGN > 1 ? LOGN : 2)> bp_;
};

template <class Logic, size_t LOGN, bool PLUCK>
class RsaSignature {
 public:
  using Field = typename Logic::Field;
  using Elt = typename Field::Elt;
  using EltW = typename Logic::EltW;
  using BitW = typename Logic::BitW;
  using v128 = typename Logic::v128;
  using v256 = typename Logic::v256;
  using MacBitPlucker = BitPlucker<Logic, kMACPluckerBits>;
  using packed_v128 = typename MacBitPlucker::packed_v128;
  using packed_v256 = typename MacBitPlucker::packed_v256;
  // The committed MAC inputs, laid out as mac_circuit.h's MAC::Witness
  // (a_p[0], a_p[1], then the digest, BitPlucker-packed); declared here
  // because MAC itself needs Field::N.
  class MacWitness {
   public:
    packed_v128 aa_[2];
    packed_v256 xx_;

    void input(const Logic& lc) {
      aa_[0] = MacBitPlucker::template packed_input<packed_v128>(lc);
      aa_[1] = MacBitPlucker::template packed_input<packed_v128>(lc);
      xx_ = MacBitPlucker::template packed_input<packed_v256>(lc);
    }
  };

  class Witness {
   public:
    MacWitness mac_;
    // x_[b][a]: limb a of x_b; q_[b][a]; c_[b][g]: the committed c'_g.
    std::vector<std::vector<EltW>> x_, q_, c_;

    void input(const Logic& lc, const RsaShape& sh) {
      const RsaRangedInput<Logic, LOGN, PLUCK> ri(lc);
      mac_.input(lc);
      x_.assign(kRsaRows, std::vector<EltW>(sh.L));
      q_.assign(kRsaRows, std::vector<EltW>(sh.Lq));
      c_.assign(kRsaRows, std::vector<EltW>(sh.G - 1));
      for (auto& row : x_) {
        for (auto& v : row) v = ri.input(sh.w);
      }
      for (auto& row : q_) {
        for (auto& v : row) v = ri.input(sh.w);
      }
      for (auto& row : c_) {
        for (auto& v : row) v = ri.input(sh.bc);
      }
    }
  };

  RsaSignature(const Logic& lc, const RsaShape& sh)
      : lc_(lc), sh_(sh), bp_(lc) {}

  // N: L public limbs. mac[2], av: public 128-bit tags and MAC key half.
  void assert_signature(const std::vector<EltW>& N, const v128 mac[2],
                        const v128& av, const Witness& vw) const {
    // The digest D, bit i of the integer at index i.
    v256 d = bp_.template unpack<v256, packed_v256>(vw.mac_.xx_);
    v128 dh[2];
    for (size_t i = 0; i < 128; ++i) {
      dh[0][i] = d[i];
      dh[1][i] = d[128 + i];
    }
    assert_mac(mac, av, dh, vw.mac_);

    std::vector<EltW> em = encoded_message(d);
    for (size_t b = 0; b < kRsaRows; ++b) {
      const bool square = b < kRsaSquarings;
      const std::vector<EltW>& y = square ? vw.x_[b] : vw.x_[0];
      const std::vector<EltW>& r = square ? vw.x_[b + 1] : em;
      assert_mul_mod(vw.x_[b], y, square, vw.q_[b], N, r, vw.c_[b]);
    }
  }

 private:
  // mac[i] = (a_p[i] + a_v) * msg[i] in GF(2^128); mac_circuit.h's MAC
  // performs the same check on a field element's bits (assert_mac there).
  void assert_mac(const v128 mac[2], const v128& av, const v128 msg[2],
                  const MacWitness& vw) const {
    v128 mv;
    for (size_t i = 0; i < 2; ++i) {
      v128 ap = bp_.template unpack<v128, packed_v128>(vw.aa_[i]);
      v128 key = lc_.vxor(av, ap);
      lc_.gf2_128_mul(mv, key, msg[i]);
      lc_.vassert_eq(mac[i], mv);
    }
  }

  // EM's limbs: the constant bytes and the digest bits, affine.
  std::vector<EltW> encoded_message(const v256& d) const {
    uint8_t em[kRsaModulusBytes] = {0};
    em[1] = 0x01;
    const size_t t0 = kRsaModulusBytes - 32 - sizeof(kRsaDigestInfo);
    for (size_t i = 2; i + 1 < t0; ++i) em[i] = 0xff;
    em[t0 - 1] = 0x00;
    for (size_t i = 0; i < sizeof(kRsaDigestInfo); ++i) {
      em[t0 + i] = kRsaDigestInfo[i];
    }
    std::vector<EltW> out(sh_.L);
    for (size_t a = 0; a < sh_.L; ++a) {
      Elt c = lc_.zero(), two_j = lc_.one();
      std::vector<EltW> terms;
      for (size_t j = 0; j < sh_.w; ++j) {
        const size_t i = a * sh_.w + j;
        if (i < 256) {
          terms.push_back(lc_.mul(two_j, lc_.eval(d[i])));
        } else if (i < kRsaModulusBits) {
          // bit i of EM, big-endian bytes
          const uint8_t byte = em[kRsaModulusBytes - 1 - i / 8];
          if ((byte >> (i % 8)) & 1) lc_.f_.add(c, two_j);
        }
        lc_.f_.add(two_j, two_j);
      }
      EltW v = lc_.konst(c);
      for (const auto& t : terms) v = lc_.add(v, t);
      out[a] = v;
    }
    return out;
  }

  Elt pow2(size_t e) const {
    Elt r = lc_.one();
    for (size_t i = 0; i < e; ++i) lc_.f_.add(r, r);
    return r;
  }

  // x y = q N + r over the integers, by the grouped carry equations.
  void assert_mul_mod(const std::vector<EltW>& x, const std::vector<EltW>& y,
                      bool square, const std::vector<EltW>& q,
                      const std::vector<EltW>& N, const std::vector<EltW>& r,
                      const std::vector<EltW>& c) const {
    const size_t L = sh_.L, Lq = sh_.Lq;
    const Elt B = pow2(sh_.w * sh_.k);
    const Elt h = pow2(sh_.bc - 1);
    const Elt Bh = lc_.mulf(B, h);
    for (size_t g = 0; g < sh_.G; ++g) {
      std::vector<EltW> terms;
      Elt s = lc_.one();
      for (size_t j = 0; j < sh_.k && g * sh_.k + j < sh_.K; ++j) {
        const size_t i = g * sh_.k + j;
        const size_t lo = i + 1 > L ? i + 1 - L : 0;
        const Elt s2 = lc_.addf(s, s);
        const Elt ms = lc_.negf(s);
        for (size_t a = lo; a <= i && a < L; ++a) {
          const size_t b = i - a;
          if (square) {
            if (a < b) terms.push_back(lc_.mul(s2, x[a], y[b]));
            if (a == b) terms.push_back(lc_.mul(s, x[a], y[b]));
          } else {
            terms.push_back(lc_.mul(s, x[a], y[b]));
          }
        }
        for (size_t a = lo; a <= i && a < Lq; ++a) {
          terms.push_back(lc_.mul(ms, q[a], N[i - a]));
        }
        if (i < L) terms.push_back(lc_.mul(ms, r[i]));
        lc_.f_.add(s, s);
        for (size_t t = 1; t < sh_.w; ++t) lc_.f_.add(s, s);
      }
      Elt k0 = lc_.zero();
      if (g > 0) {
        terms.push_back(c[g - 1]);
        lc_.f_.sub(k0, h);
      }
      if (g + 1 < sh_.G) {
        terms.push_back(lc_.mul(lc_.negf(B), c[g]));
        lc_.f_.add(k0, Bh);
      }
      terms.push_back(lc_.konst(k0));
      EltW e = lc_.add(0, terms.size(), [&](size_t t) { return terms[t]; });
      lc_.assert0(e);
    }
  }

  const Logic& lc_;
  const RsaShape& sh_;
  MacBitPlucker bp_;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_SIGNATURE_H_
