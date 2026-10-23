// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Host-side witness for the RSA proof of possession: SHA-256 block
// witnesses (upstream's FlatSHA256Witness), the exponentiation chain, the
// quotients and the grouped carries. Big integers use OpenSSL's BIGNUM
// (upstream already links libcrypto for SHA-256).

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_WITNESS_H_

#include <openssl/bn.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "arrays/dense.h"
#include "circuits/logic/bit_plucker_encoder.h"
#include "circuits/rsa/rsa_hash.h"
#include "circuits/rsa/rsa_shape.h"
#include "circuits/sha/flatsha256_witness.h"
#include "util/crypto.h"
#include "util/panic.h"

namespace proofs {

// Bit strings, LSB first.
using RsaBits = std::vector<uint8_t>;

inline RsaBits rsa_bits_of(const BIGNUM* x, size_t nbits) {
  RsaBits b(nbits);
  for (size_t i = 0; i < nbits; ++i) b[i] = BN_is_bit_set(x, int(i)) ? 1 : 0;
  return b;
}

inline void rsa_limb(BIGNUM* out, const BIGNUM* x, size_t a, size_t w) {
  BN_rshift(out, x, int(a * w));
  BN_mask_bits(out, int(w));
}

// The witness of one proof: digest, EM, and the signature circuit's
// committed numbers as bit strings.
struct RsaWitness {
  uint8_t digest[32];
  // D as 32 little-endian bytes: the MAC message (mdoc's to_bytes_field).
  uint8_t d_le[32];
  // x_[b][a], q_[b][a], c_[b][g] (c'_g, the offset carry)
  std::vector<std::vector<RsaBits>> x_, q_, c_;
  // false if some row's equation does not hold for these inputs
  bool satisfied = true;
};

// N, s big-endian 256 bytes; msg n bytes.
inline RsaWitness rsa_witness(const RsaShape& sh, const uint8_t* msg, size_t n,
                              const uint8_t sig[256], const uint8_t nmod[256]) {
  RsaWitness wt;
  SHA256 sha;
  sha.Update(msg, n);
  sha.DigestData(wt.digest);
  for (size_t i = 0; i < 32; ++i) wt.d_le[i] = wt.digest[31 - i];

  uint8_t em[kRsaModulusBytes] = {0};
  em[1] = 0x01;
  const size_t t0 = kRsaModulusBytes - 32 - sizeof(kRsaDigestInfo);
  for (size_t i = 2; i + 1 < t0; ++i) em[i] = 0xff;
  memcpy(&em[t0], kRsaDigestInfo, sizeof(kRsaDigestInfo));
  memcpy(&em[t0 + sizeof(kRsaDigestInfo)], wt.digest, 32);

  BN_CTX* ctx = BN_CTX_new();
  BIGNUM* N = BN_bin2bn(nmod, 256, nullptr);
  BIGNUM* EM = BN_bin2bn(em, 256, nullptr);
  std::vector<BIGNUM*> X(kRsaRows);
  X[0] = BN_bin2bn(sig, 256, nullptr);
  std::vector<BIGNUM*> Q(kRsaRows);
  BIGNUM* prod = BN_new();
  BIGNUM* rem = BN_new();
  for (size_t b = 0; b < kRsaRows; ++b) {
    const BIGNUM* y = b < kRsaSquarings ? X[b] : X[0];
    BN_mul(prod, X[b], y, ctx);
    Q[b] = BN_new();
    BN_div(Q[b], rem, prod, N, ctx);
    if (b < kRsaSquarings) {
      X[b + 1] = BN_dup(rem);
    }
  }

  const size_t L = sh.L, Lq = sh.Lq, w = sh.w;
  wt.x_.assign(kRsaRows, std::vector<RsaBits>(L));
  wt.q_.assign(kRsaRows, std::vector<RsaBits>(Lq));
  wt.c_.assign(kRsaRows, std::vector<RsaBits>(sh.G - 1));
  BIGNUM* t = BN_new();
  for (size_t b = 0; b < kRsaRows; ++b) {
    for (size_t a = 0; a < L; ++a) {
      rsa_limb(t, X[b], a, w);
      wt.x_[b][a] = rsa_bits_of(t, w);
    }
    for (size_t a = 0; a < Lq; ++a) {
      rsa_limb(t, Q[b], a, w);
      wt.q_[b][a] = rsa_bits_of(t, w);
    }
  }

  // Limbs as BIGNUMs for the carry computation.
  auto limbs = [&](const BIGNUM* v, size_t cnt) {
    std::vector<BIGNUM*> r(cnt);
    for (size_t a = 0; a < cnt; ++a) {
      r[a] = BN_new();
      rsa_limb(r[a], v, a, w);
    }
    return r;
  };
  auto free_all = [](std::vector<BIGNUM*>& v) {
    for (auto* p : v) BN_free(p);
  };
  std::vector<BIGNUM*> nl = limbs(N, L);
  BIGNUM* acc = BN_new();
  BIGNUM* di = BN_new();
  BIGNUM* carry = BN_new();
  BIGNUM* chk = BN_new();
  BIGNUM* off = BN_new();
  BN_one(off);
  BN_lshift(off, off, int(sh.bc - 1));
  for (size_t b = 0; b < kRsaRows; ++b) {
    const BIGNUM* y = b < kRsaSquarings ? X[b] : X[0];
    const BIGNUM* r = b < kRsaSquarings ? X[b + 1] : EM;
    std::vector<BIGNUM*> xl = limbs(X[b], L), yl = limbs(y, L);
    std::vector<BIGNUM*> ql = limbs(Q[b], Lq), rl = limbs(r, L);
    BN_zero(carry);
    for (size_t g = 0; g < sh.G; ++g) {
      // acc = E_g + c_{g-1}
      BN_copy(acc, carry);
      for (size_t j = 0; j < sh.k && g * sh.k + j < sh.K; ++j) {
        const size_t i = g * sh.k + j;
        BN_zero(di);
        for (size_t a = 0; a <= i && a < L; ++a) {
          if (i - a < L) {
            BN_mul(t, xl[a], yl[i - a], ctx);
            BN_add(di, di, t);
          }
        }
        for (size_t a = 0; a <= i && a < Lq; ++a) {
          if (i - a < L) {
            BN_mul(t, ql[a], nl[i - a], ctx);
            BN_sub(di, di, t);
          }
        }
        if (i < L) BN_sub(di, di, rl[i]);
        BN_lshift(di, di, int(w * j));
        BN_add(acc, acc, di);
      }
      if (g + 1 == sh.G) {
        if (!BN_is_zero(acc)) wt.satisfied = false;
        break;
      }
      // c_g = acc / 2^(w k), exact for a satisfied row.
      BN_rshift(carry, acc, int(w * sh.k));
      BN_lshift(chk, carry, int(w * sh.k));
      if (BN_cmp(chk, acc) != 0) wt.satisfied = false;
      BN_add(t, carry, off);
      if (BN_is_negative(t) || BN_num_bits(t) > int(sh.bc)) {
        wt.satisfied = false;
        BN_zero(t);
      }
      wt.c_[b][g] = rsa_bits_of(t, sh.bc);
    }
    free_all(xl);
    free_all(yl);
    free_all(ql);
    free_all(rl);
  }
  free_all(nl);
  for (auto* p : X) BN_free(p);
  for (auto* p : Q) BN_free(p);
  BN_free(N);
  BN_free(EM);
  BN_free(prod);
  BN_free(rem);
  BN_free(t);
  BN_free(acc);
  BN_free(di);
  BN_free(carry);
  BN_free(chk);
  BN_free(off);
  BN_CTX_free(ctx);
  return wt;
}

// Pushes a bit string as the circuit's digits: bits (LOGN = 1), LOGN-bit
// digit values (PLUCK = false) or BitPlucker encodings of LOGN-bit digits
// (PLUCK = true).
template <class Field, size_t LOGN, bool PLUCK>
void rsa_fill_bits(DenseFiller<Field>& df, const RsaBits& b, const Field& F) {
  if constexpr (LOGN == 1) {
    for (uint8_t v : b) df.push_back(v ? F.one() : F.zero());
  } else {
    BitPluckerEncoder<Field, LOGN> enc(F);
    for (size_t i = 0; i < b.size(); i += LOGN) {
      uint64_t v = 0;
      for (size_t j = 0; j < LOGN; ++j) v |= uint64_t(b[i + j]) << j;
      if constexpr (PLUCK) {
        df.push_back(enc.encode(v));
      } else {
        df.push_back(F.of_scalar(v));
      }
    }
  }
}

// N's limbs (the verifier computes them from its key).
template <class Field>
std::vector<typename Field::Elt> rsa_modulus_limbs(const RsaShape& sh,
                                                   const uint8_t nmod[256],
                                                   const Field& F) {
  BIGNUM* N = BN_bin2bn(nmod, 256, nullptr);
  BIGNUM* t = BN_new();
  std::vector<typename Field::Elt> out(sh.L);
  for (size_t a = 0; a < sh.L; ++a) {
    rsa_limb(t, N, a, sh.w);
    RsaBits bits = rsa_bits_of(t, sh.w);
    typename Field::Elt v = F.zero(), two = F.one();
    for (size_t j = 0; j < sh.w; ++j) {
      if (bits[j]) F.add(v, two);
      F.add(two, two);
    }
    out[a] = v;
  }
  BN_free(N);
  BN_free(t);
  return out;
}

// The key codec: 2048 bits and odd.
inline bool rsa_key_ok(const uint8_t nmod[256]) {
  return (nmod[0] & 0x80) != 0 && (nmod[255] & 1) != 0;
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_WITNESS_H_
