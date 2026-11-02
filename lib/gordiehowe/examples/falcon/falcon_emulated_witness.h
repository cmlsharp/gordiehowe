// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code of the Falcon relations' generators
// (falcon_emulated.h, falcon_native.h and the Falcon ring): s1, the
// committed key's coefficients, the magnitudes, the encoding's low parts
// and the norm's sum of squares. It also holds the key decoding, a public
// computation of the statement.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_WITNESS_H_

#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <vector>

#include "circuits/ntt/emulated_signature.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/falcon/falcon_params.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/ops/operators.h"
#include "circuits/ntt/falcon_ntt.h"

namespace proofs::gordiehowe::examples::falcon::emulated {

// Every computation runs without a branch, a variable-time operation or an
// address that depends on a witness value (ct.h). Reductions are
// by the compile-time q (a multiply and shift), the transforms
// falcon_ntt_ref and falcon_intt_ref at that q.

namespace host {

// The integer of each row of a bit matrix ([N][16]: sample j, bit b),
// least significant bit first.
inline std::vector<uint64_t> words_of_bits(const Tensor<uint64_t> &bits) {
  std::vector<uint64_t> c;
  for (size_t j = 0; j < bits.rows(); ++j) {
    uint64_t v = 0;
    size_t i = 0;
    for (uint64_t b : bits.row(j)) v += ct::nonzero(b) << i++;
    c.push_back(v);
  }
  return c;
}

// The challenge c as integers: the 16-bit samples of a bit matrix ([N][16],
// c from domain H) or the coefficients themselves ([N], c from the
// statement).
inline std::vector<uint64_t> challenge_integers(const Tensor<uint64_t> &c) {
  if (c.dims().size() == 2) return words_of_bits(c);
  return std::vector<uint64_t>(c.begin(), c.begin() + long(c.size()));
}

// x mod q for any 64-bit x: a division by the constant q, which the
// compiler emits as a multiply and shift.
inline uint64_t mod_q(uint64_t x) { return x % kQ; }

// The key's coefficients h = INTT(K) over Z_q from its NTT coordinates K,
// with the zetas Z: a public computation of the statement.
inline std::vector<uint64_t> decode_spectrum(const std::vector<uint64_t> &k,
                                             const std::vector<uint64_t> &z) {
  return emulated_ntt::decode(k, z, kQ);
}

// s1 = c - s2 h mod q, by the NTT.
inline std::vector<uint64_t> s1_of(const std::vector<uint64_t> &hhat,
                                   const std::vector<uint64_t> &craw,
                                   const std::vector<uint64_t> &s2,
                                   const std::vector<uint64_t> &zetas) {
  const size_t n = craw.size();
  std::vector<uint64_t> c_hat = craw;
  std::vector<uint64_t> s2hat = s2;
  std::vector<uint64_t> s1hat(n);
  falcon_ntt_ref<kQ>(c_hat, zetas);
  falcon_ntt_ref<kQ>(s2hat, zetas);
  for (size_t i = 0; i < n; ++i)
    s1hat[i] = mod_q(c_hat[i] + kQ * kQ - s2hat[i] * mod_q(hhat[i]));
  falcon_intt_ref<kQ>(s1hat, zetas);
  return s1hat;
}

// The coefficients of the key whose spectrum under the staged transform T
// is SPEC, each below q (a ring member's, which the membership argument
// binds): the inverse transform, from T's order to ntt.h's (a bit
// reversal for the natural order) and NegacyclicNtt's inverse. A
// coefficient outside [0, q) clears a bit, and the error is thrown once.
template <class F>
std::vector<uint64_t> key_coefficients(const F &f, const ops::StagedNtt<F> &t,
                                       const std::vector<typename F::Elt> &spec) {
  std::vector<typename F::Elt> a = spec;
  if (t.order == ops::NttOrder::kNatural) {
    const size_t logn = ops::ntt_log2(t.n);
    for (size_t i = 0; i < t.n; ++i) {
      const size_t j = ops::ntt_brv(i, logn);
      if (i < j) std::swap(a[i], a[j]);
    }
  }
  ops::NegacyclicNtt<F>(f, t.n, t.psi).inverse(a);
  std::vector<uint64_t> h(t.n);
  uint64_t ok = 1;
  for (size_t i = 0; i < t.n; ++i) {
    const NatInt x = nat_of_ct(f, a[i], ok);
    ok &= ct::lt128(x, kQ);
    h[i] = uint64_t(x);
  }
  if (!ok)
    throw std::runtime_error("falcon key: a coefficient of the committed "
                             "spectrum is not below q");
  return h;
}

// The centered magnitude of a coefficient in [0, q): x, or q - x above
// q / 2, by a masked select.
inline uint64_t magnitude(uint64_t x) {
  const uint64_t up = ct::lt(kQ / 2, x);
  return ct::select(ct::mask(up), kQ - x, x);
}

// The low part m mod d of a magnitude, d = 128: a mask.
inline uint64_t low_of(uint64_t m) {
  static_assert(kLowRadix == 128, "the low radix is 2^7");
  return m & 127;
}

// The sum of the squares of two vectors of n magnitudes below q: at most
// 2n q^2 < 2^39 for n <= 1024.
inline std::vector<uint64_t> sum_of_squares(const std::vector<uint64_t> &a,
                                            const std::vector<uint64_t> &b) {
  uint64_t total = 0;
  for (uint64_t x : a) total += x * x;
  for (uint64_t x : b) total += x * x;
  return {total};
}

}  // namespace host

}  // namespace proofs::gordiehowe::examples::falcon::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_WITNESS_H_
