// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the post-quantum mDL. Plain mdoc (mdoc.h, Longfellow's
// ZkSpec v7 relation) with ML-DSA-44 in place of both ECDSA signatures, as
// one proof over two domains joined by a MAC. The issuer's key, now, the
// requested attributes and the device's message are public; the MSO, its
// length, the items and both signatures are private.
//
// Domain H (a binary field) checks the MSO's windows, dates and attributes
// (mdoc_hash.h), hashes the items with SHA-256 and runs every SHAKE call
// in one Keccak batch: both signatures' mu and challenge, and ExpandA of
// the device key. Domain A verifies both signatures: over the ML-DSA
// native field in FqArm, over a Goldilocks extension with arithmetic mod
// q emulated in GoldilocksArm. The issuer's key is public; the device's
// key comes from the MSO's deviceKeyInfo window in H and crosses into A.
// pq_mdoc_builders.h builds the statement and the witness.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mdoc/mdoc_hash.h"
#include "gordiehowe/examples/mldsa/expand_a.h"
#include "gordiehowe/examples/mldsa/mldsa_emulated.h"
#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/message.h"
#include "gordiehowe/lib/sha256.h"
#include "gordiehowe/lib/windows.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::pq_mdoc {

using examples::mldsa::kK;
using examples::mldsa::kL;
using examples::mldsa::kN;

// The longest MSO: v7's kMaxMsoLen (2533 bytes, 40 SHA-256 blocks less
// the padding's 9 bytes and v7's 18-byte prefix; the MSO bytes as v7 lays
// them out, the payload's 2 length bytes, then D8 18 59 LL LL and the MSO
// map) plus the growth of the device key: v7's EC2 COSE_Key {1: 2, -1: 1,
// -2: x, -3: y} is A4 01 02 20 01 21 58 20 x 22 58 20 y, 75 bytes; the
// AKP key {1: 7, 3: -48, -1: pk} is A3 01 07 03 38 2F 20 59 05 20 pk,
// 1322 bytes. So 2533 + 1247 = 3780 bytes.
constexpr size_t kV7DeviceKeyBytes = 1 + 2 + 2 + 3 + 32 + 3 + 32;
constexpr size_t kAkpDeviceKeyBytes = 1 + 2 + 3 + 1 + 3 + 1312;
constexpr size_t kMaxMsoBytes =
    kMaxMsoLen + kAkpDeviceKeyBytes - kV7DeviceKeyBytes;
static_assert(kV7DeviceKeyBytes == 75 && kAkpDeviceKeyBytes == 1322 &&
              kMaxMsoBytes == 3780);
// The issuer's mu: SHAKE256 of tr_I || 00 00 || cose_prefix || MSO, at
// most kHeadBytes + kMaxMsoBytes = 3865 bytes, so a buffer of 29 blocks of
// 136 bytes (the least that holds the message and its padding). The MSO's
// part of the buffer is kMsoBytes; the length bound is kMaxMsoBytes.
constexpr size_t kTrBytes = 64;
constexpr size_t kPrefixBytes = 19;
constexpr size_t kHeadBytes = kTrBytes + 2 + kPrefixBytes;
constexpr size_t kRate = 136;
constexpr size_t kBlocks = (kHeadBytes + kMaxMsoBytes) / kRate + 1;
constexpr size_t kBufBytes = kRate * kBlocks;
constexpr size_t kMsoBytes = kBufBytes - kHeadBytes;
constexpr size_t kMaxMessageBytes = kHeadBytes + kMaxMsoBytes;
static_assert(kHeadBytes == 85 && kBlocks == 29 && kMsoBytes == 3859 &&
              kMaxMessageBytes == 3865 && kMaxMessageBytes < kBufBytes);
// Windows start at MSO byte 7 (after 2 + 5 length and tag bytes, as v7).
constexpr size_t kWindowFirst = examples::mdoc::kWindowFirst;
constexpr size_t kWindowEnd = kMsoBytes;
constexpr size_t kFixedWindows = examples::mdoc::kFixedWindows;
constexpr size_t kPkBytes = examples::mldsa::kPkBytes;
constexpr size_t kRhoBytes = 32;
constexpr size_t kT1Bits = 10;
// The Goldilocks arm's device relation (goldilocks_device_relation): w'
// and the residues z_hat below kT^2, and its quotient Q in base-kT digits,
// committed by hand (both operands are degree-2 products, which
// assert_mod's m >= 2 forms do not take).
constexpr uint64_t kT = 4096;

// The COSE_Sign1 ToBeSigned prefix with alg ML-DSA-44 (-48): 84 6A
// "Signature1" 44 A1 01 38 2F 40 59 (pq_mdoc_data.h).
inline const std::vector<uint8_t> &cose_prefix() {
  static const std::vector<uint8_t> v = {0x84, 0x6A, 'S',  'i',  'g',
                                         'n',  'a',  't',  'u',  'r',
                                         'e',  '1',  0x44, 0xA1, 0x01,
                                         0x38, 0x2F, 0x40, 0x59};
  return v;
}
// The deviceKeyInfo window's constant bytes before pk_D: 6D
// "deviceKeyInfo" A1 69 "deviceKey" A3 01 07 03 38 2F 20 59 05 20, the
// COSE_Key {1: 7, 3: -48, -1: bstr of 1312 bytes} (RFC 9964: kty AKP = 7,
// alg ML-DSA-44 = -48, pub = -1) in deterministic order.
inline const std::vector<uint8_t> &device_key_info_key() {
  static const std::vector<uint8_t> v = {
      0x6D, 'd',  'e',  'v',  'i',  'c',  'e',  'K',  'e',  'y',  'I',  'n',
      'f',  'o',  0xA1, 0x69, 'd',  'e',  'v',  'i',  'c',  'e',  'K',  'e',
      'y',  0xA3, 0x01, 0x07, 0x03, 0x38, 0x2F, 0x20, 0x59, 0x05, 0x20};
  return v;
}

// ---------------------------------------------------------------- gadgets --

// The device key in A: A_hat's and t1's bits crossed from H, and their
// values as affine views.
template <class AF>
struct DeviceKey {
  // [K][L][N][23]
  Ref<AF, Bit, Committed> a_bits;
  // [K][N][10]
  Ref<AF, Bit, Committed> t1_bits;
  // [K][L][N], NTT domain, canonical
  Ref<AF, Field, Committed> a_hat;
  // [K][N], coefficients
  Ref<AF, Field, Committed> t1;
};

// The crossing of the device key into domain A, in scope S: H's A_hat
// coefficients COEFFICIENTS ([K][L][N][23], below q by ExpandA's
// comparator) and t1 bits T1 ([K][N][10]) carried to A by x.to(A) (A's Bit
// cells, one MAC equality each, merged with the system's other equalities
// into one MAC), and the integers as affine views of A's bits. A_hat's
// integers are below q, and so canonical in A, by ExpandA's comparator in
// H; t1's are below 2^10. The relation reads the device key only through
// this function, so a different crossing needs a change here alone.
template <class DA, class HF, class P1, class P2>
auto device_key_crossing(const Scope &s, DA &A,
                         const Ref<HF, Bit, P1> &coefficients,
                         const Ref<HF, Bit, P2> &t1) {
  using AF = std::decay_t<decltype(A.field())>;
  const Scope sa = s.scope("a_hat");
  const auto a_bits = coefficients.to(sa[A], "bits");
  const auto a_hat = sa[A].derive("a_hat", a_bits.from_digits(2));
  const Scope st = s.scope("t1");
  const auto t_bits = t1.to(st[A], "bits");
  const auto t_values = st[A].derive("t1", t_bits.from_digits(2));
  DeviceKey<AF> k;
  k.a_bits = a_bits;
  k.t1_bits = t_bits;
  k.a_hat = a_hat;
  k.t1 = t_values;
  return k;
}

namespace host {
// The integers of BITS, W bits each, least significant first.
inline std::vector<uint64_t> integers(const std::vector<uint64_t> &bits,
                                      size_t w) {
  std::vector<uint64_t> out(bits.size() / w, 0);
  for (size_t i = 0; i < out.size(); ++i)
    for (size_t b = 0; b < w; ++b) out[i] |= (bits[w * i + b] & 1) << b;
  return out;
}
}  // namespace host

// The device's relation w' = A z - 2^d t1 c (FIPS 204 Algorithm 8, line 9)
// with A_hat and t1 committed (the device key K), in the spectrum of FIPS
// 204's transform as the ring arm checks it (mldsa_ring_native.h):
//   c_hat           NTT(c), advice [N]; Ntt(c) = c_hat o Ntt(1)
//   relation        Ntt(w'_i) = sum_j A_hat[i][j] o Ntt(z_j)
//                               - 2^d c_hat o Ntt(t1_i)
// one circuit over the shared transforms of z_j, t1_i, c and 1. Both
// identities are equalities of polynomials, since the transform is a
// bijection. Returns w' (advice [K][N], canonical).
template <class D, class AF, class PZ>
Ref<AF, Subfield<>, Committed> device_relation(
    const Scope &s, D &A, const DeviceKey<AF> &k,
    const Ref<AF, Subfield<>, PZ> &z, const Ref<AF, Bit, Committed> &c) {
  const auto w = s[A].priv(
      Subfield{}, "w", Shape{kK, kN}, depends_on(k.a_bits, k.t1_bits, z, c),
      [](const std::vector<uint64_t> &ab, const std::vector<uint64_t> &tb,
         const std::vector<uint64_t> &zz, const std::vector<uint64_t> &cb) {
        return examples::mldsa::host::w_prime(host::integers(ab, 23),
                                    host::integers(tb, kT1Bits), zz, cb);
      });
  const auto c_hat = s[A].priv(
      Subfield{}, "c_hat", Shape(kN), depends_on(c),
      [](const std::vector<uint64_t> &cb) {
        examples::mldsa::host::Poly p =
            examples::mldsa::host::challenge_coefficients(cb);
        examples::mldsa::host::ntt(p);
        return std::vector<uint64_t>(p.begin(), p.end());
      });
  const AF &f = A.field();
  const auto ntt = ops::SchemeNtt(f, kN, ops::Stages::every(4));
  const auto cpoly = examples::mldsa::challenge_poly(s, c);
  // The polynomial 1.
  std::vector<typename AF::Elt> unit(kN, f.zero());
  unit[0] = f.one();
  const auto one = constant(f, unit);
  const auto d = f.of_scalar(uint64_t(1) << examples::mldsa::kD);
  std::vector<ops::SpectralRow<AF>> rows;
  for (size_t i = 0; i < kK; ++i)
    rows.push_back(ops::spectral_row(
        w[i], ops::SpectralMatVec(k.a_hat[i], z, ntt) -
                      d * ops::SpectralProduct(c_hat, k.t1[i], ntt)));
  rows.push_back(
      ops::spectral_row(cpoly, ops::SpectralProduct(c_hat, one, ntt)));
  ops::assert_spectral(s, "relation", rows);
  return w;
}

// FIPS 204's NTT over a Goldilocks field: Algorithm 41 sends coefficients
// to residues mod q, and its integer matrix with entries centered in
// [-(q - 1)/2, (q - 1)/2] (entry (k, i) = NTT(e_i)[k]) sends integer
// coefficients to integers congruent mod q to their transform. Each row
// reads 256 coefficients and its absolute values sum to at most s =
// abs_row_sum <= 256 (q - 1)/2 (s = 557,395,231 < 2^29.06 for this
// matrix). Over Goldilocks (p > 2^63) a product stays exact while its
// interval spans less than p.
namespace host {
struct FipsNttMatrix {
  // Sparse rows and columns: (index, centered entry).
  std::vector<std::vector<std::pair<uint32_t, int64_t>>> rows, cols;
  Bound abs_row_sum = 0;
};
inline const FipsNttMatrix &fips_ntt_matrix() {
  static const FipsNttMatrix m = [] {
    FipsNttMatrix out;
    out.rows.resize(kN);
    out.cols.resize(kN);
    for (size_t i = 0; i < kN; ++i) {
      examples::mldsa::host::Poly e{};
      e[i] = 1;
      examples::mldsa::host::ntt(e);
      // Public entries: the branch reads no witness.
      for (size_t k = 0; k < kN; ++k) {
        if (e[k] == 0) continue;
        const int64_t v = e[k] > examples::mldsa::kQ / 2
                              ? int64_t(e[k]) - int64_t(examples::mldsa::kQ)
                              : int64_t(e[k]);
        out.rows[k].push_back({uint32_t(i), v});
        out.cols[i].push_back({uint32_t(k), v});
      }
    }
    for (const auto &r : out.rows) {
      Bound s = 0;
      for (const auto &[c, v] : r) s += Bound(v < 0 ? -v : v);
      out.abs_row_sum = std::max(out.abs_row_sum, s);
    }
    return out;
  }();
  return m;
}
// The matrix applied to each polynomial of X over the integers, every
// |x| below 2^63 (the callers' signed field values and small integers). In
// 64-bit sums: x = 2^32 hi + lo with lo in [0, 2^32), and each row's sums
// of v lo and v hi stay below 2^62 (|v| < 2^22, 256 terms), so y = lo sum +
// 2^32 hi sum exactly.
inline std::vector<__int128> fips_ntt_apply(const std::vector<__int128> &x) {
  const FipsNttMatrix &m = fips_ntt_matrix();
  std::vector<__int128> y(x.size());
  std::vector<int64_t> lo(kN), hi(kN);
  for (size_t e = 0; e < x.size() / kN; ++e) {
    for (size_t c = 0; c < kN; ++c) {
      const int64_t v = int64_t(x[e * kN + c]);
      lo[c] = int64_t(uint64_t(v) & 0xffffffffu);
      hi[c] = v >> 32;
    }
    for (size_t r = 0; r < kN; ++r) {
      int64_t sl = 0, sh = 0;
      for (const auto &[c, v] : m.rows[r]) {
        sl += v * lo[c];
        sh += v * hi[c];
      }
      y[e * kN + r] = __int128(sl) + (__int128(sh) << 32);
    }
  }
  return y;
}
// The signed integer of a canonical element V of F_p (p - |v| below zero),
// and back, for |x| < p / 2.
inline __int128 signed_of(uint64_t v) {
  return __int128(v) - __int128(Fp64G::kP) * __int128(ct::lt(Fp64G::kP / 2, v));
}
inline std::vector<__int128> signed_all(const std::vector<uint64_t> &v) {
  std::vector<__int128> out(v.size());
  for (size_t i = 0; i < v.size(); ++i) out[i] = signed_of(v[i]);
  return out;
}
inline uint64_t field_of(__int128 x) {
  const uint64_t neg = uint64_t(x >> 127) & 1;
  return uint64_t(x + __int128(Fp64G::kP) * __int128(neg));
}
// x mod q in [0, q) for |x| < q 2^40, without a branch.
inline uint64_t residue_q(__int128 x) {
  static const ct::Divisor64 dq(examples::mldsa::kQ);
  return uint64_t(dq.divmod(uint64_t(x + __int128(examples::mldsa::kQ) *
                                             (__int128(1) << 40)))
                      .r);
}
// The centered representative of a residue r in [0, q): r - q above
// (q - 1)/2.
inline __int128 centered_q(uint64_t r) {
  return __int128(r) - __int128(examples::mldsa::kQ) *
                           __int128(ct::lt((examples::mldsa::kQ - 1) / 2, r));
}
}  // namespace host

// The matrix as an operator over a Goldilocks field or extension: each
// coordinate's products accumulate in 128 bits, the positive and negative
// entries apart, and reduce once per sum.
template <class F>
class FipsNttOperator final : public LinearOperator<F> {
  using Elt = typename F::Elt;
  using Lists = std::vector<std::vector<std::pair<uint32_t, int64_t>>>;
  static constexpr size_t kD = sizeof(Elt) / sizeof(uint64_t);
  static_assert(sizeof(Elt) == kD * sizeof(uint64_t) &&
                    std::is_trivially_copyable_v<Elt>,
                "FipsNtt: a field of plain 64-bit coordinates");

 public:
  size_t rows() const override { return kN; }
  size_t cols() const override { return kN; }
  void apply(const Elt *x, Elt *y) const override {
    mul(host::fips_ntt_matrix().rows, x, y);
  }
  void transpose_apply(const Elt *y, Elt *x) const override {
    mul(host::fips_ntt_matrix().cols, y, x);
  }

 private:
  static void mul(const Lists &lists, const Elt *in, Elt *out) {
    std::vector<uint64_t> v(kN * kD);
    std::memcpy(v.data(), in, kN * sizeof(Elt));
    for (size_t r = 0; r < kN; ++r) {
      unsigned __int128 pos[kD] = {}, neg[kD] = {};
      for (const auto &[c, e] : lists[r]) {
        const uint64_t a = uint64_t(e < 0 ? -e : e);
        unsigned __int128 *acc = e < 0 ? neg : pos;
        for (size_t d = 0; d < kD; ++d)
          acc[d] += (unsigned __int128)v[c * kD + d] * a;
      }
      uint64_t o[kD];
      for (size_t d = 0; d < kD; ++d) {
        const uint64_t a = Fp64G::reduce128(pos[d]);
        const uint64_t b = Fp64G::reduce128(neg[d]);
        o[d] = a >= b ? a - b : a + (Fp64G::kP - b);
      }
      std::memcpy(static_cast<void *>(&out[r]), o, sizeof(Elt));
    }
  }
};

// FIPS 204's NTT as a public operator of one polynomial (the centered
// matrix), batched over leading axes; its rows' absolute values sum to at
// most s (interval propagation).
template <class F>
Op<F> FipsNtt(const F &f) {
  std::vector<uint8_t> params;
  put_u64(params, kN);
  put_u64(params, examples::mldsa::kQ);
  put_u64(params, examples::mldsa::kPsi);
  return linear_operator<F>({
      .name = "fips204_ntt_centered",
      .params = std::move(params),
      .rows = kN,
      .cols = kN,
      .make = [](const F &) { return std::make_shared<FipsNttOperator<F>>(); },
      .abs_row_sum = host::fips_ntt_matrix().abs_row_sum,
      .field = &f,
  });
}

// ẑ = NTT(z) mod q: advice [L][N], residues in [0, q) below 4096^2 (two
// digits), and assert_mod(ẑ, FipsNtt(z), q), its quotient in digits. z is
// the signed coefficient of the carrier, |z| < gamma1 - beta by its norm
// request, so |FipsNtt(z)| < 2^46.06. Returns ẑ.
template <class D, class AF, class PZ>
Ref<AF, Subfield<>, Committed> z_spectrum(const Scope &s, D &A,
                                          const Ref<AF, Subfield<>, PZ> &z) {
  const auto z_hat = s[A].priv(
      Subfield{}, "z_hat", Shape{kL, kN}, depends_on(z),
      [](const std::vector<uint64_t> &x) {
        const auto y = host::fips_ntt_apply(host::signed_all(x));
        std::vector<uint64_t> r(y.size());
        for (size_t i = 0; i < y.size(); ++i) r[i] = host::residue_q(y[i]);
        return r;
      });
  assert_range(z_hat, kT * kT, s.name("z_hat"));
  assert_mod(z_hat, FipsNtt(A.field())(z), examples::mldsa::kQ,
             s.name("z_hat.mod"));
  return z_hat;
}

// ĉ' = NTT(2^d c) mod q, centered: advice [N] in [-(q - 1)/2, (q - 1)/2]
// (a two-sided range request) and assert_mod(ĉ', 2^d FipsNtt(c), q)
// over the challenge's coefficients c = support - 2 sign. Returns ĉ'.
template <class D, class AF>
Ref<AF, Subfield<>, Committed> challenge_spectrum(
    const Scope &s, D &A, const Ref<AF, Bit, Committed> &c) {
  const AF &f = A.field();
  constexpr uint64_t kHalf = (examples::mldsa::kQ - 1) / 2;
  const auto c_hat = s[A].priv(
      Subfield{}, "c_hat", Shape(kN), depends_on(c),
      [](const std::vector<uint64_t> &cb) {
        std::vector<__int128> x(kN);
        for (size_t i = 0; i < kN; ++i)
          x[i] = (__int128(cb[2 * i]) - 2 * __int128(cb[2 * i + 1])) *
                 (__int128(1) << examples::mldsa::kD);
        const auto y = host::fips_ntt_apply(x);
        std::vector<uint64_t> r(kN);
        for (size_t i = 0; i < kN; ++i)
          r[i] = host::field_of(host::centered_q(host::residue_q(y[i])));
        return r;
      });
  assert_centered_range(c_hat, kHalf, s.name("c_hat"));
  const auto cpoly = examples::mldsa::challenge_poly(s, c);
  assert_mod(c_hat,
             f.of_scalar(uint64_t(1) << examples::mldsa::kD) *
                 FipsNtt(f)(cpoly),
             examples::mldsa::kQ, s.name("c_hat.mod"));
  return c_hat;
}

// t̂1, an integer congruent mod q to NTT(t1) and small: advice [K][N]
// = FipsNtt(t1 - 512) + kappa, kappa the centered residue of
// NTT(512) mod q (the shift centers t1's coefficients, below 2^10). The
// affine row t̂1 = FipsNtt(t1) - gamma, gamma = FipsNtt(512) -
// kappa (a multiple of q), ties it to the crossed t1; no range request.
// |t̂1| <= 512 s + (q - 1)/2, s the transform's absolute row sum.
template <class D, class AF>
Ref<AF, Subfield<>, Committed> key_spectrum(const Scope &s, D &A,
                                            const DeviceKey<AF> &k) {
  const AF &f = A.field();
  // FipsNtt(512) exactly, and kappa.
  const std::vector<__int128> shifted =
      host::fips_ntt_apply(std::vector<__int128>(kN, 512));
  std::vector<__int128> gamma(kN), kappa(kN);
  for (size_t i = 0; i < kN; ++i) {
    kappa[i] = host::centered_q(host::residue_q(shifted[i]));
    gamma[i] = shifted[i] - kappa[i];
  }
  const auto t1_hat = s[A].priv(
      Subfield{}, "t1_hat", Shape{kK, kN}, depends_on(k.t1_bits),
      [kappa](const std::vector<uint64_t> &tb) {
        const std::vector<uint64_t> t = host::integers(tb, kT1Bits);
        std::vector<__int128> x(t.size());
        for (size_t i = 0; i < t.size(); ++i) x[i] = __int128(t[i]) - 512;
        const auto y = host::fips_ntt_apply(x);
        std::vector<uint64_t> r(y.size());
        for (size_t i = 0; i < y.size(); ++i)
          r[i] = host::field_of(y[i] + kappa[i % kN]);
        return r;
      });
  std::vector<typename AF::Elt> g(kK * kN);
  for (size_t i = 0; i < g.size(); ++i)
    g[i] = f.of_scalar(host::field_of(gamma[i % kN]));
  const auto gamma_c = constant(f, g, Shape{kK, kN});
  assert_zero(t1_hat - FipsNtt(f)(k.t1) + gamma_c, s.name("t1_hat"));
  return t1_hat;
}

// The device's relation in q's NTT domain over a Goldilocks field
// (GoldilocksArm): with ẑ (z_spectrum), ĉ'
// (challenge_spectrum) and t̂1 (key_spectrum),
//   w            w' = A z - 2^d c t1 mod q, advice [K][N], below 4096^2
//   relation.w_hat  W = FipsNtt(w'), advice [K][N], an affine row
//   relation     sum_j A_hat[i][j] o ẑ_j - ĉ' o t̂1_i - W_i = q (Q_i - qlo)
//                with Q in base-4096 digits, three below 4096 and the top
//                one below TOP, one predicate per row i,
// so NTT(w') = NTT(A z - 2^d c t1) mod q coordinatewise, and w' = A z -
// 2^d c t1 mod q since the transform is a bijection. Interval bounds
// (certified): A_hat below 2^23, ẑ below 4096^2, |ĉ'| <= (q - 1)/2,
// |t̂1| <= 512 s + (q - 1)/2, |W| <= s (4096^2 - 1). Returns w'.
template <class D, class AF, class PZ>
Ref<AF, Subfield<>, Committed> goldilocks_device_relation(
    const Scope &s, D &A, const DeviceKey<AF> &k,
    const Ref<AF, Subfield<>, PZ> &z, const Ref<AF, Bit, Committed> &c) {
  const AF &f = A.field();
  const uint64_t p = Fp64G::kP;
  const auto w = s[A].priv(
      Subfield{}, "w", Shape{kK, kN}, depends_on(k.a_bits, k.t1_bits, z, c),
      [p](const std::vector<uint64_t> &ab, const std::vector<uint64_t> &tb,
          const std::vector<uint64_t> &zz, const std::vector<uint64_t> &cb) {
        std::vector<uint64_t> zq(zz.size());
        for (size_t i = 0; i < zz.size(); ++i)
          zq[i] = examples::mldsa::emulated::host::residue(zz[i], p);
        return examples::mldsa::host::w_prime(host::integers(ab, 23),
                                    host::integers(tb, kT1Bits), zq, cb);
      });
  assert_range(w, kT * kT, s.name("w"));
  const auto z_hat = z_spectrum(s.scope("z"), A, z);
  const auto c_hat = challenge_spectrum(s.scope("c"), A, c);
  const auto t1_hat = key_spectrum(s.scope("t1"), A, k);

  const auto sr = s.scope("relation");
  const auto w_hat = sr[A].priv(
      Subfield{}, "w_hat", Shape{kK, kN}, depends_on(w),
      [](const std::vector<uint64_t> &x) {
        const auto y = host::fips_ntt_apply(host::signed_all(x));
        std::vector<uint64_t> r(y.size());
        for (size_t i = 0; i < y.size(); ++i) r[i] = host::field_of(y[i]);
        return r;
      });
  assert_zero(w_hat - FipsNtt(f)(w), sr.name("w_hat"));

  // The bounds of X = sum_j A_hat o ẑ_j - ĉ' o t̂1 - W, and Q's.
  const Bound S = host::fips_ntt_matrix().abs_row_sum;
  const Bound a_max = (Bound(1) << 23) - 1;
  const Bound z_max = Bound(kT) * kT - 1;
  const Bound c_max = (examples::mldsa::kQ - 1) / 2;
  const Bound t1_max = 512 * S + (examples::mldsa::kQ - 1) / 2;
  const Bound w_max = S * (Bound(kT) * kT - 1);
  // -lo
  const Bound neg = c_max * t1_max + w_max;
  // hi
  const Bound pos = Bound(kL) * a_max * z_max + neg;
  const Bound qlo = (neg + examples::mldsa::kQ - 1) / examples::mldsa::kQ;
  const Bound qn =
      (pos + Bound(examples::mldsa::kQ) * qlo) / examples::mldsa::kQ + 1;
  // Q in base-4096 digits d0, d1, d2 below 4096 and d3 below TOP, so Q
  // spans [0, TOP 4096^3 - 1], at least [0, Qn - 1].
  const Bound t3 = Bound(kT) * kT * kT;
  const Bound top = (qn + t3 - 1) / t3;
  sr.note("certify", "top", term("TOP", top) < term("4096", kT), A);
  sr.note("certify", "nowrap", term("L 2^23 4096^2 + 2 ((q-1)/2 (512 s + (q-1)/2) + s 4096^2) "
                  "+ q (TOP 4096^3 - 1)",
                  pos + neg + Bound(examples::mldsa::kQ) * (top * t3 - 1)) <
                 term("p", field_characteristic(f)), A);
  const uint64_t qlo64 = uint64_t(qlo);
  const auto digits = sr[A].priv(
      Subfield{}, "q", Shape{4, kK, kN},
      depends_on(k.a_bits, z_hat, c_hat, t1_hat, w_hat),
      [qlo64](const std::vector<uint64_t> &ab, const std::vector<uint64_t> &zh,
              const std::vector<uint64_t> &ch, const std::vector<uint64_t> &th,
              const std::vector<uint64_t> &wh) {
        static const ct::Divisor64 dq(examples::mldsa::kQ);
        const std::vector<uint64_t> a = host::integers(ab, 23);
        std::vector<uint64_t> out(4 * kK * kN);
        for (size_t i = 0; i < kK; ++i)
          for (size_t n = 0; n < kN; ++n) {
            __int128 x = -host::signed_of(ch[n]) * host::signed_of(th[i * kN + n]) -
                         host::signed_of(wh[i * kN + n]);
            for (size_t j = 0; j < kL; ++j)
              x += __int128(a[(i * kL + j) * kN + n]) *
                   __int128(zh[j * kN + n]);
            const __int128 u =
                x + __int128(examples::mldsa::kQ) * __int128(qlo64);
            const uint64_t qv = uint64_t(dq.divmod(uint64_t(u)).q);
            for (size_t d = 0; d < 4; ++d)
              out[(d * kK + i) * kN + n] =
                  (qv >> (12 * d)) & (d < 3 ? 4095 : ~uint64_t(0));
          }
        return out;
      });
  for (size_t d = 0; d < 3; ++d)
    assert_range(digits[d], kT, sr.name("q.d" + std::to_string(d)));
  assert_range(digits[3], top, sr.name("q.d3"));
  // Q_i, row i of Q = sum_d 4096^d digits[d].
  auto quot = [&digits](size_t i) {
    return digits[0][i] + kT * digits[1][i] +
           kT * kT * digits[2][i] + kT * kT * kT * digits[3][i];
  };
  const typename AF::Elt bias =
      f.of_scalar(uint64_t(Bound(examples::mldsa::kQ) * qlo));
  for (size_t i = 0; i < kK; ++i) {
    Expr<AF, Field> x = k.a_hat[i][0] * z_hat[0];
    for (size_t j = 1; j < kL; ++j)
      x = x + k.a_hat[i][j] * z_hat[j];
    assert_zero(x - c_hat * t1_hat[i] - w_hat[i] -
                       examples::mldsa::kQ * quot(i) + bias,
                   sr.name(std::to_string(i)));
  }
  return w;
}

// The arms of domain A. Each names the issuer key's form, the two
// signature relations and UseHint's arm:
//   FqArm          A over F_q^k, ML-DSA's arithmetic native (the proof of
//                  possession's affine rows for the issuer, device_relation
//                  in FIPS 204's spectrum for the device)
//   GoldilocksArm  A over a Goldilocks extension, ML-DSA's arithmetic mod q
//                  emulated (the emulated proof of possession's assert_mod
//                  for the issuer, goldilocks_device_relation for the
//                  device, and UseHint's wrap Bit quotient)
struct FqArm {
  static constexpr const char *kName = "fq";
  static constexpr ops::Form kIssuerKeyForm = ops::Form::kNtt;
  static examples::mldsa::UseHintArm use_hint() {
    return examples::mldsa::UseHintArm{};
  }
  template <class D, class KF, class AF, class PZ>
  static auto issuer_relation(const Scope &s, D &A,
                              const examples::mldsa::Key<KF, AF> &key,
                              const Ref<AF, Subfield<>, PZ> &z,
                              const Ref<AF, Bit, Committed> &c) {
    return examples::mldsa::signature_relation(s, A, key, z, c);
  }
  template <class D, class AF, class PZ>
  static auto device_relation(const Scope &s, D &A,
                              const DeviceKey<AF> &k,
                              const Ref<AF, Subfield<>, PZ> &z,
                              const Ref<AF, Bit, Committed> &c) {
    return examples::pq_mdoc::device_relation(s, A, k, z, c);
  }
};
struct GoldilocksArm {
  static constexpr const char *kName = "goldilocks";
  static constexpr ops::Form kIssuerKeyForm = ops::Form::kCoefficients;
  static examples::mldsa::UseHintArm use_hint() {
    return examples::mldsa::UseHintArm{/*wrap=*/true};
  }
  template <class D, class KF, class AF, class PZ>
  static auto issuer_relation(const Scope &s, D &A,
                              const examples::mldsa::Key<KF, AF> &key,
                              const Ref<AF, Subfield<>, PZ> &z,
                              const Ref<AF, Bit, Committed> &c) {
    return examples::mldsa::emulated::signature_relation(s, A, key, z, c);
  }
  template <class D, class AF, class PZ>
  static auto device_relation(const Scope &s, D &A,
                              const DeviceKey<AF> &k,
                              const Ref<AF, Subfield<>, PZ> &z,
                              const Ref<AF, Bit, Committed> &c) {
    return goldilocks_device_relation(s, A, k, z, c);
  }
};

// One signature's hashes in domain H from its mu: H's copy of A's w1, c~'
// and the SampleInBall stream in the shared Keccak batch KECCAK, and
// SampleInBall; then H's challenge equals A's. Both equalities belong to
// the system's MAC. Scope S is the signature's.
template <class D, class K, class HF, class PM, class AF>
void signature_hash_domain(const Scope &s, D &H, const K &keccak,
                         const Ref<HF, Bit, PM> &mu,
                         const Ref<AF, Bit, Committed> &w1_A,
                         const Ref<AF, Bit, Committed> &c_A) {
  const auto w1 = s[H].copy_of("w1", w1_A);
  const auto h2c = s.scope("h2c");
  const auto c_H = examples::mldsa::challenge_from_mu(
      h2c, H, keccak.rescoped(h2c[H]), mu, w1);
  assert_same_bits(c_H.flat(), c_A.flat());
}

// The device's signature, step 3 of the relation, in scope SD: tr_D and
// mu_D over the statement's M_D (DEVICE_TBS, its bits in H) and ExpandA of
// the key's rho in H (the Keccak batch KECCAK), the device key DPK (the
// deviceKeyInfo window's bits in H) crossed into A (device_key_crossing),
// the arm's device relation and the signature's checks on the witness's
// signature SIG. The device-signature ablation (pq_mdoc_relation's
// DEVICE_SIGNATURE false) omits exactly this call.
template <class Arm, class DH, class DA, class K, class HF, class PD,
          class PT, class SW>
void device_signature_check(const Scope &sd, DH &H, DA &A, const K &keccak,
                            const Ref<HF, Bit, PD> &dpk,
                            const Ref<HF, Bit, PT> &device_tbs,
                            const SW &sig) {
  const auto kd = keccak.rescoped(sd[H]);
  const auto tr_d =
      lib::keccak::shake256(kd, "tr", lib::keccak::sponge_input(dpk), kTrBytes);
  const auto mu_d = lib::keccak::shake256(
      kd, "mu",
      lib::keccak::sponge_input(tr_d.out, lib::keccak::constant_bytes({0x00, 0x00}),
                                device_tbs),
      examples::mldsa::kMuBytes);
  const auto sea = sd.scope("expand_a");
  const auto rho = dpk.slice(0, 8 * kRhoBytes).named(sd.scoped("rho"));
  const auto ea =
      examples::mldsa::expand_a_on(sea, H, rho, keccak.rescoped(sea[H]));
  const auto t1_h = dpk.slice(8 * kRhoBytes, 8 * kPkBytes)
                        .reshape({kK, kN, kT1Bits})
                        .named(sd.scoped("t1.h"));
  const auto dk = device_key_crossing(sd.scope("key"), A, ea.coefficients, t1_h);
  const auto z_d = A.priv(Subfield{}, sig.z);
  const auto h_d = A.priv(Bit{}, sig.h);
  const auto c_d =
      examples::mldsa::challenge(sd.scope("challenge"), A, sig.c_tilde);
  const auto w_d = Arm::device_relation(sd.scope("signature"), A, dk, z_d, c_d);
  const auto w1_d =
      examples::mldsa::signature_checks(sd, A, z_d, h_d, w_d, Arm::use_hint());
  signature_hash_domain(sd, H, keccak, mu_d.out, w1_d, c_d);
}

// ---------------------------------------------------------------- system --

// The statement: now and the requested attributes as v7 lays them out
// (mdoc.h's MdocStatement: attr.id[a] the text header and identifier,
// attr.value[a] the CBOR value, zeros after each, and their lengths; the
// attribute count fixed per relation by the shape value), the issuer's key
// pk_I and the device's message M_D (its length fixed per relation).
template <template <class> class F>
struct PqMdocStatement {
  // 20 ASCII bytes
  F<std::array<uint8_t, examples::mdoc::kDateBytes>> now;
  examples::mdoc::MdocAttributes<F> attr;
  F<std::array<uint8_t, kPkBytes>> issuer_pk;
  F<std::vector<uint8_t>> device_tbs;
};
// One ML-DSA signature of the witness, a record member: z (centered), the
// hint bits h and c~ (which only generators read).
template <template <class> class F>
struct SignatureWitness {
  F<std::array<std::array<int32_t, kN>, kL>> z;
  F<std::array<std::array<bool, kN>, kK>> h;
  F<std::array<uint8_t, examples::mldsa::kCTildeBytes>> c_tilde;
};
// The witness: the MSO's part of the issuer's mu buffer (kMsoBytes: the
// MSO, SHAKE256's padding, zeros) and the message length L = |tr || 00 00
// || TBS|, v7's window offsets, the items, their lengths and SaltedHash
// fields (mdoc.h's MdocWitness), and both signatures (issuer.z, ...,
// device.c_tilde).
template <template <class> class F>
struct PqMdocWitness {
  F<std::array<uint8_t, kMsoBytes>> mso;
  F<uint16_t> mso_length;
  // kFixedWindows + n
  F<std::vector<uint16_t>> offsets;
  F<std::vector<std::array<uint8_t, examples::mdoc::kItemBytes>>> items;
  F<std::vector<uint8_t>> item_lengths;
  F<std::vector<std::array<bool, examples::mdoc::kSaltedBits>>> salted;
  SignatureWitness<F> issuer;
  SignatureWitness<F> device;
};

// Post-quantum mdoc in system CS over the statement ST and the witness W:
// H at H_PROFILE (declared first), A at A_PROFILE in ARM (FqArm, the
// default, or GoldilocksArm), every SHAKE call in one Keccak batch and the
// items' SHA-256 in one batch. DEVICE_SIGNATURE false is a test-only
// ablation (the device-signature ablation): step 3 (device_signature_check)
// is not declared, so M_D and the witness's device signature are never
// read; the deviceKeyInfo window, which the issuer signs, stays.
template <class Arm = FqArm, class Sys, class HP, class AP>
void pq_mdoc_relation(Sys &cs, const PqMdocStatement<In> &st,
                      const PqMdocWitness<In> &w, const HP &h_profile,
                      const AP &a_profile, bool device_signature = true) {
  auto &H = cs.domain(h_profile, "H");
  auto &A = cs.domain(a_profile, "A");
  using HF = std::decay_t<decltype(H.field())>;

  // The statement.
  const auto hash_in = examples::mdoc::mdoc_hash_inputs(H, st);
  const size_t n_attr = hash_in.attributes.size();
  if (n_attr == 0) fail("pq_mdoc: no attribute");
  const auto si = cs.scope("issuer");
  const auto key =
      examples::mldsa::mldsa_key_of<HF>(si, A, st.issuer_pk, Arm::kIssuerKeyForm);
  // The issuer key's statement bounds in the coefficient form: A's
  // coefficients below q, t1's below 2^10, as the emulated ML-DSA relation
  // declares them. The interval of the issuer's signature relation reads
  // them; the verifier computes both from pk, so an honest statement always
  // meets them.
  if constexpr (Arm::kIssuerKeyForm == ops::Form::kCoefficients) {
    key.a_hat.bounded(examples::mldsa::kQ);
    key.t1.bounded(examples::mldsa::emulated::kT1Bound);
  }
  // M_D's bits in H, read only for the device's signature.
  using TbsBits = decltype(st.device_tbs.bits(H).flat());
  std::optional<TbsBits> device_tbs;
  if (device_signature) device_tbs = st.device_tbs.bits(H).flat();
  // tr_I = SHAKE256(pk_I, 64), cached per statement.
  auto sih = si[H];
  const auto tr_i = examples::mldsa::key_hash(sih, st.issuer_pk);

  // The MSO, and its in-message flags from the length.
  const auto mso = H.priv(w.mso).flat();
  // The length counts the head: a buffer with no head.
  const auto in_message = lib::message::in_message(
      H, "mso.in_message",
      lib::message::Layout{0, kMaxMessageBytes, kBufBytes}, w.mso_length);

  // The attribute items' SHA-256, one batch.
  const auto sc = cs.scope("hash");
  const auto sha = lib::sha256::sha256_batch(
      sc[H], "sha", lib::sha256::Sha256Mode::kBatched);
  const auto items = H.priv(w.items);
  const auto salted = H.priv(w.salted);
  const auto it =
      examples::mdoc::mdoc_items(cs, H, sha, items, salted, w.item_lengths);

  // The windows over the MSO.
  const lib::windows::WindowText<HF> text{
      mso, in_message.slice(kHeadBytes, kBufBytes).named("mso.in_text"),
      kWindowFirst, kWindowEnd};
  std::vector<lib::windows::Window<HF>> windows;
  const auto from = lib::windows::keyed_window(
      cs, H, windows, "windows.valid_from.date", text, w.offsets,
      examples::mdoc::valid_from_key(), examples::mdoc::kDateBytes);
  const auto until = lib::windows::keyed_window(
      cs, H, windows, "windows.valid_until.date", text, w.offsets,
      examples::mdoc::valid_until_key(), examples::mdoc::kDateBytes);
  const auto dpk =
      lib::windows::keyed_window(cs, H, windows, "device.pk", text, w.offsets,
                                 device_key_info_key(), kPkBytes);
  windows.push_back(
      {{lib::windows::window_part<HF>(examples::mdoc::value_digests_key())}});
  for (const auto &d : it.digests)
    windows.push_back(
        {{lib::windows::window_part<HF>(examples::mdoc::digest_key()),
          lib::windows::window_part(d)}});
  lib::windows::match_windows(cs.scope("windows"), H, "match", text, w.offsets,
                              windows);
  examples::mdoc::mdoc_validity(H, from, until, hash_in.now);
  examples::mdoc::mdoc_attribute_checks(H, it.items, it.salted,
                                        hash_in.attributes);

  // Every SHAKE call in one Keccak batch.
  const auto kc = cs.scope("keccak");
  const auto keccak = lib::keccak::keccak_batch(kc[H], "batch");

  // 1. The issuer: mu_I over the MSO, then the proof of possession's A.
  std::vector<uint8_t> head = {0x00, 0x00};
  head.insert(head.end(), cose_prefix().begin(), cose_prefix().end());
  const auto mu_i = lib::keccak::shake256_varlen(
      keccak.rescoped(si[H]), "mu",
      lib::keccak::sponge_input(tr_i, lib::keccak::constant_bytes(head), mso),
      in_message, examples::mldsa::kMuBytes, kHeadBytes + kWindowFirst,
      kMaxMessageBytes);
  const auto z_i = A.priv(Subfield{}, w.issuer.z);
  const auto h_i = A.priv(Bit{}, w.issuer.h);
  const auto c_i =
      examples::mldsa::challenge(si.scope("challenge"), A, w.issuer.c_tilde);
  const auto w_i =
      Arm::issuer_relation(si.scope("signature"), A, key, z_i, c_i);
  const auto w1_i =
      examples::mldsa::signature_checks(si, A, z_i, h_i, w_i, Arm::use_hint());
  signature_hash_domain(si, H, keccak, mu_i, w1_i, c_i);

  // 3. The device's signature (device_signature_check), unless ablated.
  if (device_signature)
    device_signature_check<Arm>(cs.scope("device"), H, A, keccak, dpk,
                                *device_tbs, w.device);
}

// A statement and a witness of N_ATTR attributes and a device message of
// DEVICE_TBS_BYTES bytes as shape values (their vectors' lengths) for
// compile().
inline PqMdocStatement<Value> pq_mdoc_statement_shape(size_t n_attr,
                                                     size_t device_tbs_bytes) {
  PqMdocStatement<Value> st{};
  examples::mdoc::shape_hash_statement(st, n_attr);
  st.device_tbs.resize(device_tbs_bytes);
  return st;
}
inline PqMdocWitness<Value> pq_mdoc_witness_shape(size_t n_attr) {
  PqMdocWitness<Value> w{};
  examples::mdoc::shape_hash_witness(w, n_attr);
  return w;
}

// The relation for N_ATTR attributes and a device message of
// DEVICE_TBS_BYTES bytes in system type SYS and arm ARM, compiled under
// PROFILE with OPTIONS as the system NAME; DEVICE_SIGNATURE false is the
// device-signature ablation (pq_mdoc_relation).
template <class Arm = FqArm, class Sys, class HP, class AP>
Relation<PqMdocStatement<Value>, PqMdocWitness<Value>> pq_mdoc(
    const CompileProfile &profile, const std::string &name,
    const HP &h_profile, const AP &a_profile, size_t n_attr,
    size_t device_tbs_bytes, bool device_signature = true,
    const CompileOptions &options = {}) {
  return compile<PqMdocStatement, PqMdocWitness>(
      profile,
      [&](Sys &cs, PqMdocStatement<In> st, PqMdocWitness<In> w) {
        pq_mdoc_relation<Arm>(cs, st, w, h_profile, a_profile,
                              device_signature);
      },
      name, pq_mdoc_statement_shape(n_attr, device_tbs_bytes),
      pq_mdoc_witness_shape(n_attr), options);
}

}  // namespace proofs::gordiehowe::examples::pq_mdoc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_H_
