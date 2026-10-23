// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines, fork-derived: the fork's lib/algebra/fp_native_wide.h
// (mac-bench 8d8e0aa4), the wide profile's ML-DSA field GF(q^11) =
// F_q[X]/(X^11 - 2), q = 8380417.  Unchanged apart from this note, the
// namespace, the base field (fp24q.h) and the removal of the Falcon
// instantiations; the class template keeps its Falcon tower branch, which
// MlDsaField11 does not instantiate.
#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_MLDSA_FIELD11_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_MLDSA_FIELD11_H_

#include <stddef.h>

#include <array>
#include <cstdint>
#include <functional>
#include <iterator>
#include <optional>
#include <utility>

#include "algebra/fp24.h"
#include "fp24q.h"
#include "util/panic.h"

namespace proofs {
namespace ml_dsa_split {
// Both kernels have fixed control flow and public memory indices. The AVX2
// target benefits from coefficient Karatsuba; the portable Falcon build keeps
// the packed-limb convolution. ML-DSA uses Karatsuba on both targets.
enum class NativeConvolution { kPacked, kKaratsuba };
#if defined(__AVX2__)
inline constexpr auto kFalconConvolution = NativeConvolution::kKaratsuba;
#else
inline constexpr auto kFalconConvolution = NativeConvolution::kPacked;
#endif

template <class Base, size_t kDeg, uint32_t kBetaN, uint32_t kLinear = 0,
          bool kDelayed = false,
          NativeConvolution kKernel = NativeConvolution::kPacked,
          bool kTower = false>
class NativeWide {
public:
  using BaseField = Base;
  using Scalar = typename BaseField::Elt;
  using TypeTag = typename BaseField::TypeTag;
  using CElt = typename BaseField::CElt;

  static constexpr size_t kDegree = kDeg;
  static constexpr bool kTower20 = kTower;
  static_assert(!kTower || (Base::m_ == 12289 && kDeg == 20 &&
                           kBetaN == 11 && kLinear == 2), "Falcon tower constants");
  // Tower coordinates e[4*j+i] represent u^i v^j, u^4=11, v^5=u+2.
  // The extra protocol tag distinguishes this basis from a flat polynomial.

  static constexpr auto kProtocolFieldId = [] {
    if constexpr (kTower)
      return std::array<uint64_t, 5>{Base::m_, kDeg, kBetaN, kLinear,
                                     0x746f776572347835ULL};
    else
      return std::array<uint64_t, 4>{Base::m_, kDeg, kBetaN, kLinear};
  }();
  static constexpr size_t kIntegerBits = [] {
    size_t n = 0;
    for (uint64_t q = Base::m_; q > 1; q >>= 1)
      ++n;
    return n;
  }();

  // Canonical little-endian bitstream of fixed-width base coefficients.
  // Padding in the final byte is zero. This changes the proof wire format.
  static constexpr size_t kCoefficientBits = kIntegerBits + 1;
  static constexpr size_t kBytes = (kDegree * kCoefficientBits + 7) / 8;
  static constexpr size_t kBits = kDegree * BaseField::kBits;
  static constexpr size_t kSubFieldBytes = BaseField::kBytes;
  static constexpr size_t kSubFieldBits = BaseField::kBits;
  static constexpr bool kCharacteristicTwo = false;
  static constexpr size_t kNPolyEvaluationPoints =
      BaseField::kNPolyEvaluationPoints;

  struct Elt {
    std::array<Scalar, kDegree> e{};
    bool operator==(const Elt &y) const {
      uint32_t v = 0;
      for (size_t i = 0; i < kDegree; ++i)
        v |= e[i].n ^ y.e[i].n;
      return v == 0;
    }
    bool operator!=(const Elt &y) const { return !operator==(y); }
  };

  // Flat modulus X^degree - kLinear*X - beta, or the certified 4x5
  // tower specified above. beta is the lower quartic constant in the tower.
  static constexpr uint32_t beta_ = kBetaN;

  explicit NativeWide(const BaseField &F, const uint32_t beta = beta_) : f_(F) {
    check(beta == beta_, "NativeWide is specialised to its compile-time beta");
    // beta must be a valid base-field element. Convolution and reduction
    // bounds are checked separately by the compile-time assertions.
    check(f_.fits(beta), "beta not in base field");

    for (uint64_t i = 0; i < std::size(k_); ++i) {
      k_[i] = of_scalar(i);
    }
    khalf_ = of_scalar(f_.half());
    kmone_ = of_scalar(f_.mone());
    // Public setup only. Generic sparse moduli use a fixed dense Frobenius map.
    if constexpr (kLinear != 0 || (Base::m_ - 1) % kDegree != 0) {
      for (size_t i = 0; i < kDegree; ++i) {
        Elt x{};
        x.e[i] = f_.one();
        frob_[i] = power(x, Base::m_);
      }
    } else {
      Scalar scale = scalar_power(Scalar{beta_}, (Base::m_ - 1) / kDegree);
      Scalar v = f_.one();
      for (size_t i = 0; i < kDegree; ++i) {
        frob_[i].e[i] = v;
        f_.mul(v, scale);
      }
    }
    for (size_t i = 0; i < kDegree; ++i)
      frob_powers_[0][i].e[i] = f_.one();
    frob_powers_[1] = frob_;
    for (size_t k = 2; k < kDegree; ++k)
      for (size_t i = 0; i < kDegree; ++i)
        frob_powers_[k][i] = frobenius(frob_powers_[k - 1][i], 1);
  }

  // NativeWide is not copyable or assignable because it holds a reference to a
  // Field and precomputes constants based on that field.
  NativeWide(const NativeWide &) = delete;
  NativeWide &operator=(const NativeWide &) = delete;

  const BaseField &base_field() const { return f_; }

  // Largest Reed-Solomon evaluation domain this field admits.
  //
  // The RS encoder in algebra/reed_solomon.h evaluates at the points
  // of_scalar(0), of_scalar(1), ..., of_scalar(m-1) and inverts their
  // pairwise differences, so those images must be distinct and nonzero
  // apart.  That is a property of the field, NOT of its serialization
  // width: see the note in ligero/ligero_param.h.
  // The extension encoder (algebra/reed_solomon_extension*.h) evaluates in
  // the BASE field and encodes componentwise -- which is exactly what keeps a
  // subfield-valued row subfield-valued after encoding.
  size_t max_rs_domain() const { return f_.max_rs_domain(); }

  void add(Elt &a, const Elt &y) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.add(a.e[i], y.e[i]);
    }
  }
  void sub(Elt &a, const Elt &y) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.sub(a.e[i], y.e[i]);
    }
  }
  // Kronecker substitution, generalised to any degree.  Pack the kDegree
  // coefficients into ceil(kDegree/2) 64-bit limbs at 32-bit stride (the top
  // half-slot is zero when kDegree is odd), take one exact limb-by-limb
  // product, then read the 2*kDegree-1 convolution coefficients back out at
  // the same stride.  A conv coeff is a sum of at most kDegree products of
  // 14-bit residues, so it is at most kDegree*(m-1)^2 -- 3.63e9 at degree24 --
  // which is below 2^32 and cannot overflow its slot or carry into the next.
  // The 32-bit slot is safe only for a ~14-bit modulus; a modulus near 2^16
  // would need wider slots. The fallback uses 64-bit convolution coefficients.
  // Reduction applies x^kDegree = beta + kLinear*x.
  static constexpr size_t kLimbs = (kDegree + 1) / 2;

  static constexpr size_t kConvolutionSize = kTower ? 63 : 2 * kDegree - 1;
  using Convolution = std::array<uint64_t, kConvolutionSize>;

  void mul(Elt &a, const Elt &y) const {
    a = reduce_convolution(convolve(a, y));
  }

  Convolution convolve(const Elt &a, const Elt &y) const {
    if constexpr (kTower) {
      return tower_convolve(a, y);
    } else if constexpr (kKernel == NativeConvolution::kKaratsuba) {
      std::array<uint64_t, kDegree> x{}, z{};
      for (size_t i = 0; i < kDegree; ++i) {
        x[i] = a.e[i].n;
        z[i] = y.e[i].n;
      }
      return karatsuba(x, z);
    } else if constexpr (kDegree * uint64_t(Base::m_ - 1) * (Base::m_ - 1) <
                         (uint64_t{1} << 32)) {
      uint64_t al[kLimbs]{}, bl[kLimbs]{}, r[2 * kLimbs]{};
      for (size_t i = 0; i < kDegree; ++i) {
        al[i / 2] |= uint64_t(a.e[i].n) << (32 * (i % 2));
        bl[i / 2] |= uint64_t(y.e[i].n) << (32 * (i % 2));
      }
      for (size_t i = 0; i < kLimbs; ++i) {
        uint64_t carry = 0;
        for (size_t j = 0; j < kLimbs; ++j) {
          __uint128_t t = __uint128_t(al[i]) * bl[j] + r[i + j] + carry;
          r[i + j] = uint64_t(t);
          carry = uint64_t(t >> 64);
        }
        r[i + kLimbs] += carry;
      }
      std::array<uint64_t, 2 * kDegree - 1> c{};
      for (size_t i = 0; i < c.size(); ++i)
        c[i] = (r[i / 2] >> (32 * (i % 2))) & 0xffffffff;
      return c;
    } else {
      Convolution c{};
      for (size_t i = 0; i < kDegree; ++i)
        for (size_t j = 0; j < kDegree; ++j)
          c[i + j] += uint64_t(a.e[i].n) * y.e[j].n;
      return c;
    }
  }
  Elt mulf_schoolbook(const Elt &a, const Elt &b) const {
    Convolution c{};
    for (size_t i = 0; i < kDegree; ++i)
      for (size_t j = 0; j < kDegree; ++j) {
        const size_t pos = kTower ? 7 * (i / 4 + j / 4) + i % 4 + j % 4 : i + j;
        c[pos] += uint64_t(a.e[i].n) * b.e[j].n;
      }
    return reduce_convolution(c);
  }
  void mul(Elt &a, const Scalar &y) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.mul(a.e[i], y);
    }
  }
  void neg(Elt &x) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.neg(x.e[i]);
    }
  }
  Elt frobenius(Elt x, size_t k = 1) const {
    k %= kDegree;
    if (k == 0)
      return x;
    Elt y{};
    if constexpr (kTower) {
      // Frobenius permutes the five v-blocks; within each block it is a
      // fixed 4x4 map over Fq. All destinations and scales are public.
      size_t exponent = (k & 1) ? 4 : 1; // q == -1 mod 5
      for (size_t j = 0; j < 5; ++j) {
        const size_t dst = j * exponent % 5;
        for (size_t h = 0; h < 4; ++h) {
          uint64_t sum = 0;
          for (size_t i = 0; i < 4; ++i)
            sum += uint64_t(x.e[4 * j + i].n) *
                   frob_powers_[k][4 * j + i].e[4 * dst + h].n;
          y.e[4 * dst + h] = f_.reduce(sum);
        }
      }
    } else if constexpr (kLinear == 0) {
      // A binomial basis has monomial Frobenius images even when degree
      // does not divide q-1 (e.g. Falcon degree18). All indices are public.
      size_t exponent = 1;
      for (size_t j = 0; j < k; ++j)
        exponent = exponent * (Base::m_ % kDegree) % kDegree;
      for (size_t i = 0; i < kDegree; ++i) {
        const size_t dest = i * exponent % kDegree;
        y.e[dest] = f_.mulf(x.e[i], frob_powers_[k][i].e[dest]);
      }
    } else {
      for (size_t j = 0; j < kDegree; ++j) {
        uint64_t v = 0;
        for (size_t i = 0; i < kDegree; ++i)
          v += uint64_t(x.e[i].n) * frob_powers_[k][i].e[j].n;
        y.e[j] = f_.reduce(v);
      }
    }
    return y;
  }
  void invert(Elt &x) const {
    // Prefix norm by a fixed public addition chain; one base inversion.
    Elt t = norm_prefix(x, kDegree - 1);
    t = frobenius(t);
    Elt n = mulf(t, x);
    check(in_subfield(n), "norm must lie in base field");
    Scalar inv = scalar_power(n.e[0], Base::m_ - 2);
    mul(t, inv);
    x = t;
  }

  // functional interface
  Elt addf(Elt a, const Elt &y) const {
    add(a, y);
    return a;
  }
  Elt subf(Elt a, const Elt &y) const {
    sub(a, y);
    return a;
  }
  Elt mulf(Elt a, const Elt &y) const {
    mul(a, y);
    return a;
  }
  Elt mulf(Elt a, const Scalar &y) const {
    mul(a, y);
    return a;
  }
  Elt negf(Elt a) const {
    neg(a);
    return a;
  }
  Elt invertf(Elt a) const {
    invert(a);
    return a;
  }

  struct Accum {
    Elt acc{};
    std::array<uint64_t, kDelayed ? kConvolutionSize : 0> convolution{};
    size_t used = 0;
  };
  Elt reduce(const Accum &a) const {
    if constexpr (kDelayed)
      return addf(a.acc, reduce_convolution(a.convolution));
    else
      return a.acc;
  }
  // Flush cadence depends only on the public number of accumulated terms.
  // The static bound below covers 1024 products, including modulus folding.
  void mac(Accum &a, const Elt &x, const Elt &y) const {
    if constexpr (kDelayed) {
      const auto c = convolve(x, y);
      for (size_t i = 0; i < c.size(); ++i)
        a.convolution[i] += c[i];
      if (++a.used == 1024) {
        add(a.acc, reduce_convolution(a.convolution));
        a.convolution.fill(0);
        a.used = 0;
      }
    } else
      add(a.acc, mulf(x, y));
  }

  bool fits(uint64_t a) const { return f_.fits(a); }

  Elt of_scalar(uint64_t a) const { return of_scalar_field(a); }
  Elt of_scalar(const Scalar &e) const { return of_scalar_field(e); }

  Elt of_scalar_field(const Scalar &e) const { return Elt{e}; }
  // longfellow-baselines: an element of upstream's Fp24 (the ML-DSA host
  // code's field, ml_dsa::Fq()), which stores the canonical residue as this
  // base field does.
  Elt of_scalar(const ::proofs::Fp24::Elt &e) const {
    return Elt{Scalar{e.n}};
  }
  Elt of_scalar_field(uint64_t a) const { return Elt{f_.of_scalar(a)}; }
  Elt of_scalar_field(const std::array<uint64_t, kDegree> &a) const {
    Elt e;
    for (size_t i = 0; i < kDegree; ++i) {
      e.e[i] = f_.of_scalar_field(a[i]);
    }
    return e;
  }

  template <size_t N> Elt of_string(const char (&s)[N]) const {
    return of_scalar(f_.of_string(s));
  }

  std::optional<Elt> of_bytes_field(const uint8_t ab[/* kBytes */]) const {
    Elt e{};
    uint64_t buffer = 0;
    size_t available = 0, pos = 0;
    uint32_t invalid = 0;
    for (size_t i = 0; i < kDegree; ++i) {
      // Loop counts and addresses depend only on the public field degree.
      while (available < kCoefficientBits) {
        buffer |= uint64_t(ab[pos++]) << available;
        available += 8;
      }
      const uint32_t v = buffer & ((uint64_t{1} << kCoefficientBits) - 1);
      invalid |= uint32_t(v >= Base::m_);
      e.e[i] = Scalar{v};
      buffer >>= kCoefficientBits;
      available -= kCoefficientBits;
    }
    // Reject noncanonical coefficients and nonzero unused high bits.
    invalid |= uint32_t(buffer);
    if (invalid)
      return std::nullopt;
    return e;
  }

  Elt sample(
      const std::function<void(size_t n, uint8_t buf[])> &fill_bytes) const {
    Elt e;
    for (size_t i = 0; i < kDegree; ++i) {
      e.e[i] = f_.sample(fill_bytes);
    }
    return e;
  }

  Elt sample_subfield(
      const std::function<void(size_t n, uint8_t buf[])> &fill_bytes) const {
    auto re = f_.sample(fill_bytes);
    return of_scalar_field(re);
  }

  void to_bytes_field(uint8_t ab[/* kBytes */], const Elt &x) const {
    uint64_t buffer = 0;
    size_t available = 0, pos = 0;
    for (size_t i = 0; i < kDegree; ++i) {
      buffer |= uint64_t(x.e[i].n) << available;
      available += kCoefficientBits;
      while (available >= 8) {
        ab[pos++] = uint8_t(buffer);
        buffer >>= 8;
        available -= 8;
      }
    }
    if (available)
      ab[pos] = uint8_t(buffer);
  }

  bool in_subfield(const Elt &e) const {
    uint32_t v = 0;
    for (size_t i = 1; i < kDegree; ++i)
      v |= e.e[i].n;
    return v == 0;
  }

  std::optional<Elt>
  of_bytes_subfield(const uint8_t ab[/* kSubFieldBytes */]) const {
    if (auto re = f_.of_bytes_subfield(ab)) {
      return of_scalar(re.value());
    }
    return std::nullopt;
  }

  void to_bytes_subfield(uint8_t ab[/* kSubFieldBytes */], const Elt &x) const {
    check(in_subfield(x), "x not in subfield");
    f_.to_bytes_subfield(ab, x.e[0]);
  }

  const Elt &zero() const { return k_[0]; }
  const Elt &one() const { return k_[1]; }
  const Elt &two() const { return k_[2]; }
  const Elt &half() const { return khalf_; }
  const Elt &mone() const { return kmone_; }

  Elt beta(size_t i) const { return of_scalar(f_.beta(i)); }

  Elt poly_evaluation_point(size_t i) const {
    return of_scalar(f_.poly_evaluation_point(i));
  }
  Elt newton_denominator(size_t k, size_t i) const {
    return of_scalar(f_.newton_denominator(k, i));
  }

  // Optimized implementation of from_montgomery_reference(), exploiting
  // the fact that the multiplicand is Elt{N(1)}.
  typename BaseField::N from_montgomery(const Elt &x) const {
    for (size_t i = 1; i < kDegree; ++i) {
      check(x.e[i] == f_.zero(), "x not in subfield");
    }
    return f_.from_montgomery(x.e[0]);
  }

private:
  // Every recursive operand is a sum of at most kDegree canonical
  // coefficients. Even a loose cubic bound covers every unsigned product
  // and partial sum; cross - lo - hi is coefficientwise nonnegative.
  static_assert(__uint128_t(kDegree) * kDegree * kDegree * (Base::m_ - 1) *
                        (Base::m_ - 1) <
                    (__uint128_t(1) << 64),
                "Karatsuba intermediate bound");
  template <size_t N>
  static std::array<uint64_t, 2 * N - 1>
  karatsuba(const std::array<uint64_t, N> &a,
            const std::array<uint64_t, N> &b) {
    std::array<uint64_t, 2 * N - 1> c{};
    if constexpr (N <= 3) {
      for (size_t i = 0; i < N; ++i)
        for (size_t j = 0; j < N; ++j)
          c[i + j] += a[i] * b[j];
    } else {
      constexpr size_t M = (N + 1) / 2;
      std::array<uint64_t, M> al{}, ah{}, bl{}, bh{}, as{}, bs{};
      for (size_t i = 0; i < M; ++i) {
        al[i] = a[i];
        bl[i] = b[i];
        if (i + M < N) {
          ah[i] = a[i + M];
          bh[i] = b[i + M];
        }
        as[i] = al[i] + ah[i];
        bs[i] = bl[i] + bh[i];
      }
      auto lo = karatsuba(al, bl), hi = karatsuba(ah, bh);
      auto cross = karatsuba(as, bs);
      for (size_t i = 0; i < 2 * M - 1; ++i) {
        c[i] += lo[i];
        if (i + M < c.size())
          c[i + M] += cross[i] - lo[i] - hi[i];
        if (i + 2 * M < c.size())
          c[i + 2 * M] += hi[i];
      }
    }
    return c;
  }

  // One outer Karatsuba split (3+2), with degree-four inner convolutions.
  // Values remain unreduced so mac() can accumulate the same fast kernel.
  Convolution tower_convolve(const Elt &a, const Elt &b) const {
    using Inner = std::array<uint64_t, 4>;
    std::array<Inner, 3> al{}, bl{}, as{}, bs{};
    std::array<Inner, 2> ah{}, bh{};
    for (size_t j = 0; j < 3; ++j)
      for (size_t i = 0; i < 4; ++i) {
        al[j][i] = a.e[4 * j + i].n;
        bl[j][i] = b.e[4 * j + i].n;
        as[j][i] = al[j][i]; bs[j][i] = bl[j][i];
        if (j < 2) {
          ah[j][i] = a.e[4 * (j + 3) + i].n;
          bh[j][i] = b.e[4 * (j + 3) + i].n;
          as[j][i] += ah[j][i]; bs[j][i] += bh[j][i];
        }
      }
    auto lo = tower_outer(al, bl), cross = tower_outer(as, bs);
    auto hi = tower_outer(ah, bh);
    Convolution out{};
    for (size_t j = 0; j < 5; ++j)
      for (size_t i = 0; i < 7; ++i) {
        const uint64_t h = j < 3 ? hi[j][i] : 0;
        out[7 * j + i] += lo[j][i];
        out[7 * (j + 3) + i] += cross[j][i] - lo[j][i] - h;
        if (j < 3) out[7 * (j + 6) + i] += h;
      }
    return out;
  }
  // Outer Karatsuba operands are at most 2*(q-1). Four products still
  // fit a 32-bit Kronecker slot, so a quartic convolution needs only four
  // 64x64->128 multiplies. No carry crosses a coefficient slot.
  static std::array<uint64_t, 7>
  tower_inner(const std::array<uint64_t, 4>& a,
              const std::array<uint64_t, 4>& b) {
    static_assert(!kTower || 16 * uint64_t(Base::m_ - 1) * (Base::m_ - 1) <
                  (uint64_t{1} << 32), "tower inner coefficient slot bound");
    uint64_t al[2]{a[0] | (a[1] << 32), a[2] | (a[3] << 32)};
    uint64_t bl[2]{b[0] | (b[1] << 32), b[2] | (b[3] << 32)};
    uint64_t r[4]{};
    for (size_t i = 0; i < 2; ++i) {
      uint64_t carry = 0;
      for (size_t j = 0; j < 2; ++j) {
        __uint128_t v = __uint128_t(al[i]) * bl[j] + r[i+j] + carry;
        r[i+j] = uint64_t(v); carry = uint64_t(v >> 64);
      }
      r[i+2] += carry;
    }
    std::array<uint64_t, 7> c{};
    for (size_t i = 0; i < 7; ++i) c[i] = (r[i/2] >> (32*(i%2))) & 0xffffffff;
    return c;
  }
  template <size_t N>
  static std::array<std::array<uint64_t, 7>, 2 * N - 1>
  tower_outer(const std::array<std::array<uint64_t, 4>, N> &a,
              const std::array<std::array<uint64_t, 4>, N> &b) {
    std::array<std::array<uint64_t, 7>, 2 * N - 1> out{};
    for (size_t i = 0; i < N; ++i)
      for (size_t j = 0; j < N; ++j) {
        auto c = tower_inner(a[i], b[j]);
        for (size_t k = 0; k < 7; ++k) out[i + j][k] += c[k];
      }
    return out;
  }

  const BaseField &f_;
  Elt k_[3]; // small constants
  Elt khalf_;
  Elt kmone_;

  std::array<Elt, kDegree> frob_{};
  std::array<std::array<Elt, kDegree>, kDegree> frob_powers_{};
  static_assert(__uint128_t(1024) * kDegree * (Base::m_ - 1) * (Base::m_ - 1) *
                        (1 + kBetaN + kLinear) <
                    (__uint128_t(1) << 64),
                "batched convolution/fold bound");
  // A tower coefficient is a sum of at most 20 base products. Folding u
  // costs at most (1+11), and folding v at most (1+2+11). This deliberately
  // loose bound covers all 1024-term accumulations before any reduction.
  static_assert(!kTower || __uint128_t(1024) * 20 * (Base::m_ - 1) *
                  (Base::m_ - 1) * 12 * 14 < (__uint128_t(1) << 64),
                "tower accumulator and fold bound");
  Elt reduce_convolution(Convolution c) const {
    if constexpr (kTower) {
      std::array<std::array<uint64_t, 4>, 9> d{};
      for (size_t j = 0; j < 9; ++j) {
        for (size_t i = 0; i < 4; ++i) d[j][i] = c[7 * j + i];
        for (size_t i = 4; i < 7; ++i) d[j][i - 4] += 11 * c[7 * j + i];
      }
      for (size_t j = 5; j < 9; ++j)
        for (size_t i = 0; i < 4; ++i) {
          d[j - 5][i] += 2 * d[j][i];
          d[j - 5][(i + 1) % 4] += (i == 3 ? 11 : 1) * d[j][i];
        }
      Elt r{};
      for (size_t j = 0; j < 5; ++j)
        for (size_t i = 0; i < 4; ++i) r.e[4 * j + i] = f_.reduce(d[j][i]);
      return r;
    }
    for (size_t i = 2 * kDegree - 1; i-- > kDegree;) {
      c[i - kDegree] += c[i] * beta_;
      if constexpr (kLinear != 0)
        c[i - kDegree + 1] += c[i] * kLinear;
    }
    Elt r{};
    for (size_t i = 0; i < kDegree; ++i)
      r.e[i] = f_.reduce(c[i]);
    return r;
  }
  Scalar scalar_power(Scalar x, uint64_t n) const {
    Scalar y = f_.one();
    for (; n; n >>= 1) {
      if (n & 1)
        f_.mul(y, x);
      f_.mul(x, x);
    }
    return y;
  }
  Elt power(Elt x, uint64_t n) const {
    Elt y = one();
    for (; n; n >>= 1) {
      if (n & 1)
        mul(y, x);
      mul(x, x);
    }
    return y;
  }
  Elt norm_prefix(const Elt &x, size_t n) const {
    if (n == 1)
      return x;
    Elt a = norm_prefix(x, n / 2);
    Elt t = mulf(a, frobenius(a, n / 2));
    return (n & 1) ? mulf(x, frobenius(t)) : t;
  }
};
using MlDsaField11 = NativeWide<Fp24q, 11, 2, 0, true,
                                 NativeConvolution::kKaratsuba>;
}  // namespace ml_dsa_split
} // namespace proofs
#endif
