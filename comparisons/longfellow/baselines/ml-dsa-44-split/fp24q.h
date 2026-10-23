// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from lib/algebra/fp24.h: the prime field specialized to q = 8380417 with 3-byte serialization and compile-time modulus

// longfellow-baselines, fork-derived: the fork's lib/algebra/fp24.h
// (mac-bench 8d8e0aa4), renamed Fp24q and moved into
// proofs::ml_dsa_split so that it coexists with upstream's Fp24.  It is the
// base field of the wide profile's GF(q^11) (mldsa_field11.h), which needs
// the modulus as a compile-time constant.  Against upstream's Fp24 it
// differs in that (q = 8380417 fixed at compile time) and in serializing
// elements in 3 bytes instead of 4.

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_FP24Q_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_FP24Q_H_

// 24-bit fields
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <utility>

#include "algebra/fp_generic.h"
#include "algebra/nat.h"
#include "algebra/static_string.h"
#include "algebra/sysdep.h"
#include "util/panic.h"
#include "util/serialization.h"

namespace proofs {
namespace ml_dsa_split {
class Fp24q {
 public:
  using N = Nat<1>;
  using TypeTag = PrimeFieldTypeTag;

  static constexpr size_t kU64 = 1;
  // q = 8380417 < 2^24, so field elements serialize in 3 bytes.
  static constexpr size_t kBytes = 3;
  static constexpr size_t kSubFieldBytes = 3;
  static constexpr size_t kBits = 32;
  static constexpr size_t kSubFieldBits = kBits;

  static constexpr bool kCharacteristicTwo = false;
  static constexpr size_t kNPolyEvaluationPoints = 6;
  static constexpr bool kSupportsDot = false;

  // Largest Reed-Solomon evaluation domain this field admits.
  //
  // The RS encoder in algebra/reed_solomon.h evaluates at the points
  // of_scalar(0), of_scalar(1), ..., of_scalar(m-1) and inverts their
  // pairwise differences, so those images must be distinct and nonzero
  // apart.  That is a property of the field, NOT of its serialization
  // width: see the note in ligero/ligero_param.h.
  // of_scalar() reduces mod m_.
  size_t max_rs_domain() const { return m_; }

  // The modulus is a COMPILE-TIME constant, not a member.  reduce() below is
  // `x % m_`; against a runtime modulus that is a hardware 64-bit divide
  // (~20-40 cycles, poorly pipelined), against a constant it is the usual
  // multiply/shift/multiply-subtract.  Fp24_6::mul calls it six times per
  // extension multiply, so it dominates that path -- and it is why a Montgomery
  // field like Fp128 looked so much faster than this one.
  static constexpr uint32_t m_ = 8380417;
  static constexpr size_t exact_bits_ = 23;
  struct Elt {
    uint32_t n;
    bool operator==(const Elt& y) const { return n == y.n; }
    bool operator!=(const Elt& y) const { return !operator==(y); }
  };

  // The modulus argument is kept so call sites stay explicit, but it is checked
  // rather than stored: there is only one Fp24q.
  explicit Fp24q(uint32_t modulus) {
    check(modulus == m_, "Fp24q is specialised to q = 8380417 (ML-DSA)");

    for (uint32_t i = 0; i < sizeof(k_) / sizeof(k_[0]); ++i) {
      k_[i] = Elt{i};
    }

    mone_ = negf(k_[1]);
    half_ = Elt{1u + (m_ / 2)};

    for (size_t i = 0; i < kNPolyEvaluationPoints; ++i) {
      poly_evaluation_points_[i] = of_scalar(i);
      if (i == 0) {
        inv_small_scalars_[i] = zero();
      } else {
        inv_small_scalars_[i] = invertf(poly_evaluation_points_[i]);
      }
    }
  }

  Fp24q(const Fp24q&) = delete;
  Fp24q& operator=(const Fp24q&) = delete;

  template <size_t N>
  Elt of_string(const char (&s)[N]) const {
    return of_charp(&s[0]);
  }

  Elt of_string(const StaticString& s) const { return of_charp(s.as_pointer); }

  // The of_scalar methods should only be used on trusted inputs known
  // at compile time to be valid field elements. As a result, they return
  // Elt directly instead of std::optional, and panic if the condition is not
  // satisfied. All untrusted input should be handled via the of_bytes method.
  Elt of_scalar(uint64_t a) const { return of_scalar_field(a); }

  Elt of_scalar_field(const std::array<uint64_t, 1>& a) const {
    return of_scalar_field(a[0]);
  }
  Elt of_scalar_field(uint64_t a) const {
    check(static_cast<uint32_t>(a) == a, "scalar too large for uint32_t");
    return of_scalar_field(static_cast<uint32_t>(a));
  }
  Elt of_scalar_field(uint32_t a) const {
    check(a < m_, "of_scalar must be less than m");
    return to_montgomery(a);
  }

  bool fits(uint64_t a) const { return a < m_; }

  // basis for the binary representation of of_scalar(), so that
  // of_scalar(sum_i b[i] 2^i) = sum_i b[i] beta(i)
  Elt beta(size_t i) const {
    check(i < 64, "i < 64");
    return of_scalar(static_cast<uint64_t>(1) << i);
  }

  // a += y
  void add(uint32_t& a, uint32_t y) const { a = addcmovc_32(a - m_, y, a + y); }
  void add(Elt& a, Elt y) const { add(a.n, y.n); }

  // a -= y
  //
  void sub(uint32_t& a, uint32_t y) const { a = sub_sysdep_32(a, y, m_); }
  void sub(Elt& a, Elt y) const { sub(a.n, y.n); }

  // x = -x
  void neg(Elt& x) const {
    Elt y{0};
    sub(y, x);
    x = y;
  }

  void mul(uint32_t& x, const Elt& y) const {
    x = (static_cast<uint64_t>(x) * static_cast<uint64_t>(y.n)) % m_;
  }
  void mul(Elt& a, Elt y) const { mul(a.n, y); }

  // x = 1/x
  void invert(Elt& x) const { x = invertf(x); }

  // functional interface
  Elt addf(Elt a, const Elt& y) const {
    add(a, y);
    return a;
  }
  Elt subf(Elt a, const Elt& y) const {
    sub(a, y);
    return a;
  }
  Elt mulf(Elt a, const Elt& y) const {
    mul(a, y);
    return a;
  }
  Elt mulf(Elt a, const uint32_t y) const {
    mul(a, Elt{y});
    return a;
  }
  Elt negf(Elt a) const {
    neg(a);
    return a;
  }

  // This is the binary extended gcd algorithm, modified
  // to return the inverse of x.
  Elt invertf(Elt x) const {
    uint32_t a = x.n;
    uint32_t b = m_;
    Elt u = one();
    Elt v = zero();
    while (a != 0) {
      if ((a & 0x1u) == 0) {
        a >>= 1;
        byhalf(u);
      } else {
        if (a < b) {  // swap to maintain invariant
          std::swap(a, b);
          std::swap(u, v);
        }
        a = (a - b) >> 1;
        sub(u, v);
        byhalf(u);
      }
    }
    return v;
  }

  struct Accum {
    Elt acc;
  };

  Elt reduce(const Accum& a) const { return a.acc; }

  void mac(Accum& a, const Elt& x, const Elt& y) const {
    add(a.acc, mulf(x, y));
  }

  Elt zero() const { return Elt{0}; }
  const Elt& one() const { return k_[1]; }
  const Elt& two() const { return k_[2]; }
  const Elt& half() const { return half_; }
  const Elt& mone() const { return mone_; }

  Elt poly_evaluation_point(size_t i) const {
    check(i < kNPolyEvaluationPoints, "i < kNPolyEvaluationPoints");
    return poly_evaluation_points_[i];
  }

  // return (X[k] - X[k - i])^{-1}, were X[i] is the
  // i-th poly evalaluation point.
  Elt newton_denominator(size_t k, size_t i) const {
    check(k < kNPolyEvaluationPoints, "k < kNPolyEvaluationPoints");
    check(i <= k, "i <= k");
    check(k != (k - i), "k != (k - i)");
    return inv_small_scalars_[/* k - (k - i) = */ i];
  }

  // Type for counters.  For prime fields counters and field
  // elements have the same representation, so all conversions
  // are trivial.
  struct CElt {
    Elt e;
  };
  CElt as_counter(uint64_t a) const { return CElt{of_scalar_field(a)}; }
  CElt negf(const CElt& a) const { return CElt{negf(a.e)}; }

  // Convert a counter into *some* field element such that the counter is
  // zero (as a counter) iff the field element is zero.
  Elt znz_indicator(const CElt& celt) const { return celt.e; }

  // Reference implementation, unused.
  N from_montgomery_reference(Elt x) const { return from_montgomery(x); }

  N from_montgomery(Elt x) const { return N{x.n}; }

  Elt to_montgomery(uint64_t xn) const {
    return Elt{static_cast<uint32_t>(xn)};
  }

  // Added to pass tests which verify the from_, to_ inverse relationship.
  Elt to_montgomery(const N& xn) const {
    std::array<uint64_t, 1> u = xn.u64();
    return to_montgomery(u[0]);
  }

  bool in_subfield(Elt e) const { return true; }

  std::optional<Elt> of_bytes_field(const uint8_t ab[/* kBytes */]) const {
    uint32_t an = (uint32_t)ab[0] | ((uint32_t)ab[1] << 8) | ((uint32_t)ab[2] << 16);
    if (fits(an)) {
      return to_montgomery(an);
    } else {
      return std::nullopt;
    }
  }

  void to_bytes_field(uint8_t ab[/* kBytes */], const Elt& x) const {
    ab[0] = x.n & 0xff;
    ab[1] = (x.n >> 8) & 0xff;
    ab[2] = (x.n >> 16) & 0xff;
  }

  std::optional<Elt> of_bytes_subfield(const uint8_t ab[/* kBytes */]) const {
    return of_bytes_field(ab);
  }

  void to_bytes_subfield(uint8_t ab[/* kBytes */], const Elt& x) const {
    to_bytes_field(ab, x);
  }

  Elt sample(
      const std::function<void(size_t n, uint8_t buf[])>& fill_bytes) const {
    const size_t total_l = (exact_bits_ + 7) / 8;
    const uint32_t mask = (~static_cast<uint32_t>(0)) >> (32 - exact_bits_);
    uint8_t buf[4] = {0};  // exact_bits_ up to 32; read as u32
    for (;;) {
      fill_bytes(total_l, buf);
      uint32_t an = u32_of_le(buf);
      an &= mask;
      if (an < m_) {
        return to_montgomery(an);
      }
    }
  }

  Elt sample_subfield(
      const std::function<void(size_t n, uint8_t buf[])>& fill_bytes) const {
    return sample(fill_bytes);
  }

  // dot product is not supported
  struct NatScaledForDot {};

  NatScaledForDot prescale_for_dot(Elt e) const {
    check(false, "prescale_for_dot() not implemented");
    return NatScaledForDot{};
  }

  template <size_t WX>
  Elt reduce(const Nat<WX>& xn) const {
    // Need one-limb reduction for crt.h, but other
    // cases are not needed.
    if (WX == 1) {
      std::array<uint64_t, WX> u = xn.u64();
      return reduce(u[0]);
    } else {
      check(false, "reduce() not implemented");
      return zero();
    }
  }
  Elt dot(size_t n, const Nat<1> a[/*n*/],
          const NatScaledForDot b[/*n*/]) const {
    check(false, "dot() not implemented");
    return zero();
  }
  Elt reduce(uint64_t x) const { return Elt{static_cast<uint32_t>(x % m_)}; }

 private:
  // This method should only be used on static strings known at
  // compile time to be valid field elements.  We make it
  // private to prevent misuse.
  Elt of_charp(const char* s) const {
    Elt a(k_[0]);
    size_t zbase = 10;
    Elt base = of_scalar(10);
    if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
      s += 2;
      zbase = 16;
      base = of_scalar(16);
    }

    for (; *s; s++) {
      Elt d = of_scalar(digit(*s, zbase));
      mul(a, base);
      add(a, d);
    }
    return a;
  }

  void byhalf(Elt& a) const {
    uint32_t b = a.n & 1;
    a.n >>= 1;
    if (b != 0) {
      add(a, half_);
    }
  }

  Elt k_[3];  // small constants
  Elt half_;  // 1/2
  Elt mone_;  // minus one
  Elt poly_evaluation_points_[kNPolyEvaluationPoints];
  Elt inv_small_scalars_[kNPolyEvaluationPoints];
};
}  // namespace ml_dsa_split
}  // namespace proofs
#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_FP24Q_H_
