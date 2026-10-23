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
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from lib/algebra/fp24_6.h: degree-8 extension of Fp14 for Falcon's q = 12289, beta = 11, Kronecker-substitution multiply

#ifndef PRIVACY_PROOFS_ZK_LIB_ALGEBRA_FP14_8_H_
#define PRIVACY_PROOFS_ZK_LIB_ALGEBRA_FP14_8_H_

#include <stddef.h>

#include <array>
#include <cstdint>
#include <functional>
#include <iterator>
#include <optional>
#include <utility>

#include "algebra/fp14.h"
#include "util/panic.h"

namespace proofs {
// Octic extension of Fp14(m), represented as P(x) mod (x^8 - beta), where
// (x^8 - beta) is assumed to be irreducible.  This is the native soundness
// field for the Falcon (FN-DSA) circuit: with m = 12289, |GF(12289^8)| ~ 2^112.
//
// beta = 11.  Over F_12289 the binomial criterion for x^8 - beta collapses to
// "beta is a quadratic non-residue": q-1 = 2^12*3, so gcd(8, (q-1)/ord(beta))
// = 1 forces 4096 | ord(beta), which is exactly non-residuosity, and 12289 = 1
// mod 4 covers the 4 | n clause.  Half the field qualifies (6144 values); 11 is
// the smallest, and is also a primitive root.  No power of two is available --
// 12289 = 1 mod 8 makes 2 a residue -- so the fold cannot be reduced to a
// shift; 11 has Hamming weight 2 after the low bit (0b1011).
//
// The whole element is 8 * 14 = 112 bits (16 bytes, fits in __int128).  A raw
// base-field coefficient (< 12289) commits in kSubFieldBytes = 2 bytes -- an 8x
// discount over the 16-byte extension, and the dominant committed shape in
// Falcon (signature/NTT coefficients), so the subfield path is the one used.
//
// mul() breaks the base-field abstraction: it computes the degree-8 integer
// convolution via Kronecker substitution (one 256x256->512-bit multiply; the
// benchmarked winner, ~1.4-1.6x over schoolbook -- Karatsuba loses because the
// 14-bit base muls are too cheap to beat the extra recombination), folds
// x^8=beta, then reduces mod m once per output coefficient.  See the mul() body
// for the overflow/slot-width argument.
class Fp14_8 {
 public:
  using BaseField = Fp14;
  using Scalar = BaseField::Elt;
  using TypeTag = BaseField::TypeTag;
  using CElt = BaseField::CElt;

  static constexpr size_t kDegree = 8;

  // size of the serialization into bytes
  static constexpr size_t kBytes = kDegree * BaseField::kBytes;
  static constexpr size_t kBits = kDegree * BaseField::kBits;
  static constexpr size_t kSubFieldBytes = BaseField::kBytes;
  static constexpr size_t kSubFieldBits = BaseField::kBits;
  static constexpr bool kCharacteristicTwo = false;
  static constexpr size_t kNPolyEvaluationPoints =
      BaseField::kNPolyEvaluationPoints;

  struct Elt {
    std::array<Scalar, kDegree> e;
    bool operator==(const Elt& y) const { return e == y.e; }
    bool operator!=(const Elt& y) const { return !operator==(y); }
  };

  // beta is compile-time so the fold `m[i] += m[i + 8] * beta_` strength-
  // reduces.  x^8 - 11 is irreducible over F_12289: 11 is a primitive root, so
  // it is a quadratic non-residue, which is exactly the criterion here (q-1 =
  // 2^12*3, so irreducibility reduces to beta being a non-residue).  11 is the
  // smallest such beta; no power of two qualifies, since 12289 = 1 mod 8 makes
  // 2 a residue.
  static constexpr uint32_t beta_ = 11;

  explicit Fp14_8(const BaseField& F, const uint32_t beta) : f_(F) {
    check(beta == beta_, "Fp14_8 is specialised to beta = 11");
    // beta must be a valid base-field element (< m < 2^14); this also bounds
    // the fold term m[i+8]*beta so the u64 convolution accumulator cannot
    // overflow.
    check(f_.fits(beta), "beta not in base field");

    for (uint64_t i = 0; i < std::size(k_); ++i) {
      k_[i] = of_scalar(i);
    }
    khalf_ = of_scalar(f_.half());
    kmone_ = of_scalar(f_.mone());
  }

  // Fp14_8 is not copyable or assignable because it holds a reference to a
  // Field and precomputes constants based on that field.
  Fp14_8(const Fp14_8&) = delete;
  Fp14_8& operator=(const Fp14_8&) = delete;

  const BaseField& base_field() const { return f_; }

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

  void add(Elt& a, const Elt& y) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.add(a.e[i], y.e[i]);
    }
  }
  void sub(Elt& a, const Elt& y) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.sub(a.e[i], y.e[i]);
    }
  }
  void mul(Elt& a, const Elt& y) const {
    // Kronecker substitution (benchmarked winner, ~1.4-1.6x vs schoolbook;
    // Karatsuba loses here -- 14-bit base muls are too cheap to beat the extra
    // recombination).  Pack the 8 coeffs into a 256-bit integer with 32-bit
    // slots (2 coeffs per 64-bit limb), do ONE exact 256x256 -> 512-bit multiply,
    // then unpack the 15 convolution coeffs.  Each conv coeff is a sum of <= 8
    // products of 14-bit residues <= 8*(m-1)^2 ~ 1.21e9 < 2^31 < 2^32 = slot, so
    // no coeff overflows its slot or collides.  NOTE: the 32-bit slot is safe
    // only for a ~14-bit modulus (the Falcon field); a modulus near 2^16 would
    // reach ~2^35 and need wider slots.  Then fold x^8 = beta and reduce.
    static_assert(kDegree == 8, "Kronecker packing assumes degree 8");
    uint64_t al[4], bl[4];
    for (size_t j = 0; j < 4; ++j) {
      al[j] = (uint64_t)a.e[2 * j].n | ((uint64_t)a.e[2 * j + 1].n << 32);
      bl[j] = (uint64_t)y.e[2 * j].n | ((uint64_t)y.e[2 * j + 1].n << 32);
    }
    uint64_t r[8] = {0};
    for (size_t i = 0; i < 4; ++i) {
      uint64_t carry = 0;
      for (size_t j = 0; j < 4; ++j) {
        __uint128_t t = (__uint128_t)al[i] * bl[j] + r[i + j] + carry;
        r[i + j] = (uint64_t)t;
        carry = (uint64_t)(t >> 64);
      }
      r[i + 4] += carry;
    }
    uint64_t m[2 * kDegree - 1];
    for (size_t k = 0; k < 2 * kDegree - 1; ++k) {
      m[k] = (r[k / 2] >> (32 * (k & 1))) & 0xFFFFFFFFull;
    }
    // fold x^8 = beta : m[i] += beta * m[i + 8]
    for (size_t i = 0; i < kDegree - 1; ++i) {
      m[i] += m[i + kDegree] * (uint64_t)beta_;
    }
    for (size_t i = 0; i < kDegree; ++i) {
      a.e[i] = f_.reduce(m[i]);
    }
  }
  // Plain schoolbook, for comparison against the Kronecker path above.
  //
  // 64 independent 14x14 -> 28-bit products accumulated into 15 u64 slots: no
  // packing, no carry chain, so the multiplies pipeline freely.  Each slot is a
  // sum of <= 8 products of 14-bit residues, <= 8*(m-1)^2 ~ 1.21e9 < 2^31, and
  // the fold adds beta*slot <= 11 * 2^31 < 2^35, so u64 is ample.
  //
  // The comparison with the Kronecker path is unmeasured with the compile-time
  // modulus.  The two differ in serial dependency: schoolbook has none, and
  // Kronecker's limb product has one.
  void mul_schoolbook(Elt& a, const Elt& y) const {
    uint64_t m[2 * kDegree - 1] = {0};
    for (size_t i = 0; i < kDegree; ++i) {
      for (size_t j = 0; j < kDegree; ++j) {
        m[i + j] += (uint64_t)a.e[i].n * (uint64_t)y.e[j].n;
      }
    }
    for (size_t i = 0; i < kDegree - 1; ++i) {
      m[i] += m[i + kDegree] * (uint64_t)beta_;
    }
    for (size_t i = 0; i < kDegree; ++i) {
      a.e[i] = f_.reduce(m[i]);
    }
  }
  Elt mulf_schoolbook(Elt a, const Elt& y) const {
    mul_schoolbook(a, y);
    return a;
  }

  void mul(Elt& a, const Scalar& y) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.mul(a.e[i], y);
    }
  }
  void neg(Elt& x) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.neg(x.e[i]);
    }
  }
  void invert(Elt& x) const {
    if (in_subfield(x)) {
      f_.invert(x.e[0]);
    } else {
      gaussian_elimination_invert(x);
    }
  }

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
  Elt mulf(Elt a, const Scalar& y) const {
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
    Elt acc;
  };

  Elt reduce(const Accum& a) const { return a.acc; }

  void mac(Accum& a, const Elt& x, const Elt& y) const {
    add(a.acc, mulf(x, y));
  }

  bool fits(uint64_t a) const { return f_.fits(a); }

  Elt of_scalar(uint64_t a) const { return of_scalar_field(a); }
  Elt of_scalar(const Scalar& e) const { return of_scalar_field(e); }

  Elt of_scalar_field(const Scalar& e) const { return Elt{e}; }
  Elt of_scalar_field(uint64_t a) const { return Elt{f_.of_scalar(a)}; }
  Elt of_scalar_field(const std::array<uint64_t, kDegree>& a) const {
    Elt e;
    for (size_t i = 0; i < kDegree; ++i) {
      e.e[i] = f_.of_scalar_field(a[i]);
    }
    return e;
  }

  template <size_t N>
  Elt of_string(const char (&s)[N]) const {
    return of_scalar(f_.of_string(s));
  }

  std::optional<Elt> of_bytes_field(const uint8_t ab[/* kBytes */]) const {
    Elt e;
    for (size_t i = 0; i < kDegree; ++i) {
      auto scalar_opt = f_.of_bytes_field(ab + i * BaseField::kBytes);
      if (!scalar_opt.has_value()) {
        return std::nullopt;
      }
      e.e[i] = scalar_opt.value();
    }
    return e;
  }

  Elt sample(
      const std::function<void(size_t n, uint8_t buf[])>& fill_bytes) const {
    Elt e;
    for (size_t i = 0; i < kDegree; ++i) {
      e.e[i] = f_.sample(fill_bytes);
    }
    return e;
  }

  Elt sample_subfield(
      const std::function<void(size_t n, uint8_t buf[])>& fill_bytes) const {
    auto re = f_.sample(fill_bytes);
    return of_scalar_field(re);
  }

  void to_bytes_field(uint8_t ab[/* kBytes */], const Elt& x) const {
    for (size_t i = 0; i < kDegree; ++i) {
      f_.to_bytes_field(ab + i * BaseField::kBytes, x.e[i]);
    }
  }

  bool in_subfield(const Elt& e) const {
    for (size_t i = 1; i < kDegree; ++i) {
      if (e.e[i] != f_.zero()) return false;
    }
    return true;
  }

  std::optional<Elt> of_bytes_subfield(
      const uint8_t ab[/* kSubFieldBytes */]) const {
    if (auto re = f_.of_bytes_subfield(ab)) {
      return of_scalar(re.value());
    }
    return std::nullopt;
  }

  void to_bytes_subfield(uint8_t ab[/* kSubFieldBytes */], const Elt& x) const {
    check(in_subfield(x), "x not in subfield");
    f_.to_bytes_subfield(ab, x.e[0]);
  }

  const Elt& zero() const { return k_[0]; }
  const Elt& one() const { return k_[1]; }
  const Elt& two() const { return k_[2]; }
  const Elt& half() const { return khalf_; }
  const Elt& mone() const { return kmone_; }

  Elt beta(size_t i) const { return of_scalar(f_.beta(i)); }

  Elt poly_evaluation_point(size_t i) const {
    return of_scalar(f_.poly_evaluation_point(i));
  }
  Elt newton_denominator(size_t k, size_t i) const {
    return of_scalar(f_.newton_denominator(k, i));
  }

  // Optimized implementation of from_montgomery_reference(), exploiting
  // the fact that the multiplicand is Elt{N(1)}.
  BaseField::N from_montgomery(const Elt& x) const {
    for (size_t i = 1; i < kDegree; ++i) {
      check(x.e[i] == f_.zero(), "x not in subfield");
    }
    return f_.from_montgomery(x.e[0]);
  }

 private:
  const BaseField& f_;
  Elt k_[3];  // small constants
  Elt khalf_;
  Elt kmone_;

  // Invert via gaussian elimination with partial pivoting.
  //
  // Viewing the element X to be inverted as a polynomial A(x), we want to find
  // B(x) such that A(x) * B(x) = 1 mod (x^8 - beta).  View this as a system of
  // linear equations in the coefficients of B.
  void gaussian_elimination_invert(Elt& x) const {
    constexpr size_t n = kDegree;
    std::array<std::array<Scalar, n>, n> A;

    // Set up the beta-circulant matrix representing the Elt to be inverted.
    for (size_t i = 0; i < n; ++i) {
      for (size_t j = 0; j < n; ++j) {
        A[i][j] = (i >= j) ? x.e[i - j] : f_.mulf(x.e[i - j + n], beta_);
      }
    }

    // initialize the right-hand side B, stored in-place as X
    x = one();

    // gaussian elimination
    for (size_t i = 0; i < n; ++i) {
      for (size_t r = i; r < n; ++r) {
        if (A[r][i] != f_.zero()) {
          if (i != r) {
            std::swap(A[i], A[r]);
            std::swap(x.e[i], x.e[r]);
          }
          goto have_pivot;
        }
      }
      check(false, "element is not invertible");

    have_pivot:
      Scalar scal = f_.invertf(A[i][i]);
      for (size_t j = i; j < n; ++j) {
        f_.mul(A[i][j], scal);
      }
      f_.mul(x.e[i], scal);

      // eliminate all other rows k
      for (size_t k = 0; k < n; ++k) {
        if (k != i) {
          Scalar a = A[k][i];
          for (size_t j = i; j < n; ++j) {
            f_.sub(A[k][j], f_.mulf(a, A[i][j]));
          }
          f_.sub(x.e[k], f_.mulf(a, x.e[i]));
        }
      }
    }
  }
};
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_ALGEBRA_FP14_8_H_
