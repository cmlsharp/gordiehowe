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
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from gf2k/gf2_128.h to GF(2^256) with x^256 + x^10 + x^5 + x^2 + 1, 256-bit elements and a constant-time subfield map

#ifndef PRIVACY_PROOFS_ZK_LIB_GF2K_GF2_256_H_
#define PRIVACY_PROOFS_ZK_LIB_GF2K_GF2_256_H_

#include <stdio.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <utility>

#include "gf2k/gf2_128.h"
#include "gf2k/gf2poly.h"
#include "gf2k/sysdep256.h"
#include "util/panic.h"

namespace proofs {

template <size_t subfield_log_bits = 4> class GF2_256 {
  // avoid writing static_cast<size_t>(1) all the time.
  static constexpr size_t k1 = 1;

public:
  using TypeTag = BinaryFieldTypeTag;
  static constexpr std::array<uint64_t,4> kProtocolFieldId{2,256,0x425,subfield_log_bits};

  // Fast representation of the field element via the system-dependent
  // SIMD type.
  using N = gf2_256_elt_t;

  // "Slow" representation of the field element as array of
  // C++ integral types.
  using N1 = GF2Poly<4>;

  static constexpr size_t kNPolyEvaluationPoints = 6;
  static constexpr size_t kLogBits = 8;
  static constexpr size_t kBits = k1 << kLogBits;
  static constexpr size_t kBytes = kBits / 8u;

  static constexpr size_t kSubFieldLogBits = subfield_log_bits;
  static constexpr size_t kSubFieldBits = k1 << kSubFieldLogBits;
  static constexpr size_t kSubFieldBytes = kSubFieldBits / 8u;

  // Largest Reed-Solomon evaluation domain this field admits.
  //
  // The RS encoder in algebra/reed_solomon.h evaluates at the points
  // of_scalar(0), of_scalar(1), ..., of_scalar(m-1) and inverts their
  // pairwise differences, so those images must be distinct and nonzero
  // apart.  That is a property of the field, NOT of its serialization
  // width: see the note in ligero/ligero_param.h.
  // Here of_scalar(u) decomposes u against the subfield basis beta_[] and
  // hard-checks u < 2^kSubFieldBits, so the domain IS the subfield.  A domain
  // test based on kSubFieldBytes would hold for this field and does not
  // generalize.
  size_t max_rs_domain() const { return k1 << kSubFieldBits; }

  static_assert(kBits == 8u * kBytes);
  static_assert(kSubFieldBits == 8u * kSubFieldBytes);
  static constexpr bool kCharacteristicTwo = true;

  struct Elt {
    N n;

    Elt() : n{} {}
    explicit Elt(N n_) : n(n_) {}

    // Don't bother using SIMD instructions for comparisons,
    // otherwise we have to complicate the sysdep API surface.
    // Unpack into uint64[4] and compute manually.
    bool operator==(const Elt &y) const {
      auto a = unpack().u64(), b = y.unpack().u64();
      return ((a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3])) ==
             0;
    }
    bool operator!=(const Elt &y) const { return !operator==(y); }

    // Returns the coefficient of x^i in the polynomial.
    uint8_t operator[](size_t i) const {
      auto n1 = uint64x4_of_gf2_256(n);
      return i < 256 ? static_cast<uint8_t>((n1[i / 64] >> (i % 64)) & 1) : 0;
    }

    N1 unpack() const { return N1(uint64x4_of_gf2_256(n)); }
  };

  struct Accum {
    gf2_256_accum_t acc;
  };

  Elt reduce(const Accum &a) const { return Elt{gf2_256_accum_reduce(a.acc)}; }

  explicit GF2_256() {
    kone_ = of_scalar_field(0b1);
    kx_ = of_scalar_field(0b10);

    // x^{-1} = x^255 + x^9 + x^4 + x.
    std::array<uint64_t, 4> invx = {(1ull << 9) | (1ull << 4) | (1ull << 1), 0,
                                    0, 1ull << 63};
    kinvx_ = of_scalar_field(invx);

    Elt g = subfield_generator();
    kg_ = g;
    kinvg_ = invertf(g);

    // basis of the subfield = {1, g, g^2, ...}
    beta_[0] = one();
    for (size_t i = 1; i < kSubFieldBits; ++i) {
      beta_[i] = mulf(beta_[i - 1], g);
    }

    // Reduce the basis to row-echelon form
    beta_ref();

    // Evaluation points.  We use g^i for these as well
    poly_evaluation_points_[0] = zero();
    Elt gi = one();
    for (size_t i = 1; i < kNPolyEvaluationPoints; ++i) {
      poly_evaluation_points_[i] = gi;
      mul(gi, g);
    }

    for (size_t i = 1; i < kNPolyEvaluationPoints; i++) {
      for (size_t k = kNPolyEvaluationPoints; k-- > i;) {
        auto dx =
            subf(poly_evaluation_points_[k], poly_evaluation_points_[k - i]);
        check(dx != zero(), "dx != zero()");
        newton_denominators_[k][i] = invertf(dx);
      }
    }

    // basis of counters
    Elt cgi(g); // = g ^ {2^i}, initially i = 0
    for (size_t i = 0; i < kSubFieldBits; ++i) {
      counter_beta_[i] = cgi;
      mul(cgi, cgi);
    }
  }

  GF2_256(const GF2_256 &) = delete;
  GF2_256 &operator=(const GF2_256 &) = delete;

  // The bits of u are the coordinates with respect to the basis
  // beta_[] of the subfield.
  // Fixed-address selection, including when bit is private.
  static Elt select_bit(Elt x, uint64_t bit) {
    auto a = uint64x4_of_gf2_256(x.n);
    const uint64_t mask = uint64_t{0} - bit;
    for (auto &v : a)
      v &= mask;
    return Elt(gf2_256_of_uint64x4(a));
  }
  Elt of_scalar(uint64_t u) const {
    Elt t = zero();
    for (size_t k = 0; k < kSubFieldBits; ++k, u >>= 1)
      add(t, select_bit(beta_[k], u & 1));
    check(u == 0, "of_scalar(u), too many bits");
    return t;
  }

  Elt of_scalar_field(uint64_t n) const {
    std::array<uint64_t, 4> u = {n, 0};
    return of_scalar_field(u);
  }
  Elt of_scalar_field(const std::array<uint64_t, 4> &u) const {
    return Elt(gf2_256_of_uint64x4(u));
  }

  // The base_only flag is a placeholder that takes meaning when F is an
  // extension field.
  std::optional<Elt> of_bytes_field(const uint8_t ab[/* kBytes */],
                                    bool base_only = true) const {
    N1 an = N1::of_bytes(ab);
    return of_scalar_field(an.u64());
  }

  void to_bytes_field(uint8_t ab[/* kBytes */], const Elt &x) const {
    x.unpack().to_bytes(ab);
  }

  Elt sample(
      const std::function<void(size_t n, uint8_t buf[])> &fill_bytes) const {
    // Every 256-bit sequence is a valid field element.
    uint8_t buf[kBytes];
    fill_bytes(sizeof(buf), buf);
    std::optional<Elt> maybe = of_bytes_field(buf);
    check(maybe.has_value(), "of_bytes_field failed unexpectedly");
    return maybe.value();
  }

  Elt sample_subfield(
      const std::function<void(size_t n, uint8_t buf[])> &fill_bytes) const {
    uint8_t buf[kSubFieldBytes];
    fill_bytes(sizeof(buf), buf);
    std::optional<Elt> maybe = of_bytes_subfield(buf);
    check(maybe.has_value(), "of_bytes_subfield failed unexpectedly");
    return maybe.value();
  }

  bool in_subfield(Elt e) const {
    auto eu = solve(e);
    const auto a = eu.first.u64();
    return (a[0] | a[1] | a[2] | a[3]) == 0;
  }

  std::optional<Elt>
  of_bytes_subfield(const uint8_t ab[/* kSubFieldBytes */]) const {
    uint64_t u = 0;
    for (size_t i = kSubFieldBytes; i-- > 0;) {
      u <<= 8;
      u |= ab[i];
    }
    return of_scalar(u);
  }

  void to_bytes_subfield(uint8_t ab[/* kSubFieldBytes */], const Elt &x) const {
    auto eu = solve(x);
    const auto residual = eu.first.u64();
    check((residual[0] | residual[1] | residual[2] | residual[3]) == 0,
          "element outside subfield");
    uint64_t u = eu.second;
    for (size_t i = 0; i < kSubFieldBytes; ++i) {
      ab[i] = u & 0xFFu;
      u >>= 8;
    }
  }

  // functional interface
  Elt addf(const Elt &x, const Elt &y) const {
    return Elt{gf2_256_add(x.n, y.n)};
  }
  Elt subf(const Elt &x, const Elt &y) const {
    return Elt{gf2_256_add(x.n, y.n)};
  }
  Elt mulf(const Elt &x, const Elt &y) const {
    if (&x == &y)
      return Elt{gf2_256_square(x.n)};
    return Elt{gf2_256_mul(x.n, y.n)};
  }
  Elt negf(const Elt &x) const { return x; }

  // two-operands interface
  void add(Elt &a, const Elt &y) const { a = addf(a, y); }
  void sub(Elt &a, const Elt &y) const { a = subf(a, y); }
  void mul(Elt &a, const Elt &y) const { a = mulf(a, y); }
  void neg(Elt &a) const { /* noop */ }
  void invert(Elt &a) const { a = invertf(a); }
  void mac(Accum &a, const Elt &x, const Elt &y) const {
    gf2_256_mac(a.acc, x.n, y.n);
  }

  Elt zero() const { return Elt{}; }
  Elt one() const { return kone_; }
  Elt mone() const { return kone_; }
  Elt x() const { return kx_; }
  Elt invx() const { return kinvx_; }
  Elt g() const { return kg_; }
  Elt invg() const { return kinvg_; }
  Elt beta(size_t i) const {
    check(i < kSubFieldBits, "i < kSubFieldBits");
    return beta_[i];
  }

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
    return newton_denominators_[k][i];
  }

  Elt invertf(Elt x) const {
    // Fixed addition chain: build x^(2^255-1), then square.
    // As before, inversion maps zero to zero.
    Elt r = x;
    for (unsigned span = 1; span < 255; span = 2 * span + 1) {
      Elt t = r;
      for (unsigned j = 0; j < span; ++j)
        mul(t, t);
      mul(r, t);
      mul(r, r);
      mul(r, x);
    }
    mul(r, r);
    return r;
  }

  // Type for counters.  We represent unsigned integer n as g^n
  // where g is the generator of the subfield.
  struct CElt {
    Elt e;

    bool operator==(const CElt &y) const { return e == y.e; }
    bool operator!=(const CElt &y) const { return !operator==(y); }
  };
  CElt as_counter(uint64_t a) const {
    // 2^{bits} - 2 fits, 2^{bits} - 1 does not
    check((a + 1u) != 0, "as_counter() arg too large");
    check(((a + 1u) >> kSubFieldBits) == 0, "as_counter() arg too large");
    Elt r(one());
    for (size_t i = 0; i < kSubFieldBits; ++i) {
      Elt factor = one();
      add(factor, select_bit(addf(counter_beta(i), one()), (a >> i) & 1));
      mul(r, factor);
    }
    return CElt{r};
  }
  CElt negf(const CElt &a) const { return CElt{invertf(a.e)}; }
  Elt counter_beta(size_t i) const {
    check(i < kSubFieldBits, "i < kSubFieldBits");
    return counter_beta_[i];
  }

  // Convert a counter into *some* field element such that the counter is
  // zero (as a counter) iff the field element is zero.  Since
  // n as a counter is g^n, we have ((g^n - 1) = 0) <=> (n = 0)
  Elt znz_indicator(const CElt &celt) const { return subf(celt.e, one()); }

private:
  Elt kone_;
  Elt kx_;
  Elt kinvx_; // x^{-1}
  Elt kg_;
  Elt kinvg_;                       // g^{-1}
  Elt beta_[kSubFieldBits];         // basis of the subfield viewed as a
                                    // vector space over GF(2)
  Elt counter_beta_[kSubFieldBits]; // basis of the multiplicative group
                                    // of counters.

  // LU decomposition of beta_, in unpacked format.  We store L^{-1}
  // instead of L, see comments in beta_ref()
  N1 u_[kSubFieldBits];
  uint64_t linv_[kSubFieldBits];

  // ldnz_[i] stores the column index of the leading nonzero in u_[i].
  // This array is in principle redundant, since one can always
  // reconstruct it from u_, but we cache it for efficiency.
  size_t ldnz_[kSubFieldBits];

  Elt poly_evaluation_points_[kNPolyEvaluationPoints];
  Elt newton_denominators_[kNPolyEvaluationPoints][kNPolyEvaluationPoints];

  void byinvx(Elt &u) const {
    auto a = uint64x4_of_gf2_256(u.n);
    const uint64_t mask = 0 - (a[0] & 1);
    u.n = gf2_256_of_uint64x4({((a[0] >> 1) | (a[1] << 63)) ^ (mask & 0x212),
                               (a[1] >> 1) | (a[2] << 63),
                               (a[2] >> 1) | (a[3] << 63),
                               (a[3] >> 1) ^ (mask & (uint64_t{1} << 63))});
  }

  Elt subfield_generator() {
    // Let k = kSubFieldLogBits and n = kLogBits.
    // Let x be the generator of Field.

    // The generator r of the subfield is then
    //    x^{(2^{2^n}-1)/(2^{2^k}-1)}

    // Compute r via the identity
    //   (2^{2^n}-1)/(2^{2^k}-1) =
    //      (2^{2^k}+1)*(2^{2^(k+1)}+1)*...*(2^{2^(n-1)}+1)
    Elt r(kx_);
    for (size_t i = kSubFieldLogBits; i < kLogBits; ++i) {
      // s <- r^{2^(2^i))
      Elt s(r);
      for (size_t j = 0; j < (1u << i); ++j) {
        mul(s, s);
      }
      // r <- r^{2^(2^i)+1)
      mul(r, s);
    }

    return r;
  }

  // beta_ref() is a just a variant of Gaussian elimination, but
  // because many such variants exist, we now explain the exact
  // mechanics of the algorithm.
  //
  // The problem that we need to solve is the inversion of
  // of_scalar(): given e = of_scalar(u), solve for u.  The constraint
  // we have is that e and u are arrays of bits, conveniently stored
  // in uint64_t, and ideally we want to perform parallel bitwise
  // operations, as opposed to extracting individual bits.
  //
  // Consider the following block matrix, or tableau:
  //
  //     [ B | -I ]
  //     [ ------ ]
  //     [ e | u  ]
  //
  // Here e and u are reinterpreted as row vectors of GF(2) elements;
  // I is the identity matrix; B is such that B[i] (the i-th row of b)
  // is beta(i) (the i-th element of the basis of the subfield), and
  // beta(i) is interpreted as a row vector of 256 GF(2) elements.
  // (The minus sign in -I is irrelevant over GF(2), but would be
  // necessary over other fields.)
  //
  // We now postulate that the only allowed operation on the tableau
  // is "axpy": add one row to another, which we can do efficiently
  // via bitwise xor.
  //
  // of_scalar(u) can be reinterpreted in terms axpy as follows.
  // Start with a tableau with e=0.  Reduce u to 0 via axpy
  // operations, e.g., for all i such that u[i] = 1, add row i to the
  // last row.  Because this is exactly what of_scalar() does, at the
  // end of the process we have e = of_scalar(u).  Because I is
  // full-rank, any sequence of axpy's that reduces u to 0 produces
  // the same e.
  //
  // We now want to invert the of_scalar() process.  We cannot apply
  // the axpy operations in of_scalar() in reverse order, because we
  // don't know u, and thus we don't know which operations
  // of_scalar(u) would apply.  However, because B is a basis, any
  // sequence of axpy operations that starts with u=0 and reduces e to
  // 0 reconstructs the same u.
  //
  // For lack of a better idea, we choose the following sequence of
  // axpy operations.  First reduce B to row-echelon form via axpy
  // operations on B, and then reduce e to zero via additional axpy
  // operations.  A matrix U is in row-echelon form if the following
  // condition holds: i' > i implies that U[i'][ldnz[i]] = 0, where
  // ldnz[i] is the column index of the leading nonzero in row i.
  //
  // Since B is constant, we choose to pre-compute the row-echelon
  // form of B in beta_ref(), and finish the process in solve() when e
  // is known, for multiple values of e.
  //
  // As it happens, reducing B to row-echelon transforms the -I
  // in the upper-right block to -L^{-1}, where B=LU is the LU
  // factorization of B.  We don't use this correspondence anywhere
  // in the code other than in the choice of the name Linv for the block.
  //
  void beta_ref() {
    for (size_t i = 0; i < kSubFieldBits; ++i) {
      // B in the tableau, becomes U at the end.
      u_[i] = beta_[i].unpack();

      // -I in the tableau, becomes -L^{-1} at the end.
      // Ignore the minus sign over GF(2).
      linv_[i] = (static_cast<uint64_t>(1) << i);
    }

    // Reduce B to row-echelon form.
    //
    // Invariant: B([0,RNK), [0,J)) is already in row-echelon form.
    // The loop body extends this property to J+1 and possibly RNK+1.
    size_t rnk = 0;
    for (size_t j = 0; rnk < kSubFieldBits && j < kBits; ++j) {
      // find pivot at row >= RNK in column J
      for (size_t i = rnk; i < kSubFieldBits; ++i) {
        if (u_[i].bit(j)) {
          std::swap(u_[rnk], u_[i]);
          std::swap(linv_[rnk], linv_[i]);
          goto have_pivot;
        }
      }
      // If we get here there is no pivot.  Keep the rank RNK the same
      // and proceed to the next column ++J
      continue;

    have_pivot:
      ldnz_[rnk] = j;

      // Pivot on [rnk][j].
      for (size_t i1 = rnk + 1; i1 < kSubFieldBits; ++i1) {
        if (u_[i1].bit(j)) {
          u_[i1].add(u_[rnk]);     // axpy on U
          linv_[i1] ^= linv_[rnk]; // axpy on Linv
        }
      }
      ++rnk;
    }

    // the basis is indeed a basis:
    check(rnk == kSubFieldBits, "rnk == kSubFieldBits");
  }

  std::pair<N1, uint64_t> solve(const Elt &e) const {
    uint64_t u = 0;
    N1 ue = e.unpack();
    for (size_t rnk = 0; rnk < kSubFieldBits; ++rnk) {
      size_t j = ldnz_[rnk];
      const uint64_t mask = uint64_t{0} - uint64_t(ue.bit(j));
      for (size_t limb = 0; limb < N1::kLimbs; ++limb)
        ue.limb_[limb] ^= u_[rnk].limb_[limb] & mask;
      u ^= linv_[rnk] & mask;
    }

    return std::pair(ue, u);
  }
};

} // namespace proofs

#endif // PRIVACY_PROOFS_ZK_LIB_GF2K_GF2_256_H_
