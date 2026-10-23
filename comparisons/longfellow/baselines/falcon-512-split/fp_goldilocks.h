// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Goldilocks prime p = 2^64 - 2^32 + 1 and its quadratic extension
// F_p[x]/(x^2 - 7).  Circuits run over the extension, whose size (about
// 2^128) carries the soundness of every challenge; witness rows stay in the
// subfield F_p and open at 8 bytes per entry.
//
// Elements are canonical uint64 values in [0, p).  A 128-bit product
// hi*2^64 + lo reduces with 2^64 = 2^32 - 1 and 2^96 = -1 (mod p).
//
// Integer identities checked over these fields hold exactly only while both
// sides stay below p; kIntegerBits = 63 is the bound gadgets check against.

#ifndef LFB_FALCON_FP_GOLDILOCKS_H_
#define LFB_FALCON_FP_GOLDILOCKS_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

#include "algebra/fp_generic.h"
#include "algebra/nat.h"
#include "util/panic.h"

namespace proofs {

// ---- F_p, p = 2^64 - 2^32 + 1 ---------------------------------------------
class Fp64G {
 public:
  using TypeTag = PrimeFieldTypeTag;
  static constexpr uint64_t kP = 0xFFFFFFFF00000001ull;
  static constexpr uint64_t kEps = 0xFFFFFFFFull;  // 2^64 mod p
  static constexpr size_t kU64 = 1;
  static constexpr size_t kBytes = 8;
  static constexpr size_t kSubFieldBytes = 8;
  static constexpr size_t kBits = 64;
  static constexpr size_t kIntegerBits = 63;
  static constexpr size_t kSubFieldBits = 64;
  static constexpr bool kCharacteristicTwo = false;
  static constexpr bool kSupportsDot = false;
  static constexpr size_t kNPolyEvaluationPoints = 6;

  struct Elt {
    uint64_t n;
    bool operator==(const Elt& y) const { return n == y.n; }
    bool operator!=(const Elt& y) const { return n != y.n; }
  };

  Fp64G() {
    for (uint64_t i = 0; i < kNPolyEvaluationPoints; ++i) {
      inv_small_[i] = i == 0 ? Elt{0} : invertf(of_scalar(i));
    }
  }
  Fp64G(const Fp64G&) = delete;
  Fp64G& operator=(const Fp64G&) = delete;

  size_t max_rs_domain() const { return size_t{1} << 32; }

  // a + b + kEps c and a - b - kEps c, for the carry or borrow c of the
  // 64-bit operation. On x86-64 the carry becomes the mask by sbb, since
  // clang compiles the portable form to a branch, which random operands
  // mispredict half the time.
  static inline uint64_t add_eps(uint64_t a, uint64_t b) {
#if defined(__x86_64__)
    uint64_t adj;
    asm("addq %[b], %[a]\n\tsbbl %k[adj], %k[adj]"
        : [a] "+r"(a), [adj] "=&r"(adj)
        : [b] "r"(b)
        : "cc");
    return a + adj;
#else
    const uint64_t s = a + b;
    return s + (kEps & (uint64_t{0} - uint64_t(s < b)));
#endif
  }
  static inline uint64_t sub_eps(uint64_t a, uint64_t b) {
#if defined(__x86_64__)
    uint64_t adj;
    asm("subq %[b], %[a]\n\tsbbl %k[adj], %k[adj]"
        : [a] "+r"(a), [adj] "=&r"(adj)
        : [b] "r"(b)
        : "cc");
    return a - adj;
#else
    return a - b - (kEps & (uint64_t{0} - uint64_t(a < b)));
#endif
  }

  static inline uint64_t reduce128(unsigned __int128 x) { return reduce192(x, 0); }
  // x + 2^128 top for top < 2^31, by 2^96 = -1 and 2^128 = -2^32 (mod p):
  // hi_hi 2^96 + top 2^128 = -(hi_hi + top 2^32), and that sum is below p.
  static inline uint64_t reduce192(unsigned __int128 x, uint64_t top) {
    const uint64_t lo = (uint64_t)x, hi = (uint64_t)(x >> 64);
    const uint64_t hi_hi = (hi >> 32) + (top << 32), hi_lo = hi & kEps;
    // On a borrow, add p = 2^64 - kEps.
    const uint64_t t0 = sub_eps(lo, hi_hi);
    const uint64_t t1 = hi_lo * kEps;
    // On a carry, 2^64 = kEps.
    uint64_t t2 = add_eps(t0, t1);
    // t2 >= p only for t2 within 2^32 of 2^64, so this branch predicts.
    t2 -= kP & (uint64_t{0} - uint64_t(t2 >= kP));
    return t2;
  }
  static inline uint64_t addr(uint64_t a, uint64_t b) {
    // (a + kEps) + b carries exactly when a + b >= p, and is then
    // a + b - p; without the carry, subtract kEps again.
    return add_eps(a + kEps, b) - kEps;
  }
  static inline uint64_t subr(uint64_t a, uint64_t b) { return sub_eps(a, b); }
  // addr and subr by masks, for pairs of coordinates: clang vectorizes a
  // pair into one 128-bit lane operation without a branch.
  static inline uint64_t addr_lanes(uint64_t a, uint64_t b) {
    uint64_t s = a + b;
    // On carry, subtracting p modulo 2^64 adds epsilon as required.
    const uint64_t reduce = uint64_t(s < a) | uint64_t(s >= kP);
    s -= kP & (uint64_t{0} - reduce);
    return s;
  }
  static inline uint64_t subr_lanes(uint64_t a, uint64_t b) {
    uint64_t d = a - b;
    d -= kEps & (uint64_t{0} - uint64_t(a < b));
    return d;
  }
  static inline uint64_t mulr(uint64_t a, uint64_t b) {
    return reduce128((unsigned __int128)a * b);
  }

  void add(Elt& a, const Elt& y) const { a.n = addr(a.n, y.n); }
  void sub(Elt& a, const Elt& y) const { a.n = subr(a.n, y.n); }
  void mul(Elt& a, const Elt& y) const { a.n = mulr(a.n, y.n); }
  void neg(Elt& a) const { a.n = a.n == 0 ? 0 : kP - a.n; }
  void invert(Elt& a) const { a = invertf(a); }
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
  Elt negf(Elt a) const {
    neg(a);
    return a;
  }
  Elt powf(Elt a, uint64_t e) const {
    Elt r{1};
    while (e) {
      if (e & 1) mul(r, a);
      mul(a, a);
      e >>= 1;
    }
    return r;
  }
  Elt invertf(Elt a) const {
    check(a.n != 0, "invert zero");
    return powf(a, kP - 2);
  }

  Elt of_scalar(uint64_t a) const { return Elt{a >= kP ? a - kP : a}; }
  Elt of_scalar_field(uint64_t a) const { return of_scalar(a); }
  template <size_t N>
  Elt of_string(const char (&s)[N]) const {
    Elt r{0};
    for (size_t i = 0; i + 1 < N && s[i]; ++i) {
      check(s[i] >= '0' && s[i] <= '9', "decimal digits only");
      r = addf(mulf(r, Elt{10}), Elt{uint64_t(s[i] - '0')});
    }
    return r;
  }
  uint64_t to_u64(const Elt& x) const { return x.n; }

  std::optional<Elt> of_bytes_field(const uint8_t ab[/* 8 */]) const {
    uint64_t v = 0;
    for (size_t i = 0; i < 8; ++i) v |= uint64_t(ab[i]) << (8 * i);
    if (v >= kP) return std::nullopt;
    return Elt{v};
  }
  void to_bytes_field(uint8_t ab[/* 8 */], const Elt& x) const {
    for (size_t i = 0; i < 8; ++i) ab[i] = uint8_t(x.n >> (8 * i));
  }
  std::optional<Elt> of_bytes_subfield(const uint8_t ab[]) const {
    return of_bytes_field(ab);
  }
  void to_bytes_subfield(uint8_t ab[], const Elt& x) const {
    to_bytes_field(ab, x);
  }
  bool in_subfield(const Elt&) const { return true; }
  Elt sample(
      const std::function<void(size_t n, uint8_t buf[])>& fill_bytes) const {
    uint8_t buf[8];
    for (;;) {
      fill_bytes(8, buf);
      if (auto e = of_bytes_field(buf)) return *e;
    }
  }
  Elt sample_subfield(
      const std::function<void(size_t n, uint8_t buf[])>& fill_bytes) const {
    return sample(fill_bytes);
  }

  Elt zero() const { return Elt{0}; }
  Elt one() const { return Elt{1}; }
  Elt two() const { return Elt{2}; }
  Elt half() const { return Elt{(kP + 1) / 2}; }
  Elt mone() const { return Elt{kP - 1}; }
  Elt poly_evaluation_point(size_t i) const {
    check(i < kNPolyEvaluationPoints, "i < kNPolyEvaluationPoints");
    return Elt{i};
  }
  Elt newton_denominator(size_t k, size_t i) const {
    check(k < kNPolyEvaluationPoints && i <= k && i != 0, "newton index");
    return inv_small_[i];
  }

  struct CElt {
    Elt e;
  };
  CElt as_counter(uint64_t a) const { return CElt{of_scalar(a)}; }
  Elt znz_indicator(const CElt& c) const { return c.e; }

  struct Accum {
    Elt acc;
  };
  Elt reduce(const Accum& a) const { return a.acc; }
  void mac(Accum& a, const Elt& x, const Elt& y) const {
    add(a.acc, mulf(x, y));
  }

 private:
  Elt inv_small_[kNPolyEvaluationPoints];
};

inline const Fp64G& goldilocks_base() {
  static const Fp64G f;
  return f;
}

// ---- F_{p^2} = F_p[x]/(x^2 - 7) -------------------------------------------
class Fp64G2 {
 public:
  using BaseField = Fp64G;
  using Scalar = Fp64G::Elt;
  using TypeTag = PrimeFieldTypeTag;
  static constexpr uint64_t kW = 7;  // generates F_p^*, so a non-residue
  static constexpr std::array<uint64_t, 4> kProtocolFieldId{Fp64G::kP, 2, kW,
                                                            0};
  static constexpr size_t kBytes = 16;
  static constexpr size_t kBits = 128;
  static constexpr size_t kIntegerBits = Fp64G::kIntegerBits;
  static constexpr size_t kSubFieldBytes = 8;
  static constexpr size_t kSubFieldBits = 64;
  static constexpr bool kCharacteristicTwo = false;
  static constexpr bool kSupportsDot = true;
  static constexpr size_t kNPolyEvaluationPoints = 6;

  struct Elt {
    Scalar re, im;
    bool operator==(const Elt& y) const { return re == y.re && im == y.im; }
    bool operator!=(const Elt& y) const { return !operator==(y); }
  };

  Fp64G2() : f_(goldilocks_base()) {}
  Fp64G2(const Fp64G2&) = delete;
  Fp64G2& operator=(const Fp64G2&) = delete;

  const Fp64G& base_field() const { return f_; }
  size_t max_rs_domain() const { return f_.max_rs_domain(); }

  void add(Elt& a, const Elt& y) const {
    a.re.n = Fp64G::addr_lanes(a.re.n, y.re.n);
    a.im.n = Fp64G::addr_lanes(a.im.n, y.im.n);
  }
  void sub(Elt& a, const Elt& y) const {
    a.re.n = Fp64G::subr_lanes(a.re.n, y.re.n);
    a.im.n = Fp64G::subr_lanes(a.im.n, y.im.n);
  }
  // (a0 + a1 x)(b0 + b1 x) = (a0 b0 + 7 a1 b1) + (a0 b1 + a1 b0) x.
  // Each coordinate is summed exactly in 128 bits plus a carry limb and
  // reduced once: two reductions per product.
  struct Wide {
    unsigned __int128 lo;
    uint64_t top;
  };
  static inline Wide re_wide(uint64_t a0, uint64_t a1, uint64_t b0,
                             uint64_t b1) {
    const unsigned __int128 p11 = (unsigned __int128)a1 * b1;
    // 7 p11 = 8 p11 - p11, with the bits above 2^128 in top.
    static_assert(kW == 7, "the shift form of the non-residue");
    const unsigned __int128 p11x8 = p11 << 3;
    uint64_t top = uint64_t(p11 >> 125);
    const unsigned __int128 p11x7 = p11x8 - p11;
    top -= uint64_t(p11x8 < p11);
    const unsigned __int128 lo = p11x7 + (unsigned __int128)a0 * b0;
    top += uint64_t(lo < p11x7);
    return Wide{lo, top};
  }
  static inline Wide im_wide(uint64_t a0, uint64_t a1, uint64_t b0,
                             uint64_t b1) {
    const unsigned __int128 p01 = (unsigned __int128)a0 * b1;
    const unsigned __int128 lo = p01 + (unsigned __int128)a1 * b0;
    return Wide{lo, uint64_t(lo < p01)};
  }
  void mul(Elt& a, const Elt& y) const {
    const uint64_t a0 = a.re.n, a1 = a.im.n, b0 = y.re.n, b1 = y.im.n;
    const Wide re = re_wide(a0, a1, b0, b1);
    const Wide im = im_wide(a0, a1, b0, b1);
    a.re.n = Fp64G::reduce192(re.lo, re.top);
    a.im.n = Fp64G::reduce192(im.lo, im.top);
  }
  void mul(Elt& a, const Scalar& y) const {
    a.re.n = Fp64G::mulr(a.re.n, y.n);
    a.im.n = Fp64G::mulr(a.im.n, y.n);
  }
  void neg(Elt& a) const {
    f_.neg(a.re);
    f_.neg(a.im);
  }
  void invert(Elt& a) const {
    // 1/(a0 + a1 x) = (a0 - a1 x)/(a0^2 - 7 a1^2)
    Scalar n = f_.subf(f_.mulf(a.re, a.re),
                       f_.mulf(Scalar{kW}, f_.mulf(a.im, a.im)));
    n = f_.invertf(n);
    a.re = f_.mulf(a.re, n);
    a.im = f_.negf(f_.mulf(a.im, n));
  }
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

  // Unreduced sums of the products' coordinates: 128 bits and a carry
  // limb each, reduced once. A product adds at most 7 to a carry limb.
  struct Accum {
    unsigned __int128 re, im;
    uint64_t re_top, im_top;
  };
  static inline void wide_add(unsigned __int128& lo, uint64_t& top,
                              const Wide& x) {
    const unsigned __int128 old = lo;
    lo += x.lo;
    top += x.top + uint64_t(lo < old);
  }
  Elt reduce(const Accum& a) const {
    // 2^128 = -2^32 (mod p), for any 64-bit carry limb.
    const uint64_t re = Fp64G::subr(Fp64G::reduce128(a.re),
                                    Fp64G::mulr(a.re_top, uint64_t{1} << 32));
    const uint64_t im = Fp64G::subr(Fp64G::reduce128(a.im),
                                    Fp64G::mulr(a.im_top, uint64_t{1} << 32));
    return Elt{Scalar{re}, Scalar{im}};
  }
  void mac(Accum& a, const Elt& x, const Elt& y) const {
    const uint64_t a0 = x.re.n, a1 = x.im.n, b0 = y.re.n, b1 = y.im.n;
    wide_add(a.re, a.re_top, re_wide(a0, a1, b0, b1));
    wide_add(a.im, a.im_top, im_wide(a0, a1, b0, b1));
  }

  Elt of_scalar(uint64_t a) const { return Elt{f_.of_scalar(a), Scalar{0}}; }
  Elt of_scalar(const Scalar& e) const { return Elt{e, Scalar{0}}; }
  Elt of_scalar_field(uint64_t a) const { return of_scalar(a); }
  Elt of_scalar_field(const Scalar& e) const { return of_scalar(e); }
  template <size_t N>
  Elt of_string(const char (&s)[N]) const {
    return Elt{f_.of_string(s), Scalar{0}};
  }

  std::optional<Elt> of_bytes_field(const uint8_t ab[/* 16 */]) const {
    auto re = f_.of_bytes_field(ab);
    auto im = f_.of_bytes_field(ab + 8);
    if (!re || !im) return std::nullopt;
    return Elt{*re, *im};
  }
  void to_bytes_field(uint8_t ab[/* 16 */], const Elt& x) const {
    f_.to_bytes_field(ab, x.re);
    f_.to_bytes_field(ab + 8, x.im);
  }
  bool in_subfield(const Elt& e) const { return e.im.n == 0; }
  std::optional<Elt> of_bytes_subfield(const uint8_t ab[/* 8 */]) const {
    auto re = f_.of_bytes_field(ab);
    if (!re) return std::nullopt;
    return of_scalar(*re);
  }
  void to_bytes_subfield(uint8_t ab[/* 8 */], const Elt& x) const {
    check(in_subfield(x), "x not in subfield");
    f_.to_bytes_field(ab, x.re);
  }
  Elt sample(
      const std::function<void(size_t n, uint8_t buf[])>& fill_bytes) const {
    auto re = f_.sample(fill_bytes);
    auto im = f_.sample(fill_bytes);
    return Elt{re, im};
  }
  Elt sample_subfield(
      const std::function<void(size_t n, uint8_t buf[])>& fill_bytes) const {
    return of_scalar(f_.sample(fill_bytes));
  }
  uint64_t to_u64(const Elt& x) const {
    check(in_subfield(x), "to_u64 of a non-subfield element");
    return x.re.n;
  }

  // of_scalar(sum_i b[i] 2^i) = sum_i b[i] beta(i)
  Elt beta(size_t i) const {
    check(i < 64, "i < 64");
    return of_scalar(static_cast<uint64_t>(1) << i);
  }

  // Dot product of small integer scalars (one 64-bit limb each) with field
  // elements, for digests over public vectors.
  struct NatScaledForDot {
    Elt e;
  };
  NatScaledForDot prescale_for_dot(Elt e) const { return NatScaledForDot{e}; }
  Elt dot(size_t n, const Nat<1> a[/*n*/], const NatScaledForDot b[/*n*/]) const {
    uint64_t re = 0, im = 0;
    for (size_t i = 0; i < n; ++i) {
      const uint64_t x = a[i].u64()[0];
      re = Fp64G::addr(re, Fp64G::mulr(x, b[i].e.re.n));
      im = Fp64G::addr(im, Fp64G::mulr(x, b[i].e.im.n));
    }
    return Elt{Scalar{re}, Scalar{im}};
  }

  Elt zero() const { return of_scalar(uint64_t{0}); }
  Elt one() const { return of_scalar(uint64_t{1}); }
  Elt two() const { return of_scalar(uint64_t{2}); }
  Elt half() const { return of_scalar(f_.half()); }
  Elt mone() const { return of_scalar(f_.mone()); }
  Elt poly_evaluation_point(size_t i) const {
    return of_scalar(f_.poly_evaluation_point(i));
  }
  Elt newton_denominator(size_t k, size_t i) const {
    return of_scalar(f_.newton_denominator(k, i));
  }

  struct CElt {
    Elt e;
  };
  CElt as_counter(uint64_t a) const { return CElt{of_scalar(a)}; }
  Elt znz_indicator(const CElt& c) const { return c.e; }

 private:
  const Fp64G& f_;
};

// A primitive 2^32-th root of unity of F_p: 7^((p-1)/2^32).
inline Fp64G::Elt goldilocks_root_2_32() {
  const Fp64G& f = goldilocks_base();
  return f.powf(f.of_scalar(Fp64G2::kW), (Fp64G::kP - 1) >> 32);
}

// Reed-Solomon over F_{p^2} with evaluation points in F_p: each component is
// encoded by an F_p encoder from BaseFactory, and a subfield-only row encodes
// its first component alone, which keeps the row in F_p.
template <class BaseFactory>
class Fp64G2ReedSolomonFactory {
  using BasePtr = decltype(std::declval<const BaseFactory&>().make(0, 0));

 public:
  class Encoder {
   public:
    Encoder(size_t n, size_t m, BasePtr rs) : n_(n), m_(m), rs_(std::move(rs)) {}
    void interpolate(Fp64G2::Elt y[/*m*/], bool subfield_only = false) const {
      std::vector<Fp64G::Elt> t(m_);
      for (size_t i = 0; i < n_; ++i) t[i] = y[i].re;
      rs_->interpolate(t.data());
      for (size_t i = n_; i < m_; ++i) y[i].re = t[i];
      if (subfield_only) {
        for (size_t i = n_; i < m_; ++i) y[i].im = Fp64G::Elt{0};
        return;
      }
      for (size_t i = 0; i < n_; ++i) t[i] = y[i].im;
      rs_->interpolate(t.data());
      for (size_t i = n_; i < m_; ++i) y[i].im = t[i];
    }

   private:
    size_t n_, m_;
    BasePtr rs_;
  };

  explicit Fp64G2ReedSolomonFactory(const BaseFactory& base) : base_(base) {}
  std::unique_ptr<Encoder> make(size_t n, size_t m) const {
    return std::make_unique<Encoder>(n, m, base_.make(n, m));
  }

 private:
  const BaseFactory& base_;
};

}  // namespace proofs

#endif  // LFB_FALCON_FP_GOLDILOCKS_H_
