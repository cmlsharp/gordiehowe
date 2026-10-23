// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#ifndef LFB_FALCON_FP_GOLDILOCKS4_H_
#define LFB_FALCON_FP_GOLDILOCKS4_H_
#include "fp_goldilocks.h"
#include <array>
namespace proofs {
// X^4-7 is irreducible: 7 is a primitive element of F_p, p=1 mod 4.
// Tower representation (a0+a2*u)+(a1+a3*u)*v, u^2=7, v^2=u.
// Products are schoolbook with one reduction per coefficient; scalar
// twiddles use four base products.
class Fp64G4 {
public:
  using BaseField = Fp64G;
  static constexpr std::array<uint64_t,4> kProtocolFieldId{Fp64G::kP,4,7,0};
  using Scalar = Fp64G::Elt;
  using TypeTag = PrimeFieldTypeTag;
  static constexpr size_t kBytes = 32, kBits = 256, kIntegerBits = 63,
                          kSubFieldBytes = 8, kSubFieldBits = 64,
                          kNPolyEvaluationPoints = 6;
  static constexpr bool kCharacteristicTwo = false, kSupportsDot = true;
  struct Elt {
    std::array<Scalar, 4> e{};
    bool operator==(const Elt &b) const {
      uint64_t diff = 0;
      for (size_t i = 0; i < 4; ++i)
        diff |= e[i].n ^ b.e[i].n;
      return diff == 0;
    }
    bool operator!=(const Elt &b) const { return !(*this == b); }
  };
  const Fp64G &base_field() const { return goldilocks_base(); }
  size_t max_rs_domain() const { return base_field().max_rs_domain(); }
  Elt of_scalar(uint64_t a) const {
    return of_scalar(base_field().of_scalar(a));
  }
  Elt of_scalar(Scalar a) const { return Elt{{a, {0}, {0}, {0}}}; }
  Elt of_scalar_field(uint64_t a) const { return of_scalar(a); }
  template <size_t N> Elt of_string(const char (&s)[N]) const {
    return of_scalar(base_field().of_string(s));
  }
  Elt addf(Elt a, const Elt &b) const {
    for (size_t i = 0; i < 4; ++i)
      a.e[i].n = Fp64G::addr_lanes(a.e[i].n, b.e[i].n);
    return a;
  }
  Elt subf(Elt a, const Elt &b) const {
    for (size_t i = 0; i < 4; ++i)
      a.e[i].n = Fp64G::subr_lanes(a.e[i].n, b.e[i].n);
    return a;
  }
  Elt negf(Elt a) const {
    for (auto &x : a.e)
      base_field().neg(x);
    return a;
  }
  using Pair = std::array<uint64_t, 2>;
  static Pair pa(Pair a, Pair b) {
    return {Fp64G::addr(a[0], b[0]), Fp64G::addr(a[1], b[1])};
  }
  static Pair ps(Pair a, Pair b) {
    return {Fp64G::subr(a[0], b[0]), Fp64G::subr(a[1], b[1])};
  }
  static Pair pu(Pair a) { return {Fp64G::mulr(7, a[1]), a[0]}; }
  static Pair pm(Pair a, Pair b) {
    auto l = Fp64G::mulr(a[0], b[0]), h = Fp64G::mulr(a[1], b[1]);
    auto m = Fp64G::mulr(Fp64G::addr(a[0], a[1]), Fp64G::addr(b[0], b[1]));
    return {Fp64G::addr(l, Fp64G::mulr(7, h)),
            Fp64G::subr(Fp64G::subr(m, l), h)};
  }
  // Coefficient k of the product is sum_{i+j=k} a_i b_j + 7 sum_{i+j=k+4}
  // a_i b_j. Each sum is exact in 128 bits and a carry limb, and each
  // coefficient is reduced once: sixteen base products, four reductions.
  struct Wide {
    unsigned __int128 lo;
    uint64_t top;
  };
  static void wide_mac(Wide &w, uint64_t x, uint64_t y) {
    const unsigned __int128 p = (unsigned __int128)x * y;
    w.lo += p;
    w.top += uint64_t(w.lo < p);
  }
  // l + 7 h = l + 8 h - h; the carry limb stays below 2^31 for the at most
  // four products in l and three in h.
  static uint64_t reduce_l7h(const Wide &l, const Wide &h) {
    const unsigned __int128 h8 = h.lo << 3;
    uint64_t top = (h.top << 3) | uint64_t(h.lo >> 125);
    const unsigned __int128 h7 = h8 - h.lo;
    top -= h.top + uint64_t(h8 < h.lo);
    const unsigned __int128 lo = h7 + l.lo;
    top += l.top + uint64_t(lo < h7);
    return Fp64G::reduce192(lo, top);
  }
  Elt mulf(const Elt &a, const Elt &b) const {
    Elt r;
    for (size_t k = 0; k < 4; ++k) {
      Wide l{0, 0}, h{0, 0};
      for (size_t i = 0; i <= k; ++i)
        wide_mac(l, a.e[i].n, b.e[k - i].n);
      for (size_t i = k + 1; i < 4; ++i)
        wide_mac(h, a.e[i].n, b.e[k + 4 - i].n);
      r.e[k].n = reduce_l7h(l, h);
    }
    return r;
  }
  Elt mulf(Elt a, Scalar b) const {
    for (auto &x : a.e)
      x.n = Fp64G::mulr(x.n, b.n);
    return a;
  }
  Elt invertf(const Elt &a) const {
    Pair x{a.e[0].n, a.e[2].n}, y{a.e[1].n, a.e[3].n};
    auto n = ps(pm(x, x), pu(pm(y, y)));
    auto den = Fp64G::subr(Fp64G::mulr(n[0], n[0]),
                           Fp64G::mulr(7, Fp64G::mulr(n[1], n[1])));
    auto inv = base_field().invertf(Scalar{den}).n;
    n = {Fp64G::mulr(n[0], inv), Fp64G::subr(0, Fp64G::mulr(n[1], inv))};
    x = pm(x, n);
    y = ps({0, 0}, pm(y, n));
    return Elt{{Scalar{x[0]}, Scalar{y[0]}, Scalar{x[1]}, Scalar{y[1]}}};
  }
  void add(Elt &a, const Elt &b) const { a = addf(a, b); }
  void sub(Elt &a, const Elt &b) const { a = subf(a, b); }
  void mul(Elt &a, const Elt &b) const { a = mulf(a, b); }
  void mul(Elt &a, Scalar b) const { a = mulf(a, b); }
  void neg(Elt &a) const { a = negf(a); }
  void invert(Elt &a) const { a = invertf(a); }
  // Seven unreduced convolution coefficients. The extra carry limb makes
  // accumulation exact beyond 128 bits; no modular reductions per product.
  struct Accum {
    unsigned __int128 lo[7]{};
    uint64_t hi[7]{};
  };
  static void wide_add(Accum &a, size_t i, unsigned __int128 p) {
    const auto old = a.lo[i];
    a.lo[i] += p;
    a.hi[i] += a.lo[i] < old;
  }
  void mac(Accum &a, const Elt &x, const Elt &y) const {
    for (size_t i = 0; i < 4; ++i)
      for (size_t j = 0; j < 4; ++j)
        wide_add(a, i + j, (unsigned __int128)x.e[i].n * y.e[j].n);
  }
  Elt reduce(const Accum &a) const {
    // 2^128 = -2^32 mod p. hi is bounded by the number of products;
    // all repository tableaux are limited to fewer than 2^28 entries.
    uint64_t r[7];
    for (size_t i = 0; i < 7; ++i)
      r[i] = Fp64G::subr(Fp64G::reduce128(a.lo[i]),
                         Fp64G::mulr(a.hi[i], uint64_t{1} << 32));
    Elt out;
    for (size_t i = 0; i < 4; ++i)
      out.e[i] = {r[i]};
    for (size_t i = 4; i < 7; ++i)
      out.e[i - 4].n = Fp64G::addr(out.e[i - 4].n, Fp64G::mulr(7, r[i]));
    return out;
  }
  Elt mulf_schoolbook(const Elt &a, const Elt &b) const {
    Accum x{};
    mac(x, a, b);
    return reduce(x);
  }

  Elt zero() const { return Elt{}; }
  Elt one() const { return of_scalar(1); }
  Elt two() const { return of_scalar(2); }
  Elt half() const { return of_scalar(base_field().half()); }
  Elt mone() const { return of_scalar(base_field().mone()); }
  Elt beta(size_t i) const {
    check(i < 64, "beta index");
    return of_scalar(uint64_t{1} << i);
  }
  Elt poly_evaluation_point(size_t i) const {
    return of_scalar(base_field().poly_evaluation_point(i));
  }
  Elt newton_denominator(size_t k, size_t i) const {
    return of_scalar(base_field().newton_denominator(k, i));
  }
  bool in_subfield(const Elt &a) const {
    return !(a.e[1].n | a.e[2].n | a.e[3].n);
  }
  uint64_t to_u64(const Elt &a) const {
    check(in_subfield(a), "not scalar");
    return a.e[0].n;
  }
  std::optional<Elt> of_bytes_field(const uint8_t *b) const {
    Elt a;
    for (size_t i = 0; i < 4; ++i) {
      auto s = base_field().of_bytes_field(b + 8 * i);
      if (!s)
        return std::nullopt;
      a.e[i] = *s;
    }
    return a;
  }
  void to_bytes_field(uint8_t *b, const Elt &a) const {
    for (size_t i = 0; i < 4; ++i)
      base_field().to_bytes_field(b + 8 * i, a.e[i]);
  }
  std::optional<Elt> of_bytes_subfield(const uint8_t *b) const {
    auto s = base_field().of_bytes_field(b);
    if (!s)
      return std::nullopt;
    return of_scalar(*s);
  }
  void to_bytes_subfield(uint8_t *b, const Elt &a) const {
    check(in_subfield(a), "not scalar");
    base_field().to_bytes_field(b, a.e[0]);
  }
  Elt sample(const std::function<void(size_t, uint8_t *)> &fill) const {
    Elt a;
    for (auto &x : a.e)
      x = base_field().sample(fill);
    return a;
  }
  Elt sample_subfield(
      const std::function<void(size_t, uint8_t *)> &fill) const {
    return of_scalar(base_field().sample(fill));
  }
  struct CElt {
    Elt e;
  };
  CElt as_counter(uint64_t a) const { return {of_scalar(a)}; }
  Elt znz_indicator(const CElt &a) const { return a.e; }
  struct NatScaledForDot {
    Elt e;
  };
  NatScaledForDot prescale_for_dot(Elt a) const { return {a}; }
  Elt dot(size_t n, const Nat<1> *a, const NatScaledForDot *b) const {
    Elt r{};
    for (size_t i = 0; i < n; ++i)
      add(r, mulf(b[i].e, base_field().of_scalar(a[i].u64()[0])));
    return r;
  }
};
template <class BaseFactory> class Fp64G4ReedSolomonFactory {
  using BasePtr = decltype(std::declval<const BaseFactory &>().make(0, 0));

public:
  class Encoder {
    size_t n_, m_;
    BasePtr rs_;

  public:
    Encoder(size_t n, size_t m, BasePtr rs)
        : n_(n), m_(m), rs_(std::move(rs)) {}
    void interpolate(Fp64G4::Elt *y, bool subfield_only = false) const {
      std::vector<Fp64G::Elt> t(m_);
      for (size_t k = 0; k < (subfield_only ? 1 : 4); ++k) {
        for (size_t i = 0; i < n_; ++i)
          t[i] = y[i].e[k];
        rs_->interpolate(t.data());
        for (size_t i = n_; i < m_; ++i)
          y[i].e[k] = t[i];
      }
      if (subfield_only)
        for (size_t i = n_; i < m_; ++i)
          for (size_t k = 1; k < 4; ++k)
            y[i].e[k] = {0};
    }
  };
  explicit Fp64G4ReedSolomonFactory(const BaseFactory &b) : base_(b) {}
  std::unique_ptr<Encoder> make(size_t n, size_t m) const {
    return std::make_unique<Encoder>(n, m, base_.make(n, m));
  }

private:
  const BaseFactory &base_;
};
} // namespace proofs
#endif
