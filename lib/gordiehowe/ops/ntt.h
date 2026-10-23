// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: negacyclic NTT plans for the structured operators,
// over every field whose prime base field has the needed roots of unity: the
// Goldilocks carriers (Fp64G2, Fp64G4), the native fields over F_q (the
// Falcon fields over q = 12289 and the ML-DSA fields over q = 8380417) and
// the prime field Fp128, its own base field.
//
// The transforms are host_ntt's: NegacyclicPlan (a psi twist, a cyclic DIF
// transform with bit-reversed output, and the matching DIT inverse), the plan
// native_linear::Relation evaluates its rows with. Twiddles lie in the base
// field, so a butterfly multiplies an extension element by a base scalar.
//
// The spectrum order. NegacyclicPlan with root psi sends a to the vector
// a_hat[k] = a(psi^(2 brv(k) + 1)), brv the bit reversal of log2(n) bits.
// That is FIPS 204's NTT order (Algorithm 41, zetas = zeta^brv(i), with
// zeta = 1753 for ML-DSA) and the order of falcon_ntt_ref with
// falcon_ntt_zetas (psi = falcon_root_2n). An operand in this order is a
// polynomial "in NTT form" (Form::kNtt); its root is a parameter of the
// operator, and so part of the system digest.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_NTT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_NTT_H_

#include <cstddef>
#include <cstdint>
#include <optional>
#include <set>
#include <type_traits>
#include <utility>
#include <vector>

#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp_p128.h"
#include "circuits/ntt/emulated_signature.h"
#include "circuits/ntt/host_ntt.h"
#include "util/panic.h"

namespace proofs::gordiehowe::ops {

// The form of a public polynomial operand: its coefficients, or its
// evaluations in the spectrum order above.
enum class Form : uint8_t { kCoefficients = 0, kNtt = 1 };

namespace ntt_detail {
template <class B, class = void>
struct HasModulus : std::false_type {};
template <class B>
struct HasModulus<B, std::void_t<decltype(B::m_)>> : std::true_type {};

inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t q) {
  return static_cast<uint64_t>((unsigned __int128)a * b % q);
}
inline uint64_t powmod(uint64_t a, uint64_t e, uint64_t q) {
  uint64_t r = 1 % q;
  for (a %= q; e; e >>= 1, a = mulmod(a, a, q))
    if (e & 1) r = mulmod(r, a, q);
  return r;
}
// The least primitive root modulo the prime q.
inline uint64_t least_generator(uint64_t q) {
  std::vector<uint64_t> primes;
  uint64_t m = q - 1;
  for (uint64_t d = 2; d * d <= m; ++d)
    if (m % d == 0) {
      primes.push_back(d);
      while (m % d == 0) m /= d;
    }
  if (m > 1) primes.push_back(m);
  for (uint64_t g = 2;; ++g) {
    bool gen = true;
    for (uint64_t l : primes) gen = gen && powmod(g, (q - 1) / l, q) != 1;
    if (gen) return g;
  }
}
inline bool power_of_two(size_t n) { return n >= 1 && (n & (n - 1)) == 0; }
}  // namespace ntt_detail

// Fields with transforms: a prime base field (BaseField, Scalar), base
// scalars embedded by of_scalar, and a product mulf(Elt, Scalar).
template <class F, class = void>
struct FieldNtt {
  static constexpr bool kOk = false;
  using Scalar = typename F::Elt;
};
template <class F>
struct FieldNtt<F, std::void_t<typename F::BaseField, typename F::Scalar>> {
  using Base = typename F::BaseField;
  using Scalar = typename F::Scalar;
  using Elt = typename F::Elt;
  static constexpr bool kCarrier =
      std::is_same_v<F, Fp64G2> || std::is_same_v<F, Fp64G4>;
  static constexpr bool kNative = ntt_detail::HasModulus<Base>::value;
  static constexpr bool kOk = kCarrier || kNative;

  static const Base &base(const F &f) { return f.base_field(); }
  static Scalar scalar(const Elt &x) {
    if constexpr (std::is_same_v<F, Fp64G2>)
      return x.re;
    else
      return x.e[0];
  }
  // An element of the base field of exact order ORDER (a power of two), or
  // nothing when the base field has none. The carriers' is the 2^32-th root
  // squared down (emulated_ntt::negacyclic_root); a native field's is the
  // least primitive root of F_q to the power (q - 1) / ORDER.
  static std::optional<Elt> root(const F &f, size_t order) {
    if (order < 2 || !ntt_detail::power_of_two(order)) return std::nullopt;
    if constexpr (kCarrier) {
      if (order > (size_t{1} << 32)) return std::nullopt;
      auto r = emulated_ntt::carrier_root_2_32(f);
      for (size_t o = size_t{1} << 32; o > order; o >>= 1) r = f.mulf(r, r);
      return r;
    } else {
      const uint64_t q = Base::m_;
      if ((q - 1) % order != 0) return std::nullopt;
      const uint64_t g = ntt_detail::least_generator(q);
      return f.of_scalar(ntt_detail::powmod(g, (q - 1) / order, q));
    }
  }
  // The root of the scheme NTT of length n, which fixes Form::kNtt's order
  // by default: FIPS 204's zeta = 1753 over the ML-DSA field (n = 256, or its
  // power for shorter lengths), falcon_root_2n(n, 12289) over the Falcon
  // field (the least primitive root 11, as falcon_root_2n finds it), and
  // root(f, 2n) elsewhere.
  static std::optional<Elt> scheme_psi(const F &f, size_t n) {
    if (n < 2 || !ntt_detail::power_of_two(n)) return std::nullopt;
    if constexpr (kNative) {
      constexpr uint64_t kMLDSAQ = 8380417, kZeta = 1753;
      if (Base::m_ == kMLDSAQ) {
        if (256 % n != 0) return std::nullopt;
        return f.of_scalar(ntt_detail::powmod(kZeta, 256 / n, kMLDSAQ));
      }
    }
    return root(f, 2 * n);
  }
};
// A prime field with a two-adic root (PrimeRoot<F>): the field is its own
// base, a scalar is an element, and the roots are a primitive 2^kLog-th
// root squared down. Fp128 (p = 2^128 - 2^108 + 1, algebra/fp_p128.h) has
// the root of order 2^108 that fp_p128.h derives in pari-gp.
template <class F>
struct PrimeRoot {
  static constexpr bool kOk = false;
};
template <bool kOptimized>
struct PrimeRoot<Fp128<kOptimized>> {
  static constexpr bool kOk = true;
  static constexpr size_t kLog = 108;
  static constexpr char kRoot[] = "17166008163159356379329005055841088858";
};
template <class F>
struct FieldNtt<F, std::enable_if_t<PrimeRoot<F>::kOk>> {
  using Base = F;
  using Scalar = typename F::Elt;
  using Elt = typename F::Elt;
  static constexpr bool kCarrier = false;
  static constexpr bool kNative = false;
  static constexpr bool kOk = true;

  static Scalar scalar(const Elt &x) { return x; }
  static const Base &base(const F &f) { return f; }
  // The element of exact order ORDER (a power of two up to 2^kLog).
  static std::optional<Elt> root(const F &f, size_t order) {
    if (order < 2 || !ntt_detail::power_of_two(order)) return std::nullopt;
    size_t log = 0;
    while ((size_t{1} << log) < order) ++log;
    if (log > PrimeRoot<F>::kLog) return std::nullopt;
    Elt r = f.of_string(PrimeRoot<F>::kRoot);
    for (size_t l = PrimeRoot<F>::kLog; l > log; --l) r = f.mulf(r, r);
    return r;
  }
  static std::optional<Elt> scheme_psi(const F &f, size_t n) {
    if (n < 2 || !ntt_detail::power_of_two(n)) return std::nullopt;
    return root(f, 2 * n);
  }
};
template <class F>
constexpr bool kFieldNtt = FieldNtt<F>::kOk;

// One negacyclic transform of length n with root psi (psi^n = -1), its
// spectrum order the one above. Pointwise products take a spectrum either in
// the base field (Scalar: a public polynomial over F_q or the carrier's base
// field, the common case) or in F.
template <class F>
class NegacyclicNtt {
  static_assert(kFieldNtt<F>, "NegacyclicNtt: the field has no transform");
  using T = FieldNtt<F>;

 public:
  using Elt = typename F::Elt;
  using Scalar = typename T::Scalar;
  using Base = typename T::Base;

  NegacyclicNtt(const F &f, size_t n, const Elt &psi)
      : f_(f), n_(n), psi_(psi), plan_(f, n, psi) {
    check(f.in_subfield(psi), "NegacyclicNtt: psi in the base field");
  }
  const F &field() const { return f_; }
  size_t n() const { return n_; }
  const Elt &psi() const { return psi_; }
  // Same transform: equal length and root.
  bool same(const NegacyclicNtt &o) const {
    return n_ == o.n_ && psi_ == o.psi_;
  }

  void forward(std::vector<Elt> &a) const { plan_.transform(a, false); }
  void inverse(std::vector<Elt> &a) const { plan_.transform(a, true); }

  // The spectrum of a polynomial of base-field coefficients, computed in the
  // base field; nothing when a coefficient lies outside it.
  std::optional<std::vector<Scalar>> base_spectrum(const Elt *h) const {
    std::vector<Scalar> s(n_);
    for (size_t i = 0; i < n_; ++i) {
      if (!f_.in_subfield(h[i])) return std::nullopt;
      s[i] = T::scalar(h[i]);
    }
    base_plan().transform(s, false);
    return s;
  }
  std::vector<Elt> spectrum(const Elt *h) const {
    std::vector<Elt> s(h, h + n_);
    forward(s);
    return s;
  }

 private:
  const host_ntt::NegacyclicPlan<Base> &base_plan() const {
    if (!base_) {
      base_ = std::make_shared<host_ntt::NegacyclicPlan<Base>>(
          T::base(f_), n_, T::scalar(psi_));
    }
    return *base_;
  }
  const F &f_;
  size_t n_;
  Elt psi_;
  host_ntt::NegacyclicPlan<F> plan_;
  mutable std::shared_ptr<host_ntt::NegacyclicPlan<Base>> base_;
};

// A kernel spectrum: base-field scalars when every entry lies in the base
// field, field elements otherwise. at(k) multiplies x by entry k.
template <class F>
struct KernelSpectrum {
  using Elt = typename F::Elt;
  using Scalar = typename FieldNtt<F>::Scalar;
  std::vector<Scalar> base;
  std::vector<Elt> full;
  bool is_base() const { return !base.empty(); }
  // y += sign * s[k] * x, with s read at index k (or n - 1 - k for the
  // adjoint, whose spectrum is the index reversal: in the order above,
  // a*(x) = a(x^-1) sends frequency k to n - 1 - k, as native_linear reads
  // its kNtt operands).
  void mul_add(const F &f, const Elt *x, Elt *y, size_t n, bool adjoint) const {
    if (is_base()) {
      for (size_t k = 0; k < n; ++k)
        f.add(y[k], f.mulf(x[k], base[adjoint ? n - 1 - k : k]));
    } else {
      for (size_t k = 0; k < n; ++k)
        f.add(y[k], f.mulf(x[k], full[adjoint ? n - 1 - k : k]));
    }
  }
  static KernelSpectrum of(const NegacyclicNtt<F> &ntt, const Elt *h,
                           Form form) {
    KernelSpectrum s;
    const size_t n = ntt.n();
    if (form == Form::kNtt) {
      const F &f = ntt.field();
      bool base = true;
      for (size_t k = 0; k < n && base; ++k) base = f.in_subfield(h[k]);
      if (base) {
        s.base.resize(n);
        for (size_t k = 0; k < n; ++k) s.base[k] = FieldNtt<F>::scalar(h[k]);
      } else {
        s.full.assign(h, h + n);
      }
      return s;
    }
    if (auto b = ntt.base_spectrum(h)) {
      s.base = std::move(*b);
    } else {
      s.full = ntt.spectrum(h);
    }
    return s;
  }
};

// Bit reversal of WIDTH bits.
inline size_t ntt_brv(size_t x, size_t width) {
  size_t y = 0;
  for (size_t i = 0; i < width; ++i, x >>= 1) y = (y << 1) | (x & 1);
  return y;
}
inline size_t ntt_log2(size_t n) {
  size_t l = 0;
  while ((size_t{1} << l) < n) ++l;
  return l;
}

}  // namespace proofs::gordiehowe::ops

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_NTT_H_
