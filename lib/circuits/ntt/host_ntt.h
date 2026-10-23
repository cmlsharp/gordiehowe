// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_HOST_NTT_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_HOST_NTT_H_
#include "algebra/fp14_8.h"
#include "algebra/fp14_n.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp_native_wide.h"
#include "algebra/fp24_6.h"
#include "util/log.h"
#include <utility>
#include <vector>

namespace proofs::host_ntt {
// Twiddles in native extension fields belong to the base field, even when
// the transformed vectors (in particular Ligero row weights) do not.
template <class F> auto twiddle(const F &, typename F::Elt x) { return x; }
inline auto twiddle(const Fp24_6 &f, Fp24_6::Elt x) {
  check(f.in_subfield(x), "NTT twiddle must be in base field");
  return x.e[0];
}
inline auto twiddle(const Fp14_8 &f, Fp14_8::Elt x) {
  check(f.in_subfield(x), "NTT twiddle must be in base field");
  return x.e[0];
}
template <size_t D, uint32_t B>
auto twiddle(const Fp14_N<D, B> &f, typename Fp14_N<D, B>::Elt x) {
  check(f.in_subfield(x), "NTT twiddle must be in base field");
  return x.e[0];
}
inline auto twiddle(const Fp64G4 &f, Fp64G4::Elt x) {
 check(f.in_subfield(x), "scalar NTT twiddle"); return x.e[0];
}
template <class B, size_t D, uint32_t Beta, uint32_t Linear, bool Delayed,
          NativeConvolution Kernel, bool Tower>
auto twiddle(const NativeWide<B, D, Beta, Linear, Delayed, Kernel, Tower>& f,
             typename NativeWide<B, D, Beta, Linear, Delayed, Kernel, Tower>::Elt x) {
  check(f.in_subfield(x),"native scalar twiddle");return x.e[0];
}
template <class F> class Plan {
public:
  using E = typename F::Elt;
  using T = decltype(twiddle(std::declval<const F &>(), std::declval<E>()));
  const F &f;
  size_t n;
  std::vector<T> roots, iroots;
  T ni;
  Plan(const F &field, size_t count, E root)
      : f(field), n(count), ni(twiddle(f, f.invertf(f.of_scalar(n)))) {
    check(n >= 2 && !(n & (n - 1)), "host NTT size");
    auto r = twiddle(f, root), ir = twiddle(f, f.invertf(root));
    auto x = f.one(), y = f.one();
    roots.reserve(n / 2);
    iroots.reserve(n / 2);
    for (size_t i = 0; i < n / 2; ++i) {
      roots.push_back(twiddle(f, x));
      iroots.push_back(twiddle(f, y));
      x = f.mulf(x, r);
      y = f.mulf(y, ir);
    }
    check(x == f.mone(), "host NTT primitive root");
  }
  // Forward DIF emits bit-reversed frequencies; inverse DIT consumes that
  // ordering. Pointwise products need no permutation between the two.
  void transform(std::vector<E> &a, bool inverse, bool normalize = true) const {
    check(a.size() == n, "host NTT operand size");
    if (!inverse) {
      for (size_t len = n; len >= 2; len /= 2)
        for (size_t start = 0; start < n; start += len) {
          auto u = a[start], v = a[start + len / 2];
          a[start] = f.addf(u, v);
          a[start + len / 2] = f.subf(u, v);
          for (size_t j = 1; j < len / 2; ++j) {
            u = a[start + j];
            v = a[start + j + len / 2];
            a[start + j] = f.addf(u, v);
            a[start + j + len / 2] = f.mulf(f.subf(u, v), roots[j * n / len]);
          }
        }
    } else {
      for (size_t len = 2; len <= n; len *= 2)
        for (size_t start = 0; start < n; start += len) {
          auto u = a[start], v = a[start + len / 2];
          a[start] = f.addf(u, v);
          a[start + len / 2] = f.subf(u, v);
          for (size_t j = 1; j < len / 2; ++j) {
            u = a[start + j];
            v = f.mulf(a[start + j + len / 2], iroots[j * n / len]);
            a[start + j] = f.addf(u, v);
            a[start + j + len / 2] = f.subf(u, v);
          }
        }
      if (normalize)
        for (auto &x : a)
          x = f.mulf(x, ni);
    }
  }
};

// Negacyclic convolution modulo X^n + 1: twist by a primitive 2n-th root,
// apply a cyclic NTT, then untwist after the inverse transform.
template <class F> class NegacyclicPlan {
public:
  using E = typename F::Elt;
  using T = typename Plan<F>::T;
  const F &f;
  Plan<F> cyclic;
  std::vector<T> twist, inverse_twist;

  NegacyclicPlan(const F &field, size_t n, E root)
      : f(field), cyclic(f, n, f.mulf(root, root)) {
    const auto r = twiddle(f, root), ir = twiddle(f, f.invertf(root));
    auto x = f.one(), y = f.invertf(f.of_scalar(n));
    for (size_t i = 0; i < n; ++i) {
      twist.push_back(twiddle(f, x));
      inverse_twist.push_back(twiddle(f, y));
      x = f.mulf(x, r);
      y = f.mulf(y, ir);
    }
    check(x == f.mone(), "negacyclic NTT primitive root");
  }

  void transform(std::vector<E> &a, bool inverse) const {
    check(a.size() == twist.size(), "negacyclic NTT operand size");
    if (!inverse)
      for (size_t i = 1; i < a.size(); ++i)
        a[i] = f.mulf(a[i], twist[i]);
    cyclic.transform(a, inverse, false);
    if (inverse)
      for (size_t i = 0; i < a.size(); ++i)
        a[i] = f.mulf(a[i], inverse_twist[i]);
  }
};
} // namespace proofs::host_ntt
#endif
