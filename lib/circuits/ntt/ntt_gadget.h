// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// In-circuit radix-2 NTT over Logic's public arithmetic interface.
//
// Every butterfly multiplies by a compile-time twiddle, so the transform is
// affine: it adds wires and circuit layers but no quadratic constraints.  A
// length-n product therefore costs n pointwise multiplications plus affine
// work, against n^2 for schoolbook convolution.  That matters when both
// operands are committed, as in a ring signature where the public key is
// private; when one operand is public the relation is linear in the committed
// witness and Ligero's row interface discharges it without any transform.
//
// The sharing masks preserve a stage's outputs with axpy(0,1,x), a derived
// wire that breaks the affine chain.  They trade circuit depth against width
// and change no value.
#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_NTT_GADGET_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_NTT_GADGET_H_
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>
#include "util/panic.h"

namespace proofs::ntt_gadget {
enum class Order { Natural, BitReversed };

// Bit s requests sharing after butterfly stage s (zero based).
// Masks concern circuit representation only; they do not change the transform.
struct Sharing {
  uint64_t forward = 36;  // literal masks only mean something at one length
  uint64_t inverse = 0;
  bool before_inverse = true;
  Order spectrum_order = Order::Natural;
};

// Boundaries every `period` stages of a length-n transform.
//
// Without boundaries the compiler folds the whole butterfly network back into
// the layer that consumes it, and the transform costs n^2 terms rather than
// n log n.  With boundaries every k stages each segment flattens to a 2^k-dense
// map, so terms run about (stages/k)*n*2^k plus the per-boundary overhead.
// Small k minimizes the first part and inflates the second; period 2 measured
// best at n=512 (22,021 terms against 24,073 for every stage and 27,139 for
// every third).  Terms are a proxy for prover time, so sweep before trusting
// a period in a complete circuit.
inline uint64_t stage_mask(size_t n, size_t period = 2) {
  check(n >= 2 && (n & (n - 1)) == 0, "NTT length must be a power of two");
  check(period >= 1, "sharing period must be positive");
  size_t levels = 0;
  for (size_t m = n; m > 1; m >>= 1) ++levels;
  uint64_t mask = 0;
  for (size_t s = 0; s < levels; s += period) mask |= uint64_t{1} << s;
  return mask;
}

template <class LC>
auto share(const LC& lc, const typename LC::EltW& x) {
  // CompilerBackend::axpy uses QuadCircuit::linear, preserving the operand.
  // EvaluationBackend simply evaluates the same identity.
  return lc.axpy(lc.konst(uint64_t{0}), lc.f_.one(), x);
}
template <class LC>
void share_all(const LC& lc, std::vector<typename LC::EltW>& a) {
  for (auto& x : a) x = share(lc, x);
}
inline size_t reverse_bits(size_t x, size_t width) {
  size_t y = 0;
  for (size_t i = 0; i < width; ++i, x >>= 1) y = (y << 1) | (x & 1);
  return y;
}
template <class F>
auto power(const F& f, typename F::Elt x, size_t n) {
  auto y = f.one();
  for (; n; n >>= 1, x = f.mulf(x, x))
    if (n & 1) y = f.mulf(y, x);
  return y;
}

// Caller supplies a primitive n-th root omega. A nonzero twist psi optionally
// gives a negacyclic transform: psi^2=omega and psi^n=-1. Zero means cyclic.
// Forward input and inverse output are natural-order coefficient vectors.
// Both transforms use the selected frequency order, so convolution needs no
// permutation between forward transforms, products, and inverse.
template <class LC>
void transform(const LC& lc, std::vector<typename LC::EltW>& a,
               typename LC::Elt omega, bool inverse, const Sharing& sharing,
               typename LC::Elt psi) {
  const auto& f = lc.f_;
  const size_t n = a.size();
  check(n >= 2 && (n & (n - 1)) == 0, "NTT length must be a power of two");
  check(power(f, omega, n) == f.one() &&
        power(f, omega, n / 2) == f.mone(), "NTT primitive root");
  size_t levels = 0;
  for (size_t m = n; m > 1; m >>= 1) ++levels;
  check(levels < 64, "NTT sharing mask capacity");
  const uint64_t mask = inverse ? sharing.inverse : sharing.forward;
  check((mask >> levels) == 0, "sharing boundary outside NTT");
  const bool twisted = psi != f.zero();
  if (twisted) {
    check(f.mulf(psi, psi) == omega && power(f, psi, n) == f.mone(),
          "NTT negacyclic twist");
    if (!inverse) {
      auto w = f.one();
      for (auto& x : a) { x = lc.mul(w, x); w = f.mulf(w, psi); }
    }
  }
  if (inverse && sharing.before_inverse) share_all(lc, a);
  if (inverse) omega = f.invertf(omega);
  if (sharing.spectrum_order == Order::Natural) {
    for (size_t i = 0; i < n; ++i) {
      const size_t j = reverse_bits(i, levels);
      if (i < j) std::swap(a[i], a[j]);
    }
    size_t stage = 0;
    for (size_t len = 2; len <= n; len *= 2, ++stage) {
      const auto step = power(f, omega, n / len);
      auto w = f.one();
      for (size_t j = 0; j < len / 2; ++j) {
        for (size_t start = 0; start < n; start += len) {
          const auto u = a[start + j];
          const auto v = lc.mul(w, a[start + j + len / 2]);
          a[start + j] = lc.add(u, v);
          a[start + j + len / 2] = lc.sub(u, v);
        }
        w = f.mulf(w, step);
      }
      if (mask & (uint64_t{1} << stage)) share_all(lc, a);
    }
  } else if (!inverse) {
    size_t stage = 0;
    for (size_t length = n / 2; length; length /= 2, ++stage) {
      for (size_t start = 0; start < n; start += 2 * length) {
        const auto w = power(f, omega,
            reverse_bits(start / (2 * length), stage) * length);
        for (size_t j = start; j < start + length; ++j) {
          const auto u = a[j], v = lc.mul(w, a[j + length]);
          a[j] = lc.add(u, v);
          a[j + length] = lc.sub(u, v);
        }
      }
      if (mask & (uint64_t{1} << stage)) share_all(lc, a);
    }
  } else {
    size_t stage = 0;
    for (size_t length = 1; length < n; length *= 2, ++stage) {
      for (size_t start = 0; start < n; start += 2 * length) {
        const auto w = power(f, omega,
            reverse_bits(start / (2 * length), levels - 1 - stage) * length);
        for (size_t j = start; j < start + length; ++j) {
          const auto u = a[j], v = a[j + length];
          a[j] = lc.add(u, v);
          a[j + length] = lc.mul(w, lc.sub(u, v));
        }
      }
      if (mask & (uint64_t{1} << stage)) share_all(lc, a);
    }
  }
  if (inverse) {
    auto scale = f.invertf(f.of_scalar(n));
    const auto step = twisted ? f.invertf(psi) : f.one();
    for (auto& x : a) { x = lc.mul(scale, x); scale = f.mulf(scale, step); }
  }
}
}  // namespace proofs::ntt_gadget
#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_NTT_GADGET_H_
