// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The emulated arms' proof field, and the field-generic helpers their gadgets
// and hosts use.
//
// The emulated arms run over the Goldilocks extension F_{p^2},
// p = 2^64 - 2^32 + 1, with witness rows in F_p.  Mod-q arithmetic is emulated
// with bounded quotients, so every such integer identity must stay below the
// characteristic: field_integer_bits<F>() is the bound to check against.

#ifndef LFB_FALCON_PQ_EMULATED_FIELD_H_
#define LFB_FALCON_PQ_EMULATED_FIELD_H_

#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <vector>

#include "fp_goldilocks.h"
#include "util/panic.h"

namespace proofs {

using EmulatedField = Fp64G2;

namespace pq_field_detail {
template <class F, class = void>
struct HasIntegerBits : std::false_type {};
template <class F>
struct HasIntegerBits<F, std::void_t<decltype(F::kIntegerBits)>>
    : std::true_type {};
template <class F, class = void>
struct HasToU64 : std::false_type {};
template <class F>
struct HasToU64<F, std::void_t<decltype(std::declval<const F&>().to_u64(
                       std::declval<const typename F::Elt&>()))>>
    : std::true_type {};
}  // namespace pq_field_detail

// Largest b such that every integer below 2^b is below the characteristic.
template <class F>
constexpr size_t field_integer_bits() {
  if constexpr (pq_field_detail::HasIntegerBits<F>::value) {
    return F::kIntegerBits;
  } else {
    return F::kBits - 1;
  }
}

// The canonical integer of a field element known to be below 2^64.
template <class F>
uint64_t field_u64(const F& f, const typename F::Elt& e) {
  if constexpr (pq_field_detail::HasToU64<F>::value) {
    return f.to_u64(e);
  } else {
    auto arr = f.from_montgomery(e).u64();
    for (size_t i = 1; i < arr.size(); ++i) check(arr[i] == 0, "field_u64: value exceeds 2^64");
    return arr[0];
  }
}

// The canonical integer of a field element, as little-endian 64-bit limbs.
template <class F>
std::vector<uint64_t> field_u64_limbs(const F& f, const typename F::Elt& e) {
  if constexpr (pq_field_detail::HasToU64<F>::value) {
    return {f.to_u64(e)};
  } else {
    auto arr = f.from_montgomery(e).u64();
    return std::vector<uint64_t>(arr.begin(), arr.end());
  }
}

// Checks that an integer identity whose sides stay below 2^log2_bound holds
// exactly in F.
template <class F>
void check_integer_identity(double log2_bound, const char* what) {
  check(log2_bound < (double)field_integer_bits<F>(), what);
}

// The field element of a signed integer below 2^127 in magnitude.
template <class F>
typename F::Elt field_of_i128(const F& f, __int128_t v) {
  const bool neg = v < 0;
  __uint128_t m = neg ? (__uint128_t)(-v) : (__uint128_t)v;
  const typename F::Elt r32 = f.of_scalar(uint64_t{1} << 32);
  typename F::Elt e = f.zero();
  uint64_t d32[4] = {0, 0, 0, 0};
  size_t nd = 0;
  while (m != 0) {
    d32[nd++] = (uint64_t)(m & 0xffffffffu);
    m >>= 32;
  }
  for (size_t i = nd; i-- > 0;) e = f.addf(f.mulf(e, r32), f.of_scalar(d32[i]));
  return neg ? f.negf(e) : e;
}

}  // namespace proofs

#endif  // LFB_FALCON_PQ_EMULATED_FIELD_H_
