// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: range requests to lookups.
//
// The range lowering of a domain D collects its requests (the
// application's and the MAC equality's), selects one realization per
// request with a planner that searches the subsets of the domain's
// candidate tables for the least cost under the domain's cost model
// (RangeCosts; paper sec. rand-planning, appendix range-candidates) and
// does not depend on the order of the requests, and emits the
// realizations' digits
// and needles, one histogram per table and phase class, the challenge alpha
// and one fraction-tree circuit per table:
//
//   range.<name>.d<j>, .h<j>   digits (advice, deps == {v})
//   range.<name>.needle        an expression needle (derive)
//   range.static:<D>.<T>       m0, counts of the phase-0 needles
//   range.dynamic:<D>.<T>      m1, counts of the late needles (late)
//   alpha:<D>                  alpha, tests every needle and histogram;
//                              uniform outside [0, T_max), the largest
//                              table; the assert_in lowering
//                              (compiler/assert_in.h) declares it when the
//                              domain has an assert_in table
//   range.weights:<D>.<T>      w_j = (alpha - j)^-1
//   range.lookup:<D>.<T>       N = D * (sum m0_j w_j + sum m1_j w_j)
//
// A table whose needles exceed the group capacity (RangePolicy) is split
// into groups <D>.<T>.g<k>, each with its histograms and fraction tree,
// sharing alpha and the weights. A group with static and late needles
// takes one late histogram of T counts when that is cheaper than m0 and
// m1. Requests a value's type bounds (a Bit, a prime-field value below
// n >= p), duplicates and requests a stricter one on the same value bounds
// cost nothing; Bit values bound their terms in interval propagation, and
// the complement realization reads one needle n - 1 - v.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_RANGE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_RANGE_H_

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/certify.h"
#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/compiler/compile_times.h"
#include "gordiehowe/compiler/derivation.h"
#include "gordiehowe/compiler/log_derivative.h"
#include "gordiehowe/compiler/placement_rates.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {

namespace range_internal {

// The quad terms of the fraction tree (log_derivative.h) per needle and
// per table row in the compiled circuit, at the margin
// (gordiehowe_mod_test's FractionTreeTermsPerNeedleAndRow): a needle's leaf
// alpha - v and its share of the tree's products N_l D_r, N_r D_l and
// D_l D_r; a row's product m_j w_j in the sum.
inline constexpr Bound kNeedleTerms = 6;
inline constexpr Bound kRowTerms = 1;

// The planner's cost model (paper, fig. table-choice): the objective is
// c_T times the rows of the tables opened plus, for each request, the cost
// of its realization's committed digits and lookups over its coordinates.
// Under the domain's measured rates (placement_rates.h), in integer units
// of 10^-6 us of commit + prove + verify, so that sums are exact and equal
// costs tie: a committed coordinate (a digit) costs the commit rate of the
// domain's range values (commit_sub, or commit_full when the field is
// prime); a needle its kNeedleTerms quad terms at gkr_term; a table row
// its committed count at the commit rate and its kRowTerms quad terms at
// gkr_term (its weight is public, computed by the verifier: no committed
// coordinate and no term of its own). Without measured rates every
// committed coordinate, needle and row costs 1.
struct RangeCosts {
  Bound coord = 1, needle = 1, row = 1;
  bool measured = false;
};
inline constexpr double kRangeUnitsPerUs = 1e6;
inline Bound range_units(double us) {
  return Bound(std::llround(us * kRangeUnitsPerUs));
}
inline RangeCosts range_costs(const PlacementRates &rates, bool sub) {
  RangeCosts c;
  if (!rates.measured()) return c;
  const double commit = sub ? rates.commit_sub : rates.commit_full;
  c.coord = range_units(commit);
  c.needle = range_units(double(kNeedleTerms) * rates.gkr_term);
  c.row = range_units(commit + double(kRowTerms) * rates.gkr_term);
  c.measured = true;
  return c;
}

// One realization of one request in one table: its cost per coordinate
// (needles and net new coordinates under RangeCosts), its total over the
// request's coordinates, and its rank in the policy's kind order. Sorted
// by total, then kind rank, then the smaller table, then fewer digits.
struct Candidate {
  RangeRealization r;
  size_t kind_rank = 0;
  Bound cost = 0, total = 0;
  bool operator<(const Candidate &o) const {
    if (total != o.total) return total < o.total;
    if (kind_rank != o.kind_rank) return kind_rank < o.kind_rank;
    if (r.table != o.r.table) return r.table < o.r.table;
    return r.k < o.r.k;
  }
};

inline double log2_bound(Bound x) {
  return std::log2(static_cast<double>(x));
}

// Whether X is a point of the range table [0, T) of an odd field: an
// element of the prime field whose canonical integer is below T. O(1): the
// membership test of the prime field and its bytes. X is public (a
// challenge), so the test may branch on it.
template <class F>
bool in_range_table(const F &f, const typename F::Elt &x, Bound T) {
  if (!subfield_contains(f, x)) return false;
  uint8_t b[domain_subfield<F>::kBytes];
  subfield_to_bytes(f, b, x);
  Bound r = 0;
  for (size_t i = domain_subfield<F>::kBytes; i-- > 0;) {
    if (i >= 16) {
      if (b[i] != 0) return false;
      continue;
    }
    r = (r << 8) | b[i];
  }
  return r < T;
}

// Division by a public D of the canonical integers (NatInt, witness values)
// of a field of characteristic P (every dividend below P, P a NatInt: the
// characteristic or its floor 2^127), with the same instructions for
// every dividend (ct.h): by D's reciprocal (ct::Divisor64) when P <= 2^64,
// ct::divmod's fixed-step 128-bit division otherwise. The choice reads only
// D and P.
class PublicDivisor {
 public:
  PublicDivisor(NatInt d, NatInt p)
      : d_(d),
        small_(p != 0 && p <= (NatInt(1) << 64) && d < (NatInt(1) << 64)),
        dv_(small_ ? uint64_t(d) : 1) {}
  PublicDivisor(const Bound &d, const Bound &p)
      : PublicDivisor(nat_cast(d), nat_modulus(p)) {}
  ct::DivMod divmod(NatInt a) const {
    if (small_) return dv_.divmod(uint64_t(a));
    return ct::divmod(a, d_);
  }
  NatInt d() const { return d_; }

 private:
  NatInt d_;
  bool small_;
  ct::Divisor64 dv_;
};

// Digit J in base T of A, or of (TOP - A) mod P when TOP is set, with the
// same instructions for every A (ct.h): shifts and a mask for a
// power-of-two T, PublicDivisor's division by T (DIV, of T and P)
// otherwise. T, J, TOP and P are public.
inline NatInt digit(NatInt a, unsigned j, const PublicDivisor &div,
                 std::optional<NatInt> top, NatInt p) {
  const NatInt T = div.d();
  if (top) a = ct::sub_mod(*top, a, p);
  if ((T & (T - 1)) == 0) {
    unsigned lg = 0;
    while ((NatInt(1) << lg) < T) ++lg;
    if (NatInt(lg) * j >= 128) return 0;
    return (a >> (lg * j)) & (T - 1);
  }
  for (unsigned s = 0; s < j; ++s) a = div.divmod(a).q;
  return div.divmod(a).r;
}
inline NatInt digit(NatInt a, unsigned j, NatInt T, std::optional<NatInt> top, NatInt p) {
  return digit(a, j, PublicDivisor(T, p), top, p);
}

// The counts of buckets J0 .. J0 + R L - 1, R vectors of L lanes of T,
// over the keys KEYS[C0 .. C1).
template <size_t kR, class V, class T, class K>
void count_block(const std::vector<K> &keys, size_t c0, size_t c1, size_t j0,
                 std::vector<uint32_t> &count) {
  constexpr size_t kL = sizeof(V) / sizeof(T);
  V acc[kR], jv[kR];
  for (size_t r = 0; r < kR; ++r) {
    acc[r] = V{};
    for (size_t t = 0; t < kL; ++t) jv[r][t] = T(j0 + r * kL + t);
  }
  for (size_t i = c0; i < c1; ++i) {
    const V k = V{} + T(keys[i]);
    for (size_t r = 0; r < kR; ++r) acc[r] -= (V)(jv[r] == k);
  }
  for (size_t r = 0; r < kR; ++r)
    for (size_t t = 0; t < kL; ++t) count[j0 + r * kL + t] += acc[r][t];
}
// COUNT[j] += #{i : KEYS[i] = j} for every bucket j, oblivious: each
// block of buckets takes one pass over every key, comparing it with the
// block's buckets lane by lane (vector extensions), so no address and no
// branch depends on a key. 16-bit lanes (32 buckets a vector) while the
// buckets are below 2^16, the keys in chunks of 2^16 - 1 so no lane
// overflows; 32-bit lanes otherwise. A block is four vectors, then one
// for the buckets left.
inline void count_keys(const std::vector<uint32_t> &keys,
                       std::vector<uint32_t> &count) {
  typedef uint16_t V16 __attribute__((vector_size(64)));
  typedef uint32_t V32 __attribute__((vector_size(64)));
  // vectors per pass, then single vectors for the rest
  constexpr size_t kR = 4;
  const size_t n = count.size();
  size_t j0 = 0;
  if (n <= 65535) {
    constexpr size_t kL = 32;
    std::vector<uint16_t> k16(keys.size());
    for (size_t i = 0; i < keys.size(); ++i) k16[i] = uint16_t(keys[i]);
    auto chunks = [&](auto pass) {
      for (size_t c0 = 0; c0 < k16.size(); c0 += 65535)
        pass(c0, std::min(k16.size(), c0 + 65535));
    };
    for (; j0 + kR * kL <= n; j0 += kR * kL)
      chunks([&](size_t c0, size_t c1) {
        count_block<kR, V16, uint16_t>(k16, c0, c1, j0, count);
      });
    for (; j0 + kL <= n; j0 += kL)
      chunks([&](size_t c0, size_t c1) {
        count_block<1, V16, uint16_t>(k16, c0, c1, j0, count);
      });
  } else {
    constexpr size_t kL = 16;
    for (; j0 + kR * kL <= n; j0 += kR * kL)
      count_block<kR, V32, uint32_t>(keys, 0, keys.size(), j0, count);
    for (; j0 + kL <= n; j0 += kL)
      count_block<1, V32, uint32_t>(keys, 0, keys.size(), j0, count);
  }
  // The last buckets, one at a time.
  for (; j0 < n; ++j0)
    for (uint32_t key : keys) count[j0] += uint32_t(key == j0);
}

// The histogram over [0, SIZE) (SIZE < 2^32) of the canonical values of
// the needles IN, oblivious (ct.h): every needle adds its 0/1 match to
// every bucket (count_keys), so no address depends on a needle. A needle
// outside the prime field or not below SIZE matches no bucket.
template <class F>
std::vector<typename F::Elt> histogram(
    const F &f, Bound size,
    const std::vector<const std::vector<typename F::Elt> *> &in) {
  const uint32_t n = static_cast<uint32_t>(size);
  std::vector<uint32_t> keys;
  for (const auto *v : in)
    for (const auto &e : *v) {
      uint64_t ok = 1;
      const NatInt a = nat_of_ct(f, e, ok);
      ok &= ct::lt128(a, nat_cast(size));
      // n (no bucket) unless the needle is a canonical value below SIZE.
      keys.push_back(
          uint32_t(ct::select(ct::mask(ok), uint64_t(a), uint64_t(n))));
    }
  std::vector<uint32_t> count(n, 0);
  count_keys(keys, count);
  std::vector<typename F::Elt> out(count.size());
  for (size_t j = 0; j < count.size(); ++j)
    out[j] = f.of_scalar(uint64_t(count[j]));
  return out;
}

// A signed integer interval [lo, hi].
using Interval = std::pair<SignedInt, SignedInt>;

// The cap of interval propagation (core.h's kBoundCapBits): an interval
// or coefficient beyond 2^kIntervalCapBits bounds nothing. Every
// characteristic in use lies below it, so [0, p - 1] is always an
// interval.
inline constexpr unsigned kIntervalCapBits = kBoundCapBits;

// X as a signed integer when X < 2^CAP_BITS, or none.
inline std::optional<SignedInt> int_below(const Bound &x, unsigned cap_bits) {
  if (x >= Bound::pow2(cap_bits)) return std::nullopt;
  return SignedInt(x);
}

// [LO, HI], or a CompileError when LO > HI. Interval propagation builds no
// inverted interval; a no-wrap check over one would accept values that
// wrap around p. WHAT names the expression.
inline Interval ordered_interval(SignedInt lo, SignedInt hi,
                                 const std::string &what) {
  if (lo > hi)
    fail("interval propagation built the inverted interval [" + int_str(lo) +
         ", " + int_str(hi) + "] for " + what);
  return Interval{lo, hi};
}

// The signed integer representative of a prime-field element of F (P its
// characteristic; PRIME_FIELD when F is itself prime), or none when the element lies
// outside the prime field. Under a wide prime the representative is x or
// -x for the canonical integer x of a or of -a, whichever is at most
// (P - 1) / 2, and none when neither is.
template <class F>
std::optional<std::pair<bool, Bound>> signed_rep(const F &f, Bound p,
                                                 bool prime_field,
                                                 const typename F::Elt &a) {
  if (!prime_field && !subfield_contains(f, a)) return std::nullopt;
  if (characteristic_wide(f)) {
    // A public element: its exact canonical integer, or its negation's.
    const Bound x = nat_of(f, a);
    if (x <= (p - 1) / 2) return std::make_pair(false, x);
    const Bound y = nat_of(f, f.negf(a));
    if (y <= (p - 1) / 2) return std::make_pair(true, y);
    return std::nullopt;
  }
  const Bound x = nat_of(f, a);
  if (x <= (p - 1) / 2) return std::make_pair(false, x);
  return std::make_pair(true, p - x);
}

// The integer interval of the affine expression E over every coordinate
// (interval propagation, shared by the range and modular lowerings). A term
// a op_k(...op_1(x)) starts from the interval of node x, BOUND_OF(x): an
// exclusive bound N_x (x in [0, N_x - 1]) or a signed interval. Each
// operator maps [lo, hi] to [min(lo, 0) r, max(hi, 0) r] for a nonnegative
// integer matrix with row sum r (OpSpec::row_sum), and to [-m s, m s] with
// m = max(-lo, hi) for a signed one whose rows' absolute values sum to s
// (OpSpec::abs_row_sum); then a's signed representative scales it. A
// constant node contributes its values exactly. A node with no bound, an
// operator without a row bound, a coefficient outside the prime field, or
// an interval beyond 2^CAP_BITS leaves the expression unbounded (none,
// with WHY). IN_PRIME, when given, names the nodes whose values lie in the
// prime field: such a node without a bound has [0, p - 1], p the field's
// characteristic. An
// inverted interval fails compilation.
template <class F, class BoundOf>
std::optional<Interval> lin_interval(
    const F &f, Bound p, bool prime_field, const Graph &g, const Lin<F> &e,
    BoundOf bound_of, std::string &why,
    const std::function<bool(size_t)> *in_prime = nullptr,
    unsigned cap_bits = kIntervalCapBits) {
  const auto &N = g.nodes;
  const SignedInt kCap = SignedInt(1) << cap_bits;
  SignedInt lo = 0, hi = 0;
  std::vector<SignedInt> c(e.n, 0);
  for (const auto &t : e.terms) {
    const Node &n = N.at(t.node);
    const auto a = signed_rep(f, p, prime_field, t.scale);
    if (!a) {
      why = "the coefficient of '" + n.name + "' lies outside the prime field";
      return std::nullopt;
    }
    if (a->second >= Bound(kCap)) {
      why = "a coefficient exceeds 2^" + std::to_string(cap_bits);
      return std::nullopt;
    }
    const SignedInt sa = a->first ? -SignedInt(a->second) : SignedInt(a->second);
    if (n.kind == Kind::kConstant) {
      if (!t.chain.empty()) {
        why = "the constant '" + n.name + "' passes through an operator";
        return std::nullopt;
      }
      const auto v = g.system->template constant_values<F>(t.node);
      for (size_t j = 0; j < e.n; ++j) {
        const auto cj = signed_rep(f, p, prime_field, f.mulf(t.scale, v.at(j)));
        if (!cj) {
          why = "the constant '" + n.name + "' lies outside the prime field";
          return std::nullopt;
        }
        if (cj->second >= Bound(kCap)) {
          why = "a constant exceeds 2^" + std::to_string(cap_bits);
          return std::nullopt;
        }
        c[j] += cj->first ? -SignedInt(cj->second) : SignedInt(cj->second);
        if (c[j] >= kCap || c[j] <= -kCap) {
          why = "the constants exceed 2^" + std::to_string(cap_bits);
          return std::nullopt;
        }
      }
      continue;
    }
    // The node's interval: [0, N - 1] for an exclusive bound N, or the
    // signed interval BOUND_OF gives.
    SignedInt tlo = 0, thi = 0;
    {
      const auto b = bound_of(t.node);
      if (!b && in_prime != nullptr && (*in_prime)(t.node)) {
        // [0, p - 1] for p the characteristic itself: a wide prime's P is
        // only a floor.
        const std::optional<SignedInt> top =
            int_below(field_characteristic(f) - 1, cap_bits);
        if (!top) {
          why = "the term '" + n.name + "' is not range-checked, and its "
                "values in [0, p - 1] exceed 2^" + std::to_string(cap_bits);
          return std::nullopt;
        }
        thi = *top;
      } else if (!b) {
        why = "the term '" + n.name + "' is not range-checked";
        return std::nullopt;
      } else if constexpr (std::is_same_v<std::decay_t<decltype(*b)>,
                                          Interval>) {
        tlo = b->first;
        thi = b->second;
        if (tlo > thi)
          fail("interval propagation: the term '" + n.name +
               "' has the inverted interval [" + int_str(tlo) + ", " +
               int_str(thi) + "]");
      } else if (*b != 0) {
        // [0, N - 1], N - 1 compared with the cap in Bound.
        const auto top = int_below(*b - 1, cap_bits);
        if (!top) {
          why = "the interval exceeds 2^" + std::to_string(cap_bits);
          return std::nullopt;
        }
        thi = *top;
      }
      if (thi >= kCap || tlo <= -kCap) {
        why = "the interval exceeds 2^" + std::to_string(cap_bits);
        return std::nullopt;
      }
    }
    // X r with |X r| < 2^CAP_BITS, or none.
    auto times = [&](SignedInt x, Bound r) -> std::optional<SignedInt> {
      const SignedInt m = x < 0 ? -x : x;
      if (m == 0) return SignedInt(0);
      if (r > Bound(kCap / m)) return std::nullopt;
      return x * SignedInt(r);
    };
    for (const auto &op : t.chain) {
      std::optional<SignedInt> l, h;
      if (op->row_sum != 0) {
        l = times(std::min<SignedInt>(tlo, 0), op->row_sum);
        h = times(std::max<SignedInt>(thi, 0), op->row_sum);
      } else if (op->abs_row_sum != 0) {
        h = times(std::max<SignedInt>(-tlo, thi), op->abs_row_sum);
        if (h) l = -*h;
      } else {
        why = "the term '" + n.name + "' applies the operator '" + op->name +
              "', which bounds no row sum";
        return std::nullopt;
      }
      if (!l || !h) {
        why = "the interval exceeds 2^" + std::to_string(cap_bits);
        return std::nullopt;
      }
      tlo = *l;
      thi = *h;
    }
    // a [tlo, thi], checked: |a| max(|tlo|, |thi|) < 2^CAP_BITS.
    const auto l = times(tlo, a->second), h = times(thi, a->second);
    if (!l || !h) {
      why = "the interval exceeds 2^" + std::to_string(cap_bits);
      return std::nullopt;
    }
    lo += sa < 0 ? -*h : *l;
    hi += sa < 0 ? -*l : *h;
    if (hi >= kCap || lo <= -kCap) {
      why = "the interval exceeds 2^" + std::to_string(cap_bits);
      return std::nullopt;
    }
  }
  const auto [cmin, cmax] = std::minmax_element(c.begin(), c.end());
  return ordered_interval(lo + *cmin, hi + *cmax, "an affine expression");
}

// A short description of expression node X for compile errors: its
// leaves' node names, operators and convolutions.
template <class F>
std::string describe_term(const Graph &g, const ExprNode<F> &x,
                          size_t depth = 0) {
  if (depth > 4) return "...";
  auto kid = [&](size_t k) {
    return describe_term(g, *x.kids.at(k), depth + 1);
  };
  switch (x.op) {
    case ExprOp::kLin: {
      if (x.lin.terms.empty()) return "0";
      std::string out;
      for (size_t i = 0; i < x.lin.terms.size() && i < 3; ++i) {
        const auto &t = x.lin.terms[i];
        std::string nm = g.nodes.at(t.node).name;
        for (const auto &op : t.chain) nm = op->name + "(" + nm + ")";
        out += (i == 0 ? "" : " + ") + nm;
      }
      if (x.lin.terms.size() > 3) out += " + ...";
      return out;
    }
    case ExprOp::kConst:
      return "a constant";
    case ExprOp::kAdd:
      return kid(0) + " + " + kid(1);
    case ExprOp::kScale:
      return "k * (" + kid(0) + ")";
    case ExprOp::kMul:
      return "(" + kid(0) + ") * (" + kid(1) + ")";
    case ExprOp::kConv:
      return "conv(" + kid(0) + ", " + kid(1) + ")";
    case ExprOp::kApply:
      return x.apply->name + "(" + kid(0) + ")";
    case ExprOp::kGather:
      return "a view of " + kid(0);
    case ExprOp::kSum:
      return "sum(" + kid(0) + ")";
    case ExprOp::kBroadcast:
      return kid(0);
    default:
      return "a Logic gadget";
  }
}

// The integer interval of the expression E over every coordinate
// (interval propagation through products): affine leaves
// by lin_interval (an unbounded node of the prime field in [0, p - 1] when
// IN_PRIME names it), constants exactly, a + b, k a (k's signed
// representative), a b by the products of the endpoints, a sum of w
// coordinates w times its operand's (or, for a sum of an operand times a
// constant, each group's sum of the operand's interval times its
// constants), a view or broadcast its operands', an
// operator by its row bound (as lin_interval), conv(a, b) the sum of
// between 1 and min(la, lb) products (coefficient i sums x_u y_{i-u} over
// its terms), and a Bit [0, 1]. A coefficient outside the prime field, an
// operator without a row bound, a product of coordinates, or an interval
// beyond 2^CAP_BITS (lin_interval's cap) leaves E unbounded (none, with WHY
// naming the term).
template <class F, class BoundOf>
std::optional<Interval> expr_interval(
    const F &f, Bound p, bool prime_field, const Graph &g,
    const ExprPtr<F> &e, BoundOf bound_of, std::string &why,
    const std::function<bool(size_t)> *in_prime = nullptr,
    unsigned cap_bits = kIntervalCapBits) {
  const SignedInt kCap = SignedInt(1) << cap_bits;
  auto ok = [&](SignedInt x) { return x < kCap && x > -kCap; };
  // A B with |A B| < 2^CAP_BITS, or none.
  auto times = [&](SignedInt a, SignedInt b) -> std::optional<SignedInt> {
    const SignedInt ma = a < 0 ? -a : a;
    const SignedInt mb = b < 0 ? -b : b;
    if (ma != 0 && mb >= kCap / ma) return std::nullopt;
    return a * b;
  };
  auto signed_of = [&](const typename F::Elt &a) -> std::optional<SignedInt> {
    const auto r = signed_rep(f, p, prime_field, a);
    if (!r || r->second >= Bound(kCap)) return std::nullopt;
    return r->first ? -SignedInt(r->second) : SignedInt(r->second);
  };
  // The signed values of X per coordinate when X is a constant, or a view
  // or broadcast of one; none otherwise.
  std::function<std::optional<std::vector<SignedInt>>(const ExprNode<F> &)>
      const_values =
          [&](const ExprNode<F> &x) -> std::optional<std::vector<SignedInt>> {
    std::vector<SignedInt> v;
    if (x.op == ExprOp::kConst) {
      for (const auto &c : x.c) {
        const auto r = signed_of(c);
        if (!r) return std::nullopt;
        v.push_back(*r);
      }
      return v;
    }
    if ((x.op == ExprOp::kGather || x.op == ExprOp::kBroadcast) &&
        x.kids.size() == 1) {
      const auto k = const_values(*x.kids[0]);
      if (!k || k->empty()) return std::nullopt;
      if (x.op == ExprOp::kBroadcast) {
        for (size_t i = 0; i < x.n; ++i) v.push_back((*k)[i % k->size()]);
        return v;
      }
      for (size_t j : x.idx) {
        if (j >= k->size()) return std::nullopt;
        v.push_back((*k)[j]);
      }
      return v;
    }
    return std::nullopt;
  };
  std::map<const ExprNode<F> *, Interval> memo;
  std::function<std::optional<Interval>(const ExprNode<F> &)> go =
      [&](const ExprNode<F> &x) -> std::optional<Interval> {
    auto it = memo.find(&x);
    if (it != memo.end()) return it->second;
    auto wide = [&]() -> std::optional<Interval> {
      why = "the interval of '" + describe_term(g, x) + "' exceeds 2^" +
            std::to_string(cap_bits);
      return std::nullopt;
    };
    std::optional<Interval> out;
    switch (x.op) {
      case ExprOp::kLin: {
        if (x.lin.terms.empty()) {
          out = Interval{0, 0};
          break;
        }
        out = lin_interval(f, p, prime_field, g, x.lin, bound_of, why,
                           in_prime, cap_bits);
        if (!out) return std::nullopt;
        break;
      }
      case ExprOp::kConst: {
        SignedInt lo = 0, hi = 0;
        for (size_t i = 0; i < x.c.size(); ++i) {
          const auto c = signed_of(x.c[i]);
          if (!c) {
            why = "a constant lies outside the prime field";
            return std::nullopt;
          }
          if (i == 0 || *c < lo) lo = *c;
          if (i == 0 || *c > hi) hi = *c;
        }
        out = Interval{lo, hi};
        break;
      }
      case ExprOp::kAdd: {
        const auto a = go(*x.kids[0]);
        if (!a) return std::nullopt;
        const auto b = go(*x.kids[1]);
        if (!b) return std::nullopt;
        out = Interval{a->first + b->first, a->second + b->second};
        break;
      }
      case ExprOp::kScale: {
        const auto a = go(*x.kids[0]);
        if (!a) return std::nullopt;
        const auto k = signed_of(x.c.at(0));
        if (!k) {
          why = "the factor of '" + describe_term(g, *x.kids[0]) +
                "' lies outside the prime field";
          return std::nullopt;
        }
        const auto l = times(*k, a->first);
        const auto h = times(*k, a->second);
        if (!l || !h) return wide();
        out = Interval{std::min(*l, *h), std::max(*l, *h)};
        break;
      }
      case ExprOp::kMul:
      case ExprOp::kConv: {
        const auto a = go(*x.kids[0]);
        if (!a) return std::nullopt;
        const auto b = go(*x.kids[1]);
        if (!b) return std::nullopt;
        SignedInt lo = 0, hi = 0;
        bool first = true;
        for (SignedInt u : {a->first, a->second}) {
          for (SignedInt v : {b->first, b->second}) {
            const auto w = times(u, v);
            if (!w) return wide();
            if (first || *w < lo) lo = *w;
            if (first || *w > hi) hi = *w;
            first = false;
          }
        }
        if (x.op == ExprOp::kConv) {
          // Coefficient i sums between 1 and min(la, lb) products.
          const size_t la = x.kids[0]->dims().back();
          const size_t lb = x.kids[1]->dims().back();
          const SignedInt cnt = SignedInt(std::min(la, lb));
          const auto l = times(lo, cnt);
          const auto h = times(hi, cnt);
          if (!l || !h) return wide();
          lo = std::min(lo, *l);
          hi = std::max(hi, *h);
        }
        out = Interval{lo, hi};
        break;
      }
      case ExprOp::kSum: {
        const ExprNode<F> &k = *x.kids[0];
        const size_t w = x.w == 0 ? k.n : x.w;
        // A sum of a times constants (from_digits' digits times the powers
        // of the base): each group's sum of a's interval times each of its
        // constants, so the constants' signs and sizes are not hulled
        // first.
        if (k.op == ExprOp::kMul && w != 0) {
          for (size_t side = 0; side < 2 && !out; ++side) {
            const auto c = const_values(*k.kids[side]);
            if (!c || c->size() != k.n) continue;
            const auto a = go(*k.kids[1 - side]);
            if (!a) return std::nullopt;
            bool first = true;
            SignedInt lo = 0, hi = 0;
            for (size_t gi = 0; gi < k.n / w; ++gi) {
              SignedInt glo = 0, ghi = 0;
              for (size_t j = gi * w; j < (gi + 1) * w; ++j) {
                const auto u = times(a->first, (*c)[j]);
                const auto v = times(a->second, (*c)[j]);
                if (!u || !v) return wide();
                glo += std::min(*u, *v);
                ghi += std::max(*u, *v);
                if (!ok(glo) || !ok(ghi)) return wide();
              }
              if (first || glo < lo) lo = glo;
              if (first || ghi > hi) hi = ghi;
              first = false;
            }
            out = Interval{lo, hi};
          }
          if (out) break;
        }
        const auto a = go(k);
        if (!a) return std::nullopt;
        const SignedInt cnt = SignedInt(w);
        const auto l = times(a->first, cnt);
        const auto h = times(a->second, cnt);
        if (!l || !h) return wide();
        out = Interval{*l, *h};
        break;
      }
      case ExprOp::kBroadcast:
      case ExprOp::kMaterialize:
        out = go(*x.kids[0]);
        if (!out) return std::nullopt;
        break;
      case ExprOp::kGather: {
        for (const auto &k : x.kids) {
          const auto a = go(*k);
          if (!a) return std::nullopt;
          if (!out) {
            out = a;
          } else {
            out = Interval{std::min(out->first, a->first),
                           std::max(out->second, a->second)};
          }
        }
        break;
      }
      case ExprOp::kApply: {
        const auto a = go(*x.kids[0]);
        if (!a) return std::nullopt;
        const OpSpec<F> &op = *x.apply;
        std::optional<SignedInt> l, h;
        // The row bounds are Bounds: compared with the cap before the cast.
        if (op.row_sum != 0) {
          const auto r = int_below(op.row_sum, cap_bits);
          if (!r) return wide();
          l = times(std::min<SignedInt>(a->first, 0), *r);
          h = times(std::max<SignedInt>(a->second, 0), *r);
        } else if (op.abs_row_sum != 0) {
          const auto r = int_below(op.abs_row_sum, cap_bits);
          if (!r) return wide();
          h = times(std::max<SignedInt>(-a->first, a->second), *r);
          if (h) l = -*h;
        } else {
          why = "the term '" + describe_term(g, x) +
                "' applies the operator '" + op.name +
                "', which bounds no row sum";
          return std::nullopt;
        }
        if (!l || !h) return wide();
        out = Interval{*l, *h};
        break;
      }
      case ExprOp::kMux: {
        if (x.bit) {
          out = Interval{0, 1};
          break;
        }
        const auto a = go(*x.kids[1]);
        if (!a) return std::nullopt;
        const auto b = go(*x.kids[2]);
        if (!b) return std::nullopt;
        out = Interval{std::min(a->first, b->first),
                       std::max(a->second, b->second)};
        break;
      }
      case ExprOp::kProd:
        why = "the term '" + describe_term(g, x) +
              "' is a product of coordinates, which interval propagation "
              "does not bound";
        return std::nullopt;
      default:
        // Logic's builders: Bit results.
        out = Interval{0, 1};
        break;
    }
    if (!ok(out->first) || !ok(out->second)) return wide();
    if (out->first > out->second)
      ordered_interval(out->first, out->second,
                       "'" + describe_term(g, x) + "'");
    memo[&x] = *out;
    return out;
  };
  return go(*e);
}

// Whether node ID's values lie in the prime field of domain D (an
// unbounded such node has [0, p - 1] in interval propagation): a Bit, a
// value of the designated subfield when it is the prime field, or any
// value of a prime field.
template <class F>
std::function<bool(size_t)> prime_node(const Domain<F> &d, const Graph &g) {
  const bool field_prime = d.prime == Space::kField;
  const bool sub_prime = d.prime == Space::kSubfield;
  return [&g, field_prime, sub_prime](size_t id) {
    const Type ty = g.nodes.at(id).type;
    if (ty.base == Base::kBit || field_prime) return true;
    return sub_prime && ty.base == Base::kSubfield && ty.degree == 0;
  };
}

// The interval [0, N - 1] of a plain request implied by the bound N
// (RangeRealization::plain).
inline void set_plain_interval(RangeRealization &R, Bound N) {
  R.plain = true;
  R.plain_n = N;
  R.lo = 0;
  R.hi = N == 0 ? SignedInt(0) : SignedInt(N - 1);
}

// request_bound's cap on N - 1 and on the constants' sums: interval
// propagation's.
inline constexpr unsigned kRequestCapBits = kIntervalCapBits;
inline const SignedInt kRequestCap = SignedInt::pow2(kRequestCapBits);

// The interval node ID has before the range lowering runs (mod.h's rule,
// shared by assert_int_equal): [0, 1] for a Bit; [0, N - 1] for a
// statement value's declared bound N (Ref::bounded) and for the least
// bound N its plain range requests can establish (n for an exact request,
// m for an interval); and for a request on x + c (c a constant node), x in
// [-max c, N - 1 - min c]. The narrowest interval wins. A view without a
// request of its own (gather, at, slice) has the hull of its sources'
// intervals, a zero coordinate [0, 0]. None otherwise. A request with
// N = 0, or N - 1 or constants beyond the cap, gives no interval.
// WHY, when given, records the interval's source (IvlWhy).
template <class F>
std::optional<Interval> request_bound(const Domain<F> &d, const Graph &g,
                                      Bound p, size_t id,
                                      IvlWhy *why = nullptr) {
  const F &f = d.field();
  const bool prime_field = d.prime == Space::kField;
  const Node &n = g.nodes.at(id);
  if (n.type.base == Base::kBit) {
    if (why != nullptr) why->kind = IvlWhy::kBit;
    return Interval{0, 1};
  }
  std::optional<Interval> out;
  IvlWhy w;
  // A statement bound N (Ref::bounded): the verifier rejects a statement
  // outside [0, N - 1].
  if (n.stmt_bound != 0) {
    if (const auto top = int_below(n.stmt_bound - 1, kRequestCapBits)) {
      out = Interval{0, *top};
      w.kind = IvlWhy::kStmt;
    }
  }
  for (const auto &r : d.requests()) {
    if (r.implied_only || r.pending()) continue;
    bool plain = true;
    bool seen = false;
    SignedInt cmin = 0, cmax = 0;
    for (const auto &t : r.v.terms) {
      if (!t.chain.empty()) {
        plain = false;
        break;
      }
      if (g.nodes.at(t.node).kind == Kind::kConstant) {
        const auto v = g.system->template constant_values<F>(t.node);
        if (v.empty()) {
          plain = false;
          break;
        }
        SignedInt lo = 0, hi = 0;
        for (size_t j = 0; j < v.size(); ++j) {
          const auto c = signed_rep(f, p, prime_field, f.mulf(t.scale, v[j]));
          if (!c) {
            plain = false;
            break;
          }
          // Magnitudes below interval propagation's cap.
          const auto m = int_below(c->second, kRequestCapBits);
          if (!m) {
            plain = false;
            break;
          }
          const SignedInt cj = c->first ? -*m : *m;
          if (j == 0 || cj < lo) lo = cj;
          if (j == 0 || cj > hi) hi = cj;
        }
        if (!plain) break;
        cmin += lo;
        cmax += hi;
        if (cmax >= kRequestCap || cmin <= -kRequestCap) {
          plain = false;
          break;
        }
        continue;
      }
      if (seen || t.node != id || t.scale != f.one()) {
        plain = false;
        break;
      }
      seen = true;
    }
    if (!plain || !seen) continue;
    const Bound N = r.interval ? r.m : r.n;
    // A request above the cap bounds nothing that interval propagation
    // could use.
    if (N == 0) continue;
    const auto top = int_below(N - 1, kRequestCapBits);
    if (!top) continue;
    const Interval iv = ordered_interval(
        -cmax, *top - cmin, "the range request '" + r.name + "'");
    if (!out || iv.second - iv.first < out->second - out->first) {
      out = iv;
      w = IvlWhy{};
      w.kind = IvlWhy::kRequest;
      w.request = r.name;
      w.offset = cmin != 0 || cmax != 0 || r.v.terms.size() != 1;
      w.bound = N;
    }
  }
  if (out) {
    if (why != nullptr) *why = std::move(w);
    return out;
  }
  const auto *src = d.view_sources(id);
  if (src == nullptr) return std::nullopt;
  std::map<size_t, Interval> seen;
  w = IvlWhy{};
  w.kind = IvlWhy::kViews;
  for (const auto &[s, k] : *src) {
    Interval iv{0, 0};
    if (s != kZeroCoordinate) {
      auto it = seen.find(s);
      if (it == seen.end()) {
        IvlWhy ws;
        const auto b = request_bound(d, g, p, s, why ? &ws : nullptr);
        if (!b) return std::nullopt;
        it = seen.emplace(s, *b).first;
        w.sources.push_back({s, std::move(ws)});
      }
      iv = it->second;
    }
    out = out ? Interval{std::min(out->first, iv.first),
                         std::max(out->second, iv.second)}
              : iv;
  }
  if (why != nullptr) *why = std::move(w);
  return out;
}

// The interval node ID takes from a vanishing product of domain D: assert_zero
// of a product of k >= 2 factors u x + r_i with u in {1, -1}, read coordinate
// for coordinate. The factors are the leaves of a tree of products (kMul): a
// scaling by a nonzero constant or a nonzero constant factor drops out, and
// a leaf is either affine, u x + r with r affine in other values (the
// centered magnitude's (mag - x) (mag - (q - x)); a Bit's x (x - 1) is the
// case r = 0, -1), or a product of groups (kProd, Expr::prod) whose
// coordinates are u x_j + c, c a constant (prod_c (x - c)). Each root
// -r_i / u lies in an interval by BOUND_OF's intervals of r_i's terms; when
// every root lies in [0, p - 1], the canonical value of x is one of them,
// so x lies in their hull. The narrowest hull over D's predicates wins. A
// node without such a predicate takes the hull of the views of it that
// have one, when they cover every coordinate. None otherwise, and under a
// characteristic at or above the cap.
template <class F, class BoundOf>
// WHY, when given, records the predicates the hull comes from (IvlWhy::
// kRoots), and for a quadratic (two factors u x + r, each r one node m),
// the node m.
std::optional<Interval> root_hull(const Domain<F> &d, const Graph &g, Bound p,
                                  size_t id, BoundOf bound_of,
                                  IvlWhy *why = nullptr) {
  using Elt = typename F::Elt;
  // The rest node of each root factor of the predicate being read (SIZE_MAX
  // where a factor's rest is not one node), and the best predicates.
  std::vector<size_t> rests;
  std::vector<std::string> best_preds;
  size_t best_m = SIZE_MAX;
  const F &f = d.field();
  if (p >= Bound(kRequestCap)) return std::nullopt;
  const bool prime_field = d.prime == Space::kField;
  const std::function<bool(size_t)> pub = [&g](size_t k) {
    return is_public(g.nodes.at(k).kind);
  };
  const std::function<bool(size_t)> any = [](size_t) { return true; };
  // The hull of the roots of the vanishing products on node X.
  auto direct = [&](size_t xid) -> std::optional<Interval> {
    const Node &x = g.nodes.at(xid);
    auto in_range = [&](const Interval &r) {
      return r.first >= 0 && r.second <= SignedInt(p - 1);
    };
    // The root of one factor u x + r, or none.
    auto root = [&](const ExprPtr<F> &factor) -> std::optional<Interval> {
      const auto a = affine_form<F>(factor, pub, any);
      if (!a || !a->kc.empty()) return std::nullopt;
      Lin<F> rest = a->lin;
      rest.terms.clear();
      std::optional<Elt> u;
      for (const auto &t : a->lin.terms) {
        if (t.node != xid) {
          rest.terms.push_back(t);
          continue;
        }
        if (u || !t.chain.empty() || t.in_n != x.n) return std::nullopt;
        u = t.scale;
      }
      if (!u || (*u != f.one() && *u != f.mone())) return std::nullopt;
      {
        size_t m = SIZE_MAX, nonconst = 0;
        for (const auto &t : rest.terms)
          if (g.nodes.at(t.node).kind != Kind::kConstant) {
            m = t.node;
            ++nonconst;
          }
        rests.push_back(nonconst == 1 ? m : SIZE_MAX);
      }
      Interval r{0, 0};
      if (!rest.terms.empty()) {
        std::string why;
        const auto iv =
            lin_interval(f, p, prime_field, g, rest, bound_of, why);
        if (!iv) return std::nullopt;
        r = *iv;
      }
      SignedInt cmin = 0, cmax = 0;
      for (size_t j = 0; j < a->c.size(); ++j) {
        const auto c = signed_rep(f, p, prime_field, a->c[j]);
        if (!c) return std::nullopt;
        const SignedInt cj =
            c->first ? -SignedInt(c->second) : SignedInt(c->second);
        if (j == 0 || cj < cmin) cmin = cj;
        if (j == 0 || cj > cmax) cmax = cj;
      }
      r = Interval{r.first + cmin, r.second + cmax};
      const Interval out =
          *u == f.one() ? Interval{-r.second, -r.first} : r;
      if (!in_range(out)) return std::nullopt;
      return out;
    };
    // Each coordinate of E as u x_j + c (u = 0 when it reads no
    // coordinate of x), from leaves, constants, sums, scalings, broadcasts
    // and views; none for any other node.
    struct XCoord {
      size_t j = 0;
      Elt u, c;
    };
    std::function<std::optional<std::vector<XCoord>>(const ExprNode<F> &)>
        coords = [&](const ExprNode<F> &e)
        -> std::optional<std::vector<XCoord>> {
      std::vector<XCoord> out(e.n, XCoord{0, f.zero(), f.zero()});
      switch (e.op) {
        case ExprOp::kLin:
          for (const auto &t : e.lin.terms) {
            if (t.node != xid || !t.chain.empty() || t.in_n != e.n)
              return std::nullopt;
            for (size_t i = 0; i < e.n; ++i) {
              out[i].j = i;
              f.add(out[i].u, t.scale);
            }
          }
          return out;
        case ExprOp::kConst:
          for (size_t i = 0; i < e.n; ++i) out[i].c = e.c.at(i);
          return out;
        case ExprOp::kAdd: {
          const auto a = coords(*e.kids[0]);
          const auto b = coords(*e.kids[1]);
          if (!a || !b) return std::nullopt;
          for (size_t i = 0; i < e.n; ++i) {
            const XCoord &l = (*a)[i], &r = (*b)[i];
            if (l.u != f.zero() && r.u != f.zero() && l.j != r.j)
              return std::nullopt;
            out[i].j = l.u != f.zero() ? l.j : r.j;
            out[i].u = f.addf(l.u, r.u);
            out[i].c = f.addf(l.c, r.c);
          }
          return out;
        }
        case ExprOp::kScale: {
          const auto a = coords(*e.kids[0]);
          if (!a) return std::nullopt;
          for (size_t i = 0; i < e.n; ++i)
            out[i] = {(*a)[i].j, f.mulf(e.c[0], (*a)[i].u),
                      f.mulf(e.c[0], (*a)[i].c)};
          return out;
        }
        case ExprOp::kBroadcast: {
          const auto a = coords(*e.kids[0]);
          if (!a || a->empty()) return std::nullopt;
          for (size_t i = 0; i < e.n; ++i) out[i] = (*a)[i % a->size()];
          return out;
        }
        case ExprOp::kGather: {
          std::vector<XCoord> all;
          for (const auto &k : e.kids) {
            const auto a = coords(*k);
            if (!a) return std::nullopt;
            all.insert(all.end(), a->begin(), a->end());
          }
          for (size_t i = 0; i < e.n; ++i)
            if (e.idx[i] != kGatherNone) out[i] = all.at(e.idx[i]);
          return out;
        }
        default:
          return std::nullopt;
      }
    };
    // The hull of the roots of a product of groups: coordinate j w + k of
    // its operand is u x_j + c with one u in {1, -1}.
    auto group_roots = [&](const ExprNode<F> &e) -> std::optional<Interval> {
      if (e.n != x.n || e.w < 2) return std::nullopt;
      const auto a = coords(*e.kids[0]);
      if (!a || a->size() != e.n * e.w) return std::nullopt;
      const Elt u = (*a)[0].u;
      if (u != f.one() && u != f.mone()) return std::nullopt;
      std::optional<Interval> h;
      for (size_t i = 0; i < a->size(); ++i) {
        const XCoord &xc = (*a)[i];
        if (xc.u != u || xc.j != i / e.w) return std::nullopt;
        const auto c = signed_rep(f, p, prime_field, xc.c);
        if (!c) return std::nullopt;
        const SignedInt cv =
            c->first ? -SignedInt(c->second) : SignedInt(c->second);
        const SignedInt r = u == f.one() ? -cv : cv;
        h = h ? Interval{std::min(h->first, r), std::max(h->second, r)}
              : Interval{r, r};
      }
      if (!h || !in_range(*h)) return std::nullopt;
      return h;
    };
    // The hull of every factor's roots, with their count, or none when a
    // factor has no root form.
    std::function<bool(const ExprPtr<F> &, std::optional<Interval> &,
                       size_t &)>
        factors = [&](const ExprPtr<F> &e, std::optional<Interval> &h,
                      size_t &k) -> bool {
      auto join = [&](const Interval &r, size_t roots) {
        h = h ? Interval{std::min(h->first, r.first),
                         std::max(h->second, r.second)}
              : r;
        k += roots;
      };
      if (e->n != x.n) return false;
      if (e->op == ExprOp::kMul)
        return factors(e->kids[0], h, k) && factors(e->kids[1], h, k);
      if (e->op == ExprOp::kScale && e->c[0] != f.zero())
        return factors(e->kids[0], h, k);
      if (e->op == ExprOp::kConst) {
        for (const auto &c : e->c)
          if (c == f.zero()) return false;
        return true;
      }
      if (e->op == ExprOp::kProd) {
        const auto r = group_roots(*e);
        if (!r) return false;
        join(*r, e->w);
        return true;
      }
      const auto r = root(e);
      if (!r) return false;
      join(*r, 1);
      return true;
    };
    std::optional<Interval> out;
    for (const auto &pd : d.predicates()) {
      if (pd.truth || pd.e->n != x.n) continue;
      const ExprOp op = pd.e->op;
      if (op != ExprOp::kMul && op != ExprOp::kScale && op != ExprOp::kProd)
        continue;
      std::optional<Interval> h;
      size_t k = 0;
      rests.clear();
      if (!factors(pd.e, h, k) || k < 2 || !h) continue;
      if (!out || h->second - h->first < out->second - out->first) {
        out = h;
        best_preds = {pd.name};
        best_m = rests.size() == 2 && rests[0] == rests[1] ? rests[0] : SIZE_MAX;
      }
    }
    return out;
  };
  if (auto out = direct(id)) {
    if (why != nullptr) {
      why->kind = IvlWhy::kRoots;
      why->preds = best_preds;
      why->m = best_m;
      why->lo = out->first;
      why->hi = out->second;
    }
    return out;
  }
  std::vector<std::string> view_preds;
  // The views of ID with a vanishing product of their own, when together
  // they read every coordinate of ID.
  const size_t n = g.nodes.at(id).n;
  std::vector<bool> covered(n, false);
  size_t count = 0;
  std::optional<Interval> out;
  for (size_t v = 0; v < g.nodes.size(); ++v) {
    const Node &vn = g.nodes.at(v);
    if (std::find(vn.deps.begin(), vn.deps.end(), id) == vn.deps.end())
      continue;
    const auto *src = d.view_sources(v);
    if (src == nullptr) continue;
    const auto h = direct(v);
    if (!h) continue;
    view_preds.insert(view_preds.end(), best_preds.begin(), best_preds.end());
    for (const auto &[sid, k] : *src) {
      if (sid != id || covered.at(k)) continue;
      covered[k] = true;
      ++count;
    }
    out = out ? Interval{std::min(out->first, h->first),
                         std::max(out->second, h->second)}
              : *h;
  }
  if (count != n) return std::nullopt;
  if (why != nullptr) {
    why->kind = IvlWhy::kRoots;
    why->preds = view_preds;
    why->m = SIZE_MAX;
    if (out) {
      why->lo = out->first;
      why->hi = out->second;
    }
  }
  return out;
}

// E over the integers, for the plan export (PlanRecords::Affine): each
// term's signed coefficient and operand, and the constants per coordinate
// (a constant of one coordinate broadcasts).
template <class F>
PlanRecords::Affine plan_affine(const F &f, Bound p, bool prime_field,
                                const Graph &g, const Lin<F> &e) {
  PlanRecords::Affine out;
  out.n = e.n;
  out.consts.assign(e.n, 0);
  // A signed representative's magnitude is at most (p - 1) / 2.
  auto rep = [&](const typename F::Elt &a) -> std::optional<SignedInt> {
    const auto s = signed_rep(f, p, prime_field, a);
    if (!s) return std::nullopt;
    return s->first ? -SignedInt(s->second) : SignedInt(s->second);
  };
  for (const auto &t : e.terms) {
    const Node &n = g.nodes.at(t.node);
    if (n.kind == Kind::kConstant) {
      if (!t.chain.empty()) {
        out.error = "the constant '" + n.name + "' passes through an operator";
        return out;
      }
      const auto v = g.system->template constant_values<F>(t.node);
      if (v.size() != e.n && v.size() != 1) {
        out.error = "the constant '" + n.name + "' has " +
                    std::to_string(v.size()) + " coordinates";
        return out;
      }
      for (size_t j = 0; j < e.n; ++j) {
        const auto c = rep(f.mulf(t.scale, v.at(v.size() == 1 ? 0 : j)));
        if (!c) {
          out.error = "the constant '" + n.name + "' lies outside the prime field";
          return out;
        }
        // The sum of the constants, refused beyond interval propagation's
        // cap.
        out.consts[j] += *c;
        if (out.consts[j] >= kRequestCap || out.consts[j] <= -kRequestCap) {
          out.error = "the constants exceed 2^" +
                      std::to_string(kIntervalCapBits);
          return out;
        }
      }
      continue;
    }
    const auto a = rep(t.scale);
    if (!a) {
      out.error = "the coefficient of '" + n.name + "' lies outside the prime field";
      return out;
    }
    if (t.chain.empty()) {
      out.terms.push_back({'n', n.name});
    } else if (t.chain.size() == 1 && t.chain[0]->name == "sum") {
      out.terms.push_back({'s', n.name});
    } else {
      std::string nm = n.name;
      for (const auto &op : t.chain) nm = op->name + "(" + nm + ")";
      out.terms.push_back({'o', nm});
    }
    std::vector<std::pair<std::string, Bound>> bounds;
    if (out.terms.back().first == 'o')
      for (const auto &op : t.chain) {
        const std::string pre = t.chain.size() > 1 ? op->name + "." : "";
        if (!op->bound_terms.empty()) {
          for (const auto &[k, v] : op->bound_terms) bounds.push_back({pre + k, v});
        } else if (op->row_sum != 0) {
          bounds.push_back({pre + "rowSum", op->row_sum});
        } else if (op->abs_row_sum != 0) {
          bounds.push_back({pre + "absRowSum", op->abs_row_sum});
        }
      }
    out.op_bounds.push_back(std::move(bounds));
    out.coeffs.push_back(*a);
  }
  return out;
}

// The least b >= 1 with b^k >= n.
inline Bound ceil_root(Bound n, unsigned k) {
  if (k == 1 || n <= 1) return n;
  // Whether b^k >= n, without overflow.
  auto reaches = [n, k](Bound b) {
    Bound r = 1;
    for (unsigned j = 0; j < k; ++j) {
      if (r > (n - 1) / b) return true;
      r *= b;
    }
    return r >= n;
  };
  Bound lo = 1, hi = n;
  while (lo < hi) {
    const Bound mid = lo + (hi - lo) / 2;
    if (reaches(mid)) {
      hi = mid;
    } else {
      lo = mid + 1;
    }
  }
  return lo;
}

// Adds to OUT the candidate tables of a range check below N (exact, or with
// MaxBound M when INTERVAL) whose realizations have between K_MIN and
// max_digits digits (paper, appendix range-candidates): b = ceil(N^(1/k))
// where a realization with k digits is valid at b (k = 1: the direct table
// b = N; k >= 2: digits with b^k admissible and b^k <= p, or, with
// TWO_SIDED, two-sided digits with 2 (b^k - 1) < p), and
// 2 <= b <= min(p, CAP).
inline void add_candidates(Bound n, Bound m, bool interval, Bound cap, Bound p,
                           const RangePolicy &pol, unsigned k_min,
                           std::set<Bound> &out, bool two_sided = true) {
  auto has = [&pol](RealizationKind k) {
    return std::find(pol.kinds.begin(), pol.kinds.end(), k) != pol.kinds.end();
  };
  for (unsigned k = k_min; k <= pol.max_digits; ++k) {
    const Bound b = ceil_root(n, k);
    if (b < 2 || b > p || b > cap) continue;
    if (k == 1) {
      out.insert(b);
      continue;
    }
    const Bound Tk = bound_pow(b, k);
    const bool digits = has(RealizationKind::kDigits) && Tk <= p &&
                        (interval ? n <= Tk && Tk <= m : Tk == n);
    const bool two = two_sided && has(RealizationKind::kTwoSided) &&
                     bound_mul(2, Tk - 1) < p;
    if (digits || two) out.insert(b);
  }
}

}  // namespace range_internal

template <class F, class S>
class RangeLoweringImpl : Lowering {
  using D = Domain<F>;
  using Elt = typename F::Elt;
  using Candidate = range_internal::Candidate;

  // The proven bounds of nodes (node -> exclusive bound): the least
  // selected bound among the plain requests on each.
  using Bounds = std::map<size_t, Bound>;

  // What the planner decides, which emit reads.
  struct Plan {
    std::vector<size_t> phase;
    std::set<size_t> claimed;         // nodes the selected digits bind
    std::map<size_t, std::string> not_implied;  // request -> why (report)
    std::map<size_t, size_t> dup_of;      // duplicate request -> its first
    std::map<size_t, size_t> implied_by;  // plain request -> the bounding one
    std::set<size_t> by_type;             // plain requests bounded by type
  };

  // A needle: a node of the domain whose every coordinate lies in [0, T).
  struct Needle {
    Ref<F> ref;
    Bound table;
    Bound honest;  // the honest exclusive bound (S_dyn)
    size_t req = SIZE_MAX;  // the request it checks
  };

 public:
  RangeLoweringImpl(D &d, ConstraintSystemBuilder<S> &b)
      : d_(d),
        b_(b),
        f_(d.field()),
        pol_(b.profile().range),
        costs_(range_internal::range_costs(d.rates(),
                                           d.prime != Space::kField)) {}

  void run() {
    auto &reqs = requests(d_);
    std::vector<size_t> todo;
    for (size_t i = 0; i < reqs.size(); ++i)
      if (!reqs[i].lowered) todo.push_back(i);
    if (todo.empty()) return;
    // R1: lookups need an odd characteristic.
    if constexpr (F::kCharacteristicTwo) {
      fail("range request '" + reqs[todo[0]].name + "' in domain " + d_.name +
           ", which has characteristic 2; range requests need an odd "
           "characteristic");
    } else {
      for (size_t i : todo)
        if (reqs[i].pending())
          fail("range request '" + reqs[i].name + "' of domain " + d_.name +
               " (Slack): no assert_int_equal reading its value derived its "
               "maximum");
      std::optional<CompileRegion> ph;
      ph.emplace(compile_times_on() ? "plan " + d_.name : "");
      const Plan pl = plan(todo);
      ph.reset();
      ph.emplace(compile_times_on() ? "emit " + d_.name : "");
      auto needles = emit(todo, pl);
      ph.reset();
      ph.emplace(compile_times_on() ? "tables " + d_.name : "");
      tables(needles);
    }
  }

 private:
  // ------------------------------------------------------------ planner --

  // A request is plain when V is one node, read with coefficient 1 and no
  // operator.
  std::optional<size_t> plain(const RangeRequest<F> &r) const {
    if (r.v.terms.size() != 1) return std::nullopt;
    const auto &t = r.v.terms[0];
    if (!t.chain.empty() || t.scale != f_.one()) return std::nullopt;
    return t.node;
  }

  // A request on x + c: one node x read with coefficient 1 and no operator,
  // and constant nodes. Its digits can bind x (x = digits - c).
  std::optional<size_t> offset_node(const RangeRequest<F> &r) const {
    const auto &N = b_.system().graph().nodes;
    std::optional<size_t> x;
    for (const auto &t : r.v.terms) {
      if (!t.chain.empty()) return std::nullopt;
      if (N.at(t.node).kind == Kind::kConstant) continue;
      if (x || t.scale != f_.one()) return std::nullopt;
      x = t.node;
    }
    return x;
  }
  // The request's node that its digits bind: the plain node, or x of x + c.
  std::optional<size_t> bound_node(const RangeRequest<F> &r) const {
    if (auto x = plain(r)) return x;
    return offset_node(r);
  }
  // The constants of an x + c request, per coordinate, as elements.
  std::vector<Elt> offsets(const RangeRequest<F> &r) const {
    std::vector<Elt> c(r.v.n, f_.zero());
    for (const auto &t : r.v.terms) {
      if (b_.system().graph().nodes.at(t.node).kind != Kind::kConstant)
        continue;
      const auto cv = b_.system().graph().gens.at(t.node).eval(ValueStore<S>{});
      const auto &v = S::template get<F>(cv);
      for (size_t j = 0; j < r.v.n; ++j) f_.add(c[j], f_.mulf(t.scale, v.at(j)));
    }
    return c;
  }

  // Whether the digits of a request on node X can bind X (B1-B5): phase-0
  // advice or a private input whose digits no other selection binds
  // (CLAIMED).
  bool bindable(size_t x, const std::set<size_t> &claimed) const {
    if (!pol_.bind_digit_views) return false;
    const Node &n = b_.system().graph().nodes.at(x);
    if ((n.kind != Kind::kAdvice && n.kind != Kind::kPrivateInput) ||
        n.domain != d_.index)
      return false;
    if (pl_.phase.at(x) != 0) return false;
    if (n.type.base == Base::kBit) return false;
    if (claimed.count(x)) return false;
    return d_.bindable_shape(x);
  }

  // The candidate tables of the requests REQS (paper, appendix
  // range-candidates; range_internal::add_candidates with 1 <= k <=
  // max_digits, each within its request's table cap), leaving out the
  // assert_range_implied requests, which no table realizes. Some least-cost
  // plan uses only these tables (lem:range-candidates). Ascending.
  // UNCAPPED ignores the caps (for the compile error that names them).
  std::vector<Bound> candidate_tables(const std::vector<size_t> &reqs,
                                      bool uncapped = false) const {
    std::set<Bound> out;
    for (size_t i : reqs) {
      const RangeRequest<F> &r = d_.requests()[i];
      if (r.implied_only) continue;
      range_internal::add_candidates(r.n, r.m, r.interval,
                                     uncapped ? p_ : table_cap(r), p_, pol_,
                                     1, out);
    }
    return std::vector<Bound>(out.begin(), out.end());
  }

  // The largest table request R may use: its own max_table, else its
  // domain's, else the policy's.
  Bound table_cap(const RangeRequest<F> &r) const {
    if (*r.max_table != 0) return *r.max_table;
    if (d_.max_table() != 0) return d_.max_table();
    return pol_.max_table;
  }

  // The signed integer representative of a prime-field coefficient.
  std::optional<std::pair<bool, Bound>> signed_rep(const Elt &a) const {
    return range_internal::signed_rep(f_, p_, d_.prime == Space::kField, a);
  }

  // The realizations of request I in the tables TABS, sorted (Candidate's
  // order): BOUNDS give the interval of the complement's v, and CLAIMED
  // the nodes whose digits another selection binds. For each table, the
  // digit and two-sided realizations take the least valid number of
  // digits. Rejections are appended to WHY when it is given.
  std::vector<Candidate> options(size_t i, const std::vector<Bound> &tabs,
                                 const Bounds &bounds,
                                 const std::set<size_t> &claimed,
                                 std::vector<std::string> *why) const {
    const RangeRequest<F> &r = d_.requests()[i];
    std::vector<Candidate> out;
    auto reject = [why](const std::string &w) {
      if (why) why->push_back(w);
    };
    for (size_t kr = 0; kr < pol_.kinds.size(); ++kr) {
      const RealizationKind kind = pol_.kinds[kr];
      for (Bound T : tabs) {
        const std::string at =
            std::string(realization_name(kind)) + " T=" + bound_str(T) + ": ";
        if (T > p_) {  // R2
          reject(at + "T > p");
          continue;
        }
        if (T > table_cap(r)) {
          reject(at + "T above the table cap " + bound_str(table_cap(r)) +
                 " (raise it with max_table on the request or domain)");
          continue;
        }
        Candidate c;
        c.kind_rank = kr;
        c.r.kind = kind;
        c.r.table = T;
        auto admissible = [&](Bound N) {
          return r.interval ? (r.n <= N && N <= r.m) : N == r.n;
        };
        switch (kind) {
          case RealizationKind::kDirect: {
            if (!admissible(T)) {
              reject(at + "established " + bound_str(T) +
                     (r.interval ? " outside [" + bound_str(r.n) + ", " +
                                       bound_str(r.m) + "]"
                                 : " != n = " + bound_str(r.n)));
              continue;
            }
            c.r.established = T;
            c.r.needles = 1;
            break;
          }
          case RealizationKind::kComplement: {
            // One needle n - 1 - v, from v's interval [lo, hi]: lo >= 0 and
            // hi + T < p.
            if (r.n > T) {
              reject(at + "n > T");
              continue;
            }
            std::string w;
            const auto iv = interval(r, bounds, w);
            if (!iv) {
              reject(at + "no interval: " + w);
              continue;
            }
            if (iv->first < 0 || bound_add(Bound(iv->second), T) >= p_) {
              reject(at + "the interval [" + int_str(iv->first) + ", " +
                     int_str(iv->second) + "] has lo < 0 or hi + T >= p");
              continue;
            }
            c.r.established = r.n;
            c.r.needles = 1;
            c.r.lo = iv->first;
            c.r.hi = iv->second;
            break;
          }
          case RealizationKind::kDigits: {
            std::optional<unsigned> k;
            Bound Tk = 1;
            for (unsigned j = 1; j <= pol_.max_digits; ++j) {
              Tk = bound_mul(Tk, T);
              if (Tk > p_) break;
              if (admissible(Tk)) {
                k = j;
                break;
              }
              if (Tk > r.m) break;
            }
            if (!k) {
              reject(at + "no k <= " + std::to_string(pol_.max_digits) +
                     " with T^k admissible and T^k <= p");
              continue;
            }
            c.r.k = *k;
            c.r.established = Tk;
            c.r.needles = *k;
            c.r.coords = *k;
            break;
          }
          default: {  // kTwoSided
            std::optional<unsigned> k;
            Bound Tk = 1;
            for (unsigned j = 1; j <= pol_.max_digits; ++j) {
              Tk = bound_mul(Tk, T);
              if (Tk >= r.n) {
                k = j;
                break;
              }
            }
            if (!k) {
              reject(at + "no k <= " + std::to_string(pol_.max_digits) +
                     " with n <= T^k");
              continue;
            }
            if (bound_mul(2, Tk - 1) >= p_) {
              reject(at + "2(T^k - 1) >= p");
              continue;
            }
            c.r.k = *k;
            c.r.established = r.n;
            c.r.needles = 2 * *k;
            c.r.coords = 2 * *k;
            break;
          }
        }
        // A plain phase-0 advice node is bound by its digits.
        const bool digits = kind == RealizationKind::kDigits ||
                            kind == RealizationKind::kTwoSided;
        const auto bx = bound_node(r);
        bool offsets_prime = true;
        if (bx && !plain(r))
          for (const auto &e : offsets(r))
            offsets_prime = offsets_prime && subfield_contains(f_, e);
        if (digits && bx && offsets_prime && bindable(*bx, claimed)) {
          c.r.bound = true;
          c.r.coords -= 1;
        }
        c.cost = Bound(c.r.needles) * costs_.needle +
                 Bound(c.r.coords) * costs_.coord;
        c.total = c.cost * r.v.n;
        out.push_back(c);
      }
    }
    std::sort(out.begin(), out.end());
    return out;
  }

  // The conditions the realization R of request REQ relies on (the
  // planner's checks), recorded
  // with certify
  // under range.<name>.<condition>.
  void certify_realization(const RangeRequest<F> &req,
                           const RangeRealization &R, const Plan &pl) const {
    const std::string nm = "range." + req.name + ".";
    const Bound T = R.table;
    auto cert = [&](const std::string &c, const Condition &cond) {
      b_.system().note("certify", nm + c, cond, d_);
    };
    cert("table", term("T", T) <= term("p", p_));
    switch (R.kind) {
      case RealizationKind::kComplement:
        cert("complementLow", term("0", 0) <= term("lo", Bound(R.lo)));
        cert("complementHigh",
             term("hi + T", bound_add(Bound(R.hi), T)) < term("p", p_));
        break;
      case RealizationKind::kDigits:
        cert("digits", term("T^k", R.established) <= term("p", p_));
        break;
      case RealizationKind::kTwoSided: {
        Bound Tk = 1;
        for (unsigned j = 0; j < R.k; ++j) Tk = bound_mul(Tk, T);
        cert("twoSided", term("2 (T^k - 1)", bound_mul(2, Tk - 1)) <
                             term("p", p_));
        break;
      }
      default:
        break;
    }
  }

  std::string describe_request(const RangeRequest<F> &r) const {
    return "range request '" + r.name + "' of domain " + d_.name +
           (r.interval ? " (n = " + bound_str(r.n) + ", m = " +
                             bound_str(r.m) + ")"
                       : " (exact, n = " + bound_str(r.n) + ")");
  }

  // ------------------------------------------------- interval propagation

  // The exclusive bound of node ID: its proven bound in BOUNDS, 2 for a
  // Bit (its Boolean check or packing), a statement value's declared bound
  // (Ref::bounded; the smaller one when BOUNDS also has one), for a view
  // the largest of its sources' (1 for a zero coordinate), or none.
  std::optional<Bound> bound_of(size_t id, const Bounds &bounds) const {
    const Bound declared = b_.system().graph().nodes.at(id).stmt_bound;
    auto it = bounds.find(id);
    if (it != bounds.end())
      return declared != 0 ? std::min(it->second, declared) : it->second;
    if (b_.system().graph().nodes.at(id).type.base == Base::kBit)
      return Bound(2);
    if (declared != 0) return declared;
    const auto *src = d_.view_sources(id);
    if (src == nullptr) return std::nullopt;
    Bound out = 1;
    std::set<size_t> seen;
    for (const auto &[s, k] : *src) {
      if (s == kZeroCoordinate || !seen.insert(s).second) continue;
      const auto b = bound_of(s, bounds);
      if (!b) return std::nullopt;
      out = std::max(out, *b);
    }
    return out;
  }
  // The bound node ID's type gives it: 2 for a Bit, p for a value of the
  // prime field (its canonical integer is below p).
  std::optional<Bound> type_bound(size_t id) const {
    const Node &n = b_.system().graph().nodes.at(id);
    if (n.type.base == Base::kBit) return Bound(2);
    if (n.domain != d_.index) return std::nullopt;
    if (d_.prime == Space::kField && n.type.base != Base::kBytes) return p_;
    if (d_.prime == Space::kSubfield && n.type.base == Base::kSubfield &&
        n.type.degree <= 1)
      return p_;
    return std::nullopt;
  }

  // The integer interval [lo, hi] of request R's expression over every
  // coordinate: a term a x, with a's signed integer representative and x a
  // node of proven bound N_x, spans a [0, N_x - 1];
  // a constant contributes exactly. A term that is not range-checked, an
  // operator, a coefficient outside the prime field, or an interval beyond
  // interval propagation's cap leaves the expression unbounded (none, with
  // WHY).
  std::optional<std::pair<SignedInt, SignedInt>> interval(
      const RangeRequest<F> &r, const Bounds &bounds, std::string &why) const {
    return range_internal::lin_interval(
        f_, p_, d_.prime == Space::kField, b_.system().graph(), r.v,
        [&](size_t id) { return bound_of(id, bounds); }, why);
  }

  // The bound N that the interval [LO, HI] establishes for R: the canonical
  // value is the integer itself when 0 <= LO and HI < N <= p, and R admits N
  // (N = n exact; n <= N <= m otherwise). None, with WHY, when it does not.
  std::optional<Bound> implied_bound(const RangeRequest<F> &r, SignedInt lo,
                                     SignedInt hi, std::string &why) const {
    if (lo < 0) {
      why = "the interval [" + int_str(lo) + ", " + int_str(hi) +
            "] has a negative lower end, where the canonical value wraps to "
            "p + lo";
      return std::nullopt;
    }
    const Bound need = Bound(hi) + 1;
    const Bound n = r.interval ? std::max(r.n, need) : r.n;
    if (need > n || n > r.m || n > p_) {
      why = "the interval [" + int_str(lo) + ", " + int_str(hi) +
            "] needs N >= " + bound_str(need) +
            (r.interval ? ", outside [" + bound_str(r.n) + ", " +
                              bound_str(std::min(r.m, p_)) + "]"
                        : ", above n = " + bound_str(r.n));
      return std::nullopt;
    }
    return n;
  }

  // Whether request I is implied under BOUNDS; fills the realization.
  bool implied(size_t i, const Bounds &bounds, RangeRealization &out,
               std::string &why) const {
    const RangeRequest<F> &r = d_.requests()[i];
    auto iv = interval(r, bounds, why);
    if (!iv) return false;
    auto n = implied_bound(r, iv->first, iv->second, why);
    if (!n) return false;
    out = RangeRealization{};
    out.kind = RealizationKind::kImplied;
    out.established = *n;
    out.lo = iv->first;
    out.hi = iv->second;
    return true;
  }

  // -------------------------------------------------------- planner steps --

  // The requests to plan, as the subset search reads them: the plain
  // requests independent of every expression, per node; the components of
  // plain requests joined by the expressions they may imply, with those
  // expressions; the expression requests; the bounds and tables of
  // requests lowered before the search; and the groups of requests of which
  // at least one pays in every subset (the first of each node's
  // independent plain requests, each expression no interval propagation can
  // imply, and a component's members on one node).
  // Every list is in the fixed request order (order_less), so the search
  // does not depend on the order of declaration.
  struct Component {
    std::vector<size_t> members, exprs;
  };
  struct Problem {
    std::map<size_t, std::vector<size_t>> indep;
    std::vector<Component> comps;
    std::vector<size_t> exprs;
    std::set<size_t> links;
    Bounds base, tight;
    std::set<Bound> open;
    std::vector<std::vector<size_t>> must_pay;
  };
  // One subset's assignment: the selections, the plain requests another
  // request on the same value implies, the nodes digits bind, the reasons
  // expressions are not implied, and the cost (the subset's new rows plus
  // every selection's total). WHY says why the subset admits no
  // assignment.
  struct Choice {
    bool ok = true;
    Bound cost = 0;
    std::map<size_t, RangeRealization> sel;
    std::map<size_t, Bound> totals;
    std::map<size_t, size_t> implied_by;
    std::map<size_t, std::string> not_implied;
    std::set<size_t> claimed;
    std::string why;
  };

  // The fixed order of requests: a plain request's limit (n, or m with
  // MaxBound) first when LIMIT_FIRST, then the request's expression, bounds
  // and kind (signature, with operators by name), then its name.
  bool order_less(size_t a, size_t b, bool limit_first) const {
    const auto &ra = d_.requests()[a], &rb = d_.requests()[b];
    if (limit_first && limit(ra) != limit(rb)) return limit(ra) < limit(rb);
    const auto ka = order_key(ra), kb = order_key(rb);
    if (ka != kb) return ka < kb;
    if (ra.name != rb.name) return ra.name < rb.name;
    return a < b;
  }
  std::vector<uint8_t> order_key(const RangeRequest<F> &r) const {
    std::vector<uint8_t> b;
    put_bound(b, r.n);
    put_bound(b, r.m);
    put_u64(b, r.interval ? 1 : 0);
    put_u64(b, r.implied_only ? 1 : 0);
    put_u64(b, r.v.n);
    put_u64(b, r.v.terms.size());
    for (const auto &t : r.v.terms) {
      put_u64(b, t.node);
      uint8_t e[F::kBytes];
      f_.to_bytes_field(e, t.scale);
      b.insert(b.end(), e, e + F::kBytes);
      put_u64(b, t.chain.size());
      for (const auto &op : t.chain) put_str(b, op->name);
    }
    return b;
  }
  // The bound a request's realization may not exceed: n, or m with
  // MaxBound.
  static Bound limit(const RangeRequest<F> &r) {
    return r.interval ? r.m : r.n;
  }
  void sort_requests(std::vector<size_t> &v, bool limit_first) const {
    std::sort(v.begin(), v.end(), [&](size_t a, size_t b) {
      return order_less(a, b, limit_first);
    });
  }

  // Request I's realization when a selection establishing E on the same
  // value implies it.
  static RangeRealization implied_at(const RangeRequest<F> &r, Bound E) {
    RangeRealization R;
    R.kind = RealizationKind::kImplied;
    R.established = r.interval ? std::max(r.n, E) : r.n;
    range_internal::set_plain_interval(R, E);
    return R;
  }

  // Selects the realization of every pending request (paper sec.
  // rand-planning): the candidate tables C from the requests' bounds, and
  // the subset of C whose assignment costs least, searched by branch and
  // bound. Duplicates and requests a value's type bounds cost nothing and
  // are settled first.
  Plan plan(const std::vector<size_t> &todo) {
    p_ = field_characteristic(f_);
    pl_.phase = b_.phases();
    auto &reqs = requests(d_);
    const auto &N = b_.system().graph().nodes;

    // Duplicates: a request equal to another (same expression and bounds)
    // takes its realization and costs nothing; the first in the fixed
    // order is realized.
    std::vector<size_t> live;
    {
      std::vector<size_t> sorted = todo;
      sort_requests(sorted, false);
      std::map<std::vector<uint8_t>, size_t> first;
      for (size_t i : sorted) {
        auto [it, fresh] = first.emplace(signature(reqs[i]), i);
        if (fresh)
          live.push_back(i);
        else
          pl_.dup_of[i] = it->second;
      }
    }
    // A plain request its node's type bounds: a Bit below 2, a prime-field
    // value below p.
    for (size_t i : live) {
      const auto x = plain(reqs[i]);
      if (!x || reqs[i].implied_only) continue;
      const auto tb = type_bound(*x);
      if (!tb) continue;
      const RangeRequest<F> &r = reqs[i];
      const Bound n = r.interval ? std::max(r.n, *tb) : r.n;
      if (*tb > n || n > r.m) continue;
      RangeRealization R;
      R.kind = RealizationKind::kImplied;
      R.established = n;
      range_internal::set_plain_interval(R, *tb);
      reqs[i].realization = R;
      reqs[i].lowered = true;
      pl_.by_type.insert(i);
    }

    Problem pr;
    // The bounds and tables of the requests already lowered.
    for (const auto &r : reqs) {
      if (!r.lowered) continue;
      if (auto x = plain(r)) {
        auto it = pr.base.find(*x);
        if (it == pr.base.end() || r.realization.established < it->second)
          pr.base[*x] = r.realization.established;
      }
      if (r.realization.kind != RealizationKind::kImplied &&
          r.realization.table != 0)
        pr.open.insert(r.realization.table);
    }

    std::map<size_t, std::vector<size_t>> plain_of;  // node -> plain requests
    for (size_t i : live)
      if (auto x = plain(reqs[i]); x && !reqs[i].lowered)
        plain_of[*x].push_back(i);
    // Expression requests that interval propagation may establish, and the
    // plain requests their terms read.
    std::map<size_t, std::vector<size_t>> links;
    for (size_t i : live) {
      if (plain(reqs[i])) {
        if (reqs[i].implied_only)
          fail(describe_request(reqs[i]) + " reads one node with "
               "coefficient 1, which interval propagation cannot bound");
        continue;
      }
      pr.exprs.push_back(i);
      std::vector<size_t> ops;
      std::string why;
      for (const auto &t : reqs[i].v.terms) {
        if (N.at(t.node).kind == Kind::kConstant) continue;
        // A Bit is bounded by its type.
        if (N.at(t.node).type.base == Base::kBit) continue;
        auto it = plain_of.find(t.node);
        if (it == plain_of.end()) {
          why = "the term '" + N.at(t.node).name + "' is not range-checked";
          break;
        }
        ops.insert(ops.end(), it->second.begin(), it->second.end());
      }
      if (why.empty()) {
        links[i] = ops;
        pr.links.insert(i);
      } else if (reqs[i].implied_only) {
        fail(describe_request(reqs[i]) + " is not implied: " + why);
      } else {
        pl_.not_implied[i] = why;
        pr.must_pay.push_back({i});
      }
    }
    sort_requests(pr.exprs, false);
    // An expression that is not implied even at its terms' tightest bounds
    // (each plain node at the least n of its requests; intervals only
    // narrow as bounds fall) is looked up in every subset: it pays.
    pr.tight = pr.base;
    for (const auto &[x, rs] : plain_of)
      for (size_t i : rs) {
        auto it = pr.tight.find(x);
        if (it == pr.tight.end() || reqs[i].n < it->second)
          pr.tight[x] = reqs[i].n;
      }
    for (size_t e : pr.links) {
      if (reqs[e].implied_only) continue;
      RangeRealization R;
      std::string why;
      if (!implied(e, pr.tight, R, why)) pr.must_pay.push_back({e});
    }

    // Components of plain requests joined by the expressions they bound.
    std::map<size_t, size_t> comp;
    std::function<size_t(size_t)> root = [&](size_t i) {
      auto it = comp.find(i);
      if (it == comp.end() || it->second == i) return i;
      return it->second = root(it->second);
    };
    for (const auto &[e, ops] : links)
      for (size_t a : ops) {
        comp.emplace(a, a);
        comp.emplace(ops[0], ops[0]);
        comp[root(a)] = root(ops[0]);
      }
    {
      std::map<size_t, Component> groups;
      for (size_t i : live) {
        const auto x = plain(reqs[i]);
        if (!x || reqs[i].lowered) continue;
        if (comp.count(i)) {
          groups[root(i)].members.push_back(i);
        } else {
          pr.indep[*x].push_back(i);
        }
      }
      for (const auto &[e, ops] : links)
        if (!ops.empty() && comp.count(ops[0]))
          groups[root(ops[0])].exprs.push_back(e);
      for (auto &[g, cp] : groups) {
        sort_requests(cp.members, false);
        sort_requests(cp.exprs, false);
        std::map<size_t, std::vector<size_t>> on;
        for (size_t m : cp.members) on[*plain(reqs[m])].push_back(m);
        for (auto &[x, ms] : on) pr.must_pay.push_back(ms);
        pr.comps.push_back(std::move(cp));
      }
      // Components in the order of their first member.
      std::sort(pr.comps.begin(), pr.comps.end(),
                [&](const Component &a, const Component &b) {
                  return order_less(a.members[0], b.members[0], false);
                });
      for (auto &[x, rs] : pr.indep) {
        sort_requests(rs, true);
        pr.must_pay.push_back({rs[0]});
      }
    }

    // The candidate tables, from every request still to plan.
    std::vector<size_t> pending;
    for (size_t i : live)
      if (!reqs[i].lowered) pending.push_back(i);
    if (pending.empty()) {
      settle_duplicates();
      return pl_;
    }
    const std::vector<Bound> cand = candidate_tables(pending);
    const size_t nc = cand.size();

    // The search's lower bound. lb[j][u]: the least total of a request of
    // must-pay group j in table cand[u] alone (none without a realization
    // there), with no node claimed and, for an expression, its terms at
    // their tightest bounds (the complement's interval only narrows as
    // bounds fall); its last entry, when present, is the least in the open
    // tables. share[u]: the number of groups with a
    // realization in cand[u], among which an undecided table's rows (at
    // c_T each) are split.
    std::vector<std::vector<std::optional<Bound>>> lb;
    std::vector<size_t> share(nc, 0);
    const std::vector<Bound> open(pr.open.begin(), pr.open.end());
    auto least = [&](const std::vector<size_t> &group,
                     const std::vector<Bound> &tabs) {
      std::optional<Bound> m;
      for (size_t i : group) {
        const Bounds &bd = plain(reqs[i]) ? pr.base : pr.tight;
        const auto o = options(i, tabs, bd, {}, nullptr);
        if (!o.empty() && (!m || o[0].total < *m)) m = o[0].total;
      }
      return m;
    };
    for (const auto &group : pr.must_pay) {
      std::vector<std::optional<Bound>> row(nc);
      for (size_t u = 0; u < nc; ++u) {
        row[u] = least(group, {cand[u]});
        if (row[u]) ++share[u];
      }
      if (!open.empty()) row.push_back(least(group, open));
      lb.push_back(std::move(row));
    }

    // Branch and bound over the subsets of C, deciding the tables from the
    // largest down, each left out before it is put in: a large table's rows
    // bound the search early, and a small table seldom lowers a request's
    // least total once the large ones are decided. A subset costs c_T times
    // its tables' rows (those not already open) plus its assignment
    // (evaluate), under the domain's cost model (RangeCosts). A node's
    // lower bound is the cost of the rows of the tables put in plus, for
    // each must-pay group, its least total over the allowed tables, an
    // undecided table adding the cost of its rows divided among the groups
    // that could share it (each table's rows are paid once, by at most that
    // many groups). Costs are integers, so a node whose bound exceeds the
    // best cost so far less one is cut; ties go to the subset the search
    // reaches first. The search visits at most max_search_nodes nodes, and
    // a domain that needs more fails the compile.
    //
    // The choice is then the default among the subsets within
    // kDefaultMarginPercent of that least cost (placement_rates.h): the
    // fewest tables, then the fewest total rows, then the least cost. A
    // second search per table count K, from 1 up, with the same bounds and
    // the margin as its cut, evaluates every subset of K tables within the
    // margin; the first K with one decides. The least-cost subset is within
    // the margin, so the K searches end by its count, and the choice is
    // exact.
    std::vector<bool> in(nc, false);
    std::optional<Choice> best;
    std::vector<Bound> best_tables;
    size_t evaluated = 0, nodes = 0;
    // The table-count search: K (0 for the least-cost search), the cut
    // (costs above it are outside the margin), and its pick.
    size_t want_k = 0;
    long double cut = 0;
    std::optional<Choice> pick;
    std::vector<Bound> pick_tables;
    Bound pick_rows = 0;
    // T: the number of tables decided, cand[nc - T .. nc - 1]. ROWS: the
    // cost of the rows of the tables put in, c_T per row; CNT: their
    // number.
    std::function<void(size_t, Bound, size_t)> dfs = [&](size_t t, Bound rows,
                                                         size_t cnt) {
      if (want_k != 0 && (cnt > want_k || cnt + (nc - t) < want_k)) return;
      if (++nodes > pol_.max_search_nodes) {
        std::string list;
        for (Bound b : cand) list += (list.empty() ? "" : ", ") + bound_str(b);
        fail("range planning of domain " + d_.name + ": the search over the "
             "subsets of " + std::to_string(nc) + " candidate tables (" +
             list + ") visited more than max_search_nodes = " +
             std::to_string(pol_.max_search_nodes) + " nodes");
      }
      long double low = static_cast<long double>(rows);
      for (size_t j = 0; j < lb.size(); ++j) {
        std::optional<long double> m;
        auto offer = [&m](long double v) {
          if (!m || v < *m) m = v;
        };
        for (size_t u = 0; u < nc; ++u) {
          if (!lb[j][u]) continue;
          const bool decided = u + t >= nc;
          if (decided && in[u]) offer(static_cast<long double>(*lb[j][u]));
          if (!decided)
            offer(static_cast<long double>(*lb[j][u]) +
                  static_cast<long double>(cand[u] * costs_.row) /
                      static_cast<long double>(share[u]));
        }
        if (lb[j].size() > nc && lb[j].back())
          offer(static_cast<long double>(*lb[j].back()));
        if (!m) return;
        low += *m;
      }
      if (want_k == 0 && best &&
          low > static_cast<long double>(best->cost) - 1 + 1e-6L)
        return;
      if (want_k != 0 && low > cut) return;
      if (t == nc) {
        std::vector<Bound> tabs(pr.open.begin(), pr.open.end());
        for (size_t u = 0; u < nc; ++u)
          if (in[u] && !pr.open.count(cand[u])) tabs.push_back(cand[u]);
        std::sort(tabs.begin(), tabs.end());
        ++evaluated;
        Choice c = evaluate(pr, tabs);
        if (!c.ok) return;
        c.cost += rows;
        std::vector<Bound> tables;
        Bound trows = 0;
        for (size_t u = 0; u < nc; ++u)
          if (in[u]) {
            tables.push_back(cand[u]);
            trows += cand[u];
          }
        if (want_k == 0) {
          if (!best || c.cost < best->cost) {
            best = std::move(c);
            best_tables = std::move(tables);
          }
          return;
        }
        if (static_cast<long double>(c.cost) > cut) return;
        if (!pick || std::make_pair(trows, c.cost) <
                         std::make_pair(pick_rows, pick->cost)) {
          pick = std::move(c);
          pick_tables = std::move(tables);
          pick_rows = trows;
        }
        return;
      }
      const size_t u = nc - 1 - t;
      in[u] = false;
      dfs(t + 1, rows, cnt);
      in[u] = true;
      dfs(t + 1,
          pr.open.count(cand[u]) ? rows : rows + cand[u] * costs_.row,
          cnt + 1);
      in[u] = false;
    };
    dfs(0, 0, 0);
    const Bound least_cost = best ? best->cost : 0;
    if (best && !best_tables.empty()) {
      // C is within the margin of the least cost L when L does not beat it
      // as a default (beats_default): C (100 - margin) <= 100 L.
      cut = static_cast<long double>(least_cost) * 100 /
            (100 - kDefaultMarginPercent);
      for (want_k = 1; want_k <= best_tables.size(); ++want_k) {
        dfs(0, 0, 0);
        if (pick) break;
      }
      want_k = 0;
      if (pick) {
        best = std::move(pick);
        best_tables = std::move(pick_tables);
      }
    }
    if (!best) {
      // No subset admits an assignment: the reasons under every candidate,
      // those above a table cap included.
      std::vector<Bound> all(pr.open.begin(), pr.open.end());
      const std::vector<Bound> wide = candidate_tables(pending, true);
      all.insert(all.end(), wide.begin(), wide.end());
      std::sort(all.begin(), all.end());
      Choice c = evaluate(pr, all, true);
      fail(c.why.empty() ? "range planning of domain " + d_.name +
                               ": no subset of the candidate tables admits "
                               "every request"
                         : c.why);
    }

    // The selected assignment.
    for (const auto &[i, R] : best->sel) {
      reqs[i].realization = R;
      reqs[i].lowered = true;
    }
    for (const auto &[i, k] : best->implied_by) pl_.implied_by[i] = k;
    for (const auto &[i, w] : best->not_implied) pl_.not_implied[i] = w;
    pl_.claimed = best->claimed;
    settle_duplicates();

    std::string cl, bl;
    for (Bound b : cand) cl += (cl.empty() ? "" : ", ") + bound_str(b);
    for (Bound b : best_tables) bl += (bl.empty() ? "" : ", ") + bound_str(b);
    b_.summary().report.push_back(
        "range planning of domain " + d_.name + ": |C| = " +
        std::to_string(cand.size()) + " candidate tables {" + cl + "}, " +
        bound_str(Bound(1) << cand.size()) + " subsets, " +
        std::to_string(nodes) + " search nodes, " +
        std::to_string(evaluated) + " evaluated; tables {" + bl +
        "}, cost " + cost_str(best->cost) +
        (best->cost != least_cost
             ? ", the default within " +
                   std::to_string(kDefaultMarginPercent) +
                   " % of the least cost " + cost_str(least_cost)
             : std::string()));
    return pl_;
  }

  // A cost of the model: in ms under measured rates, else the count.
  std::string cost_str(Bound c) const {
    if (!costs_.measured) return bound_str(c);
    char b[64];
    std::snprintf(b, sizeof(b), "%.3f ms (modeled)",
                  double(c) / range_internal::kRangeUnitsPerUs / 1000);
    return b;
  }

  // Duplicates take the realization of the request they duplicate.
  void settle_duplicates() {
    auto &reqs = requests(d_);
    for (const auto &[i, f] : pl_.dup_of) {
      RangeRealization R;
      R.kind = RealizationKind::kImplied;
      R.established = reqs[f].realization.established;
      range_internal::set_plain_interval(R, R.established);
      reqs[i].realization = R;
      reqs[i].lowered = true;
    }
  }

  // The assignment of PR's requests in the tables TABS: each node's
  // independent plain requests in the order of their limits, the first
  // taking its cheapest realization and implying the others; each
  // component searched jointly (joint); then each expression implied when
  // its interval allows, else its cheapest realization. With EXPLAIN, a
  // request with no realization fails the compile naming each rejection.
  Choice evaluate(const Problem &pr, const std::vector<Bound> &tabs,
                  bool explain = false) const {
    const auto &reqs = d_.requests();
    Choice c;
    Bounds bounds = pr.base;
    auto take = [&](size_t i, const Candidate &k) {
      c.sel[i] = k.r;
      c.totals[i] = k.total;
      c.cost += k.total;
      if (k.r.bound) c.claimed.insert(*bound_node(reqs[i]));
      if (auto x = plain(reqs[i])) {
        auto it = bounds.find(*x);
        if (it == bounds.end() || k.r.established < it->second)
          bounds[*x] = k.r.established;
      }
    };
    auto none = [&](size_t i) {
      std::vector<std::string> why;
      options(i, tabs, bounds, c.claimed, &why);
      std::string msg = describe_request(reqs[i]) +
                        " has no admissible realization:";
      if (auto it = c.not_implied.find(i); it != c.not_implied.end())
        msg += "\n  implied: " + it->second;
      else if (auto jt = pl_.not_implied.find(i); jt != pl_.not_implied.end())
        msg += "\n  implied: " + jt->second;
      for (const auto &w : why) msg += "\n  " + w;
      if (explain) fail(msg);
      c.ok = false;
      c.why = msg;
    };
    for (const auto &[x, rs] : pr.indep) {
      for (size_t i : rs) {
        if (i != rs[0]) {
          const Bound E = c.sel.at(rs[0]).established;
          if (E <= limit(reqs[i])) {
            c.sel[i] = implied_at(reqs[i], E);
            c.implied_by[i] = rs[0];
            continue;
          }
        }
        const auto o = options(i, tabs, bounds, c.claimed, nullptr);
        if (o.empty()) {
          none(i);
          return c;
        }
        take(i, o[0]);
      }
    }
    for (const auto &cp : pr.comps) {
      if (!joint(cp, tabs, bounds, c, take, explain)) return c;
    }
    for (size_t i : pr.exprs) {
      if (pr.links.count(i)) {
        RangeRealization R;
        std::string why;
        if (implied(i, bounds, R, why)) {
          c.sel[i] = R;
          continue;
        }
        if (reqs[i].implied_only) {
          const std::string msg =
              describe_request(reqs[i]) + " is not implied: " + why;
          if (explain) fail(msg);
          c.ok = false;
          c.why = msg;
          return c;
        }
        if (!c.not_implied.count(i)) c.not_implied[i] = why;
      }
      const auto o = options(i, tabs, bounds, c.claimed, nullptr);
      if (o.empty()) {
        none(i);
        return c;
      }
      take(i, o[0]);
    }
    return c;
  }

  // The bytes that identify a request: its expression, bounds and kind.
  std::vector<uint8_t> signature(const RangeRequest<F> &r) const {
    std::vector<uint8_t> b;
    put_u64(b, r.v.n);
    put_u64(b, r.v.terms.size());
    for (const auto &t : r.v.terms) {
      put_u64(b, t.node);
      uint8_t e[F::kBytes];
      f_.to_bytes_field(e, t.scale);
      b.insert(b.end(), e, e + F::kBytes);
      put_u64(b, t.chain.size());
      for (const auto &op : t.chain)
        put_u64(b, uint64_t(reinterpret_cast<uintptr_t>(op.get())));
    }
    put_bound(b, r.n);
    put_bound(b, r.m);
    put_u64(b, r.interval ? 1 : 0);
    put_u64(b, r.implied_only ? 1 : 0);
    return b;
  }

  // A component's joint search in the tables TABS: the product of the
  // members' realization lists, up to max_joint_candidates combinations;
  // no two members' digits may bind one node. A combination must imply
  // every assert_range_implied expression of the component; among those,
  // the cheapest wins, counting the members' realizations and the lookup
  // of each other expression it leaves unimplied, then the one implying
  // more, then the first in the product's order. The members are then
  // selected (TAKE), and a member another member on the same value bounds
  // within its limit, and whose digits bind nothing, becomes implied.
  // False, with C.why, when no combination qualifies.
  template <class Take>
  bool joint(const Component &cp, const std::vector<Bound> &tabs,
             const Bounds &outer, Choice &c, Take &take, bool explain) const {
    const auto &reqs = d_.requests();
    const auto &members = cp.members;
    std::vector<std::vector<Candidate>> cand;
    for (size_t m : members) {
      cand.push_back(options(m, tabs, outer, c.claimed, nullptr));
      if (cand.back().empty()) {
        std::vector<std::string> why;
        options(m, tabs, outer, c.claimed, &why);
        std::string msg = describe_request(reqs[m]) +
                          " has no admissible realization:";
        for (const auto &w : why) msg += "\n  " + w;
        if (explain) fail(msg);
        c.ok = false;
        c.why = msg;
        return false;
      }
    }
    // The cost of looking an expression up when no combination implies it
    // (its cheapest realization; an expression with none counts as large,
    // above any total of the cost model's units).
    std::map<size_t, Bound> lookup;
    for (size_t e : cp.exprs) {
      if (reqs[e].implied_only) continue;
      const auto o = options(e, tabs, outer, c.claimed, nullptr);
      lookup[e] = o.empty() ? Bound(1) << 80 : o[0].total;
    }
    std::vector<size_t> idx(members.size(), 0);
    std::optional<std::vector<size_t>> best;
    Bound best_cost = 0;
    size_t best_held = 0, seen = 0;
    bool truncated = false;
    for (;;) {
      if (seen++ >= pol_.max_joint_candidates) {
        truncated = true;
        break;
      }
      Bounds bounds = outer;
      Bound cost = 0;
      std::set<size_t> binds;
      bool clash = false;
      for (size_t k = 0; k < members.size(); ++k) {
        const auto &o = cand[k][idx[k]];
        const size_t x = *plain(reqs[members[k]]);
        auto it = bounds.find(x);
        if (it == bounds.end() || o.r.established < it->second)
          bounds[x] = o.r.established;
        cost += o.total;
        if (o.r.bound && !binds.insert(x).second) clash = true;
      }
      size_t held = 0;
      bool required = !clash;
      for (size_t e : cp.exprs) {
        if (!required) break;
        RangeRealization r;
        std::string why;
        const bool ok = implied(e, bounds, r, why);
        held += ok ? 1 : 0;
        if (!ok && reqs[e].implied_only) required = false;
        if (!ok && !reqs[e].implied_only) cost += lookup.at(e);
      }
      if (required &&
          (!best || cost < best_cost || (cost == best_cost && held > best_held))) {
        best = idx;
        best_cost = cost;
        best_held = held;
      }
      size_t k = 0;
      while (k < idx.size() && ++idx[k] == cand[k].size()) {
        idx[k] = 0;
        ++k;
      }
      if (k == idx.size()) break;
    }
    if (!best) {
      std::string msg;
      for (size_t e : cp.exprs)
        if (reqs[e].implied_only) {
          msg = describe_request(reqs[e]) +
                " is implied by no combination of its terms' realizations; "
                "members:";
          break;
        }
      for (size_t k = 0; k < members.size(); ++k) {
        msg += "\n  " + reqs[members[k]].name + ": candidate bounds";
        for (const auto &o : cand[k])
          msg += " " + bound_str(o.r.established) + " (" +
                 realization_name(o.r.kind) + ")";
      }
      if (truncated)
        msg += "\n  (search stopped at max_joint_candidates = " +
               std::to_string(pol_.max_joint_candidates) + ")";
      if (explain) fail(msg);
      c.ok = false;
      c.why = msg;
      return false;
    }
    if (truncated)
      for (size_t e : cp.exprs)
        c.not_implied[e] = "search stopped at max_joint_candidates = " +
                           std::to_string(pol_.max_joint_candidates);
    for (size_t k = 0; k < members.size(); ++k)
      take(members[k], cand[k][(*best)[k]]);
    // Members on one value: the least established bound implies the
    // others within their limits.
    std::map<size_t, std::vector<size_t>> on;
    for (size_t m : members) on[*plain(reqs[m])].push_back(m);
    for (auto &[x, rs] : on) {
      if (rs.size() < 2) continue;
      std::stable_sort(rs.begin(), rs.end(), [&](size_t a, size_t b) {
        return c.sel.at(a).established < c.sel.at(b).established;
      });
      const Bound N0 = c.sel.at(rs[0]).established;
      for (size_t k = 1; k < rs.size(); ++k) {
        const RangeRealization &R = c.sel.at(rs[k]);
        if (R.bound || R.kind == RealizationKind::kImplied) continue;
        if (N0 > limit(reqs[rs[k]])) continue;
        c.cost -= c.totals.at(rs[k]);
        c.totals.erase(rs[k]);
        c.sel[rs[k]] = implied_at(reqs[rs[k]], N0);
        c.implied_by[rs[k]] = rs[0];
      }
    }
    return true;
  }

  // ------------------------------------------------------------ emitter --

  Lin<F> constant(const std::string &nm, size_t n, Bound value) {
    return Lin<F>(d_.constant(nm, std::vector<Elt>(n, elt_of_nat(f_, value))));
  }
  Ref<F> derive(const std::string &nm, const Lin<F> &e) {
    return d_.derive(nm, e);
  }

  // Digits j < k of to_nat(x) in base T, or of top - to_nat(x) when TOP is
  // set (two-sided), by range_internal::digit (branch-free).
  // OFF: the offsets c of an x + c request whose digits bind x (digits of
  // x + c, computed from x alone).
  std::vector<Ref<F>> digits(const RangeRequest<F> &r, Ref<F> x,
                             const std::string &stem, unsigned k, Bound T,
                             std::optional<Bound> top, bool late,
                             const std::vector<Bound> &off = {}) {
    std::vector<Ref<F>> out;
    // The generators' integers are NatInts: the digits of a value of a
    // field wider than 128 bits (F_p256) exist only for a request whose
    // values, offsets and two-sided top fit 128 bits.
    if (!p_.fits128() && !(r.interval ? r.m : r.n).fits128())
      fail("range request '" + r.name + "': its digits decompose values up to " +
           bound_str((r.interval ? r.m : r.n) - 1) +
           ", beyond the 128-bit integers witness generation reads");
    const NatInt p = nat_modulus(p_);
    const range_internal::PublicDivisor div(nat_cast(T), p);
    const std::optional<NatInt> ntop =
        top ? std::optional<NatInt>(nat_cast(*top)) : std::nullopt;
    std::vector<NatInt> noff;
    for (const Bound &c : off) noff.push_back(nat_cast(c));
    for (unsigned j = 0; j < k; ++j) {
      auto digit = [p, j, div, ntop](NatInt a) {
        return range_internal::digit(a, j, div, ntop, p);
      };
      const std::string nm = "range." + r.name + "." + stem + std::to_string(j);
      auto decl = [&](auto fn) -> Ref<F> {
        if (d_.prime == Space::kField)
          return priv(d_, Field{}, nm, Shape(x.dims()), depends_on(x), nat(fn));
        return priv(d_, Subfield{}, nm, Shape(x.dims()), depends_on(x), nat(fn));
      };
      Ref<F> dj =
          off.empty()
              ? decl(digit)
              : decl([digit, noff, p](const Tensor<NatInt> &a) {
                  std::vector<NatInt> o(a.size());
                  for (size_t i = 0; i < a.size(); ++i)
                    o[i] = digit(ct::add_mod(a[i], noff[i], p));
                  return o;
                });
      out.push_back(dj);
    }
    return out;
  }
  Lin<F> radix_sum(const std::vector<Ref<F>> &dig, Bound T) const {
    Lin<F> s;
    Bound w = 1;
    for (size_t j = 0; j < dig.size(); ++j) {
      Lin<F> t = elt_of_nat(f_, w) * dig[j];
      s = j == 0 ? t : s + t;
      if (j + 1 < dig.size()) w = bound_mul(w, T);
    }
    return s;
  }
  static std::string radix_note(const std::vector<Ref<F>> &dig, Bound T) {
    std::string s;
    for (size_t j = 0; j < dig.size(); ++j) {
      if (j) s += " + ";
      if (j == 1) s += bound_str(T) + "*";
      if (j > 1) s += bound_str(T) + "^" + std::to_string(j) + "*";
      s += "d" + std::to_string(j);
    }
    return s + " (range)";
  }

  // The nodes a realization's derivation reads: the direct or complement
  // needle, the value V the digits LO decompose, the two-sided digits HI and
  // top constant TOP; OFFSET for digits that bind x of an x + c request.
  struct DerivNodes {
    size_t needle = SIZE_MAX, value = SIZE_MAX, top = SIZE_MAX;
    // The node the digits bind (R.bound): v, or x of an x + c request.
    size_t bound = SIZE_MAX;
    std::vector<size_t> lo, hi;
  };

  // Records the derivation of request R's in predicate (compiler/
  // derivation.h) from its realization: its needles' lookups, each into a
  // range table [0, T); then
  //   direct: the needle's range (moved from a derived needle to the
  //     record through its definition);
  //   digits: the reconstruction row (or the binding of the value to its
  //     digits) as record = sum_j T^j d_j, so record < T^k;
  //   two-sided: that, and the top row as (n - 1) - record = sum_j T^j h_j,
  //     so (n - 1) - record < T^k too, and with 2 T^k - 1 <= p, record < n.
  // A realization whose argument the rules do not state (the complement,
  // the digits of x + c) records a gap.
  void record_derivation(const RangeRequest<F> &r, const DerivNodes &dn) {
    const RangeRealization &R = r.realization;
    Deriv dv(r.name, d_.name);
    const auto rec = dx::side(r.name, 0);
    const SignedInt T(R.table);
    auto lookups = [&](size_t first, const std::vector<size_t> &ds) {
      std::vector<size_t> out;
      for (size_t j = 0; j < ds.size(); ++j)
        out.push_back(dv.range_nat(dv.lookup(r.name, first + j)));
      return out;
    };
    // sum_j T^j d_j over the nodes DS.
    auto radix = [&](const std::vector<size_t> &ds) {
      dx::E s;
      SignedInt w(1);
      for (size_t j = 0; j < ds.size(); ++j) {
        dx::E t = j == 0 ? dx::leaf(ds[j]) : dx::scale(w, dx::leaf(ds[j]));
        s = j == 0 ? t : dx::add(std::move(s), std::move(t));
        w = w * T;
      }
      return s;
    };
    // eq E sum_j T^j d_j from the row ROW (E - sum = 0 with the value v
    // read for the record), or from the binding of v to its digits.
    auto radix_eq = [&](const std::string &row, dx::E e,
                        const std::vector<size_t> &ds, SignedInt sign) {
      const bool plain_v = plain(r).has_value();
      std::vector<std::pair<size_t, SignedInt>> ps;
      if (row.empty()) {
        // The bound node's definition is the sum (minus the request's
        // constants for x of x + c).
        ps.push_back({dv.subst(dx::leaf(dn.bound), dx::def(dn.bound)), 1});
      } else {
        ps.push_back({dv.realized(row, true), 1});
        if (!plain_v)
          ps.push_back({dv.subst(dx::leaf(dn.value), dx::def(dn.value)), sign});
      }
      return dv.linear(std::move(ps), std::move(e), radix(ds));
    };
    switch (R.kind) {
      case RealizationKind::kDirect: {
        const size_t n = dv.range_nat(dv.lookup(r.name, 0));
        if (plain(r)) {
          dv.conclude(n);
        } else {
          const size_t s = dv.subst(dx::leaf(dn.needle), dx::def(dn.needle));
          dv.conclude(dv.transport(s, n));
        }
        break;
      }
      case RealizationKind::kDigits:
      case RealizationKind::kTwoSided: {
        if (R.bound && !plain(r) && dn.bound == dn.value) {
          dv.gap("the digits bind a derived value of the record, which no "
                 "predicate relates to the record");
          break;
        }
        const std::vector<size_t> nd = lookups(0, dn.lo);
        const size_t ea = radix_eq(R.bound ? std::string() : R.recon_row, rec,
                                   dn.lo, SignedInt(-1));
        const size_t na = dv.digits(ea, nd, R.table);
        if (R.kind == RealizationKind::kDigits) {
          dv.conclude(na);
          break;
        }
        const std::vector<size_t> nh = lookups(dn.lo.size(), dn.hi);
        // X = (n - 1) - record < T^k, so record + X = n - 1 with both
        // below T^k <= p: record < n.
        const dx::E X = dx::sub(dx::leaf(dn.top), rec);
        const size_t eb = radix_eq(R.top_row, X, dn.hi, SignedInt(1));
        const size_t nb = dv.digits(eb, nh, R.table);
        dv.conclude(dv.nat_comp(na, nb));
        break;
      }
      case RealizationKind::kComplement: {
        // The needle (n - 1) - record < T; the record in [lo, hi] by its
        // terms' intervals, lo >= 0 and hi + T < p (the certified
        // complementLow, complementHigh): record < n.
        const size_t n = dv.range_nat(dv.lookup(r.name, 0));
        const size_t s = dv.subst(dx::leaf(dn.needle), dx::def(dn.needle));
        const size_t x = dv.transport(s, n);
        std::map<size_t, size_t> done;
        std::map<size_t, IvlWhy> why;
        std::vector<size_t> nodes;
        const Graph &g = b_.system().graph();
        const std::function<bool(size_t)> in_prime = range_internal::prime_node(d_, g);
        for (const auto &t : r.v.terms) {
          nodes.push_back(t.node);
          IvlWhy w;
          if (range_internal::request_bound(d_, g, p_, t.node, &w) &&
              !(w.kind == IvlWhy::kRequest && w.request == r.name)) {
            why[t.node] = std::move(w);
          } else if (const auto *src = d_.view_sources(t.node)) {
            // The request itself bounds its record: the view's sources'.
            IvlWhy v;
            v.kind = IvlWhy::kViews;
            std::set<size_t> seen;
            for (const auto &[sn, k] : *src) {
              if (sn == kZeroCoordinate || !seen.insert(sn).second) continue;
              IvlWhy ws;
              if (!range_internal::request_bound(d_, g, p_, sn, &ws) && in_prime(sn))
                ws.kind = IvlWhy::kPrime;
              v.sources.push_back({sn, std::move(ws)});
            }
            why[t.node] = std::move(v);
          } else if (in_prime(t.node) && g.nodes.at(t.node).kind != Kind::kConstant) {
            why[t.node].kind = IvlWhy::kPrime;
          }
        }
        // A record that is one node with a range request of its own takes
        // that request's range directly.
        size_t nr = SIZE_MAX;
        if (r.v.terms.size() == 1 && r.v.terms[0].chain.empty() &&
            r.v.terms[0].scale == f_.one()) {
          auto it = why.find(r.v.terms[0].node);
          if (it != why.end() && it->second.kind == IvlWhy::kRequest &&
              !it->second.offset && it->second.request != r.name)
            nr = dv.inline_request(it->second.request);
        }
        if (nr == SIZE_MAX)
          nr = dv.nat_ivl(dv.ivl_expr(ivl_premises(dv, g, nodes, why, done), rec,
                                      R.lo, R.hi));
        dv.conclude(dv.nat_comp(nr, x));
        break;
      }
      default:
        dv.gap(std::string("the ") + realization_name(R.kind) +
               " realization has no derivation");
    }
    dv.commit(b_.records());
  }

  // The realizations of PL's requests: digits, needle views and their
  // rows. Returns the needles, for the tables.
  std::vector<Needle> emit(const std::vector<size_t> &todo, const Plan &pl) {
    auto &reqs = requests(d_);
    auto &sum = b_.summary();
    auto &descr = sum.descr;
    const auto &N = b_.system().graph().nodes;
    std::vector<Needle> needles;
    put_str(descr, d_.name);
    put_u64(descr, todo.size());
    for (size_t i : todo) {
      RangeRequest<F> &r = reqs[i];
      const RangeRealization &R = r.realization;
      const auto x = plain(r);
      const bool late = [&] {
        size_t ph = 0;
        for (size_t id : r.v.deps()) ph = std::max(ph, pl.phase.at(id));
        return ph >= 1;
      }();
      const size_t first_needle = needles.size();
      r.realization.late = late;
      if (R.kind == RealizationKind::kImplied) {
        put_str(descr, r.name);
        put_u64(descr, static_cast<uint64_t>(R.kind));
        put_bound(descr, R.established);
        put_bound(descr, r.n);
        put_bound(descr, r.m);
        put_bound(descr, static_cast<Bound>(R.lo));
        put_bound(descr, static_cast<Bound>(R.hi));
        std::string by;
        if (auto it = pl.dup_of.find(i); it != pl.dup_of.end())
          by = " (a duplicate of '" + reqs[it->second].name + "')";
        else if (auto jt = pl.implied_by.find(i); jt != pl.implied_by.end())
          by = " (by '" + reqs[jt->second].name + "' on the same value)";
        else if (pl.by_type.count(i))
          by = " (by the value's type)";
        put_u64(descr, pl.dup_of.count(i) ? 1 : pl.implied_by.count(i) ? 2
                                          : pl.by_type.count(i)      ? 3
                                                                   : 0);
        sum.report.push_back(r.name + ": implied" + by + ", interval [" +
                             int_str(R.lo) + ", " + int_str(R.hi) +
                             "] -> bound " + bound_str(R.established) +
                             "; no needles, coordinates or rows");
        // A request only interval propagation realizes (assert_range_implied)
        // has its derivation from the lowering that made it.
        if (!r.implied_only) {
          Deriv dv(r.name, d_.name);
          dv.gap("the implied realization's interval sources are not "
                 "recorded");
          dv.commit(b_.records());
        }
        continue;
      }
      // R7: needles are circuit-readable.
      for (const auto &t : r.v.terms)
        for (const auto &op : t.chain)
          if (!op->emit || !op->deps.empty())
            fail(describe_request(r) + ": its needle applies the operator '" +
                 op->name + "', which has no circuit expansion "
                 "(OpSpec::emit), so the lookup circuit cannot read it");
      certify_realization(r, R, pl);
      auto value = [&]() -> Ref<F> {
        if (x) return ref_of(d_, *x);
        return derive("range." + r.name + ".value", r.v);
      };
      std::string line = r.name + ": " + realization_name(R.kind) +
                         " T=" + bound_str(R.table);
      put_str(descr, r.name);
      put_u64(descr, static_cast<uint64_t>(R.kind));
      put_bound(descr, R.table);
      put_u64(descr, R.k);
      put_bound(descr, R.established);
      put_bound(descr, r.n);
      put_bound(descr, r.m);
      // What the derivation reads (record_derivation): the needle, the
      // value, the digits, the two-sided top constant.
      DerivNodes dn;
      switch (R.kind) {
        case RealizationKind::kDirect: {
          Ref<F> nd = x ? ref_of(d_, *x) : derive("range." + r.name + ".needle", r.v);
          needles.push_back({nd, R.table, r.n});
          dn.needle = nd.id;
          break;
        }
        case RealizationKind::kComplement: {
          // n - 1 - v in [0, T), with v in [lo, hi], lo >= 0, hi + T < p.
          const Lin<F> topc = constant("range." + r.name + ".top", r.v.n, r.n - 1);
          Ref<F> nd = derive("range." + r.name + ".needle", topc - r.v);
          needles.push_back({nd, R.table, r.n});
          dn.needle = nd.id;
          dn.top = topc.terms.at(0).node;
          line += " (n - 1 - v, v in [" + int_str(R.lo) + ", " +
                  int_str(R.hi) + "])";
          put_bound(descr, Bound(R.hi));
          break;
        }
        default: {  // digits, two-sided
          // x + c with x bound: digits of x + c from x, and x = digits - c.
          const auto ox = R.bound && !x ? offset_node(r) : std::nullopt;
          std::vector<Ref<F>> lo;
          Ref<F> v;
          if (ox) {
            const Ref<F> xr = ref_of(d_, *ox);
            std::vector<Bound> off;
            Lin<F> cst;
            for (const auto &c : offsets(r)) off.push_back(nat_of(f_, c));
            for (const auto &t : r.v.terms)
              if (t.node != *ox) {
                Lin<F> tl;
                tl.f = &f_;
                tl.n = t.in_n;
                tl.terms = {t};
                cst = cst.terms.empty() ? tl : cst + tl;
              }
            lo = digits(r, xr, "d", R.k, R.table, std::nullopt, late, off);
            bind_view(d_, xr, radix_sum(lo, R.table) - cst,
                      radix_note(lo, R.table) + " - c");
            r.realization.bound_id = *ox;
            r.realization.bound_offset = true;
            dn.bound = *ox;
            line += " k=" + std::to_string(R.k) + "; '" + N.at(*ox).name +
                    "' bound to the digits of itself + c (no cell)";
            v = value();
          } else {
            v = value();
            lo = digits(r, v, "d", R.k, R.table, std::nullopt, late);
          }
          for (const auto &dj : lo) needles.push_back({dj, R.table, R.table});
          dn.value = v.id;
          for (const auto &dj : lo) dn.lo.push_back(dj.id);
          if (ox) {
          } else if (R.bound) {
            bind_view(d_, v, radix_sum(lo, R.table), radix_note(lo, R.table));
            r.realization.bound_id = v.id;
            dn.bound = v.id;
            line += " k=" + std::to_string(R.k) + "; '" + N.at(v.id).name +
                    "' bound to its digits (no cell)";
          } else {
            d_.affine("range." + r.name + ".reconstruct",
                      v - radix_sum(lo, R.table));
            r.realization.recon_row = "range." + r.name + ".reconstruct";
            line += " k=" + std::to_string(R.k) + "; reconstruction row";
          }
          put_u64(descr, R.bound ? 1 : 0);
          put_u64(descr, v.id);
          for (const auto &dj : lo) put_u64(descr, dj.id);
          if (R.kind == RealizationKind::kTwoSided) {
            auto hi = digits(r, v, "h", R.k, R.table, r.n - 1, late);
            for (const auto &hj : hi) {
              needles.push_back({hj, R.table, R.table});
              put_u64(descr, hj.id);
              dn.hi.push_back(hj.id);
            }
            const Lin<F> topc =
                constant("range." + r.name + ".top", r.v.n, r.n - 1);
            dn.top = topc.terms.at(0).node;
            d_.affine("range." + r.name + ".top",
                      topc - v - radix_sum(hi, R.table));
            r.realization.top_row = "range." + r.name + ".top";
          }
          break;
        }
      }
      put_u64(descr, R.bound ? 1 : 0);
      record_derivation(r, dn);
      for (size_t k = first_needle; k < needles.size(); ++k) {
        needles[k].req = i;
        r.realization.needle_ids.push_back(needles[k].ref.id);
      }
      line += " -> bound " + bound_str(R.established) + "; " +
              std::to_string(R.needles) + " needles and " +
              std::to_string(R.coords) + " new coordinates per coordinate (" +
              std::to_string(r.v.n) + " coordinates)";
      if (auto it = pl.not_implied.find(i); it != pl.not_implied.end())
        line += "; not implied: " + it->second;
      sum.report.push_back(line);
    }
    return needles;
  }

  // One range group of a table: coordinate ranges [b, e) of its needles,
  // static first, and its histograms.
  struct Slice {
    Ref<F> ref;
    size_t b = 0, e = 0;
    bool late = false;
    Bound honest = 0;
    size_t req = SIZE_MAX;
  };
  struct Group {
    std::vector<Slice> slices;
    size_t nst = 0, ndy = 0;
    Bound s_dyn = 0;
    bool merged = false;  // one late histogram of T counts every needle
    Ref<F> m0, m1;
  };

  // The needles per range group of table T: the least of p - 1 (each
  // honest count stays below p), the screen's (the largest n with
  // (n + 2T - 1) / |K| <= 2^-group_error_bits) and the profile's override.
  size_t group_capacity(Bound T) const {
    Bound cap = p_ - 1;
    const double log2K =
        range_internal::log2_bound(p_) * (F::kBytes / domain_subfield<F>::kBytes);
    const double screen = log2K - pol_.group_error_bits;
    if (screen < 120) {
      const double n = std::floor(std::exp2(screen)) - double(2 * T - 1);
      cap = std::min<Bound>(cap, n < 1 ? Bound(1) : Bound(n));
    }
    if (pol_.group_capacity != 0) cap = std::min<Bound>(cap, pol_.group_capacity);
    return size_t(std::min<Bound>(cap, Bound(SIZE_MAX)));
  }

  // The groups of table T over NEEDLES: phase-0 needles fill the groups
  // first, the late ones the last groups; a needle may span two groups.
  // A group with static and late needles gets one late histogram of T
  // counts when that costs less than m0 (T) and m1 (S_dyn), each count a
  // committed coordinate and each late one also a message element:
  // 2T < T + 2 S_dyn.
  std::vector<Group> group_needles(Bound T, const std::vector<Needle> &needles,
                                   const std::vector<size_t> &phase) const {
    std::vector<Slice> order;
    for (int late = 0; late < 2; ++late)
      for (const auto &nd : needles)
        if (nd.table == T && (phase.at(nd.ref.id) != 0) == bool(late))
          order.push_back({nd.ref, 0, nd.ref.n, bool(late), nd.honest, nd.req});
    const size_t cap = group_capacity(T);
    std::vector<Group> out(1);
    size_t room = cap;
    for (Slice sl : order) {
      size_t at = 0;
      while (at < sl.ref.n) {
        if (room == 0) {
          out.emplace_back();
          room = cap;
        }
        const size_t take = std::min(room, sl.ref.n - at);
        Slice part = sl;
        part.b = at;
        part.e = at + take;
        Group &g = out.back();
        g.slices.push_back(part);
        (sl.late ? g.ndy : g.nst) += take;
        if (sl.late) g.s_dyn = std::max(g.s_dyn, sl.honest);
        at += take;
        room -= take;
      }
    }
    for (auto &g : out)
      g.merged = g.nst != 0 && g.ndy != 0 && 2 * T < T + 2 * g.s_dyn;
    return out;
  }

  // Histograms, alpha, weights and one fraction-tree circuit per group of
  // each table.
  void tables(const std::vector<Needle> &needles) {
    auto &s = b_.system();
    auto &sum = b_.summary();
    const auto phase = b_.phases();
    std::vector<Bound> Ts;
    for (const auto &nd : needles)
      if (std::find(Ts.begin(), Ts.end(), nd.table) == Ts.end())
        Ts.push_back(nd.table);
    std::sort(Ts.begin(), Ts.end());
    struct Table {
      Bound T;
      std::vector<Group> groups;
      Ref<F> w;
    };
    std::vector<Table> tabs;
    const F *pf = &f_;
    size_t largest = 0;
    for (Bound T : Ts) {
      Table t;
      t.T = T;
      t.groups = group_needles(T, needles, phase);
      // Each request's group: the one holding its first needle coordinate.
      {
        std::set<size_t> seen;
        auto &reqs = requests(d_);
        for (size_t k = 0; k < t.groups.size(); ++k)
          for (const auto &sl : t.groups[k].slices)
            if (sl.req != SIZE_MAX && seen.insert(sl.req).second)
              reqs[sl.req].realization.group = k;
      }
      if (T >= (Bound(1) << 32))
        fail("range table " + bound_str(T) + " of domain " + d_.name +
             ": the oblivious histogram takes tables below 2^32");
      const std::string tag = d_.name + "." + bound_str(T);
      // A table above the policy's cap, which a max_table raised.
      if (T > pol_.max_table) {
        std::string names;
        for (const auto &r : d_.requests())
          if (r.realization.table == T &&
              r.realization.kind != RealizationKind::kImplied)
            names += (names.empty() ? "'" : ", '") + r.name + "'";
        sum.report.push_back("warning: range table " + tag + " has " +
                             bound_str(T) + " rows, above the cap " +
                             bound_str(pol_.max_table) + " (max_table: " +
                             names + ")");
      }
      const bool split = t.groups.size() > 1;
      for (size_t k = 0; k < t.groups.size(); ++k) {
        const Group &g = t.groups[k];
        largest = std::max(largest, g.nst + g.ndy);
        // Each group's honest counts stay below p (its needles), and the
        // dynamic histogram's support lies in the table (R4).
        const std::string gn = "range.table:" +
                               (split ? tag + ".g" + std::to_string(k) : tag);
        s.note("certify", gn + ".counts", term("needles", Bound(g.nst + g.ndy)) < term("p", p_), d_);
        s.note("certify", gn + ".support", term("S_dyn", g.s_dyn) <= term("T", T), d_);
      }
      for (size_t k = 0; k < t.groups.size(); ++k) {
        Group &g = t.groups[k];
        const std::string gt = split ? tag + ".g" + std::to_string(k) : tag;
        // The histograms (range_internal::histogram over the group's
        // coordinate ranges, oblivious). An out-of-table needle is not
        // counted; the identity then fails and the prover's satisfaction
        // check or the verifier rejects. Their type is the digits'
        // (Subfield, or Field in a prime field).
        auto counts = [&](const std::string &nm, Bound size,
                          const std::vector<Slice> &sl) -> Ref<F> {
          std::vector<Ref<F>> refs;
          std::vector<std::pair<size_t, size_t>> rg;
          for (const auto &x : sl) {
            refs.push_back(x.ref);
            rg.push_back({x.b, x.e});
          }
          auto fn = [pf, size, rg](const std::vector<const std::vector<Elt> *> &in) {
            std::vector<std::vector<Elt>> part(in.size());
            std::vector<const std::vector<Elt> *> ptr(in.size());
            for (size_t j = 0; j < in.size(); ++j) {
              part[j].assign(in[j]->begin() + long(rg[j].first),
                             in[j]->begin() + long(rg[j].second));
              ptr[j] = &part[j];
            }
            return range_internal::histogram(*pf, size, ptr);
          };
          if (d_.prime == Space::kField)
            return priv(d_, Field{}, nm, static_cast<size_t>(size), refs, fn);
          return priv(d_, Subfield{}, nm, static_cast<size_t>(size), refs, fn);
        };
        std::vector<Slice> st, dy;
        for (const auto &x : g.slices) (x.late ? dy : st).push_back(x);
        if (g.merged) {
          g.m1 = counts("range.dynamic:" + gt, T, g.slices);
        } else {
          if (!st.empty()) g.m0 = counts("range.static:" + gt, T, st);
          if (!dy.empty())
            g.m1 = counts("range.dynamic:" + gt, g.s_dyn, dy);
        }
      }
      tabs.push_back(std::move(t));
    }
    // Tests every needle and histogram (inferred from the lookups). Alpha
    // is uniform outside U = [0, T_max), the union of the tables [0, T), so
    // every weight (alpha - j)^-1 is defined and the honest identity holds
    // at every alpha drawn (perfect completeness). It is the domain's one
    // LogUp challenge alpha:<D>: when the assert_in lowering declared it,
    // its sampler reads T_max from logup_tmax, and its phase, inferred from
    // every lookup that reads it, is the later of the two.
    Bound tmax = 0;
    for (const auto &t : tabs) tmax = std::max(tmax, t.T);
    const std::string an = "alpha:" + d_.name;
    auto &shared = logup_alpha(d_);
    const bool joined = shared.has_value();
    if (!joined) {
      shared = d_.challenge_outside(
          an, {}, [pf, tmax](const ValueReader &) {
            return std::function<bool(const Elt &)>([pf, tmax](const Elt &x) {
              return range_internal::in_range_table(*pf, x, tmax);
            });
          });
      realization(d_, *shared);
    } else {
      set_sampler(d_, *shared, "field-minus-tables");
    }
    const Ref<F, Field, Public> alpha = *shared;
    *logup_tmax(d_) = tmax;
    {
      auto &exs = b_.records().excluded;
      auto it = std::find_if(exs.begin(), exs.end(), [&](const auto &e) {
        return e.challenge == an;
      });
      if (it == exs.end()) {
        PlanRecords::Excluded ex;
        ex.challenge = an;
        exs.push_back(std::move(ex));
        it = exs.end() - 1;
      }
      it->range = tmax;
    }
    sum.report.push_back(an + ": drawn outside [0, " + bound_str(tmax) + ")");
    // The degree charged for alpha's event: each table's T and, per group,
    // N + T - 1 (the fraction identity). Alpha is uniform in K minus U, so
    // the event's probability is sum_g (N_g + T - 1) / (|K| - |U|) (the
    // groups' identities, no pole). The charge keeps the T of each table,
    // read over |K|: with A = sum_g (N_g + T - 1) and P = sum T >= |U|,
    // A / (|K| - |U|) <= (A + P) / |K| whenever A + P <= |K| (otherwise
    // the charge bounds nothing), so the charge over |K| still bounds the
    // event. A shared alpha's charge is the sum of the two lowerings':
    // its event is the union of theirs, and U is this lowering's set.
    {
      Bound charge = 0, exact = 0;
      for (const auto &t : tabs) {
        charge = bound_add(charge, t.T);
        for (const auto &g : t.groups) {
          charge = bound_add(charge, Bound(g.nst + g.ndy) + t.T - 1);
          exact = bound_add(exact, Bound(g.nst + g.ndy) + t.T - 1);
        }
      }
      auto &chs = b_.records().charges;
      auto it = std::find_if(chs.begin(), chs.end(), [&](const auto &c) {
        return c.label == an;
      });
      if (it == chs.end()) {
        chs.push_back({an, charge, exact});
      } else {
        it->exact = bound_add(it->exact.value_or(it->degree), exact);
        it->degree = bound_add(it->degree, charge);
      }
    }
    auto &stats = range_tables(d_);
    for (auto &t : tabs) {
      const Bound T = t.T;
      const std::string tag = d_.name + "." + bound_str(T);
      t.w = d_.pub(Field{}, "range.weights:" + tag, static_cast<size_t>(T),
          depends_on(alpha), computes("inverse_table", {uint64_t(T)}),
          [pf, T](const std::vector<Elt> &a) {
            std::vector<Elt> w(static_cast<size_t>(T));
            for (size_t j = 0; j < w.size(); ++j) {
              const Elt d = pf->subf(a[0], pf->of_scalar(j));
              // Alpha is drawn outside [0, T) (challenge_outside above).
              if (d == pf->zero())
                throw std::logic_error("range weights: alpha on a table point");
              w[j] = pf->invertf(d);
            }
            return w;
          });
      const bool split = t.groups.size() > 1;
      if (split) {
        std::string sizes;
        for (const auto &g : t.groups)
          sizes += (sizes.empty() ? "" : ", ") + std::to_string(g.nst + g.ndy);
        sum.report.push_back("table " + tag + ": " +
                             std::to_string(t.groups.size()) +
                             " groups of at most " +
                             std::to_string(group_capacity(T)) +
                             " needles (" + sizes + "), one alpha and one "
                             "weight table");
      }
      for (size_t k = 0; k < t.groups.size(); ++k) {
        Group &g = t.groups[k];
        const std::string gt = split ? tag + ".g" + std::to_string(k) : tag;
        // Reads: needles (static, then dynamic), m0, m1, weights, alpha.
        std::vector<Ref<F>> rd;
        std::vector<std::pair<size_t, size_t>> rg;
        for (const auto &x : g.slices) {
          rd.push_back(x.ref);
          rg.push_back({x.b, x.e});
        }
        const size_t nn = rd.size();
        const bool has0 = g.m0.f != nullptr, has1 = g.m1.f != nullptr;
        if (has0) rd.push_back(g.m0);
        if (has1) rd.push_back(g.m1);
        rd.push_back(t.w);
        rd.push_back(alpha);
        // The closure's key (the compile cache): its needle slices and
        // multiplicities.
        std::vector<uint8_t> key;
        put_str(key, "range.lookup");
        put_u64(key, nn);
        put_u64(key, (has0 ? 1 : 0) | (has1 ? 2 : 0));
        for (const auto &[b, e] : rg) {
          put_u64(key, b);
          put_u64(key, e);
        }
        gkr(d_, "range.lookup:" + gt, rd,
               [nn, has0, has1, rg](const auto &lc, const auto &w) {
                 fraction_tree(lc, w, nn, rg, has0, has1);
               },
               key);
        const Bound sd = g.merged ? T : g.s_dyn;
        stats.push_back(RangeTableStats{T, g.nst, g.ndy, sd, alpha.id,
                                        has0 ? g.m0.id : SIZE_MAX,
                                        has1 ? g.m1.id : SIZE_MAX, k, gt,
                                        group_capacity(T), g.merged});
        stats.back().circuit = "range.lookup:" + gt;
        for (const auto &sl : g.slices)
          stats.back().members.push_back({sl.req, sl.ref.id, sl.b, sl.e});
        put_bound(sum.descr, T);
        put_u64(sum.descr, g.nst);
        put_u64(sum.descr, g.ndy);
        put_bound(sum.descr, sd);
        if (split || g.merged) {
          put_u64(sum.descr, k);
          put_u64(sum.descr, g.merged ? 1 : 0);
        }
        std::string hist;
        if (g.merged)
          hist = "one late histogram of " + bound_str(T) +
                 " (cheaper than m0 and m1)";
        else
          hist = std::string("m0 ") +
                 (has0 ? bound_str(T) : std::string("none")) + ", m1 " +
                 (has1 ? bound_str(g.s_dyn) : std::string("none"));
        sum.report.push_back(
            "table " + gt + ": " + std::to_string(g.nst) + " static and " +
            std::to_string(g.ndy) + " dynamic needles; " + hist);
      }
    }
    if (largest != 0) {
      bool any_split = false;
      for (const auto &t : tabs) any_split = any_split || t.groups.size() > 1;
      if (any_split)
        sum.report.push_back(an +
                             ": the groups share alpha; the largest has " +
                             std::to_string(largest) + " needles");
    }
  }

  // The log-derivative identity (log_derivative.h) over the needles'
  // coordinates RG[k] of read k. W holds the needles' wires (NN reads),
  // then m0 and m1 when present, the weights and alpha.
  template <class LC, class W>
  static void fraction_tree(const LC &lc, const W &w, size_t nn,
                            const std::vector<std::pair<size_t, size_t>> &rg,
                            bool has0, bool has1) {
    using Wires = std::decay_t<decltype(w[0])>;
    size_t at = nn;
    std::vector<const Wires *> counts;
    if (has0) counts.push_back(&w[at++]);
    if (has1) counts.push_back(&w[at++]);
    const auto &wt = w[at++];
    const size_t alpha = w[at][0];
    std::vector<size_t> needles;
    for (size_t k = 0; k < nn; ++k)
      for (size_t i = rg[k].first; i < rg[k].second; ++i)
        needles.push_back(w[k][i]);
    assert_log_derivative(lc, needles, alpha, counts, wt);
  }

  D &d_;
  ConstraintSystemBuilder<S> &b_;
  const F &f_;
  const RangePolicy &pol_;
  // The cost model of the domain's rates (range_internal::RangeCosts).
  const range_internal::RangeCosts costs_;
  // The characteristic.
  Bound p_ = 0;
  Plan pl_;  // the plan in progress (plan() returns it)
};

template <class F, class S>
void lower_ranges(Domain<F> &d, ConstraintSystemBuilder<S> &b) {
  RangeLoweringImpl<F, S>(d, b).run();
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_RANGE_H_
