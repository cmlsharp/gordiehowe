// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Ligero parameters of a tableau from the per-round target.
//
// The round errors are those of the paper's Ligero lemma (lem:ligero,
// sections/be-commitment.tex) at an agreement threshold A, k <= A <= N, with
// rho repetitions of the low-degree test (LigeroMode::ldt_reps):
//
//   commit   (B / (|K| - 1))^rho    B the line certificate's exceptional count
//   test     1 / |K| (split masks), l / |K| (untested masks)
//   column   ((A-1)_t + (m)_t + s (k-1)_t) / (N)_t
//            m = 2k - 1 (split masks) or the Johnson agreement a (untested)
//            s = 1 when the tableau has subfield rows
//
// the Lean's TreeLayout.Masking.bounds (formal/GordieHowe/ProofSystem/
// Ligero/MaskRow/Layout.lean) with the joint subfield term
// (Numbers.proofError). Untested masks take the Lean's
// UntestedMaskRow.Parameters at a = johnsonAgreement N (2k - 2) and
// l = listBound N (2k - 2) a (MaskedConstraintList.lean), and need
// a + 1 <= N and N (2k - 2) < (a + 1)^2.
//
// and the parameters follow this rule:
//   1. A_lo is the least A >= max(k, isqrt(N (k-1))) whose least
//      certificate count B meets the commit round at 2^-s, i.e.
//      B^rho 2^s <= (|K| - 1)^rho;
//   2. t is the least t whose column round at A_lo meets 2^-s;
//   3. at that t, A in [A_lo, A_hi] minimizes max(commit, column).
//
// Each challenge is charged its own error (the paper's thm:backend(2); the
// Lean's FieldRoundsLe, formal/GordieHowe/ProofSystem/Program/
// FieldDomain.lean, and fieldForkError_le, FieldFJ.lean): every round is
// checked against 2^-s on its own, and no other round's error is added to
// the column round. The rounds this choice meets are the commit, the test
// and the column; the domain's masked inner-product rounds (its batches
// summed, each GKR round, the packing combinations) are checked apart, in
// compiled_domain.h's check_own_rounds, which also checks the phases.
// B is the least count of the unique-decoding certificate (BCIKS20: B = N
// when A >= N - floor((N-k)/2)) and the weighted Johnson certificates
// (DKT26, ArkLib's IsJohnsonWeightedCertificate) with 1 <= m <= 120 and
// 1 <= Bj <= min(250, 2D + 1, floor((mA - 1)/D)), D = k - 1.
//
// The search returns the certificate the
// enumeration of that space returns (best_line_exhaustive: the least count,
// the first in (m, Bj) order to reach it) without visiting all of it. A
// count grows with Bj and h, so a certificate's least count at h = Bj bounds
// every larger Bj: line_search stops Bj once that bound exceeds the best
// count so far (or the commit budget), and admits a certificate by
// comparing products, with no 128-bit division. Every weighted count
// exceeds N, so at unique decoding it visits nothing. Where a weighted
// count could reach 2^62 (at thresholds A just above a certificate's slope
// root, for large N; random tableaux reach counts above 2^64 from N near
// 8 * 10^5) the enumeration's 64-bit cast could wrap, and line_search
// enumerates instead (line_bounds_hold). A_lo's walk asks only whether
// some count meets the budget, and stops at the first that does. Step 3
// stops at the first A whose column round reaches the best max: the
// computed column round does not fall as A grows.
//
// Masking: this choice solves one masking; compiled_domain.h's size search
// takes the one of the smaller predicted proof, split masks on a tie
// (split masks need 2t <= k).
//
// The column round is compared in long double: each falling-factorial ratio
// is a product of t <= N factors below one, with relative error far below
// the factor (A/N or 1 + t/A) between neighbouring t or A. The commit and
// test rounds are compared exactly against floor((|K| - 1)/2^s) and
// floor(|K|/2^s).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LIGERO_CHOICE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LIGERO_CHOICE_H_

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <map>
#include <mutex>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "ligero/ligero_param.h"
#include "sumcheck/circuit_id.h"

namespace proofs::gordiehowe::compiler {

// A natural number as little-endian 64-bit limbs: the order of a field.
struct FieldOrder {
  std::vector<uint64_t> limbs;

  static FieldOrder of_u64(uint64_t x) { return FieldOrder{{x}}; }
  // P^D.
  static FieldOrder power(uint64_t p, uint64_t d) {
    FieldOrder r = of_u64(1);
    for (uint64_t i = 0; i < d; ++i) r = r.times(p);
    return r;
  }
  FieldOrder times(uint64_t x) const {
    FieldOrder r;
    unsigned __int128 carry = 0;
    for (uint64_t l : limbs) {
      const unsigned __int128 v = (unsigned __int128)l * x + carry;
      r.limbs.push_back(uint64_t(v));
      carry = v >> 64;
    }
    if (carry != 0) r.limbs.push_back(uint64_t(carry));
    return r;
  }
  FieldOrder minus_one() const {
    FieldOrder r = *this;
    for (auto &l : r.limbs)
      if (l-- != 0) break;
    return r;
  }
  // floor(x / 2^s), saturated at UINT64_MAX.
  uint64_t shifted(size_t s) const {
    const size_t q = s / 64, b = s % 64;
    std::vector<uint64_t> r;
    for (size_t i = q; i < limbs.size(); ++i) {
      uint64_t v = limbs[i] >> b;
      if (b != 0 && i + 1 < limbs.size()) v |= limbs[i + 1] << (64 - b);
      r.push_back(v);
    }
    for (size_t i = 1; i < r.size(); ++i)
      if (r[i] != 0) return UINT64_MAX;
    return r.empty() ? 0 : r[0];
  }
  double log2() const {
    double r = 0;
    for (size_t i = limbs.size(); i-- > 0;)
      r = r * 18446744073709551616.0 + double(limbs[i]);
    return std::log2(r);
  }
  FieldOrder times(const FieldOrder &o) const {
    FieldOrder r;
    r.limbs.assign(limbs.size() + o.limbs.size(), 0);
    for (size_t i = 0; i < limbs.size(); ++i) {
      unsigned __int128 carry = 0;
      for (size_t j = 0; j < o.limbs.size(); ++j) {
        const unsigned __int128 v =
            (unsigned __int128)limbs[i] * o.limbs[j] + r.limbs[i + j] + carry;
        r.limbs[i + j] = uint64_t(v);
        carry = v >> 64;
      }
      r.limbs[i + o.limbs.size()] = uint64_t(carry);
    }
    return r;
  }
  FieldOrder pow(size_t e) const {
    FieldOrder r = of_u64(1);
    for (size_t i = 0; i < e; ++i) r = r.times(*this);
    return r;
  }
  // x 2^s.
  FieldOrder shl(size_t s) const {
    FieldOrder r;
    r.limbs.assign(limbs.size() + s / 64 + 1, 0);
    for (size_t i = 0; i < limbs.size(); ++i) {
      const unsigned __int128 v = (unsigned __int128)limbs[i] << (s % 64);
      r.limbs[i + s / 64] |= uint64_t(v);
      r.limbs[i + s / 64 + 1] |= uint64_t(v >> 64);
    }
    return r;
  }
  // *this <= o.
  bool le(const FieldOrder &o) const {
    const size_t n = std::max(limbs.size(), o.limbs.size());
    for (size_t i = n; i-- > 0;) {
      const uint64_t a = i < limbs.size() ? limbs[i] : 0;
      const uint64_t b = i < o.limbs.size() ? o.limbs[i] : 0;
      if (a != b) return a < b;
    }
    return true;
  }
};

// The largest B (at most UINT64_MAX) with (B / X)^REPS <= 2^-(HALF/2),
// exactly: B^REPS 2^(HALF/2) <= X^REPS for an even HALF, and B^(2 REPS)
// 2^HALF <= X^(2 REPS) for an odd one (a target of a whole number of bits
// and a half).  One repetition at a whole target: floor(X / 2^(HALF/2)),
// saturated.
inline uint64_t power_budget(const FieldOrder &x, size_t half, size_t reps) {
  if (half % 2 == 0 && reps == 1) return x.shifted(half / 2);
  const size_t e = half % 2 == 0 ? reps : 2 * reps;
  const size_t sh = half % 2 == 0 ? half / 2 : half;
  const FieldOrder rhs = x.pow(e);
  auto ok = [&](uint64_t b) {
    return FieldOrder::of_u64(b).pow(e).shl(sh).le(rhs);
  };
  uint64_t lo = 0, hi = UINT64_MAX;
  if (ok(hi)) return hi;
  while (hi - lo > 1) {
    const uint64_t mid = lo + (hi - lo) / 2;
    if (ok(mid))
      lo = mid;
    else
      hi = mid;
  }
  return lo;
}

// The largest B (at most UINT64_MAX) with (B / (|K| - 1))^REPS <= G / |K|,
// exactly: B^REPS |K| <= G (|K| - 1)^REPS (the commit budget at the target
// G/|K| of a fallback domain, compiled_domain.h's choose_tableau).
inline uint64_t ratio_budget(const FieldOrder &order, uint64_t g,
                             size_t reps) {
  const FieldOrder rhs = order.minus_one().pow(reps).times(g);
  auto ok = [&](uint64_t b) {
    return FieldOrder::of_u64(b).pow(reps).times(order).le(rhs);
  };
  uint64_t lo = 0, hi = UINT64_MAX;
  if (ok(hi)) return hi;
  while (hi - lo > 1) {
    const uint64_t mid = lo + (hi - lo) / 2;
    if (ok(mid))
      lo = mid;
    else
      hi = mid;
  }
  return lo;
}

// The commit round's budget at REPS repetitions and the target 2^-s: the
// largest count B with B^REPS 2^s <= (|K| - 1)^REPS, i.e. (B / (|K| -
// 1))^REPS <= 2^-s.  One repetition: floor((|K| - 1) / 2^s), saturated.
inline uint64_t commit_budget(const FieldOrder &order, size_t s, size_t reps) {
  return power_budget(order.minus_one(), 2 * s, reps);
}

// A line certificate at threshold A: its exceptional count, and either
// unique decoding or the weighted Johnson parameters (m, Bj, H).
struct LineCertificate {
  uint64_t count = 0;
  bool unique_decoding = false;
  uint64_t m = 0, bj = 0, h = 0;
  std::string name() const {
    if (unique_decoding) return "unique decoding";
    return "weighted Johnson (m, Bj, H) = (" + std::to_string(m) + ", " +
           std::to_string(bj) + ", " + std::to_string(h) + ")";
  }
};

// The parameters of one tableau (N, k) at the per-round target 2^-s: the
// opened columns, the masking, the low-degree repetitions, the agreement
// threshold and its certificate, the untested masks' agreement a (0 with
// split masks), and each round's -log2 (commit: all REPS repetitions).
struct LigeroChoice {
  size_t N = 0, k = 0, t = 0;
  LigeroMasking masking = LigeroMasking::kSplit;
  size_t reps = 1;
  // The profile's target, in half bits, and whether the tableau is the
  // fallback (compiled_domain.h's choose_tableau): one of the domain's own
  // rounds besides Ligero's exceeds the profile's target, and the tableau
  // is planned at the largest of them, GOAL_NUM/|K| (IP_BITS = -log2 of
  // it); GOAL_NUM is 0 otherwise.
  size_t half = 0;
  bool fallback = false;
  uint64_t goal_num = 0;
  double ip_bits = 0;
  // The agreement threshold, and the untested masks' agreement a and list
  // size l (0 with split masks).
  size_t A = 0, a = 0, l = 0;
  LineCertificate cert;
  double commit = 0, test = 0, column = 0;
};

namespace ligero_choice_detail {

using I128 = __int128;

// floor(x / y) for y > 0.
inline I128 floor_div(I128 x, I128 y) {
  I128 q = x / y;
  if ((x % y != 0) && (x < 0)) --q;
  return q;
}

// ArkLib's weighted Johnson certificate (WeightedCertificate.lean) at
// (n, D, A, m, Bj): the ceiling of johnsonWeightedRefinedExceptionCount at
// its H, when the certificate and lineCertificate_of_weightedJohnson's side
// conditions hold.
inline std::optional<LineCertificate> weighted(uint64_t n, uint64_t D,
                                               uint64_t A, uint64_t m,
                                               uint64_t bj) {
  if (m < 1 || bj < 1 || !(D * bj < m * A)) return std::nullopt;
  if (!(1 <= D && D + 1 <= A && A <= n && bj <= 2 * D + 1))
    return std::nullopt;
  const I128 mA = I128(m) * A, Bj = bj, d = D, N = n;
  const I128 nw = (Bj + 1) * mA - d * Bj * (Bj + 1) / 2;
  const I128 w = mA * Bj * (Bj + 1) / 2 - d * Bj * (Bj + 1) * (2 * Bj + 1) / 6;
  const I128 u = std::min<I128>(Bj, I128(m) - 1);
  const I128 r = (u + 1) * I128(m) - u * (u + 1) / 2;
  const I128 t = I128(m) * u * (u + 1) / 2 - u * (u + 1) * (2 * u + 1) / 6;
  const I128 slope = nw - N * r;
  if (slope <= 0) return std::nullopt;
  const I128 h = std::max<I128>(Bj, floor_div(w - N * t, slope));
  const I128 num = ((2 * Bj - 1) * h + (N - d - 1) * Bj) * (A - d) +
                   (N - d) * (h + Bj + (2 * d - 1) * h * (2 * Bj - 1));
  const I128 den = I128(A) - d;
  LineCertificate c;
  c.count = uint64_t((num + den - 1) / den);
  c.m = m;
  c.bj = bj;
  c.h = uint64_t(h);
  return c;
}

constexpr uint64_t kMaxM = 120, kMaxBj = 250;

// The definition of the line certificate at threshold A: the least
// exceptional count over the unique-decoding certificate and the weighted
// Johnson certificates of the search space, the first in (m, Bj) order to
// reach it. line_search returns the same certificate faster, and falls back
// to this enumeration where its bounds do not hold.
inline std::optional<LineCertificate> best_line_exhaustive(uint64_t N,
                                                           uint64_t k,
                                                           uint64_t A) {
  if (A < k || A > N) return std::nullopt;
  const uint64_t D = k - 1;
  std::optional<LineCertificate> best;
  if (N <= A + (N - k) / 2) {
    LineCertificate c;
    c.count = N;
    c.unique_decoding = true;
    best = c;
  }
  for (uint64_t m = 1; m <= kMaxM; ++m) {
    const uint64_t top = std::min({kMaxBj, 2 * D + 1, (m * A - 1) / D});
    for (uint64_t bj = 1; bj <= top; ++bj) {
      const auto c = weighted(N, D, A, m, bj);
      if (c && (!best || c->count < best->count)) best = c;
    }
  }
  return best;
}

// tri[b] = b (b + 1)/2 and pyr[b] = b (b + 1)(2b + 1)/6, 0 <= b <= kMaxBj.
struct BjSums {
  int64_t tri[kMaxBj + 1], pyr[kMaxBj + 1];
};
inline const BjSums &bj_sums() {
  static const BjSums s = [] {
    BjSums r;
    for (int64_t b = 0; b <= int64_t(kMaxBj); ++b) {
      r.tri[b] = b * (b + 1) / 2;
      r.pyr[b] = b * (b + 1) * (2 * b + 1) / 6;
    }
    return r;
  }();
  return s;
}

// line_search's bounds. Each weighted certificate (m, Bj) at A has
//   slope = (Bj + 1) m A - K,   w - N t = m tri(Bj) A - J
// (K = D tri(Bj) + N r and J = D pyr(Bj) + N t do not depend on A), so
//   (w - N t) / slope = Bj/2 + R / slope,   R = (Bj K - 2 J)/2,
// and h <= max(Bj, Bj/2 + R / slope). Its count is ceil((c1 h + c0) /
// (A - D)), where c1 and c0 grow with Bj. The search's loop needs N < 2^36
// (each product below 2^63) and every count below 2^62 (the count
// best_line_exhaustive compares, weighted's cast to 64 bits, is then exact).
// That holds where
//   - h <= max(Bj, m A tri(Bj)) (slope >= 1, w - N t <= w) bounds every
//     count below 2^62 (line_bounds_coarse), or
//   - A >= a_base and A lies in no certificate's window (line_danger): at
//     Bj = Bmax = min(kMaxBj, 2D + 1), Hs(A) = 2^61 (A - D)/c1 - (N + 1) -
//     Bmax/2 grows with A, the count at h = Bmax/2 + Hs(A) is below 2^61 + 2
//     (c0 <= c1 (N + 1)), a_base is the least A with Hs(A) >= Bmax/2, and a
//     certificate with R > 0 has the window of A where 1 <= slope <= R /
//     Hs(A_s), A_s its window's least A: outside it R / slope < Hs(A).
inline bool line_bounds_coarse(uint64_t N, uint64_t D, uint64_t A) {
  if (D == 0 || N >= (uint64_t{1} << 36)) return false;
  const long double b = (long double)std::min(kMaxBj, 2 * D + 1);
  const long double n = N, d = D, a = A, den = a - d;
  const long double h =
      std::max(b, (long double)kMaxM * a * b * (b + 1) / 2);
  const long double c1 =
      (2 * b - 1) * den + (n - d) * (1 + (2 * d - 1) * (2 * b - 1));
  const long double c0 = b * ((n - d - 1) * den + (n - d));
  return (c1 * h + c0) / den + 1 < std::ldexp((long double)1, 62);
}

struct LineDanger {
  // The least A at which the windows decide (N + 1 when none does).
  uint64_t a_base = 0;
  // Disjoint windows [lo, hi], in order.
  std::vector<std::pair<uint64_t, uint64_t>> windows;
};

// The windows of (N, k), and a_base.
inline LineDanger line_danger(uint64_t N, uint64_t k) {
  const uint64_t D = k - 1;
  const BjSums &s = bj_sums();
  const uint64_t bmax = std::min(kMaxBj, 2 * D + 1);
  const long double n = N, d = D, b = bmax;
  auto hs = [&](uint64_t A) {
    const long double den = (long double)A - d;
    const long double c1 =
        (2 * b - 1) * den + (n - d) * (1 + (2 * d - 1) * (2 * b - 1));
    return std::ldexp((long double)1, 61) * den / c1 - (n + 1) - b / 2;
  };
  LineDanger r;
  uint64_t lo = k, hi = N + 1;
  while (lo < hi) {
    const uint64_t mid = lo + (hi - lo) / 2;
    if (hs(mid) >= b / 2)
      hi = mid;
    else
      lo = mid + 1;
  }
  r.a_base = lo;
  if (r.a_base > N) return r;
  std::vector<std::pair<uint64_t, uint64_t>> w;
  for (uint64_t m = 1; m <= kMaxM; ++m) {
    for (uint64_t bj = 1; bj <= bmax; ++bj) {
      const uint64_t u = std::min(bj, m - 1);
      const I128 a1 = I128(bj + 1) * m;
      const I128 K = I128(D) * s.tri[bj] +
                     I128(N) * (I128(u + 1) * m - s.tri[u]);
      const I128 J = I128(D) * s.pyr[bj] +
                     I128(N) * (I128(m) * s.tri[u] - s.pyr[u]);
      const I128 r2 = I128(bj) * K - 2 * J;
      if (r2 <= 0) continue;
      // The least A >= a_base with slope >= 1.
      const I128 a_s = std::max<I128>(r.a_base, K / a1 + 1);
      if (a_s > I128(N)) continue;
      // The integer slopes at most R / Hs(A_s), with a relative margin of
      // 2^-30 for the long double's rounding.
      const long double cap = (long double)r2 / 2 / hs(uint64_t(a_s)) *
                              (1 + std::ldexp((long double)1, -30));
      if (cap < 1) continue;
      const I128 smax = cap >= n * (long double)a1 ? I128(N) * a1 : I128(cap);
      const I128 a_e = std::min<I128>(N, (K + smax) / a1);
      if (a_e < a_s) continue;
      w.emplace_back(uint64_t(a_s), uint64_t(a_e));
    }
  }
  std::sort(w.begin(), w.end());
  for (const auto &x : w) {
    if (!r.windows.empty() && x.first <= r.windows.back().second + 1)
      r.windows.back().second = std::max(r.windows.back().second, x.second);
    else
      r.windows.push_back(x);
  }
  return r;
}

// Whether line_search's bounds hold at (N, k, A); line_danger is computed
// once per (N, k), where the coarse bound fails.
inline bool line_bounds_hold(uint64_t N, uint64_t k, uint64_t A) {
  const uint64_t D = k - 1;
  if (line_bounds_coarse(N, D, A)) return true;
  if (D == 0 || N >= (uint64_t{1} << 36)) return false;
  static std::mutex mu;
  static std::map<std::pair<uint64_t, uint64_t>, LineDanger> memo;
  std::lock_guard<std::mutex> lock(mu);
  auto it = memo.find({N, k});
  if (it == memo.end())
    it = memo.emplace(std::make_pair(N, k), line_danger(N, k)).first;
  const LineDanger &g = it->second;
  if (A < g.a_base) return false;
  auto w = std::upper_bound(
      g.windows.begin(), g.windows.end(), A,
      [](uint64_t a, const std::pair<uint64_t, uint64_t> &x) {
        return a < x.first;
      });
  return w == g.windows.begin() || std::prev(w)->second < A;
}

// The least count at threshold A that is at most LIMIT, the certificate
// best_line_exhaustive returns when its count is at most LIMIT, and none
// otherwise; with ANY, the first certificate found whose count is at most
// LIMIT (whether one exists).
//
// A weighted count is ceil(num / (A - D)), num = c1 h + c0, where c1 and c0
// grow with Bj and h >= Bj. So the count is at most L iff c1 h + c0 <= L (A
// - D), and the least count of a given Bj (h = Bj) grows with Bj. The search
// keeps L = min(best - 1, LIMIT): it stops Bj at the first Bj whose least
// count exceeds L, and admits a certificate iff c1 h + c0 <= L (A - D),
// computing h = max(Bj, floor((w - N t) / slope)) with one 64-bit division
// (none when w - N t < Bj slope). Every weighted count exceeds N (at Bj = 1,
// h >= 1: N - D + ceil((N - D)(2D + 1) / (A - D)) > N), so at unique
// decoding no weighted certificate is admitted. A certificate it admits is
// weighted's, recomputed.
inline std::optional<LineCertificate> line_search(uint64_t N, uint64_t k,
                                                  uint64_t A, uint64_t limit,
                                                  bool any) {
  if (A < k || A > N) return std::nullopt;
  const uint64_t D = k - 1;
  if (!line_bounds_hold(N, k, A)) {
    const auto c = best_line_exhaustive(N, k, A);
    if (c && c->count <= limit) return c;
    return std::nullopt;
  }
  using U128 = unsigned __int128;
  const int64_t *tri = bj_sums().tri, *pyr = bj_sums().pyr;
  const uint64_t den = A - D;
  const uint64_t bj_top = std::min(kMaxBj, 2 * D + 1);
  U128 c1[kMaxBj + 1], c0[kMaxBj + 1];
  for (uint64_t b = 1; b <= bj_top; ++b) {
    c1[b] = U128(2 * b - 1) * den +
            U128(N - D) * (1 + U128(2 * D - 1) * (2 * b - 1));
    c0[b] = U128(b) * (U128(N - D - 1) * den + (N - D));
  }
  std::optional<LineCertificate> best;
  uint64_t L = limit;
  if (N <= A + (N - k) / 2 && N <= limit) {
    LineCertificate c;
    c.count = N;
    c.unique_decoding = true;
    if (any) return c;
    best = c;
    L = N - 1;
  }
  U128 l_den = U128(L) * den;
  // The largest Bj whose least count is at most L.
  uint64_t bj_lim = bj_top;
  auto shrink = [&] {
    while (bj_lim > 0 && c1[bj_lim] * bj_lim + c0[bj_lim] > l_den) --bj_lim;
  };
  shrink();
  const int64_t n = int64_t(N), d = int64_t(D);
  for (uint64_t m = 1; m <= kMaxM && bj_lim > 0; ++m) {
    const int64_t mi = int64_t(m), mA = int64_t(m * A);
    const uint64_t top = std::min(bj_lim, (m * A - 1) / D);
    for (uint64_t bj = 1; bj <= top && bj <= bj_lim; ++bj) {
      const int64_t b = int64_t(bj);
      const int64_t u = std::min(b, mi - 1);
      const int64_t slope =
          (b + 1) * mA - d * tri[b] - n * ((u + 1) * mi - tri[u]);
      if (slope <= 0) continue;
      const int64_t x = mA * tri[b] - d * pyr[b] - n * (mi * tri[u] - pyr[u]);
      const uint64_t h = x < b * slope ? bj : uint64_t(x / slope);
      if (c1[bj] * h + c0[bj] > l_den) continue;
      best = weighted(N, D, A, m, bj);
      if (any) return best;
      L = best->count - 1;
      l_den = U128(L) * den;
      shrink();
    }
  }
  return best;
}

// The least count at threshold A as best_line_exhaustive finds it.
inline std::optional<LineCertificate> best_line(uint64_t N, uint64_t k,
                                                uint64_t A) {
  return line_search(N, k, A, UINT64_MAX, false);
}

// line_search, remembered for the process: the planner asks for the same
// (N, k, A) across tableaus, maskings, repetitions and domains. Each
// (N, k, A) keeps its certificate once a search has found the least count,
// and otherwise the largest LIMIT below which a search found none.
inline std::optional<LineCertificate> line_search_cached(uint64_t N,
                                                         uint64_t k,
                                                         uint64_t A,
                                                         uint64_t limit,
                                                         bool any) {
  struct Known {
    bool exact = false;
    std::optional<LineCertificate> best;
    // No count is at most below.
    uint64_t below = 0;
  };
  static std::mutex mu;
  static std::map<std::tuple<uint64_t, uint64_t, uint64_t>, Known> memo;
  const auto key = std::make_tuple(N, k, A);
  {
    std::lock_guard<std::mutex> lock(mu);
    auto it = memo.find(key);
    if (it != memo.end()) {
      const Known &e = it->second;
      if (e.exact) {
        if (e.best && e.best->count <= limit) return e.best;
        return std::nullopt;
      }
      if (limit <= e.below) return std::nullopt;
    }
  }
  const auto c = line_search(N, k, A, limit, any);
  std::lock_guard<std::mutex> lock(mu);
  Known &e = memo[key];
  if (!e.exact) {
    if (c && !any) {
      e.exact = true;
      e.best = c;
    } else if (!c) {
      e.below = std::max(e.below, limit);
    }
  }
  return c;
}

// (x)_t / (N)_t, zero when t > x.
inline long double ratio(size_t x, size_t N, size_t t) {
  if (t > x) return 0;
  long double r = 1;
  for (size_t i = 0; i < t; ++i) r *= (long double)(x - i) / (N - i);
  return r;
}

inline size_t isqrt(uint64_t x) {
  uint64_t s = uint64_t(std::sqrt((long double)x));
  while (s * s > x) --s;
  while ((s + 1) * (s + 1) <= x) ++s;
  return size_t(s);
}

// MaskedConstraintList.johnsonAgreement N d: the least a with
// d (N - 1) <= a (a + 1).
inline size_t johnson_agreement(size_t N, size_t d) {
  const size_t s = isqrt(uint64_t(d) * (N - 1));
  return uint64_t(d) * (N - 1) <= uint64_t(s) * (s + 1) ? s : s + 1;
}

// MaskedConstraintList.listBound N d a = N (a + 1 - d) / ((a + 1)^2 - N d),
// natural subtraction and division, when UntestedMaskRow.Parameters'
// a + 1 <= N and N d < (a + 1)^2 hold; none otherwise.
inline std::optional<uint64_t> list_bound(size_t N, size_t d, size_t a) {
  const unsigned __int128 a1 = a + 1, nd = (unsigned __int128)N * d;
  if (!(a1 <= N && nd < a1 * a1)) return std::nullopt;
  const unsigned __int128 num = a1 >= d ? (unsigned __int128)N * (a1 - d) : 0;
  return uint64_t(num / (a1 * a1 - nd));
}

// The rounds of one tableau at target 2^-s, for one masking.
struct Tableau {
  size_t N, k, s;
  // floor((|K| - 1)/2^s) and floor(|K|/2^s).
  uint64_t commit_budget, test_budget;
  bool subfield_rows;
  double log2_order;
  LigeroMasking masking;
  // The low-degree repetitions.
  size_t reps = 1;
  // The mask term's x: 2k - 1 (split) or a (untested).
  size_t mask_x() const {
    return masking == LigeroMasking::kSplit ? 2 * k - 1
                                            : johnson_agreement(N, 2 * k - 2);
  }
  long double column(size_t A, size_t t) const {
    return ratio(A - 1, N, t) + ratio(mask_x(), N, t) +
           (subfield_rows ? ratio(k - 1, N, t) : 0);
  }
  // The target in half bits (2 s; odd for a target of a whole number of
  // bits and a half), and 2^-(HALF/2); or, when GOAL_NUM is nonzero, the
  // target GOAL_NUM/|K|.
  size_t half = 0;
  uint64_t goal_num = 0;
  long double goal() const {
    if (goal_num != 0)
      return (long double)goal_num * std::exp2l(-(long double)log2_order);
    return half != 0 ? std::exp2l(-(long double)half / 2)
                     : std::ldexp((long double)1, -int(s));
  }
  // The column round alone against the target.
  bool column_ok(size_t A, size_t t) const { return column(A, t) <= goal(); }
};

// The least t and the chosen A for one masking, or none when a round cannot
// meet the target.
inline std::optional<LigeroChoice> solve(const Tableau &tb) {
  const size_t N = tb.N, k = tb.k;
  if (k < 2 || k > N) return std::nullopt;
  // The test round: 1/|K| or l/|K|, l = listBound N (2k - 2) a, against
  // the test budget.
  uint64_t l = 1;
  if (tb.masking != LigeroMasking::kSplit) {
    const auto lb = list_bound(N, 2 * k - 2, tb.mask_x());
    if (!lb) return std::nullopt;
    l = *lb;
  }
  if (l > tb.test_budget) return std::nullopt;
  // The commit round fixes A_lo. Whether a count meets the budget takes the
  // first certificate within it; the chosen A's takes the least.
  auto line = [&](size_t A) {
    return line_search_cached(N, k, A, tb.commit_budget, false);
  };
  auto commit_ok = [&](size_t A) {
    return line_search_cached(N, k, A, tb.commit_budget, true).has_value();
  };
  size_t a_lo = std::max(k, isqrt(uint64_t(N) * (k - 1)));
  while (a_lo <= N && !commit_ok(a_lo)) ++a_lo;
  if (a_lo > N) return std::nullopt;
  // The least t at A_lo: doubling, then bisection (the column round falls
  // with t).
  size_t hi = 1;
  while (!tb.column_ok(a_lo, hi)) {
    hi *= 2;
    if (hi > N) return std::nullopt;
  }
  size_t lo = hi > 1 ? hi / 2 + 1 : 1;
  while (lo < hi) {
    const size_t mid = (lo + hi) / 2;
    if (tb.column_ok(a_lo, mid))
      hi = mid;
    else
      lo = mid + 1;
  }
  const size_t t = lo;
  if (tb.masking == LigeroMasking::kSplit && 2 * t > k) return std::nullopt;
  // A_hi: the largest A whose column round meets the target at t (the
  // column round grows with A).
  size_t alo = k, ahi = N;
  while (alo < ahi) {
    const size_t mid = (alo + ahi + 1) / 2;
    if (tb.column_ok(mid, t))
      alo = mid;
    else
      ahi = mid - 1;
  }
  const size_t a_hi = alo;
  // A in [A_lo, A_hi] minimizing max(commit, column), the least such A. The
  // computed column round does not fall as A grows (each factor (A - 1 -
  // i)/(N - i) and each rounded product and sum is monotone), so once it
  // reaches the best max no larger A is strictly better.
  std::optional<LigeroChoice> best;
  long double best_worst = 0;
  for (size_t A = a_lo; A <= a_hi; ++A) {
    if (best && !(tb.column(A, t) < best_worst)) break;
    if (!commit_ok(A)) continue;
    const LineCertificate c = *line(A);
    const long double commit = std::exp2l(
        (long double)tb.reps *
        ((long double)std::log2((double)c.count) - tb.log2_order));
    const long double worst = std::max(commit, tb.column(A, t));
    if (best && !(worst < best_worst)) continue;
    LigeroChoice r;
    r.N = N;
    r.k = k;
    r.t = t;
    r.masking = tb.masking;
    r.reps = tb.reps;
    r.A = A;
    r.a = tb.masking == LigeroMasking::kSplit ? 0 : tb.mask_x();
    r.l = tb.masking == LigeroMasking::kSplit ? 0 : l;
    r.cert = c;
    r.commit = double(tb.reps) * (tb.log2_order - std::log2((double)c.count));
    r.test = tb.log2_order - std::log2((double)std::max<uint64_t>(l, 1));
    r.column = -double(std::log2l(tb.column(A, t)));
    best = r;
    best_worst = worst;
  }
  return best;
}

}  // namespace ligero_choice_detail

// The per-round target of a domain, in half bits: per-round errors at most
// 2^-(half / 2). The classical parameters' is 2^-113.5 (227), the
// post-quantum ones' 2^-236 (472). kClassicalFallback, 2^-108 (216), is the
// level of the parameter tables' classical rows. A domain one of whose own rounds
// besides Ligero's exceeds 2^-113.5 is planned at the largest of them
// (compiled_domain.h's choose_tableau).
enum class LigeroTarget : uint16_t {
  kClassical = 227,
  kPostQuantum = 472,
  kClassicalFallback = 216
};
// The target's half bits, and its bits.
constexpr size_t target_half(LigeroTarget t) { return size_t(t); }
constexpr double target_bits(LigeroTarget t) { return double(size_t(t)) / 2; }

// The parameters of the tableau (N, k) over a field of order ORDER at the
// target, with or without subfield rows (the column round's s), at REPS
// low-degree repetitions, with split masks; none when they do not meet it.
// ONLY = untested takes untested masks instead (compiled_domain.h's size
// search weighs both). Memoized: the size search asks for each
// tableau once per domain and repetition count, and every domain over one
// field asks for the same ones.
// At the target 2^-(HALF/2) (HALF = 2 s; an odd HALF is a target of a whole
// number of bits and a half, e.g. 227 for 2^-113.5), or, when GOAL_NUM is
// nonzero, at the target GOAL_NUM/|K| (choose_ligero_at_num).
inline std::optional<LigeroChoice> choose_ligero_half(size_t N, size_t k,
                                                      const FieldOrder &order,
                                                      size_t half,
                                                      bool subfield_rows,
                                                      size_t reps = 1,
                                                      std::optional<LigeroMasking>
                                                          only = std::nullopt,
                                                      uint64_t goal_num = 0) {
  namespace d = ligero_choice_detail;
  const size_t s = half / 2;
  d::Tableau tb{N,
                k,
                s,
                goal_num != 0 ? ratio_budget(order, goal_num, reps)
                              : power_budget(order.minus_one(), half, reps),
                goal_num != 0 ? goal_num : power_budget(order, half, 1),
                subfield_rows,
                order.log2(),
                LigeroMasking::kSplit};
  tb.reps = reps;
  tb.half = half;
  tb.goal_num = goal_num;
  const bool untested = only && *only == LigeroMasking::kUntested;
  using Key = std::tuple<size_t, size_t, size_t, uint64_t, uint64_t, bool,
                         size_t, bool, uint64_t>;
  static std::mutex mu;
  static std::map<Key, std::optional<LigeroChoice>> cache;
  const Key key{N,    k,   half, tb.commit_budget, tb.test_budget,
                subfield_rows, reps, untested, goal_num};
  {
    std::lock_guard<std::mutex> g(mu);
    auto it = cache.find(key);
    if (it != cache.end()) return it->second;
  }
  if (untested) tb.masking = LigeroMasking::kUntested;
  const std::optional<LigeroChoice> r = d::solve(tb);
  std::lock_guard<std::mutex> g(mu);
  cache.emplace(key, r);
  return r;
}

inline std::optional<LigeroChoice> choose_ligero(size_t N, size_t k,
                                                 const FieldOrder &order,
                                                 LigeroTarget target,
                                                 bool subfield_rows,
                                                 size_t reps = 1) {
  return choose_ligero_half(N, k, order, target_half(target), subfield_rows,
                            reps);
}

// The order of the field F: p^d from its protocol field id, or the
// modulus of a prime field without one (F_p256, Fp128).
template <class F>
FieldOrder field_order(const F &f) {
  if constexpr (circuit_id_detail::HasFieldId<F>::value) {
    return FieldOrder::power(F::kProtocolFieldId[0], F::kProtocolFieldId[1]);
  } else {
    using limb_t = typename F::limb_t;
    constexpr size_t kLimbBits = 8 * sizeof(limb_t);
    FieldOrder r;
    r.limbs.assign((F::N::kLimbs * kLimbBits + 63) / 64, 0);
    for (size_t i = 0; i < F::N::kLimbs; ++i)
      r.limbs[i * kLimbBits / 64] |= uint64_t(f.m_.limb_[i])
                                     << (i * kLimbBits % 64);
    return r;
  }
}

// The block_enc values a domain's Reed-Solomon encoder admits, as the
// size search walks them.
enum class BlockGrid : uint8_t {
  // block_enc a power of two (F_p256's encoder).
  kPowerOfTwo,
  // block_enc = (rate + 2) 2^j - 1, whose block 2^j and rate + 2 cosets of
  // the 2^j subgroup are the encoders' of Goldilocks and Fp128 (a longer
  // codeword of the same block takes one more coset).
  kPowerOfTwoBlock,
  // The geometric grid e -> floor(9e/8) + 1 from 4 (the F_q^m encoders).
  kGeometric8,
  // The geometric grid e -> floor(17e/16) + 1 from 64, and the powers of
  // two (the GF(2^k) encoders, below the GF(2^16) subfield's 2^16 points).
  kGeometric16,
};

// The candidates of GRID at RATE, at most MAX_E (0: no cap beyond the
// grid's own).
inline std::vector<size_t> block_candidates(BlockGrid grid, size_t rate,
                                            size_t max_e) {
  const size_t cap = max_e != 0 ? max_e : (size_t{1} << 22);
  std::vector<size_t> out;
  switch (grid) {
    case BlockGrid::kPowerOfTwo:
      for (size_t e = 16; e <= cap; e *= 2) out.push_back(e);
      break;
    case BlockGrid::kPowerOfTwoBlock:
      for (size_t j = 4; j <= 20; ++j) {
        const size_t e = (2 + rate) * (size_t{1} << j) - 1;
        if (e <= cap) out.push_back(e);
      }
      break;
    case BlockGrid::kGeometric8:
      for (size_t e = 4; e <= cap; e = (e * 9) / 8 + 1) out.push_back(e);
      break;
    case BlockGrid::kGeometric16: {
      const size_t top = std::min(cap, (size_t{1} << 16) - 1);
      for (size_t e = 64; e <= top; e = (e * 17) / 16 + 1) out.push_back(e);
      for (size_t e = 64; e <= top; e *= 2) out.push_back(e);
      std::sort(out.begin(), out.end());
      out.erase(std::unique(out.begin(), out.end()), out.end());
      break;
    }
  }
  return out;
}

// (N, k) of block_enc E at RATE (ligero_param.h): k = (E + 1)/(rate + 2),
// N = E - (2k - 1); none when E is too short for the rate.
inline std::optional<std::pair<size_t, size_t>> tableau_of(size_t e,
                                                          size_t rate) {
  const size_t k = (e + 1) / (rate + 2);
  if (k < 2 || e < 2 * k - 1) return std::nullopt;
  return std::make_pair(e - (2 * k - 1), k);
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_LIGERO_CHOICE_H_
