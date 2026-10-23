// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The rows of the paper's table tab:mask-test-room (sections/
// be-commitment.tex) from the compiler's Ligero choice
// (gordiehowe/compiler/ligero_choice.h): at each tableau (N, k) of the
// table, each low-degree repetition count rho in {1, 2, 3}, and each
// masking (split masks, the mask test; untested masks, without it), the
// choice choose_ligero_half makes at the domain's target, with the rounds
// that set it.
//
// The tableaus are those the compiler chose in the paper's measurements
// (eval_params.json): the hashing field's tableau H of the ML-DSA-44 proof
// of possession, (3392, 282) over GF(2^128) at the ROM parameters and
// (4069, 339) over GF(2^256) at the QROM parameters, and the tableau A of
// the ECDSA mDL, (1367, 341) over F_p256 at the ROM parameters. Every
// domain profile has subfield rows (domain_profile.h), and none of these
// domains is planned at the fallback target, so each row is
// choose_ligero_half(N, k, |K|, half, true, rho, masking).
//
// A row's rounds:
//   A_lo  the least A >= max(k, isqrt(N (k - 1))) whose certificate meets
//         the commit budget (count_lo_prev: the least count at A_lo - 1,
//         above the budget, or none; budget sat: every count meets it, and
//         A_lo is the least certified A);
//   t     the least t whose column round at A_lo meets the target
//         (column_lo_prev: -log2 of the column round at A_lo and t - 1);
//   A     the threshold in [A_lo, A_hi] minimizing max(commit, column);
// commit, test and column are -log2 of the rounds at the chosen A and t.
//
// The curve lines give the exceptional count at the Johnson agreement A_J
// (johnson_agreement(N, 2k - 2)) and at the least certified A from
// max(k, isqrt(N (k - 1))), which the text around the table cites.
//
// Usage: masktest_rows (no arguments).

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <optional>
#include <string>
#include <vector>

#include "gordiehowe/compiler/ligero_choice.h"

namespace proofs::gordiehowe::compiler {
namespace {

namespace d = ligero_choice_detail;

FieldOrder p256() {
  return FieldOrder{{0xFFFFFFFFFFFFFFFFull, 0x00000000FFFFFFFFull, 0,
                     0xFFFFFFFF00000001ull}};
}

struct Field {
  const char *name;
  FieldOrder order;
  // The domain's target in half bits.
  size_t half;
  const char *params;
};

struct TableTableau {
  const char *what;
  Field field;
  size_t N, k;
};

std::vector<TableTableau> tableaus() {
  const Field gf128{"GF(2^128)", FieldOrder::power(2, 128),
                    target_half(LigeroTarget::kClassical), "ROM"};
  const Field fp256{"F_p256", p256(), target_half(LigeroTarget::kClassical),
                    "ROM"};
  const Field gf256{"GF(2^256)", FieldOrder::power(2, 256),
                    target_half(LigeroTarget::kPostQuantum), "QROM"};
  return {
      {"ML-DSA-44 H", gf128, 3392, 282},
      {"ECDSA mDL A", fp256, 1367, 341},
      {"ML-DSA-44 H", gf256, 4069, 339},
  };
}

std::string count_str(const std::optional<LineCertificate> &c) {
  return c ? std::to_string(c->count) : std::string("none");
}

// A budget, "sat" when power_budget saturates at UINT64_MAX (every count
// meets it).
std::string budget_str(uint64_t b) {
  return b == UINT64_MAX ? std::string("sat") : std::to_string(b);
}

void print_row(const TableTableau &tt, size_t reps, LigeroMasking m) {
  const FieldOrder &order = tt.field.order;
  const size_t half = tt.field.half;
  const size_t N = tt.N, k = tt.k;
  const bool split = m == LigeroMasking::kSplit;
  const double room = order.log2() - double(half) / 2 / double(reps);
  std::printf("row %s %s %s (%zu, %zu) rate 1/%zu rho %zu room %.2f %s",
              tt.field.name, tt.what, tt.field.params, N, k,
              size_t(std::lround(double(N) / double(k))), reps, room,
              split ? "mask-test" : "untested");
  const auto c = choose_ligero_half(N, k, order, half, true, reps, m);
  if (!c) {
    std::printf(" none\n");
    return;
  }
  // The rounds that set A_lo and t, recomputed with solve's own pieces.
  d::Tableau tb{N,
                k,
                half / 2,
                power_budget(order.minus_one(), half, reps),
                power_budget(order, half, 1),
                true,
                order.log2(),
                m};
  tb.reps = reps;
  tb.half = half;
  size_t a_lo = std::max(k, d::isqrt(uint64_t(N) * (k - 1)));
  while (a_lo <= N &&
         !d::line_search(N, k, a_lo, tb.commit_budget, true).has_value())
    ++a_lo;
  const auto at_lo = d::best_line(N, k, a_lo);
  const auto before_lo = d::best_line(N, k, a_lo - 1);
  const double col_prev =
      c->t > 1 ? -double(std::log2l(tb.column(a_lo, c->t - 1))) : 0;
  const double col_lo = -double(std::log2l(tb.column(a_lo, c->t)));
  std::printf(
      " t %zu A %zu count %llu cert {%s} commit %.3f test %.3f column %.3f"
      " | A_lo %zu count_lo %s count_lo_prev %s budget %s"
      " column_lo %.3f column_lo_prev %.3f",
      c->t, c->A, (unsigned long long)c->cert.count, c->cert.name().c_str(),
      c->commit, c->test, c->column, a_lo, count_str(at_lo).c_str(),
      count_str(before_lo).c_str(), budget_str(tb.commit_budget).c_str(),
      col_lo, col_prev);
  if (!split) std::printf(" a %zu l %zu", c->a, c->l);
  std::printf("\n");
}

void print_curve(size_t N, size_t k) {
  const size_t aj = d::johnson_agreement(N, 2 * k - 2);
  size_t a = std::max(k, d::isqrt(uint64_t(N) * (k - 1)));
  while (a <= N && !d::best_line(N, k, a)) ++a;
  const auto at_j = d::best_line(N, k, aj);
  const auto at_a = d::best_line(N, k, a);
  std::printf(
      "curve (%zu, %zu) N/k %.2f A_J %zu log2_count_AJ %.1f A_min %zu"
      " log2_count_Amin %.1f inv_log2_N_over_k %.3f\n",
      N, k, double(N) / double(k), aj,
      at_j ? std::log2(double(at_j->count)) : NAN, a,
      at_a ? std::log2(double(at_a->count)) : NAN,
      1 / std::log2(double(N) / double(k)));
}

}  // namespace
}  // namespace proofs::gordiehowe::compiler

int main() {
  using namespace proofs::gordiehowe::compiler;
  for (const auto &tt : tableaus())
    for (size_t reps = 1; reps <= 3; ++reps)
      for (const auto m :
           {proofs::LigeroMasking::kSplit, proofs::LigeroMasking::kUntested})
        print_row(tt, reps, m);
  const size_t curves[][2] = {{3392, 282},  {4069, 339}, {1367, 341},
                              {2560, 512},  {10111, 842}, {2726, 389},
                              {4951, 550},  {3072, 512}};
  for (const auto &nk : curves) print_curve(nk[0], nk[1]);
  return 0;
}
