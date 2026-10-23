// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the measured cost rates of the placement rule (placement.h). A
// profile states them per field (lib/params/placement_rates_measured.h through
// lib/params/param_sets.h), each with the bench run it comes from.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLACEMENT_RATES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLACEMENT_RATES_H_

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <optional>
#include <string>
#include <vector>

#include "gordiehowe/compiler/op_count_types.h"
#include "gordiehowe/compiler/stage_rates.h"
#include "util/diagnostics.h"

namespace proofs::gordiehowe::compiler {

// The first round's evaluator of a batch, by its operands' type.
enum class BatchEval : uint8_t {
  // Bit operands in characteristic 2: bit-sliced, 64 instances per lane.
  kBitSliced = 0,
  // Operands in a proper subfield of the field.
  kSubfield = 1,
  // Field operands.
  kField = 2,
};
inline const char *batch_eval_name(BatchEval e) {
  switch (e) {
    case BatchEval::kBitSliced:
      return "bit-sliced";
    case BatchEval::kSubfield:
      return "subfield";
    default:
      return "full field";
  }
}

// The default margin of every cost-based choice of the compiler (the
// placement rule, the range planner's tables and the packing tree's chains):
// the choice keeps its default unless the cheapest candidate's modeled cost
// is more than this many percent below the default's. The defaults: the circuit
// for a check group; for range tables, the fewest tables, then the fewest total
// rows.
inline constexpr unsigned kDefaultMarginPercent = 5;
// Whether a candidate of cost BEST displaces a default of cost DEFAULT_COST:
// BEST is more than kDefaultMarginPercent below it.
inline bool beats_default(double best, double default_cost) {
  return best * 100 < default_cost * double(100 - kDefaultMarginPercent);
}

// The request scan of the rate microbench: with the rate_requests file of
// util/diagnostics.h set, appends the line "<field> <what>" to it and is true;
// false otherwise. Measurement only.
inline bool record_rate_request(const char *field, const std::string &what) {
  const std::string &scan = diagnostics::options().rate_requests;
  if (scan.empty()) return false;
  if (std::FILE *out = std::fopen(scan.c_str(), "a")) {
    std::fprintf(out, "%s %s\n", field, what.c_str());
    std::fclose(out);
  }
  return true;
}

// The measured cost rates of one field's domains, in microseconds of
// commit + prove + verify. SOURCE names the bench run they come from. A
// profile without measured rates (the test-only profiles) costs every unit
// the models count 1 (unit()): a triple, a quad term, a committed
// coordinate, and a batch's fixed part, each instance's operand and each
// merged predicate (1 + n K + parts - 1 for n instances of K operands), at
// the default width (16 bit-sliced, 4 otherwise); the range planner counts
// its coordinates, needles and rows the same way (range.h).
struct PlacementRates {
  // One committed coordinate: a full-field cell, and a relatively packed
  // subfield coordinate.
  double commit_full = 0, commit_sub = 0;
  // One GKR quad term.
  double gkr_term = 0;
  // One quadratic triple, TRIPLE + TRIPLE_B block_enc (its coordinates in
  // the quadratic rows and its share of the quadratic test); and each
  // quadratic row the triples add to the domain's tableau, TRIPLE_ROW +
  // TRIPLE_ROW_B block_enc (the rows the provisional tableau counts,
  // compiled_domain.h).
  // And per compression they add to hashing the tableau's columns,
  // TRIPLE_HASH block_enc (a column's rows grow by the triples' rows); and
  // once for a group of triples, TRIPLE_FIXED + TRIPLE_FIXED_B block_enc.
  double triple = 0, triple_b = 0, triple_row = 0, triple_row_b = 0;
  double triple_hash = 0, triple_fixed = 0, triple_fixed_b = 0;
  // A batch's cost at one evaluator (op_counts.h): FIXED per batch and a
  // rate per operation its kernel counts in one proof, at the evaluator's
  // skip width (16 bit-sliced, 4 otherwise).
  // MUL, ADD and MAC price the skip's field operations, MAP_MUL, MAP_ADD
  // and MAP_MAC the operand map's (OpCounts' map share); a pooled fit
  // gives both the same rates. REGION prices a bit-sliced batch's
  // coefficients at the packing tree's root (OpCounts::region).
  struct OpRates {
    BatchEval eval = BatchEval::kSubfield;
    double fixed = 0, mul = 0, add = 0, mac = 0;
    double lane_lookup = 0, lane_mul = 0, lane_term = 0, lin = 0;
    double map_mul = 0, map_add = 0, map_mac = 0;
    double region = 0;
    double cost(const OpCounts &c) const {
      return fixed + mul * double(c.mul - c.map_mul) +
             add * double(c.add - c.map_add) +
             mac * double(c.mac - c.map_mac) +
             map_mul * double(c.map_mul) + map_add * double(c.map_add) +
             map_mac * double(c.map_mac) +
             lane_lookup * double(c.lane_lookup) +
             lane_mul * double(c.lane_mul) +
             lane_term * double(c.lane_term) + lin * double(c.lin) +
             region * double(c.region);
    }
  };
  std::vector<OpRates> batch;
  // The packing tree's chains (stage_rates.h), by which the compiler
  // chooses a root edge's chain.
  StageRates stage;
  const char *source = "";
  // The field the rates are of, as the rate run names it (Fp24_6, ...).
  const char *field = "";
  // Unit rates (unit()), not measured ones.
  bool unit_rates = false;
  bool measured() const { return gkr_term > 0 && !unit_rates; }
  // The unit rates of a profile without measured ones.
  static PlacementRates unit() {
    PlacementRates r;
    r.commit_full = r.commit_sub = r.gkr_term = r.triple = 1;
    r.source = "unit";
    r.unit_rates = true;
    return r;
  }
  // These rates, or unit() when none are measured.
  PlacementRates or_unit() const { return measured() ? *this : unit(); }
  // The batch rates of EVAL, or none (the placement rule then leaves the
  // batch out of its automatic choice; unit rates have none: the caller
  // counts units).
  //
  // The request scan of the rate microbench: with
  // diagnostics::Options::rate_requests naming a file (--rate-requests;
  // GH_RATE_REQUESTS in a test binary), every request of measured rates appends
  // "<field> <evaluator> <degree> <n>" to it, N the candidate's instances
  // (the microbench measures forms of the requested degrees over the
  // requested instance counts). Measurement only.
  // Whether these rates price a batch of EVAL (no request recorded): the
  // compiler counts a candidate batch's work only then.
  bool has_batch(BatchEval eval) const {
    for (const auto &b : batch)
      if (b.eval == eval) return true;
    return false;
  }
  std::optional<OpRates> batch_rates(BatchEval eval, unsigned degree,
                                     size_t n) const {
    if (measured())
      record_rate_request(
            field, std::string(eval == BatchEval::kBitSliced ? "bit-sliced"
                               : eval == BatchEval::kSubfield ? "subfield"
                                                              : "field") +
                       " " + std::to_string(degree) + " " + std::to_string(n));
    for (const auto &b : batch)
      if (b.eval == eval) return b;
    return std::nullopt;
  }
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLACEMENT_RATES_H_
