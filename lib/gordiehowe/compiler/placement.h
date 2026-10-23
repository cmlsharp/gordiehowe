// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: where a check goes, by measured cost.
//
// A check group is n coordinatewise checks the compiler is free to place:
// the Boolean checks x^2 - x of a domain's phase-0 Bit cells, the
// non-affine assert_zero predicates of one batched form (batch_form.h),
// merged, or one conv(x, y) (conv.h: the direct form its circuit target,
// the spectral batch its batch target, each with the coordinates it
// commits). Each group goes to the circuit, its default, unless the
// cheapest admissible target costs more than kDefaultMarginPercent less
// (placement_rates.h):
//
//   quadratic triples  Ligero's quadratic test, one triple per coordinate.
//                      Admissible when the check is a b - c (or b b - b)
//                      on committed phase-0 full-field cells: the
//                      commitment's quadratic rows read full-field
//                      coordinates only. Cost: three committed
//                      coordinates (its x, y and z rows) and the test.
//   circuit            constraints of the domain's GKR circuit. Always
//                      admissible. Cost: its quad terms.
//   batch              one masked skip zerocheck (batch.h) over the
//                      group's instances. Admissible for a polynomial of a
//                      degree the skip domain admits, over affine views of
//                      phase-0 committed values of one type, with public
//                      per-instance coefficients. Its first round's
//                      evaluator is the operands' type's: bit-sliced for
//                      Bit in characteristic 2, the subfield's or the
//                      field's otherwise. Cost: the field's batch rates
//                      of the evaluator (a fixed part and a rate per
//                      operation) on the work its kernel counts in one
//                      proof (op_counts.h).
//
// A target that commits values of its own (CheckGroup::cells_*) adds
// their committed coordinates at the profile's commit rate.
//
// The rates are constants of the domain's profile (DomainProfile::rates),
// measured once and never timed at compile time, so a plan is a function of
// the system and its profile. A profile without measured rates costs every
// unit 1 (PlacementRates::unit). A measured profile without the batch rate
// a candidate needs fails the compile. A pin (Predicate::pin,
// Domain::pin_bit_checks) overrides the costs.
//
// Proof bytes are counted (no measurement): a batch's messages and
// committed pads, a circuit's layers, a triple's three coordinates;
// committed coordinates in bytes through Ligero's opened columns. The
// report flags a choice that grows the proof by more than kFlagBytes over
// the smallest; bytes do not decide.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLACEMENT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLACEMENT_H_

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <functional>
#include <map>
#include <string>
#include <vector>

#include "gordiehowe/expr.h"
#include "gordiehowe/compiler/placement_rates.h"

namespace proofs::gordiehowe::compiler {

// A choice whose proof bytes exceed the smallest candidate's by more than
// this is flagged in the report.
constexpr double kFlagBytes = 16384;

// One candidate of a group: admissible or why not, its cost and bytes.
struct PlacementCandidate {
  Placement where = Placement::kCircuit;
  bool admissible = false;
  double us = 0;
  double bytes = 0;
  size_t terms = 0;     // kCircuit: the group's quad terms
  unsigned width = 0;   // kBatch: the skip width
  std::string why_not;  // when not admissible
};

// A group's target, the candidates considered and the reason.
struct PlacementChoice {
  Placement where = Placement::kCircuit;
  unsigned width = 0;  // kBatch: the skip width
  std::string why;
  std::vector<PlacementCandidate> candidates;
  // The chosen candidate's bytes over the smallest admissible one's.
  double growth = 0;
  // "circuit 1.2 ms (3072 terms, 2.1 KB); field batch 0.4 ms (w = 4, 3.0
  // KB);
  // quadratic triples: not a b - c on full-field cells"
  std::string costs() const {
    std::string out;
    for (const auto &c : candidates) {
      if (!out.empty()) out += "; ";
      out += placement_name(c.where);
      if (!c.admissible) {
        out += ": " + c.why_not;
        continue;
      }
      char b[128];
      if (c.us > 0 || c.where == Placement::kCircuit) {
        std::snprintf(b, sizeof(b), " %.3f ms", c.us / 1000);
        out += b;
      }
      if (c.where == Placement::kCircuit) {
        std::snprintf(b, sizeof(b), " (%zu terms, %.1f KB)", c.terms,
                      c.bytes / 1024);
        out += b;
      } else if (c.where == Placement::kBatch) {
        std::snprintf(b, sizeof(b), " (w = %u, %.1f KB)", c.width,
                      c.bytes / 1024);
        out += b;
      } else {
        std::snprintf(b, sizeof(b), " (%.1f KB)", c.bytes / 1024);
        out += b;
      }
    }
    return out;
  }
};

// The provisional pass (compiled_domain.h): a domain compiled once with
// every group at its default target, which fixes the tableau whose rows
// the costs count. Set while that pass runs (ProvisionalPass).
inline bool &provisional_pass() {
  thread_local bool on = false;
  return on;
}
struct ProvisionalPass {
  bool prev;
  ProvisionalPass() : prev(provisional_pass()) { provisional_pass() = true; }
  ~ProvisionalPass() { provisional_pass() = prev; }
};

// What a group admits, and its size.
struct CheckGroup {
  size_t n = 0;  // instances (coordinates)
  // The batch's counted work in one proof (op_counts.h), which the field's
  // batch rates price; its operands per instance, which unit rates count.
  OpCounts work;
  size_t operands = 1;
  unsigned degree = 2;  // Q's degree (batch)
  BatchEval eval = BatchEval::kSubfield;
  size_t parts = 1;  // merged predicates
  // Triples: why not, or "" when admissible; the quadratic rows they add to
  // the provisional tableau, and its block_enc.
  std::string triple_not;
  size_t triple_rows = 0, block_enc = 0;
  // The compressions the triples' rows add to hashing each of the
  // provisional tableau's columns.
  size_t triple_hash_blocks = 0;
  // The circuit's quad terms for the whole group.
  size_t circuit_terms = 0;
  // The batch: why not, or "" when admissible.
  std::string batch_not;
  // Counted proof bytes of each target, and the batch's per width (its
  // message count depends on it).
  double bytes_triple = 0, bytes_circuit = 0;
  std::function<double(unsigned)> bytes_batch;
  // Committed coordinates the circuit and the batch target each add (a
  // realization's own values: conv's C or z), at the rate of subfield
  // coordinates when CELLS_SUB, of full-field cells otherwise.
  size_t cells_circuit = 0, cells_batch = 0;
  bool cells_sub = true;
};

// The target of G under RATES (unit rates when none are measured): the
// circuit unless the cheapest admissible target beats it by more than
// kDefaultMarginPercent (beats_default), then that target (ties in the
// order triples, batch). A batch the measured rates have no rate for
// (batch_rates) takes no part in that choice ("no rates"). PIN (not kAuto)
// decides instead when it is admissible (the caller refuses an
// inadmissible pin), with or without rates; a pinned batch without rates
// carries no cost.
inline PlacementChoice choose_placement(const PlacementRates &measured,
                                        const CheckGroup &g, Placement pin) {
  const PlacementRates rates = measured.or_unit();
  PlacementChoice ch;
  // The provisional pass places every unpinned group at its default.
  if (provisional_pass() && pin == Placement::kAuto) {
    ch.where = Placement::kCircuit;
    ch.why = "provisional";
    return ch;
  }
  const double nn = double(g.n);
  PlacementCandidate tri{Placement::kQuadratic};
  tri.admissible = g.triple_not.empty();
  tri.why_not = g.triple_not;
  tri.us = nn * (rates.triple + rates.triple_b * double(g.block_enc)) +
           double(g.triple_rows) *
               (rates.triple_row + rates.triple_row_b * double(g.block_enc)) +
           double(g.triple_hash_blocks) * rates.triple_hash *
               double(g.block_enc) +
           rates.triple_fixed + rates.triple_fixed_b * double(g.block_enc);
  tri.bytes = g.bytes_triple;
  const double cell = g.cells_sub ? rates.commit_sub : rates.commit_full;
  PlacementCandidate circ{Placement::kCircuit};
  circ.admissible = true;
  circ.terms = g.circuit_terms;
  circ.us = double(g.circuit_terms) * rates.gkr_term +
            double(g.cells_circuit) * cell;
  circ.bytes = g.bytes_circuit;
  PlacementCandidate bat{Placement::kBatch};
  bat.admissible = g.batch_not.empty();
  bat.why_not = g.batch_not;
  // Admissible but without rates: a pin may take it, the choice may not.
  bool bat_priced = bat.admissible;
  if (bat.admissible) {
    bat.width = g.eval == BatchEval::kBitSliced ? 16 : 4;
    if (rates.unit_rates) {
      bat.us = 1 + nn * double(g.operands) + double(g.parts - 1) +
               double(g.cells_batch) * cell;
    } else if (const auto b = rates.batch_rates(g.eval, g.degree, g.n)) {
      bat.us = b->cost(g.work) + double(g.cells_batch) * cell;
    } else {
      bat_priced = false;
    }
  }
  // A batch's bytes build its skip (MaskedFieldSkip's pad monomials, costly
  // at high degree): only for a batch the choice weighs or a pin takes.
  if (bat.admissible && g.bytes_batch &&
      (bat_priced || pin == Placement::kBatch))
    bat.bytes = g.bytes_batch(bat.width);
  ch.candidates = {tri, circ, bat};
  if (pin == Placement::kAuto && bat.admissible && !bat_priced) {
    ch.candidates[2].admissible = false;
    ch.candidates[2].why_not = "no rates";
  }
  auto growth = [&](const PlacementCandidate &chosen) {
    double lo = chosen.bytes;
    for (const auto &c : ch.candidates)
      if (c.admissible && c.bytes < lo) lo = c.bytes;
    return chosen.bytes - lo;
  };
  if (pin != Placement::kAuto) {
    ch.where = pin;
    ch.width = pin == Placement::kBatch ? bat.width : 0;
    ch.why = "pinned";
    for (const auto &c : ch.candidates)
      if (c.where == pin && c.admissible) ch.growth = growth(c);
    return ch;
  }
  const PlacementCandidate *best = &ch.candidates[1];
  for (const auto &c : ch.candidates)
    if (c.admissible && c.us < best->us) best = &c;
  if (!beats_default(best->us, ch.candidates[1].us)) {
    best = &ch.candidates[1];
    ch.why = "default";
  } else {
    ch.why = "cheapest";
  }
  ch.where = best->where;
  ch.width = best->width;
  ch.growth = growth(*best);
  return ch;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLACEMENT_H_
