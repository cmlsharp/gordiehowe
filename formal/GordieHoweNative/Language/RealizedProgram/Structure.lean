-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.IvlSource

/-!
# GordieHowe: the structure records

The compiler's structure records (`Structure`: the gadget records and the placement pointers) that
the certificate checkers read, in the Mathlib-free library `GordieHoweNative`, which Lake compiles
to a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
generated `Structure.lean` modules import this module directly; it has no companion module in
`GordieHowe`.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

/-- **The kind of a gadget record**, which fixes the meaning of its slots. -/
inductive GadgetKind where
  /-- `select_row` (`lib/table.h`): a row selected from a public table by a challenge. -/
  | selectRow
  /-- A spectral product form of a `mod_q` (`mod.h`, `product_sides`). -/
  | spectralProduct
  /-- The first-`n` cutoff selection (`lib/select.h`, `lib/cutoff_select.h`). -/
  | selectFirst
  /-- One Keccak permutation (`lib/keccak.h`), its rounds in order. -/
  | keccak
  /-- A MAC site (`mac.h`): a cross-field `equal` and its tails. -/
  | macSite
  /-- A `mod_q` in the field form. -/
  | modField
  /-- A `mod_q` with committed quotient digits. -/
  | modCommitted
  /-- A grouped `mod_q`. -/
  | modGrouped
  /-- A `mod_q` in the digit form. -/
  | modDigits
  /-- A `mod_q` in the one-digit form. -/
  | modOneDigit
  /-- A two-sided range lookup realization. -/
  | lookupTwoSided
  /-- A digit range lookup realization. -/
  | lookupDigits
  /-- A γ-packed lookup table (`assert_in.h`). -/
  | packedTable
  deriving Repr, DecidableEq, Inhabited

/-- **A part of a gadget record** where the kind needs expressions. -/
inductive GadgetPart where
  /-- A printed expression. -/
  | expr (e : Expr)
  /-- A kernel part of a spectral product: the scale's code, the value, its block count, the block,
  the operator's index and the operand's. -/
  | kernel (scale value blocks block op operand : Nat)
  /-- A run of a selection's stream: the bit view, and the slot of the zero it is padded with. -/
  | stream (bitView : Nat) (zeroSlot : Option Nat)
  /-- A selected record's kernel: record slot `record` is read by part `part` of the spectral
  product of predicate `pred`. -/
  | kernelOf (record pred part : Nat)
  deriving Repr, Inhabited

/-- **A gadget record.** -/
structure Gadget where
  /-- The kind. -/
  kind : GadgetKind
  /-- The predicates, in the kind's slot order. -/
  preds : List Nat
  /-- The values, in the kind's slot order. -/
  values : List Nat
  /-- The parameters, in the kind's slot order. -/
  params : List Nat
  /-- The parts, where the kind has them. -/
  parts : List GadgetPart := []
  deriving Repr, Inhabited

/-- **Where a value comes from**: gadget `gadget`'s value slot `slot`. -/
structure Origin where
  /-- The gadget record's index. -/
  gadget : Nat
  /-- The value slot. -/
  slot : Nat
  deriving Repr, DecidableEq, Inhabited

/-- **How a predicate is lowered**: affine rows (on views or on cells), the quadratic test, a
batch's part, a GKR circuit's entry, or the field equation of a realized predicate with its
conversions in mismatch order. -/
inductive Route where
  /-- Affine rows; `onViews` when they read views. -/
  | affine (onViews : Bool)
  /-- The quadratic test. -/
  | quadratic
  /-- Part `part` of batch `batch`. -/
  | batch (batch part : Nat)
  /-- Entry `entry` of GKR circuit `circuit`. -/
  | gkr (circuit entry : Nat)
  /-- The field equation of predicate `pred`, its conversions `convs` in mismatch order. -/
  | realized (pred : Nat) (convs : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- **The structure records of a program.** Every list of pairs is sorted by its first
component, with no repeated key. -/
structure Structure where
  /-- The gadget records. -/
  gadgets : List Gadget
  /-- Per created value, its origin. -/
  origins : List (Nat × Origin)
  /-- Per late value, its message value. -/
  messages : List (Nat × Nat)
  /-- Per bound value, the lookup whose record it is. -/
  boundRecs : List (Nat × Nat)
  /-- Per member check (its index), the value it reads. -/
  memberValues : List (Nat × Nat)
  /-- Per predicate, its route. -/
  routes : List (Nat × Route)
  /-- Per table group `(table, group)`, the hosting circuit entry `(circuit, entry)`. -/
  logupHosts : List ((Nat × Nat) × (Nat × Nat))
  /-- Per cross-field `equal` with a circuit-hosted H half, the hosting entry `(circuit, entry)`. -/
  macHosts : List (Nat × (Nat × Nat))
  /-- Per challenge, the value holding it. -/
  chalValues : List (Nat × Nat)
  /-- Per value with an interval, its interval source. -/
  ivlSources : List (Nat × IvlSource)
  /-- Per γ-packed table, its `packedTable` gadget record. -/
  tableGadgets : List (Nat × Nat)
  /-- Per MAC record of the plan (its index in `Plan.macs`), the indices in `Plan.requests` of the
  range requests its lowering reads, in the order of its form (`<name>.low`, `.high`, `.nowrap`;
  `<name>.q`; or `<name>.gq`, `.final.q`). -/
  macRequests : List (Nat × List Nat)
  /-- Per modular equality of the plan (its index in `Plan.modEqualities`), the indices in
  `Plan.requests` of its quotient digits' range requests, in the order of
  `Export.ModEquality.digitRequests`. -/
  modRequests : List (Nat × List Nat)
  deriving Repr, Inhabited

end GordieHowe.RealizedProgram
