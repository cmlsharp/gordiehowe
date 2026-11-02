-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Structure
public import GordieHoweNative.ProofSystem.GKR.Twin

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.StructureCheck`

The definitions of `GordieHowe.Language.RealizedProgram.StructureCheck` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/StructureCheck.lean`, which imports this module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

open GordieHowe.Twin

namespace NatTrie

variable {α : Type}

/-- **The trie of a keyed list**: each entry set in turn, so a later entry of a key replaces an
earlier one. -/
def ofList (l : List (Nat × α)) : NatTrie α :=
  l.foldl (fun t kx => t.set kx.1 kx.2) .nil

end NatTrie

namespace Structure

/-- **The gadget records by their first predicate**: key `preds[0]`, value the record's index;
built once from the emitted records (a later record of the same first predicate replaces an
earlier one). -/
def gadgetAt (S : Structure) : NatTrie Nat :=
  S.gadgets.zipIdx.foldl
    (fun t gi =>
      match gi.1.preds with
      | p :: _ => t.set p gi.2
      | [] => t)
    .nil

end Structure

/-- **Why a structure check failed.** Each batch of the checkers appends its own reasons. -/
inductive StructReason where
  /-- A list of pairs is not sorted by its key, or repeats a key. -/
  | badKey
  /-- No record at the pointer. -/
  | noRecord
  /-- The record at the pointer has another kind. -/
  | wrongKind
  /-- A slot of the record does not match its expectation. -/
  | slotMismatch
  /-- A predicate's role is not the record's. -/
  | roleMismatch
  /-- An item the records must cover is not covered. -/
  | uncovered
  /-- A value has no interval. -/
  | noIvl
  /-- An item at the pointer has another name. -/
  | nameMismatch
  /-- Batch 1 (MAC sites): the record at the pointer is no `macSite` record. -/
  | notMacSite
  /-- Batch 1: the `macSite` record has no site at the slot. -/
  | noSlot
  /-- Batch 1: the record's first predicate is no cross-field `equal`. -/
  | notCross
  /-- Batch 1: the record's site is another cross-field `equal`'s. -/
  | wrongSite
  /-- Batch 1: the predicate does not play the MAC role its step names. -/
  | macRole
  /-- Batch 1: the site's MAC facts do not check. -/
  | siteFacts
  -- Batch 2 (companion rows, interval sources, type roles).
  /-- A pointer past the end of its list. -/
  | badPointer
  /-- Batch 3 (lookups). The lookup at a bound value's pointer does not have the value as its
  record bound to its digits (the slot names the lookup). -/
  | notBoundRec
  /-- A two-sided or digit lookup does not have one record and a range. -/
  | lookupShape
  /-- A lookup whose digits are generated as a quotient digit's fails that digit's check
  (`commLookupCB`). -/
  | commLookup
  /-- A lookup whose digits are generated as its own fails its facts (`DigitLookupFactsC`). -/
  | lookupFacts
  -- Batch 4 (placement: routes, hosts, challenge values).
  /-- The program has no domain. -/
  | nonempty
  /-- A listed challenge value does not hold its challenge. -/
  | chalValue
  /-- A value holds a challenge before its listed value, or a challenge has no listed value. -/
  | chalSweep
  /-- A batch fails the batch check (`batchOkB`). -/
  | batch
  /-- A predicate that needs a route has none. -/
  | routeMissing
  /-- A route of a predicate that needs none, or a route left over. -/
  | routeExtra
  /-- The routed predicate has no domain of the program. -/
  | routeDomain
  /-- The route's row, triple, batch part or circuit entry is not the predicate's. -/
  | routePointer
  /-- The routes into a batch are not its parts with their indices, in order. -/
  | batchRoutes
  /-- The realized route's predicate or conversions do not admit the predicate. -/
  | realized
  /-- The LogUp hosts' keys are not the tables' groups in order. -/
  | logupKeys
  /-- The LogUp host's circuit entry is not the group's LogUp identity. -/
  | logupPointer
  /-- A predicate that needs its H half hosted has no host, or another predicate has one. -/
  | macHKeys
  /-- The H half's host entry is not the predicate's H half. -/
  | macHPointer
  /-- No value of the challenge's field holds a table's challenge. -/
  | alpha
  /-- A circuit entry is not covered by the honest prover. -/
  | entry
  /-- A node-typed value's type does not follow from its domain's cells. -/
  | types
  /-- Batch 6 (names). An entry of `messages` names a value that is not its key's message. -/
  | notMessage
  /-- The value at a member check's pointer is not the check's member. -/
  | notMember
  /-- An earlier value than the pointer's is the member check's member (the slot names it). -/
  | earlierMember
  /-- The member check does not hold at the pointer's value (`CheckOk`). -/
  | checkFails
  /-- The plan and the program have different numbers of domains. -/
  | domainCount
  /-- The plan's domain at a position is not the program's domain there. -/
  | domainMismatch
  /-- A packing edge breaks the tree condition at its parent (the slot names the parent). -/
  | treeEdge
  /-- A cell's node does not have the degree of an edge whose child it is, or of the field. -/
  | nodeDegree
  deriving Repr, DecidableEq, Inhabited

/-- **The failure of a structure check**: the item (a gadget record's index, or a program or plan
id), the slot, and the reason. -/
structure StructFailure where
  /-- The item. -/
  item : Nat
  /-- The slot. -/
  slot : Nat
  /-- The reason. -/
  reason : StructReason
  deriving Repr, DecidableEq, Inhabited

end GordieHowe.RealizedProgram
