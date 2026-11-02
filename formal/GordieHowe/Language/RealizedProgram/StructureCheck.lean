-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.IvlSource
public import GordieHoweNative.Language.RealizedProgram.Structure
public import GordieHowe.Language.RealizedProgram.NatTrie
public import GordieHowe.ProofSystem.GKR.Twin
public import GordieHoweNative.Language.RealizedProgram.StructureCheck

@[expose] public section

/-!
# Reading and checking the structure records

The common pieces the checkers of the structure records (`GordieHowe.RealizedProgram.Structure`)
share:

* **pointer reads**: a keyed list read through a trie built once (`NatTrie.ofList`, whose entries
  are entries of the list, `NatTrie.mem_of_get?_ofList`), and the gadget record whose first
  predicate is a given predicate (`Structure.gadgetAt`, `Structure.gadgetAt_spec`). A read needs no
  uniqueness of the keys: whichever entry is read is checked at the pointer;
* **the failure** a checker's twin reports (`StructFailure`: the item, the slot and the reason);
* **the keys' order**: every list of pairs of the records is sorted by its key with no repeated key
  (`Structure.keysOkB`, a sweep, and its twin `Structure.keysOkE`).

The definitions are in `GordieHoweNative/Language/RealizedProgram/StructureCheck.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.Twin

/-! ## Pointer reads -/

namespace NatTrie

variable {α : Type}

/-- **A trie built from a list reads entries of the list or of the starting trie.** -/
theorem mem_of_get?_foldl (l : List (Nat × α)) (t : NatTrie α) {k : Nat} {x : α}
    (h : (l.foldl (fun t kx => t.set kx.1 kx.2) t).get? k = some x) :
    (k, x) ∈ l ∨ t.get? k = some x := by
  induction l generalizing t with
  | nil => exact .inr h
  | cons a l ih =>
    rcases ih _ h with hm | ht
    · exact .inl (List.mem_cons_of_mem _ hm)
    · rw [get?_set] at ht
      split at ht
      · subst_vars
        cases ht
        exact .inl List.mem_cons_self
      · exact .inr ht

/-- **A trie built from a list reads only entries of the list.** -/
theorem mem_of_get?_ofList {l : List (Nat × α)} {k : Nat} {x : α}
    (h : (ofList l).get? k = some x) : (k, x) ∈ l := by
  rcases mem_of_get?_foldl l .nil h with hm | hn
  · exact hm
  · rw [get?_nil] at hn
    cases hn

end NatTrie

namespace Structure

theorem gadgetAt_foldl (l : List (Gadget × Nat)) (t : NatTrie Nat) {p i : Nat}
    (h : (l.foldl (fun t gi =>
      match gi.1.preds with
      | p :: _ => t.set p gi.2
      | [] => t) t).get? p = some i) :
    (∃ g, (g, i) ∈ l ∧ g.preds.head? = some p) ∨ t.get? p = some i := by
  induction l generalizing t with
  | nil => exact .inr h
  | cons a l ih =>
    rcases ih _ h with ⟨g, hg, hp⟩ | ht
    · exact .inl ⟨g, List.mem_cons_of_mem _ hg, hp⟩
    · obtain ⟨g, j⟩ := a
      cases hq : g.preds with
      | nil =>
        simp only [hq] at ht
        exact .inr ht
      | cons q qs =>
        simp only [hq, NatTrie.get?_set] at ht
        split at ht
        · subst_vars
          cases ht
          exact .inl ⟨g, List.mem_cons_self, by simp [hq]⟩
        · exact .inr ht

/-- **The record `gadgetAt` names has that first predicate.** -/
theorem gadgetAt_spec {S : Structure} {p i : Nat} (h : S.gadgetAt.get? p = some i) :
    ∃ g, S.gadgets[i]? = some g ∧ g.preds.head? = some p := by
  rcases gadgetAt_foldl _ _ h with ⟨g, hg, hp⟩ | hn
  · exact ⟨g, List.mem_zipIdx_iff_getElem?.1 hg, hp⟩
  · rw [NatTrie.get?_nil] at hn
    cases hn

end Structure

/-! ## The keys' order -/

/-- **A keyed list is sorted by its key with no repeated key**, as a check whose failure names the
list `item` and the key out of order. -/
def keysSortedE {α : Type} (item : Nat) : List (Nat × α) → Except StructFailure Unit
  | a :: b :: rest =>
    seqE (guardE (decide (a.1 < b.1)) ⟨item, b.1, .badKey⟩) (keysSortedE item (b :: rest))
  | _ => .ok ()

/-- **A list keyed by pairs is sorted by its key, lexicographically, with no repeated key.** -/
def pairKeysSortedE {α : Type} (item : Nat) : List ((Nat × Nat) × α) → Except StructFailure Unit
  | a :: b :: rest =>
    seqE (guardE (decide (a.1.1 < b.1.1 ∨ (a.1.1 = b.1.1 ∧ a.1.2 < b.1.2))) ⟨item, b.1.1, .badKey⟩)
      (pairKeysSortedE item (b :: rest))
  | _ => .ok ()

namespace Structure

/-- **Every list of pairs of the records is sorted by its key with no repeated key**, the lists
numbered in `Structure`'s field order. -/
def keysOkE (S : Structure) : Except StructFailure Unit :=
  seqE (keysSortedE 1 S.origins) <| seqE (keysSortedE 2 S.messages) <|
  seqE (keysSortedE 3 S.boundRecs) <| seqE (keysSortedE 4 S.memberValues) <|
  seqE (keysSortedE 5 S.routes) <| seqE (pairKeysSortedE 6 S.logupHosts) <|
  seqE (keysSortedE 7 S.macHosts) <| seqE (keysSortedE 8 S.chalValues) <|
  seqE (keysSortedE 9 S.ivlSources) <| seqE (keysSortedE 10 S.tableGadgets) <|
  seqE (keysSortedE 11 S.macRequests) (keysSortedE 12 S.modRequests)

/-- **The keys' order**, as a `Bool` (`okB` of `keysOkE`). -/
def keysOkB (S : Structure) : Bool := okB S.keysOkE

end Structure

end GordieHowe.RealizedProgram
