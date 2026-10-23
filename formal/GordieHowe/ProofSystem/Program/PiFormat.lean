-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.PhasedFormat

@[expose] public section

/-!
# The writes and readers of finite products

Write codecs and challenge readers of finite dependent products, for application phases whose
message and challenge types are products over a finite index set (the plan-level programs: a
phase's message is its late values, a phase's challenge its challenges):

- `WriteCodec.piFin`: the components of `(i : Fin n) → β i` written one after the other, after an
  empty byte string (so the write is never empty), with its bound `piFin_B`;
- `WriteCodec.piList`: the components of `(a : α) → β a` written in the order of a duplicate-free
  list `l` of every index (`List.Nodup.getEquivOfForallMemList`);
- `Codec.FieldBytes.ofSubgroup`: the bytes of an element of an additive subgroup as the bytes of
  the element;
- `CReader.piList`: the components of `(a : α) → β a` drawn one after the other in the order of `l`
  (`CReader.piDep`), with its load.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM

namespace WriteCodec

/-- **The components of a finite dependent product written in order**, after an empty byte
string: the write of `(i : Fin n) → β i` is `bstr 0 ‖ C 0 ‖ … ‖ C (n − 1)`. -/
def piFin : (n : ℕ) → {β : Fin n → Type} → (∀ i, WriteCodec (β i)) → WriteCodec (∀ i, β i)
  | 0, _, _ => (bstr 0).mapEquiv
      { toFun := fun _ i => i.elim0, invFun := fun _ i => i.elim0,
        left_inv := fun _ => funext fun i => i.elim0, right_inv := fun _ => funext fun i => i.elim0 }
  | n + 1, β, C => ((C 0).prod (piFin n fun i => C i.succ)).mapEquiv (Fin.consEquiv β).symm

/-- The bound of `piFin`: the empty byte string's `9` bytes and the components' bounds. -/
theorem piFin_B : (n : ℕ) → {β : Fin n → Type} → (C : ∀ i, WriteCodec (β i)) →
    (piFin n C).B = 9 + ∑ i, (C i).B
  | 0, _, _ => rfl
  | n + 1, β, C => by
    change (C 0).B + (piFin n fun i => C i.succ).B = _
    rw [piFin_B n, Fin.sum_univ_succ]
    omega

variable {α : Type} [DecidableEq α] {β : α → Type}

/-- **The components of a product over a finite index set written in the order of `l`**, a
duplicate-free list of every index (`piFin` through `List.Nodup.getEquivOfForallMemList`). -/
def piList (l : List α) (hl : l.Nodup) (hall : ∀ a, a ∈ l) (C : ∀ a, WriteCodec (β a)) :
    WriteCodec (∀ a, β a) :=
  (piFin l.length fun i => C (hl.getEquivOfForallMemList l hall i)).mapEquiv
    (Equiv.piCongrLeft β (hl.getEquivOfForallMemList l hall)).symm

/-- The bound of `piList`: the empty byte string's `9` bytes and the components' bounds, in the
order of `l`. -/
theorem piList_B (l : List α) (hl : l.Nodup) (hall : ∀ a, a ∈ l) (C : ∀ a, WriteCodec (β a)) :
    (piList l hl hall C).B = 9 + (l.map fun a => (C a).B).sum := by
  change (piFin l.length _).B = _
  rw [piFin_B]
  congr 1
  conv_rhs => rw [← List.ofFn_get l, List.map_ofFn, List.sum_ofFn]
  rfl

end WriteCodec

namespace Codec.FieldBytes

variable {K : Type} [AddGroup K] {fb : ℕ}

/-- **The bytes of an element of an additive subgroup**: the bytes of the element; a byte string
parses when it is the bytes of an element of the subgroup (`ofSection` at the inclusion and the
retraction sending the rest to `0`). -/
def ofSubgroup [DecidableEq K] (FB : FieldBytes K fb) (H : AddSubgroup K)
    [DecidablePred (· ∈ H)] : FieldBytes H fb :=
  FB.ofSection Subtype.val (fun x => if h : x ∈ H then ⟨x, h⟩ else 0) fun s => by
    simp [s.2]

end Codec.FieldBytes

namespace CReader

variable {α : Type} [DecidableEq α] {β : α → Type} [∀ a, Fintype (β a)]

/-- **The components of a product over a finite index set drawn in the order of `l`**, a
duplicate-free list of every index, each component's load at most `L` (`piDep` through
`List.Nodup.getEquivOfForallMemList`). -/
def piList (l : List α) (hl : l.Nodup) (hall : ∀ a, a ∈ l) (r : ∀ a, CReader (β a)) (L : Load)
    (hL : ∀ a, (r a).load ≤ L) : CReader (∀ a, β a) :=
  haveI : Fintype (∀ i : Fin l.length, β (hl.getEquivOfForallMemList l hall i)) :=
    Pi.instFintype
  (piDep (fun i => r (hl.getEquivOfForallMemList l hall i)) L fun _ => hL _).map
    (Equiv.piCongrLeft β (hl.getEquivOfForallMemList l hall))

@[simp] theorem piList_load (l : List α) (hl : l.Nodup) (hall : ∀ a, a ∈ l)
    (r : ∀ a, CReader (β a)) (L : Load) (hL : ∀ a, (r a).load ≤ L) :
    (piList l hl hall r L hL).load = L.nsmul l.length :=
  rfl

end CReader

end GordieHowe.SPBCS
