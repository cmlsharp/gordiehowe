-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Annotations
public import GordieHowe.Language.RealizedProgram.StructureCheck
public import GordieHoweNative.Language.RealizedProgram.MemberValues

@[expose] public section

/-!
# The member checks' values at the structure records' pointers

A member check of the statement reads the value of its member (`RealizedProgram.memberValue?`, the
first value that is the member, `isMemberOf`). The compiler names that value per check
(`Structure.memberValues`, keyed by the check's index), and the checks below read it at the
pointer, so `memberValue?` stays the meaning and is never evaluated:

* **the pointer check** (`memberValuesE`, its `Bool` `memberValuesB`): every check has an entry,
  the entry's value is the check's member, no earlier value is (a sweep of the values), and the
  check holds at that value (`checkAtB`, `CheckOk`'s arms);
* **its soundness**: the entry is `memberValue?` (`memberValue?_of_memberValuesB`), and every
  check is well formed (`checksOk_of_memberValuesB`, the member-check clause of
  `RealizedProgram.WellFormed`);
* **`WellFormed` through the annotations and the pointers** (`wellFormed_of_ann_members`, the form
  the generated modules decide: every hypothesis a `Bool` check, so elaboration reduces nothing);
* **facts at a check's pointer** (`checkAtPtrB`, `check_of_ptr`; over every check `checksAtPtrsB`,
  `forall_checks_of_ptrs`), for the applications.

The definitions are in `GordieHoweNative/Language/RealizedProgram/MemberValues.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.Twin

/-- **A list check passes exactly when it passes at every index** (`allE`, from index `i`). -/
theorem okB_allE_iff {ε α : Type} {f : ℕ → α → Except ε Unit} :
    ∀ {i : ℕ} {l : List α}, okB (allE f i l) = true ↔
      ∀ j (hj : j < l.length), okB (f (i + j) l[j]) = true
  | _, [] => by simp [allE, okB]
  | i, x :: xs => by
    rw [allE, okB_seqE, Bool.and_eq_true, okB_allE_iff]
    constructor
    · rintro ⟨h0, h⟩ j hj
      cases j with
      | zero => simpa using h0
      | succ j =>
        rw [show i + (j + 1) = i + 1 + j by omega]
        simpa using h j (by simpa using hj)
    · intro h
      refine ⟨h 0 (by simp), fun j hj => ?_⟩
      have := h (j + 1) (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega] at this
      simpa using this

/-- **A list check passing passes at every index** (`allE`, from index `i`). -/
theorem okB_allE_getElem {ε α : Type} {f : ℕ → α → Except ε Unit} {i : ℕ} {l : List α}
    (h : okB (allE f i l) = true) : ∀ j (hj : j < l.length), okB (f (i + j) l[j]) = true :=
  okB_allE_iff.1 h

end GordieHowe.Twin

namespace GordieHowe.RealizedProgram

open GordieHowe.Twin

section

variable (ir : RealizedProgram)

theorem isMemberOf_eq (member : String) (v : ℕ) :
    ir.isMemberOf member v = isMemberV member (ir.value v) := rfl

/-- **`p` holds of check `k` and the value at its pointer.** -/
def checkAtPtrB (S : Structure) (p : MemberCheck → ℕ → Bool) (k : ℕ) : Bool :=
  match ir.statement.checks[k]?, S.memberValueTab.get? k with
  | some m, some v => p m v
  | _, _ => false

/-- **`p` holds of every check and the value at its pointer.** -/
def checksAtPtrsB (S : Structure) (p : MemberCheck → ℕ → Bool) : Bool :=
  (List.range ir.statement.checks.length).all (ir.checkAtPtrB S p)

end

variable {ir : RealizedProgram} {S : Structure}

/-- **The pointer that checks is the member's value** (`memberValue?`, the first value that is the
member). -/
theorem memberValue?_of_memberAtE {k : ℕ} {m : MemberCheck} {v : ℕ}
    (h : okB (ir.memberAtE k m v) = true) : ir.memberValue? m.member = some v := by
  unfold memberAtE at h
  simp only [okB_seqE, okB_guardE, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hmem⟩, hall, -⟩ := h
  unfold memberValue?
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨hmem, v, by simpa using hv, by simp, fun j hj => ?_⟩
  have hjl : j < ir.values.length := by omega
  have := okB_allE_getElem hall j hjl
  simp only [Nat.zero_add, okB_guardE, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at this
  rcases this with hle | hn
  · omega
  · simp only [List.getElem_range, isMemberOf_eq, Bool.not_eq_true']
    rw [value_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
    exact hn

/-- **A check that holds at the member's value is well formed** (`CheckOk`). -/
theorem checkOk_of_checkAtB {m : MemberCheck} {v : ℕ} (hv : ir.memberValue? m.member = some v)
    (h : ir.checkAtB v m = true) : ir.CheckOk m := by
  unfold checkAtB at h
  unfold CheckOk
  rw [hv]
  split at h <;> simp_all

/-- **The entry of a check is its member's value** where the records check. -/
theorem memberValue?_of_memberValuesB (h : ir.memberValuesB S = true) {k : ℕ} {m : MemberCheck}
    (hk : ir.statement.checks[k]? = some m) {v : ℕ} (hv : S.memberValueTab.get? k = some v) :
    ir.memberValue? m.member = some v := by
  obtain ⟨hkl, rfl⟩ := List.getElem?_eq_some_iff.1 hk
  have := okB_allE_getElem h k hkl
  rw [Nat.zero_add, hv] at this
  exact memberValue?_of_memberAtE this

/-- **Every member check is well formed** (`CheckOk`, the member-check clause of
`RealizedProgram.WellFormed`) where the records check. -/
theorem checksOk_of_memberValuesB (h : ir.memberValuesB S = true) :
    ∀ m ∈ ir.statement.checks, ir.CheckOk m := by
  intro m hm
  obtain ⟨k, hkl, rfl⟩ := List.getElem_of_mem hm
  have := okB_allE_getElem h k hkl
  rw [Nat.zero_add] at this
  split at this
  · rename_i v hv
    refine checkOk_of_checkAtB (memberValue?_of_memberAtE this) ?_
    unfold memberAtE at this
    simp only [okB_seqE, okB_guardE, Bool.and_eq_true] at this
    exact this.2.2
  · cases this

/-- **`WellFormed`, through checked annotations and the member checks at the structure records'
pointers.** -/
theorem wellFormed_of_ann_members {a : ExprAnn} (h : ir.exprAnnOkB a = true) (S : Structure)
    (hA : ir.wellFormedA a = true) (hS : ir.memberValuesB S = true) : ir.WellFormed :=
  wellFormed_of_ann h hA (checksOk_of_memberValuesB hS)

/-- **A fact at check `k`'s pointer** is a fact of the check and its member's value. -/
theorem check_of_ptr (h : ir.memberValuesB S = true) {p : MemberCheck → ℕ → Bool} {k : ℕ}
    (hp : ir.checkAtPtrB S p k = true) :
    ∃ m, ir.statement.checks[k]? = some m ∧
      ∃ v, ir.memberValue? m.member = some v ∧ p m v = true := by
  unfold checkAtPtrB at hp
  split at hp
  · rename_i m v hm hv
    exact ⟨m, hm, v, memberValue?_of_memberValuesB h hm hv, hp⟩
  · cases hp

/-- **A fact at check `k`'s pointer**, as a member check of the statement. -/
theorem exists_check_of_ptr (h : ir.memberValuesB S = true) {p : MemberCheck → ℕ → Bool} {k : ℕ}
    (hp : ir.checkAtPtrB S p k = true) :
    ∃ m ∈ ir.statement.checks, ∃ v, ir.memberValue? m.member = some v ∧ p m v = true := by
  obtain ⟨m, hm, v, hv, hpv⟩ := check_of_ptr h hp
  exact ⟨m, List.mem_of_getElem? hm, v, hv, hpv⟩

/-- **A fact at every check's pointer** is a fact of every check and its member's value. -/
theorem forall_checks_of_ptrs (h : ir.memberValuesB S = true) {p : MemberCheck → ℕ → Bool}
    (hp : ir.checksAtPtrsB S p = true) :
    ∀ m ∈ ir.statement.checks, ∃ v, ir.memberValue? m.member = some v ∧ p m v = true := by
  intro m hm
  obtain ⟨k, hkl, rfl⟩ := List.getElem_of_mem hm
  obtain ⟨m', hm', v, hv, hpv⟩ :=
    check_of_ptr h (List.all_eq_true.1 hp k (List.mem_range.2 hkl))
  rw [List.getElem?_eq_getElem hkl, Option.some.injEq] at hm'
  subst hm'
  exact ⟨v, hv, hpv⟩

end GordieHowe.RealizedProgram
