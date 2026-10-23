-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Semantics

@[expose] public section

/-!
# GordieHowe: statement bounds from the member checks

The export declares a statement bound (`Value.bound`, `RealizedProgram.declaredRanges`) on a
statement value that a member check bounds coordinate by coordinate (`MemberCheck.coordBound?`: an
entry check `below q` bounds every coordinate by `q`, `limbBits b w L` every limb by `2^w`). A
statement passing the member checks whose bounded coordinates are the casts of their integer
readings then lies within the declared bounds (`RealizedProgram.stmtBounded_of_checks`), which the
honest strategies of the applications use for their statements.
-/

namespace GordieHowe.RealizedProgram

/-- **The bound a member check sets on every coordinate of its member's value**: `q` for an entry
check `below q`, `2^w` for `limbBits b w L` (`MemberCheck.kind?`), none for any other. -/
def MemberCheck.coordBound? (m : MemberCheck) : Option ℕ :=
  match m.kind? with
  | some (.below q _) => some q
  | some (.limbBits _ w _) => some (2 ^ w)
  | _ => none

variable {ir : RealizedProgram} {I : Interp}

/-- **A member check that accepts the statement bounds its member's coordinates**
(`MemberCheck.coordBound?`, `MemberHolds`). -/
theorem memberHolds_coord_lt {x : ir.Valuation I} {m : MemberCheck} (h : ir.MemberHolds I x m)
    {v : ℕ} (hv : ir.memberValue? m.member = some v) {q : ℕ} (hq : m.coordBound? = some q) :
    ∀ i < (ir.value v).size, (I (ir.valueField v)).toNat (x v i) < q := by
  unfold MemberHolds at h
  rw [hv] at h
  unfold MemberCheck.coordBound? at hq
  unfold MemberCheck.entryBound? at h
  split at hq
  · rename_i q' w hk
    cases hq
    simp only [hk] at h
    exact h
  · rename_i b w L hk
    cases hq
    simp only [hk] at h
    exact h.1
  · cases hq

/-- **A statement passing the member checks lies within the declared bounds** (`StmtBounded`)
when every declared bound is at least a member check's bound on the same value (`hcov`) and every
bounded coordinate is the cast of its integer reading (`hnat`). -/
theorem stmtBounded_of_checks {x : ir.Valuation I} (hok : ir.StatementOk I x)
    (hcov : ∀ vN ∈ ir.declaredRanges, ∃ m ∈ ir.statement.checks,
      ir.memberValue? m.member = some vN.1 ∧ ∃ q, m.coordBound? = some q ∧ q ≤ vN.2)
    (hnat : ∀ vN ∈ ir.declaredRanges, ∀ i < (ir.value vN.1).size,
      (((I (ir.valueField vN.1)).toNat (x vN.1 i) : ℕ) : (I (ir.valueField vN.1)).K) =
        x vN.1 i) :
    ir.StmtBounded I x := by
  intro vN hvN i hi
  obtain ⟨m, hm, hv, q, hq, hle⟩ := hcov vN hvN
  exact ⟨_, lt_of_lt_of_le (memberHolds_coord_lt (hok m hm) hv hq i hi) hle,
    (hnat vN hvN i hi).symm⟩

end GordieHowe.RealizedProgram
