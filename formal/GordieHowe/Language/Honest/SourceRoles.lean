-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.RealizedProgram.SourceRoles

public section

namespace GordieHowe.RealizedProgram

variable {ir : RealizedProgram}

/-- **The checked role table covers every source execution coordinate.**
The no-pad-copy premise comes from the completion certificate's committed facts. -/
theorem SourceRolesOk.exec_covered {rs : List SourceRoleEntry}
    (h : SourceRolesOk ir rs) {v i : Nat} (hc : ir.ExecCoord v i) (hs : ir.IsSourceValue v)
    (hpad : ∀ u < ir.values.length, ir.IsSourceValue u → (ir.value u).kind.isPadCopy = false) :
    ∃ r, (sourceRoleTable rs).get? v = some r := by
  obtain ⟨hv, _, hk⟩ := hc.source_kind hs hpad
  apply h.covered v hv
  have hrole : (ir.value v).role = .source := hs
  rcases hk with hk | hk
  · simp only [Value.needsSourceRole, hrole, decide_true, hk, Bool.true_and]
  · cases hx : (ir.value v).kind <;>
      simp_all only [Kind.isBound, Bool.false_eq_true, Value.needsSourceRole,
        decide_true, Bool.true_and]

/-- Every valid source bound has an entry in the checked source-role table. -/
theorem SourceRolesOk.bound_covered {rs : List SourceRoleEntry}
    (h : SourceRolesOk ir rs) {v : Nat} (hv : v < ir.values.length)
    (hs : ir.IsSourceValue v) (hb : (ir.value v).kind.isBound = true) :
    ∃ r, (sourceRoleTable rs).get? v = some r := by
  apply h.covered v hv
  have hrole : (ir.value v).role = .source := hs
  cases hx : (ir.value v).kind <;>
    simp_all only [Kind.isBound, Bool.false_eq_true, Value.needsSourceRole,
      decide_true, Bool.true_and]

end GordieHowe.RealizedProgram
