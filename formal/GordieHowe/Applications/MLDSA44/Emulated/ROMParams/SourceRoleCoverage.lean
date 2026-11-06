-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Facts
public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Embed

public section

/-! The hash-field cell coverage required by the existing emulated honest strategy follows from
checked private-field ownership, source-role coverage, and the existing native embedding. -/

namespace GordieHowe.MLDSA44.Emulated.ROMParams.SourceRoleCoverage
open RealizedProgram
open Generated.MLDSA44.Native.ROMParams
open Program (program)
/-- Every checked hash-field role belongs to the existing embedded value domain. -/
private theorem row_mem {r : SourceRoleEntry} (hm : r ∈ SourceRoles.roles) :
    r.field ≠ 1 ∨ r.value ∈ MLDSA44.Emulated.hV := by
  have h : SourceRoles.roles.all
      (fun r => decide (r.field ≠ 1 ∨ r.value ∈ MLDSA44.Emulated.hV)) = true := by
    rw [SourceRoles.roles_eq]
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h r hm)

/-- A private native hash-field cell is covered by the embedded value domain. -/
theorem source_hV {v : Nat} (hv : v < program.values.length)
    (hp : program.privCellB v = true) (hf : program.valueField v = 1) :
    v ∈ MLDSA44.Emulated.hV := by
  have hs := ShapeFacts.value_w1_2ewords_private_field_sources v hv hp hf
  have hk := kind_of_privCellB hp
  have hn : (program.value v).needsSourceRole = true := by
    simp only [Value.needsSourceRole, show (program.value v).role = .source from hs,
      decide_true, hk, Bool.true_and]
  obtain ⟨r, hr⟩ := SourceRoleFacts.rolesOk.covered v hv hn
  obtain ⟨hm, hrv⟩ := sourceRoleTable_mem hr
  have hfield : r.field = 1 := (SourceRoleFacts.rolesOk.lookup hr).2.2.1.symm.trans hf
  have hv' := (row_mem hm).resolve_left (fun h => h hfield)
  simpa only [hrv] using hv'

/-- The existing embedding preserves every native hash-field private cell. -/
theorem hCells (target : RealizedProgram)
    (hE : program.Embedding target MLDSA44.Emulated.σ
      MLDSA44.Emulated.hV MLDSA44.Emulated.hR)
    (hwf : target.WellFormed) :
    ∀ v < program.values.length, program.privCellB v = true → program.valueField v = 1 →
      v ∈ MLDSA44.Emulated.hV ∧ target.privCellB (v + 1) = true := by
  intro v hv hp hf
  have hm := source_hV hv hp hf
  refine ⟨hm, ?_⟩
  obtain ⟨_, hv', _, _, _, _, hk, _⟩ := hE.vals v hm
  rw [kind_of_privCellB hp] at hk
  exact hwf.privCellB_of_kind_priv hv' (MLDSA44.Emulated.σ.kindCorr_priv hk)

end GordieHowe.MLDSA44.Emulated.ROMParams.SourceRoleCoverage
