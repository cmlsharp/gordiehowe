-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Facts
public import GordieHoweCerts.Applications.MLDSA44.Emulated.Frontend.Embed

public section

/-! The hash-field cell coverage required by the existing emulated honest strategy follows from
checked private-field ownership, source-role coverage, and the existing native embedding. -/

namespace GordieHowe.MLDSA44.Emulated.QROMParams.SourceRoleCoverage
open RealizedProgram
open Generated.MLDSA44.Native.QROMParams
open Program (program)
variable {V : List ℕ}
  (hrows : SourceRoles.roles.all (fun r => decide (r.field ≠ 1 ∨ r.value ∈ V)) = true)
include hrows

/-- A private native hash-field cell is covered by the embedded value domain `V`, which holds every
checked hash-field role. -/
theorem source_hV {v : Nat} (hv : v < program.values.length)
    (hp : program.privCellB v = true) (hf : program.valueField v = 1) : v ∈ V := by
  have hs := ShapeFacts.value_w1_2ewords_private_field_sources v hv hp hf
  have hk := kind_of_privCellB hp
  have hn : (program.value v).needsSourceRole = true := by
    simp only [Value.needsSourceRole, show (program.value v).role = .source from hs,
      decide_true, hk, Bool.true_and]
  obtain ⟨r, hr⟩ := SourceRoleFacts.rolesOk.covered v hv hn
  obtain ⟨hm, hrv⟩ := sourceRoleTable_mem hr
  have hfield : r.field = 1 := (SourceRoleFacts.rolesOk.lookup hr).2.2.1.symm.trans hf
  have hv' := (of_decide_eq_true (List.all_eq_true.mp hrows r hm)).resolve_left
    (fun h => h hfield)
  simpa only [hrv] using hv'

/-- An embedding preserves every native hash-field private cell, renamed. -/
theorem hCells (target : RealizedProgram) {σ : Renaming} {R : List ℕ}
    (hE : program.Embedding target σ V R) (hwf : target.WellFormed) :
    ∀ v < program.values.length, program.privCellB v = true → program.valueField v = 1 →
      v ∈ V ∧ target.privCellB (σ.val v) = true := by
  intro v hv hp hf
  have hm := source_hV hrows hv hp hf
  refine ⟨hm, ?_⟩
  obtain ⟨_, hv', _, _, _, _, hk, _⟩ := hE.vals v hm
  rw [kind_of_privCellB hp] at hk
  exact hwf.privCellB_of_kind_priv hv' (σ.kindCorr_priv hk)

end GordieHowe.MLDSA44.Emulated.QROMParams.SourceRoleCoverage
