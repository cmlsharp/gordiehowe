-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation

@[expose] public section

/-!
# GordieHowe: the realization step from valid derivations

The realization step (`GordieHowe.RealizedProgram.realizeLowering_of_derivs`) with valid derivations
(`DerivationsValid`) in place of the recognized realization shapes: the same
lowering data (the projection `bindAsg` and the realization events), its soundness from
`satAt_or_realEvent_of_derivs`, its challenge-use rule from `challengeUseAt_realEvent_of_derivs`
and its error bound (`eventBound_realizeLowering_of_derivs`) from
`probUniform_realEvent_le_of_derivs`, given the selections' bound (`SelSound`). The model reads no field-form linearity (`FieldFormModel`):
the derivations' rules state their own side conditions.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP ProofSystem.PhaseLayout
open scoped NNReal

section

variable {ir : RealizedProgram} (I : Interp) {primeNodes : ℕ → List String}

/-- **The realization step, from valid derivations**: the lowering for the derivations `D`,
valid (`DerivationsValid`) at the value ranges `declaredRanges ++ orng`. -/
def realizeLowering_of_derivs (hwf : ir.WellFormed) {orng : List (ℕ × ℕ)} {D : Derivations}
    (hv : ir.DerivationsValid primeNodes (ir.declaredRanges ++ orng) D)
    (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)
    (hO : ir.OpaqueRanges I orng) :
    Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (ir.Pred I)) (ir.Realized I) where
  proj a := ir.bindAsg a
  event k x a r := ∃ jj : ir.ChalAt k, ir.RealEvent jj.1 (ir.layoutEnv I x (ir.bindAsg a) r)
  challengeUse x a k r r' h :=
    exists_congr fun jj => challengeUseAt_realEvent_of_derivs hwf hv jj.1 (layoutEnv_eqUpTo h jj)
  sound x a r h := by
    by_cases hok : ir.stmtOk I x = true
    swap
    · exact Or.inl (Constraint.guard_of fun h' => absurd h' hok)
    rcases satAt_or_realEvent_of_derivs hv ⟨hwf, hI, hL, hv.tables, hM⟩
        (layoutEnv_sampled x _ r) h (ranges_reader hL hO _ (stmtOk_iff.1 hok).2)
        (fun _ hvl _ hk => reader_bindAsg_of_boundOk hv.bound rfl hvl hk) with
      hs | ⟨j, hj⟩
    · exact Or.inl (Constraint.guard_of fun _ => hs)
    · right
      have hs := isPhaseChal_of_realEvent_ev hv.eventsOk hj
      exact ⟨⟨(ir.challenge j).phase - 1, by have := hs.2.2; have := hs.2.1; omega⟩,
        ⟨⟨j, hs.1⟩, by have := hs.2.1; simp only; omega⟩, hj⟩

open Classical in
/-- **The error of the realization step from valid derivations**: at phase `k + 1`, the sum over
the phase's challenges of `realError`. -/
theorem eventBound_realizeLowering_of_derivs (hwf : ir.WellFormed) {orng : List (ℕ × ℕ)}
    {D : Derivations} (hv : ir.DerivationsValid primeNodes (ir.declaredRanges ++ orng) D)
    (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)
    (hO : ir.OpaqueRanges I orng) (hsel : ir.SelSound I) :
    (ir.realizeLowering_of_derivs I hwf hv hI hL hM hO).EventBound fun k =>
      ∑ jj : ir.ChalAt k, ir.realError I jj.1 := by
  intro k x a r
  change Pr[c ← (ir.layout I).Ch k :
    ∃ jj : ir.ChalAt k, ir.RealEvent jj.1 (ir.layoutEnv I x (ir.bindAsg a) (r.setChal k c))] ≤ _
  refine probUniform_exists_le_sum fun jj => ?_
  rw [← card_le_iff_probUniform_le]
  refine card_le_of_card_update_le (β := fun jj : ir.ChalAt k => ir.ChalVal I jj.1) jj
    fun f => ?_
  have hb := (card_le_iff_probUniform_le _ _ _).2
    (probUniform_realEvent_le_of_derivs hwf hv hI hsel jj.1
      (ir.layoutEnv I x (ir.bindAsg a) (r.setChal k f)))
  refine le_trans (le_of_eq ?_) hb
  congr 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, layoutEnv_setChal_update]

/-- **The realization step, from derivable realizations** (`Derivable`): the lowering of
`realizeLowering_of_derivs`, whose data (the projection `bindAsg` and the realization events) reads
no derivation; its soundness and challenge-use rule from any valid derivations. -/
def realizeLowering_of_derivable (hwf : ir.WellFormed) {orng : List (ℕ × ℕ)}
    (hv : ir.Derivable primeNodes (ir.declaredRanges ++ orng))
    (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)
    (hO : ir.OpaqueRanges I orng) :
    Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (ir.Pred I)) (ir.Realized I) where
  proj a := ir.bindAsg a
  event k x a r := ∃ jj : ir.ChalAt k, ir.RealEvent jj.1 (ir.layoutEnv I x (ir.bindAsg a) r)
  challengeUse x a k r r' h := by
    obtain ⟨D, hD⟩ := hv
    exact (ir.realizeLowering_of_derivs I hwf hD hI hL hM hO).challengeUse x a k h
  sound x a r h := by
    obtain ⟨D, hD⟩ := hv
    exact (ir.realizeLowering_of_derivs I hwf hD hI hL hM hO).sound x a r h

/-- **The error of the realization step from derivable realizations**
(`eventBound_realizeLowering_of_derivs`). -/
theorem eventBound_realizeLowering_of_derivable (hwf : ir.WellFormed) {orng : List (ℕ × ℕ)}
    (hv : ir.Derivable primeNodes (ir.declaredRanges ++ orng))
    (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir)
    (hO : ir.OpaqueRanges I orng) (hsel : ir.SelSound I) :
    (ir.realizeLowering_of_derivable I hwf hv hI hL hM hO).EventBound fun k =>
      ∑ jj : ir.ChalAt k, ir.realError I jj.1 := by
  obtain ⟨D, hD⟩ := hv
  exact eventBound_realizeLowering_of_derivs I hwf hD hI hL hM hO hsel


end

end GordieHowe.RealizedProgram
