-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.Decoder
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement

@[expose] public section

/-!
# Reed--Solomon correlated agreement on affine lines

This file is the finite, natural-number bridge from the vendored BCIKS20
unique-decoding theorem to the local `GordieHowe.RSCode` interface.  The vendored
theorem is used only with the embedding supplied by `C.D`; the radius condition
is discharged from `C.radius`.

The ArkLib source and its pinned CompPoly dependency are recorded in `Vendor/rs-provenance.json`.
-/

namespace GordieHowe.RSCode.CorrelatedLine

open Polynomial
open scoped Classical NNReal

section

variable {F : Type} [Field F] [Fintype F] {N : ℕ}

/-- Two polynomials give a common nearby affine-line pair. -/
structure JointNearby (C : GordieHowe.RSCode F N) (u v : Fin N → F) : Prop where
  witness : ∃ p q : F[X], p.natDegree < C.k ∧ q.natDegree < C.k ∧
    (Finset.univ.filter fun j =>
      u j ≠ p.eval (C.D j) ∨ v j ≠ q.eval (C.D j)).card ≤ C.e

/-- If more than `N` affine coefficients have a nearby line, the two rows have
common nearby Reed--Solomon polynomials. -/
theorem correlatedAgreement (C : GordieHowe.RSCode F N) (u v : Fin N → F)
    (hcount : N <
      (Finset.univ.filter fun z : F =>
        ∃ p : F[X],
          p.natDegree < C.k ∧
          (Finset.univ.filter fun j =>
            u j + z * v j ≠ p.eval (C.D j)).card ≤ C.e).card) :
    JointNearby C u v := by
  classical
  have hN : 0 < N := by
    have h := C.k_pos
    have hr := C.radius
    omega
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : NeZero C.k := ⟨Nat.ne_of_gt C.k_pos⟩
  let domain : Fin N ↪ F := ⟨C.D, C.D_injective⟩
  let δ : ℝ≥0 := C.e / (Fintype.card (Fin N) : ℝ≥0)
  have hδfloor : Nat.floor (δ * (Fintype.card (Fin N))) = C.e := by
    simp [δ, Fintype.card_fin]
  have hr := C.radius
  have hknNat : C.k ≤ N := by omega
  have hkn : C.k ≤ Fintype.card (Fin N) := by simpa using hknNat
  have he_udr : C.e ≤
      Code.uniqueDecodingRadius
        (C := (ReedSolomon.code domain C.k : Set (Fin N → F))) := by
    rw [ReedSolomon.uniqueDecodingRadius_RS_eq hkn]
    simp only [Fintype.card_fin]
    have hr := C.radius
    omega
  have hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (C := (ReedSolomon.code domain C.k : Set (Fin N → F))) := by
    dsimp [δ]
    exact (Code.dist_le_UDR_iff_relDist_le_relUDR
      (C := (ReedSolomon.code domain C.k : Set (Fin N → F))) C.e).mp he_udr
  let W : Code.WordStack F (Fin 2) (Fin N) := fun i => Fin.cases u (fun _ => v) i
  have hW0 : W 0 = u := by rfl
  have hW1 : W 1 = v := by rfl
  let good : Finset F := Finset.univ.filter fun z : F =>
    ∃ p : F[X], p.natDegree < C.k ∧
      (Finset.univ.filter fun j => u j + z * v j ≠ p.eval (C.D j)).card ≤ C.e
  have hgood_card : good.card > Fintype.card (Fin N) := by
    simpa [good] using hcount
  have hgood_subset : good ⊆
      ProximityGap.RS_goodCoeffs (F := F) (ι := Fin N)
        (deg := C.k) (domain := domain) W δ := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨-, ⟨p, hpdeg, hpclose⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Code.relDistFromCode_le_iff_distFromCode_le]
    rw [Code.closeToCode_iff_closeToCodeword_of_minDist]
    refine ⟨fun j => p.eval (domain j), ?_, ?_⟩
    · exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval p hpdeg
        (fun j => rfl)
    · rw [Code.hammingDist_eq_disagreementCols_card, hδfloor]
      rw [hW0, hW1]
      change (Finset.univ.filter fun j =>
        u j + z * v j ≠ p.eval (C.D j)).card ≤ C.e
      exact hpclose
  have hS : (ProximityGap.RS_goodCoeffs
      (deg := C.k) (domain := domain) W δ).card > Fintype.card (Fin N) := by
    exact lt_of_lt_of_le hgood_card (Finset.card_le_card hgood_subset)
  have hja : Code.jointAgreement
      (C := ReedSolomon.code domain C.k)
      (δ := δ) (W := W) :=
    ProximityGap.RS_jointAgreement_of_goodCoeffs_card_gt
      (deg := C.k) (domain := domain) (δ := δ) hδ W hS
  rcases hja with ⟨S, hS_card, w, hw⟩
  obtain ⟨p, hpdeg, hp_eval⟩ :=
    (ReedSolomon.mem_code_iff_eval_of_ne_zero).mp (hw 0).1
  obtain ⟨q, hqdeg, hq_eval⟩ :=
    (ReedSolomon.mem_code_iff_eval_of_ne_zero).mp (hw 1).1
  have hS_nat : N - C.e ≤ S.card := by
    have hS_card' :
        (1 - δ) * (Fintype.card (Fin N) : ℝ≥0) ≤ S.card := by
      exact hS_card
    have hfloor := (Code.relDist_floor_bound_iff_complement_bound
      (Fintype.card (Fin N)) S.card δ).mpr hS_card'
    rw [hδfloor] at hfloor
    simpa [Fintype.card_fin] using hfloor
  let E : Finset (Fin N) := Finset.univ.filter fun j =>
    u j ≠ p.eval (C.D j) ∨ v j ≠ q.eval (C.D j)
  have hEsub : E ⊆ Finset.univ \ S := by
    intro j hj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hjS
    have h0 := (hw 0).2 hjS
    have h1 := (hw 1).2 hjS
    have hu0 : w 0 j = W 0 j := by simpa using h0
    have hv1 : w 1 j = W 1 j := by simpa using h1
    have hp_eval' : p.eval (C.D j) = w 0 j := by
      simpa [domain] using hp_eval j
    have hq_eval' : q.eval (C.D j) = w 1 j := by
      simpa [domain] using hq_eval j
    have hu : p.eval (C.D j) = u j := by
      rw [hp_eval', hu0]
      exact congrFun hW0 j
    have hv : q.eval (C.D j) = v j := by
      rw [hq_eval', hv1]
      exact congrFun hW1 j
    rcases (Finset.mem_filter.mp hj).2 with h | h
    · exact h hu.symm
    · exact h hv.symm
  have hEcard : E.card ≤ C.e := by
    have hcard := Finset.card_le_card hEsub
    have hcomp : (Finset.univ \ S).card = N - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp [Fintype.card_fin]
    rw [hcomp] at hcard
    omega
  refine ⟨?_⟩
  refine ⟨p, q, ?_, ?_, ?_⟩
  · simpa using hpdeg
  · simpa using hqdeg
  · simpa [E] using hEcard

end

end GordieHowe.RSCode.CorrelatedLine
