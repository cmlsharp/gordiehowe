-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.NIZK
public import GordieHowe.SPBCS.Merkle.LeafHiding
public import GordieHowe.Foundations.ToMathlib.UniformFunction
public import GordieHowe.Foundations.Probability.Probability

@[expose] public section

/-!
# Lazy sampling in total variation

A uniform random function `F : A → B` queried adaptively: the answer to query `i` is
`F (q i ρ)`, where the query `q i ρ` depends only on the earlier answers (`q` is causal for a
well-founded order on the query indices). The answers are the unique solution `sol F` of
`ρ i = F (q i ρ)`. Lazy sampling replaces them by independent uniform answers `ρ` and the
function by `F` reprogrammed at the queries with those answers:

    tvDist (law of (F, sol F)) (law of (reprogram F [q i ρ := ρ i]ᵢ, ρ)) ≤ Pr_ρ[the queries repeat]

(`tvDist_lazy_le`). On outcomes with distinct queries the two laws agree point by point: given
`(g, a)`, both have mass `1 / |A → B|` exactly when `a i = g (q i a)` for every `i`. The
reprogrammed function is counted by `GordieHowe.QROM.card_reprogram_eq` (its values off the queries
are those of `F`, and at the queries those of the assignment list).

The zero-knowledge arguments (`GordieHowe/SPBCS/ZeroKnowledge.lean`) apply it to the challenge
streams of one proof, the `xof` answers at the keys of its rounds.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.SPBCS

open GordieHowe.QROM

variable {A B : Type*} [DecidableEq A] [Fintype A] [Fintype B] [DecidableEq B]

/-! ### The lazy-sampling bound -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty B]

open IOP

/-- **Lazy sampling in total variation.** Let `q` be causal (`q i ρ` depends only on `ρ j` for
`j < i`), `sol F` the answers of `F` (`sol F i = F (q i (sol F))`) and `L` an enumeration of the
query indices. The law of `F` with its answers and the law of `F` reprogrammed at the queries
with independent uniform answers, with those answers, are within the probability, over uniform
answers, that two queries coincide. -/
theorem tvDist_lazy_le (L : List ι) (hL : L.Nodup) (hLc : ∀ i, i ∈ L) (q : ι → (ι → B) → A)
    (hq : ∀ i ρ ρ', (∀ j, j < i → ρ j = ρ' j) → q i ρ = q i ρ')
    (sol : (A → B) → ι → B) (hsol : ∀ F i, sol F i = F (q i (sol F))) :
    (PMF.uniformOfFintype (A → B)).map (fun F => (F, sol F)) ≈[
        (Pr[ρ ← (ι → B) : ¬ Function.Injective fun i => q i ρ]).toReal]
      (PMF.uniformOfFintype ((A → B) × (ι → B))).map fun p =>
        (p.1.reprogram (L.map fun i => ⟨q i p.2, p.2 i⟩), p.2) := by
  classical
  -- a solution of the answer equations is `sol F`
  have huniq : ∀ (F : A → B) (a : ι → B), (∀ i, a i = F (q i a)) → a = sol F := by
    intro F a ha
    funext i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      rw [ha i, hsol F i, hq i a (sol F) fun j hj => ih j hj]
  set ass : (ι → B) → List (Quantum.Assignment A B) := fun a => L.map fun i => ⟨q i a, a i⟩
  set μR := (PMF.uniformOfFintype (A → B)).map fun F => (F, sol F)
  set μI := (PMF.uniformOfFintype ((A → B) × (ι → B))).map fun p => (p.1.reprogram (ass p.2), p.2)
  set Bad : Set ((A → B) × (ι → B)) := {p | ¬ Function.Injective fun i => q i p.2}
  have hlen : L.length = Fintype.card ι := by
    rw [← List.toFinset_card_of_nodup hL]
    exact congrArg Finset.card (Finset.eq_univ_iff_forall.2 fun i => List.mem_toFinset.2 (hLc i))
  -- the two laws agree off `Bad`
  have hR : ∀ g a, μR (g, a) = if a = sol g then (Fintype.card (A → B) : ENNReal)⁻¹ else 0 := by
    intro g a
    rw [PMF.map_apply, tsum_eq_single g fun F hF => by simp [Prod.ext_iff, Ne.symm hF]]
    by_cases h : a = sol g <;> simp [h, PMF.uniformOfFintype_apply, Prod.ext_iff, eq_comm]
  have hI : ∀ g a, (g, a) ∉ Bad →
      μI (g, a) = if a = sol g then (Fintype.card (A → B) : ENNReal)⁻¹ else 0 := by
    intro g a hga
    have hinj : Function.Injective fun i => q i a := by simpa [Bad] using hga
    have hnd : ((ass a).map Quantum.Assignment.input).Nodup := by
      simp only [ass, List.map_map, Function.comp_def]
      exact hL.map hinj
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    rw [Finset.sum_comm, Finset.sum_eq_single a (fun b _ hb => Finset.sum_eq_zero fun F _ => by
      simp [Prod.ext_iff, Ne.symm hb]) (by simp)]
    have hcount := card_reprogram_eq (ass a) hnd g
    have hcond : (∀ e ∈ ass a, g e.input = e.output) ↔ a = sol g := by
      constructor
      · intro h
        exact huniq g a fun i => (h ⟨q i a, a i⟩ (List.mem_map.2 ⟨i, hLc i, rfl⟩)).symm
      · rintro rfl e he
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
        exact (hsol g i).symm
    refine Eq.trans (Finset.sum_congr rfl (g := fun F : A → B =>
      (if F.reprogram (ass a) = g then 1 else 0) *
        ((Fintype.card (A → B) * Fintype.card (ι → B) : ℕ) : ENNReal)⁻¹) fun F _ => ?_) ?_
    · by_cases h : F.reprogram (ass a) = g
      · simp [h, PMF.uniformOfFintype_apply, Fintype.card_prod]
      · simp [h, Prod.ext_iff, Ne.symm h]
    rw [← Finset.sum_mul, Finset.sum_boole, hcount]
    by_cases h : a = sol g
    · rw [if_pos (hcond.2 h), if_pos h, List.length_map, hlen]
      have hc : (Fintype.card (ι → B) : ENNReal) = (Fintype.card B : ENNReal) ^ Fintype.card ι := by
        simp [Fintype.card_fun]
      push_cast
      rw [← hc, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
        mul_comm (Fintype.card (ι → B) : ENNReal), mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
    · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]
      simp
  have heq : ∀ x ∉ Bad, μR x = μI x := fun ⟨g, a⟩ h => by rw [hR, hI g a h]
  refine (PMF.tvDist_le_of_eq_of_notMem μR μI Bad heq).trans ?_
  -- the two laws give `Bad` the same mass, the probability that two queries coincide
  have hmass : (μR.toOuterMeasure Bad).toReal = (μI.toOuterMeasure Bad).toReal := by
    have h1 := PMF.sum_toReal μR
    have h2 := PMF.sum_toReal μI
    rw [PMF.toReal_toOuterMeasure_apply, PMF.toReal_toOuterMeasure_apply]
    have hsplit : ∀ μ : PMF ((A → B) × (ι → B)), ∑ x, (μ x).toReal =
        (∑ x, if x ∈ Bad then (μ x).toReal else 0) + ∑ x, if x ∈ Bad then 0 else (μ x).toReal :=
      fun μ => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
    have hoff : (∑ x, if x ∈ Bad then 0 else (μR x).toReal) =
        ∑ x, if x ∈ Bad then 0 else (μI x).toReal :=
      Finset.sum_congr rfl fun x _ => by
        by_cases hx : x ∈ Bad
        · simp [hx]
        · simp [hx, heq x hx]
    rw [hsplit μR] at h1
    rw [hsplit μI] at h2
    linarith
  have hI : (μI.toOuterMeasure Bad).toReal =
      (Pr[ρ ← (ι → B) : ¬ Function.Injective fun i => q i ρ]).toReal := by
    rw [probUniform, PMF.toOuterMeasure_map_apply, PMF.toReal_toOuterMeasure_apply,
      PMF.toReal_toOuterMeasure_apply,
      Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Set.mem_preimage, Bad, Set.mem_ofPred_eq, PMF.toReal_uniformOfFintype_apply,
      Fintype.card_prod]
    have h1 : (Fintype.card (A → B) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h2 : (Fintype.card (ι → B) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    by_cases hρ : Function.Injective fun i => q i ρ
    · simp [hρ]
    · simp only [hρ, not_false_eq_true, ite_true, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      push_cast
      field_simp
  rw [hmass, hI]
  linarith

end GordieHowe.SPBCS
