-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeStep
public import GordieHowe.Foundations.ToMathlib.PMFFiber
public import GordieHowe.Foundations.ToMathlib.PMFUniform

@[expose] public section

/-!
# Guessing a key-free signature from its public output

The key-free loop (`kfLoop`, `GordieHowe/Applications/Ring/MLDSAW1KeyFreeStep.lean`) outputs
`(w₁, σ, v)`: the published commitment, the signature and the base value of its commitment hash.
Each output is the output of one of the `k · T` attempts, whose coins are a uniform response `z`
in the mask box and a uniform base value; the signature carries `z`. So the signature is hard to
guess from the public part `(w₁, v)`: summed over the public parts, the largest probability of a
signature is at most `k · T · |BucketVec| / |MaskBox|` (the average conditional min-entropy bound
of Dodis, Ostrovsky, Reyzin, Smith, "Fuzzy Extractors", SIAM J. Comput. 38(1), 2008, Section 2.4).

- `exists_coins_of_kfLoop_eq_some`: an output's response and base value are the coins of one
  attempt.
- `prob_kfCoins_apply_eq`: one attempt's coins are uniform.
- `sum_iSup_prob_kfLoop_le`: the guessing bound.
- `cTilde_of_kfLoop_eq_some`, `chAns_symm_eq_chOf`: an output's commitment hash is that of its base
  value, which is the commitment hash of every oracle value with that base component.
-/

open Finset
open scoped ENNReal BigOperators

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section Guess

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁]
  [AddGroup Y₂] {O : W1Oracles X Y p prims Msg N reps} {sp : Y ≃+ Y₁ × Y₂} {βmin : ℚ≥0}
  {k D : ℕ} [NeZero D]

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [NeZero D] in
/-- **A key-free output's response and base value are one attempt's coins.** -/
theorem exists_coins_of_kfLoop_eq_some (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (hc : Fin R.1.length × BucketVec p → CommitHashBytes p)
    (sc : KFCoins (p := p) (T := T) k D Y₁) {s : BucketVec p × FIPSSignature p prims × Y₁}
    (hs : kfLoop prims O sp βmin pk R i hc sc = some s) :
    ∃ c t, (sc.1 c t).1.1 = s.2.1.z ∧ (sc.1 c t).2 = s.2.2 := by
  obtain ⟨c, t, hatt⟩ := exists_of_attLoop_eq_some hs
  refine ⟨c, t, ?_⟩
  unfold kfAttV keyFreeAttempt at hatt
  split_ifs at hatt
  · obtain rfl := (Option.some.inj hatt).symm
    exact ⟨rfl, rfl⟩
  · exact absurd hatt (by simp)

omit [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] in
/-- **One attempt's coins are uniform**: under uniform side coins, the coins of attempt `t` of
call `c` lie in `S` with probability `|S| / |MaskBox × Y₁|`. -/
theorem prob_kfCoins_apply_mem [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] (c : Fin k) (t : Fin T)
    (S : Set (MaskBox p × Y₁)) [DecidablePred (· ∈ S)] :
    (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)).toOuterMeasure
        {sc | sc.1 c t ∈ S} =
      (PMF.uniformOfFintype (MaskBox p × Y₁)).toOuterMeasure S := by
  have h : (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)).map (fun sc => sc.1 c t) =
      PMF.uniformOfFintype (MaskBox p × Y₁) := by
    rw [show (fun sc : KFCoins (p := p) (T := T) k D Y₁ => sc.1 c t) =
        (fun f : Fin T → MaskBox p × Y₁ => f t) ∘ (fun g : Fin k → Fin T → MaskBox p × Y₁ => g c) ∘
          Prod.fst from rfl, ← PMF.map_comp, ← PMF.map_comp, PMF.map_fst_uniformOfFintype,
      PMF.uniformOfFintype_map_eval, PMF.uniformOfFintype_map_eval]
  rw [← h, PMF.toOuterMeasure_map_apply]
  rfl

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] in
/-- **The key-free signature is hard to guess from its public part**: summed over the published
commitment and base value `(w₁, v)`, the largest probability of a signature `σ` with output
`(w₁, σ, v)` is at most `k · T · |BucketVec| / |MaskBox|`. -/
theorem sum_iSup_prob_kfLoop_le [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
    (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) :
    ∑ y : BucketVec p × Y₁, ⨆ σ : FIPSSignature p prims,
        (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)).toOuterMeasure
          {sc | kfLoop prims O sp βmin pk R i hc sc = some (y.1, σ, y.2)} ≤
      k * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p) := by
  classical
  set μ := PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)
  have hone : ∀ (z : RqVec p.l) (v : Y₁),
      (PMF.uniformOfFintype (MaskBox p × Y₁)).toOuterMeasure {x | x.1.1 = z ∧ x.2 = v} ≤
        ((Fintype.card (MaskBox p) : ℝ≥0∞) * Fintype.card Y₁)⁻¹ := by
    intro z v
    by_cases h : ∃ x : MaskBox p × Y₁, x.1.1 = z ∧ x.2 = v
    · obtain ⟨x, hx1, hx2⟩ := h
      have hsub : {x' : MaskBox p × Y₁ | x'.1.1 = z ∧ x'.2 = v} ⊆ {x} := fun x' hx' =>
        Prod.ext (Subtype.ext (hx'.1.trans hx1.symm)) (hx'.2.trans hx2.symm)
      refine (MeasureTheory.measure_mono hsub).trans_eq ?_
      rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_prod,
        Nat.cast_mul]
    · have hemp : {x' : MaskBox p × Y₁ | x'.1.1 = z ∧ x'.2 = v} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun x' hx' => h ⟨x', hx'⟩
      rw [hemp, MeasureTheory.measure_empty]
      exact zero_le
  have hpt : ∀ y : BucketVec p × Y₁, ∀ σ : FIPSSignature p prims,
      μ.toOuterMeasure {sc | kfLoop prims O sp βmin pk R i hc sc = some (y.1, σ, y.2)} ≤
        k * T * ((Fintype.card (MaskBox p) : ℝ≥0∞) * Fintype.card Y₁)⁻¹ := by
    intro y σ
    calc μ.toOuterMeasure {sc | kfLoop prims O sp βmin pk R i hc sc = some (y.1, σ, y.2)}
        ≤ μ.toOuterMeasure (⋃ ct ∈ (Finset.univ : Finset (Fin k × Fin T)),
            {sc | sc.1 ct.1 ct.2 ∈ {x : MaskBox p × Y₁ | x.1.1 = σ.z ∧ x.2 = y.2}}) := by
          refine MeasureTheory.measure_mono fun sc hsc => ?_
          obtain ⟨c, t, h1, h2⟩ := exists_coins_of_kfLoop_eq_some pk R i hc sc hsc
          exact Set.mem_biUnion (Finset.mem_univ (c, t)) ⟨h1, h2⟩
      _ ≤ ∑ ct ∈ (Finset.univ : Finset (Fin k × Fin T)),
            μ.toOuterMeasure {sc | sc.1 ct.1 ct.2 ∈ {x : MaskBox p × Y₁ | x.1.1 = σ.z ∧ x.2 = y.2}} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ _ct ∈ (Finset.univ : Finset (Fin k × Fin T)),
            ((Fintype.card (MaskBox p) : ℝ≥0∞) * Fintype.card Y₁)⁻¹ := by
          refine Finset.sum_le_sum fun ct _ => ?_
          rw [prob_kfCoins_apply_mem]
          exact hone _ _
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  calc ∑ y : BucketVec p × Y₁, ⨆ σ : FIPSSignature p prims,
        μ.toOuterMeasure {sc | kfLoop prims O sp βmin pk R i hc sc = some (y.1, σ, y.2)}
      ≤ ∑ _y : BucketVec p × Y₁,
          k * T * ((Fintype.card (MaskBox p) : ℝ≥0∞) * Fintype.card Y₁)⁻¹ :=
        Finset.sum_le_sum fun y _ => iSup_le fun σ => hpt y σ
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        have hY : (Fintype.card Y₁ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
        have hY' : (Fintype.card Y₁ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        rw [ENNReal.mul_inv (Or.inr hY') (Or.inr hY), div_eq_mul_inv]
        push_cast
        calc (Fintype.card (BucketVec p) : ℝ≥0∞) * Fintype.card Y₁ *
              (k * T * ((Fintype.card (MaskBox p) : ℝ≥0∞)⁻¹ * (Fintype.card Y₁ : ℝ≥0∞)⁻¹))
            = k * T * Fintype.card (BucketVec p) * (Fintype.card (MaskBox p) : ℝ≥0∞)⁻¹ *
                ((Fintype.card Y₁ : ℝ≥0∞) * (Fintype.card Y₁ : ℝ≥0∞)⁻¹) := by ring
          _ = _ := by rw [ENNReal.mul_inv_cancel hY hY', mul_one]

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [NeZero D] in
/-- **A key-free output's commitment hash is the commitment hash of its base value**: an output
`(w₁, σ, v)` of `kfLoop` has `σ.c̃ = chOf v`. -/
theorem cTilde_of_kfLoop_eq_some (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (hc : Fin R.1.length × BucketVec p → CommitHashBytes p)
    (sc : KFCoins (p := p) (T := T) k D Y₁) {s : BucketVec p × FIPSSignature p prims × Y₁}
    (hs : kfLoop prims O sp βmin pk R i hc sc = some s) :
    s.2.1.cTilde = chOf O sp s.2.2 := by
  obtain ⟨c, t, hatt⟩ := exists_of_attLoop_eq_some hs
  unfold kfAttV keyFreeAttempt at hatt
  split_ifs at hatt
  · obtain rfl := (Option.some.inj hatt).symm
    rfl
  · exact absurd hatt (by simp)

omit [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [NeZero D] in
/-- **The commitment hash of a value is that of its base component**: for decodings reading only
the base component, `chAns (sp.symm (v, h)) = chOf v`. -/
theorem chAns_symm_eq_chOf (hO : O.ReadsFst sp) (v : Y₁) (h : Y₂) :
    O.chAns (sp.symm (v, h)) = chOf O sp v :=
  hO.chAns_eq _ _ (by simp)

end Guess

end GordieHowe.Ring.MLDSAW1
