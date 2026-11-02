-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.RevealedReprogram
public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Model.Quantum.Interactive.AbsorbTranscript
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

/-!
# Adaptive reprogramming at revealed points with a point bound per start draw

The game form `RingSignature.gameAdvantage_runLawIn_revealed_le`
(`GordieHowe/Model/RingSignature/RevealedReprogram.lean`) takes one point bound `ε` for every start
draw `k`. When the bound depends on the start draw (for signatures, on the users' keys: the point
probability of a commitment depends on the key's matrix), apply it at each `k` and average: since
the square root is concave, the average of the per-draw bounds is at most the bound at the
average point bound (Jensen).

- `QueryBoundedAdversary.transcriptLawIn_eq_map`, `runLawIn_eq_map`: against a challenger that never
  reprograms, the answered requests are the history's requests and the final oracle in force is
  the oracle: `transcriptLawIn` and `runLawIn` are `transcriptLaw` and `runLaw` mapped.
- `gameAdvantage_runLawIn_revealed_le_avg`: **the game form with a point bound `ε k` per start
  draw**, at the average `∑ k, ε k / |K|`.
-/

namespace GordieHowe.RingSignature

open Quantum
open scoped ENNReal

variable {X Y Req Resp O Y₁ Y₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ}

open Classical in
/-- **The game form with a point bound per start draw** (module docstring): for every start draw
`k` a `RevealedPair` of challengers `C₀ k` and `C₁ k` with point bound `ε k`, `Q` requests and at
most `qc` classical reads per request, and an adversary and an event reading the oracle only
through its classical part, the runs against `C₀` and against `C₁` differ by at most
`Q · (√(ε̄ W) + ε̄ W / 2)`, `W = t + qc · Q`, at the average `ε̄ = ∑ k, ε k / |K|`. -/
theorem gameAdvantage_runLawIn_revealed_le_avg {K : Type} [Fintype K] [Nonempty K] [Nonempty Req]
    [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
    {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : K → ℝ}
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', SameClassical sp B H H' → A k H = A k H')
    {C₀ C₁ : K → Challenger X Y Req Resp} (P : ∀ k, (C₀ k).RevealedPair sp B (ε k) (C₁ k))
    {Q qc : ℕ} (hQ : ∀ k, (C₀ k).Q = Q) (hq : ∀ k, (C₀ k).q ≤ qc) (hε : ∀ k, 0 ≤ ε k)
    (E : Set (K × (X → Y) × Option (O × List Req × (X → Y))))
    (hE : ∀ k H H' x, SameClassical sp B H H' → ((k, H, x) ∈ E ↔ (k, H', x) ∈ E)) :
    gameAdvantage (runLawIn A C₀) (runLawIn A C₁) E ≤
      Q * (√((∑ k, (Fintype.card K : ℝ)⁻¹ * ε k) * (t + qc * Q)) +
        (∑ k, (Fintype.card K : ℝ)⁻¹ * ε k) * (t + qc * Q) / 2) := by
  set W : ℝ := t + qc * Q with hW
  have hW0 : 0 ≤ W := by positivity
  set u : ℝ := (Fintype.card K : ℝ)⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  have hsum_u : ∑ _k : K, u = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  -- the inner probability at each start draw
  set inner : (K → Challenger X Y Req Resp) → K → ℝ≥0∞ := fun C k =>
    ∑' H, PMF.uniformOfFintype (X → Y) H *
      ((A k H).transcriptLawIn (C k) H).toOuterMeasure {o | (k, H, o) ∈ E} with hinner
  have hle : ∀ C k, inner C k ≤ 1 := fun C k =>
    PMF.tsum_mul_le_one _ fun _ => PMF.toOuterMeasure_apply_le_one _ _
  -- the bound at each start draw, from the one-draw game
  have hk : ∀ k, |(inner C₀ k).toReal - (inner C₁ k).toReal| ≤
      Q * (√(ε k * W) + ε k * W / 2) := by
    intro k
    have h := gameAdvantage_runLawIn_revealed_le (K := Unit) (fun _ H => A k H)
      (fun _ H H' h => hA k H H' h) (C₀ := fun _ => C₀ k) (C₁ := fun _ => C₁ k)
      (fun _ => P k) (fun _ => hQ k) (fun _ => hq k) {x | (k, x.2) ∈ E}
      (fun _ H H' x h => hE k H H' x h)
    rw [gameAdvantage] at h
    change |((runLawIn _ _).toOuterMeasure _).toReal - ((runLawIn _ _).toOuterMeasure _).toReal|
      ≤ _ at h
    rw [toOuterMeasure_runLawIn, toOuterMeasure_runLawIn, tsum_fintype, tsum_fintype,
      Fintype.sum_unique, Fintype.sum_unique, PMF.uniformOfFintype_apply, Fintype.card_unique,
      Nat.cast_one, inv_one, one_mul, one_mul] at h
    exact h
  rw [gameAdvantage]
  change |((runLawIn A C₀).toOuterMeasure E).toReal - ((runLawIn A C₁).toOuterMeasure E).toReal|
    ≤ _
  rw [toOuterMeasure_runLawIn, toOuterMeasure_runLawIn]
  change |(∑' k, PMF.uniformOfFintype K k * inner C₀ k).toReal -
    (∑' k, PMF.uniformOfFintype K k * inner C₁ k).toReal| ≤ _
  rw [PMF.toReal_tsum_mul_fintype _ (hle C₀), PMF.toReal_tsum_mul_fintype _ (hle C₁),
    ← Finset.sum_sub_distrib]
  have hpu : ∀ k, (PMF.uniformOfFintype K k).toReal = u := fun k => by
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [hpu, ← mul_sub]
  -- the triangle inequality, then the per-draw bounds
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k : K, |u * ((inner C₀ k).toReal - (inner C₁ k).toReal)| ≤
      Q * (u * √(ε k * W)) + Q * (u * ε k) * W / 2 := fun k => by
    rw [abs_mul, abs_of_nonneg hu0]
    calc u * |(inner C₀ k).toReal - (inner C₁ k).toReal|
        ≤ u * (Q * (√(ε k * W) + ε k * W / 2)) := mul_le_mul_of_nonneg_left (hk k) hu0
      _ = Q * (u * √(ε k * W)) + Q * (u * ε k) * W / 2 := by ring
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  have e1 : ∑ k : K, (Q * (u * √(ε k * W)) + Q * (u * ε k) * W / 2) =
      Q * (∑ k : K, u * √(ε k * W)) + Q * (∑ k : K, u * ε k) * W / 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
  rw [e1]
  -- Jensen: the square root is concave
  have hjensen : ∑ k : K, u * √(ε k * W) ≤ √((∑ k : K, u * ε k) * W) := by
    have h := (Real.strictConcaveOn_sqrt.concaveOn).le_map_sum (t := Finset.univ)
      (w := fun _ : K => u) (p := fun k => ε k * W) (fun _ _ => hu0) hsum_u
      (fun k _ => Set.mem_Ici.2 (mul_nonneg (hε k) hW0))
    simp only [smul_eq_mul] at h
    calc ∑ k : K, u * √(ε k * W) ≤ √(∑ k : K, u * (ε k * W)) := h
      _ = √((∑ k : K, u * ε k) * W) := by
        rw [Finset.sum_mul]
        simp only [mul_assoc]
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hJ := mul_le_mul_of_nonneg_left hjensen hQ0
  have e2 : (Q : ℝ) * ((∑ k : K, u * ε k) * W / 2) =
      ((Q * ∑ k : K, u * ε k) * t + (Q * ∑ k : K, u * ε k) * (qc * Q)) / 2 := by
    rw [hW]; ring
  have e3 : (Q : ℝ) * (√((∑ k : K, u * ε k) * W) + (∑ k : K, u * ε k) * W / 2) =
      Q * √((∑ k : K, u * ε k) * W) + Q * ((∑ k : K, u * ε k) * W / 2) := mul_add _ _ _
  rw [e3, e2]
  linarith

/-- **Against a challenger that never reprograms, `transcriptLawIn` is `transcriptLaw` mapped**: the
answered requests are the history's requests (`AdaptiveIAlg.map_request_history`) and the final
oracle in force is the oracle (`Challenger.NoAssign.oracle_eq`). -/
theorem _root_.GordieHowe.Quantum.QueryBoundedAdversary.transcriptLawIn_eq_map
    {C : Challenger X Y Req Resp} (hC : C.NoAssign) (A : QueryBoundedAdversary X Y Req Resp O t)
    (H : X → Y) :
    A.transcriptLawIn C H = (A.transcriptLaw C H).map
      (Option.map fun p => (p.1, p.2.map HistoryEntry.request, H)) := by
  unfold QueryBoundedAdversary.transcriptLawIn QueryBoundedAdversary.transcriptLaw
  rw [PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [Quantum.KindAlg.outLaw_composeBothOut_eq_map, Quantum.KindAlg.outLaw_composeBothOut_eq_map
    (f := fun v => ((A.alg a).output C v, (A.alg a).history C v)), PMF.map_comp,
    Option.map_comp_map]
  refine congrArg (fun g => PMF.map (Option.map g) _) (funext fun v => ?_)
  simp only [Function.comp_apply, AdaptiveIAlg.map_request_history, hC.oracle_eq]

/-- **Against challengers that never reprogram, `runLawIn` is `runLaw` mapped.** -/
theorem runLawIn_eq_map {K : Type} [Fintype K] [Nonempty K]
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    {C : K → Challenger X Y Req Resp} (hC : ∀ k, (C k).NoAssign) :
    runLawIn A C = (runLaw A C).map
      (fun x => (x.1, x.2.1, x.2.2.map fun p => (p.1, p.2.map HistoryEntry.request, x.2.1))) := by
  unfold runLawIn runLaw
  simp only [PMF.map_bind]
  refine congrArg _ (funext fun k => congrArg _ (funext fun H => ?_))
  rw [QueryBoundedAdversary.transcriptLawIn_eq_map (hC k), PMF.map_comp, PMF.map_comp]
  rfl

end GordieHowe.RingSignature
