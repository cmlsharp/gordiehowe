-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Anonymity
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Concentration

@[expose] public section

/-!
# The coupling error of the fresh-mask w₁ signer

`w1Concrete.anonAdvantage_le` (`MLDSAW1Anonymity.lean`) bounds anonymity of the ML-DSA ring
publishing `w₁` by the average of `idealDist`, the largest distance over the valid challenges
between the two users' refusal-or-public-value laws of the fresh-mask base signer. This file bounds
that average, for a scheme whose supported rings all have defect at most `s`, by the analysis of
`GordieHowe/Applications/Ring/PublicW1/`. The anonymity headlines that use it are in
`MLDSAW1AnonQuery.lean`.

Bounded loops with a finite keep coin (about Mathlib objects):

- `PMF.tvDist_firstSome_le`, `PMF.tvDist_firstSome_untilSome_le`: two bounded loops are within `n`
  times the distance of their attempts; a bounded loop of `n` attempts is within `r^n` of the
  unbounded loop, `r` the rejection probability.
- `PMF.card_filter_lt_mem_Icc`, `PMF.tvDist_finCoin_le`: keeping when `u < D · w` for a uniform
  `u ∈ Fin D` is within `1 / D` of keeping with probability `w`, for `w ≤ 1`.
- `PMF.weightedAttemptMasksFin`, `PMF.firstOf_pure`, `PMF.firstOf_acceptAt`,
  `PMF.tvDist_weightedAttemptMasksFin_le`, `PMF.tvDist_finCall_le`,
  `PMF.map_uniform_findSome?_eq_firstSome`, `PMF.tvDist_firstSome_finCall_le`: **one call with
  `T` masks and a keep coin on `Fin D` is within `1 / D` of the call with the real coin, and the
  bounded loop of `k` such calls is within `k / D + r^k` of the unbounded loop of one attempt with
  one uniform mask**, `r` the rejection probability of that attempt, for `T ≥ 1`.
- `PMF.map_uniformOfFintype_comp_embedding`, `PMF.map_uniformOfFintype_comp_left`,
  `PMF.map_uniformOfFintype_prodMap`, `PMF.expect_eq_sum_uniformOfFintype`,
  `PMF.expect_comp_of_map_eq`, `PMF.map_uniformOfFintype_callCoins`: uniform laws under
  restriction along an embedding, decoding, products and the per-call coins.
- `List.findSome?_ite_eq_map_find?`, `List.option_map_findSome?`.

The w₁ ring:

- `W1Oracles.UniformSplit`, `W1Oracles.ptEmb`, `W1Oracles.decodePts`,
  `W1Oracles.split_symm_apply_of_isPt`, `W1Oracles.gameOrc_split_symm`,
  `W1Oracles.gameOrc_eq_of_split`, `W1Oracles.map_decodePts`, `W1Oracles.expect_gameOrc_split`:
  **a domain separation of the base signer's oracles with uniform decodings**; the game's oracles
  `((H_µ, H), G)` read off a uniform first part of the split are uniform.
  `W1Oracles.expect_gameOrc`, `W1Oracles.expect_ringCheck_gOrc_le`: the game's oracles read off
  a uniform oracle are uniform, and a ring of defect at least `s` passes the check of a uniform
  oracle with probability at most `checkError`.
- `w1Of_attemptOutput`, `callOut_map_w1Of`, `refusalPubLaw_freshBase_of_not`,
  `refusalPubLaw_freshBase_eq`, `tvDist_refusalPubLaw_freshBase_le`: **the refusal-or-public-value
  law of the fresh-mask base signer** is the refusal on a ring it refuses, and otherwise, for an
  honest key and a uniform mask decoding, the commitment law of the bounded finite-coin loop,
  within `k / D + r^k` of the unbounded loop of one ideal attempt for `T ≥ 1`.
- `reqPair`, `reqPair_attempt`, `idxOf_lt_of_valid`, `chalPair`, `tvDist_refusalPubLaw_le_chalPair`:
  the two users' signers of a valid admitted challenge as a `PMF.RingPair`; their laws are within
  the distance of the two ideal loops plus `k / D + r_b^k` per user.
- `LowChal`, `lowFamily`, `lowError`, `lowFamily_mass_pos`, `lowError_nonneg`,
  `lowFamily_error_le`, `lowFamily_countVar_le`, `lowFamily_devVar_le`, `expect_lowError_le`: the
  family of **all** valid challenges of ring defect at most `s` with distinct message
  representatives, its family bound (the counterpart of `oracleError` for all valid challenges),
  and its average over the commitment-hash oracle: `2 / ((1 - s) θ)` times the users' regularity
  gaps plus the McDiarmid terms, with `C` a bound on the number of valid challenges in the
  logarithms.
- `couplingBound`, `couplingBound_nonneg`, `tvDist_refusalPubLaw_le_couplingBound`,
  `idealDist_le_couplingBound`: at fixed oracles, when every supported ring has defect at most `s`,
  `idealDist` is at most twice the family bound, twice `k / D` and twice `(1 - Lk)^k` (each ideal
  attempt keeps with probability at least the keep level when the family bound is below `1/2`,
  `keep_ge_of_familyBound_lt`).
- `regGapAt`, `collAt`, `w1CouplingError`, `expect_idealDist_le`: **the averaged coupling error**:
  `𝔼_{keys, ω₂} idealDist ≤ w1CouplingError` when every supported ring has defect at most `s`, an
  explicit expression in the average regularity gap `regGapAt` and commitment collision
  probability `collAt` of one honest key, `N`, `n`, `C`, `k`, `D` and the keep level `Lk`.
- `uniformSplit_sumOracles`, `SatY`, `satMu`, `satCh`, `satMask`, `map_uniformOfFintype_triple`,
  `map_satMu`, `map_satCh`, `map_satMask`, `uniformSplit_sumOracles_satY`, `keepLevel_div_le_one`,
  `div_le_keepLevel_mldsa44`, `div_le_keepLevel_mldsa65`, `div_le_keepLevel_mldsa87`:
  satisfiability of the hypotheses of the headlines: `sumOracles` and `sumMask` over the additive
  group `SatY` with uniform decodings satisfy `hO` and `hMask`, and `Lk = β_min θ / 64` satisfies
  `hLk` at `s = 1/2` for `θ ≥ 0`, and `hLk1` for `β_min ≤ 1` and `θ ∈ [0, 1]`.

## What the bound leaves open

- **The regularity and collision terms are the defined averages `regGapAt` and `collAt` at the
  concrete primitives.** The numeric bounds of `MLDSAPublicW1Regularity.lean` and
  `MLDSAPublicW1Concentration.lean` are for the game with `ExpandA`, `ExpandS` and `SampleInBall`
  random oracles and are not applied here: the scheme constants use the FIPS 204 functions, and
  their key generation reads no oracle.
-/

open Finset
open scoped ENNReal BigOperators

namespace PMF

/-! ### Bounded loops -/

section Loops

variable {α : Type*} [Fintype α]

/-- **Two bounded loops are within `n` times the distance of their attempts** (`firstOf_const`,
`tvDist_pi_le`). -/
theorem tvDist_firstSome_le (A B : PMF (Option α)) (n : ℕ) :
    tvDist (firstSome A n) (firstSome B n) ≤ n * tvDist A B := by
  rw [← firstOf_const, ← firstOf_const]
  unfold firstOf
  refine (tvDist_map_le _ _ _).trans ((tvDist_pi_le _ _).trans_eq ?_)
  simp

/-- **A bounded loop is within the rejection of all its attempts of the unbounded loop**
(`tvDist_firstSome_map_condSome`; both loops reject surely when one attempt does). -/
theorem tvDist_firstSome_untilSome_le (A : PMF (Option α)) (n : ℕ) :
    tvDist (firstSome A n) (untilSome A) ≤ (A none ^ n).toReal := by
  by_cases h : A none = 1
  · have h1 : firstSome A n = PMF.pure none := by
      ext o
      cases o with
      | none => rw [firstSome_apply_none, h, one_pow, pure_apply_self]
      | some a =>
        rw [firstSome_apply_some, apply_some_eq_zero_of_apply_none_eq_one h a, zero_mul]
        simp
    rw [h1, untilSome_of_apply_none_eq_one h, tvDist_self]
    exact ENNReal.toReal_nonneg
  · unfold untilSome
    simp only [h, ↓reduceDIte]
    exact (tvDist_firstSome_map_condSome A h n).le

end Loops

/-! ### The keep coin on `Fin D` -/

section Coin

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of `u < D` below a real `x ∈ [0, D]` is within one above `x`. -/
theorem card_filter_lt_mem_Icc {D : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hxD : x ≤ D) :
    x ≤ ((univ.filter fun u : Fin D => ((u : ℕ) : ℝ) < x).card : ℝ) ∧
      ((univ.filter fun u : Fin D => ((u : ℕ) : ℝ) < x).card : ℝ) ≤ x + 1 := by
  set m := ⌈x⌉₊
  have hmD : m ≤ D := Nat.ceil_le.2 hxD
  have hmem : ∀ u : Fin D, ((u : ℕ) : ℝ) < x ↔ (u : ℕ) < m := fun u => (Nat.lt_ceil).symm
  have hcard : (univ.filter fun u : Fin D => ((u : ℕ) : ℝ) < x).card = m := by
    rw [Finset.filter_congr fun u _ => hmem u]
    have : (univ.filter fun u : Fin D => (u : ℕ) < m).map Fin.valEmbedding = range m := by
      ext j
      simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
      exact ⟨fun ⟨u, hu, he⟩ => he ▸ hu, fun hj => ⟨⟨j, hj.trans_le hmD⟩, hj, rfl⟩⟩
    rw [← card_map, this, card_range]
  rw [hcard]
  exact ⟨Nat.le_ceil x, (Nat.ceil_lt_add_one hx0).le⟩

/-- **The keep coin on `Fin D` against the real coin**: keeping `a` when the uniform `u ∈ Fin D`
is below `D · w` is within `1 / D` of keeping it with probability `w` (`keepOrReject`). -/
theorem tvDist_finCoin_le (a : α) {w : ℝ≥0∞} (hw : w ≤ 1) {D : ℕ} [NeZero D] :
    tvDist ((uniformOfFintype (Fin D)).map fun u : Fin D =>
        if ((u : ℕ) : ℝ≥0∞) < D * w then some a else none) (keepOrReject a w hw) ≤
      (D : ℝ)⁻¹ := by
  classical
  have hD : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  set x : ℝ := D * w.toReal
  have hx0 : 0 ≤ x := by positivity
  have hxD : x ≤ D := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hw
    rw [ENNReal.toReal_one] at this
    nlinarith
  have hlt : ∀ u : Fin D, ((u : ℕ) : ℝ≥0∞) < D * w ↔ ((u : ℕ) : ℝ) < x := fun u => by
    rw [← ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwt), ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  set F := univ.filter fun u : Fin D => ((u : ℕ) : ℝ) < x
  obtain ⟨hF0, hF1⟩ := card_filter_lt_mem_Icc (D := D) hx0 hxD
  set f : Fin D → Option α := fun u => if ((u : ℕ) : ℝ≥0∞) < D * w then some a else none
  have hP : ∀ o, (((uniformOfFintype (Fin D)).map f) o).toReal =
      ∑ u, (D : ℝ)⁻¹ * if f u = o then 1 else 0 := fun o => by
    rw [toReal_map_apply]
    refine sum_congr rfl fun u _ => ?_
    rw [toReal_uniformOfFintype_apply, Fintype.card_fin]
    split_ifs <;> simp
  have hPs : (((uniformOfFintype (Fin D)).map f) (some a)).toReal = F.card / D := by
    rw [hP, ← mul_sum, sum_boole, div_eq_inv_mul]
    congr 2
    refine congrArg _ (Finset.filter_congr fun u _ => ?_)
    simp only [f]
    split_ifs with h
    · exact iff_of_true rfl ((hlt u).1 h)
    · exact iff_of_false (by simp) fun h' => h ((hlt u).2 h')
  have hPn : (((uniformOfFintype (Fin D)).map f) none).toReal = 1 - F.card / D := by
    have hsum := sum_toReal ((uniformOfFintype (Fin D)).map f)
    rw [Fintype.sum_option] at hsum
    have h0 : ∀ b, b ≠ a → (((uniformOfFintype (Fin D)).map f) (some b)).toReal = 0 := fun b hb => by
      rw [hP]
      refine sum_eq_zero fun u _ => ?_
      simp only [f]
      split_ifs <;> simp_all
    rw [← sum_erase_add _ _ (mem_univ a), sum_eq_zero fun b hb => h0 b (ne_of_mem_erase hb),
      zero_add, hPs] at hsum
    linarith
  have hQs : (keepOrReject a w hw (some a)).toReal = w.toReal := by
    simp [keepOrReject]
  have hQn : (keepOrReject a w hw none).toReal = 1 - w.toReal := by
    simp [keepOrReject, ENNReal.toReal_sub_of_le hw ENNReal.one_ne_top]
  rw [tvDist_eq_sum, Fintype.sum_option, ← sum_erase_add _ _ (mem_univ a),
    sum_eq_zero fun b hb => ?_, zero_add, hPn, hQn, hPs, hQs]
  · have e1 : |1 - F.card / (D : ℝ) - (1 - w.toReal)| = |F.card / (D : ℝ) - w.toReal| := by
      rw [← abs_neg]; ring_nf
    rw [e1, ← two_mul, mul_div_cancel_left₀ _ two_ne_zero, abs_le]
    have hx : w.toReal = x / D := by rw [mul_div_cancel_left₀ _ hD.ne']
    rw [hx, div_sub_div_same, le_div_iff₀ hD, div_le_iff₀ hD]
    have hDD : (D : ℝ)⁻¹ * D = 1 := inv_mul_cancel₀ hD.ne'
    constructor <;> linarith
  · have hb : b ≠ a := ne_of_mem_erase hb
    have h1 : ((uniformOfFintype (Fin D)).map f (some b)).toReal = 0 := by
      rw [hP]
      refine sum_eq_zero fun u _ => ?_
      simp only [f]
      split_ifs <;> simp_all
    have h2 : (keepOrReject a w hw (some b)).toReal = 0 := by
      simp [keepOrReject, hb]
    rw [h1, h2, sub_zero, abs_zero]

end Coin

/-! ### One call with a keep coin on `Fin D` -/

section FinCall

/-- **A first acceptance read off a list** is the first element passing the test. -/
theorem _root_.List.findSome?_ite_eq_map_find? {β γ : Type*} (p : β → Bool) (f : β → γ)
    (l : List β) : (l.findSome? fun t => if p t then some (f t) else none) = (l.find? p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.find?_cons]
    cases p a <;> simp [ih]

variable {α : Type*} [Fintype α]

/-- **The first acceptance among sure attempts** is sure. -/
theorem firstOf_pure {k : ℕ} (o : Fin k → Option α) :
    firstOf (fun t => PMF.pure (o t)) = PMF.pure ((List.finRange k).findSome? o) := by
  classical
  have hpi : pi (fun t => PMF.pure (o t)) = PMF.pure o := by
    ext f
    rw [pi_apply, pure_apply]
    simp only [pure_apply]
    by_cases hfo : f = o
    · subst hfo
      simp
    · obtain ⟨t, ht⟩ := Function.ne_iff.1 hfo
      simp only [hfo, ↓reduceIte]
      exact Finset.prod_eq_zero (mem_univ t) (by simp [ht])
  rw [firstOf, hpi, pure_map]

variable {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype C]
  [DecidableEq C] (s : RingWeights N V C) (i : N) {Y : Type*} [Fintype Y] (w1 : Y → V)
  (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1) {S : Type*} [Fintype S]
  [DecidableEq S] (out : Y → C → S) (H : N × V → C)

open Classical in
/-- **One call with `T` given masks and a keep coin `u ∈ Fin D`**: the first mask `y` whose
attempt passes the checks, kept when `u < D · w` for its keep weight
`w = κ (w₁ y, H (i, w₁ y)) · otherWeight` and output with its commitment; `none` when no mask
passes or the coin rejects. The finite-coin form of `weightedAttemptMasks`. -/
noncomputable def weightedAttemptMasksFin {T : ℕ} (D : ℕ) (ys : Fin T → Y) (u : Fin D) :
    Option (V × S) :=
  match (List.finRange T).find? (fun t => acc (ys t) (H (i, w1 (ys t)))) with
  | none => none
  | some t =>
    if ((u : ℕ) : ℝ≥0∞) < D * (κ (w1 (ys t), H (i, w1 (ys t))) *
        s.otherWeight i H (w1 (ys t))) then
      some (w1 (ys t), out (ys t) (H (i, w1 (ys t))))
    else none

omit [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
/-- The acceptance tests of `T` given masks: the first accepted mask, surely. -/
theorem firstOf_acceptAt {T : ℕ} (ys : Fin T → Y) :
    firstOf (fun t => acceptAt i w1 acc H (ys t)) =
      PMF.pure (((List.finRange T).find? fun t => acc (ys t) (H (i, w1 (ys t)))).map ys) := by
  have h : ∀ t, acceptAt i w1 acc H (ys t) =
      PMF.pure (if acc (ys t) (H (i, w1 (ys t))) then some (ys t) else none) := fun t => by
    unfold acceptAt
    split_ifs <;> rfl
  simp only [h]
  rw [firstOf_pure, List.findSome?_ite_eq_map_find?]

omit [Fintype S] [DecidableEq S] in
/-- **At given masks, the finite keep coin is within `1 / D` of the real one**
(`tvDist_finCoin_le`). -/
theorem tvDist_weightedAttemptMasksFin_le {T : ℕ} (D : ℕ) [NeZero D] (ys : Fin T → Y) :
    tvDist ((uniformOfFintype (Fin D)).map (weightedAttemptMasksFin s i w1 acc κ out H D ys))
      (weightedAttemptMasks s i w1 acc κ hκ out H ys) ≤ (D : ℝ)⁻¹ := by
  classical
  unfold weightedAttemptMasks
  rw [firstOf_acceptAt, pure_bind]
  rcases ht : (List.finRange T).find? (fun t => acc (ys t) (H (i, w1 (ys t)))) with _ | t
  · have h0 : weightedAttemptMasksFin s i w1 acc κ out H D ys = fun _ => none := by
      funext u
      simp only [weightedAttemptMasksFin, ht]
    rw [h0, show (fun _ : Fin D => (none : Option (V × S))) = Function.const _ none from rfl,
      map_const]
    simp only [Option.map_none, Option.elim, tvDist_self]
    positivity
  · set y := ys t
    have h1 : weightedAttemptMasksFin s i w1 acc κ out H D ys =
        Option.map (fun v => (v, out y (H (i, w1 y)))) ∘ fun u : Fin D =>
          if ((u : ℕ) : ℝ≥0∞) < D * (κ (w1 y, H (i, w1 y)) * s.otherWeight i H (w1 y)) then
            some (w1 y) else none := by
      funext u
      simp only [weightedAttemptMasksFin, ht, Function.comp_apply, y]
      split_ifs <;> rfl
    rw [h1, ← map_comp]
    simp only [Option.map_some, Option.elim]
    unfold keepAt
    exact (tvDist_map_le _ _ _).trans (tvDist_finCoin_le _ _)

omit [Fintype S] [DecidableEq S] in
/-- **One call with the finite keep coin is within `1 / D` of the call with the real coin**, at
uniform masks (`tvDist_weightedAttemptMasksFin_le`, averaged by `tvDist_bind_left_le`). -/
theorem tvDist_finCall_le [Nonempty Y] {T : ℕ} (D : ℕ) [NeZero D] :
    tvDist ((uniformOfFintype ((Fin T → Y) × Fin D)).map fun z =>
        weightedAttemptMasksFin s i w1 acc κ out H D z.1 z.2)
      ((uniformOfFintype (Fin T → Y)).bind (weightedAttemptMasks s i w1 acc κ hκ out H)) ≤
      (D : ℝ)⁻¹ := by
  classical
  rw [uniformOfFintype_prod_eq_bind, map_bind]
  simp only [map_comp]
  refine (tvDist_bind_left_le _ _ _).trans ?_
  calc ∑ ys, ((uniformOfFintype (Fin T → Y)) ys).toReal * tvDist _ _
      ≤ ∑ ys, ((uniformOfFintype (Fin T → Y)) ys).toReal * (D : ℝ)⁻¹ :=
        sum_le_sum fun ys _ => mul_le_mul_of_nonneg_left
          (tvDist_weightedAttemptMasksFin_le s i w1 acc κ hκ out H D ys) ENNReal.toReal_nonneg
    _ = (D : ℝ)⁻¹ := by rw [← sum_mul, sum_toReal, one_mul]

/-- **`k` independent calls stopping at the first acceptance** are the bounded loop of one
call (`firstOf_const`, `pi_map`). -/
theorem map_uniform_findSome?_eq_firstSome {β : Type*} [Fintype β] [Nonempty β] (k : ℕ)
    (f : β → Option α) :
    (uniformOfFintype (Fin k → β)).map (fun z => (List.finRange k).findSome? fun c => f (z c)) =
      firstSome ((uniformOfFintype β).map f) k := by
  rw [← firstOf_const]
  unfold firstOf
  rw [← pi_map, map_comp, pi_uniformOfFintype]
  rfl

/-- **The bounded loop of `k` calls with the finite keep coin against the unbounded loop of one
ideal attempt**: its commitment law is within `k / D` (the coin, `tvDist_finCall_le` and
`tvDist_firstSome_le`) plus the probability `r^k` that `k` ideal attempts all reject (the bound
on the loop, `tvDist_firstSome_untilSome_le`, with a call rejecting at most as often as one
attempt, `uniform_bind_weightedAttemptMasks_none_le`) of the unbounded loop of one attempt with
one uniform mask (`untilSome_uniform_bind_weightedAttemptMasks`), for `T ≥ 1` masks per call. -/
theorem tvDist_firstSome_finCall_le [Nonempty Y] [DecidableEq Y] {T : ℕ} (hT : 0 < T) (D : ℕ)
    [NeZero D] (k : ℕ) :
    tvDist ((firstSome ((uniformOfFintype ((Fin T → Y) × Fin D)).map fun z =>
        weightedAttemptMasksFin s i w1 acc κ out H D z.1 z.2) k).map (Option.map Prod.fst))
      (untilSome (weightedAttempt s i (uniformOfFintype Y) w1 acc κ hκ H)) ≤
      k * (D : ℝ)⁻¹ + ((weightedAttempt s i (uniformOfFintype Y) w1 acc κ hκ H none) ^ k).toReal := by
  set F := (uniformOfFintype ((Fin T → Y) × Fin D)).map fun z =>
    weightedAttemptMasksFin s i w1 acc κ out H D z.1 z.2
  set R := (uniformOfFintype (Fin T → Y)).bind (weightedAttemptMasks s i w1 acc κ hκ out H)
  set W := weightedAttemptWith s i (uniformOfFintype Y) w1 acc κ hκ out H
  have hU : untilSome (weightedAttempt s i (uniformOfFintype Y) w1 acc κ hκ H) =
      (untilSome W).map (Option.map Prod.fst) := by
    rw [untilSome_map_optionMap, map_weightedAttemptWith]
  have hRW : untilSome R = untilSome W :=
    untilSome_uniform_bind_weightedAttemptMasks s i w1 acc κ hκ out H hT
  have hnone : W none = weightedAttempt s i (uniformOfFintype Y) w1 acc κ hκ H none := by
    rw [← map_weightedAttemptWith s i (uniformOfFintype Y) w1 acc κ hκ out H, map_apply,
      tsum_eq_single none fun o ho => by cases o <;> simp_all]
    simp [W]
  have hR : R none ≤ W none := uniform_bind_weightedAttemptMasks_none_le s i w1 acc κ hκ out H hT
  rw [hU]
  refine (tvDist_map_le _ _ _).trans ?_
  calc tvDist (firstSome F k) (untilSome W)
      ≤ tvDist (firstSome F k) (firstSome R k) + tvDist (firstSome R k) (untilSome R) := by
        rw [hRW]
        exact tvDist_triangle _ _ _
    _ ≤ k * (D : ℝ)⁻¹ + (R none ^ k).toReal :=
        add_le_add ((tvDist_firstSome_le F R k).trans (mul_le_mul_of_nonneg_left
          (tvDist_finCall_le s i w1 acc κ hκ out H D) (Nat.cast_nonneg _)))
          (tvDist_firstSome_untilSome_le R k)
    _ ≤ _ := add_le_add le_rfl (ENNReal.toReal_mono (ENNReal.pow_ne_top (apply_ne_top _ _))
        (pow_le_pow_left₀ bot_le (hR.trans_eq hnone) k))

end FinCall

/-! ### Uniform laws under restriction, decoding and products -/

section Uniform

variable {A A' Y Z : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype Y]
  [Nonempty Y] [Fintype Z] [Nonempty Z]

/-- **The pullback of a uniform function along an embedding is uniform** (`splitAlong`). -/
theorem map_uniformOfFintype_comp_embedding (e : A' ↪ A) :
    (uniformOfFintype (A → Y)).map (fun g a => g (e a)) = uniformOfFintype (A' → Y) := by
  rw [← map_uniformOfFintype_equiv (GordieHowe.splitAlong (Y' := Y) e).symm, map_comp]
  have h : ((fun g a => g (e a)) ∘ (GordieHowe.splitAlong (Y' := Y) e).symm) = Prod.snd := by
    funext q a
    exact GordieHowe.splitAlong_symm_apply_embed e q.1 q.2 a
  rw [h, map_snd_uniformOfFintype]

/-- **Decoding the values of a uniform function** by a map pushing the uniform law to the uniform
law gives a uniform function (`pi_map`). -/
theorem map_uniformOfFintype_comp_left {φ : Y → Z}
    (hφ : (uniformOfFintype Y).map φ = uniformOfFintype Z) :
    (uniformOfFintype (A → Y)).map (fun g a => φ (g a)) = uniformOfFintype (A → Z) := by
  classical
  rw [← pi_uniformOfFintype, ← pi_uniformOfFintype, pi_map]
  simp only [hφ]

omit [DecidableEq A] [DecidableEq A'] in
/-- **Two maps pushing uniform laws to uniform laws** push the uniform law on the product to the
uniform law (`uniformOfFintype_prod_eq_bind`). -/
theorem map_uniformOfFintype_prodMap {φ : Y → Z} {ψ : A → A'} [Nonempty A] [Nonempty A']
    (hφ : (uniformOfFintype Y).map φ = uniformOfFintype Z)
    (hψ : (uniformOfFintype A).map ψ = uniformOfFintype A') :
    (uniformOfFintype (Y × A)).map (Prod.map φ ψ) = uniformOfFintype (Z × A') := by
  rw [uniformOfFintype_prod_eq_bind, uniformOfFintype_prod_eq_bind, map_bind, ← hφ, bind_map]
  refine congrArg _ (funext fun y => ?_)
  rw [← hψ]
  change _ = map (Prod.mk (φ y)) (map ψ _)
  simp only [PMF.map_comp]
  rfl

omit [Nonempty Y] in
/-- An average is the sum against the uniform law. -/
theorem expect_eq_sum_uniformOfFintype [Nonempty Y] (F : Y → ℝ) :
    𝔼 x, F x = ∑ x, ((uniformOfFintype Y) x).toReal * F x := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [toReal_uniformOfFintype_apply, Finset.card_univ, div_eq_inv_mul]

/-- **A change of variables pushing the uniform law to the uniform law preserves averages.** -/
theorem expect_comp_of_map_eq {φ : Y → Z} (hφ : (uniformOfFintype Y).map φ = uniformOfFintype Z)
    (G : Z → ℝ) : 𝔼 y, G (φ y) = 𝔼 z, G z := by
  rw [expect_eq_sum_uniformOfFintype, expect_eq_sum_uniformOfFintype, ← hφ, sum_toReal_map_mul]

/-- **Per-call coins as mask vectors**: `k` uniform functions on `A`, read at the points `e a'`
and decoded by `φ`, together with `k` uniform coins on `B`, are `k` uniform pairs of a function
on `A'` and a coin. -/
theorem map_uniformOfFintype_callCoins (k : ℕ) (e : A' ↪ A) {φ : Y → Z}
    (hφ : (uniformOfFintype Y).map φ = uniformOfFintype Z) {B : Type*} [Fintype B] [Nonempty B] :
    (uniformOfFintype ((Fin k → A → Y) × (Fin k → B))).map
        (fun c j => ((fun a' => φ (c.1 j (e a'))), c.2 j)) =
      uniformOfFintype (Fin k → (A' → Z) × B) := by
  classical
  have h1 : (uniformOfFintype (A → Y)).map (fun g a' => φ (g (e a'))) =
      uniformOfFintype (A' → Z) := by
    have h : (fun (g : A → Y) a' => φ (g (e a'))) =
        (fun (g' : A' → Y) a' => φ (g' a')) ∘ fun (g : A → Y) a' => g (e a') := rfl
    rw [h, ← map_comp, map_uniformOfFintype_comp_embedding, map_uniformOfFintype_comp_left hφ]
  have h2 : (uniformOfFintype (Fin k → A → Y)).map (fun g j a' => φ (g j (e a'))) =
      uniformOfFintype (Fin k → A' → Z) := by
    have h := pi_map (fun _ : Fin k => uniformOfFintype (A → Y)) fun _ g a' => φ (g (e a'))
    rw [pi_uniformOfFintype] at h
    rw [h]
    simp only [h1]
    exact pi_uniformOfFintype
  have h : (fun (c : (Fin k → A → Y) × (Fin k → B)) j => ((fun a' => φ (c.1 j (e a'))), c.2 j)) =
      (Equiv.arrowProdEquivProdArrow _ _ _).symm ∘
        Prod.map (fun g j a' => φ (g j (e a'))) id := by
    funext c j
    rfl
  rw [h, ← map_comp, map_uniformOfFintype_prodMap h2 (map_id _), map_uniformOfFintype_equiv]

end Uniform

end PMF

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature PMF
open scoped ENNReal NNReal BigOperators

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### A uniform oracle at the base signer's points -/

section Oracles

variable {prims : Primitives p} [Fintype Y] [Nonempty Y]

/-- **A domain separation of the base signer's oracles with uniform decodings**: the points of
the message-representative, commitment-hash and check oracles are injective with pairwise
disjoint ranges, and the three decodings push the uniform law on `Y` to the uniform law on their
ranges. A uniform oracle at these points is then three independent uniform oracles `H_µ`, `H`,
`G` (`expect_gameOrc_split`). `sumOracles` at decodings with this property satisfies it
(`uniformSplit_sumOracles`). -/
structure W1Oracles.UniformSplit (O : W1Oracles X Y p prims Msg N reps) : Prop where
  /-- The message points are injective. -/
  muPt_injective : Function.Injective O.muPt
  /-- The commitment-hash points are injective. -/
  chPt_injective : Function.Injective O.chPt
  /-- The check points are injective. -/
  gPt_injective : Function.Injective O.gPt
  /-- Message and commitment-hash points differ. -/
  muPt_ne_chPt : ∀ a b, O.muPt a ≠ O.chPt b
  /-- Message and check points differ. -/
  muPt_ne_gPt : ∀ a b, O.muPt a ≠ O.gPt b
  /-- Commitment-hash and check points differ. -/
  chPt_ne_gPt : ∀ a b, O.chPt a ≠ O.gPt b
  /-- The message representatives are uniform. -/
  map_muAns : (uniformOfFintype Y).map O.muAns = uniformOfFintype (Bytes 64)
  /-- The commitment hashes are uniform. -/
  map_chAns : (uniformOfFintype Y).map O.chAns = uniformOfFintype (CommitHashBytes p)
  /-- The check values are uniform. -/
  map_gAns : (uniformOfFintype Y).map O.gAns = uniformOfFintype (CommitHashBytes p)

variable (O : W1Oracles X Y p prims Msg N reps)

/-- **The base signer's points inside the points of the split**: message, commitment-hash and
check points as one sum type (`W1Pts`). -/
def W1Oracles.ptEmb (hO : O.UniformSplit) : W1Pts p prims Msg N reps ↪ {x // O.IsPt x} where
  toFun a := match a with
    | .inl a => ⟨O.muPt a, Or.inl ⟨a, rfl⟩⟩
    | .inr (.inl a) => ⟨O.chPt a, Or.inr (Or.inl ⟨a, rfl⟩)⟩
    | .inr (.inr a) => ⟨O.gPt a, Or.inr (Or.inr ⟨a, rfl⟩)⟩
  inj' := by
    rintro (a | a | a) (b | b | b) h <;> replace h := congrArg Subtype.val h <;> dsimp only at h
    · exact congrArg _ (hO.muPt_injective h)
    · exact absurd h (hO.muPt_ne_chPt a b)
    · exact absurd h (hO.muPt_ne_gPt a b)
    · exact absurd h.symm (hO.muPt_ne_chPt b a)
    · exact congrArg _ (congrArg _ (hO.chPt_injective h))
    · exact absurd h (hO.chPt_ne_gPt a b)
    · exact absurd h.symm (hO.muPt_ne_gPt b a)
    · exact absurd h.symm (hO.chPt_ne_gPt b a)
    · exact congrArg _ (congrArg _ (hO.gPt_injective h))

/-- **The game's oracles from values at the base signer's points**: the three decoded
oracles `((H_µ, H), G)`. -/
def W1Oracles.decodePts (f : W1Pts p prims Msg N reps → Y) : GameOrc prims Msg N reps :=
  ((fun a => O.muAns (f (.inl a)), fun a => O.chAns (f (.inr (.inl a)))),
    fun a => O.gAns (f (.inr (.inr a))))

omit [Fintype Y] [Nonempty Y] in
open Classical in
/-- The oracle assembled by the split takes the first part's value at a point of the base
signer's oracles. -/
theorem W1Oracles.split_symm_apply_of_isPt (ω₂ : {x // O.IsPt x} → Y)
    (h₁ : {x // ¬ O.IsPt x} → Y) {x : X} (hx : O.IsPt x) : O.split.symm (ω₂, h₁) x = ω₂ ⟨x, hx⟩ := by
  simp [W1Oracles.split, Equiv.piEquivPiSubtypeProd_symm_apply, hx]

open Classical in
/-- **The game's oracles read off the split** are the decoded values of its first part at the
base signer's points. -/
theorem W1Oracles.gameOrc_split_symm (hO : O.UniformSplit) (ω₂ : {x // O.IsPt x} → Y)
    (h₁ : {x // ¬ O.IsPt x} → Y) :
    O.gameOrc (O.split.symm (ω₂, h₁)) = O.decodePts fun a => ω₂ (O.ptEmb hO a) := by
  refine Prod.ext (Prod.ext (funext fun a => ?_) (funext fun a => ?_)) (funext fun a => ?_)
  · exact congrArg O.muAns (O.split_symm_apply_of_isPt ω₂ h₁ (Or.inl ⟨a, rfl⟩))
  · exact congrArg O.chAns (O.split_symm_apply_of_isPt ω₂ h₁ (Or.inr (Or.inl ⟨a, rfl⟩)))
  · exact congrArg O.gAns (O.split_symm_apply_of_isPt ω₂ h₁ (Or.inr (Or.inr ⟨a, rfl⟩)))

omit [Fintype Y] [Nonempty Y] in
/-- The game's oracles read off two oracles with the same first part of the split agree. -/
theorem W1Oracles.gameOrc_eq_of_split {H H' : X → Y} (h : (O.split H).1 = (O.split H').1) :
    O.gameOrc H = O.gameOrc H' := by
  simp only [W1Oracles.gameOrc, O.muOrc_eq_of_split h, O.chOrc_eq_of_split h, O.gOrc_eq_of_split h]

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype Msg] [DecidableEq Msg]

open Classical in
/-- **The decoded oracles of a uniform function are uniform** (`map_uniformOfFintype_comp_left`,
`map_uniformOfFintype_prodMap`). -/
theorem W1Oracles.map_decodePts (hO : O.UniformSplit) :
    (uniformOfFintype (W1Pts p prims Msg N reps → Y)).map O.decodePts =
      uniformOfFintype (GameOrc prims Msg N reps) := by
  classical
  let E : (W1Pts p prims Msg N reps → Y) ≃
      ((Bytes 64 × Msg → Y) × (Bytes 64 × BucketVec p → Y)) ×
        (KeyRing (PubKey p prims) N × Fin N × Fin reps → Y) :=
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow _ _ _))).trans
      (Equiv.prodAssoc _ _ _).symm
  have h : O.decodePts = Prod.map (Prod.map (fun g a => O.muAns (g a)) fun g a => O.chAns (g a))
      (fun g a => O.gAns (g a)) ∘ E := by
    funext f
    rfl
  rw [h, ← PMF.map_comp, map_uniformOfFintype_equiv,
    map_uniformOfFintype_prodMap (map_uniformOfFintype_prodMap
      (map_uniformOfFintype_comp_left hO.map_muAns) (map_uniformOfFintype_comp_left hO.map_chAns))
      (map_uniformOfFintype_comp_left hO.map_gAns)]

open Classical in
/-- **A uniform oracle at the base signer's points gives uniform game oracles**: for a domain
separation with uniform decodings (`W1Oracles.UniformSplit`), the average over the first part `ω₂`
of the split of a function of the game's oracles read off the oracle is its average over uniform
`((H_µ, H), G)` (`PMF.expect_comp_embedding` along `ptEmb`, `map_decodePts`). -/
theorem W1Oracles.expect_gameOrc_split [Fintype X] [DecidableEq X] (hO : O.UniformSplit)
    (h₁ : {x // ¬ O.IsPt x} → Y) (F : GameOrc prims Msg N reps → ℝ) :
    𝔼 ω₂ : ({x // O.IsPt x} → Y), F (O.gameOrc (O.split.symm (ω₂, h₁))) =
      𝔼 HG : GameOrc prims Msg N reps, F HG := by
  simp only [O.gameOrc_split_symm hO]
  rw [PMF.expect_comp_embedding (O.ptEmb hO) fun f => F (O.decodePts f)]
  exact expect_comp_of_map_eq (O.map_decodePts hO) F

open Classical in
/-- **A uniform oracle gives uniform game oracles**: for a domain separation with uniform
decodings, the average over a uniform oracle of a function of the game's oracles read off it is
its average over uniform `((H_µ, H), G)` (`expect_gameOrc_split` at every value off the base
signer's points). -/
theorem W1Oracles.expect_gameOrc [Fintype X] [DecidableEq X] (hO : O.UniformSplit)
    (F : GameOrc prims Msg N reps → ℝ) :
    𝔼 H : X → Y, F (O.gameOrc H) = 𝔼 HG : GameOrc prims Msg N reps, F HG := by
  rw [Fintype.expect_equiv O.split (fun H => F (O.gameOrc H))
    (fun q => F (O.gameOrc (O.split.symm q))) fun H => by rw [Equiv.symm_apply_apply],
    ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  simp only [O.expect_gameOrc_split hO]
  exact Finset.expect_const Finset.univ_nonempty _

open Classical in
/-- **A ring of defect at least `s` passes the check of a uniform oracle with probability at most
`checkError reps tol s x`**, for a domain separation with uniform decodings and `x ≥ 1`
(`expect_gameOrc`, `expect_ringCheck_le`). -/
theorem W1Oracles.expect_ringCheck_gOrc_le [NeZero (bucketCount p)] [NTTRingOps]
    [Fintype X] [DecidableEq X]
    (hO : O.UniformSplit)
    (βmin : ℚ≥0) (tol : ℕ) (R : KeyRing (PubKey p prims) N) {s x : ℝ}
    (hs : s ≤ ringDefect prims βmin R.1) (hx : 1 ≤ x) :
    𝔼 H : X → Y, (if RingCheck prims βmin tol (O.gOrc H) R then 1 else 0 : ℝ) ≤
      checkError reps tol s x := by
  have h := O.expect_gameOrc hO fun HG => if RingCheck prims βmin tol HG.2 R then 1 else 0
  change 𝔼 H : X → Y, (if RingCheck prims βmin tol (O.gameOrc H).2 R then 1 else 0 : ℝ) ≤ _
  rw [h, Finset.expect_comp_snd (fun G : CheckOrc p prims N reps =>
    (if RingCheck prims βmin tol G R then 1 else 0 : ℝ))]
  exact expect_ringCheck_le prims βmin tol R hs hx

end Oracles


/-! ### The public-value law of the fresh-mask base signer -/

/-- **Mapping a first acceptance** maps the accepted value. -/
theorem _root_.List.option_map_findSome? {α β γ : Type*} (f : β → γ) (g : α → Option β)
    (l : List α) : (l.findSome? g).map f = l.findSome? fun a => (g a).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases g a <;> simp [ih]

section Law

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **The recomputed commitment of an accepted attempt is its commitment** for an honest key with
`‖s₂‖∞ ≤ η`, given the signing and verification laws and a coherent encoding
(`ringVerify_attemptOutput`). -/
theorem w1Of_attemptOutput (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta) (y : MaskBox p)
    (c : CommitHashBytes p)
    (hacc : attemptAccept prims (keyGen prims seed).2 (prims.expandA (keyGen prims seed).2.rho) y c =
      true) :
    w1Of prims enc (keyGen prims seed).1 (attemptOutput prims (keyGen prims seed).2
      (prims.expandA (keyGen prims seed).2.rho) (y, c)) =
      realBuckets (prims.expandA (keyGen prims seed).2.rho) y := by
  have hver := ringVerify_attemptOutput prims h_laws hv henc (seed := seed)
    (pk := (keyGenFromSeed p prims seed).1) (sk := (keyGenFromSeed p prims seed).2) rfl hs2
    (Msg := Unit) (fun _ => c) () y (by simpa only [keyGen, keyGenFromSeed_rho] using hacc)
  simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq] at hver
  simpa only [w1Of, keyGen, keyGenFromSeed_rho, pubPk] using hver.1.1.2

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [NeZero D] in
/-- **One call with its recomputed commitment is the finite-coin call with its commitment**
(`weightedAttemptMasksFin` at the ring's weights, the signer's attempt and flattening coin), for an
honest key (`w1Of_attemptOutput`). -/
theorem callOut_map_w1Of (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (ys : Fin T → MaskBox p) (u : Fin D) :
    (callOut prims βmin D (keyGen prims seed).2 R i hc ys u).map
        (w1Of prims enc (keyGen prims seed).1) =
      (weightedAttemptMasksFin (ringWeights prims βmin (ringT0s prims R.1)) i
        (realBuckets (prims.expandA (keyGen prims seed).2.rho))
        (attemptAccept prims (keyGen prims seed).2 (prims.expandA (keyGen prims seed).2.rho))
        (fun a => (flattenCoin prims (keyGen prims seed).2 βmin a : ℝ≥0∞))
        (fun y c => attemptOutput prims (keyGen prims seed).2
          (prims.expandA (keyGen prims seed).2.rho) (y, c)) hc D ys u).map Prod.fst := by
  unfold callOut weightedAttemptMasksFin
  rcases ht : (List.finRange T).find? (fun t => attemptAccept prims (keyGen prims seed).2
      (prims.expandA (keyGen prims seed).2.rho) (ys t)
      (hc (i, realBuckets (prims.expandA (keyGen prims seed).2.rho) (ys t)))) with _ | t
  · rfl
  · dsimp only
    simp only [ENNReal.natCast_lt_natCast_mul_mul_iff]
    split_ifs
    · simp only [Option.map_some]
      exact congrArg some (w1Of_attemptOutput prims enc h_laws hv henc hs2 _ _
        (by simpa using List.find?_some ht))
    · rfl


open Classical in
/-- **A ring the fresh-mask base signer refuses** (failing the public check or with two equal
message representatives) has the refusal as its refusal-or-public-value law, for every key. -/
theorem refusalPubLaw_freshBase_of_not (H : X → Y) (kc : Bytes 32) (R : KeyRing (PubKey p prims) N)
    (m : RMsg)
    (h : ¬ (RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m))) :
    (freshBase prims O M βmin tol enc k D bmsg).refusalPubLaw H kc R m = PMF.pure none := by
  have key : ∀ i cb, (((freshBase prims O M βmin tol enc k D bmsg).bsign
      ((freshBase prims O M βmin tol enc k D bmsg).sk kc) R i m cb).run H).map
        (fun σ => ((freshBase prims O M βmin tol enc k D bmsg).pub
          ((freshBase prims O M βmin tol enc k D bmsg).pk kc) σ).run H) = none := fun i cb => by
    refine (congrArg (Option.map _) (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M)
      k D bmsg _ R _ m cb H)).trans ?_
    simp only [h, ↓reduceIte]
    rfl
  unfold BaseSigner.refusalPubLaw
  simp only [key]
  exact PMF.map_const _ _

open Classical in
/-- **The refusal-or-public-value law of the fresh-mask base signer on an admitted ring** is the
commitment law of the bounded loop of `k` finite-coin calls (`weightedAttemptMasksFin`) with `T`
uniform masks each, for an honest key in the ring and a mask decoding pushing the uniform law to
the uniform law on the mask box (`hMask`): the `T` masks of a call are the mask function at the
distinct points `(t, (K, (tr, m)))` (`map_uniformOfFintype_callCoins`), the loop stops at the first
kept call (`map_uniform_findSome?_eq_firstSome`), and the public value of a kept signature is its
commitment (`callOut_map_w1Of`). -/
theorem refusalPubLaw_freshBase_eq
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {kc : Bytes 32} (hs2 : polyVecBounded (keyGen prims kc).2.s2 p.eta) (H : X → Y)
    (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (hi : R.1.idxOf ((freshBase prims O M βmin tol enc k D bmsg).pk kc) < R.1.length)
    (hok : RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m)) :
    (freshBase prims O M βmin tol enc k D bmsg).refusalPubLaw H kc R m =
      (firstSome ((uniformOfFintype ((Fin T → MaskBox p) × Fin D)).map fun z =>
        weightedAttemptMasksFin (ringWeights prims βmin (ringT0s prims R.1))
          ⟨R.1.idxOf ((freshBase prims O M βmin tol enc k D bmsg).pk kc), hi⟩
          (realBuckets (prims.expandA (keyGen prims kc).2.rho))
          (attemptAccept prims (keyGen prims kc).2 (prims.expandA (keyGen prims kc).2.rho))
          (fun a => (flattenCoin prims (keyGen prims kc).2 βmin a : ℝ≥0∞))
          (fun y c => attemptOutput prims (keyGen prims kc).2
            (prims.expandA (keyGen prims kc).2.rho) (y, c))
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) D z.1 z.2) k).map
        (Option.map Prod.fst) := by
  let e : Fin T ↪ MaskPt T Msg := ⟨fun t => (t, ((keyGen prims kc).2.key, ((keyGen prims kc).2.tr,
    bmsg R m))), fun a b h => congrArg Prod.fst h⟩
  set fin := fun z : (Fin T → MaskBox p) × Fin D =>
    weightedAttemptMasksFin (ringWeights prims βmin (ringT0s prims R.1))
      ⟨R.1.idxOf ((freshBase prims O M βmin tol enc k D bmsg).pk kc), hi⟩
      (realBuckets (prims.expandA (keyGen prims kc).2.rho))
      (attemptAccept prims (keyGen prims kc).2 (prims.expandA (keyGen prims kc).2.rho))
      (fun a => (flattenCoin prims (keyGen prims kc).2 βmin a : ℝ≥0∞))
      (fun y c => attemptOutput prims (keyGen prims kc).2 (prims.expandA (keyGen prims kc).2.rho)
        (y, c))
      (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) D z.1 z.2
  have key : ∀ cb : (Fin k → MaskPt T Msg → Y) × (Fin k → Fin D),
      (((freshBase prims O M βmin tol enc k D bmsg).bsign
        ((freshBase prims O M βmin tol enc k D bmsg).sk kc) R
        (R.1.idxOf ((freshBase prims O M βmin tol enc k D bmsg).pk kc)) m cb).run H).map
          (fun σ => ((freshBase prims O M βmin tol enc k D bmsg).pub
            ((freshBase prims O M βmin tol enc k D bmsg).pk kc) σ).run H) =
        ((List.finRange k).findSome? fun c => fin ((fun t => M.ans (cb.1 c (e t))), cb.2 c)).map
          Prod.fst := fun cb => by
    refine (congrArg (Option.map _) (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M)
      k D bmsg _ R _ m cb H)).trans ?_
    simp only [hok, hi, and_self, ↓reduceIte, ↓reduceDIte]
    unfold loopOut
    erw [List.option_map_findSome?, List.option_map_findSome?]
    congr 1
    funext c
    exact callOut_map_w1Of prims βmin enc D h_laws hv henc hs2 R _ _ _ _
  have hfun : (fun cb : (Fin k → MaskPt T Msg → Y) × (Fin k → Fin D) =>
      ((List.finRange k).findSome? fun c => fin ((fun t => M.ans (cb.1 c (e t))), cb.2 c)).map
        Prod.fst) =
      (Option.map Prod.fst ∘ fun z : Fin k → (Fin T → MaskBox p) × Fin D =>
        (List.finRange k).findSome? fun c => fin (z c)) ∘
        fun cb : (Fin k → MaskPt T Msg → Y) × (Fin k → Fin D) =>
          fun j => ((fun t => M.ans (cb.1 j (e t))), cb.2 j) := rfl
  unfold BaseSigner.refusalPubLaw
  simp only [RingSignature.idxOf_decEq_eq]
  refine (congrArg (fun f => PMF.map f (uniformOfFintype _)) ((funext key).trans hfun)).trans ?_
  refine (PMF.map_comp _ _ _).symm.trans ?_
  erw [map_uniformOfFintype_callCoins (B := Fin D) k e hMask]
  refine (PMF.map_comp _ _ _).symm.trans ?_
  rw [map_uniform_findSome?_eq_firstSome]


open Classical in
/-- **The fresh-mask base signer on an admitted ring against the unbounded ideal loop**: for `T ≥ 1`
masks per call, an honest key in the ring and a uniform mask decoding, its refusal-or-public-value
law is within `k / D` (the finite keep coin) plus the probability that `k` ideal attempts all
reject of the unbounded loop of one ideal attempt (one uniform mask, the checks of FIPS 204
Algorithm 7 and the real flattening coin, `weightedAttempt`), against the members' commitment
hashes read from `H` (`refusalPubLaw_freshBase_eq`, `tvDist_firstSome_finCall_le`). -/
theorem tvDist_refusalPubLaw_freshBase_le (hT : 0 < T)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {kc : Bytes 32} (hs2 : polyVecBounded (keyGen prims kc).2.s2 p.eta) (H : X → Y)
    (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (hi : R.1.idxOf ((freshBase prims O M βmin tol enc k D bmsg).pk kc) < R.1.length)
    (hok : RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m)) :
    tvDist ((freshBase prims O M βmin tol enc k D bmsg).refusalPubLaw H kc R m)
      (untilSome (weightedAttempt (ringWeights prims βmin (ringT0s prims R.1))
        ⟨R.1.idxOf ((freshBase prims O M βmin tol enc k D bmsg).pk kc), hi⟩ (maskUniform p)
        (realBuckets (prims.expandA (keyGen prims kc).2.rho))
        (attemptAccept prims (keyGen prims kc).2 (prims.expandA (keyGen prims kc).2.rho))
        (fun a => (flattenCoin prims (keyGen prims kc).2 βmin a : ℝ≥0∞))
        (coe_flattenCoin_le_one prims (keyGen prims kc).2 βmin)
        (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)))) ≤
      k * (D : ℝ)⁻¹ + ((weightedAttempt (ringWeights prims βmin (ringT0s prims R.1))
        ⟨R.1.idxOf ((freshBase prims O M βmin tol enc k D bmsg).pk kc), hi⟩ (maskUniform p)
        (realBuckets (prims.expandA (keyGen prims kc).2.rho))
        (attemptAccept prims (keyGen prims kc).2 (prims.expandA (keyGen prims kc).2.rho))
        (fun a => (flattenCoin prims (keyGen prims kc).2 βmin a : ℝ≥0∞))
        (coe_flattenCoin_le_one prims (keyGen prims kc).2 βmin)
        (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) none) ^ k).toReal := by
  rw [refusalPubLaw_freshBase_eq prims O M βmin tol enc k D bmsg hMask h_laws hv henc hs2 H R m hi
    hok]
  exact tvDist_firstSome_finCall_le _ _ _ _ _ (coe_flattenCoin_le_one prims _ βmin) _ _ hT D k

end Law


/-! ### The two signers of a challenge as a ring pair -/

section Pair

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] (βmin : ℚ≥0)

/-- **Two signers of a ring with distinct message representatives as a ring pair**: the members'
points `µ_j = H_µ(tr_j, m)` of the commitment-hash oracle (`ringMus`), the member weights of the
published `t₀`s, the two signers' positions `pos` and their ring attempts (`ringLoopSigner`) at
their secret keys `sk`. -/
noncomputable def reqPair (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (Hmu : MuOrc Msg) (R : KeyRing (PubKey p prims) N) (m : Msg) (hmu : MuDistinct prims Hmu R m)
    (pos : Bool → Fin R.1.length) (sk : Bool → SecretKey p) :
    PMF.RingPair (Bytes 64) (BucketVec p) (CommitHashBytes p) where
  Mem := Fin R.1.length
  pt := ⟨ringMus prims Hmu R.1 m, ringMus_injective prims hmu⟩
  wts := ringWeights prims βmin (ringT0s prims R.1)
  pos := pos
  signer b := ringLoopSigner prims (sk b) (prims.expandA (sk b).rho) hp hβ0 hβt

/-- **The attempt of a signer of the ring pair** against the commitment-hash oracle read from `H`
is its weighted attempt against the members' commitment hashes read from `H`. -/
theorem reqPair_attempt (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (O : W1Oracles X Y p prims Msg N reps) (H : X → Y) (R : KeyRing (PubKey p prims) N) (m : Msg)
    (hmu : MuDistinct prims (O.muOrc H) R m) (pos : Bool → Fin R.1.length)
    (sk : Bool → SecretKey p) (b : Bool) :
    (reqPair prims βmin hp hβ0 hβt (O.muOrc H) R m hmu pos sk).attempt b (O.chOrc H) =
      weightedAttempt (ringWeights prims βmin (ringT0s prims R.1)) (pos b) (maskUniform p)
        (realBuckets (prims.expandA (sk b).rho)) (attemptAccept prims (sk b) (prims.expandA (sk b).rho))
        (fun a => (flattenCoin prims (sk b) βmin a : ℝ≥0∞))
        (coe_flattenCoin_le_one prims (sk b) βmin)
        (PMF.ringOf (ringPts prims R.1 m) (O.hOrc H)) :=
  rfl

end Pair

/-! ### The family of all valid challenges of low defect -/

section Family

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
  (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm]
  (n : ℕ) (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)

local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm

omit [Inhabited prims.Hint] in
/-- The position of user `b` of a valid challenge is in its ring. -/
theorem idxOf_lt_of_valid {keys : Fin n → Bytes 32} {c : AnonRequest (Sh) n} (hc : c.Valid keys)
    (b : Bool) : c.ring.1.idxOf ((Bf).pk (keys (c.user b))) < c.ring.1.length :=
  List.idxOf_lt_length_iff.2 (hc.pk_mem b)

/-- **The two users' signers of a valid challenge with distinct message representatives** as a
ring pair (`reqPair` at the users' positions and secret keys). -/
noncomputable def chalPair (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg) (c : AnonRequest (Sh) n)
    (hc : c.Valid keys) (hmu : MuDistinct prims Hmu c.ring (bmsg c.ring c.msg)) :
    PMF.RingPair (Bytes 64) (BucketVec p) (CommitHashBytes p) :=
  reqPair prims βmin hp hβ0 hβt Hmu c.ring (bmsg c.ring c.msg) hmu
    (fun b => ⟨c.ring.1.idxOf ((Bf).pk (keys (c.user b))),
      idxOf_lt_of_valid prims O M βmin tol enc k D bmsg PS adm n hc b⟩)
    (fun b => (keyGen prims (keys (c.user b))).2)

open Classical in
/-- **A valid challenge admitted by the fresh-mask base signer**: the two users' laws are within
the distance of the unbounded ideal loops of its ring pair (`chalPair`), plus for each user `k / D`
and the probability that `k` ideal attempts all reject (`tvDist_refusalPubLaw_freshBase_le`). -/
theorem tvDist_refusalPubLaw_le_chalPair (hT : 0 < T)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) (H : X → Y)
    (keys : Fin n → Bytes 32) (c : AnonRequest (Sh) n) (hc : c.Valid keys)
    (hok : RingCheck prims βmin tol (O.gOrc H) c.ring ∧
      MuDistinct prims (O.muOrc H) c.ring (bmsg c.ring c.msg)) :
    tvDist ((Bf).refusalPubLaw H (keys c.user₀) c.ring c.msg)
        ((Bf).refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤
      tvDist (untilSome ((chalPair prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys
          (O.muOrc H) c hc hok.2).attempt false (O.chOrc H)))
        (untilSome ((chalPair prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys
          (O.muOrc H) c hc hok.2).attempt true (O.chOrc H))) +
      ∑ b : Bool, (k * (D : ℝ)⁻¹ + (((chalPair prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt
        keys (O.muOrc H) c hc hok.2).attempt b (O.chOrc H) none) ^ k).toReal) := by
  set P := chalPair prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys (O.muOrc H) c hc hok.2
  have h : ∀ b, tvDist ((Bf).refusalPubLaw H (keys (c.user b)) c.ring c.msg)
      (untilSome (P.attempt b (O.chOrc H))) ≤
        k * (D : ℝ)⁻¹ + ((P.attempt b (O.chOrc H) none) ^ k).toReal := fun b =>
    tvDist_refusalPubLaw_freshBase_le prims O M βmin tol enc k D bmsg hT hMask h_laws hv henc
      (hs2 _) H c.ring c.msg (idxOf_lt_of_valid prims O M βmin tol enc k D bmsg PS adm n hc b) hok
  have h0 := h false
  have h1 := h true
  rw [tvDist_comm] at h1
  have t1 := tvDist_triangle ((Bf).refusalPubLaw H (keys c.user₀) c.ring c.msg)
    (untilSome (P.attempt false (O.chOrc H))) ((Bf).refusalPubLaw H (keys c.user₁) c.ring c.msg)
  have t2 := tvDist_triangle (untilSome (P.attempt false (O.chOrc H)))
    (untilSome (P.attempt true (O.chOrc H))) ((Bf).refusalPubLaw H (keys c.user₁) c.ring c.msg)
  rw [Fintype.sum_bool]
  change _ ≤ _ + ((k * (D : ℝ)⁻¹ + ((P.attempt true (O.chOrc H) none) ^ k).toReal) +
    (k * (D : ℝ)⁻¹ + ((P.attempt false (O.chOrc H) none) ^ k).toReal))
  calc _ ≤ _ := t1
    _ ≤ _ := add_le_add le_rfl t2
    _ ≤ _ := add_le_add h0 (add_le_add le_rfl h1)
    _ = _ := by ring

/-- The valid challenges of ring defect at most `s` with distinct message representatives at
`H_µ`. -/
abbrev LowChal (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg) (s : ℝ) : Type :=
  {c : AnonRequest (Sh) n // c.Valid keys ∧ MuDistinct prims Hmu c.ring (bmsg c.ring c.msg) ∧
    LowDefect prims βmin s c.ring}

open Classical in
noncomputable instance (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg) (s : ℝ) :
    Fintype (LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) :=
  Subtype.fintype _

/-- **The ring pairs of the valid challenges of low defect** (`chalPair`). -/
noncomputable def lowFamily (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg) (s : ℝ)
    (c : LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) :
    PMF.RingPair (Bytes 64) (BucketVec p) (CommitHashBytes p) :=
  chalPair prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu c.1 c.2.1 c.2.2.1

open Classical in
/-- **The family bound of all valid challenges of low defect** at the users' coins, `H_µ` and
the commitment-hash oracle `H`, at the threshold fraction `θ` (`familyBound`), or zero without such
challenges. The counterpart of `oracleError` over all valid challenges instead of an adversary's
finite set. -/
noncomputable def lowError (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg) (s θ : ℝ) (Hch : ChOrc p) :
    ℝ :=
  if h : Nonempty (LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) then
    haveI := h
    familyBound (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s) θ Hch
  else 0

variable {prims O M βmin tol enc k D bmsg PS adm n}

/-- The rings of defect at most `s < 1` have positive mass. -/
theorem lowFamily_mass_pos {s : ℝ} (hs1 : s < 1) (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg)
    (c : LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) :
    0 < (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s c).wts.mass :=
  RingWeights.mass_pos _ fun v => (sub_pos.2 hs1).trans_le
    (one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt c.2.2.2 v)

/-- The family bound of the valid challenges of low defect is nonnegative. -/
theorem lowError_nonneg {s θ : ℝ} (hs1 : s < 1) (hθ0 : 0 < θ) (keys : Fin n → Bytes 32)
    (Hmu : MuOrc Msg) (Hch : ChOrc p) :
    0 ≤ lowError prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s θ Hch := by
  unfold lowError
  split_ifs with h
  · exact familyBound_nonneg hθ0 (lowFamily_mass_pos hp hβ0 hβt hs1 keys Hmu) Hch
  · exact le_rfl

/-- **The error of a ring of low defect** is at most `2 / ((1 - s) θ)` times the sum of the honest
users' regularity gaps (`RingPair.error_le_of_massRatio_le`, `massRatio_le_of_ringDefect_le`,
`relColError_le_ringRegGap`). -/
theorem lowFamily_error_le (h_laws : SigningLaws prims)
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) {s θ : ℝ} (hθ0 : 0 < θ)
    (hs1 : s < 1) (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg)
    (c : LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) :
    (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s c).error θ ≤
      2 * (1 - s)⁻¹ / θ * ∑ u, ringRegGap prims (keyGen prims (keys u)).2
        (prims.expandA (keyGen prims (keys u)).2.rho) βmin := by
  set R := lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s c
  have hκ0 : 0 ≤ (1 - s)⁻¹ := (inv_pos.2 (sub_pos.2 hs1)).le
  set G := ∑ u, ringRegGap prims (keyGen prims (keys u)).2
    (prims.expandA (keyGen prims (keys u)).2.rho) βmin
  refine (RingPair.error_le_of_massRatio_le R hθ0 (fun v => (sub_pos.2 hs1).trans_le
    (one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt c.2.2.2 v))
    (massRatio_le_of_ringDefect_le prims hp hβ0 hβt c.2.2.2 hs1)).trans ?_
  have hb : ∀ b : Bool, relColError R.wts (R.pos b) (R.signer b).P (R.signer b).w1
      (R.signer b).acc (R.signer b).κ (R.signer b).β ≤ G := fun b => by
    have hlt := idxOf_lt_of_valid prims O M βmin tol enc k D bmsg PS adm n c.2.1 b
    have hget : c.1.ring.1[c.1.ring.1.idxOf ((Bf).pk (keys (c.1.user b)))] =
        (Bf).pk (keys (c.1.user b)) := List.getElem_idxOf hlt
    have hi : ringT0s prims c.1.ring.1 (R.pos b) = (keyGen prims (keys (c.1.user b))).2.t0 :=
      congrArg (fun x : PubKey p prims => x.2.2) hget
    exact (relColError_le_ringRegGap prims _ _ hp h_laws (hs2 _) _ _ hi hβ0 hβt).trans
      (Finset.single_le_sum (f := fun u => ringRegGap prims (keyGen prims (keys u)).2
        (prims.expandA (keyGen prims (keys u)).2.rho) βmin)
        (fun u _ => ringRegGap_nonneg prims _ _ βmin) (Finset.mem_univ (c.1.user b)))
  calc (1 - s)⁻¹ / θ * ∑ b : Bool, relColError R.wts (R.pos b) (R.signer b).P (R.signer b).w1
        (R.signer b).acc (R.signer b).κ (R.signer b).β
      ≤ (1 - s)⁻¹ / θ * ∑ _b : Bool, G :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hb b) (div_nonneg hκ0 hθ0.le)
    _ = 2 * (1 - s)⁻¹ / θ * G := by rw [Fintype.sum_bool]; ring

/-- **The weight variance proxy of a ring of low defect**: at most
`N / ((1 - θ)² (1 - s)² |V|)` (`RingPair.countVar_le`). -/
theorem lowFamily_countVar_le {s θ : ℝ} (hθ1 : θ < 1) (hs1 : s < 1) (keys : Fin n → Bytes 32)
    (Hmu : MuOrc Msg) (c : LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) :
    (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s c).countVar θ ≤
      N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p)) :=
  (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s c).countVar_le
    ((Fintype.card_fin _).trans_le c.1.ring.2) hθ1 (by linarith)
    (RingWeights.mul_card_le_mass _ fun v =>
      one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt c.2.2.2 v)

/-- **The deviation variance proxy of a ring of low defect**: both signers have the level
`β = K · β_min`, so it is at most
`4N / (θ (1 - s))² · (2 ∑_u CP(Â_u) / (β |V|)² + 2 / |V|)` with `CP(Â_u)` the collision probability
of user `u`'s commitment (`RingPair.devVar_le`, `commitCollision`). -/
theorem lowFamily_devVar_le {s θ : ℝ} (hθ0 : 0 < θ) (hs1 : s < 1) (keys : Fin n → Bytes 32)
    (Hmu : MuOrc Msg) (c : LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) :
    (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s c).devVar θ ≤
      4 * N / (θ * (1 - s)) ^ 2 *
        (2 * (∑ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho)) /
            ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
          2 / Fintype.card (BucketVec p)) := by
  set β := (standinScale p * βmin).toReal
  set W : ℝ := (Fintype.card (BucketVec p) : ℝ)
  set S := ∑ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho)
  have hS : ∀ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho) ≤ S := fun u =>
    Finset.single_le_sum (f := fun u => commitCollision (prims.expandA (keyGen prims (keys u)).2.rho))
      (fun u _ => commitCollision_nonneg _) (Finset.mem_univ u)
  have hK : 0 ≤ 4 * (N : ℝ) / (θ * (1 - s)) ^ 2 := by positivity
  refine ((lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s c).devVar_le
    (β := β) ((Fintype.card_fin _).trans_le c.1.ring.2) hθ0 (by linarith)
    (RingWeights.mul_card_le_mass _ fun v =>
      one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt c.2.2.2 v)
    fun b => rfl).trans (mul_le_mul_of_nonneg_left ?_ hK)
  have h0 := hS (c.1.user false)
  have h1 := hS (c.1.user true)
  rw [Fintype.sum_bool]
  change (commitCollision (prims.expandA (keyGen prims (keys (c.1.user true))).2.rho) /
      (β * W) ^ 2 + 1 / W) + (commitCollision (prims.expandA
        (keyGen prims (keys (c.1.user false))).2.rho) / (β * W) ^ 2 + 1 / W) ≤
    2 * S / (β * W) ^ 2 + 2 / W
  have hB : 0 ≤ (β * W) ^ 2 := sq_nonneg _
  have e1 := div_le_div_of_nonneg_right h0 hB
  have e2 := div_le_div_of_nonneg_right h1 hB
  have e3 : 2 * S / (β * W) ^ 2 = S / (β * W) ^ 2 + S / (β * W) ^ 2 := by ring
  have e4 : (2 : ℝ) / W = 1 / W + 1 / W := by ring
  rw [e3, e4]
  linarith


/-- **The average family bound over the commitment-hash oracle**: at most `2 / ((1 - s) θ)` times
the sum of the honest users' regularity gaps plus the McDiarmid terms of the variance proxies
(`lowFamily_devVar_le`, `lowFamily_countVar_le`), with `C` a bound on the valid challenges for
every key vector (`expect_familyBound_le`). -/
theorem expect_lowError_le (h_laws : SigningLaws prims)
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) {s θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hs1 : s < 1) {C : ℕ}
    (hC : ∀ keys : Fin n → Bytes 32,
      (Finset.univ.filter fun c : AnonRequest (Sh) n => c.Valid keys).card ≤ C)
    (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg) :
    𝔼 Hch : ChOrc p, lowError prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s θ Hch ≤
      2 * (1 - s)⁻¹ / θ * ∑ u, ringRegGap prims (keyGen prims (keys u)).2
          (prims.expandA (keyGen prims (keys u)).2.rho) βmin +
        √(4 * N / (θ * (1 - s)) ^ 2 *
            (2 * (∑ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho)) /
                ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
              2 / Fintype.card (BucketVec p)) * Real.log C / 2) +
        √(N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p)) * Real.log (C + 1) / 2) := by
  set sd := 4 * N / (θ * (1 - s)) ^ 2 *
    (2 * (∑ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho)) /
        ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
      2 / Fintype.card (BucketVec p))
  set sc := (N : ℝ) / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p))
  have hsd0 : 0 ≤ sd := mul_nonneg (by positivity) (add_nonneg (div_nonneg (mul_nonneg zero_le_two
    (Finset.sum_nonneg fun u _ => commitCollision_nonneg _)) (sq_nonneg _)) (by positivity))
  have hsc0 : 0 ≤ sc := by positivity
  have he0 : 0 ≤ 2 * (1 - s)⁻¹ / θ * ∑ u, ringRegGap prims (keyGen prims (keys u)).2
      (prims.expandA (keyGen prims (keys u)).2.rho) βmin :=
    mul_nonneg (div_nonneg (mul_nonneg zero_le_two (inv_pos.2 (sub_pos.2 hs1)).le) hθ0.le)
      (Finset.sum_nonneg fun u _ => ringRegGap_nonneg prims _ _ βmin)
  by_cases h : Nonempty (LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s)
  · have hor : ∀ Hch, lowError prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s θ Hch =
        haveI := h
        familyBound (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s) θ
          Hch := fun Hch => dite_eq_left h
    simp only [hor]
    have := h
    have hcardC : (Fintype.card (LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) : ℝ) ≤
        C := by
      have : Fintype.card (LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) ≤
          (Finset.univ.filter fun c : AnonRequest (Sh) n => c.Valid keys).card := by
        refine (Fintype.card_le_of_injective (fun c => (⟨c.1, by simpa using c.2.1⟩ :
          (Finset.univ.filter fun c : AnonRequest (Sh) n => c.Valid keys))) fun c c' hcc => by
            have h' := congrArg Subtype.val hcc
            exact Subtype.ext h').trans_eq (Fintype.card_coe _)
      exact_mod_cast this.trans (hC keys)
    have hcard1 : (0 : ℝ) < Fintype.card (LowChal prims O M βmin tol enc k D bmsg PS adm n keys Hmu s) := by
      exact_mod_cast Fintype.card_pos
    refine (expect_familyBound_le hθ0 hθ1 (lowFamily_mass_pos hp hβ0 hβt hs1 keys Hmu)
      (lowFamily_error_le hp hβ0 hβt h_laws hs2 hθ0 hs1 keys Hmu)
      (lowFamily_devVar_le hp hβ0 hβt hθ0 hs1 keys Hmu)
      (lowFamily_countVar_le hp hβ0 hβt hθ1 hs1 keys Hmu)).trans ?_
    refine add_le_add (add_le_add le_rfl ?_) ?_
    · exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.log_le_log hcard1 hcardC) hsd0) (by norm_num))
    · exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hsc0)
        (by norm_num))
  · have hor : ∀ Hch, lowError prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys Hmu s θ Hch =
        0 := fun Hch => dite_eq_right h
    simp only [hor, Finset.expect_const_zero]
    exact add_nonneg (add_nonneg he0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

variable (prims O M βmin tol enc k D bmsg PS adm n) in
/-- **The coupling bound on rings of low defect** at the game's oracles `((H_µ, H), G)`: twice the
family bound of the valid challenges of low defect, twice the cost `k / D` of the finite keep coin
and twice the bound `(1 - Lk)^k` on `k` rejecting attempts. -/
noncomputable def couplingBound (keys : Fin n → Bytes 32) (s θ Lk : ℝ)
    (HG : GameOrc prims Msg N reps) : ℝ :=
  2 * lowError prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys HG.1.1 s θ HG.1.2 +
    2 * (k * (D : ℝ)⁻¹) + 2 * (1 - Lk) ^ k

/-- The coupling bound on rings of low defect is nonnegative. -/
theorem couplingBound_nonneg {s θ Lk : ℝ} (hs1 : s < 1) (hθ0 : 0 < θ) (hLk1 : Lk ≤ 1)
    (keys : Fin n → Bytes 32) (HG : GameOrc prims Msg N reps) :
    0 ≤ couplingBound prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys s θ Lk HG := by
  unfold couplingBound
  have h1 := lowError_nonneg (O := O) (M := M) (βmin := βmin) (tol := tol) (enc := enc) (k := k) (D := D) (bmsg := bmsg) (PS := PS) (adm := adm) hp hβ0 hβt hs1 hθ0 keys HG.1.1 HG.1.2
  have h2 : 0 ≤ (1 - Lk) ^ k := pow_nonneg (sub_nonneg.2 hLk1) _
  have h3 : (0 : ℝ) ≤ k * (D : ℝ)⁻¹ := by positivity
  linarith

/-- **The two users' laws of a valid challenge on a ring of defect at most `s` are within the
coupling bound on rings of low defect** at the game's oracles read from `H`, for `T ≥ 1` masks per
call, a uniform mask decoding, honest keys, and any `Lk ≤ 1` at most the keep level: a refused ring
has the refusal in both experiments; otherwise the two ideal loops are within the family bound
(`tvDist_le_familyBound`), each ideal attempt keeps with probability at least `Lk` when the family
bound is below `1/2` (`keep_ge_of_familyBound_lt`) and the distance is at most
`1 ≤ 2 · familyBound` otherwise (`tvDist_refusalPubLaw_le_chalPair`). -/
theorem tvDist_refusalPubLaw_le_couplingBound (hT : 0 < T)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) {s θ Lk : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hs1 : s < 1) (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1) (H : X → Y)
    (keys : Fin n → Bytes 32) (c : AnonRequest (Sh) n) (hc : c.Valid keys)
    (hlow : LowDefect prims βmin s c.ring) :
    tvDist ((Bf).refusalPubLaw H (keys c.user₀) c.ring c.msg)
        ((Bf).refusalPubLaw H (keys c.user₁) c.ring c.msg) ≤
      couplingBound prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys s θ Lk
        (O.gameOrc H) := by
  have hΦ0 := couplingBound_nonneg (O := O) (M := M) (βmin := βmin) (tol := tol) (enc := enc) (k := k) (D := D) (bmsg := bmsg) (PS := PS) (adm := adm) hp hβ0 hβt hs1 hθ0 hLk1 keys (O.gameOrc H)
  have h2 : 0 ≤ (1 - Lk) ^ k := pow_nonneg (sub_nonneg.2 hLk1) _
  have h3 : (0 : ℝ) ≤ k * (D : ℝ)⁻¹ := by positivity
  by_cases hok : RingCheck prims βmin tol (O.gOrc H) c.ring ∧
      MuDistinct prims (O.muOrc H) c.ring (bmsg c.ring c.msg)
  · let m : LowChal prims O M βmin tol enc k D bmsg PS adm n keys (O.muOrc H) s := ⟨c, hc, hok.2, hlow⟩
    have hne : Nonempty (LowChal prims O M βmin tol enc k D bmsg PS adm n keys (O.muOrc H) s) := ⟨m⟩
    set F := lowError prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys (O.muOrc H) s θ
      (O.chOrc H)
    have hF : F = familyBound (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys
        (O.muOrc H) s) θ (O.chOrc H) := dite_eq_left hne
    set P := chalPair prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys (O.muOrc H) c hc hok.2
    have htv := tvDist_refusalPubLaw_le_chalPair prims O M βmin tol enc k D bmsg PS adm n hp hβ0
      hβt hT hMask h_laws hv henc hs2 H keys c hc hok
    have hU : tvDist (untilSome (P.attempt false (O.chOrc H)))
        (untilSome (P.attempt true (O.chOrc H))) ≤ F :=
      hF ▸ tvDist_le_familyBound hθ0 hθ1 (lowFamily_mass_pos hp hβ0 hβt hs1 keys (O.muOrc H)) m
        (O.chOrc H)
    have hF0 : 0 ≤ F := lowError_nonneg (O := O) (M := M) (βmin := βmin) (tol := tol) (enc := enc) (k := k) (D := D) (bmsg := bmsg) (PS := PS) (adm := adm) hp hβ0 hβt hs1 hθ0 keys (O.muOrc H) (O.chOrc H)
    have hΦ : couplingBound prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys s θ Lk
        (O.gameOrc H) = 2 * F + 2 * (k * (D : ℝ)⁻¹) + 2 * (1 - Lk) ^ k := rfl
    rw [hΦ]
    by_cases hF2 : F < 1 / 2
    · have hkeep : ∀ b, ((P.attempt b (O.chOrc H) none) ^ k).toReal ≤ (1 - Lk) ^ k := fun b => by
        have hk := keep_ge_of_familyBound_lt (lowFamily prims O M βmin tol enc k D bmsg PS adm n hp
          hβ0 hβt keys (O.muOrc H) s) hθ0 hθ1 (lowFamily_mass_pos hp hβ0 hβt hs1 keys (O.muOrc H))
          (hF ▸ hF2) m b
        have hmass : (1 - s) * Fintype.card (BucketVec p) ≤ P.wts.mass := by
          calc (1 - s) * Fintype.card (BucketVec p) = ∑ _v : BucketVec p, (1 - s) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
            _ ≤ _ := Finset.sum_le_sum fun v _ =>
                one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt hlow v
        have hlev : Lk ≤ (1 - P.attempt b (O.chOrc H) none).toReal := by
          refine hLk.trans (le_trans ?_ hk)
          unfold keepLevel
          change (standinScale p * βmin).toReal * (θ * ((1 - s) * Fintype.card (BucketVec p))) / 2 ≤
            (standinScale p * βmin).toReal * (θ * P.wts.mass) / 2
          have hβ := ringLevel_pos hp hβ0 hβt
          gcongr
        have ha1 : P.attempt b (O.chOrc H) none ≤ 1 := PMF.coe_le_one _ _
        rw [ENNReal.toReal_sub_of_le ha1 ENNReal.one_ne_top, ENNReal.toReal_one] at hlev
        rw [ENNReal.toReal_pow]
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg (by linarith) k
      have h0 := hkeep false
      have h1 := hkeep true
      rw [Fintype.sum_bool] at htv
      linarith
    · push Not at hF2
      linarith [tvDist_le_one ((Bf).refusalPubLaw H (keys c.user₀) c.ring c.msg)
        ((Bf).refusalPubLaw H (keys c.user₁) c.ring c.msg)]
  · rw [refusalPubLaw_freshBase_of_not prims O M βmin tol enc k D bmsg H _ c.ring c.msg hok,
      refusalPubLaw_freshBase_of_not prims O M βmin tol enc k D bmsg H _ c.ring c.msg hok, tvDist_self]
    exact hΦ0

end Family


/-! ### The average coupling error -/

section Average

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] (βmin : ℚ≥0)

/-- **The average regularity gap of an honest key** at the cut-off `β_min`: the regularity gap
`ringRegGap` of the key of a uniform seed at its matrix `Â = ExpandA(ρ)` (FIPS 204 key generation
`keyGen` at the primitives `prims`). -/
noncomputable def regGapAt : ℝ :=
  𝔼 seed : Bytes 32, ringRegGap prims (keyGen prims seed).2 (prims.expandA (keyGen prims seed).2.rho)
    βmin

/-- **The average commitment collision probability of an honest key**: `commitCollision` at the
matrix `Â = ExpandA(ρ)` of the key of a uniform seed. -/
noncomputable def collAt : ℝ :=
  𝔼 seed : Bytes 32, commitCollision (prims.expandA (keyGen prims seed).2.rho)

variable (N n : ℕ) (s θ : ℝ) (C k D : ℕ) (Lk : ℝ) (reps tol : ℕ) (x : ℝ)

/-- **The coupling error of the fresh-mask w1 signer** for `n` honest users, rings of at most `N`
members, at most `C` valid challenges per key vector, `k` calls with keep coins on `Fin D`, the
defect budget `s`, the threshold fraction `θ` and a keep level `Lk`: twice the regularity term
`2 / ((1 - s) θ) · n · regGapAt` and the McDiarmid terms (with the collision term `n · collAt`),
twice `k / D` for the finite keep coin and twice `(1 - Lk)^k` for `k` rejecting calls. It bounds
the averaged coupling error of a scheme whose supported rings all have defect at most `s`
(`expect_idealDist_le`). -/
noncomputable def w1CouplingError : ℝ :=
  2 * (2 * (1 - s)⁻¹ / θ * (n * regGapAt prims βmin) +
      √(4 * N / (θ * (1 - s)) ^ 2 *
          (2 * (n * collAt prims) / ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
            2 / Fintype.card (BucketVec p)) * Real.log C / 2) +
      √(N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p)) * Real.log (C + 1) / 2)) +
    2 * (k * (D : ℝ)⁻¹) + 2 * (1 - Lk) ^ k

end Average

section AverageBound

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
  (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm]
  (n : ℕ) (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) [Fintype X]
  [DecidableEq X]

local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm

open Classical in
/-- **The coupling error of the fresh-mask signer at fixed oracles is at most the coupling bound
on rings of low defect** at the game's oracles read off the split, when every supported ring has
defect at most `s` (`hadm`; `tvDist_refusalPubLaw_le_couplingBound` for every valid challenge
on a supported ring; the game's oracles depend only on the first part `ω₂`). -/
theorem idealDist_le_couplingBound (hT : 0 < T)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) {s θ Lk : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hs1 : s < 1) (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1)
    (hadm : ∀ R, adm R → LowDefect prims βmin s R)
    (keys : Fin n → Bytes 32) (ω₂ : {x // O.IsPt x} → Y) (h₀ : {x // ¬ O.IsPt x} → Y) :
    idealDist prims O M βmin tol enc k D bmsg PS adm n keys ω₂ ≤
      couplingBound prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys s θ Lk
        (O.gameOrc (O.split.symm (ω₂, h₀))) := by
  have hΦ0 := couplingBound_nonneg (O := O) (M := M) (βmin := βmin) (tol := tol) (enc := enc)
    (k := k) (D := D) (bmsg := bmsg) (PS := PS) (adm := adm) hp hβ0 hβt hs1 hθ0 hLk1 keys
    (O.gameOrc (O.split.symm (ω₂, h₀)))
  unfold idealDist
  refine (NNReal.coe_le_coe.2 (Finset.sup_le fun q hq => ?_)).trans_eq (NNReal.coe_mk _ hΦ0)
  refine NNReal.coe_le_coe.1 ?_
  have hva : q.2.Valid keys ∧ adm q.2.ring := by
    have h := (Finset.mem_product.1 hq).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hG : O.gameOrc (O.split.symm (ω₂, q.1)) = O.gameOrc (O.split.symm (ω₂, h₀)) :=
    O.gameOrc_eq_of_split (by simp only [Equiv.apply_symm_apply])
  exact (tvDist_refusalPubLaw_le_couplingBound hp hβ0 hβt hT hMask h_laws hv henc hs2 hθ0 hθ1 hs1 hLk hLk1 _ keys q.2 hva.1 (hadm _ hva.2)).trans_eq
    (congrArg (couplingBound prims O M βmin tol enc k D bmsg PS adm n hp hβ0 hβt keys s θ Lk) hG)

include hp hβ0 hβt in
open Classical in
/-- **The averaged coupling error of the fresh-mask signer on rings of low defect**: averaged over
the honest users' coins and the oracle at the base signer's points, `idealDist` is at most
`w1CouplingError` when every supported ring has defect at most `s` (`hadm`), for `T ≥ 1`
masks per call, a domain separation with uniform decodings (`hO`), a uniform mask decoding
(`hMask`), the signing and verification laws, a coherent encoding, `‖s₂‖∞ ≤ η` for every honest
key, any defect budget `s < 1`, threshold fraction `θ ∈ (0, 1)`, keep level `Lk ≤ 1` at
most `keepLevel`, and `C` a bound on the valid challenges for every key vector. The game's oracles
read off a uniform first part are uniform (`W1Oracles.expect_gameOrc_split`); the family bound
averages to the regularity and McDiarmid terms (`expect_lowError_le`); and the users' coins enter
through the average
regularity gap and collision probability of one honest key (`PMF.expect_apply_eval`, Jensen's
inequality `Real.expect_sqrt_le_sqrt_expect`). -/
theorem expect_idealDist_le (hT : 0 < T) (hO : O.UniformSplit)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) {s θ Lk : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hs1 : s < 1) (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1)
    (hadm : ∀ R, adm R → LowDefect prims βmin s R) {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32,
      (Finset.univ.filter fun c : AnonRequest (Sh) n => c.Valid keys).card ≤ C) :
    𝔼 keys : Fin n → Bytes 32, 𝔼 ω₂ : ({x // O.IsPt x} → Y),
        idealDist prims O M βmin tol enc k D bmsg PS adm n keys ω₂ ≤
      w1CouplingError prims βmin N n s θ C k D Lk := by
  obtain ⟨h₀⟩ : Nonempty ({x // ¬ O.IsPt x} → Y) := inferInstance
  set β := (standinScale p * βmin).toReal
  set W : ℝ := (Fintype.card (BucketVec p) : ℝ)
  set A : ℝ := 4 * N / (θ * (1 - s)) ^ 2
  set L : ℝ := Real.log C
  set sc : ℝ := N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * W)
  set K : ℝ := 2 * (k * (D : ℝ)⁻¹) + 2 * (1 - Lk) ^ k
  set gap : (Fin n → Bytes 32) → ℝ := fun keys => ∑ u, ringRegGap prims (keyGen prims (keys u)).2
    (prims.expandA (keyGen prims (keys u)).2.rho) βmin
  set cp : (Fin n → Bytes 32) → ℝ := fun keys =>
    ∑ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho)
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg C
  have hA0 : 0 ≤ A := by positivity
  have hcp0 : ∀ keys, 0 ≤ cp keys := fun keys => Finset.sum_nonneg fun u _ => commitCollision_nonneg _
  -- the bound at fixed users' coins
  have hkey : ∀ keys : Fin n → Bytes 32,
      𝔼 ω₂ : ({x // O.IsPt x} → Y), idealDist prims O M βmin tol enc k D bmsg PS adm n keys ω₂ ≤
        2 * (2 * (1 - s)⁻¹ / θ * gap keys + √(A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2) +
          √(sc * Real.log (C + 1) / 2)) + K := fun keys => by
    have hL : 𝔼 Hmu : MuOrc Msg, 𝔼 Hch : ChOrc p, lowError prims O M βmin tol enc k D bmsg PS adm n
        hp hβ0 hβt keys Hmu s θ Hch ≤ 2 * (1 - s)⁻¹ / θ * gap keys +
          √(A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2) + √(sc * Real.log (C + 1) / 2) :=
      (Finset.expect_le_expect fun Hmu _ => expect_lowError_le hp hβ0 hβt h_laws hs2 hθ0 hθ1 hs1
        hC keys Hmu).trans_eq (Finset.expect_const Finset.univ_nonempty _)
    calc 𝔼 ω₂ : ({x // O.IsPt x} → Y), idealDist prims O M βmin tol enc k D bmsg PS adm n keys ω₂
        ≤ 𝔼 ω₂ : ({x // O.IsPt x} → Y), couplingBound prims O M βmin tol enc k D bmsg PS adm n hp
            hβ0 hβt keys s θ Lk (O.gameOrc (O.split.symm (ω₂, h₀))) :=
          Finset.expect_le_expect fun ω₂ _ => idealDist_le_couplingBound prims O M βmin tol enc k D
            bmsg PS adm n hp hβ0 hβt hT hMask h_laws hv henc hs2 hθ0 hθ1 hs1 hLk hLk1 hadm keys ω₂ h₀
      _ = 𝔼 HG : GameOrc prims Msg N reps, couplingBound prims O M βmin tol enc k D bmsg PS adm n hp
            hβ0 hβt keys s θ Lk HG := O.expect_gameOrc_split hO h₀ _
      _ = 2 * 𝔼 Hmu : MuOrc Msg, 𝔼 Hch : ChOrc p, lowError prims O M βmin tol enc k D bmsg PS adm
            n hp hβ0 hβt keys Hmu s θ Hch + (2 * (k * (D : ℝ)⁻¹) + 2 * (1 - Lk) ^ k) := by
          unfold couplingBound
          rw [Finset.expect_add_distrib, Finset.expect_add_distrib,
            ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty,
            Finset.expect_const Finset.univ_nonempty,
            Finset.expect_comp_fst (fun SH : SchOrc p Msg => lowError prims O M βmin tol enc k D bmsg
              PS adm n hp hβ0 hβt keys SH.1 s θ SH.2), ← Finset.univ_product_univ,
            Finset.expect_product]
          ring
      _ ≤ _ := by
          simp only [K]
          linarith
  -- the average over the users' coins
  have hgap : 𝔼 keys : Fin n → Bytes 32, gap keys = n * regGapAt prims βmin := by
    simp only [gap]
    rw [Finset.expect_sum_comm, Finset.sum_congr rfl fun u _ => PMF.expect_apply_eval u
      (fun x => ringRegGap prims (keyGen prims x).2 (prims.expandA (keyGen prims x).2.rho) βmin)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, regGapAt]
  have hcp : 𝔼 keys : Fin n → Bytes 32, cp keys = n * collAt prims := by
    simp only [cp]
    rw [Finset.expect_sum_comm, Finset.sum_congr rfl fun u _ => PMF.expect_apply_eval u
      (fun x => commitCollision (prims.expandA (keyGen prims x).2.rho))]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, collAt]
  have hsd : 𝔼 keys : Fin n → Bytes 32, √(A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2) ≤
      √(A * (2 * (n * collAt prims) / (β * W) ^ 2 + 2 / W) * L / 2) := by
    refine (Real.expect_sqrt_le_sqrt_expect _ fun keys => by
      have := hcp0 keys
      positivity).trans (Real.sqrt_le_sqrt (le_of_eq ?_))
    have hlin : ∀ keys : Fin n → Bytes 32, A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2 =
        (A * L / (β * W) ^ 2) * cp keys + A * (2 / W) * L / 2 := fun keys => by ring
    simp only [hlin]
    rw [Finset.expect_add_distrib, ← Finset.mul_expect, hcp, Finset.expect_const Finset.univ_nonempty]
    ring
  calc 𝔼 keys : Fin n → Bytes 32, 𝔼 ω₂ : ({x // O.IsPt x} → Y),
        idealDist prims O M βmin tol enc k D bmsg PS adm n keys ω₂
      ≤ 𝔼 keys : Fin n → Bytes 32, (2 * (2 * (1 - s)⁻¹ / θ * gap keys +
          √(A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2) + √(sc * Real.log (C + 1) / 2)) + K) :=
        Finset.expect_le_expect fun keys _ => hkey keys
    _ = 2 * (2 * (1 - s)⁻¹ / θ * 𝔼 keys : Fin n → Bytes 32, gap keys +
          𝔼 keys : Fin n → Bytes 32, √(A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2) +
          √(sc * Real.log (C + 1) / 2)) + K := by
        rw [Finset.expect_add_distrib, ← Finset.mul_expect, Finset.expect_add_distrib,
          Finset.expect_add_distrib, ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty,
          Finset.expect_const Finset.univ_nonempty]
    _ ≤ w1CouplingError prims βmin N n s θ C k D Lk := by
        rw [hgap]
        unfold w1CouplingError
        simp only [K]
        linarith [hsd]
end AverageBound


/-! ### Satisfiability of the hypotheses `hO` and `hMask` -/

section Satisfiable

variable {prims : Primitives p} [Fintype Y] [Nonempty Y]

/-- **The sum-type domain separation with uniform decodings is a `UniformSplit`**: the hypothesis
`hO` of the headlines holds for `sumOracles` at decodings pushing the uniform law to the uniform
law. -/
theorem uniformSplit_sumOracles {muAns : Y → Bytes 64} {chAns gAns : Y → CommitHashBytes p}
    (hmu : (uniformOfFintype Y).map muAns = uniformOfFintype (Bytes 64))
    (hch : (uniformOfFintype Y).map chAns = uniformOfFintype (CommitHashBytes p))
    (hg : (uniformOfFintype Y).map gAns = uniformOfFintype (CommitHashBytes p)) :
    (sumOracles (prims := prims) (N := N) (reps := reps) (T := T) (Msg := Msg) muAns chAns
      gAns).UniformSplit where
  muPt_injective a b h := by simpa [sumOracles] using h
  chPt_injective a b h := by simpa [sumOracles] using h
  gPt_injective a b h := by simpa [sumOracles] using h
  muPt_ne_chPt a b := by simp [sumOracles]
  muPt_ne_gPt a b := by simp [sumOracles]
  chPt_ne_gPt a b := by simp [sumOracles]
  map_muAns := hmu
  map_chAns := hch
  map_gAns := hg

variable (p) in
/-- **An oracle range with uniform decodings and a group structure**: indices of a message
representative, a commitment hash and a mask, `Fin`-coded. -/
def SatY [Nonempty (MaskBox p)] : Type :=
  Fin (Fintype.card (Bytes 64)) × Fin (Fintype.card (CommitHashBytes p)) ×
    Fin (Fintype.card (MaskBox p))

section SatY

variable [Nonempty (MaskBox p)]

instance : Fintype (SatY p) := inferInstanceAs (Fintype (Fin _ × Fin _ × Fin _))

instance : DecidableEq (SatY p) := inferInstanceAs (DecidableEq (Fin _ × Fin _ × Fin _))

instance : Nonempty (SatY p) :=
  ⟨(⟨0, Fintype.card_pos⟩, ⟨0, Fintype.card_pos⟩, ⟨0, Fintype.card_pos⟩)⟩

noncomputable instance : AddCommGroup (SatY p) :=
  haveI : NeZero (Fintype.card (Bytes 64)) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (Fintype.card (CommitHashBytes p)) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (Fintype.card (MaskBox p)) := ⟨Fintype.card_ne_zero⟩
  inferInstanceAs (AddCommGroup (Fin _ × Fin _ × Fin _))

/-- The message representative of a value of `SatY`. -/
noncomputable def satMu (y : SatY p) : Bytes 64 := (Fintype.equivFin _).symm y.1

/-- The commitment hash of a value of `SatY`. -/
noncomputable def satCh (y : SatY p) : CommitHashBytes p := (Fintype.equivFin _).symm y.2.1

/-- The mask of a value of `SatY`. -/
noncomputable def satMask (y : SatY p) : MaskBox p := (Fintype.equivFin _).symm y.2.2

omit [Nonempty (MaskBox p)] in
/-- A coordinate of a uniform triple is uniform. -/
theorem map_uniformOfFintype_triple {A B C' Z : Type*} [Fintype A] [Nonempty A] [Fintype B]
    [Nonempty B] [Fintype C'] [Nonempty C'] [Fintype Z] [Nonempty Z] (e : A ≃ Z) :
    (uniformOfFintype (A × B × C')).map (fun y => e y.1) = uniformOfFintype Z := by
  rw [show (fun y : A × B × C' => e y.1) = e ∘ Prod.fst from rfl, ← PMF.map_comp,
    map_fst_uniformOfFintype, map_uniformOfFintype_equiv]

/-- The message-representative decoding of `SatY` pushes the uniform law to the uniform law. -/
theorem map_satMu : (uniformOfFintype (SatY p)).map satMu = uniformOfFintype (Bytes 64) :=
  map_uniformOfFintype_triple (Fintype.equivFin _).symm

/-- The commitment-hash decoding of `SatY` pushes the uniform law to the uniform law. -/
theorem map_satCh : (uniformOfFintype (SatY p)).map satCh = uniformOfFintype (CommitHashBytes p) := by
  rw [show (satCh : SatY p → CommitHashBytes p) =
    (fun y => (Fintype.equivFin _).symm y.1) ∘ fun y : SatY p => (y.2.1, y.2.2, y.1) from rfl,
    ← PMF.map_comp]
  have e : (uniformOfFintype (SatY p)).map (fun y : SatY p => (y.2.1, y.2.2, y.1)) =
      uniformOfFintype _ := map_uniformOfFintype_equiv
        ⟨fun y : SatY p => (y.2.1, y.2.2, y.1), fun z => (z.2.2, z.1, z.2.1), fun _ => rfl,
          fun _ => rfl⟩
  rw [e, map_uniformOfFintype_triple]

/-- The mask decoding of `SatY` pushes the uniform law to the uniform law: the hypothesis `hMask`
of the headlines holds for `sumMask satMask`. -/
theorem map_satMask : (uniformOfFintype (SatY p)).map satMask = uniformOfFintype (MaskBox p) := by
  rw [show (satMask : SatY p → MaskBox p) =
    (fun y => (Fintype.equivFin _).symm y.1) ∘ fun y : SatY p => (y.2.2, y.1, y.2.1) from rfl,
    ← PMF.map_comp]
  have e : (uniformOfFintype (SatY p)).map (fun y : SatY p => (y.2.2, y.1, y.2.1)) =
      uniformOfFintype _ := map_uniformOfFintype_equiv
        ⟨fun y : SatY p => (y.2.2, y.1, y.2.1), fun z => (z.2.1, z.2.2, z.1), fun _ => rfl,
          fun _ => rfl⟩
  rw [e, map_uniformOfFintype_triple]

/-- **The hypothesis `hO` holds** for the sum-type domain separation at the decodings of `SatY`
(the check oracle decoded like the commitment hash). -/
theorem uniformSplit_sumOracles_satY :
    (sumOracles (prims := prims) (N := N) (reps := reps) (T := T) (Msg := Msg)
      (satMu (p := p)) satCh satCh).UniformSplit :=
  uniformSplit_sumOracles map_satMu map_satCh map_satCh

end SatY

end Satisfiable

/-! ### The keep level at the approved parameter sets -/

section KeepLevel

/-- **`Lk = β_min θ / 64` is at most one** for `β_min ≤ 1` and `θ ∈ [0, 1]`: the hypothesis
`hLk1` of the headlines. -/
theorem keepLevel_div_le_one {βmin : ℚ≥0} (hβ1 : (βmin : ℝ≥0∞) ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1 := by
  have hb0 : 0 ≤ (βmin : ℝ≥0∞).toReal := ENNReal.toReal_nonneg
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 * 1 := mul_le_mul hb1 hθ1 hθ0 zero_le_one
  linarith

/-- **The keep level at ML-DSA-44** at the defect budget `1/2` is at least `β_min θ / 64`
(`K |V| ≥ 1/16`, `one_div_sixteen_le_standinScale_mul_card_mldsa44`): the hypothesis `hLk` of
`w1Scheme44.anonAdvantage_le` holds at `Lk = β_min θ / 64`. -/
theorem div_le_keepLevel_mldsa44 (βmin : ℚ≥0) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    (βmin : ℝ≥0∞).toReal * θ / 64 ≤ keepLevel _root_.MLDSA.mldsa44 βmin (1 / 2) θ := by
  have hK := one_div_sixteen_le_standinScale_mul_card_mldsa44
  unfold keepLevel
  rw [ENNReal.toReal_mul]
  have hx := mul_le_mul_of_nonneg_right hK
    (mul_nonneg ENNReal.toReal_nonneg hθ0 : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
  nlinarith [hx]

/-- **The keep level at ML-DSA-65** at the defect budget `1/2` is at least `β_min θ / 64`. -/
theorem div_le_keepLevel_mldsa65 (βmin : ℚ≥0) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    (βmin : ℝ≥0∞).toReal * θ / 64 ≤ keepLevel _root_.MLDSA.mldsa65 βmin (1 / 2) θ := by
  have hK := one_div_sixteen_le_standinScale_mul_card_mldsa65
  unfold keepLevel
  rw [ENNReal.toReal_mul]
  have hx := mul_le_mul_of_nonneg_right hK
    (mul_nonneg ENNReal.toReal_nonneg hθ0 : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
  nlinarith [hx]

/-- **The keep level at ML-DSA-87** at the defect budget `1/2` is at least `β_min θ / 64`. -/
theorem div_le_keepLevel_mldsa87 (βmin : ℚ≥0) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    (βmin : ℝ≥0∞).toReal * θ / 64 ≤ keepLevel _root_.MLDSA.mldsa87 βmin (1 / 2) θ := by
  have hK := one_div_sixteen_le_standinScale_mul_card_mldsa87
  unfold keepLevel
  rw [ENNReal.toReal_mul]
  have hx := mul_le_mul_of_nonneg_right hK
    (mul_nonneg ENNReal.toReal_nonneg hθ0 : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
  nlinarith [hx]

end KeepLevel

end GordieHowe.Ring.MLDSAW1
