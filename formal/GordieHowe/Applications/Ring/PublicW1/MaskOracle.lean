-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.PublicValue
public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched
public import GordieHowe.Foundations.ToMathlib.PMFRejection
public import GordieHowe.Foundations.ToMathlib.PMFUniform
public import GordieHowe.Model.ROM.Lazy

@[expose] public section

/-!
# Hedged signing with a mask oracle

The step from a ring signer with ideal masks (every attempt's mask uniform and fresh) to a hedged
signer that reads its masks from a random oracle at a fresh nonce, as FIPS 204 Algorithm 7 does
(`ρ'' = H(K ‖ rnd ‖ µ)`, `y = ExpandMask(ρ'', κ)`, with `H` and ExpandMask together a random
oracle on `(rnd, point)`), against adversaries that query that oracle at most `q` times per
phase and see every other oracle whole.

- `PMF.etv`, `seqRun`, `etv_seqRun_le`, `bind_pi_seqRun`, `sum_pi_seqRun_mul`: sequential rounds,
  the hybrid over the rounds, and randomness drawn up front for each round (the signature table of
  `PubAnonAdversary`, the nonces, the masks) read only in its round.
- `PMF.firstOf`, `PMF.firstSome_bind_contWith_untilSome`, `PMF.untilSome_firstSome_bind`: bounded
  loops with given attempts, and the unbounded loop unrolled.
- `PMF.weightedAttemptMasks`, `PMF.untilSome_uniform_bind_weightedAttemptMasks`: one call of the
  base signer with `T` given masks (the first that passes), then the ring signer's coin; with
  uniform masks its unbounded loop is the ideal-mask loop.
- `swapY`, `sum_uniform_swapY`, `sum_uniform_nonceHit_le`, `sum_uniform_not_distinct_le`: the
  swap of the mask oracle's slices at the nonces drawn up front with fresh masks (an involution
  preserving the uniform law for distinct nonces), the union bound for queries hitting a drawn
  nonce, and the birthday bound.
- `sum_uniform_hedged_close`: the hedged rounds and the rounds with fresh masks, averaged over the
  mask oracle, are within `(Q k)² / |R| + (Q + 1) q Q k / |R| + 2 Q ρ^k`: draw the nonces of the
  first `k` attempts of every round up front, swap their slices with fresh masks, charge the query
  phases that hit a drawn nonce, and the rounds whose `k` attempts all reject (`ρ` bounds the
  rejection of one attempt with fresh masks).
- `MaskedSigner`, `MaskedSigner.real`, `MaskedSigner.QueryBounded`, `MaskedSigner.atMask`,
  `MaskedSigner.advantage_le_atMask`: in the game of `PubAnonAdversary`, the advantage against
  the hedged signer is at most the average over the mask oracle of the advantage of the adversary
  at that oracle against the ideal-mask signer, plus twice the error above. With
  `ρ = 1 - s̄` and `k ≈ t / s̄` the error is about `2 Q e^{-t} + (Q + 1) q Q t / (|R| s̄)`.

The adversary class is classical, with at most `q` queries to the mask oracle per choice and for
the distinguisher (`ROM.Alg`, CY24 p. 20), and the whole oracles otherwise. Superposition
queries to the mask oracle are covered by the `RingScheme` anonymity headlines
(`GordieHowe/Applications/Ring/MLDSAW1AnonQuery.lean`, `MLDSAW1AnonOracle.lean`). Deterministic
signing (a fixed nonce) is not covered: the bound charges the queries that hit a fresh nonce.
-/

open scoped NNReal ENNReal BigOperators

/-! ### The one-sided excess -/

namespace PMF

variable {α β : Type*}

/-- **The excess** `∑' a, (p a - q a)` of `p` over `q`, the total variation distance in `ℝ≥0∞`
(`PMF.tvDist_eq_toReal_tsum_tsub`). -/
noncomputable def etv (p q : PMF α) : ℝ≥0∞ := ∑' a, (p a - q a)

theorem etv_le_one (p q : PMF α) : etv p q ≤ 1 := tsum_tsub_le_one p q

theorem etv_comm (p q : PMF α) : etv p q = etv q p := tsum_tsub_comm p q

@[simp] theorem etv_self (p : PMF α) : etv p p = 0 := by simp [etv]

theorem etv_triangle (p q r : PMF α) : etv p r ≤ etv p q + etv q r := by
  unfold etv
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => tsub_le_tsub_add_tsub

/-- **Data processing** for a kernel. -/
theorem etv_bind_right_le (p q : PMF α) (k : α → PMF β) :
    etv (p.bind k) (q.bind k) ≤ etv p q := by
  unfold etv
  calc ∑' b, ((p.bind k) b - (q.bind k) b)
      ≤ ∑' b, ∑' a, (p a - q a) * k a b := by
        refine ENNReal.tsum_le_tsum fun b => tsub_le_iff_left.2 ?_
        simp only [bind_apply]
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun a => ?_
        rw [← add_mul]
        gcongr
        exact le_add_tsub
    _ = ∑' a, (p a - q a) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun a => by rw [ENNReal.tsum_mul_left, (k a).tsum_coe, mul_one]

/-- **Data processing** for a function. -/
theorem etv_map_le (p q : PMF α) (f : α → β) : etv (p.map f) (q.map f) ≤ etv p q := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact etv_bind_right_le p q _

/-- **Mixtures**: mixing two kernels by the same law costs at most the average excess. -/
theorem etv_bind_left_le (p : PMF α) (k₁ k₂ : α → PMF β) :
    etv (p.bind k₁) (p.bind k₂) ≤ ∑' a, p a * etv (k₁ a) (k₂ a) := by
  unfold etv
  calc ∑' b, ((p.bind k₁) b - (p.bind k₂) b)
      ≤ ∑' b, ∑' a, p a * (k₁ a b - k₂ a b) := by
        refine ENNReal.tsum_le_tsum fun b => tsub_le_iff_left.2 ?_
        simp only [bind_apply]
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun a => ?_
        rw [← mul_add]
        gcongr
        exact le_add_tsub
    _ = ∑' a, p a * ∑' b, (k₁ a b - k₂ a b) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun a => ENNReal.tsum_mul_left

/-- **Identical until bad**: two laws that agree off `s`. -/
theorem etv_le_of_eq_of_notMem (p q : PMF α) (s : Set α) (h : ∀ a ∉ s, p a = q a) :
    etv p q ≤ p.toOuterMeasure s := tsum_tsub_le_of_eq_of_notMem p q s h

/-- Two kernels mixed by one law differ by at most the probability that they differ. -/
theorem etv_bind_le_toOuterMeasure_ne (p : PMF α) (k₁ k₂ : α → PMF β) :
    etv (p.bind k₁) (p.bind k₂) ≤ p.toOuterMeasure {a | k₁ a ≠ k₂ a} := by
  classical
  refine (etv_bind_left_le p k₁ k₂).trans ?_
  rw [toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : k₁ a = k₂ a
  · simp [ha]
  · rw [Set.indicator_of_mem (show a ∈ {a | k₁ a ≠ k₂ a} from ha)]
    exact mul_le_of_le_one_right' (etv_le_one _ _)

/-- **Event form**: an event's probabilities differ by at most the excess. -/
theorem toOuterMeasure_le_add_etv (p q : PMF α) (s : Set α) :
    p.toOuterMeasure s ≤ q.toOuterMeasure s + etv p q :=
  toOuterMeasure_le_add_tsum_tsub p q s

/-- The excess in `ℝ` is the total variation distance. -/
theorem toReal_etv (p q : PMF α) : (etv p q).toReal = tvDist p q :=
  (tvDist_eq_toReal_tsum_tsub p q).symm

/-! ### The keep probability of a ring attempt -/

section Keep

variable {V C K : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype K] [DecidableEq K]

/-- **The keep probability of a ring attempt** is at least its level times the total ring
weight, less its deviation. -/
theorem RingPair.massAt_sub_dev_le (R : RingPair K V C) (b : Bool) (G : K × V → C) :
    (R.signer b).β * R.massAt G - R.dev b G ≤ (1 - R.attempt b G none).toReal := by
  rw [← sum_toReal_apply_some]
  unfold RingPair.massAt RingPair.dev weightedDev RingWeights.weightMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  have := neg_abs_le ((R.attempt b G (some v)).toReal -
    (R.signer b).β * ((R.wts).ringWeight (ringOf R.pt G) v : ℝ≥0∞).toReal)
  unfold RingPair.attempt at this ⊢
  linarith

variable {M : Type} [Fintype M] [Nonempty M] (R : M → RingPair K V C) {θ : ℝ}

/-- **A small family bound keeps every ring attempt**: if the family bound at `G` is below `1/2`,
every signer of every ring of the family keeps with probability at least its level times `θ`
times half the ring mass. -/
theorem keep_ge_of_familyBound_lt (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : ∀ m, 0 < (R m).wts.mass)
    {G : K × V → C} (hG : familyBound R θ G < 1 / 2) (m : M) (b : Bool) :
    ((R m).signer b).β * (θ * (R m).wts.mass) / 2 ≤ (1 - (R m).attempt b G none).toReal := by
  classical
  have hden : ∀ b, 0 < famDen R θ m b := fun b => mul_pos ((R m).signer b).hβ (mul_pos hθ0 (hμ m))
  have hdev0 : ∀ b, 0 ≤ (R m).dev b G := fun b => Finset.sum_nonneg fun v _ => abs_nonneg _
  have hfd0 : ∀ m', 0 ≤ famDev R θ m' G := fun m' => Finset.sum_nonneg fun b _ =>
    div_nonneg (Finset.sum_nonneg fun v _ => abs_nonneg _)
      (mul_pos ((R m').signer b).hβ (mul_pos hθ0 (hμ m'))).le
  have hsupD : famDev R θ m G ≤ Finset.univ.sup' Finset.univ_nonempty (fun m => famDev R θ m G) :=
    Finset.le_sup' (fun m => famDev R θ m G) (Finset.mem_univ m)
  have hsupS : famShort R θ (some m) G ≤
      Finset.univ.sup' Finset.univ_nonempty (fun o => famShort R θ o G) :=
    Finset.le_sup' (fun o => famShort R θ o G) (Finset.mem_univ (some m))
  have hS0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun o => famShort R θ o G) :=
    le_trans (le_of_eq rfl) (Finset.le_sup' (fun o => famShort R θ o G) (Finset.mem_univ none))
  have hD0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun m => famDev R θ m G) :=
    (hfd0 m).trans hsupD
  unfold familyBound at hG
  -- the deviation of signer `b`
  have hdevb : (R m).dev b G / famDen R θ m b < 1 / 2 := by
    have : (R m).dev b G / famDen R θ m b ≤ famDev R θ m G := by
      unfold famDev
      exact Finset.single_le_sum (f := fun b => (R m).dev b G / famDen R θ m b)
        (fun b _ => div_nonneg (hdev0 b) (hden b).le) (Finset.mem_univ b)
    linarith
  rw [div_lt_iff₀ (hden b)] at hdevb
  -- the total ring weight
  have hshort : famShort R θ (some m) G < 1 / 2 := by linarith
  simp only [famShort, Option.elim] at hshort
  have hmθ : 0 < (1 - θ) * (R m).wts.mass := mul_pos (by linarith) (hμ m)
  rw [div_lt_iff₀ hmθ] at hshort
  have hmass : θ * (R m).wts.mass ≤ (R m).massAt G := by nlinarith [hμ m]
  have hkeep := RingPair.massAt_sub_dev_le (R m) b G
  have hβ := ((R m).signer b).hβ
  unfold famDen at hdevb
  nlinarith

end Keep

end PMF

/-! ### Rejection loops with given attempts -/

namespace PMF

section Loops

variable {α : Type*} [Fintype α]

/-- **The first acceptance among `k` independent attempts** of laws `As t` (attempt `t` drawn
from `As t`), or `none` if all reject. -/
noncomputable def firstOf {k : ℕ} (As : Fin k → PMF (Option α)) : PMF (Option α) :=
  (pi As).map fun os => (List.finRange k).findSome? os

/-- With one law for every attempt, the first acceptance is the bounded loop. -/
theorem firstOf_const (A : PMF (Option α)) (k : ℕ) : firstOf (fun _ : Fin k => A) = firstSome A k :=
  (firstSome_eq_map_pi A k).symm

/-- All `k` attempts reject with the product of their rejection probabilities. -/
theorem firstOf_apply_none {k : ℕ} (As : Fin k → PMF (Option α)) :
    firstOf As none = ∏ t, As t none := by
  classical
  rw [firstOf, map_apply, tsum_fintype, Finset.sum_eq_single (fun _ => none)]
  · rw [if_pos (List.findSome?_eq_none_iff.2 fun _ _ => rfl).symm, pi_apply]
  · intro os _ hos
    rw [if_neg]
    intro h
    refine hos (funext fun t => ?_)
    have := (List.findSome?_eq_none_iff.1 h.symm) t (List.mem_finRange t)
    exact this
  · simp

/-- **Independent mixtures**: the product of mixtures is the mixture of products. -/
theorem pi_bind_eq {k : ℕ} {β γ : Fin k → Type*} [∀ t, Fintype (β t)] [∀ t, Fintype (γ t)]
    (μ : ∀ t, PMF (β t)) (g : ∀ t, β t → PMF (γ t)) :
    (pi fun t => (μ t).bind (g t)) = (pi μ).bind fun rv => pi fun t => g t (rv t) := by
  ext f
  rw [pi_apply, bind_apply, tsum_fintype]
  simp only [bind_apply, tsum_fintype, pi_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun rv _ => Finset.prod_mul_distrib

/-- **The continuation of a loop after a rejection**: `none` continues with `F`, an accepted
value is output. -/
noncomputable def contWith (F : PMF (Option α)) : Option α → PMF (Option α) :=
  fun o => o.elim F fun a => PMF.pure (some a)

/-- **The unbounded loop unrolled**: `k` attempts, then the unbounded loop if all reject. -/
theorem firstSome_bind_contWith_untilSome (A : PMF (Option α)) (k : ℕ) :
    (firstSome A k).bind (contWith (untilSome A)) = untilSome A := by
  classical
  set r := A none
  have happly : ∀ o, ((firstSome A k).bind (contWith (untilSome A))) o =
      r ^ k * untilSome A o + ∑ a, firstSome A k (some a) * (PMF.pure (some a) : PMF (Option α)) o := by
    intro o
    rw [bind_apply, tsum_fintype, Fintype.sum_option, firstSome_apply_none]
    rfl
  by_cases h : r = 1
  · have h0 : ∀ a, A (some a) = 0 := fun a => by
      have hs := sum_apply_some A
      rw [show A none = 1 from h, tsub_self] at hs
      exact (Finset.sum_eq_zero_iff.1 hs) a (Finset.mem_univ _)
    ext o
    rw [happly, h, one_pow, one_mul]
    simp [firstSome_apply_some, h0]
  · refine eq_of_apply_eq_mul (F := fun o => o.elim 0 fun a => A (some a))
      (a := r ^ k * (1 - r)⁻¹ + ∑ i ∈ Finset.range k, r ^ i) (b := (1 - r)⁻¹) (fun o => ?_)
      (fun o => ?_)
    · rw [happly]
      cases o with
      | none => simp [untilSome_apply_none h]
      | some x =>
        rw [untilSome_apply_some, Finset.sum_eq_single x (fun b _ hb => by
          rw [pure_apply, if_neg (fun e => hb (Option.some_injective _ e).symm), mul_zero]) (by simp),
          pure_apply_self, mul_one, firstSome_apply_some]
        simp only [Option.elim]
        rw [div_eq_mul_inv]
        ring
    · cases o with
      | none => simp [untilSome_apply_none h]
      | some x =>
        rw [untilSome_apply_some, div_eq_mul_inv, mul_comm]
        rfl

/-- **Attempts on independent uniform inputs** are the bounded loop of the mixed attempt. -/
theorem uniform_bind_firstOf {β : Type*} [Fintype β] [Nonempty β] [DecidableEq β] (k : ℕ)
    (g : β → PMF (Option α)) :
    (uniformOfFintype (Fin k → β)).bind (fun v => firstOf fun t => g (v t)) =
      firstSome ((uniformOfFintype β).bind g) k := by
  rw [← firstOf_const]
  unfold firstOf
  rw [← map_bind, pi_bind_eq, pi_uniformOfFintype]

/-- **Proportional accepted masses give the same unbounded loop.** -/
theorem untilSome_eq_of_apply_some_eq_mul {A B : PMF (Option α)} {G : ℝ≥0∞} (hG0 : G ≠ 0)
    (hGt : G ≠ ⊤) (h : ∀ x, B (some x) = G * A (some x)) : untilSome B = untilSome A := by
  have hsum : 1 - B none = G * (1 - A none) := by
    rw [← sum_apply_some, ← sum_apply_some, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => h x
  by_cases hA : A none = 1
  · have hB : B none = 1 := by
      have : 1 - B none = 0 := by rw [hsum, hA, tsub_self, mul_zero]
      exact le_antisymm (B.coe_le_one none) (tsub_eq_zero_iff_le.1 this)
    rw [untilSome_of_apply_none_eq_one hA, untilSome_of_apply_none_eq_one hB]
  · have hB : B none ≠ 1 := fun hB => by
      have h0 : G * (1 - A none) = 0 := by rw [← hsum, hB, tsub_self]
      rcases mul_eq_zero.1 h0 with h1 | h1
      · exact hG0 h1
      · exact hA (le_antisymm (A.coe_le_one none) (tsub_eq_zero_iff_le.1 h1))
    ext o
    cases o with
    | none => rw [untilSome_apply_none hA, untilSome_apply_none hB]
    | some x =>
      rw [untilSome_apply_some, untilSome_apply_some, h, hsum, ENNReal.mul_div_mul_left _ _ hG0 hGt]

/-- **A bounded first loop, then a continuation on the accepted value**, has the unbounded loop
of one attempt followed by the continuation: the bounded loop multiplies every accepted mass by
the same factor. -/
theorem untilSome_firstSome_bind {β : Type*} [Fintype β] (A : PMF (Option β))
    (g : β → PMF (Option α)) {T : ℕ} (hT : 0 < T) :
    untilSome ((firstSome A T).bind fun o => o.elim (PMF.pure none) g) =
      untilSome (A.bind fun o => o.elim (PMF.pure none) g) := by
  classical
  set G := ∑ i ∈ Finset.range T, A none ^ i
  refine untilSome_eq_of_apply_some_eq_mul (G := G) ?_ ?_ fun x => ?_
  · refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
    calc (1 : ℝ≥0∞) = A none ^ 0 := (pow_zero _).symm
      _ ≤ G := Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_range.2 hT)
  · exact ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top (A.apply_ne_top none)
  · rw [bind_apply, bind_apply, tsum_fintype, tsum_fintype, Fintype.sum_option, Fintype.sum_option]
    simp only [Option.elim, PMF.pure_apply, reduceCtorEq, if_false, mul_zero, zero_add,
      firstSome_apply_some, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [← Finset.mul_sum]; ring

/-- The unbounded loop of an attempt that always accepts `a` outputs `a`. -/
theorem untilSome_pure_some (a : α) : untilSome (PMF.pure (some a)) = PMF.pure (some a) := by
  classical
  have h : (PMF.pure (some a) : PMF (Option α)) none ≠ 1 := by simp
  ext o
  cases o with
  | none => rw [untilSome_apply_none h]; simp
  | some x => rw [untilSome_apply_some]; simp [PMF.pure_apply]

/-- **A coordinate of a product law has the coordinate's law.** -/
theorem pi_map_eval {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {δ : ι' → Type*}
    [∀ i, Fintype (δ i)] [∀ i, DecidableEq (δ i)] (ν : ∀ i, PMF (δ i)) (j : ι') :
    (pi ν).map (fun T => T j) = ν j := by
  ext x
  simp only [map_apply, tsum_fintype]
  have := sum_pi_mul_apply_coord ν j fun b => if x = b then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
  rw [← this]
  exact Finset.sum_congr rfl fun T _ => by split_ifs <;> simp

/-- **One point of the masks of a uniform function on pairs**, for every first coordinate, is a
uniform function of the first coordinate. -/
theorem uniform_map_slice {ι' κ' M : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ']
    [DecidableEq κ'] [Fintype M] [Nonempty M] [DecidableEq M] (x : κ') :
    (uniformOfFintype (ι' × κ' → M)).map (fun Z t => Z (t, x)) = uniformOfFintype (ι' → M) := by
  have hc : (uniformOfFintype (ι' × κ' → M)).map Function.curry = uniformOfFintype (ι' → κ' → M) :=
    map_uniformOfFintype_equiv (Equiv.curry ι' κ' M)
  calc (uniformOfFintype (ι' × κ' → M)).map (fun Z t => Z (t, x))
      = ((uniformOfFintype (ι' × κ' → M)).map Function.curry).map (fun F t => F t x) := by
        rw [map_comp]; rfl
    _ = (pi fun _ : ι' => uniformOfFintype (κ' → M)).map (fun F t => F t x) := by
        rw [hc, pi_uniformOfFintype]
    _ = pi fun _ : ι' => (uniformOfFintype (κ' → M)).map fun f => f x :=
        pi_map (fun _ => uniformOfFintype (κ' → M)) fun _ f => f x
    _ = pi fun _ : ι' => uniformOfFintype M := by
        congr 1
        funext t
        rw [← pi_uniformOfFintype, pi_map_eval]
    _ = uniformOfFintype (ι' → M) := pi_uniformOfFintype

end Loops

/-! ### Weighted ring attempts with given masks -/

section Masks

variable {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype C]
  [DecidableEq C] (s : RingWeights N V C) (i : N) {Y : Type*} [Fintype Y] (w1 : Y → V)
  (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1) {S : Type*} [Fintype S]
  [DecidableEq S] (out : Y → C → S) (H : N × V → C)

/-- **The acceptance test of one mask**: the mask if the base signer's checks pass at its
commitment hash, `none` otherwise. -/
noncomputable def acceptAt (y : Y) : PMF (Option Y) :=
  if acc y (H (i, w1 y)) = true then PMF.pure (some y) else PMF.pure none

/-- **The ring signer's coin on an accepted mask**: keep its commitment with the flattening
weight, with the signer's output. -/
noncomputable def keepAt (y : Y) : PMF (Option (V × S)) :=
  (keepOrReject (w1 y) (κ (w1 y, H (i, w1 y)) * s.otherWeight i H (w1 y))
    (keepWeight_le_one s i κ hκ H (w1 y))).map (Option.map fun v => (v, out y (H (i, w1 y))))

/-- **One call of the base signer with `T` given masks, then the ring signer's coin**: the
first mask that passes the base signer's checks, kept with the flattening weight; `none` if no
mask passes or the coin rejects. -/
noncomputable def weightedAttemptMasks {T : ℕ} (ys : Fin T → Y) : PMF (Option (V × S)) :=
  (firstOf fun t => acceptAt i w1 acc H (ys t)).bind fun o =>
    o.elim (PMF.pure none) (keepAt s i w1 κ hκ out H)

omit [Fintype S] [DecidableEq S] in
/-- The weighted attempt is one acceptance test followed by the coin. -/
theorem weightedAttemptWith_eq_bind (P : PMF Y) :
    weightedAttemptWith s i P w1 acc κ hκ out H =
      (P.bind (acceptAt i w1 acc H)).bind fun o => o.elim (PMF.pure none) (keepAt s i w1 κ hκ out H) := by
  rw [PMF.bind_bind]
  unfold weightedAttemptWith
  congr 1
  funext y
  unfold acceptAt
  split_ifs <;> rw [PMF.pure_bind] <;> rfl

/-- **`T` uniform masks per call give the weighted attempt's unbounded loop**: the bounded inner
loop multiplies every kept mass by one factor. -/
theorem untilSome_uniform_bind_weightedAttemptMasks [Nonempty Y] [DecidableEq Y] {T : ℕ}
    (hT : 0 < T) :
    untilSome ((uniformOfFintype (Fin T → Y)).bind (weightedAttemptMasks s i w1 acc κ hκ out H)) =
      untilSome (weightedAttemptWith s i (uniformOfFintype Y) w1 acc κ hκ out H) := by
  unfold weightedAttemptMasks
  rw [← PMF.bind_bind, uniform_bind_firstOf, weightedAttemptWith_eq_bind]
  exact untilSome_firstSome_bind _ _ hT

/-- **With `T ≥ 1` masks per call, a call rejects at most as often as one attempt.** -/
theorem uniform_bind_weightedAttemptMasks_none_le [Nonempty Y] [DecidableEq Y] {T : ℕ}
    (hT : 0 < T) :
    (uniformOfFintype (Fin T → Y)).bind (weightedAttemptMasks s i w1 acc κ hκ out H) none ≤
      weightedAttemptWith s i (uniformOfFintype Y) w1 acc κ hκ out H none := by
  classical
  unfold weightedAttemptMasks
  rw [← PMF.bind_bind, uniform_bind_firstOf, weightedAttemptWith_eq_bind]
  set A := (uniformOfFintype Y).bind (acceptAt i w1 acc H)
  set g := keepAt s i w1 κ hκ out H
  set G := ∑ j ∈ Finset.range T, A none ^ j
  have hG : 1 ≤ G := by
    calc (1 : ℝ≥0∞) = A none ^ 0 := (pow_zero _).symm
      _ ≤ G := Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_range.2 hT)
  have hsome : ∀ x, ((firstSome A T).bind fun o => o.elim (PMF.pure none) g) (some x) =
      G * (A.bind fun o => o.elim (PMF.pure none) g) (some x) := fun x => by
    rw [bind_apply, bind_apply, tsum_fintype, tsum_fintype, Fintype.sum_option, Fintype.sum_option]
    simp only [Option.elim, PMF.pure_apply, reduceCtorEq, if_false, mul_zero, zero_add,
      firstSome_apply_some, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [← Finset.mul_sum]; ring
  have h1 : 1 - ((firstSome A T).bind fun o => o.elim (PMF.pure none) g) none =
      G * (1 - (A.bind fun o => o.elim (PMF.pure none) g) none) := by
    rw [← sum_apply_some, ← sum_apply_some, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => hsome x
  have h2 : 1 - (A.bind fun o => o.elim (PMF.pure none) g) none ≤
      1 - ((firstSome A T).bind fun o => o.elim (PMF.pure none) g) none := by
    rw [h1]
    exact le_mul_of_one_le_left zero_le hG
  exact (ENNReal.sub_le_sub_iff_left (PMF.coe_le_one _ _) ENNReal.one_ne_top).1 h2

end Masks

end PMF

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM PMF
open scoped NNReal ENNReal BigOperators



/-! ### Sequential rounds -/

section SeqRun

variable {Ω Pub Pf : Type} [Fintype Ω] [Nonempty Ω] {Q : ℕ}

/-- **The laws of the rounds**: in round `j`, from the oracle and the history, the law of the
round's output (`none` for `⊥`). -/
abbrev StepLaws (Ω Pub Pf : Type) (Q : ℕ) : Type :=
  (j : Fin Q) → Ω × PubHist Pub Pf j → PMF (Option (Pub × Pf))

/-- **The rounds with step laws `f`**: the oracle uniform, then round `j` drawn from `f j`
and appended to the history. -/
noncomputable def seqRun (f : StepLaws Ω Pub Pf Q) : (j : ℕ) → j ≤ Q → PMF (Ω × PubHist Pub Pf j)
  | 0, _ => (PMF.uniformOfFintype Ω).map fun h => (h, Fin.elim0)
  | j + 1, hj => (seqRun f j (by omega)).bind fun s =>
      (f ⟨j, by omega⟩ s).map fun o => (s.1, Fin.snoc (α := fun _ => Option (Pub × Pf)) s.2 o)

/-- Step laws that agree before round `j` give the same rounds up to `j`. -/
theorem seqRun_congr {f g : StepLaws Ω Pub Pf Q} :
    ∀ j (hj : j ≤ Q), (∀ i : Fin Q, i.1 < j → f i = g i) → seqRun f j hj = seqRun g j hj
  | 0, _, _ => rfl
  | j + 1, hj, h => by
    rw [seqRun, seqRun, seqRun_congr j (by omega) fun i hi => h i (by omega),
      h ⟨j, by omega⟩ (by simp)]

/-- **The rounds of a selector are sequential rounds.** -/
theorem pubRun_eq_seqRun {X W : Type} (law : Ω → X → W → PMF Pf) (pubOf : X → Pub)
    (sel : Selector Ω X W Pub Pf Q) :
    ∀ j (hj : j ≤ Q), pubRun law pubOf sel j hj =
      seqRun (fun i s => roundLaw law pubOf s.1 (sel i s.1 s.2)) j hj
  | 0, _ => rfl
  | j + 1, hj => by
    rw [pubRun, seqRun, pubRun_eq_seqRun law pubOf sel j]
    rfl

/-- **The hybrid over the rounds**: two families of step laws give rounds whose excess is at most
the sum over the rounds of the average excess of their step laws, averaged over the rounds of
the second family. -/
theorem etv_seqRun_le (f g : StepLaws Ω Pub Pf Q) :
    ∀ j (hj : j ≤ Q), PMF.etv (seqRun f j hj) (seqRun g j hj) ≤
      ∑ i : Fin j, ∑' s, seqRun g i (by omega) s *
        PMF.etv (f (Fin.castLE hj i) s) (g (Fin.castLE hj i) s)
  | 0, _ => by simp [seqRun]
  | j + 1, hj => by
    rw [Fin.sum_univ_castSucc]
    have hih := etv_seqRun_le f g j (by omega)
    rw [seqRun, seqRun]
    refine (PMF.etv_triangle _ ((seqRun g j (by omega)).bind fun s =>
      (f ⟨j, by omega⟩ s).map fun o => (s.1, Fin.snoc (α := fun _ => Option (Pub × Pf)) s.2 o))
      _).trans ?_
    refine add_le_add ((PMF.etv_bind_right_le _ _ _).trans hih) ?_
    refine (PMF.etv_bind_left_le _ _ _).trans (ENNReal.tsum_le_tsum fun s => ?_)
    exact mul_le_mul_right (PMF.etv_map_le _ _ _) _

/-- **Resampling one coordinate of a product law**, as laws: if `G T` does not depend on
coordinate `j` of `T`, binding `G T (T j)` over `T ← pi ν` is binding the `ν_j`-mixture of
`G T`. -/
theorem _root_.PMF.pi_bind_coord {ι : Type*} [Fintype ι] [DecidableEq ι] {δ : ι → Type*}
    [∀ i, Fintype (δ i)] [∀ i, DecidableEq (δ i)] {γ : Type*} (ν : ∀ i, PMF (δ i)) (j : ι)
    (G : (∀ i, δ i) → δ j → PMF γ) (hG : ∀ T b, G (Function.update T j b) = G T) :
    (PMF.pi ν).bind (fun T => G T (T j)) = (PMF.pi ν).bind fun T => (ν j).bind (G T) := by
  ext x
  simp only [PMF.bind_apply, tsum_fintype]
  exact PMF.sum_pi_mul_apply_eq ν j (fun T b => G T b x) fun T b => by rw [hG]

/-- **Randomness drawn up front for each round, used only in its round**, is the same as drawn
in the round: with `ρ ← pi μ` and round `i` reading only `ρ i`, the rounds have the law of the
rounds whose step law in round `i` mixes over `ρ i ← μ i`. -/
theorem bind_pi_seqRun {Ρ : Fin Q → Type} [∀ i, Fintype (Ρ i)] [∀ i, DecidableEq (Ρ i)]
    (μ : ∀ i, PMF (Ρ i)) (f : (i : Fin Q) → Ρ i → Ω × PubHist Pub Pf i → PMF (Option (Pub × Pf))) :
    ∀ j (hj : j ≤ Q), (PMF.pi μ).bind (fun ρ => seqRun (fun i s => f i (ρ i) s) j hj) =
      seqRun (fun i s => (μ i).bind fun r => f i r s) j hj
  | 0, _ => by simp [seqRun]
  | j + 1, hj => by
    simp only [seqRun]
    have hK := PMF.pi_bind_coord μ (⟨j, by omega⟩ : Fin Q)
      (fun ρ r => (seqRun (fun i s => f i (ρ i) s) j (by omega)).bind fun s =>
        (f ⟨j, by omega⟩ r s).map fun o => (s.1, Fin.snoc (α := fun _ => Option (Pub × Pf)) s.2 o))
      fun T b => by
        have hr : seqRun (fun i s => f i (Function.update T ⟨j, by omega⟩ b i) s) j (by omega) =
            seqRun (fun i s => f i (T i) s) j (by omega) :=
          seqRun_congr j (by omega) fun i hi => by
            funext s
            rw [Function.update_of_ne (fun h => by rw [h] at hi; exact lt_irrefl _ hi)]
        funext r
        rw [hr]
    rw [hK]
    have hc : ∀ ρ : (∀ i, Ρ i), ((μ ⟨j, by omega⟩).bind fun r =>
        (seqRun (fun i s => f i (ρ i) s) j (by omega)).bind fun s =>
          (f ⟨j, by omega⟩ r s).map fun o =>
            (s.1, Fin.snoc (α := fun _ => Option (Pub × Pf)) s.2 o)) =
        (seqRun (fun i s => f i (ρ i) s) j (by omega)).bind fun s =>
          ((μ ⟨j, by omega⟩).bind fun r => f ⟨j, by omega⟩ r s).map fun o =>
            (s.1, Fin.snoc (α := fun _ => Option (Pub × Pf)) s.2 o) := fun ρ => by
      rw [PMF.bind_comm]
      congr 1
      funext s
      rw [PMF.map_bind]
    simp_rw [hc]
    rw [← PMF.bind_bind, bind_pi_seqRun μ f j (by omega)]

/-- **The rounds up to `j`, averaged with a function of the round-`j` randomness**: with `ρ ← pi μ`
drawn up front and round `i` reading only `ρ i`, the average over `ρ` and the rounds up to `j`
of `φ (ρ j) s` is the average over the rounds with the randomness drawn in the rounds of the
`μ j`-average of `φ`. The rounds before `j` do not read `ρ j`. -/
theorem sum_pi_seqRun_mul {Ρ : Fin Q → Type} [∀ i, Fintype (Ρ i)] [∀ i, DecidableEq (Ρ i)]
    (μ : ∀ i, PMF (Ρ i)) (f : (i : Fin Q) → Ρ i → Ω × PubHist Pub Pf i → PMF (Option (Pub × Pf)))
    (j : Fin Q) (φ : Ρ j → Ω × PubHist Pub Pf j → ℝ≥0∞) :
    ∑ ρ, PMF.pi μ ρ * ∑' s, seqRun (fun i s => f i (ρ i) s) j j.2.le s * φ (ρ j) s =
      ∑' s, seqRun (fun i s => (μ i).bind fun r => f i r s) j j.2.le s *
        ∑ r, μ j r * φ r s := by
  have hG := PMF.sum_pi_mul_apply_eq μ j
    (fun ρ r => ∑' s, seqRun (fun i s => f i (ρ i) s) j j.2.le s * φ r s) fun T b => by
      funext r
      rw [seqRun_congr j j.2.le fun i hi => by
        funext s
        rw [Function.update_of_ne (fun h => by rw [h] at hi; exact lt_irrefl _ hi)]]
  rw [hG]
  have hrun := bind_pi_seqRun μ f j j.2.le
  calc ∑ ρ, PMF.pi μ ρ * ∑ r, μ j r * ∑' s, seqRun (fun i s => f i (ρ i) s) j j.2.le s * φ r s
      = ∑' s, ∑ r, μ j r * ((∑ ρ, PMF.pi μ ρ * seqRun (fun i s => f i (ρ i) s) j j.2.le s) *
          φ r s) := by
        simp_rw [Finset.mul_sum, ← ENNReal.tsum_mul_left]
        rw [Finset.sum_comm, Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine Finset.sum_congr rfl fun ρ _ => tsum_congr fun s => ?_
        ring
    _ = _ := by
        refine tsum_congr fun s => ?_
        rw [← hrun, PMF.bind_apply, tsum_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring

end SeqRun

/-! ### Masks read from an oracle at a fresh nonce -/

section Core

variable {Ω Pub Pf Ch α Rnd Pt Mask : Type} [Fintype Ω] [Nonempty Ω] [Fintype α] [DecidableEq α]
  [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Pt] [DecidableEq Pt]
  [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] {Q : ℕ}

/-- **The step laws of a choice function and signature laws**: round `j` signs the chosen
challenge `cf j s` with the law `sig j c`, then the round's output is `rnd j s c x` of the
signature `x`. -/
noncomputable def chooseSteps
    (rnd : (j : Fin Q) → Ω × PubHist Pub Pf j → Ch → α → PMF (Option (Pub × Pf)))
    (cf : (j : Fin Q) → Ω × PubHist Pub Pf j → Ch) (sig : (j : Fin Q) → Ch → PMF α) :
    StepLaws Ω Pub Pf Q :=
  fun j s => (sig j (cf j s)).bind (rnd j s (cf j s))

/-- **The slice of the mask oracle at a nonce `r`**: the masks of every point at nonce `r`. -/
def maskSlice (Y : Rnd × Pt → Mask) (r : Rnd) : Pt → Mask := fun x => Y (r, x)

variable (att : Ch → (Pt → Mask) → PMF (Option α)) (dflt : α)

/-- **One hedged attempt at the mask oracle `Y`**: a uniform nonce `r`, then the attempt with the
masks of the slice at `r`. -/
noncomputable def realAtt (Y : Rnd × Pt → Mask) (c : Ch) : PMF (Option α) :=
  (PMF.uniformOfFintype Rnd).bind fun r => att c (maskSlice Y r)

/-- **One attempt with fresh masks**: the attempt with a uniform slice. -/
noncomputable def meanAtt (c : Ch) : PMF (Option α) :=
  (PMF.uniformOfFintype (Pt → Mask)).bind (att c)

/-- **A signature from a first loop `X` and a continuation `F`**: `X`, then `F` if `X` rejects,
then the default `dflt` for a loop that never accepts. -/
noncomputable def finish (X F : PMF (Option α)) : PMF α :=
  (X.bind (PMF.contWith F)).map fun o => o.getD dflt

/-- The signature law of the hedged signer at the mask oracle `Y`. -/
noncomputable def sigReal (Y : Rnd × Pt → Mask) : (j : Fin Q) → Ch → PMF α :=
  fun _ c => (untilSome (realAtt att Y c)).map fun o => o.getD dflt

/-- The signature law of the signer with fresh masks. -/
noncomputable def sigIdeal : (j : Fin Q) → Ch → PMF α :=
  fun _ c => (untilSome (meanAtt att c)).map fun o => o.getD dflt

/-- The signature with the nonces `rv` of its first `k` attempts given. -/
noncomputable def sigNonces {k : ℕ} (Y : Rnd × Pt → Mask) (rv : Fin k → Rnd) (c : Ch) : PMF α :=
  finish dflt (PMF.firstOf fun t => att c (maskSlice Y (rv t))) (untilSome (realAtt att Y c))

/-- The signature with the masks `zv` of its first `k` attempts given. -/
noncomputable def sigMasks {k : ℕ} (Y : Rnd × Pt → Mask) (zv : Fin k → Pt → Mask) (c : Ch) :
    PMF α :=
  finish dflt (PMF.firstOf fun t => att c (zv t)) (untilSome (realAtt att Y c))

/-- The signature with `k` attempts with fresh masks, then the hedged loop. -/
noncomputable def sigFresh (k : ℕ) (Y : Rnd × Pt → Mask) (c : Ch) : PMF α :=
  finish dflt (firstSome (meanAtt att c) k) (untilSome (realAtt att Y c))

omit [DecidableEq α] [DecidableEq Rnd] [DecidableEq Pt] [DecidableEq Mask] in
/-- **Attempts with uniform inputs drawn up front** are the bounded loop of the mixed attempt. -/
theorem uniform_bind_finish {β : Type} [Fintype β] [Nonempty β] [DecidableEq β] (k : ℕ)
    (g : β → PMF (Option α)) (F : PMF (Option α)) :
    (PMF.uniformOfFintype (Fin k → β)).bind (fun v => finish dflt (PMF.firstOf fun t => g (v t)) F) =
      finish dflt (firstSome ((PMF.uniformOfFintype β).bind g) k) F := by
  have h1 : (PMF.uniformOfFintype (Fin k → β)).bind (fun v => PMF.firstOf fun t => g (v t)) =
      firstSome ((PMF.uniformOfFintype β).bind g) k := by
    rw [← PMF.firstOf_const]
    unfold PMF.firstOf
    rw [← PMF.map_bind, PMF.pi_bind_eq, PMF.pi_uniformOfFintype]
  unfold finish
  rw [← h1, PMF.bind_bind, PMF.map_bind]

omit [DecidableEq Pt] [DecidableEq Mask] in
/-- **The nonces of the first attempts, averaged, give the hedged signer.** -/
theorem uniform_bind_sigNonces (k : ℕ) (Y : Rnd × Pt → Mask) (c : Ch) :
    (PMF.uniformOfFintype (Fin k → Rnd)).bind (fun rv => sigNonces att dflt Y rv c) =
      (untilSome (realAtt att Y c)).map fun o => o.getD dflt := by
  unfold sigNonces
  rw [uniform_bind_finish dflt k (fun r => att c (maskSlice Y r)), finish,
    show (PMF.uniformOfFintype Rnd).bind (fun r => att c (maskSlice Y r)) = realAtt att Y c from rfl,
    PMF.firstSome_bind_contWith_untilSome]

omit [DecidableEq Rnd] in
/-- **The masks of the first attempts, averaged, give `k` attempts with fresh masks.** -/
theorem uniform_bind_sigMasks (k : ℕ) (Y : Rnd × Pt → Mask) (c : Ch) :
    (PMF.uniformOfFintype (Fin k → Pt → Mask)).bind (fun zv => sigMasks att dflt Y zv c) =
      sigFresh att dflt k Y c :=
  uniform_bind_finish dflt k (att c) _

omit [DecidableEq α] in
/-- **Two continuations after one first loop** give signatures within the loop's rejection
probability. -/
theorem etv_finish_le (X F₁ F₂ : PMF (Option α)) :
    PMF.etv (finish dflt X F₁) (finish dflt X F₂) ≤ X none := by
  unfold finish
  refine (PMF.etv_map_le _ _ _).trans ((PMF.etv_bind_le_toOuterMeasure_ne _ _ _).trans ?_)
  calc X.toOuterMeasure {o | PMF.contWith F₁ o ≠ PMF.contWith F₂ o}
      ≤ X.toOuterMeasure {none} := PMF.toOuterMeasure_mono _ fun o ho => by
        cases o with
        | none => rfl
        | some a => exact absurd rfl ho.1
    _ = X none := PMF.toOuterMeasure_apply_singleton _ _

omit [DecidableEq Rnd] in
/-- **The hedged signer with fresh masks is the signer with fresh masks**, up to the rejection of
`k` attempts. -/
theorem etv_sigFresh_le (k : ℕ) (Y : Rnd × Pt → Mask) (c : Ch) :
    PMF.etv (sigFresh att dflt k Y c) ((untilSome (meanAtt att c)).map fun o => o.getD dflt) ≤
      meanAtt att c none ^ k := by
  have h := etv_finish_le dflt (firstSome (meanAtt att c) k) (untilSome (realAtt att Y c))
    (untilSome (meanAtt att c))
  unfold finish at h
  rw [PMF.firstSome_bind_contWith_untilSome, firstSome_apply_none] at h
  exact h

end Core

/-! ### Nonces drawn up front, and the swap of their slices -/

section Swap

variable {Rnd Pt Mask : Type} [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Pt]
  [DecidableEq Pt] [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] {Q k : ℕ}

/-- **The nonce `r` is one of the drawn nonces** `ρ j t`. -/
def NonceHit (ρ : Fin Q → Fin k → Rnd) (r : Rnd) : Prop := ∃ jt : Fin Q × Fin k, ρ jt.1 jt.2 = r

/-- **The drawn nonces are distinct.** -/
def NoncesDistinct (ρ : Fin Q → Fin k → Rnd) : Prop :=
  Function.Injective fun jt : Fin Q × Fin k => ρ jt.1 jt.2

open Classical in
/-- **The mask oracle with the slices at the drawn nonces replaced** by the masks `Z`. -/
noncomputable def swapY (ρ : Fin Q → Fin k → Rnd) (Y : Rnd × Pt → Mask)
    (Z : Fin Q → Fin k → Pt → Mask) : Rnd × Pt → Mask :=
  fun p => if h : NonceHit ρ p.1 then Z h.choose.1 h.choose.2 p.2 else Y p

/-- **The slices of the mask oracle at the drawn nonces.** -/
def swapZ (ρ : Fin Q → Fin k → Rnd) (Y : Rnd × Pt → Mask) : Fin Q → Fin k → Pt → Mask :=
  fun j t x => Y (ρ j t, x)

/-- **The swap**: the slices at the drawn nonces exchanged with the masks `Z`. -/
noncomputable def swapPair (ρ : Fin Q → Fin k → Rnd)
    (YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask)) :
    (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask) :=
  (swapY ρ YZ.1 YZ.2, swapZ ρ YZ.1)

omit [Fintype Rnd] [Nonempty Rnd] [Fintype Pt] [DecidableEq Pt] [Fintype Mask] [Nonempty Mask]
  [DecidableEq Mask] in
theorem swapY_of_not {ρ : Fin Q → Fin k → Rnd} {Y : Rnd × Pt → Mask}
    {Z : Fin Q → Fin k → Pt → Mask} {p : Rnd × Pt} (h : ¬ NonceHit ρ p.1) : swapY ρ Y Z p = Y p := by
  unfold swapY; rw [dif_neg h]

omit [Fintype Rnd] [Nonempty Rnd] [Fintype Pt] [DecidableEq Pt] [Fintype Mask] [Nonempty Mask]
  [DecidableEq Mask] in
/-- With distinct nonces, the slice of the swapped oracle at a drawn nonce is the given mask
slice. -/
theorem maskSlice_swapY {ρ : Fin Q → Fin k → Rnd} (hρ : NoncesDistinct ρ) (Y : Rnd × Pt → Mask)
    (Z : Fin Q → Fin k → Pt → Mask) (j : Fin Q) (t : Fin k) :
    maskSlice (swapY ρ Y Z) (ρ j t) = Z j t := by
  funext x
  have h : NonceHit ρ (ρ j t) := ⟨(j, t), rfl⟩
  simp only [maskSlice, swapY, dif_pos h]
  have := @hρ h.choose (j, t) h.choose_spec
  rw [this]

omit [Fintype Rnd] [Nonempty Rnd] [Fintype Pt] [DecidableEq Pt] [Fintype Mask] [Nonempty Mask]
  [DecidableEq Mask] in
theorem swapPair_involutive {ρ : Fin Q → Fin k → Rnd} (hρ : NoncesDistinct ρ) :
    Function.Involutive (swapPair (Pt := Pt) (Mask := Mask) ρ) := by
  rintro ⟨Y, Z⟩
  refine Prod.ext (funext fun p => ?_) (funext fun j => funext fun t => funext fun x => ?_)
  · by_cases h : NonceHit ρ p.1
    · obtain ⟨⟨j, t⟩, hjt⟩ := h
      obtain ⟨r, x⟩ := p
      simp only at hjt
      subst hjt
      have := congrFun (maskSlice_swapY hρ (swapY ρ Y Z) (swapZ ρ Y) j t) x
      simp only [maskSlice] at this
      simp only [swapPair, this, swapZ]
    · simp only [swapPair]
      rw [swapY_of_not h, swapY_of_not h]
  · simp only [swapPair, swapZ]
    exact congrFun (maskSlice_swapY hρ Y Z j t) x

/-- **The swap preserves the uniform law**: averages of a function of the swapped oracle are
averages of the oracle, for distinct nonces. -/
theorem sum_uniform_swapY {ρ : Fin Q → Fin k → Rnd} (hρ : NoncesDistinct ρ)
    (g : (Rnd × Pt → Mask) → ℝ≥0∞) :
    ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask),
        PMF.uniformOfFintype _ YZ * g (swapY ρ YZ.1 YZ.2) =
      ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ * g YZ.1 := by
  classical
  simp only [PMF.uniformOfFintype_apply]
  exact Fintype.sum_equiv (swapPair_involutive hρ).toPerm _ _ fun YZ => rfl

/-- **One drawn nonce is uniform.** -/
theorem sum_uniform_nonce_eq (j : Fin Q) (t : Fin k) (r : Rnd) :
    ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ * (if ρ j t = r then 1 else 0) =
      (Fintype.card Rnd : ℝ≥0∞)⁻¹ := by
  classical
  rw [← PMF.pi_uniformOfFintype]
  have h1 := PMF.sum_pi_mul_apply_coord (fun _ : Fin Q => PMF.uniformOfFintype (Fin k → Rnd)) j
    (fun v => if v t = r then (1 : ℝ≥0∞) else 0)
  rw [h1, ← PMF.pi_uniformOfFintype]
  have h2 := PMF.sum_pi_mul_apply_coord (fun _ : Fin k => PMF.uniformOfFintype Rnd) t
    (fun x => if x = r then (1 : ℝ≥0∞) else 0)
  rw [h2, Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
  simp [PMF.uniformOfFintype_apply]

open Classical in
/-- **A union bound over the nonces**: the drawn nonces hit one of the nonces of a list of points
with probability at most `|L| · Q k / |R|`. -/
theorem sum_uniform_nonceHit_le (L : List (Rnd × Pt)) :
    ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        (if ∃ x ∈ L, NonceHit ρ x.1 then 1 else 0) ≤
      L.length * (Q * k) * (Fintype.card Rnd : ℝ≥0∞)⁻¹ := by
  classical
  calc ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        (if ∃ x ∈ L, NonceHit ρ x.1 then 1 else 0)
      ≤ ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
          (L.map fun x => ∑ jt : Fin Q × Fin k, (if ρ jt.1 jt.2 = x.1 then 1 else 0 : ℝ≥0∞)).sum := by
        refine Finset.sum_le_sum fun ρ _ => ?_
        gcongr
        split_ifs with h
        · obtain ⟨x, hx, jt, hjt⟩ := h
          refine le_trans ?_ (List.single_le_sum (fun _ _ => zero_le) _
            (List.mem_map_of_mem (f := fun x => ∑ jt : Fin Q × Fin k,
              (if ρ jt.1 jt.2 = x.1 then 1 else 0 : ℝ≥0∞)) hx))
          exact le_trans (by simp [hjt]) (Finset.single_le_sum (fun _ _ => zero_le)
            (Finset.mem_univ jt))
        · exact zero_le
    _ = (L.map fun x => ∑ jt : Fin Q × Fin k, ∑ ρ : Fin Q → Fin k → Rnd,
          PMF.uniformOfFintype _ ρ * (if ρ jt.1 jt.2 = x.1 then 1 else 0)).sum := by
        clear * -
        induction L with
        | nil => simp
        | cons x L ih =>
          simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ← ih,
            Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = L.length * (Q * k) * (Fintype.card Rnd : ℝ≥0∞)⁻¹ := by
        simp only [sum_uniform_nonce_eq, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, List.map_const', List.sum_replicate]
        push_cast
        ring

/-- **Two distinct coordinates of a uniform function collide** with probability `1 / |R|`. -/
theorem sum_uniform_coord_eq_coord {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b) :
    ∑ σ : ι → Rnd, PMF.uniformOfFintype _ σ * (if σ a = σ b then 1 else 0) =
      (Fintype.card Rnd : ℝ≥0∞)⁻¹ := by
  classical
  rw [← PMF.pi_uniformOfFintype]
  have h := PMF.sum_pi_mul_apply_eq (fun _ : ι => PMF.uniformOfFintype Rnd) a
    (fun T x => if x = T b then (1 : ℝ≥0∞) else 0) fun T x => by
      funext y; rw [Function.update_of_ne (Ne.symm hab)]
  rw [h]
  have hin : ∀ T : ι → Rnd, ∑ x, PMF.uniformOfFintype Rnd x * (if x = T b then (1 : ℝ≥0∞) else 0) =
      (Fintype.card Rnd : ℝ≥0∞)⁻¹ := fun T => by
    rw [Finset.sum_eq_single (T b) (fun x _ hx => by simp [hx]) (by simp)]
    simp [PMF.uniformOfFintype_apply]
  simp only [hin]
  rw [← Finset.sum_mul, PMF.sum_coe, one_mul]

/-- Averages over curried nonces are averages over uncurried ones. -/
theorem sum_uniform_curry (g : (Fin Q → Fin k → Rnd) → ℝ≥0∞) :
    ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ * g ρ =
      ∑ σ : Fin Q × Fin k → Rnd, PMF.uniformOfFintype _ σ * g (Function.curry σ) := by
  have hc : Fintype.card (Fin Q → Fin k → Rnd) = Fintype.card (Fin Q × Fin k → Rnd) :=
    Fintype.card_congr (Equiv.curry _ _ _).symm
  simp only [PMF.uniformOfFintype_apply, hc]
  exact (Fintype.sum_equiv (Equiv.curry (Fin Q) (Fin k) Rnd) _ _ fun σ => rfl).symm

open Classical in
/-- **A birthday bound**: the `Q k` drawn nonces collide with probability at most
`(Q k)² / |R|`. -/
theorem sum_uniform_not_distinct_le :
    ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ * (if NoncesDistinct ρ then 0 else 1) ≤
      (Q * k) ^ 2 * (Fintype.card Rnd : ℝ≥0∞)⁻¹ := by
  rw [sum_uniform_curry]
  calc ∑ σ : Fin Q × Fin k → Rnd, PMF.uniformOfFintype _ σ *
        (if NoncesDistinct (Function.curry σ) then 0 else 1)
      ≤ ∑ σ : Fin Q × Fin k → Rnd, PMF.uniformOfFintype _ σ *
          ∑ a : Fin Q × Fin k, ∑ b : Fin Q × Fin k,
            (if a ≠ b ∧ σ a = σ b then 1 else 0 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        gcongr
        split_ifs with h
        · exact zero_le
        · unfold NoncesDistinct Function.Injective at h
          push Not at h
          obtain ⟨a, b, hab, hne⟩ := h
          refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ a))
          refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ b))
          rw [if_pos ⟨hne, hab⟩]
    _ = ∑ a : Fin Q × Fin k, ∑ b : Fin Q × Fin k, ∑ σ : Fin Q × Fin k → Rnd,
          PMF.uniformOfFintype _ σ * (if a ≠ b ∧ σ a = σ b then 1 else 0 : ℝ≥0∞) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ ≤ ∑ _a : Fin Q × Fin k, ∑ _b : Fin Q × Fin k, (Fintype.card Rnd : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        by_cases hab : a = b
        · simp [hab]
        · rw [← sum_uniform_coord_eq_coord (Rnd := Rnd) hab]
          exact le_of_eq (Finset.sum_congr rfl fun σ _ => by simp [hab])
    _ = (Q * k) ^ 2 * (Fintype.card Rnd : ℝ≥0∞)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

end Swap

/-! ### Two-sided bounds -/

/-- **`a` and `b` are within `e`** in `ℝ≥0∞`, in both directions. -/
def EClose (a b e : ℝ≥0∞) : Prop := a ≤ b + e ∧ b ≤ a + e

namespace EClose

variable {a b c e f : ℝ≥0∞}

theorem symm (h : EClose a b e) : EClose b a e := ⟨h.2, h.1⟩

theorem trans (h₁ : EClose a b e) (h₂ : EClose b c f) : EClose a c (e + f) :=
  ⟨h₁.1.trans ((add_le_add h₂.1 le_rfl).trans_eq (by rw [add_assoc, add_comm f e])),
    h₂.2.trans ((add_le_add h₁.2 le_rfl).trans_eq (add_assoc _ _ _))⟩

theorem of_eq (h : a = b) : EClose a b e := ⟨h ▸ le_self_add, h ▸ le_self_add⟩

theorem mono (h : EClose a b e) (hef : e ≤ f) : EClose a b f :=
  ⟨h.1.trans (add_le_add le_rfl hef), h.2.trans (add_le_add le_rfl hef)⟩

theorem of_le_one (ha : a ≤ 1) (hb : b ≤ 1) : EClose a b 1 :=
  ⟨ha.trans le_add_self, hb.trans le_add_self⟩

/-- **Weighted sums of close values** are within the weighted sum of the bounds. -/
theorem wsum {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0∞) {x y d : ι → ℝ≥0∞}
    (h : ∀ i, EClose (x i) (y i) (d i)) :
    EClose (∑ i ∈ s, w i * x i) (∑ i ∈ s, w i * y i) (∑ i ∈ s, w i * d i) := by
  constructor
  · calc ∑ i ∈ s, w i * x i ≤ ∑ i ∈ s, w i * (y i + d i) :=
          Finset.sum_le_sum fun i _ => by gcongr; exact (h i).1
      _ = _ := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
  · calc ∑ i ∈ s, w i * y i ≤ ∑ i ∈ s, w i * (x i + d i) :=
          Finset.sum_le_sum fun i _ => by gcongr; exact (h i).2
      _ = _ := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => mul_add _ _ _

end EClose

/-- The uniform law on a product weighs a pair by the product of the uniform weights. -/
theorem _root_.PMF.uniformOfFintype_prod_apply {A B : Type*} [Fintype A] [Nonempty A] [Fintype B]
    [Nonempty B] (a : A) (b : B) :
    PMF.uniformOfFintype (A × B) (a, b) = PMF.uniformOfFintype A a * PMF.uniformOfFintype B b := by
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- **An average over a product of uniform laws**, one component at a time. -/
theorem sum_uniform_prod {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (g : A × B → ℝ≥0∞) :
    ∑ ab : A × B, PMF.uniformOfFintype _ ab * g ab =
      ∑ a, PMF.uniformOfFintype A a * ∑ b, PMF.uniformOfFintype B b * g (a, b) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [PMF.uniformOfFintype_prod_apply, mul_assoc]

/-- A uniform average of a constant is the constant. -/
theorem sum_uniform_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ≥0∞) :
    ∑ a, PMF.uniformOfFintype A a * c = c := by
  rw [← Finset.sum_mul, PMF.sum_coe, one_mul]

/-- **An average of a product over independent uniform coordinates** is the power of the
average. -/
theorem sum_uniform_prod_pow {β : Type*} [Fintype β] [Nonempty β] [DecidableEq β] (k : ℕ)
    (g : β → ℝ≥0∞) :
    ∑ v : Fin k → β, PMF.uniformOfFintype _ v * ∏ t, g (v t) =
      (∑ b, PMF.uniformOfFintype β b * g b) ^ k := by
  rw [← PMF.pi_uniformOfFintype]
  simp only [PMF.pi_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin k) b => PMF.uniformOfFintype β b * g b), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Exchanging a finite weighted sum with a tsum of products. -/
theorem sum_mul_tsum_mul_comm {ι σ : Type*} [Fintype ι] (w : ι → ℝ≥0∞) (a : σ → ℝ≥0∞)
    (b : ι → σ → ℝ≥0∞) :
    ∑ i, w i * ∑' s, a s * b i s = ∑' s, a s * ∑ i, w i * b i s := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine tsum_congr fun s => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The hedged rounds against the rounds with fresh masks -/

section Compare

variable {Ω Pub Pf Ch α Rnd Pt Mask : Type} [Fintype Ω] [Nonempty Ω] [Fintype α] [DecidableEq α]
  [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Pt] [DecidableEq Pt]
  [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] {Q : ℕ}
  (att : Ch → (Pt → Mask) → PMF (Option α)) (dflt : α)
  (rnd : (j : Fin Q) → Ω × PubHist Pub Pf j → Ch → α → PMF (Option (Pub × Pf)))
  (adm : Ch → Prop) [DecidablePred adm]
  (cf : (Rnd × Pt → Mask) → (j : Fin Q) → Ω × PubHist Pub Pf j → Ch) {q k : ℕ}
  (algC : (j : Fin Q) → Ω × PubHist Pub Pf j → ROM.Alg (Rnd × Pt) Mask Ch q)

open Classical in
/-- **The choice of round `j` queries a slice at a drawn nonce.** -/
def BadChoice (ρ : Fin Q → Fin k → Rnd) (Y : Rnd × Pt → Mask) (j : Fin Q)
    (s : Ω × PubHist Pub Pf j) : Prop :=
  ∃ x ∈ (algC j s).queries Y q, NonceHit ρ x.1

open Classical in
/-- **The rejection of the given masks of round `j`**: on an admitted challenge, the probability
that the `k` attempts with the masks `Z j` all reject. -/
noncomputable def failMass (Y : Rnd × Pt → Mask) (Z : Fin Q → Fin k → Pt → Mask) (j : Fin Q)
    (s : Ω × PubHist Pub Pf j) : ℝ≥0∞ :=
  if adm (cf Y j s) then ∏ t, att (cf Y j s) (Z j t) none else 0

include algC in
open Classical in
/-- **One round of the hedged signer at the swapped oracle against one round with the given
masks**: when the choice of the round does not query a slice at a drawn nonce, the two rounds
differ only in the continuation after `k` rejected attempts. -/
theorem etv_step_swap_le
    (hrnd : ∀ j s c, ¬ adm c → ∀ x, rnd j s c x = rnd j s c dflt)
    (hC : ∀ Y j s, cf Y j s = (algC j s).output Y)
    {ρ : Fin Q → Fin k → Rnd} (hρ : NoncesDistinct ρ) (Y : Rnd × Pt → Mask)
    (Z : Fin Q → Fin k → Pt → Mask) (j : Fin Q) (s : Ω × PubHist Pub Pf j) :
    PMF.etv (chooseSteps rnd (cf (swapY ρ Y Z)) (fun j c => sigNonces att dflt (swapY ρ Y Z) (ρ j) c)
        j s)
      (chooseSteps rnd (cf Y) (fun j c => sigMasks att dflt Y (Z j) c) j s) ≤
      (if BadChoice algC ρ Y j s then 1 else 0) + failMass att adm cf Y Z j s := by
  by_cases hb : BadChoice algC ρ Y j s
  · rw [if_pos hb]
    exact (PMF.etv_le_one _ _).trans le_self_add
  rw [if_neg hb, zero_add]
  have hc : cf (swapY ρ Y Z) j s = cf Y j s := by
    rw [hC, hC]
    refine (algC j s).output_eq_of_agree fun x hx => swapY_of_not fun hx' => hb ⟨x, hx, hx'⟩
  unfold chooseSteps
  rw [hc]
  set c := cf Y j s
  dsimp only
  have hsig : sigNonces att dflt (swapY ρ Y Z) (ρ j) c =
      finish dflt (PMF.firstOf fun t => att c (Z j t)) (untilSome (realAtt att (swapY ρ Y Z) c)) := by
    unfold sigNonces
    simp only [maskSlice_swapY hρ]
  rw [hsig]
  unfold failMass
  by_cases ha : adm c
  · rw [if_pos ha, ← PMF.firstOf_apply_none]
    exact (PMF.etv_bind_right_le _ _ _).trans (etv_finish_le dflt _ _ _)
  · rw [if_neg ha]
    have hconst : ∀ X : PMF α, X.bind (rnd j s c) = rnd j s c dflt := fun X => by
      rw [show rnd j s c = fun _ => rnd j s c dflt from funext (hrnd j s c ha), PMF.bind_const]
    rw [hconst, hconst, PMF.etv_self]

omit [DecidableEq Pt] [DecidableEq Mask] [DecidablePred adm] in
/-- **The hedged rounds with the nonces of the first `k` attempts drawn up front.** -/
theorem seqRun_sigReal_eq (Y : Rnd × Pt → Mask) (j : ℕ) (hj : j ≤ Q) :
    seqRun (chooseSteps rnd (cf Y) (sigReal att dflt Y)) j hj =
      (PMF.uniformOfFintype (Fin Q → Fin k → Rnd)).bind fun ρ =>
        seqRun (chooseSteps rnd (cf Y) fun j c => sigNonces att dflt Y (ρ j) c) j hj := by
  have h := bind_pi_seqRun (fun _ : Fin Q => PMF.uniformOfFintype (Fin k → Rnd))
    (fun i rv s => (sigNonces att dflt Y rv (cf Y i s)).bind (rnd i s (cf Y i s))) j hj
  rw [PMF.pi_uniformOfFintype] at h
  refine Eq.trans ?_ h.symm
  refine seqRun_congr j hj fun i _ => funext fun s => ?_
  rw [← PMF.bind_bind, uniform_bind_sigNonces]
  rfl

omit [DecidablePred adm] in
/-- **The rounds with the masks of the first `k` attempts drawn up front.** -/
theorem seqRun_sigFresh_eq (Y : Rnd × Pt → Mask) (j : ℕ) (hj : j ≤ Q) :
    seqRun (chooseSteps rnd (cf Y) fun _ c => sigFresh att dflt k Y c) j hj =
      (PMF.uniformOfFintype (Fin Q → Fin k → Pt → Mask)).bind fun Z =>
        seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) j hj := by
  have h := bind_pi_seqRun (fun _ : Fin Q => PMF.uniformOfFintype (Fin k → Pt → Mask))
    (fun i zv s => (sigMasks att dflt Y zv (cf Y i s)).bind (rnd i s (cf Y i s))) j hj
  rw [PMF.pi_uniformOfFintype] at h
  refine Eq.trans ?_ h.symm
  refine seqRun_congr j hj fun i _ => funext fun s => ?_
  rw [← PMF.bind_bind, uniform_bind_sigMasks]
  rfl

omit [DecidableEq Rnd] in
/-- **The rounds with `k` fresh-mask attempts against the rounds with fresh masks**: within
`Q ρ^k`, when every admitted chosen challenge's fresh-mask attempt rejects with probability at
most `ρ`. -/
theorem etv_seqRun_sigFresh_le (hrnd : ∀ j s c, ¬ adm c → ∀ x, rnd j s c x = rnd j s c dflt)
    {ρb : ℝ≥0∞} (Y : Rnd × Pt → Mask)
    (hρ : ∀ j s, adm (cf Y j s) → meanAtt att (cf Y j s) none ≤ ρb) :
    PMF.etv (seqRun (chooseSteps rnd (cf Y) fun _ c => sigFresh att dflt k Y c) Q le_rfl)
      (seqRun (chooseSteps rnd (cf Y) (sigIdeal att dflt)) Q le_rfl) ≤ Q * ρb ^ k := by
  refine (etv_seqRun_le _ _ Q le_rfl).trans ?_
  have hstep : ∀ (i : Fin Q) s, PMF.etv (chooseSteps rnd (cf Y) (fun _ c => sigFresh att dflt k Y c) i s)
      (chooseSteps rnd (cf Y) (sigIdeal att dflt) i s) ≤ ρb ^ k := fun i s => by
    unfold chooseSteps
    by_cases ha : adm (cf Y i s)
    · refine (PMF.etv_bind_right_le _ _ _).trans ((etv_sigFresh_le att dflt k Y _).trans ?_)
      exact pow_le_pow_left₀ zero_le (hρ i s ha) k
    · have hconst : ∀ X : PMF α, X.bind (rnd i s (cf Y i s)) = rnd i s (cf Y i s) dflt := fun X => by
        rw [show rnd i s (cf Y i s) = fun _ => rnd i s (cf Y i s) dflt from
          funext (hrnd i s _ ha), PMF.bind_const]
      rw [hconst, hconst, PMF.etv_self]
      exact zero_le
  calc ∑ i : Fin Q, ∑' s, seqRun (chooseSteps rnd (cf Y) (sigIdeal att dflt)) i (by omega) s *
        PMF.etv (chooseSteps rnd (cf Y) (fun _ c => sigFresh att dflt k Y c) (Fin.castLE le_rfl i) s)
          (chooseSteps rnd (cf Y) (sigIdeal att dflt) (Fin.castLE le_rfl i) s)
      ≤ ∑ _i : Fin Q, ρb ^ k := Finset.sum_le_sum fun i _ => by
        calc _ ≤ ∑' s, seqRun (chooseSteps rnd (cf Y) (sigIdeal att dflt)) i (by omega) s * ρb ^ k :=
              ENNReal.tsum_le_tsum fun s => by gcongr; exact hstep _ s
          _ = ρb ^ k := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = Q * ρb ^ k := by simp

variable (algE : Ω × PubHist Pub Pf Q → ROM.Alg (Rnd × Pt) Mask Prop q)

/-- **The distinguisher queries a slice at a drawn nonce.** -/
def BadEvent (ρ : Fin Q → Fin k → Rnd) (Y : Rnd × Pt → Mask) (s : Ω × PubHist Pub Pf Q) : Prop :=
  ∃ x ∈ (algE s).queries Y q, NonceHit ρ x.1

/-- **The error of the swap** at the masks `Z`: the choices and the distinguisher querying a
slice at a drawn nonce, and the rejection of the `k` attempts with the masks `Z`, in the rounds
with the masks `Z`. -/
noncomputable def swapErr (ρ : Fin Q → Fin k → Rnd) (Y : Rnd × Pt → Mask)
    (Z : Fin Q → Fin k → Pt → Mask) : ℝ≥0∞ :=
  open Classical in
  (∑ i : Fin Q, ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) i
      (by omega) s * ((if BadChoice algC ρ Y i s then 1 else 0) + failMass att adm cf Y Z i s)) +
    (seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl).toOuterMeasure
      {s | BadEvent algE ρ Y s}

include algC algE in
/-- **The hedged rounds at the swapped oracle against the rounds with the masks `Z`**, for
distinct nonces: an event of the distinguisher has probabilities within the swap error. -/
theorem toOuterMeasure_swap_le
    (hrnd : ∀ j s c, ¬ adm c → ∀ x, rnd j s c x = rnd j s c dflt)
    (hC : ∀ Y j s, cf Y j s = (algC j s).output Y)
    (Ev : (Rnd × Pt → Mask) → Ω × PubHist Pub Pf Q → Prop) (hE : ∀ Y s, Ev Y s = (algE s).output Y)
    {ρ : Fin Q → Fin k → Rnd} (hρ : NoncesDistinct ρ) (Y : Rnd × Pt → Mask)
    (Z : Fin Q → Fin k → Pt → Mask) :
    (seqRun (chooseSteps rnd (cf (swapY ρ Y Z)) fun j c => sigNonces att dflt (swapY ρ Y Z) (ρ j) c)
        Q le_rfl).toOuterMeasure {s | Ev (swapY ρ Y Z) s} ≤
        (seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl).toOuterMeasure
          {s | Ev Y s} + swapErr att dflt rnd adm cf algC algE ρ Y Z ∧
      (seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl).toOuterMeasure
          {s | Ev Y s} ≤
        (seqRun (chooseSteps rnd (cf (swapY ρ Y Z)) fun j c =>
          sigNonces att dflt (swapY ρ Y Z) (ρ j) c) Q le_rfl).toOuterMeasure
            {s | Ev (swapY ρ Y Z) s} + swapErr att dflt rnd adm cf algC algE ρ Y Z := by
  classical
  set p := seqRun (chooseSteps rnd (cf (swapY ρ Y Z)) fun j c =>
    sigNonces att dflt (swapY ρ Y Z) (ρ j) c) Q le_rfl
  set r := seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl
  have hS : PMF.etv p r ≤ ∑ i : Fin Q, ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c =>
      sigMasks att dflt Y (Z j) c) i (by omega) s *
        ((if BadChoice algC ρ Y i s then 1 else 0) + failMass att adm cf Y Z i s) :=
    (etv_seqRun_le _ _ Q le_rfl).trans (Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun s =>
      mul_le_mul_right (etv_step_swap_le att dflt rnd adm cf algC hrnd hC hρ Y Z _ s) _)
  have hev : ∀ s, ¬ BadEvent algE ρ Y s → (Ev (swapY ρ Y Z) s ↔ Ev Y s) := fun s hs => by
    rw [hE, hE, (algE s).output_eq_of_agree fun x hx => swapY_of_not fun hx' => hs ⟨x, hx, hx'⟩]
  have hsub1 : {s | Ev (swapY ρ Y Z) s} ⊆ {s | Ev Y s} ∪ {s | BadEvent algE ρ Y s} := fun s hs => by
    by_cases hb : BadEvent algE ρ Y s
    · exact Or.inr hb
    · exact Or.inl ((hev s hb).1 hs)
  have hsub2 : {s | Ev Y s} ⊆ {s | Ev (swapY ρ Y Z) s} ∪ {s | BadEvent algE ρ Y s} := fun s hs => by
    by_cases hb : BadEvent algE ρ Y s
    · exact Or.inr hb
    · exact Or.inl ((hev s hb).2 hs)
  have hu1 := (PMF.toOuterMeasure_mono r fun s hs => hsub1 hs.1).trans (MeasureTheory.measure_union_le
    (μ := r.toOuterMeasure) _ _)
  have hu2 := (PMF.toOuterMeasure_mono r fun s hs => hsub2 hs.1).trans (MeasureTheory.measure_union_le
    (μ := r.toOuterMeasure) _ _)
  unfold swapErr
  constructor
  · calc p.toOuterMeasure {s | Ev (swapY ρ Y Z) s}
        ≤ r.toOuterMeasure {s | Ev (swapY ρ Y Z) s} + PMF.etv p r := PMF.toOuterMeasure_le_add_etv _ _ _
      _ ≤ (r.toOuterMeasure {s | Ev Y s} + r.toOuterMeasure {s | BadEvent algE ρ Y s}) +
            PMF.etv p r := by gcongr
      _ ≤ _ := (add_assoc _ _ _).le.trans
          (add_le_add le_rfl ((add_comm _ _).le.trans (add_le_add hS le_rfl)))
  · calc r.toOuterMeasure {s | Ev Y s}
        ≤ r.toOuterMeasure {s | Ev (swapY ρ Y Z) s} + r.toOuterMeasure {s | BadEvent algE ρ Y s} :=
          hu2
      _ ≤ (p.toOuterMeasure {s | Ev (swapY ρ Y Z) s} + PMF.etv r p) +
            r.toOuterMeasure {s | BadEvent algE ρ Y s} := by
          gcongr
          exact PMF.toOuterMeasure_le_add_etv _ _ _
      _ ≤ _ := by
          rw [PMF.etv_comm]
          exact (add_assoc _ _ _).le.trans (add_le_add le_rfl (add_le_add hS le_rfl))

include att in
open Classical in
/-- **The rejection of the given masks, averaged over the masks**: at most `ρ^k` in every round,
when every admitted chosen challenge's fresh-mask attempt rejects with probability at most
`ρ`. -/
theorem sum_uniform_failMass_le {ρb : ℝ≥0∞} (Y : Rnd × Pt → Mask)
    (hρ : ∀ j s, adm (cf Y j s) → meanAtt att (cf Y j s) none ≤ ρb) (i : Fin Q) :
    ∑ Z : Fin Q → Fin k → Pt → Mask, PMF.uniformOfFintype _ Z *
        ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) i (by omega) s *
          failMass att adm cf Y Z i s ≤ ρb ^ k := by
  rw [show PMF.uniformOfFintype (Fin Q → Fin k → Pt → Mask) =
    PMF.pi (fun _ => PMF.uniformOfFintype (Fin k → Pt → Mask)) from PMF.pi_uniformOfFintype.symm]
  have h := sum_pi_seqRun_mul (fun _ : Fin Q => PMF.uniformOfFintype (Fin k → Pt → Mask))
    (fun i zv s => (sigMasks att dflt Y zv (cf Y i s)).bind (rnd i s (cf Y i s))) i
    (fun zv s => if adm (cf Y i s) then ∏ t, att (cf Y i s) (zv t) none else 0)
  calc _ = _ := h
    _ ≤ ∑' s, seqRun (fun i s => (PMF.uniformOfFintype (Fin k → Pt → Mask)).bind fun r =>
          (sigMasks att dflt Y r (cf Y i s)).bind (rnd i s (cf Y i s))) i i.2.le s * ρb ^ k := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        gcongr
        by_cases ha : adm (cf Y i s)
        · simp only [ha, if_true]
          rw [sum_uniform_prod_pow k fun z => att (cf Y i s) z none]
          refine pow_le_pow_left₀ zero_le ?_ k
          refine le_trans (le_of_eq ?_) (hρ i s ha)
          rw [meanAtt, PMF.bind_apply, tsum_fintype]
        · simp [ha]
    _ = ρb ^ k := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

include att in
open Classical in
/-- **The swap error averaged over the nonces**: the queries of the `Q` choices and of the
distinguisher hit a drawn nonce with probability at most `(Q + 1) q Q k / |R|`. -/
theorem sum_uniform_swapErr_le (Y : Rnd × Pt → Mask) (Z : Fin Q → Fin k → Pt → Mask) :
    ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ * swapErr att dflt rnd adm cf algC algE ρ Y Z ≤
      (∑ i : Fin Q, ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) i
          (by omega) s * failMass att adm cf Y Z i s) +
        (Q + 1) * q * (Q * k) * (Fintype.card Rnd : ℝ≥0∞)⁻¹ := by
  set B : ℝ≥0∞ := q * (Q * k) * (Fintype.card Rnd : ℝ≥0∞)⁻¹
  have hhit : ∀ L : List (Rnd × Pt), L.length = q →
      ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        (if ∃ x ∈ L, NonceHit ρ x.1 then 1 else 0) ≤ B := fun L hL => by
    have := sum_uniform_nonceHit_le (Q := Q) (k := k) (Pt := Pt) L
    rw [hL] at this
    exact this
  unfold swapErr
  -- the rounds
  have hR : ∀ i : Fin Q, ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
      ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) i (by omega) s *
        ((if BadChoice algC ρ Y i s then 1 else 0) + failMass att adm cf Y Z i s) ≤
      B + ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) i
        (by omega) s * failMass att adm cf Y Z i s := fun i => by
    rw [sum_mul_tsum_mul_comm]
    calc ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) i (by omega) s *
          ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
            ((if BadChoice algC ρ Y i s then 1 else 0) + failMass att adm cf Y Z i s)
        ≤ ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) i (by omega) s *
            (B + failMass att adm cf Y Z i s) := by
          refine ENNReal.tsum_le_tsum fun s => ?_
          gcongr
          simp_rw [mul_add, Finset.sum_add_distrib, sum_uniform_const]
          gcongr
          convert hhit ((algC i s).queries Y q) (ROM.Alg.length_queries _ _ _) using 4 <;> rfl
      _ = _ := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hE : ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
      (seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl).toOuterMeasure
        {s | BadEvent algE ρ Y s} ≤ B := by
    simp only [PMF.toOuterMeasure_apply, Set.indicator_apply, Set.mem_setOf_eq]
    have hc : ∀ ρ : Fin Q → Fin k → Rnd,
        (∑' s, if BadEvent algE ρ Y s then
          seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl s else 0) =
        ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl s *
          (if BadEvent algE ρ Y s then 1 else 0) := fun ρ =>
      tsum_congr fun s => by split_ifs <;> simp
    simp_rw [hc]
    rw [sum_mul_tsum_mul_comm]
    calc _ ≤ ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl s *
          B := ENNReal.tsum_le_tsum fun s => by
            gcongr
            convert hhit ((algE s).queries Y q) (ROM.Alg.length_queries _ _ _) using 4 <;> rfl
      _ = B := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc _ = (∑ i : Fin Q, ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
          ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) i (by omega) s *
            ((if BadChoice algC ρ Y i s then 1 else 0) + failMass att adm cf Y Z i s)) +
        ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
          (seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl).toOuterMeasure
            {s | BadEvent algE ρ Y s} := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [mul_add, Finset.mul_sum]
    _ ≤ (∑ i : Fin Q, (B + ∑' s, seqRun (chooseSteps rnd (cf Y) fun j c =>
          sigMasks att dflt Y (Z j) c) i (by omega) s * failMass att adm cf Y Z i s)) + B :=
        add_le_add (Finset.sum_le_sum fun i _ => hR i) hE
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        simp only [B]
        ring

include att algC algE in
open Classical in
/-- **The hedged signer against the signer with fresh masks**, averaged over a uniform mask
oracle: for choices and a distinguisher that read the mask oracle through at most `q` queries
each (`hC`, `hE`) and every admitted chosen challenge's fresh-mask attempt rejecting with
probability at most `ρ` (`hρ`), the probabilities of the distinguisher's event are within
`(Q k)² / |R| + (Q + 1) q Q k / |R| + 2 Q ρ^k`, for every number `k` of attempts. The proof
draws the nonces of the first `k` attempts of every round up front, swaps the slices of the mask
oracle at those nonces with fresh masks (an involution preserving the uniform law, for distinct
nonces), and charges the rounds whose choice, or the distinguisher, queries a drawn nonce, and
the rounds whose `k` attempts all reject. -/
theorem sum_uniform_hedged_close
    (hrnd : ∀ j s c, ¬ adm c → ∀ x, rnd j s c x = rnd j s c dflt)
    (hC : ∀ Y j s, cf Y j s = (algC j s).output Y)
    (Ev : (Rnd × Pt → Mask) → Ω × PubHist Pub Pf Q → Prop) (hE : ∀ Y s, Ev Y s = (algE s).output Y)
    {ρb : ℝ≥0∞} (hρ : ∀ Y j s, adm (cf Y j s) → meanAtt att (cf Y j s) none ≤ ρb) :
    EClose (∑ Y, PMF.uniformOfFintype _ Y *
        (seqRun (chooseSteps rnd (cf Y) (sigReal att dflt Y)) Q le_rfl).toOuterMeasure {s | Ev Y s})
      (∑ Y, PMF.uniformOfFintype _ Y *
        (seqRun (chooseSteps rnd (cf Y) (sigIdeal att dflt)) Q le_rfl).toOuterMeasure {s | Ev Y s})
      ((Q * k) ^ 2 * (Fintype.card Rnd : ℝ≥0∞)⁻¹ +
        (Q + 1) * q * (Q * k) * (Fintype.card Rnd : ℝ≥0∞)⁻¹ + 2 * Q * ρb ^ k) := by
  set P1 : (Rnd × Pt → Mask) → (Fin Q → Fin k → Rnd) → ℝ≥0∞ := fun Y ρ =>
    (seqRun (chooseSteps rnd (cf Y) fun j c => sigNonces att dflt Y (ρ j) c) Q le_rfl).toOuterMeasure
      {s | Ev Y s}
  set P3 : (Rnd × Pt → Mask) → (Fin Q → Fin k → Pt → Mask) → ℝ≥0∞ := fun Y Z =>
    (seqRun (chooseSteps rnd (cf Y) fun j c => sigMasks att dflt Y (Z j) c) Q le_rfl).toOuterMeasure
      {s | Ev Y s}
  set PF : (Rnd × Pt → Mask) → ℝ≥0∞ := fun Y =>
    (seqRun (chooseSteps rnd (cf Y) fun _ c => sigFresh att dflt k Y c) Q le_rfl).toOuterMeasure
      {s | Ev Y s}
  have hle1 : ∀ (p : PMF (Ω × PubHist Pub Pf Q)) (S : Set _), p.toOuterMeasure S ≤ 1 :=
    fun p S => PMF.toOuterMeasure_apply_le_one _ _
  have hsum1 : ∀ {A : Type} [Fintype A] [Nonempty A] (g : A → ℝ≥0∞), (∀ a, g a ≤ 1) →
      ∑ a, PMF.uniformOfFintype A a * g a ≤ 1 := fun g hg =>
    (Finset.sum_le_sum fun a _ => mul_le_of_le_one_right' (hg a)).trans_eq (PMF.sum_coe _)
  -- the hedged rounds, with the nonces drawn up front
  have hA : ∑ Y, PMF.uniformOfFintype _ Y *
      (seqRun (chooseSteps rnd (cf Y) (sigReal att dflt Y)) Q le_rfl).toOuterMeasure {s | Ev Y s} =
      ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        ∑ Y, PMF.uniformOfFintype _ Y * P1 Y ρ := by
    simp_rw [seqRun_sigReal_eq att dflt rnd cf (k := k), PMF.toOuterMeasure_bind_apply, tsum_fintype,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun Y _ => by ring
  -- the rounds with the masks drawn up front
  have hC1 : ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
      ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
        P3 YZ.1 YZ.2 = ∑ Y, PMF.uniformOfFintype _ Y * PF Y := by
    rw [sum_uniform_const, sum_uniform_prod]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [PF]
    rw [seqRun_sigFresh_eq att dflt rnd cf Y Q le_rfl, PMF.toOuterMeasure_bind_apply, tsum_fintype]
  -- the swap
  have hB : EClose (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        ∑ Y, PMF.uniformOfFintype _ Y * P1 Y ρ)
      (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
          P3 YZ.1 YZ.2)
      (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        (if NoncesDistinct ρ then
          ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
            swapErr att dflt rnd adm cf algC algE ρ YZ.1 YZ.2 else 1)) := by
    refine EClose.wsum _ _ fun ρ => ?_
    by_cases hd : NoncesDistinct ρ
    · rw [if_pos hd]
      have hsw : ∑ Y, PMF.uniformOfFintype _ Y * P1 Y ρ =
          ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
            P1 (swapY ρ YZ.1 YZ.2) ρ := by
        rw [sum_uniform_swapY hd fun Y => P1 Y ρ, sum_uniform_prod]
        simp only [sum_uniform_const]
      rw [hsw]
      exact EClose.wsum _ _ fun YZ =>
        toOuterMeasure_swap_le att dflt rnd adm cf algC algE hrnd hC Ev hE hd YZ.1 YZ.2
    · rw [if_neg hd]
      exact EClose.of_le_one (hsum1 _ fun Y => hle1 _ _) (hsum1 _ fun YZ => hle1 _ _)
  -- the rounds with `k` fresh-mask attempts against the rounds with fresh masks
  have hD : EClose (∑ Y, PMF.uniformOfFintype _ Y * PF Y)
      (∑ Y, PMF.uniformOfFintype _ Y *
        (seqRun (chooseSteps rnd (cf Y) (sigIdeal att dflt)) Q le_rfl).toOuterMeasure {s | Ev Y s})
      (∑ Y : Rnd × Pt → Mask, PMF.uniformOfFintype _ Y * (Q * ρb ^ k)) := by
    refine EClose.wsum _ _ fun Y => ?_
    have h := etv_seqRun_sigFresh_le att dflt rnd adm cf (k := k) hrnd Y (hρ Y)
    exact ⟨(PMF.toOuterMeasure_le_add_etv _ _ _).trans (add_le_add le_rfl h),
      (PMF.toOuterMeasure_le_add_etv _ _ _).trans (add_le_add le_rfl ((PMF.etv_comm _ _).le.trans h))⟩
  rw [sum_uniform_const] at hD
  rw [hA]
  rw [← hC1] at hD
  refine (hB.trans hD).mono ?_
  -- the error
  have hfail : ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
      (∑ i : Fin Q, ∑' s, seqRun (chooseSteps rnd (cf YZ.1) fun j c =>
        sigMasks att dflt YZ.1 (YZ.2 j) c) i (by omega) s * failMass att adm cf YZ.1 YZ.2 i s) ≤
      Q * ρb ^ k := by
    rw [sum_uniform_prod]
    calc _ ≤ ∑ Y : Rnd × Pt → Mask, PMF.uniformOfFintype _ Y * (Q * ρb ^ k) := by
          refine Finset.sum_le_sum fun Y _ => ?_
          gcongr
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          calc _ ≤ ∑ _i : Fin Q, ρb ^ k := Finset.sum_le_sum fun i _ =>
                sum_uniform_failMass_le att dflt rnd adm cf Y (hρ Y) i
            _ = Q * ρb ^ k := by simp
      _ = Q * ρb ^ k := sum_uniform_const _
  have hcoll := sum_uniform_not_distinct_le (Q := Q) (k := k) (Rnd := Rnd)
  have hsw : ∀ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask),
      ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        swapErr att dflt rnd adm cf algC algE ρ YZ.1 YZ.2 ≤
      (∑ i : Fin Q, ∑' s, seqRun (chooseSteps rnd (cf YZ.1) fun j c =>
        sigMasks att dflt YZ.1 (YZ.2 j) c) i (by omega) s * failMass att adm cf YZ.1 YZ.2 i s) +
        (Q + 1) * q * (Q * k) * (Fintype.card Rnd : ℝ≥0∞)⁻¹ := fun YZ =>
    sum_uniform_swapErr_le att dflt rnd adm cf algC algE YZ.1 YZ.2
  calc (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
        (if NoncesDistinct ρ then
          ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
            swapErr att dflt rnd adm cf algC algE ρ YZ.1 YZ.2 else 1)) + Q * ρb ^ k
      ≤ (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
          ((if NoncesDistinct ρ then 0 else 1) +
            ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
              swapErr att dflt rnd adm cf algC algE ρ YZ.1 YZ.2)) + Q * ρb ^ k := by
        gcongr with ρ
        split_ifs
        · rw [zero_add]
        · exact le_self_add
    _ = (∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ * (if NoncesDistinct ρ then 0 else 1)) +
          ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
            ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ *
              swapErr att dflt rnd adm cf algC algE ρ YZ.1 YZ.2 + Q * ρb ^ k := by
        congr 1
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun YZ _ => Finset.sum_congr rfl fun ρ _ => by ring
    _ ≤ (Q * k) ^ 2 * (Fintype.card Rnd : ℝ≥0∞)⁻¹ +
          (Q * ρb ^ k + (Q + 1) * q * (Q * k) * (Fintype.card Rnd : ℝ≥0∞)⁻¹) + Q * ρb ^ k := by
        gcongr
        calc _ ≤ ∑ YZ : (Rnd × Pt → Mask) × (Fin Q → Fin k → Pt → Mask), PMF.uniformOfFintype _ YZ *
              ((∑ i : Fin Q, ∑' s, seqRun (chooseSteps rnd (cf YZ.1) fun j c =>
                sigMasks att dflt YZ.1 (YZ.2 j) c) i (by omega) s *
                  failMass att adm cf YZ.1 YZ.2 i s) +
                (Q + 1) * q * (Q * k) * (Fintype.card Rnd : ℝ≥0∞)⁻¹) :=
              Finset.sum_le_sum fun YZ _ => by gcongr; exact hsw YZ
          _ ≤ _ := by
              simp_rw [mul_add, Finset.sum_add_distrib, sum_uniform_const]
              gcongr
    _ = _ := by ring

end Compare

/-! ### The game in rounds -/

section GameRounds

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {S : PubSigner N RMsg}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {M : SPBCS Mg P S.Stmt k kN kS L e} {n Q : ℕ}

/-- **The statement and witness proved for a challenge** with the public value and base
signature `x` in the experiment `b` at the oracle `H`, or `⊥` when the signer refuses the ring. -/
def PubSigner.proved (S : PubSigner N RMsg) (H : S.Orc) (b : Bool) (c : S.Choice n)
    (x : S.Pub × S.Sig) : Option (S.Stmt × S.Wit) :=
  if S.Admit H c.ring c.msg then some (S.stmt c.ring c.msg x.1, S.wit (c.idx b) x.2) else none

/-- **One coordinate of a product law**, as laws: binding a function of coordinate `j` over a
product law is binding it over the coordinate's law. -/
theorem _root_.PMF.pi_bind_apply_coord {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {δ : ι' → Type*}
    [∀ i, Fintype (δ i)] [∀ i, DecidableEq (δ i)] {γ : Type*} (ν : ∀ i, PMF (δ i)) (j : ι')
    (G : δ j → PMF γ) : (PMF.pi ν).bind (fun T => G (T j)) = (ν j).bind G := by
  ext x
  simp only [PMF.bind_apply, tsum_fintype]
  exact PMF.sum_pi_mul_apply_coord ν j fun b => G b x

namespace PubAnonAdversary

variable (A : PubAnonAdversary S M n Q) (E : (j : ι) → (M.comp j).Encoder)
  {V : S.Orc → S.Stmt → FullTr P τ → Bool} (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type}
  [Fintype R] [Nonempty R] (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)

/-- **The game with the signature table is the game drawing each round's signature in the
round**: only the chosen challenge's entry of each round's row is read. -/
theorem tableLaw_bind_run_eq (H : S.Orc) (keys : Fin n → S.KeyCoins) (b : Bool) :
    (A.tableLaw H keys b).bind (fun T => A.run E Qs honest H keys b T Q le_rfl) =
      seqRun (chooseSteps (fun j s c x => roundLaw (proofLawAt E Qs honest H) S.stmtPub s.1
          (S.proved H b c x)) (fun j s => A.choose j keys H s.1 s.2)
        (fun _ c => c.signLaw H keys b)) Q le_rfl := by
  classical
  have h := bind_pi_seqRun (fun _ : Fin Q => PMF.pi fun c : A.choices => c.1.signLaw H keys b)
    (fun i row s => roundLaw (proofLawAt E Qs honest H) S.stmtPub s.1
      (S.proved H b (A.choose i keys H s.1 s.2) (row ⟨_, A.choose_mem i keys H s.1 s.2⟩))) Q le_rfl
  unfold tableLaw
  simp only [run, pubRun_eq_seqRun]
  refine h.trans (seqRun_congr _ _ fun i _ => funext fun s => ?_)
  exact PMF.pi_bind_apply_coord (fun c : A.choices => c.1.signLaw H keys b)
    ⟨_, A.choose_mem i keys H s.1 s.2⟩ fun x =>
      roundLaw (proofLawAt E Qs honest H) S.stmtPub s.1 (S.proved H b (A.choose i keys H s.1 s.2) x)

end PubAnonAdversary

end GameRounds

/-! ### Hedged ring signers -/

section Hedged

variable {N : ℕ} {RMsg : Type}

/-- **A ring signer whose masks a hedged signer reads from an oracle** (FIPS 204 Algorithm 7,
lines 7 and 11: `ρ'' = H(K ‖ rnd ‖ µ)` with a fresh nonce `rnd`, and the mask
`y = ExpandMask(ρ'', κ)` of attempt `κ`). The ideal signer `S` signs with the attempt law
`attempt H sk R i m Z` on mask slices `Z : Pt → Mask` (`Pt` the rest of a mask point: the secret
seed, the message representative and the attempt index), repeated until it accepts with a fresh
uniform slice every time (`signLaw_eq`); the hedged signer (`real`) draws a uniform nonce
`r : Rnd` for every attempt and reads its slice from the mask oracle at `r`. `dflt` is the
output of a loop that never accepts. -/
structure MaskedSigner (S : PubSigner N RMsg) where
  /-- Nonces. -/
  Rnd : Type
  /-- The rest of a mask point. -/
  Pt : Type
  /-- Masks. -/
  Mask : Type
  [instFintypeRnd : Fintype Rnd]
  [instNonemptyRnd : Nonempty Rnd]
  [instDecEqRnd : DecidableEq Rnd]
  [instFintypePt : Fintype Pt]
  [instDecEqPt : DecidableEq Pt]
  [instFintypeMask : Fintype Mask]
  [instNonemptyMask : Nonempty Mask]
  [instDecEqMask : DecidableEq Mask]
  /-- One attempt at a mask slice: the oracle of the base scheme, the secret key, the ring, the
  position, the message and the masks. -/
  attempt : S.Orc → S.SK → RingOf S.PK N → ℕ → RMsg → (Pt → Mask) → PMF (Option (S.Pub × S.Sig))
  /-- The output of a loop that never accepts. -/
  dflt : S.Pub × S.Sig
  /-- The ideal signer repeats the attempt with fresh uniform masks until it accepts. -/
  signLaw_eq : ∀ H sk R i m, S.signLaw H sk R i m =
    (untilSome ((PMF.uniformOfFintype (Pt → Mask)).bind (attempt H sk R i m))).map
      fun o => o.getD dflt

attribute [instance] MaskedSigner.instFintypeRnd MaskedSigner.instNonemptyRnd
  MaskedSigner.instDecEqRnd MaskedSigner.instFintypePt MaskedSigner.instDecEqPt
  MaskedSigner.instFintypeMask MaskedSigner.instNonemptyMask MaskedSigner.instDecEqMask

namespace MaskedSigner

variable {S : PubSigner N RMsg} (W : MaskedSigner S)

/-- **The mask oracle**: a mask at every nonce and point. -/
abbrev MaskOrc : Type := W.Rnd × W.Pt → W.Mask

/-- **The hedged signer**: the oracle of the base scheme with the mask oracle; every attempt draws
a uniform nonce and reads its masks from the mask oracle's slice at that nonce, until one accepts.
The ring relation and the refusal rule are the ideal signer's. -/
noncomputable def real : PubSigner N RMsg :=
  { S with
    Orc := S.Orc × W.MaskOrc
    signLaw := fun HY sk R i m =>
      (untilSome ((PMF.uniformOfFintype W.Rnd).bind fun r =>
        W.attempt HY.1 sk R i m fun x => HY.2 (r, x))).map fun o => o.getD W.dflt
    rel := fun HY => S.rel HY.1
    Admit := fun HY R m => S.Admit HY.1 R m
    instFintypeOrc := inferInstance
    instNonemptyOrc := inferInstance
    instDecAdmit := fun HY R m => S.instDecAdmit HY.1 R m }

end MaskedSigner

end Hedged

/-! ### Anonymity of the hedged signer -/

section HedgedGame

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {S : PubSigner N RMsg} (W : MaskedSigner S)
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {M : SPBCS Mg P S.Stmt k kN kS L e} {n Q : ℕ}

namespace MaskedSigner

/-- **A query-bounded adversary and distinguisher against the hedged signer**: every choice of
the adversary, and the distinguisher, reads the mask oracle through a classical algorithm of at
most `q` queries (`ROM.Alg`, CY24 p. 20), at every value of everything else (the users' coins,
the oracle of the base scheme, the oracle of the compiled argument and the history). The other
oracles are given whole, as in `PubAnonAdversary`. -/
structure QueryBounded (A : PubAnonAdversary W.real M n Q)
    (D : (Fin n → S.KeyCoins) → W.real.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) (q : ℕ) : Prop where
  /-- Every choice reads the mask oracle through `q` queries. -/
  choose : ∀ j keys H h hist, ∃ alg : ROM.Alg (W.Rnd × W.Pt) W.Mask (S.Choice n) q,
    ∀ Y, A.choose j keys (H, Y) h hist = alg.output Y
  /-- The distinguisher reads the mask oracle through `q` queries. -/
  dist : ∀ keys H h hist, ∃ alg : ROM.Alg (W.Rnd × W.Pt) W.Mask Prop q,
    ∀ Y, D keys (H, Y) h hist = alg.output Y

/-- **The adversary at a fixed mask oracle `Y`**, an adversary against the ideal signer.

Running time: that of the adversary, with the mask oracle `Y` fixed in its input; each choice is
the adversary's choice at `(H, Y)`. This running time is argued here, not proved in Lean. -/
def atMask (A : PubAnonAdversary W.real M n Q) (Y : W.MaskOrc) : PubAnonAdversary S M n Q where
  choices := A.choices
  choose j keys H h hist := A.choose j keys (H, Y) h hist
  choose_mem j keys H h hist := A.choose_mem j keys (H, Y) h hist
  choose_valid j keys H h hist := A.choose_valid j keys (H, Y) h hist

/-- **The fresh-mask attempt** of user `b` of a challenge at the oracle `H` and the users' coins
`keys`. -/
noncomputable def meanAttempt (H : S.Orc) (keys : Fin n → S.KeyCoins) (c : S.Choice n) (b : Bool) :
    PMF (Option (S.Pub × S.Sig)) :=
  (PMF.uniformOfFintype (W.Pt → W.Mask)).bind
    (W.attempt H (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg)

/-- **The error of the hedged signer**: the nonces of the `Q k` first attempts collide, or the
`Q + 1` query phases of `q` queries hit one of them, or `k` attempts all reject, each round of the
two hybrids, with the fresh-mask attempt rejecting with probability at most `ρ`. -/
noncomputable def hedgeError (Q q k : ℕ) (ρ : ℝ≥0∞) : ℝ≥0∞ :=
  (Q * k) ^ 2 * (Fintype.card W.Rnd : ℝ≥0∞)⁻¹ +
    (Q + 1) * q * (Q * k) * (Fintype.card W.Rnd : ℝ≥0∞)⁻¹ + 2 * Q * ρ ^ k

variable {W} {E : (j : ι) → (M.comp j).Encoder} {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
  {honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt}

open Classical in
/-- **At fixed users' coins, oracle of the base scheme and experiment**: the hedged game and the
game of the adversary at a fixed mask oracle, both averaged over a uniform mask oracle, are
within the hedged error. -/
theorem eclose_hedged (A : PubAnonAdversary W.real M n Q)
    (D : (Fin n → S.KeyCoins) → W.real.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) {q : ℕ} (hq : W.QueryBounded A D q) (ka : ℕ)
    (keys : Fin n → S.KeyCoins) (H : S.Orc) (b : Bool) {ρb : ℝ≥0∞}
    (hρ : ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg → W.meanAttempt H keys c b none ≤ ρb) :
    EClose (∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y *
        ((A.tableLaw (H, Y) keys b).bind fun T =>
          A.run (V := fun HY => V HY.1) E (fun HY => Qs HY.1) (fun HY => honest HY.1) (H, Y) keys b T
            Q le_rfl).toOuterMeasure {s | D keys (H, Y) s.1 s.2})
      (∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y *
        (((W.atMask A Y).tableLaw H keys b).bind fun T =>
          (W.atMask A Y).run E Qs honest H keys b T Q le_rfl).toOuterMeasure
            {s | D keys (H, Y) s.1 s.2})
      (W.hedgeError Q q ka ρb) := by
  have core := sum_uniform_hedged_close (k := ka)
    (fun c : S.Choice n => W.attempt H (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg) W.dflt
    (fun j s c x => roundLaw (PubAnonAdversary.proofLawAt E Qs honest H) S.stmtPub s.1
      (S.proved H b c x)) (fun c : S.Choice n => S.Admit H c.ring c.msg)
    (fun Y j s => A.choose j keys (H, Y) s.1 s.2)
    (fun j s => Classical.choose (hq.choose j keys H s.1 s.2))
    (fun s => Classical.choose (hq.dist keys H s.1 s.2))
    (fun j s c hc x => by simp [PubSigner.proved, hc])
    (fun Y j s => Classical.choose_spec (hq.choose j keys H s.1 s.2) Y)
    (fun Y s => D keys (H, Y) s.1 s.2)
    (fun Y s => Classical.choose_spec (hq.dist keys H s.1 s.2) Y)
    (ρb := ρb) (fun Y j s ha => hρ _ (A.choose_mem j keys (H, Y) s.1 s.2)
      (A.choose_valid j keys (H, Y) s.1 s.2) ha)
  have hR := fun Y : W.MaskOrc => A.tableLaw_bind_run_eq (V := fun HY => V HY.1) E
    (fun HY => Qs HY.1) (fun HY => honest HY.1) (H, Y) keys b
  simp only [hR, PubAnonAdversary.tableLaw_bind_run_eq]
  have hI : ∀ c : S.Choice n, c.signLaw H keys b =
      (untilSome (meanAtt (fun c : S.Choice n =>
        W.attempt H (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg) c)).map fun o => o.getD W.dflt :=
    fun c => W.signLaw_eq _ _ _ _ _
  simp only [hI]
  exact core

omit [DecidableEq RMsg] in
/-- The hedged error is finite for `ρ ≤ 1`. -/
theorem hedgeError_ne_top (W : MaskedSigner S) (Q q k : ℕ) {ρ : ℝ≥0∞} (hρ : ρ ≤ 1) :
    W.hedgeError Q q k ρ ≠ ⊤ := by
  unfold hedgeError
  have hc : (Fintype.card W.Rnd : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hp : ρ ^ k ≠ ⊤ := ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hρ)
  have hn : ∀ m : ℕ, (m : ℝ≥0∞) ≠ ⊤ := fun m => ENNReal.natCast_ne_top m
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top (hn _) (hn _))) hc, ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hn _, ENNReal.one_ne_top⟩)
        (hn _)) (ENNReal.mul_ne_top (hn _) (hn _))) hc⟩,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hn _)) hp⟩

/-- A weighted uniform sum in `ℝ≥0∞` of finite values, read in `ℝ`, is the average. -/
theorem toReal_sum_uniform_mul {A : Type*} [Fintype A] [Nonempty A] {f : A → ℝ≥0∞}
    (hf : ∀ a, f a ≠ ⊤) :
    (∑ a, PMF.uniformOfFintype A a * f a).toReal = 𝔼 a, (f a).toReal := by
  rw [ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hf a)]
  simp only [ENNReal.toReal_mul]
  exact PMF.sum_toReal_uniformOfFintype_mul _

open Classical in
/-- **Anonymity of the hedged signer from anonymity of the ideal-mask signer** (the step from
the idealized signer to FIPS 204 hedged signing, with the mask derivation
`ExpandMask(H(K ‖ rnd ‖ µ), κ)` a random oracle `W.MaskOrc` and a fresh nonce `rnd` for every
attempt): for an adversary and a distinguisher that read the mask oracle through at most `q`
queries per choice and for the distinguisher (`hq`), the advantage against the hedged signer is at
most the average over the mask oracle of the advantage of the adversary at that mask oracle
against the ideal-mask signer, plus twice the hedged error at every number `k` of attempts:
`(Q k)² / |R| + (Q + 1) q Q k / |R| + 2 Q ρ^k`, `ρ` bounding the probability that a fresh-mask
attempt of a valid admitted challenge rejects. With `ρ ≤ 1 - s̄`, `k ≈ t / s̄` makes the last
term `2 Q e^{-t}` and the guessing term `(Q + 1) q Q t / (|R| s̄)`. The bound needs the nonces to
be fresh: deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_atMask (A : PubAnonAdversary W.real M n Q)
    (D : (Fin n → S.KeyCoins) → W.real.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) {q : ℕ} (hq : W.QueryBounded A D q) (ka : ℕ)
    (ρ : (Fin n → S.KeyCoins) → S.Orc → ℝ≥0∞) (hρ1 : ∀ keys H, ρ keys H ≤ 1)
    (hρ : ∀ keys H, ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg → ∀ b,
      W.meanAttempt H keys c b none ≤ ρ keys H) :
    A.advantage (V := fun HY => V HY.1) E (fun HY => Qs HY.1) (fun HY => honest HY.1) D ≤
      𝔼 Y : W.MaskOrc, (W.atMask A Y).advantage E Qs honest (fun keys H => D keys (H, Y)) +
        2 * 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, (W.hedgeError Q q ka (ρ keys H)).toReal := by
  set err : (Fin n → S.KeyCoins) → S.Orc → ℝ≥0∞ := fun keys H => W.hedgeError Q q ka (ρ keys H)
  have herr : ∀ keys H, err keys H ≠ ⊤ := fun keys H => hedgeError_ne_top W Q q ka (hρ1 keys H)
  set e : ℝ≥0∞ := ∑ keys, PMF.uniformOfFintype _ keys * ∑ H, PMF.uniformOfFintype _ H * err keys H
  have he : e ≠ ⊤ := ENNReal.sum_ne_top.2 fun keys _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (ENNReal.sum_ne_top.2 fun H _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (herr keys H))
  have heR : e.toReal = 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, (err keys H).toReal := by
    rw [toReal_sum_uniform_mul fun keys => ENNReal.sum_ne_top.2 fun H _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (herr keys H)]
    exact Finset.expect_congr rfl fun keys _ => toReal_sum_uniform_mul (herr keys)
  -- the probabilities of the event in the two games
  set PR : Bool → ℝ≥0∞ := fun b =>
    (A.game (V := fun HY => V HY.1) E (fun HY => Qs HY.1) (fun HY => honest HY.1) b).toOuterMeasure
      {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}
  set PI : W.MaskOrc → Bool → ℝ≥0∞ := fun Y b =>
    ((W.atMask A Y).game E Qs honest b).toOuterMeasure {o | D o.1 (o.2.1, Y) o.2.2.1 o.2.2.2}
  have hclose : ∀ b, EClose (PR b) (∑ Y, PMF.uniformOfFintype _ Y * PI Y b) e := fun b => by
    have hPR : PR b = _ := A.toOuterMeasure_game_eq (V := fun HY => V HY.1) (E := E)
      (Qs := fun HY => Qs HY.1) (honest := fun HY => honest HY.1) b D
    have hPI : ∀ Y, PI Y b = _ := fun Y => (W.atMask A Y).toOuterMeasure_game_eq (E := E) (Qs := Qs)
      (honest := honest) b fun keys H h hist => D keys (H, Y) h hist
    have hL : ∑ keys, PMF.uniformOfFintype _ keys * ∑ HY : W.real.Orc, PMF.uniformOfFintype _ HY *
        ((A.tableLaw HY keys b).bind fun T => A.run (V := fun HY => V HY.1) E (fun HY => Qs HY.1)
          (fun HY => honest HY.1) HY keys b T Q le_rfl).toOuterMeasure {s | D keys HY s.1 s.2} =
        ∑ keys, PMF.uniformOfFintype _ keys * ∑ H : S.Orc, PMF.uniformOfFintype _ H *
          ∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y *
            ((A.tableLaw (H, Y) keys b).bind fun T => A.run (V := fun HY => V HY.1) E
              (fun HY => Qs HY.1) (fun HY => honest HY.1) (H, Y) keys b T Q le_rfl).toOuterMeasure
                {s | D keys (H, Y) s.1 s.2} :=
      Finset.sum_congr rfl fun keys _ => congrArg _ (sum_uniform_prod (A := S.Orc) (B := W.MaskOrc)
        fun HY => ((A.tableLaw HY keys b).bind fun T => A.run (V := fun HY => V HY.1) E
          (fun HY => Qs HY.1) (fun HY => honest HY.1) HY keys b T Q le_rfl).toOuterMeasure
            {s | D keys HY s.1 s.2})
    have hRt : ∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y *
        ∑ keys, PMF.uniformOfFintype _ keys * ∑ H : S.Orc, PMF.uniformOfFintype _ H *
          (((W.atMask A Y).tableLaw H keys b).bind fun T =>
            (W.atMask A Y).run E Qs honest H keys b T Q le_rfl).toOuterMeasure
              {s | D keys (H, Y) s.1 s.2} =
        ∑ keys, PMF.uniformOfFintype _ keys * ∑ H : S.Orc, PMF.uniformOfFintype _ H *
          ∑ Y : W.MaskOrc, PMF.uniformOfFintype _ Y *
            (((W.atMask A Y).tableLaw H keys b).bind fun T =>
              (W.atMask A Y).run E Qs honest H keys b T Q le_rfl).toOuterMeasure
                {s | D keys (H, Y) s.1 s.2} := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun keys _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun Y _ => by ring
    rw [hPR, hL]
    simp only [hPI]
    rw [hRt]
    exact EClose.wsum _ _ fun keys => EClose.wsum _ _ fun H =>
      eclose_hedged A D hq ka keys H b fun c hc hv ha => hρ keys H c hc hv ha b
  -- in `ℝ`
  have hfin : ∀ b, ∑ Y, PMF.uniformOfFintype _ Y * PI Y b ≤ 1 := fun b =>
    (Finset.sum_le_sum fun Y _ => mul_le_of_le_one_right' (PMF.toOuterMeasure_apply_le_one _ _)).trans_eq
      (PMF.sum_coe _)
  have hreal : ∀ b, |(PR b).toReal - (∑ Y, PMF.uniformOfFintype _ Y * PI Y b).toReal| ≤ e.toReal :=
    fun b => by
      have h1 := (hclose b).1
      have h2 := (hclose b).2
      have hP : PR b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
      have hI : (∑ Y, PMF.uniformOfFintype _ Y * PI Y b) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (hfin b)
      have r1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI, he⟩) h1
      have r2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hP, he⟩) h2
      rw [ENNReal.toReal_add hI he] at r1
      rw [ENNReal.toReal_add hP he] at r2
      rw [abs_le]
      constructor <;> linarith
  have hmix : |(∑ Y, PMF.uniformOfFintype _ Y * PI Y false).toReal -
      (∑ Y, PMF.uniformOfFintype _ Y * PI Y true).toReal| ≤
      𝔼 Y : W.MaskOrc, (W.atMask A Y).advantage E Qs honest (fun keys H => D keys (H, Y)) := by
    refine (PMF.abs_sum_mul_sub_sum_mul_le _ (fun Y => PMF.toOuterMeasure_apply_le_one _ _)
      fun Y => PMF.toOuterMeasure_apply_le_one _ _).trans_eq ?_
    rw [PMF.sum_toReal_uniformOfFintype_mul]
    rfl
  have hadv : A.advantage (V := fun HY => V HY.1) E (fun HY => Qs HY.1) (fun HY => honest HY.1) D =
      |(PR false).toReal - (PR true).toReal| := rfl
  rw [hadv, ← heR]
  have h0 := hreal false
  have h1 := hreal true
  rw [abs_le] at h0 h1 hmix ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, hmix.1, hmix.2]

omit [DecidableEq RMsg] in
open Classical in
/-- **The hedged error at a keep bound on a good event**, averaged: with `ρ = 1 - L` on the good
event and `ρ = 1` off it, the hedged error is at most
`(Q k)² / |R| + (Q + 1) q Q k / |R| + 2 Q ((1 - L)^k + Pr[¬ good])`. -/
theorem expect_toReal_hedgeError_le (W : MaskedSigner S) (Q q ka : ℕ) {α β : Type*} [Fintype α]
    [Nonempty α] [Fintype β] [Nonempty β] (Good : α → β → Prop) {L : ℝ} (hL0 : 0 ≤ L)
    (hL1 : L ≤ 1) :
    𝔼 a, 𝔼 b, (W.hedgeError Q q ka (1 - if Good a b then ENNReal.ofReal L else 0)).toReal ≤
      (Q * ka) ^ 2 * (Fintype.card W.Rnd : ℝ)⁻¹ +
        (Q + 1) * q * (Q * ka) * (Fintype.card W.Rnd : ℝ)⁻¹ +
          2 * Q * ((1 - L) ^ ka + 𝔼 a, 𝔼 b, (if Good a b then 0 else 1 : ℝ)) := by
  have hpt : ∀ a b, (W.hedgeError Q q ka (1 - if Good a b then ENNReal.ofReal L else 0)).toReal ≤
      (Q * ka) ^ 2 * (Fintype.card W.Rnd : ℝ)⁻¹ +
        (Q + 1) * q * (Q * ka) * (Fintype.card W.Rnd : ℝ)⁻¹ +
          2 * Q * ((1 - L) ^ ka + (if Good a b then 0 else 1 : ℝ)) := fun a b => by
    have hc : (Fintype.card W.Rnd : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have hn : ∀ m : ℕ, (m : ℝ≥0∞) ≠ ⊤ := fun m => ENNReal.natCast_ne_top m
    set ρ : ℝ≥0∞ := 1 - if Good a b then ENNReal.ofReal L else 0
    have hρ1 : ρ ≤ 1 := tsub_le_self
    have hρk : (ρ ^ ka).toReal ≤ (1 - L) ^ ka + (if Good a b then 0 else 1 : ℝ) := by
      rw [ENNReal.toReal_pow]
      by_cases hG : Good a b
      · simp only [ρ, hG, if_true, add_zero]
        rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 hL1) ENNReal.one_ne_top,
          ENNReal.toReal_one, ENNReal.toReal_ofReal hL0]
      · simp only [ρ, hG, if_false, tsub_zero, ENNReal.toReal_one, one_pow]
        have : 0 ≤ (1 - L) ^ ka := pow_nonneg (by linarith) ka
        linarith
    unfold hedgeError
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top (hn _) (hn _))) hc, ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hn _, ENNReal.one_ne_top⟩)
            (hn _)) (ENNReal.mul_ne_top (hn _) (hn _))) hc⟩)
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hn _))
          (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hρ1))),
      ENNReal.toReal_add (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top (hn _) (hn _))) hc) (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hn _, ENNReal.one_ne_top⟩)
            (hn _)) (ENNReal.mul_ne_top (hn _) (hn _))) hc)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_add (hn _) ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_pow] at hρk
    have hQ : (0 : ℝ) ≤ 2 * Q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hρk hQ]
  refine (Finset.expect_le_expect fun a _ => Finset.expect_le_expect fun b _ => hpt a b).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  exact le_rfl

end MaskedSigner

end HedgedGame

end GordieHowe.Ring
