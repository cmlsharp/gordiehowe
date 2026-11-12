-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Anonymity
public import GordieHowe.Foundations.ToMathlib.PMFUniformPullback
public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched
public import GordieHowe.Foundations.ToMathlib.PMFRejection
public import GordieHowe.Foundations.ToMathlib.PMFUniform
public import GordieHowe.Model.ROM.Lazy

@[expose] public section

/-!
# Laws for hedged signing with a mask oracle

Facts about laws that the hedged ML-DSA signer of the ring publishing `w₁` uses: FIPS 204
Algorithm 7 reads its masks from a random oracle at a fresh nonce (`ρ'' = H(K ‖ rnd ‖ µ)`,
`y = ExpandMask(ρ'', κ)`, with `H` and ExpandMask together a random oracle on `(rnd, point)`).

- `PMF.etv`, `PMF.etv_triangle`, `PMF.etv_bind_left_le`, `PMF.etv_bind_right_le`,
  `PMF.toOuterMeasure_le_add_etv`: the expected total variation of two laws and its calculus.
- `PMF.RingPair.massAt_sub_dev_le`, `PMF.keep_ge_of_familyBound_lt`: a lower bound on the keep
  probability of one ring attempt from the family bound.
- `PMF.firstOf`, `PMF.firstSome_bind_contWith_untilSome`, `PMF.untilSome_firstSome_bind`: bounded
  loops with given attempts, and the unbounded loop unrolled.
- `PMF.weightedAttemptMasks`, `PMF.untilSome_uniform_bind_weightedAttemptMasks`,
  `PMF.uniform_bind_weightedAttemptMasks_none_le`: one call of the base signer with `T` given masks
  (the first that passes), then the ring signer's coin; with uniform masks its unbounded loop is the
  ideal-mask loop.
- `PMF.pi_bind_coord`, `PMF.pi_bind_apply_coord`, `PMF.uniformOfFintype_prod_apply`,
  `sum_uniform_curry`, `sum_uniform_prod`, `sum_uniform_const`, `sum_uniform_prod_pow`: product
  laws and uniform sums.
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
theorem RingPair.massAt_sub_dev_le (R : RingPair K V C) [Fintype R.Mem] [DecidableEq R.Mem]
    (b : Bool) (G : K × V → C) :
    (R.signer b).β * R.massAt G - R.dev b G ≤ (1 - R.attempt b G none).toReal := by
  rw [← sum_toReal_apply_some]
  unfold RingPair.massAt RingPair.dev weightedDev RingWeights.weightMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  have := neg_abs_le ((R.attempt b G (some v)).toReal -
    (R.signer b).β * ((R.wts).ringWeight (ringOf R.pt G) v : ℝ≥0∞).toReal)
  unfold RingPair.attempt at this ⊢
  linarith

variable {M : Type} [Fintype M] [Nonempty M] (R : M → RingPair K V C) [∀ m, Fintype (R m).Mem]
  [∀ m, DecidableEq (R m).Mem] [∀ m b, Fintype ((R m).signer b).Y] {θ : ℝ}

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


end SeqRun

/-! ### Masks read from an oracle at a fresh nonce -/


/-! ### Nonces drawn up front, and the swap of their slices -/

section Swap

variable {Rnd Pt Mask : Type} [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Pt]
  [DecidableEq Pt] [Fintype Mask] [Nonempty Mask] [DecidableEq Mask] {Q k : ℕ}


/-- Averages over curried nonces are averages over uncurried ones. -/
theorem sum_uniform_curry (g : (Fin Q → Fin k → Rnd) → ℝ≥0∞) :
    ∑ ρ : Fin Q → Fin k → Rnd, PMF.uniformOfFintype _ ρ * g ρ =
      ∑ σ : Fin Q × Fin k → Rnd, PMF.uniformOfFintype _ σ * g (Function.curry σ) := by
  have hc : Fintype.card (Fin Q → Fin k → Rnd) = Fintype.card (Fin Q × Fin k → Rnd) :=
    Fintype.card_congr (Equiv.curry _ _ _).symm
  simp only [PMF.uniformOfFintype_apply, hc]
  exact (Fintype.sum_equiv (Equiv.curry (Fin Q) (Fin k) Rnd) _ _ fun σ => rfl).symm


end Swap

/-! ### Two-sided bounds -/


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


/-! ### The game in rounds -/

section GameRounds

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι}
  {Mg : Merges τ} {nr : ι → ℕ} {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n Q : ℕ}


/-- **One coordinate of a product law**, as laws: binding a function of coordinate `j` over a
product law is binding it over the coordinate's law. -/
theorem _root_.PMF.pi_bind_apply_coord {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {δ : ι' → Type*}
    [∀ i, Fintype (δ i)] [∀ i, DecidableEq (δ i)] {γ : Type*} (ν : ∀ i, PMF (δ i)) (j : ι')
    (G : δ j → PMF γ) : (PMF.pi ν).bind (fun T => G (T j)) = (ν j).bind G := by
  ext x
  simp only [PMF.bind_apply, tsum_fintype]
  exact PMF.sum_pi_mul_apply_coord ν j fun b => G b x


end GameRounds

/-! ### Hedged ring signers -/


/-! ### Anonymity of the hedged signer -/


end GordieHowe.Ring
