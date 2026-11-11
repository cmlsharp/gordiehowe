-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFOracleSide
public import GordieHowe.Foundations.ToMathlib.PMFFiber

public section

/-!
# A signer's loop against one random function

The signer's attempt reads its challenge from a function `H : V → C` drawn once
(`oracleAttempt`): `y ← P`, reject unless `acc y (H (w1 y))`, keep `w1 y` with probability
`κ (w1 y, H (w1 y))`. The prover draws `H` uniformly and loops (`oracleProver`).

* `oracleKernel`: given the kept `(v, c)`, a uniform `H` reprogrammed at `v` to `c`.
* `map_condSome_jointAttempt_oracleAttempt`: the accepted attempt against a uniform `H`, jointly
  with `H`, is the signer's fresh kept `(v, c)` (`freshAttempt`) followed by the kernel.
* `tvDist_oracleProver_le`: for every law `L` of `(v, c)`, the prover is within the oracle
  concentration term `oracleConc` and the distance of the fresh kept law from `L`, of `L`
  followed by the kernel.
* `jointAttempt_oracleAttempt_apply_none`: against a uniform `H`, one attempt rejects as often as
  the fresh attempt, since `H (w1 y)` is uniform and independent of `y`.
* `oracleConc_le`: the oracle concentration term is at most `√(δ / q̄) / 2`, with `δ` the largest
  probability of one commitment and `q̄` the keep probability of one attempt against a uniform
  `H` (`quenchedConc_le` with no side data and the unit keep factor, through
  `oracleAttempt_eq_quenchedAttempt`).

About Mathlib objects only.
-/

open Finset
open scoped ENNReal BigOperators

namespace PMF

variable {V C Y : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype Y] (P : PMF Y) (w1 : Y → V) (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞)
  (hκ : ∀ a, κ a ≤ 1)

/-- **One attempt against the function `H`**: `y ← P`, reject unless `acc y (H (w1 y))`, and keep
`w1 y` with probability `κ (w1 y, H (w1 y))`. -/
@[expose] noncomputable def oracleAttempt (H : V → C) : PMF (Option V) :=
  P.bind fun y =>
    if acc y (H (w1 y)) = true then keepOrReject (w1 y) (κ (w1 y, H (w1 y))) (hκ _)
    else pure none

omit [Fintype C] [DecidableEq C] [Nonempty C] in
/-- The attempt against `H` keeps `v` with probability `signerMass v (H v) · κ (v, H v)`. -/
theorem oracleAttempt_apply_some (H : V → C) (v : V) :
    oracleAttempt P w1 acc κ hκ H (some v) = signerMass P w1 acc v (H v) * κ (v, H v) := by
  rw [oracleAttempt, bind_apply, tsum_fintype, signerMass, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases hv : w1 y = v
  · subst hv
    by_cases ha : acc y (H (w1 y)) = true <;> simp [ha, keepOrReject_apply_some]
  · have hv' : v ≠ w1 y := Ne.symm hv
    split_ifs <;> first | (exfalso; tauto) | simp [keepOrReject_apply_some, hv']

/-- **The prover against a random function**: a uniform `H` drawn once, then attempts against `H`
until one keeps; the output is `H` with the kept commitment. -/
@[expose] noncomputable def oracleProver : PMF ((V → C) × Option V) :=
  loopForever (uniformOfFintype (V → C)) (oracleAttempt P w1 acc κ hκ)

/-- **The reprogramming kernel**: given `(v, c)`, a uniform `H` with its value at `v` set to `c`,
output with `v`. -/
@[expose] noncomputable def oracleKernel (vc : V × C) : PMF ((V → C) × Option V) :=
  (uniformOfFintype (V → C)).map fun H => (Function.update H vc.1 vc.2, some vc.1)

omit [Nonempty C] in
/-- The functions equal to `H` off `v`, with `H v = c`, are the updates at `v` to `c`; there are
`|C|` of them. -/
theorem card_update_eq (v : V) (c : C) (H : V → C) :
    (univ.filter fun H₀ : V → C => Function.update H₀ v c = H).card =
      if H v = c then Fintype.card C else 0 := by
  classical
  split_ifs with hc
  · rw [← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun H₀ => H₀.1 v
        invFun := fun a => ⟨Function.update H v a, by
          rw [Function.update_idem]; subst hc; exact Function.update_eq_self _ _⟩
        left_inv := fun H₀ => Subtype.ext (by
          funext x
          by_cases hx : x = v
          · subst hx; simp
          · show Function.update H v (H₀.1 v) x = H₀.1 x
            rw [Function.update_of_ne hx]
            exact (congrFun H₀.2 x).symm.trans (Function.update_of_ne hx _ _))
        right_inv := fun a => by simp }
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro H₀ _ h
    exact hc (by rw [← h, Function.update_self])

/-- The kernel at `(v, c)` puts mass `|C| / |V → C|` on every `(H, some v)` with `H v = c`. -/
theorem oracleKernel_apply (vc : V × C) (H : V → C) (o : Option V) :
    oracleKernel vc (H, o) = if o = some vc.1 ∧ H vc.1 = vc.2 then
      (Fintype.card C : ℝ≥0∞) * (Fintype.card (V → C) : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [oracleKernel, map_apply, tsum_fintype]
  simp only [Prod.mk.injEq, uniformOfFintype_apply]
  by_cases ho : o = some vc.1
  · subst ho
    simp only [and_true, true_and]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    simp_rw [eq_comm (a := H)]
    rw [card_update_eq]
    split_ifs <;> simp
  · simp [ho]

/-- **The oracle concentration term** of the prover against a random function:
`E_H[(q H / q̄ - 1)⁺]`, with `q H` the keep probability of one attempt against `H` and `q̄` its
average over a uniform `H`. -/
noncomputable def oracleConc : ℝ :=
  (∑ H, uniformOfFintype (V → C) H *
    ((1 - oracleAttempt P w1 acc κ hκ H none) /
      (1 - jointAttempt (uniformOfFintype _) (oracleAttempt P w1 acc κ hκ) none) - 1)).toReal

omit [DecidableEq C] [Fintype Y] in
/-- The oracle concentration term is nonnegative. -/
theorem oracleConc_nonneg : 0 ≤ oracleConc P w1 acc κ hκ := by
  unfold oracleConc
  exact ENNReal.toReal_nonneg

omit [DecidableEq C] [Nonempty C] in
/-- **A uniform function read at one point**, against a weight: `∑_H u(H) F(H v) = ∑_c u(c) F(c)`
(`uniformOfFintype_map_eval`). -/
theorem sum_uniformOfFintype_mul_eval [Nonempty C] (v : V) (F : C → ℝ≥0∞) :
    ∑ H : V → C, uniformOfFintype (V → C) H * F (H v) = ∑ c, uniformOfFintype C c * F c := by
  classical
  rw [← uniformOfFintype_map_eval (E := V) (C := C) v]
  simp only [map_apply, tsum_fintype, sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Against a uniform function, one attempt rejects as often as the fresh attempt**: the
challenge `H (w1 y)` of a uniform `H` is uniform and independent of `y`. -/
theorem jointAttempt_oracleAttempt_apply_none :
    jointAttempt (uniformOfFintype (V → C)) (oracleAttempt P w1 acc κ hκ) none =
      freshAttempt P w1 acc κ hκ none := by
  have h : 1 - jointAttempt (uniformOfFintype (V → C)) (oracleAttempt P w1 acc κ hκ) none =
      1 - freshAttempt P w1 acc κ hκ none := by
    rw [← sum_apply_some, ← sum_apply_some, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [jointAttempt_apply_some, oracleAttempt_apply_some, freshAttempt_apply_some]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun v _ => ?_
    refine (sum_uniformOfFintype_mul_eval v fun c => signerMass P w1 acc v c * κ (v, c)).trans ?_
    refine sum_congr rfl fun c _ => ?_
    rw [uniformOfFintype_apply]
    ring
  exact (ENNReal.sub_right_inj ENNReal.one_ne_top (coe_le_one _ _) (coe_le_one _ _)).1 h

/-- **The accepted attempt against a uniform function splits**: jointly with `H`, the accepted
commitment is the fresh kept `(v, c)` followed by the reprogramming kernel. -/
theorem map_condSome_jointAttempt_oracleAttempt
    (h : jointAttempt (uniformOfFintype _) (oracleAttempt P w1 acc κ hκ) none ≠ 1)
    (h' : freshAttempt P w1 acc κ hκ none ≠ 1) :
    (condSome (jointAttempt (uniformOfFintype _) (oracleAttempt P w1 acc κ hκ)) h).map
        (fun z => (z.1, some z.2)) =
      (condSome (freshAttempt P w1 acc κ hκ) h').bind oracleKernel := by
  refine eq_of_apply_eq_mul (F := fun x => x.2.elim 0 fun v =>
      signerMass P w1 acc v (x.1 v) * κ (v, x.1 v))
    (a := (Fintype.card (V → C) : ℝ≥0∞)⁻¹ *
      (1 - jointAttempt (uniformOfFintype _) (oracleAttempt P w1 acc κ hκ) none)⁻¹)
    (b := (Fintype.card C : ℝ≥0∞)⁻¹ * (1 - freshAttempt P w1 acc κ hκ none)⁻¹ *
      ((Fintype.card C : ℝ≥0∞) * (Fintype.card (V → C) : ℝ≥0∞)⁻¹)) ?_ ?_
  · rintro ⟨H, o⟩
    cases o with
    | none => simp only [Option.elim_none, mul_zero]; exact map_pair_some_apply_none _ H
    | some v =>
      simp only [Option.elim_some]
      rw [map_pair_some_apply_some, condSome_apply, jointAttempt_apply_some,
        uniformOfFintype_apply, oracleAttempt_apply_some]
      simp only [div_eq_mul_inv]
      ring
  · rintro ⟨H, o⟩
    rw [bind_apply, tsum_fintype, Fintype.sum_prod_type]
    cases o with
    | none =>
      simp only [Option.elim_none, mul_zero, oracleKernel_apply, reduceCtorEq, false_and,
        ite_false, sum_const_zero]
    | some v =>
      simp only [Option.elim_some, oracleKernel_apply, Option.some.injEq]
      rw [sum_eq_single v (fun v' _ hv' => sum_eq_zero fun c _ => by
        rw [ite_eq_right fun h => hv' h.1.symm, mul_zero]) (by simp),
        sum_eq_single (H v) (fun c _ hc => by rw [ite_eq_right fun h => hc h.2.symm, mul_zero])
        (by simp), ite_eq_left ⟨rfl, rfl⟩, condSome_apply, freshAttempt_apply_some]
      simp only [div_eq_mul_inv]
      ring

/-- **The attempt against a uniform function keeps** as soon as the fresh attempt does. -/
theorem jointAttempt_oracleAttempt_ne_one (h' : freshAttempt P w1 acc κ hκ none ≠ 1) :
    jointAttempt (uniformOfFintype _) (oracleAttempt P w1 acc κ hκ) none ≠ 1 := by
  classical
  have hs : ∑ a, freshAttempt P w1 acc κ hκ (some a) ≠ 0 := by
    rw [sum_apply_some]; exact one_sub_apply_none_ne_zero h'
  obtain ⟨⟨v, c⟩, -, hvc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  rw [freshAttempt_apply_some] at hvc
  have hmk : signerMass P w1 acc v c * κ (v, c) ≠ 0 := fun h0 => hvc (by
    rw [mul_right_comm, h0, zero_mul])
  refine jointAttempt_apply_none_ne_one (θ₀ := fun _ => c) (by simp) fun h1 => ?_
  have hz := sum_apply_some (oracleAttempt P w1 acc κ hκ fun _ => c)
  rw [h1, tsub_self] at hz
  have := (Finset.sum_eq_zero_iff.1 hz) v (mem_univ _)
  rw [oracleAttempt_apply_some] at this
  exact hmk this

/-- **The prover against a random function, against any target**: if the signer's fresh attempt
keeps with positive probability, the prover is within the oracle concentration term and the
distance of the fresh kept law of `(v, c)` from `L`, of `L` followed by the reprogramming
kernel. -/
theorem tvDist_oracleProver_le (L : PMF (V × C)) (h' : freshAttempt P w1 acc κ hκ none ≠ 1) :
    tvDist (oracleProver P w1 acc κ hκ) (L.bind oracleKernel) ≤
      oracleConc P w1 acc κ hκ + tvDist (condSome (freshAttempt P w1 acc κ hκ) h') L := by
  have h := jointAttempt_oracleAttempt_ne_one P w1 acc κ hκ h'
  refine (tvDist_triangle _ _ _).trans (add_le_add (tvDist_loopForever_le _ _ h) ?_)
  rw [map_condSome_jointAttempt_oracleAttempt P w1 acc κ hκ h h']
  exact tvDist_bind_right_le _ _ _

section Concentration

/-- Functions on `V` as functions on `V` with no side data. -/
def unitSideEquiv (V C : Type*) : (V → C) ≃ (V → C × Unit) where
  toFun H v := (H v, ())
  invFun F v := (F v).1
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unit keep factor with no side data. -/
def unitKeep (V C : Type*) : V × C × Unit → ℝ≥0∞ := fun _ => 1

theorem unitKeep_le_one (V C : Type*) (a : V × C × Unit) : unitKeep V C a ≤ 1 := le_rfl

omit [Fintype C] [DecidableEq C] [Nonempty C] in
/-- **The attempt against one function is the core attempt** with no side data and the unit keep
factor. -/
theorem oracleAttempt_eq_quenchedAttempt (H : V → C) :
    oracleAttempt P w1 acc κ hκ H =
      quenchedAttempt P w1 acc κ hκ (unitKeep V C) (unitKeep_le_one V C) (unitSideEquiv V C H) := by
  refine eq_of_apply_some_eq fun v => ?_
  rw [oracleAttempt_apply_some, quenchedAttempt_apply_some, unitKeep, mul_one]
  rfl

omit [DecidableEq C] in
/-- **The oracle concentration term is the core's** with no side data and the unit keep factor. -/
theorem oracleConc_eq_quenchedConc :
    oracleConc P w1 acc κ hκ = quenchedConc P w1 acc κ hκ (unitKeep V C) (unitKeep_le_one V C) := by
  have hA : oracleAttempt P w1 acc κ hκ = fun H => quenchedAttempt P w1 acc κ hκ (unitKeep V C)
      (unitKeep_le_one V C) (unitSideEquiv V C H) :=
    funext (oracleAttempt_eq_quenchedAttempt P w1 acc κ hκ)
  rw [oracleConc, quenchedConc, hA, jointAttempt_comp_equiv_apply_none (unitSideEquiv V C)]
  beta_reduce
  exact congrArg ENNReal.toReal (sum_uniformOfFintype_comp_equiv (unitSideEquiv V C) fun F =>
    (1 - quenchedAttempt P w1 acc κ hκ (unitKeep V C) (unitKeep_le_one V C) F none) /
      (1 - jointAttempt (uniformOfFintype _)
        (quenchedAttempt P w1 acc κ hκ (unitKeep V C) (unitKeep_le_one V C)) none) - 1)

omit [DecidableEq C] in
/-- **The oracle concentration term is at most `√(δ / q̄) / 2`**, with `δ` the largest probability
of one commitment and `q̄` the keep probability of one attempt against a uniform function
(`quenchedConc_le` with no side data). -/
theorem oracleConc_le {δ : ℝ} (hδ : ∀ v, (P.map w1 v).toReal ≤ δ)
    (h : jointAttempt (uniformOfFintype (V → C)) (oracleAttempt P w1 acc κ hκ) none ≠ 1) :
    oracleConc P w1 acc κ hκ ≤
      √(δ / (1 - jointAttempt (uniformOfFintype (V → C)) (oracleAttempt P w1 acc κ hκ)
        none).toReal) / 2 := by
  have hA : oracleAttempt P w1 acc κ hκ = fun H => quenchedAttempt P w1 acc κ hκ (unitKeep V C)
      (unitKeep_le_one V C) (unitSideEquiv V C H) :=
    funext (oracleAttempt_eq_quenchedAttempt P w1 acc κ hκ)
  rw [hA, jointAttempt_comp_equiv_apply_none (unitSideEquiv V C)] at h ⊢
  rw [oracleConc_eq_quenchedConc]
  exact quenchedConc_le P w1 acc κ hκ _ _ hδ h

end Concentration

end PMF
