-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFReprogram

@[expose] public section

/-!
# Rejection loops against a shared random function

Rejection loops whose attempts all read one random parameter `θ ← μ` (a random oracle, drawn
once), output jointly with `θ`, against the law of one attempt conditioned on acceptance, jointly
with `θ` (`condSome (jointAttempt μ A)`):

- `tvDist_loopForever_le`: the unbounded loop (`untilSome`, `loopForever`) is within the
  concentration term `E_θ[(q θ / q̄ - 1)⁺]`, with `q θ` the acceptance probability of one attempt
  given `θ` and `q̄` its average;
- `tvDist_loopWith_le`: the loop bounded by `n` attempts (`loopWith`) is within that term plus the
  averaged rejection term `E_θ[A θ none ^ n]`.

The concentration term is there because the rejected attempts read `θ` too, so the oracle is
biased at the points of rejected attempts.

Ring rejection against a uniform function `H : N × V → C` (`ringAttempt`): an attempt draws `y`,
reads the challenge `H (i, w1 y)` of member `i`, rejects unless `acc` accepts and every other
member `j` has `H (j, w1 y)` off its excluded set (`ExclSets`), and keeps `w1 y` with a coin.

- `map_condSome_jointAttempt_ringAttempt`: the accepted `(H, v)` is the accepted `(v, c)` of the
  same attempt with a fresh uniform challenge (`freshAttempt`), followed by a uniform `H` with
  `H (i, v) = c` and the other members' values at `v` uniform off their excluded sets
  (`ringKernel`, built from `slotLaw`);
- `ringTarget_eq_bind_ringKernel`: the target (`v` uniform, `H` uniform with every member's value
  at `v` uniform off its excluded set) is the same kernel after `v` uniform and `c` uniform off
  member `i`'s set (`signerTarget`); `ringTarget_of_excl_eq_empty`: with no excluded sets it is a
  uniform `H` independent of a uniform `v`;
- `tvDist_ringProver_ringTarget_le`: the unbounded ring loop (`ringProver`) is within the
  concentration term (`oracleConcError`) and the distance of the signer's accepted `(v, c)` from
  `signerTarget`, provided the signer's fresh attempt keeps with positive probability
  (`jointAttempt_ringAttempt_ne_one`: then so does the ring attempt);
- `oracleConcError_le`: the concentration term is at most `√(δ / q̄) / 2` when every value
  `w1 y = v` has probability at most `δ` (two columns of a uniform function are independent,
  `sum_uniform_column_mul`, so the variance of `q H` is at most `δ · q̄`);
- `tvDist_condSomeOr_freshAttempt_flatten_le`: if the fresh attempt's accepted mass is
  proportional to `u · w`, flattening with the coin `min 1 (β / w)` brings its accepted law within
  `∑ u · (β - w) / ∑ u · min w β` of `u` (`FlattenHyp.tvDist_condSome_thin_le`).

About Mathlib objects only; a candidate for upstreaming with
`GordieHowe/Foundations/ToMathlib/PMFRejection.lean`.
-/

open Finset
open scoped BigOperators ENNReal

namespace PMF

section Proportional

variable {α : Type*} [Fintype α]

/-- **Two laws proportional to one weight are equal.** -/
theorem eq_of_apply_eq_mul {p q : PMF α} {F : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hp : ∀ x, p x = a * F x) (hq : ∀ x, q x = b * F x) : p = q := by
  have h1 : a * ∑ x, F x = 1 := by
    rw [mul_sum, ← sum_coe p]; exact sum_congr rfl fun x _ => (hp x).symm
  have h2 : b * ∑ x, F x = 1 := by
    rw [mul_sum, ← sum_coe q]; exact sum_congr rfl fun x _ => (hq x).symm
  have hF0 : ∑ x, F x ≠ 0 := fun h => by simp [h] at h1
  have hFt : ∑ x, F x ≠ ⊤ := fun h => by
    rw [h] at h1
    rcases eq_or_ne a 0 with ha | ha
    · simp [ha] at h1
    · simp [ENNReal.mul_top ha] at h1
  have hab : a = b := (ENNReal.mul_left_inj hF0 hFt).1 (h1.trans h2.symm)
  ext x
  rw [hp, hq, hab]

/-- The law of an attempt conditioned on acceptance, or `d` if the attempt always rejects. -/
noncomputable def condSomeOr (A : PMF (Option α)) (d : PMF α) : PMF α :=
  if h : A none = 1 then d else condSome A h

theorem condSomeOr_of_ne {A : PMF (Option α)} (d : PMF α) (h : A none ≠ 1) :
    condSomeOr A d = condSome A h :=
  dite_eq_right_of_eq_false (eq_false h)

end Proportional

section MapPair

variable {β γ : Type*} [DecidableEq γ]

/-- Pairing with a constant second component puts the mass of `x` on `(x, c₀)`. -/
theorem map_pair_const_apply (p : PMF β) (c₀ : γ) (x : β) (c : γ) :
    p.map (fun b => (b, c₀)) (x, c) = if c = c₀ then p x else 0 := by
  rw [map_apply]
  split_ifs with hc
  · subst hc
    rw [tsum_eq_single x fun b hb => by simp [Ne.symm hb]]
    simp
  · exact ENNReal.tsum_eq_zero.2 fun b => by simp [hc]

/-- Pairing with a constant first component puts the mass of `x` on `(θ₀, x)`. -/
theorem map_const_pair_apply (p : PMF β) (θ₀ : γ) (θ : γ) (x : β) :
    p.map (Prod.mk θ₀) (θ, x) = if θ = θ₀ then p x else 0 := by
  rw [map_apply]
  split_ifs with hc
  · subst hc
    rw [tsum_eq_single x fun b hb => by simp [Ne.symm hb]]
    simp
  · exact ENNReal.tsum_eq_zero.2 fun b => by simp [hc]

omit [DecidableEq γ] in
/-- Tagging the second component with `some` keeps the mass of `(θ, a)` on `(θ, some a)`. -/
theorem map_pair_some_apply_some {α : Type*} [Fintype γ] [Fintype α] (p : PMF (γ × α)) (θ : γ)
    (a : α) : p.map (fun z => (z.1, some z.2)) (θ, some a) = p (θ, a) := by
  classical
  rw [map_apply, tsum_fintype]
  refine (Finset.sum_eq_single (θ, a) (fun z _ hz => ite_eq_right_of_eq_false _ _
    (eq_false fun he => hz (by
      obtain ⟨h1, h2⟩ := Prod.mk.inj he
      exact Prod.ext h1.symm (Option.some_injective _ h2).symm)))
    (fun h => absurd (mem_univ _) h)).trans ?_
  exact ite_eq_left_of_eq_true _ _ (eq_true rfl)

omit [DecidableEq γ] in
/-- Tagging the second component with `some` puts no mass on `none`. -/
theorem map_pair_some_apply_none {α : Type*} (p : PMF (γ × α)) (θ : γ) :
    p.map (fun z => (z.1, some z.2)) (θ, none) = 0 := by
  rw [map_apply]; exact ENNReal.tsum_eq_zero.2 fun z => by simp

end MapPair

section SharedLoop

variable {Θ α : Type*}

/-- **One attempt jointly with its parameter**: `θ ← μ`, then an attempt of law `A θ`, the
accepted value paired with `θ`. -/
noncomputable def jointAttempt (μ : PMF Θ) (A : Θ → PMF (Option α)) : PMF (Option (Θ × α)) :=
  μ.bind fun θ => (A θ).map (Option.map (Prod.mk θ))

/-- **The bounded loop jointly with a shared parameter**: `θ ← μ` once, then up to `n` independent
attempts of law `A θ`; the output is `θ` with the first accepted value, or `none`. -/
noncomputable def loopWith (μ : PMF Θ) (A : Θ → PMF (Option α)) (n : ℕ) :
    PMF (Θ × Option α) :=
  μ.bind fun θ => (firstSome (A θ) n).map (Prod.mk θ)

/-- The joint attempt accepts `(θ, a)` with probability `μ θ · A θ (some a)`. -/
theorem jointAttempt_apply_some (μ : PMF Θ) (A : Θ → PMF (Option α)) (θ : Θ) (a : α) :
    jointAttempt μ A (some (θ, a)) = μ θ * A θ (some a) := by
  classical
  rw [jointAttempt, bind_apply, tsum_eq_single θ fun θ' hθ' => ?_]
  · congr 1
    rw [map_apply, tsum_eq_single (some a) fun o ho => ?_]
    · simp
    · cases o with
      | none => simp
      | some b => simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
                  exact ite_eq_right_of_eq_false _ _ (eq_false fun h => ho (by rw [h]))
  · rw [map_apply, ENNReal.tsum_eq_zero.2 fun o => ?_, mul_zero]
    cases o with
    | none => simp
    | some b => simp [Ne.symm hθ']

/-- The joint attempt rejects with probability `∑ θ, μ θ · A θ none`. -/
theorem jointAttempt_apply_none [Fintype Θ] (μ : PMF Θ) (A : Θ → PMF (Option α)) :
    jointAttempt μ A none = ∑ θ, μ θ * A θ none := by
  rw [jointAttempt, bind_apply, tsum_fintype]
  refine sum_congr rfl fun θ _ => ?_
  congr 1
  rw [map_apply, tsum_eq_single none fun o ho => ?_]
  · simp
  · cases o with
    | none => exact absurd rfl ho
    | some b => simp

/-- The loop outputs `(θ, o)` with probability `μ θ · firstSome (A θ) n o`. -/
theorem loopWith_apply (μ : PMF Θ) (A : Θ → PMF (Option α)) (n : ℕ) (θ : Θ) (o : Option α) :
    loopWith μ A n (θ, o) = μ θ * firstSome (A θ) n o := by
  classical
  rw [loopWith, bind_apply, tsum_eq_single θ fun θ' hθ' => ?_]
  · rw [map_const_pair_apply, ite_eq_left_of_eq_true _ _ (eq_self θ)]
  · rw [map_const_pair_apply, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hθ')), mul_zero]

/-- **A bounded loop with a shared parameter against one conditioned attempt**: the loop over at
most `n` attempts of law `A θ`, with `θ ← μ` drawn once, is within the averaged rejection term
`E_θ[A θ none ^ n]` and the concentration term `E_θ[(q θ / q̄ - 1)⁺]` of the joint attempt
conditioned on acceptance, with `q θ = 1 - A θ none` and `q̄ = 1 - jointAttempt μ A none`. -/
theorem tvDist_loopWith_le [Fintype Θ] [Fintype α] (μ : PMF Θ) (A : Θ → PMF (Option α)) (n : ℕ)
    (h : jointAttempt μ A none ≠ 1) :
    tvDist (loopWith μ A n)
        ((condSome (jointAttempt μ A) h).map fun z => (z.1, some z.2)) ≤
      (∑ θ, μ θ * A θ none ^ n).toReal +
        (∑ θ, μ θ * ((1 - A θ none) / (1 - jointAttempt μ A none) - 1)).toReal := by
  classical
  set s := 1 - jointAttempt μ A none with hs
  have hs0 : s ≠ 0 := one_sub_apply_none_ne_zero h
  have hfin1 : ∑ θ, μ θ * A θ none ^ n ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun θ _ =>
      ENNReal.mul_ne_top (μ.apply_ne_top θ) (ENNReal.pow_ne_top ((A θ).apply_ne_top none))
  have hfin2 : ∑ θ, μ θ * ((1 - A θ none) / s - 1) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun θ _ =>
      ENNReal.mul_ne_top (μ.apply_ne_top θ)
        (ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top hs0)
          (tsub_le_self.trans (ENNReal.div_le_div_right tsub_le_self _)))
  have hM : ∀ θ a, ((condSome (jointAttempt μ A) h).map fun z => (z.1, some z.2)) (θ, some a) =
      μ θ * A θ (some a) * s⁻¹ := fun θ a => by
    rw [map_pair_some_apply_some, condSome_apply, jointAttempt_apply_some, div_eq_mul_inv]
  have hM0 : ∀ θ, ((condSome (jointAttempt μ A) h).map fun z => (z.1, some z.2)) (θ, none) =
      0 := fun θ => map_pair_some_apply_none _ θ
  rw [tvDist_comm, tvDist_eq_toReal_tsum_tsub, tsum_fintype, ← ENNReal.toReal_add hfin1 hfin2]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) ?_
  rw [Fintype.sum_prod_type, ← sum_add_distrib]
  refine sum_le_sum fun θ _ => ?_
  rw [Fintype.sum_option, hM0, zero_tsub, zero_add]
  simp only [hM, loopWith_apply, firstSome_apply_some]
  set r := A θ none
  set G := ∑ k ∈ range n, r ^ k
  have hq : ∑ a, A θ (some a) = 1 - r := sum_apply_some (A θ)
  have hqG : (1 - r) * G = 1 - r ^ n := by
    have := sum_apply_some (firstSome (A θ) n)
    rw [firstSome_apply_none] at this
    simp only [firstSome_apply_some, ← sum_mul, hq] at this
    exact this
  have hterm : ∀ a, μ θ * A θ (some a) * s⁻¹ - μ θ * (A θ (some a) * G) =
      μ θ * A θ (some a) * (s⁻¹ - G) := fun a => by
    rw [ENNReal.mul_sub fun _ _ => ENNReal.mul_ne_top (μ.apply_ne_top θ)
      ((A θ).apply_ne_top _), ← mul_assoc]
  simp only [hterm, ← sum_mul, ← mul_sum, hq]
  have hr1 : r ^ n ≤ 1 := pow_le_one₀ bot_le ((A θ).coe_le_one none)
  have hkey : (1 - r) * (s⁻¹ - G) ≤ r ^ n + ((1 - r) / s - 1) := by
    rw [ENNReal.mul_sub fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self, hqG,
      ← div_eq_mul_inv]
    calc (1 - r) / s - (1 - r ^ n) ≤ ((1 - r) / s - 1) + (1 - (1 - r ^ n)) :=
          tsub_le_tsub_add_tsub
      _ = r ^ n + ((1 - r) / s - 1) := by
          rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hr1, add_comm]
  calc μ θ * (1 - r) * (s⁻¹ - G) = μ θ * ((1 - r) * (s⁻¹ - G)) := mul_assoc _ _ _
    _ ≤ μ θ * (r ^ n + ((1 - r) / s - 1)) := by gcongr
    _ = μ θ * r ^ n + μ θ * ((1 - r) / s - 1) := mul_add _ _ _

/-- **The unbounded rejection loop**: repeat attempts of law `A` until one accepts, output the
accepted value; the law of the output is `condSome A`, the limit of the bounded loops
(`tvDist_firstSome_map_condSome`). If `A` always rejects the loop does not terminate, recorded as
`none`. -/
noncomputable def untilSome [Fintype α] (A : PMF (Option α)) : PMF (Option α) :=
  if h : A none = 1 then pure none else (condSome A h).map some

/-- **The unbounded loop jointly with a shared parameter**: `θ ← μ` once, then the unbounded loop
over attempts of law `A θ`, output with `θ`. -/
noncomputable def loopForever [Fintype α] (μ : PMF Θ) (A : Θ → PMF (Option α)) : PMF (Θ × Option α) :=
  μ.bind fun θ => (untilSome (A θ)).map (Prod.mk θ)

/-- The unbounded loop outputs `a` with probability `A (some a) / (1 - A none)`. -/
theorem untilSome_apply_some [Fintype α] (A : PMF (Option α)) (a : α) :
    untilSome A (some a) = A (some a) / (1 - A none) := by
  unfold untilSome
  split_ifs with h
  · have h0 : A (some a) = 0 := by
      have hs := sum_apply_some A
      rw [h, tsub_self] at hs
      exact (Finset.sum_eq_zero_iff.1 hs) a (mem_univ _)
    simp [h0]
  · rw [map_some_apply_some, condSome_apply]

/-- The unbounded loop with a shared parameter outputs `(θ, some a)` with probability
`μ θ · A θ (some a) / (1 - A θ none)`. -/
theorem loopForever_apply_some [Fintype α] (μ : PMF Θ) (A : Θ → PMF (Option α)) (θ : Θ) (a : α) :
    loopForever μ A (θ, some a) = μ θ * (A θ (some a) / (1 - A θ none)) := by
  classical
  rw [loopForever, bind_apply, tsum_eq_single θ fun θ' hθ' => by
    rw [map_const_pair_apply, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hθ')), mul_zero]]
  rw [map_const_pair_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), untilSome_apply_some]

/-- **An unbounded loop with a shared parameter against one conditioned attempt**: the distance
is at most the concentration term `E_θ[(q θ / q̄ - 1)⁺]`, with `q θ = 1 - A θ none` and
`q̄ = 1 - jointAttempt μ A none`. -/
theorem tvDist_loopForever_le [Fintype Θ] [Fintype α] (μ : PMF Θ) (A : Θ → PMF (Option α))
    (h : jointAttempt μ A none ≠ 1) :
    tvDist (loopForever μ A) ((condSome (jointAttempt μ A) h).map fun z => (z.1, some z.2)) ≤
      (∑ θ, μ θ * ((1 - A θ none) / (1 - jointAttempt μ A none) - 1)).toReal := by
  classical
  set s := 1 - jointAttempt μ A none with hs
  have hs0 : s ≠ 0 := one_sub_apply_none_ne_zero h
  have hfin : ∑ θ, μ θ * ((1 - A θ none) / s - 1) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun θ _ =>
      ENNReal.mul_ne_top (μ.apply_ne_top θ)
        (ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top hs0)
          (tsub_le_self.trans (ENNReal.div_le_div_right tsub_le_self _)))
  rw [tvDist_comm, tvDist_eq_toReal_tsum_tsub, tsum_fintype]
  refine ENNReal.toReal_mono hfin ?_
  rw [Fintype.sum_prod_type]
  refine sum_le_sum fun θ _ => ?_
  rw [Fintype.sum_option, map_pair_some_apply_none, zero_tsub, zero_add]
  simp only [map_pair_some_apply_some, condSome_apply, jointAttempt_apply_some,
    loopForever_apply_some]
  set r := A θ none
  have hq : ∑ a, A θ (some a) = 1 - r := sum_apply_some (A θ)
  by_cases hr : r = 1
  · have h0 : ∀ a, A θ (some a) = 0 := fun a => by
      have := hq; rw [hr, tsub_self] at this
      exact (Finset.sum_eq_zero_iff.1 this) a (mem_univ _)
    simp [h0]
  · have hr0 : 1 - r ≠ 0 := one_sub_apply_none_ne_zero hr
    have hterm : ∀ a, μ θ * A θ (some a) / s - μ θ * (A θ (some a) / (1 - r)) =
        μ θ * A θ (some a) * (s⁻¹ - (1 - r)⁻¹) := fun a => by
      rw [ENNReal.mul_sub fun _ _ => ENNReal.mul_ne_top (μ.apply_ne_top θ)
        ((A θ).apply_ne_top _), div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    rw [sum_congr rfl fun a _ => hterm a, ← sum_mul, ← mul_sum, hq]
    rw [mul_assoc, ENNReal.mul_sub fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self,
      ENNReal.mul_inv_cancel hr0 (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self),
      div_eq_mul_inv]

/-- The joint attempt does not always reject if some `θ` of positive mass does not. -/
theorem jointAttempt_apply_none_ne_one [Fintype Θ] {μ : PMF Θ} {A : Θ → PMF (Option α)} {θ₀ : Θ}
    (hμ : μ θ₀ ≠ 0) (hA : A θ₀ none ≠ 1) : jointAttempt μ A none ≠ 1 := by
  intro h
  have hlt : (jointAttempt μ A none).toReal < 1 := by
    rw [jointAttempt_apply_none, ENNReal.toReal_sum fun θ _ =>
      ENNReal.mul_ne_top (apply_ne_top _ _) (apply_ne_top _ _), ← sum_toReal μ]
    refine Finset.sum_lt_sum (fun θ _ => ENNReal.toReal_mono (apply_ne_top _ _)
      (mul_le_of_le_one_right' (coe_le_one _ _))) ⟨θ₀, mem_univ _, ?_⟩
    refine ENNReal.toReal_strict_mono (apply_ne_top _ _) ?_
    calc μ θ₀ * _ < μ θ₀ * 1 := by
          rw [mul_comm (μ θ₀), mul_comm (μ θ₀)]
          exact ENNReal.mul_lt_mul_left hμ (apply_ne_top _ _)
            (lt_of_le_of_ne (coe_le_one _ _) hA)
      _ = μ θ₀ := mul_one _
  rw [h] at hlt
  simp at hlt

end SharedLoop

section Ring

variable {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C]

/-! ### Uniform functions with constrained values at one column -/

/-- The allowed values of `H x` when every member's value at column `v` is constrained:
`H (j, v) ∈ F j`, and `H (j, v')` free for `v' ≠ v`. -/
def pointSlots (F : N → Finset C) (v : V) (x : N × V) : Finset C :=
  if x.2 = v then F x.1 else univ

omit [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq C] in
theorem pointSlots_nonempty [Nonempty C] {F : N → Finset C} (hF : ∀ j, (F j).Nonempty) (v : V)
    (x : N × V) : (pointSlots F v x).Nonempty := by
  unfold pointSlots
  split_ifs
  · exact hF _
  · exact univ_nonempty

/-- **A uniform function constrained at one column**: independent values, `H (j, v)` uniform on
`F j` and every other value uniform on `C`. -/
noncomputable def slotLaw [Nonempty C] (F : N → Finset C) (hF : ∀ j, (F j).Nonempty) (v : V) :
    PMF (N × V → C) :=
  pi fun x => uniformOfFinset (pointSlots F v x) (pointSlots_nonempty hF v x)

/-- The number of functions `slotLaw F hF v` is uniform on. -/
def slotCount (V : Type*) [Fintype V] (F : N → Finset C) : ℕ :=
  (∏ j, (F j).card) * Fintype.card C ^ ((Fintype.card V - 1) * Fintype.card N)

omit [DecidableEq N] [DecidableEq C] in
/-- The constrained functions number `slotCount F`, whatever the column. -/
theorem prod_card_pointSlots (F : N → Finset C) (v : V) :
    ∏ x, (pointSlots F v x).card = slotCount V F := by
  rw [Fintype.prod_prod_type, slotCount, pow_mul, ← card_univ (α := N), ← prod_const,
    ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [Fintype.prod_eq_mul_prod_compl v]
  simp only [pointSlots, ite_true]
  congr 1
  rw [prod_congr rfl fun v' hv' => by
    rw [if_neg (by simpa using hv')], prod_const, card_univ, card_compl, card_singleton]

/-- The law `slotLaw F hF v` is uniform on the functions with `H (j, v) ∈ F j` for every `j`. -/
theorem slotLaw_apply [Nonempty C] (F : N → Finset C) (hF : ∀ j, (F j).Nonempty) (v : V)
    (H : N × V → C) :
    slotLaw F hF v H = if ∀ j, H (j, v) ∈ F j then ((slotCount V F : ℝ≥0∞))⁻¹ else 0 := by
  have hiff : (∀ x, H x ∈ pointSlots F v x) ↔ ∀ j, H (j, v) ∈ F j := by
    constructor
    · intro h j
      simpa [pointSlots] using h (j, v)
    · rintro h ⟨j, v'⟩
      unfold pointSlots
      split_ifs with hx
      · simp only at hx; subst hx; exact h j
      · exact mem_univ _
  rw [slotLaw, pi_apply]
  by_cases hH : ∀ j, H (j, v) ∈ F j
  · rw [if_pos hH, ← prod_card_pointSlots F v, Nat.cast_prod, ENNReal.prod_inv_distrib
      fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _)]
    exact prod_congr rfl fun x _ => uniformOfFinset_apply_of_mem _ (hiff.2 hH x)
  · rw [if_neg hH]
    obtain ⟨x, hx⟩ := not_forall.1 fun h => hH (hiff.1 h)
    exact prod_eq_zero (mem_univ x) (uniformOfFinset_apply_of_notMem _ hx)

/-! ### Excluded sets and the ring attempt -/

/-- **Per-member excluded challenge sets**, each missing some challenge. -/
structure ExclSets (N C : Type*) [Fintype C] [DecidableEq C] where
  /-- The challenges excluded for member `j`. -/
  excl : N → Finset C
  /-- Some challenge is not excluded. -/
  compl_nonempty : ∀ j, (excl j)ᶜ.Nonempty

variable (E : ExclSets N C) (i : N)

/-- The constraints at column `v` given the signer's challenge `c`: `H (i, v) = c`, and
`H (j, v)` off member `j`'s excluded set for `j ≠ i`. -/
def signerSlots (c : C) : N → Finset C :=
  Function.update (fun j => (E.excl j)ᶜ) i {c}

omit [Fintype N] in
theorem signerSlots_nonempty (c : C) (j : N) : (signerSlots E i c j).Nonempty := by
  unfold signerSlots
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self]; exact singleton_nonempty c
  · rw [Function.update_of_ne hj]; exact E.compl_nonempty j

/-- The other members' challenges at column `v` miss their excluded sets. -/
def nonSignerPass (H : N × V → C) (v : V) : Prop :=
  ∀ j, j ≠ i → H (j, v) ∉ E.excl j

instance (H : N × V → C) (v : V) : Decidable (nonSignerPass E i H v) := by
  unfold nonSignerPass; infer_instance

omit [Fintype N] [Fintype V] [DecidableEq V] in
theorem forall_mem_signerSlots_iff (H : N × V → C) (v : V) (c : C) :
    (∀ j, H (j, v) ∈ signerSlots E i c j) ↔ H (i, v) = c ∧ nonSignerPass E i H v := by
  constructor
  · intro h
    refine ⟨by simpa [signerSlots] using h i, fun j hj => ?_⟩
    have := h j
    rw [signerSlots, Function.update_of_ne hj] at this
    simpa using this
  · rintro ⟨hc, hp⟩ j
    rcases eq_or_ne j i with rfl | hj
    · simp [signerSlots, hc]
    · rw [signerSlots, Function.update_of_ne hj]; simpa using hp j hj

omit [DecidableEq V] in
theorem slotCount_signerSlots (c c' : C) :
    slotCount V (signerSlots E i c) = slotCount V (signerSlots E i c') := by
  unfold slotCount
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rcases eq_or_ne j i with rfl | hj
  · simp [signerSlots]
  · simp [signerSlots, Function.update_of_ne hj]

omit [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] in
theorem forall_notMem_iff (H : N × V → C) (v : V) :
    (∀ j, H (j, v) ∉ E.excl j) ↔ H (i, v) ∉ E.excl i ∧ nonSignerPass E i H v :=
  ⟨fun h => ⟨h i, fun j _ => h j⟩, fun ⟨hi, hp⟩ j => by
    rcases eq_or_ne j i with rfl | hj
    · exact hi
    · exact hp j hj⟩

variable [Nonempty C] [Nonempty V]

/-- **The ring kernel**: given the accepted column `v` and signer challenge `c`, a uniform `H`
with `H (i, v) = c` and `H (j, v)` uniform off member `j`'s excluded set for `j ≠ i`, output
with `v`. -/
noncomputable def ringKernel (vc : V × C) : PMF ((N × V → C) × Option V) :=
  (slotLaw (signerSlots E i vc.2) (signerSlots_nonempty E i vc.2) vc.1).map fun H => (H, some vc.1)

variable (V) in
/-- **The ring target**: `v` uniform, and `H` uniform with every member's value at column `v`
uniform off its excluded set. -/
noncomputable def ringTarget : PMF ((N × V → C) × Option V) :=
  (uniformOfFintype V).bind fun v =>
    (slotLaw (fun j => (E.excl j)ᶜ) E.compl_nonempty v).map fun H => (H, some v)

/-- The signer's coordinates of the ring target: `v` uniform and `c` uniform off member `i`'s
excluded set. -/
noncomputable def signerTarget : PMF (V × C) :=
  (uniformOfFintype V).bind fun v =>
    (uniformOfFinset (E.excl i)ᶜ (E.compl_nonempty i)).map (Prod.mk v)

variable {Y : Type*} [Fintype Y] (P : PMF Y) (w1 : Y → V) (acc : Y → C → Bool)
  (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1)

/-- **One ring attempt against `H`**: draw `y ← P`, read the signer's challenge `H (i, w1 y)`,
reject unless `acc` accepts and every other member's challenge `H (j, w1 y)` misses its excluded
set, and keep `w1 y` with probability `κ (w1 y, H (i, w1 y))`. -/
noncomputable def ringAttempt (H : N × V → C) : PMF (Option V) :=
  P.bind fun y =>
    if acc y (H (i, w1 y)) = true ∧ nonSignerPass E i H (w1 y) then
      keepOrReject (w1 y) (κ (w1 y, H (i, w1 y))) (hκ _)
    else pure none

/-- **The ring prover**: a uniform `H` drawn once, then ring attempts until one keeps (the
unbounded loop of FIPS 204, Appendix C); the output is `H` with the kept `v`. -/
noncomputable def ringProver : PMF ((N × V → C) × Option V) :=
  loopForever (uniformOfFintype (N × V → C)) (ringAttempt E i P w1 acc κ hκ)

/-- **The signer's attempt with a fresh challenge**: `y ← P`, `c` uniform, and keep `(w1 y, c)`
with probability `κ (w1 y, c)` if `acc y c`. -/
noncomputable def freshAttempt : PMF (Option (V × C)) :=
  P.bind fun y => (uniformOfFintype C).bind fun c =>
    if acc y c = true then keepOrReject (w1 y, c) (κ (w1 y, c)) (hκ _) else pure none

/-- `Pr_{y ← P}[w1 y = v ∧ acc y c]`. -/
noncomputable def signerMass (v : V) (c : C) : ℝ≥0∞ :=
  ∑ y, if w1 y = v ∧ acc y c = true then P y else 0

/-- **The oracle concentration term**: `E_H[(q H / q̄ - 1)⁺]`, with `q H` the keep probability
of one ring attempt against the oracle `H` and `q̄` its average over a uniform `H`. -/
noncomputable def oracleConcError : ℝ :=
  (∑ H, uniformOfFintype (N × V → C) H *
    ((1 - ringAttempt E i P w1 acc κ hκ H none) /
      (1 - jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ) none) - 1)).toReal

omit [DecidableEq N] [DecidableEq C] [Nonempty C] in
theorem keepOrReject_apply_some {α : Type*} [Fintype α] [DecidableEq α] (a : α) (k : ℝ≥0∞)
    (hk : k ≤ 1) (b : α) : keepOrReject a k hk (some b) = if b = a then k else 0 :=
  rfl

omit [Nonempty C] [Nonempty V] in
/-- A ring attempt against `H` keeps `v` with probability
`signerMass v (H (i, v)) · κ (v, H (i, v))` if the other members pass, else `0`. -/
theorem ringAttempt_apply_some (H : N × V → C) (v : V) :
    ringAttempt E i P w1 acc κ hκ H (some v) =
      signerMass P w1 acc v (H (i, v)) * κ (v, H (i, v)) *
        (if nonSignerPass E i H v then 1 else 0) := by
  rw [ringAttempt, bind_apply, tsum_fintype, signerMass, sum_mul, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases hv : w1 y = v
  · subst hv
    by_cases ha : acc y (H (i, w1 y)) = true <;> by_cases hp : nonSignerPass E i H (w1 y) <;>
      simp [ha, hp, keepOrReject_apply_some]
  · have hv' : v ≠ w1 y := Ne.symm hv
    split_ifs <;> first | (exfalso; tauto) | simp [keepOrReject_apply_some, hv']

omit [Nonempty V] in
/-- A fresh attempt keeps `(v, c)` with probability `signerMass v c · |C|⁻¹ · κ (v, c)`. -/
theorem freshAttempt_apply_some (v : V) (c : C) :
    freshAttempt P w1 acc κ hκ (some (v, c)) =
      signerMass P w1 acc v c * (Fintype.card C : ℝ≥0∞)⁻¹ * κ (v, c) := by
  rw [freshAttempt, bind_apply, tsum_fintype, signerMass, sum_mul, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  rw [bind_apply, tsum_fintype, sum_eq_single c (fun c' _ hc' => by
    split_ifs <;> simp [keepOrReject_apply_some, Ne.symm hc']) (by simp), uniformOfFintype_apply]
  by_cases hv : w1 y = v
  · subst hv
    by_cases ha : acc y c = true <;> simp [ha, keepOrReject_apply_some]
    ring
  · by_cases ha : acc y c = true <;> simp [ha, hv, keepOrReject_apply_some, Ne.symm hv]

/-- With no excluded sets the constrained law is the uniform law on functions. -/
theorem slotLaw_univ :
    slotLaw (V := V) (fun _ : N => (univ : Finset C)) (fun _ => univ_nonempty) =
      fun _ => uniformOfFintype (N × V → C) := by
  funext v
  ext H
  rw [slotLaw_apply, if_pos fun _ => mem_univ _, uniformOfFintype_apply]
  congr 1
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos
  simp only [slotCount, card_univ, prod_const, Fintype.card_pi, Fintype.card_prod]
  rw [← pow_add, Nat.cast_pow, Nat.cast_pow]
  congr 1
  rw [Nat.sub_mul, one_mul, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left _ hV), mul_comm]

/-- **With no excluded sets the target is `v` uniform and an independent uniform oracle.** -/
theorem ringTarget_of_excl_eq_empty (hE : ∀ j, E.excl j = ∅) :
    ringTarget V E =
      (uniformOfFintype V).bind fun v => (uniformOfFintype (N × V → C)).map fun H => (H, some v) := by
  have hF : (fun j => (E.excl j)ᶜ) = fun _ : N => (univ : Finset C) := by
    funext j; rw [hE j, compl_empty]
  unfold ringTarget
  congr 1
  funext v
  congr 1
  have := congrFun (slotLaw_univ (N := N) (V := V) (C := C)) v
  rw [← this]
  congr 1

omit [Nonempty V] in
/-- The ring kernel at `(H, some v)`: the mass of the signer's challenge `c = H (i, v)`. -/
theorem bind_ringKernel_apply_some (L : PMF (V × C)) (H : N × V → C) (v : V) (c₀ : C) :
    L.bind (ringKernel E i) (H, some v) =
      L (v, H (i, v)) * (if nonSignerPass E i H v then 1 else 0) *
        ((slotCount V (signerSlots E i c₀) : ℝ≥0∞))⁻¹ := by
  have hoff : ∀ v', v' ≠ v → ∑ c, L (v', c) * ringKernel E i (v', c) (H, some v) = 0 :=
    fun v' hv' => sum_eq_zero fun c _ => by
      rw [ringKernel, map_pair_const_apply, if_neg fun h => hv' (Option.some_injective _ h).symm,
        mul_zero]
  have hoffc : ∀ c, c ≠ H (i, v) → L (v, c) * ringKernel E i (v, c) (H, some v) = 0 :=
    fun c hc => by
      rw [ringKernel, map_pair_const_apply, if_pos rfl, slotLaw_apply,
        if_neg fun h => hc ((forall_mem_signerSlots_iff E i H v c).1 h).1.symm, mul_zero]
  rw [bind_apply, tsum_fintype, Fintype.sum_prod_type,
    sum_eq_single v (fun v' _ hv' => hoff v' hv') (by simp),
    sum_eq_single (H (i, v)) (fun c _ hc => hoffc c hc) (by simp)]
  rw [ringKernel, map_pair_const_apply, if_pos rfl, slotLaw_apply,
    slotCount_signerSlots E i (H (i, v)) c₀]
  by_cases hp : nonSignerPass E i H v
  · rw [if_pos ((forall_mem_signerSlots_iff E i H v _).2 ⟨rfl, hp⟩), if_pos hp, mul_one]
  · rw [if_neg fun h => hp ((forall_mem_signerSlots_iff E i H v _).1 h).2, if_neg hp]
    simp

omit [Nonempty V] in
/-- The ring kernel puts no mass on a rejection. -/
theorem bind_ringKernel_apply_none (L : PMF (V × C)) (H : N × V → C) :
    L.bind (ringKernel E i) (H, none) = 0 := by
  rw [bind_apply]
  exact ENNReal.tsum_eq_zero.2 fun vc => by simp [ringKernel]

/-- **The target splits at the signer**: the ring target is the ring kernel after `v` uniform and
the signer's challenge uniform off its excluded set. -/
theorem ringTarget_eq_bind_ringKernel :
    ringTarget V E = (signerTarget E i).bind (ringKernel E i) := by
  obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
  refine eq_of_apply_eq_mul (F := fun x => x.2.elim 0 fun v =>
      if ∀ j, x.1 (j, v) ∉ E.excl j then 1 else 0)
    (a := (Fintype.card V : ℝ≥0∞)⁻¹ * ((slotCount V fun j => (E.excl j)ᶜ : ℕ) : ℝ≥0∞)⁻¹)
    (b := (Fintype.card V : ℝ≥0∞)⁻¹ * (((E.excl i)ᶜ.card : ℕ) : ℝ≥0∞)⁻¹ *
      ((slotCount V (signerSlots E i c₀) : ℕ) : ℝ≥0∞)⁻¹) ?_ ?_
  · rintro ⟨H, o⟩
    cases o with
    | none =>
      simp only [Option.elim_none, mul_zero]
      rw [ringTarget, bind_apply]
      exact ENNReal.tsum_eq_zero.2 fun v => by simp
    | some v =>
      simp only [Option.elim_some]
      rw [ringTarget, bind_apply, tsum_eq_single v fun v' hv' => by
        rw [map_pair_const_apply, if_neg fun h => hv' (Option.some_injective _ h).symm,
          mul_zero]]
      rw [map_pair_const_apply, if_pos rfl, slotLaw_apply, uniformOfFintype_apply]
      simp only [mem_compl]
      split_ifs <;> simp [mul_comm]
  · rintro ⟨H, o⟩
    cases o with
    | none =>
      simp only [Option.elim_none, mul_zero]
      exact bind_ringKernel_apply_none E i _ H
    | some v =>
      simp only [Option.elim_some]
      rw [bind_ringKernel_apply_some E i _ H v c₀, signerTarget, bind_map_prodMk_apply,
        uniformOfFintype_apply, uniformOfFinset_apply]
      have := forall_notMem_iff E i H v
      by_cases h1 : H (i, v) ∉ E.excl i <;> by_cases h2 : nonSignerPass E i H v <;>
        simp_all [mul_comm, mul_left_comm]

omit [Nonempty V] in
/-- **The accepted ring attempt splits at the signer**: jointly with `H`, the accepted `v` of a
ring attempt is the accepted `(v, c)` of the fresh attempt followed by the ring kernel. -/
theorem map_condSome_jointAttempt_ringAttempt
    (h : jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ) none ≠ 1)
    (h' : freshAttempt P w1 acc κ hκ none ≠ 1) :
    (condSome (jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ)) h).map
        (fun z => (z.1, some z.2)) =
      (condSome (freshAttempt P w1 acc κ hκ) h').bind (ringKernel E i) := by
  obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
  refine eq_of_apply_eq_mul (F := fun x => x.2.elim 0 fun v =>
      signerMass P w1 acc v (x.1 (i, v)) * κ (v, x.1 (i, v)) *
        (if nonSignerPass E i x.1 v then 1 else 0))
    (a := (Fintype.card (N × V → C) : ℝ≥0∞)⁻¹ *
      (1 - jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ) none)⁻¹)
    (b := (Fintype.card C : ℝ≥0∞)⁻¹ * (1 - freshAttempt P w1 acc κ hκ none)⁻¹ *
      ((slotCount V (signerSlots E i c₀) : ℕ) : ℝ≥0∞)⁻¹) ?_ ?_
  · rintro ⟨H, o⟩
    cases o with
    | none => simp only [Option.elim_none, mul_zero]; exact map_pair_some_apply_none _ H
    | some v =>
      simp only [Option.elim_some]
      rw [map_pair_some_apply_some, condSome_apply, jointAttempt_apply_some,
        uniformOfFintype_apply, ringAttempt_apply_some]
      simp only [div_eq_mul_inv]
      ring
  · rintro ⟨H, o⟩
    cases o with
    | none =>
      simp only [Option.elim_none, mul_zero]
      exact bind_ringKernel_apply_none E i _ H
    | some v =>
      simp only [Option.elim_some]
      rw [bind_ringKernel_apply_some E i _ H v c₀, condSome_apply, freshAttempt_apply_some]
      simp only [div_eq_mul_inv]
      ring

/-- **The ring attempt keeps with positive probability** as soon as the signer's fresh attempt
does: choose `H` with the signer's challenge where the fresh attempt keeps and every other
member's challenge off its excluded set. -/
theorem jointAttempt_ringAttempt_ne_one (h' : freshAttempt P w1 acc κ hκ none ≠ 1) :
    jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ) none ≠ 1 := by
  classical
  have hs : ∑ a, freshAttempt P w1 acc κ hκ (some a) ≠ 0 := by
    rw [sum_apply_some]; exact one_sub_apply_none_ne_zero h'
  obtain ⟨⟨v, c⟩, -, hvc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  rw [freshAttempt_apply_some] at hvc
  have hmk : signerMass P w1 acc v c * κ (v, c) ≠ 0 := fun h0 => hvc (by
    rw [mul_right_comm, h0, zero_mul])
  let H₀ : N × V → C := fun x =>
    if x.1 = i then c else (E.compl_nonempty x.1).choose
  have hH₀i : H₀ (i, v) = c := by simp [H₀]
  have hpass : nonSignerPass E i H₀ v := fun j hj => by
    have := (E.compl_nonempty j).choose_spec
    simpa [H₀, hj] using this
  refine jointAttempt_apply_none_ne_one (θ₀ := H₀) (by simp) fun h1 => ?_
  have hz := sum_apply_some (ringAttempt E i P w1 acc κ hκ H₀)
  rw [h1, tsub_self] at hz
  have := (Finset.sum_eq_zero_iff.1 hz) v (mem_univ _)
  rw [ringAttempt_apply_some, hH₀i, if_pos hpass, mul_one] at this
  exact hmk this

/-- **The ring prover against the target**: if the signer's fresh attempt keeps with positive
probability, the ring prover is within the oracle concentration term and the distance of the
signer's accepted `(v, c)` (fresh challenge, flattening coin) from `v` uniform and `c` uniform off
the signer's excluded set, of the ring target. -/
theorem tvDist_ringProver_ringTarget_le (h' : freshAttempt P w1 acc κ hκ none ≠ 1) :
    tvDist (ringProver E i P w1 acc κ hκ) (ringTarget V E) ≤
      oracleConcError E i P w1 acc κ hκ +
        tvDist (condSome (freshAttempt P w1 acc κ hκ) h') (signerTarget E i) := by
  have h := jointAttempt_ringAttempt_ne_one E i P w1 acc κ hκ h'
  refine (tvDist_triangle _ _ _).trans (add_le_add (tvDist_loopForever_le _ _ h) ?_)
  rw [map_condSome_jointAttempt_ringAttempt E i P w1 acc κ hκ h h',
    ringTarget_eq_bind_ringKernel E i]
  exact tvDist_bind_right_le _ _ _

end Ring

section ColumnIndependence

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]

/-- **Two coordinates of a uniform function are independent**: for `k ≠ k'`,
`E_f[φ (f k) · ψ (f k')] = E_x[φ x] · E_x[ψ x]`, written with the uniform weights. -/
theorem sum_pi_mul_apply_mul_apply {k k' : ι} (hk : k ≠ k') (φ ψ : β → ℝ) :
    ∑ f : ι → β, (Fintype.card (ι → β) : ℝ)⁻¹ * (φ (f k) * ψ (f k')) =
      (∑ x, (Fintype.card β : ℝ)⁻¹ * φ x) * ∑ x, (Fintype.card β : ℝ)⁻¹ * ψ x := by
  set c := (Fintype.card β : ℝ)⁻¹
  let g : ι → β → ℝ := fun j x =>
    c * ((if j = k then φ x else 1) * (if j = k' then ψ x else 1))
  have hterm : ∀ f : ι → β, (Fintype.card (ι → β) : ℝ)⁻¹ * (φ (f k) * ψ (f k')) =
      ∏ j, g j (f j) := fun f => by
    simp only [g, prod_mul_distrib, prod_const, card_univ, Fintype.card_fun, Nat.cast_pow,
      inv_pow, c, prod_ite_eq', mem_univ, ite_true]
  have hj : ∀ j, ∑ x, g j x =
      (if j = k then ∑ x, c * φ x else 1) * (if j = k' then ∑ x, c * ψ x else 1) := fun j => by
    by_cases hjk : j = k
    · subst hjk; simp [g, hk]
    · by_cases hjk' : j = k'
      · subst hjk'; simp [g, hjk]
      · have hc : ∑ _x : β, c = 1 := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
        simp [g, hjk, hjk', hc]
  rw [sum_congr rfl fun f _ => hterm f, ← Fintype.prod_sum]
  simp only [hj, prod_mul_distrib, prod_ite_eq', mem_univ, ite_true]

/-- One coordinate of a uniform function is uniform. -/
theorem sum_pi_mul_apply (k : ι) (φ : β → ℝ) :
    ∑ f : ι → β, (Fintype.card (ι → β) : ℝ)⁻¹ * φ (f k) =
      ∑ x, (Fintype.card β : ℝ)⁻¹ * φ x := by
  set c := (Fintype.card β : ℝ)⁻¹
  let g : ι → β → ℝ := fun j x => c * (if j = k then φ x else 1)
  have hterm : ∀ f : ι → β, (Fintype.card (ι → β) : ℝ)⁻¹ * φ (f k) = ∏ j, g j (f j) :=
    fun f => by
      simp only [g, prod_mul_distrib, prod_const, card_univ, Fintype.card_fun, Nat.cast_pow,
        inv_pow, c, prod_ite_eq', mem_univ, ite_true]
  have hj : ∀ j, ∑ x, g j x = if j = k then ∑ x, c * φ x else 1 := fun j => by
    by_cases hjk : j = k
    · subst hjk; simp [g]
    · simp only [g, hjk, ite_false, mul_one, sum_const, card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  rw [sum_congr rfl fun f _ => hterm f, ← Fintype.prod_sum]
  simp only [hj, prod_ite_eq', mem_univ, ite_true]

end ColumnIndependence

section OracleConcentration

variable {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] [Nonempty C] [Nonempty V]
  (E : ExclSets N C) (i : N) {Y : Type*} [Fintype Y] (P : PMF Y) (w1 : Y → V)
  (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1)

/-- The column of `H` at `v`: every member's value at `v`. -/
def column (H : N × V → C) (v : V) : N → C := fun j => H (j, v)

omit [DecidableEq C] [Nonempty V] in
/-- **Two columns of a uniform function are independent.** -/
theorem sum_uniform_column_mul {v v' : V} (hv : v ≠ v') (φ ψ : (N → C) → ℝ) :
    ∑ H : N × V → C, (Fintype.card (N × V → C) : ℝ)⁻¹ * (φ (column H v) * ψ (column H v')) =
      (∑ H : N × V → C, (Fintype.card (N × V → C) : ℝ)⁻¹ * φ (column H v)) *
        ∑ H : N × V → C, (Fintype.card (N × V → C) : ℝ)⁻¹ * ψ (column H v') := by
  classical
  let e : (N × V → C) ≃ (V → N → C) :=
    ⟨fun H v j => H (j, v), fun f x => f x.2 x.1, fun _ => rfl, fun _ => rfl⟩
  have hcard : Fintype.card (N × V → C) = Fintype.card (V → N → C) := Fintype.card_congr e
  have h1 := Fintype.sum_equiv e
    (fun H => (Fintype.card (N × V → C) : ℝ)⁻¹ * (φ (column H v) * ψ (column H v')))
    (fun f => (Fintype.card (V → N → C) : ℝ)⁻¹ * (φ (f v) * ψ (f v'))) fun H => by
      rw [hcard]; rfl
  have h2 := Fintype.sum_equiv e
    (fun H => (Fintype.card (N × V → C) : ℝ)⁻¹ * φ (column H v))
    (fun f => (Fintype.card (V → N → C) : ℝ)⁻¹ * φ (f v)) fun H => by rw [hcard]; rfl
  have h3 := Fintype.sum_equiv e
    (fun H => (Fintype.card (N × V → C) : ℝ)⁻¹ * ψ (column H v'))
    (fun f => (Fintype.card (V → N → C) : ℝ)⁻¹ * ψ (f v')) fun H => by rw [hcard]; rfl
  rw [h1, h2, h3, sum_pi_mul_apply_mul_apply hv, sum_pi_mul_apply, sum_pi_mul_apply]

omit [Fintype V] [Fintype C] [DecidableEq C] [Nonempty C] [Nonempty V] in
/-- `Pr_y[w1 y = v ∧ acc y c]` is at most `Pr_y[w1 y = v]`. -/
theorem signerMass_le_map (v : V) (c : C) : signerMass P w1 acc v c ≤ P.map w1 v := by
  classical
  rw [signerMass, map_apply, tsum_fintype]
  refine sum_le_sum fun y _ => ?_
  by_cases h : w1 y = v
  · subst h; split_ifs <;> simp_all
  · rw [if_neg fun h' => h h'.1, if_neg fun h' => h h'.symm]

omit [Nonempty C] in
/-- For `x ≠ ⊤`, `(x - 1).toReal = max (x.toReal - 1) 0`. -/
theorem _root_.ENNReal.toReal_tsub_one {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    (x - 1).toReal = max (x.toReal - 1) 0 := by
  rcases le_total x 1 with h | h
  · rw [tsub_eq_zero_of_le h, ENNReal.toReal_zero, max_eq_right]
    have := ENNReal.toReal_mono ENNReal.one_ne_top h
    simp only [ENNReal.toReal_one] at this
    linarith
  · rw [ENNReal.toReal_sub_of_le h hx, ENNReal.toReal_one, max_eq_left]
    have := ENNReal.toReal_mono hx h
    simp only [ENNReal.toReal_one] at this
    linarith

omit [Nonempty V] in
/-- **The oracle concentration bound**: if every commitment `w1 y = v` has probability at most
`δ`, the oracle concentration term is at most `√(δ / q̄) / 2`, with `q̄` the keep probability of
one ring attempt against a uniform oracle. The keep probability `q H` against a fixed oracle is a
sum over columns `v` of terms each at most `δ` that depend on the column of `H` at `v` only, so its
variance is at most `δ · q̄`. -/
theorem oracleConcError_le {δ : ℝ} (hδ : ∀ v, (P.map w1 v).toReal ≤ δ)
    (h : jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ) none ≠ 1) :
    oracleConcError E i P w1 acc κ hκ ≤
      √(δ / (1 - jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ) none).toReal)
        / 2 := by
  classical
  set U := uniformOfFintype (N × V → C)
  set J := jointAttempt U (ringAttempt E i P w1 acc κ hκ)
  set A := ringAttempt E i P w1 acc κ hκ
  set c0 : ℝ := (Fintype.card (N × V → C) : ℝ)⁻¹
  have hU : ∀ H, (U H).toReal = c0 := fun H => toReal_uniformOfFintype_apply H
  have hc0 : ∑ _H : N × V → C, c0 = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  have hc0nn : 0 ≤ c0 := inv_nonneg.2 (Nat.cast_nonneg _)
  -- the per-column keep probabilities
  let φ : V → (N → C) → ℝ := fun v cs =>
    (signerMass P w1 acc v (cs i) * κ (v, cs i) *
      (if ∀ j, j ≠ i → cs j ∉ E.excl j then 1 else 0)).toReal
  let G : V → (N × V → C) → ℝ := fun v H => (A H (some v)).toReal
  have hG : ∀ v H, G v H = φ v (column H v) := fun v H => by
    simp only [G, φ, A, ringAttempt_apply_some, column]
    rfl
  have hφ0 : ∀ v cs, 0 ≤ φ v cs := fun _ _ => ENNReal.toReal_nonneg
  have hφδ : ∀ v cs, φ v cs ≤ δ := fun v cs => by
    refine le_trans (ENNReal.toReal_mono (apply_ne_top _ _) ?_) (hδ v)
    calc signerMass P w1 acc v (cs i) * κ (v, cs i) *
          (if ∀ j, j ≠ i → cs j ∉ E.excl j then 1 else 0)
        ≤ signerMass P w1 acc v (cs i) * 1 * 1 := by
          gcongr
          · exact hκ _
          · split_ifs <;> simp
      _ ≤ P.map w1 v := by rw [mul_one, mul_one]; exact signerMass_le_map P w1 acc v _
  set Q : (N × V → C) → ℝ := fun H => ∑ v, G v H
  have hQ : ∀ H, (1 - A H none).toReal = Q H := fun H => by
    rw [← sum_apply_some, ENNReal.toReal_sum fun v _ => apply_ne_top _ _]
  -- the average keep probability
  set m := (1 - J none).toReal with hm_def
  have hsum : ∑ H, U H * (1 - A H none) + J none = 1 := by
    rw [show J = jointAttempt U A from rfl, jointAttempt_apply_none, ← sum_add_distrib]
    calc ∑ H, (U H * (1 - A H none) + U H * A H none) = ∑ H, U H :=
          sum_congr rfl fun H _ => by
            rw [← mul_add, tsub_add_cancel_of_le (coe_le_one _ _), mul_one]
      _ = 1 := sum_coe U
  have hJt : J none ≠ ⊤ := apply_ne_top _ _
  have hm : m = ∑ H, c0 * Q H := by
    rw [hm_def, ← ENNReal.eq_sub_of_add_eq hJt hsum, ENNReal.toReal_sum fun H _ =>
      ENNReal.mul_ne_top (apply_ne_top _ _) (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
    exact sum_congr rfl fun H _ => by rw [ENNReal.toReal_mul, hU, hQ]
  have hs0 : 1 - J none ≠ 0 := one_sub_apply_none_ne_zero h
  have hm0 : 0 < m := ENNReal.toReal_pos hs0 (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  -- the second moment
  have hmom : ∑ H, c0 * Q H ^ 2 ≤ m ^ 2 + δ * m := by
    have hexp : ∀ H, c0 * Q H ^ 2 = ∑ v, ∑ v', c0 * (G v H * G v' H) := fun H => by
      rw [sq, show Q H = ∑ v, G v H from rfl, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun v _ => by rw [mul_sum]
    have hpair : ∀ v v', ∑ H, c0 * (G v H * G v' H) ≤
        (∑ H, c0 * G v H) * (∑ H, c0 * G v' H) + if v = v' then δ * ∑ H, c0 * G v H else 0 := by
      intro v v'
      by_cases hvv : v = v'
      · subst hvv
        rw [if_pos rfl]
        have hle : ∑ H, c0 * (G v H * G v H) ≤ δ * ∑ H, c0 * G v H := by
          rw [mul_sum]
          refine sum_le_sum fun H _ => ?_
          rw [hG]
          have h0 := hφ0 v (column H v)
          have h1 := hφδ v (column H v)
          have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h0) hc0nn
          linarith
        have hsq : 0 ≤ (∑ H, c0 * G v H) * (∑ H, c0 * G v H) := mul_self_nonneg _
        linarith
      · rw [if_neg hvv, add_zero]
        simp only [hG]
        exact (sum_uniform_column_mul hvv (φ v) (φ v')).le
    calc ∑ H, c0 * Q H ^ 2 = ∑ v, ∑ v', ∑ H, c0 * (G v H * G v' H) := by
          simp only [hexp]
          rw [sum_comm]
          exact sum_congr rfl fun v _ => sum_comm
      _ ≤ ∑ v, ∑ v', ((∑ H, c0 * G v H) * (∑ H, c0 * G v' H) +
            if v = v' then δ * ∑ H, c0 * G v H else 0) :=
          sum_le_sum fun v _ => sum_le_sum fun v' _ => hpair v v'
      _ = (∑ v, ∑ H, c0 * G v H) ^ 2 + δ * ∑ v, ∑ H, c0 * G v H := by
          simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, ← sum_mul, sq]
      _ = m ^ 2 + δ * m := by
          have : ∑ v, ∑ H, c0 * G v H = m := by
            rw [hm, sum_comm]
            exact sum_congr rfl fun H _ => by rw [← mul_sum]
          rw [this]
  -- the concentration term in `ℝ`
  set X : (N × V → C) → ℝ := fun H => Q H / m - 1
  have hconc : oracleConcError E i P w1 acc κ hκ = ∑ H, c0 * max (X H) 0 := by
    rw [oracleConcError, ENNReal.toReal_sum fun H _ => ENNReal.mul_ne_top (apply_ne_top _ _)
      (ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top hs0)
        (tsub_le_self.trans (ENNReal.div_le_div_right tsub_le_self _)))]
    refine sum_congr rfl fun H _ => ?_
    rw [ENNReal.toReal_mul, hU, ENNReal.toReal_tsub_one (ENNReal.div_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) hs0), ENNReal.toReal_div, hQ]
  have hX0 : ∑ H, c0 * X H = 0 := by
    simp only [X, mul_sub, mul_one, sum_sub_distrib, hc0, mul_div_assoc', ← sum_div, ← hm,
      div_self hm0.ne', sub_self]
  have hmax : ∀ x : ℝ, max x 0 = (x + |x|) / 2 := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
  have hX2 : ∑ H, c0 * X H ^ 2 ≤ δ / m := by
    have hexp : ∀ H, c0 * X H ^ 2 = c0 * Q H ^ 2 / m ^ 2 - 2 * (c0 * Q H) / m + c0 := fun H => by
      simp only [X]; field_simp; ring
    have hmom' : c0 * ∑ H, Q H ^ 2 ≤ m ^ 2 + δ * m := by rw [mul_sum]; exact hmom
    simp only [hexp, sum_add_distrib, sum_sub_distrib, ← sum_div, ← mul_sum, ← hm, hc0]
    have : (c0 * ∑ H, Q H ^ 2) / m ^ 2 ≤ (m ^ 2 + δ * m) / m ^ 2 :=
      div_le_div_of_nonneg_right hmom' (by positivity)
    have h2 : (m ^ 2 + δ * m) / m ^ 2 = 1 + δ / m := by field_simp
    rw [show 2 * m / m = 2 by field_simp]
    linarith
  have hexpect : ∀ f : (N × V → C) → ℝ, ∑ H, c0 * f H = 𝔼 H, f H := fun f => by
    rw [Fintype.expect_eq_sum_div_card, sum_div]
    exact sum_congr rfl fun H _ => by rw [div_eq_inv_mul]
  have habs : ∑ H, c0 * |X H| ≤ √(δ / m) := by
    rw [hexpect]
    calc 𝔼 H, |X H| = 𝔼 H, √(X H ^ 2) := by simp only [Real.sqrt_sq_eq_abs]
      _ ≤ √(𝔼 H, X H ^ 2) := Real.expect_sqrt_le_sqrt_expect _ fun H => sq_nonneg _
      _ ≤ √(δ / m) := Real.sqrt_le_sqrt (by rw [← hexpect]; exact hX2)
  rw [hconc]
  calc ∑ H, c0 * max (X H) 0 = (∑ H, c0 * X H + ∑ H, c0 * |X H|) / 2 := by
        simp only [hmax, mul_div_assoc', ← sum_div, mul_add, sum_add_distrib]
    _ ≤ √(δ / m) / 2 := by rw [hX0, zero_add]; gcongr

end OracleConcentration

section FreshFlatten

variable {V C Y : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype C] [DecidableEq C]
  [Nonempty C] [Fintype Y]

omit [Nonempty V] in
/-- **Flattening a fresh attempt whose accepted law is `u · w`**: if
`Pr_y[w1 y = v ∧ acc y c] / |C|` is proportional to `u (v, c) · w (v, c)`, the fresh attempt with
the flattening coin `min 1 (β / w)` has accepted law within `∑ u · (β - w) / ∑ u · min w β` of
`u` (`FlattenHyp.tvDist_condSome_thin_le`). -/
theorem tvDist_condSomeOr_freshAttempt_flatten_le (P : PMF Y) (w1 : Y → V) (acc : Y → C → Bool)
    (u : PMF (V × C)) {w : V × C → ℝ≥0∞} {β : ℝ≥0∞} (hw : ∀ a, w a ≤ 1) (hβ : β ≤ 1)
    (hmass : ∑ a, u a * min (w a) β ≠ 0) {r : ℝ≥0∞} (hr0 : r ≠ 0)
    (hS : ∀ v c, signerMass P w1 acc v c * (Fintype.card C : ℝ≥0∞)⁻¹ = r * (u (v, c) * w (v, c)))
    (d : PMF (V × C)) :
    tvDist (condSomeOr (freshAttempt P w1 acc (flattenKeep w β) (flattenKeep_le_one w β)) d) u ≤
      ((∑ a, u a * (β - w a)) / ∑ a, u a * min (w a) β).toReal := by
  set Z := ∑ a, u a * w a
  have hZt : Z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top <| (sum_coe u).symm ▸
    sum_le_sum fun b _ => mul_le_of_le_one_right' (hw b)
  have hZ0 : Z ≠ 0 := fun h0 => hmass (le_antisymm (h0 ▸ sum_le_sum fun b _ => by
    gcongr; exact min_le_left _ _) bot_le)
  let S : PMF (V × C) := ofFintype (fun a => u a * w a / Z) (by
    simp only [div_eq_mul_inv, ← sum_mul]; exact ENNReal.mul_inv_cancel hZ0 hZt)
  have hFl : FlattenHyp u w β S := ⟨hw, hβ, fun a => rfl, hmass⟩
  set κ := flattenKeep w β
  have hfresh : ∀ a, freshAttempt P w1 acc κ (flattenKeep_le_one w β) (some a) =
      r * (u a * w a * κ a) := fun ⟨v, c⟩ => by
    rw [freshAttempt_apply_some, hS, mul_assoc, mul_assoc]
  have hthin : ∀ a, thin S κ (flattenKeep_le_one w β) (some a) = Z⁻¹ * (u a * w a * κ a) :=
    fun a => by
      rw [thin_apply_some]
      change u a * w a / Z * κ a = _
      rw [div_eq_mul_inv]; ring
  have h' : freshAttempt P w1 acc κ (flattenKeep_le_one w β) none ≠ 1 := by
    intro h1
    have hs := sum_apply_some (freshAttempt P w1 acc κ (flattenKeep_le_one w β))
    rw [h1, tsub_self] at hs
    rw [sum_congr rfl fun a _ => hfresh a, ← mul_sum] at hs
    have hs2 := (mul_eq_zero.1 hs).resolve_left hr0
    apply hFl.thin_apply_none_ne_one
    rw [apply_none_eq_one_sub, sum_congr rfl fun a _ => hthin a, ← mul_sum, hs2, mul_zero,
      tsub_zero]
  rw [condSomeOr_of_ne _ h']
  have heq : condSome (freshAttempt P w1 acc κ (flattenKeep_le_one w β)) h' =
      condSome (thin S κ (flattenKeep_le_one w β)) hFl.thin_apply_none_ne_one :=
    eq_of_apply_eq_mul (F := fun a => u a * w a * κ a)
      (a := r * (1 - freshAttempt P w1 acc κ (flattenKeep_le_one w β) none)⁻¹)
      (b := Z⁻¹ * (1 - thin S κ (flattenKeep_le_one w β) none)⁻¹)
      (fun a => by rw [condSome_apply, hfresh, div_eq_mul_inv]; ring)
      (fun a => by rw [condSome_apply, hthin, div_eq_mul_inv]; ring)
  rw [heq]
  exact hFl.tvDist_condSome_thin_le

end FreshFlatten

end PMF
