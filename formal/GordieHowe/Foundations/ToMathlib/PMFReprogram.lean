-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFRejection
public import GordieHowe.Foundations.ToMathlib.PMFUniform
public import GordieHowe.Foundations.ToMathlib.UniformFunction

@[expose] public section

/-!
# Reprogramming a uniform random function at sampled points

Attempts that read their challenges `H (f y₀), …, H (f yₙ₋₁)` from one uniform random function
`H : X → C`, at points `yᵢ ← P` drawn independently, against attempts with fresh uniform
challenges `cᵢ` and the function `H` reprogrammed at `f yᵢ` to `cᵢ` (`reprogram`):

- `map_reprogram_eq_of_injective`: at distinct points the two laws of (function, challenges)
  are equal;
- `tvDist_readChallenges_freshChallenges_le`: jointly with the points, the two experiments are
  at total variation distance at most `(n choose 2) · δ` when `Pr_{y ← P}[f y = x] ≤ δ` for
  every `x` (collisions among the points, `prob_not_injective_le`).

Everything the attempts output is a function of (function, points, challenges), so the same bound
holds for every loop over these attempts, by data processing (`tvDist_map_le`). The reprogrammed
function is reprogrammed at every point drawn, accepted or not.

About Mathlib objects only; a candidate for upstreaming with
`GordieHowe/Foundations/ToMathlib/PMFTV.lean` and
`GordieHowe/Foundations/ToMathlib/UniformFunction.lean`.
-/

open Finset
open scoped BigOperators ENNReal

namespace PMF

section Reprogram

variable {X C : Type*} [DecidableEq X]

/-- **Reprogramming** `H` at the points `pts i` to the values `cs i`, in order (a later point
overrides an earlier equal one). -/
def reprogram {n : ℕ} (pts : Fin n → X) (cs : Fin n → C) (H : X → C) : X → C :=
  (List.finRange n).foldl (fun G i => Function.update G (pts i) (cs i)) H

/-- Updating along a list leaves the points it does not touch unchanged. -/
theorem foldl_update_apply_of_forall_ne {ι : Type*} (pts : ι → X) (cs : ι → C) (l : List ι)
    (G : X → C) {x : X} (hx : ∀ i ∈ l, pts i ≠ x) :
    l.foldl (fun G i => Function.update G (pts i) (cs i)) G x = G x := by
  induction l generalizing G with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih _ fun i hi => hx i (List.mem_cons_of_mem j hi),
      Function.update_of_ne (hx j List.mem_cons_self).symm]

/-- Updating along a list without repetitions, at an injective family of points, gives each
point its value. -/
theorem foldl_update_apply_of_injective {ι : Type*} {pts : ι → X} (hpts : Function.Injective pts)
    (cs : ι → C) {l : List ι} (hl : l.Nodup) (G : X → C) {i : ι} (hi : i ∈ l) :
    l.foldl (fun G i => Function.update G (pts i) (cs i)) G (pts i) = cs i := by
  induction l generalizing G with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hil
    · rw [foldl_update_apply_of_forall_ne pts cs l _ fun k hk h => ?_, Function.update_self]
      exact (List.nodup_cons.1 hl).1 (hpts h ▸ hk)
    · exact ih (List.nodup_cons.1 hl).2 _ hil

/-- At injective points, the reprogrammed function takes the new values. -/
theorem reprogram_apply_of_injective {n : ℕ} {pts : Fin n → X} (hpts : Function.Injective pts)
    (cs : Fin n → C) (H : X → C) (i : Fin n) : reprogram pts cs H (pts i) = cs i :=
  foldl_update_apply_of_injective hpts cs (List.nodup_finRange n) H (List.mem_finRange i)

/-- Off the points, the reprogrammed function is unchanged. -/
theorem reprogram_apply_of_notMem {n : ℕ} (pts : Fin n → X) (cs : Fin n → C) (H : X → C) {x : X}
    (hx : x ∉ Set.range pts) : reprogram pts cs H x = H x :=
  foldl_update_apply_of_forall_ne pts cs _ H fun i _ h => hx ⟨i, h⟩

variable [Fintype X] [Fintype C] [Nonempty C]

omit [Nonempty C] in
/-- At injective points, reprogramming replaces the pullback part of `splitAlong`. -/
theorem reprogram_eq_splitAlong_symm {n : ℕ} (pts : Fin n ↪ X) (cs : Fin n → C) (H : X → C) :
    reprogram pts cs H = (GordieHowe.splitAlong pts).symm ((GordieHowe.splitAlong pts H).1, cs) := by
  funext x
  by_cases hx : x ∈ Set.range pts
  · obtain ⟨i, rfl⟩ := hx
    rw [reprogram_apply_of_injective pts.injective, GordieHowe.splitAlong_symm_apply_embed]
  · rw [reprogram_apply_of_notMem _ _ _ hx, GordieHowe.splitAlong_symm_apply_of_notMem _ _ _ hx]
    conv_lhs => rw [← (GordieHowe.splitAlong pts).symm_apply_apply H]
    rw [GordieHowe.splitAlong_symm_apply_of_notMem _ _ _ hx]

/-- **Reprogramming at distinct points is exact**: for injective `pts`, the reprogrammed uniform
function with its fresh uniform values has the law of a uniform function with its own values at
`pts`. -/
theorem map_reprogram_eq_of_injective {n : ℕ} {pts : Fin n → X} (hpts : Function.Injective pts) :
    (uniformOfFintype ((X → C) × (Fin n → C))).map (fun Hc => (reprogram pts Hc.2 Hc.1, Hc.2)) =
      (uniformOfFintype (X → C)).map fun H => (H, fun i => H (pts i)) := by
  let F := {x // x ∉ Set.range (⟨pts, hpts⟩ : Fin n ↪ X)} → C
  let e : (X → C) ≃ F × (Fin n → C) := GordieHowe.splitAlong ⟨pts, hpts⟩
  have hR : (uniformOfFintype (X → C)).map (fun H => (H, fun i => H (pts i))) =
      (uniformOfFintype (F × (Fin n → C))).map fun z => (e.symm z, z.2) := by
    rw [← map_uniformOfFintype_equiv e.symm, map_comp]
    congr 1
    funext ⟨z1, z2⟩
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    funext i
    simpa [e] using GordieHowe.splitAlong_symm_apply_embed ⟨pts, hpts⟩ z1 z2 i
  let ψ : (F × (Fin n → C)) × (Fin n → C) ≃ (F × (Fin n → C)) × (Fin n → C) :=
    { toFun := fun z => ((z.1.1, z.2), z.1.2)
      invFun := fun w => ((w.1.1, w.2), w.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hI : (uniformOfFintype ((X → C) × (Fin n → C))).map
      (fun Hc => (reprogram pts Hc.2 Hc.1, Hc.2)) =
      ((uniformOfFintype ((F × (Fin n → C)) × (Fin n → C))).map ψ).map
        (fun w => (e.symm w.1, w.1.2)) := by
    rw [← map_uniformOfFintype_equiv (Equiv.prodCongr e.symm (Equiv.refl (Fin n → C))), map_comp,
      map_comp]
    congr 1
    funext z
    simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map, Equiv.coe_refl, id, ψ,
      Equiv.coe_fn_mk]
    rw [show reprogram pts = reprogram (⟨pts, hpts⟩ : Fin n ↪ X) from rfl,
      reprogram_eq_splitAlong_symm]
    simp [e]
  rw [hI, hR, map_uniformOfFintype_equiv]
  conv_lhs => rw [show (fun w : (F × (Fin n → C)) × (Fin n → C) => (e.symm w.1, w.1.2)) =
    (fun z : F × (Fin n → C) => (e.symm z, z.2)) ∘ Prod.fst from rfl, ← map_comp,
    map_fst_uniformOfFintype]

end Reprogram

section Collision

variable {Z : Type*} [Fintype Z] [DecidableEq Z] {n : ℕ}

/-- Two coordinates of `n` independent draws from `q` both equal `x` with probability
`q x ^ 2`. -/
theorem sum_pi_const_mul_ite_mul_ite (q : PMF Z) {i j : Fin n} (hij : i ≠ j) (x : Z) :
    ∑ zs : Fin n → Z, (pi (fun _ => q) zs).toReal *
        ((if zs i = x then (1 : ℝ) else 0) * (if zs j = x then 1 else 0)) = (q x).toReal ^ 2 := by
  let g : Fin n → Z → ℝ := fun k z => (q z).toReal *
    ((if k = i then (if z = x then 1 else 0) else 1) * (if k = j then (if z = x then 1 else 0) else 1))
  have hterm : ∀ zs : Fin n → Z, (pi (fun _ => q) zs).toReal *
      ((if zs i = x then (1 : ℝ) else 0) * (if zs j = x then 1 else 0)) = ∏ k, g k (zs k) := by
    intro zs
    simp only [g, prod_mul_distrib, toReal_pi_apply, prod_ite_eq', mem_univ, ite_true]
  have hk : ∀ k, ∑ z, g k z =
      (if k = i then (q x).toReal else 1) * (if k = j then (q x).toReal else 1) := by
    intro k
    by_cases hki : k = i
    · subst hki
      simp [g, hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [g, hki]
      · simp [g, hki, hkj, sum_toReal]
  rw [sum_congr rfl fun zs _ => hterm zs, ← Fintype.prod_sum]
  simp only [hk, prod_mul_distrib, prod_ite_eq', mem_univ, ite_true, sq]

/-- Two coordinates of `n` independent draws from `q` collide with probability at most `δ` when
`q x ≤ δ` for every `x`. -/
theorem sum_pi_const_mul_ite_eq_le (q : PMF Z) {δ : ℝ} (hδ : ∀ x, (q x).toReal ≤ δ) {i j : Fin n}
    (hij : i ≠ j) :
    ∑ zs : Fin n → Z, (pi (fun _ => q) zs).toReal * (if zs i = zs j then (1 : ℝ) else 0) ≤ δ := by
  have hind : ∀ zs : Fin n → Z, (if zs i = zs j then (1 : ℝ) else 0) =
      ∑ x, (if zs i = x then (1 : ℝ) else 0) * (if zs j = x then 1 else 0) := fun zs => by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    exact if_congr eq_comm rfl rfl
  simp only [hind, mul_sum]
  rw [sum_comm]
  simp only [sum_pi_const_mul_ite_mul_ite q hij]
  calc ∑ x, (q x).toReal ^ 2 ≤ ∑ x, δ * (q x).toReal :=
        sum_le_sum fun x _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (hδ x) ENNReal.toReal_nonneg
    _ = δ := by rw [← mul_sum, sum_toReal, mul_one]

omit [Fintype Z] in
/-- A non-injective tuple has a pair `i < j` of equal coordinates (the union bound's
pointwise form). -/
theorem ite_injective_le_sum (zs : Fin n → Z) :
    (if Function.Injective zs then (0 : ℝ) else 1) ≤
      ∑ j, ∑ i ∈ Iio j, (if zs i = zs j then (1 : ℝ) else 0) := by
  have hnn : ∀ j, 0 ≤ ∑ i ∈ Iio j, (if zs i = zs j then (1 : ℝ) else 0) := fun j =>
    sum_nonneg fun i _ => by split_ifs <;> norm_num
  split_ifs with hinj
  · exact sum_nonneg fun j _ => hnn j
  · have hpair : ∃ i j, i < j ∧ zs i = zs j := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨a, b, hab, hne⟩ := hinj
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨a, b, h, hab⟩
      · exact ⟨b, a, h, hab.symm⟩
    obtain ⟨i, j, hij, heq⟩ := hpair
    calc (1 : ℝ) = if zs i = zs j then 1 else 0 := by simp [heq]
      _ ≤ ∑ i ∈ Iio j, (if zs i = zs j then (1 : ℝ) else 0) :=
        single_le_sum (f := fun i => if zs i = zs j then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (mem_Iio.2 hij)
      _ ≤ _ := single_le_sum (fun j _ => hnn j) (mem_univ j)

/-- The number of pairs `i < j` in `Fin n` is `n choose 2`. -/
theorem sum_card_Iio_fin (n : ℕ) : ∑ j : Fin n, ((Iio j).card : ℝ) = (n.choose 2 : ℕ) := by
  simp only [Fin.card_Iio]
  rw [← Nat.cast_sum, Fin.sum_univ_eq_sum_range (fun i => i) n, sum_range_id, Nat.choose_two_right]

/-- **The birthday bound**: `n` independent draws from `q` are not all distinct with probability
at most `(n choose 2) · δ` when `q x ≤ δ` for every `x`. -/
theorem prob_not_injective_le (q : PMF Z) {δ : ℝ} (hδ : ∀ x, (q x).toReal ≤ δ) :
    ∑ zs : Fin n → Z, (pi (fun _ => q) zs).toReal * (if Function.Injective zs then (0 : ℝ) else 1) ≤
      n.choose 2 * δ := by
  calc _ ≤ ∑ zs : Fin n → Z, (pi (fun _ => q) zs).toReal *
          ∑ j, ∑ i ∈ Iio j, (if zs i = zs j then (1 : ℝ) else 0) :=
        sum_le_sum fun zs _ =>
          mul_le_mul_of_nonneg_left (ite_injective_le_sum zs) ENNReal.toReal_nonneg
    _ = ∑ j, ∑ i ∈ Iio j, ∑ zs : Fin n → Z,
          (pi (fun _ => q) zs).toReal * (if zs i = zs j then (1 : ℝ) else 0) := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun j _ => sum_comm
    _ ≤ ∑ j : Fin n, ∑ _i ∈ Iio j, δ :=
        sum_le_sum fun j _ => sum_le_sum fun i hi =>
          sum_pi_const_mul_ite_eq_le q hδ (ne_of_lt (mem_Iio.1 hi))
    _ = n.choose 2 * δ := by
        simp only [sum_const, nsmul_eq_mul, ← sum_mul]
        rw [sum_card_Iio_fin]

end Collision

section Challenges

variable {Y X C : Type*} [Fintype Y] [Fintype X] [DecidableEq X] [Fintype C] [Nonempty C]

/-- **Challenges read from a random oracle**: `n` independent points `ys i ← P`, a uniform
function `H`, and the challenges `H (f (ys i))`. -/
noncomputable def readChallenges (P : PMF Y) (f : Y → X) (n : ℕ) :
    PMF ((X → C) × (Fin n → Y) × (Fin n → C)) :=
  (pi fun _ : Fin n => P).bind fun ys =>
    (uniformOfFintype (X → C)).map fun H => (H, ys, fun i => H (f (ys i)))

/-- **Fresh challenges with a reprogrammed oracle**: `n` independent points `ys i ← P`, fresh
uniform challenges `cs`, and a uniform function reprogrammed at each `f (ys i)` to `cs i`. -/
noncomputable def freshChallenges (P : PMF Y) (f : Y → X) (n : ℕ) :
    PMF ((X → C) × (Fin n → Y) × (Fin n → C)) :=
  (pi fun _ : Fin n => P).bind fun ys =>
    (uniformOfFintype ((X → C) × (Fin n → C))).map fun Hc =>
      (reprogram (fun i => f (ys i)) Hc.2 Hc.1, ys, Hc.2)

/-- **Reading challenges from a random oracle is `(n choose 2) · δ`-close to fresh challenges
with a reprogrammed oracle**, when `Pr_{y ← P}[f y = x] ≤ δ` for every `x`. -/
theorem tvDist_readChallenges_freshChallenges_le (P : PMF Y) (f : Y → X) (n : ℕ) {δ : ℝ}
    (hδ : ∀ x, (P.map f x).toReal ≤ δ) :
    tvDist (readChallenges (C := C) P f n) (freshChallenges P f n) ≤ n.choose 2 * δ := by
  classical
  refine (tvDist_bind_left_le _ _ _).trans ?_
  have hpt : ∀ ys : Fin n → Y,
      tvDist ((uniformOfFintype (X → C)).map fun H => (H, ys, fun i => H (f (ys i))))
        ((uniformOfFintype ((X → C) × (Fin n → C))).map fun Hc =>
          (reprogram (fun i => f (ys i)) Hc.2 Hc.1, ys, Hc.2)) ≤
      if Function.Injective fun i => f (ys i) then 0 else 1 := fun ys => by
    split_ifs with hinj
    · have hR : ((uniformOfFintype (X → C)).map fun H => (H, ys, fun i => H (f (ys i)))) =
          ((uniformOfFintype (X → C)).map fun H => (H, fun i => H (f (ys i)))).map
            fun Hc => (Hc.1, ys, Hc.2) := by rw [map_comp]; rfl
      have hI : ((uniformOfFintype ((X → C) × (Fin n → C))).map fun Hc =>
          (reprogram (fun i => f (ys i)) Hc.2 Hc.1, ys, Hc.2)) =
          ((uniformOfFintype ((X → C) × (Fin n → C))).map fun Hc =>
            (reprogram (fun i => f (ys i)) Hc.2 Hc.1, Hc.2)).map
            fun Hc => (Hc.1, ys, Hc.2) := by rw [map_comp]; rfl
      rw [hR, hI, map_reprogram_eq_of_injective hinj, tvDist_self]
    · exact tvDist_le_one _ _
  calc _ ≤ ∑ ys : Fin n → Y, ((pi fun _ : Fin n => P) ys).toReal *
          (if Function.Injective fun i => f (ys i) then (0 : ℝ) else 1) :=
        sum_le_sum fun ys _ => mul_le_mul_of_nonneg_left (hpt ys) ENNReal.toReal_nonneg
    _ = ∑ zs : Fin n → X, ((pi fun _ : Fin n => P.map f) zs).toReal *
          (if Function.Injective zs then (0 : ℝ) else 1) := by
        rw [← pi_map (fun _ : Fin n => P) (fun _ => f), sum_toReal_map_mul]
    _ ≤ n.choose 2 * δ := prob_not_injective_le _ hδ

end Challenges

section Loop

variable {Y C : Type*} [Fintype Y] [Fintype C] [Nonempty C]

omit [Fintype Y] [Fintype C] [Nonempty C] in
/-- The joint law of `y ← P` and a challenge `c ← Q(y)` at `(y, c)`: `P y · Q y c`. -/
theorem bind_map_prodMk_apply (P : PMF Y) (Q : Y → PMF C) (y : Y) (c : C) :
    (P.bind fun y => (Q y).map (Prod.mk y)) (y, c) = P y * Q y c := by
  rw [bind_apply, tsum_eq_single y fun y' hy' => ?_]
  · rw [map_apply, tsum_eq_single c fun c' hc' => by simp [Ne.symm hc']]
    simp
  · rw [map_apply, ENNReal.tsum_eq_zero.2 fun c' => by simp [Ne.symm hy'], mul_zero]

/-- **`n` independent joint draws** are `n` independent points followed by `n` independent
challenges. -/
theorem pi_withUniform (P : PMF Y) (n : ℕ) :
    (pi fun _ : Fin n => withUniform P C) =
      (pi fun _ : Fin n => P).bind fun ys =>
        (pi fun _ : Fin n => uniformOfFintype C).map fun cs i => (ys i, cs i) := by
  classical
  ext w
  rw [pi_apply, bind_apply, tsum_eq_single (fun i => (w i).1) fun ys hys => ?_]
  · rw [map_apply, tsum_eq_single (fun i => (w i).2) fun cs hcs => ?_]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), pi_apply, pi_apply, ← prod_mul_distrib]
      exact prod_congr rfl fun i _ => bind_map_prodMk_apply P _ (w i).1 (w i).2
    · refine ite_eq_right_of_eq_false _ _ (eq_false fun h => hcs ?_)
      funext i
      rw [h]
  · rw [map_apply, ENNReal.tsum_eq_zero.2 fun cs => ?_, mul_zero]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun h => hys ?_)
    funext i
    rw [h]

/-- **The first accepted attempt** among attempts `(ys i, cs i)`, in the shape of
`List.findSome?` over the attempts. -/
def firstAccept (acc : Y → C → Bool) {n : ℕ} (ys : Fin n → Y) (cs : Fin n → C) :
    Option (Y × C) :=
  (List.finRange n).findSome? fun i => if acc (ys i) (cs i) then some (ys i, cs i) else none

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **With fresh challenges, the loop output is bounded rejection sampling**: the first accepted
attempt of `freshChallenges` has the law `firstSome (rejectionAttempt P acc) n`. -/
theorem map_freshChallenges_firstAccept (P : PMF Y) (f : Y → X) (acc : Y → C → Bool) (n : ℕ) :
    (freshChallenges P f n).map (fun w => firstAccept acc w.2.1 w.2.2) =
      firstSome (rejectionAttempt P acc) n := by
  rw [firstSome_eq_map_pi, rejectionAttempt_eq_map, ← pi_map, map_comp, pi_withUniform, map_bind,
    freshChallenges, map_bind]
  congr 1
  funext ys
  rw [map_comp, map_comp, pi_uniformOfFintype]
  conv_lhs => rw [show ((fun w : (X → C) × (Fin n → Y) × (Fin n → C) =>
      firstAccept acc w.2.1 w.2.2) ∘ fun Hc : (X → C) × (Fin n → C) =>
        (reprogram (fun i => f (ys i)) Hc.2 Hc.1, ys, Hc.2)) =
    (fun cs => firstAccept acc ys cs) ∘ Prod.snd from rfl, ← map_comp, map_snd_uniformOfFintype]
  rfl

/-- **The loop with a random oracle against the loop with fresh challenges**: jointly with the
oracle, the first accepted attempt with challenges `H (f (ys i))` is within `(n choose 2) · δ` of
the first accepted attempt with fresh challenges (whose law is `firstSome (rejectionAttempt P acc)
n`, `map_freshChallenges_firstAccept`) jointly with the oracle reprogrammed at every point drawn. -/
theorem tvDist_firstAccept_readChallenges_freshChallenges_le (P : PMF Y) (f : Y → X)
    (acc : Y → C → Bool) (n : ℕ) {δ : ℝ} (hδ : ∀ x, (P.map f x).toReal ≤ δ) :
    tvDist ((readChallenges (C := C) P f n).map fun w => (w.1, firstAccept acc w.2.1 w.2.2))
        ((freshChallenges P f n).map fun w => (w.1, firstAccept acc w.2.1 w.2.2)) ≤
      n.choose 2 * δ :=
  (tvDist_map_le _ _ _).trans (tvDist_readChallenges_freshChallenges_le P f n hδ)

end Loop

end PMF
