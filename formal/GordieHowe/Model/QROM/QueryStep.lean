-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Compressed
public import GordieHowe.Model.QROM.Instability

@[expose] public section

/-!
# CMS19 Lemma 5.10: one query of the compressed oracle

Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum Random Oracle Model" (CMS19, ePrint
2019/834), Lemma 5.10 (p. 22): "For any database property P, ‖P(P_t O P_t)P̄‖² ≤ 6 I(P, t)."

The proof includes the inputs with `|D| = t`, `D(x) ≠ ⊥`, `u ≠ 0^n`, which the paper's proof (pp.
25–29) omits, and is organised by the blocks of `Dec_x` (`GordieHowe/Model/QROM/Compressed.lean`, "`Dec` is
unitary"). The operator `O` acts on each `|x, u, z⟩` separately, as `Dec_x Φ_u Dec_x` on the
database register, where `Φ_u` multiplies `|D⟩` by `(−1)^{u·D(x)}`. `Dec_x = 1 − ∑_B w_B w_Bᵀ` is a
sum of reflections over the blocks `B = {|D₀⟩} ∪ {|D₀ + [x ↦ y]⟩ : y}` (`x ∉ supp(D₀)`, `|D₀| < t`),
and `Φ_u` preserves the blocks, so for `|D'⟩ ≠ |D⟩` (`reflKernel_sandwich`):

    ⟨D'| O |D⟩ = −[same block] w(D') w(D) ((−1)^{u·D'(x)} + (−1)^{u·D(x)} − c_B),

with `c_B = 1` for `u ≠ 0^n` and every entry `0` for `u = 0^n`. On one block, with
`χ(y) = (−1)^{u·y}`, `β_{w,y} = 1 − χ(w) − χ(y)` and `ρ = 1/√2^n`, this is CMS19's matrix: from
`|D₀⟩` to `|D₀ + [x ↦ y]⟩` the entry `ρ χ(y)` (`Φ2`), from `|D₀ + [x ↦ w]⟩` to `|D₀⟩` the entry
`ρ χ(w)` (`Φ4`), and between `|D₀ + [x ↦ w]⟩` and `|D₀ + [x ↦ y]⟩` the entry `ρ² β_{w,y}` (`Φ5`);
the inputs with `|D| = t` and `D(x) ≠ ⊥`, which the paper omits, are the block members
`|D₀ + [x ↦ w]⟩` with `|D₀| = t − 1`. Then for a state `α` on `P̄`:

- if `D₀ ∈ P̄` (the paper's `Ξ1` and `Ξ3`, merged), the weight landing in `P` is
  `∑_{y ∈ S_P} |ρ χ(y) α_{D₀} − ρ² ∑_w β_{w,y} α_w|² ≤ 6 · |S_P|/2^n · ‖α‖²`
  (`block_bound_bot_notMem`), with `|S_P|/2^n ≤ flip(P̄ → P, t)`;
- if `D₀ ∈ P` (the paper's `Ψ4` and `Ξ2`), it is
  `|ρ ∑_w χ(w) α_w|² + ∑_{y ∈ S_P} |ρ² ∑_w β_{w,y} α_w|² ≤ (1 + 5) · |S_P̄|/2^n · ‖α‖²`
  (`block_bound_bot_mem`), with `|S_P̄|/2^n ≤ flip(P → P̄, t)`.

Both use `∑_y β_{w,y}² = 2^n (3 − 2χ(w)) ≤ 5 · 2^n` (`sum_beta_sq`), which needs `u ≠ 0^n`.
-/

open Finset GordieHowe.Quantum
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

/-! ### Two inequalities on one block -/

section Block

variable {Y : Type} [Fintype Y] (χ : Y → ℝ)

/-- A finite sum with real coefficients: `‖∑ cᵢ zᵢ‖² ≤ (∑ cᵢ²)(∑ ‖zᵢ‖²)`. -/
theorem norm_sum_mul_sq_le {ι : Type} (s : Finset ι) (c : ι → ℝ) (z : ι → ℂ) :
    ‖∑ i ∈ s, (c i : ℂ) * z i‖ ^ 2 ≤ (∑ i ∈ s, c i ^ 2) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, (c i : ℂ) * z i‖ ≤ ∑ i ∈ s, |c i| * ‖z i‖ :=
    (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs])
  calc ‖∑ i ∈ s, (c i : ℂ) * z i‖ ^ 2 ≤ (∑ i ∈ s, |c i| * ‖z i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i ∈ s, |c i| ^ 2) * ∑ i ∈ s, ‖z i‖ ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by simp only [sq_abs]

variable {χ}

/-- **`∑_y β_{w,y}² = 2^n (3 − 2χ(w))`** for signs `χ` with `∑_y χ(y) = 0`, where
`β_{w,y} = χ(y) + χ(w) − 1` (the paper's `−β`). -/
theorem sum_beta_sq (hχ : ∀ y, χ y * χ y = 1) (hsum : ∑ y, χ y = 0) (w : Y) :
    ∑ y, (χ y + χ w - 1) ^ 2 = Fintype.card Y * (3 - 2 * χ w) := by
  have : ∀ y, (χ y + χ w - 1) ^ 2 = (3 - 2 * χ w) + (2 * χ w - 2) * χ y := fun y => by
    have h1 := hχ y
    have h2 := hχ w
    nlinarith
  simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_beta_sq_le (hχ : ∀ y, χ y * χ y = 1) (hsum : ∑ y, χ y = 0) (w : Y) :
    ∑ y, (χ y + χ w - 1) ^ 2 ≤ (5 : ℝ) * Fintype.card Y := by
  rw [sum_beta_sq hχ hsum]
  have : -1 ≤ χ w := by nlinarith [hχ w]
  have hN : (0 : ℝ) ≤ Fintype.card Y := Nat.cast_nonneg _
  nlinarith

/-- The entries `w` of `√2 u` on a block: `1` at `|D₀⟩`, `−ρ` at `|D₀ + [x ↦ y]⟩`. -/
def blockW (ρ : ℝ) : Option Y → ℝ
  | none => 1
  | some _ => -ρ

/-- The phases `(−1)^{u·D(x)}` on a block: `1` at `|D₀⟩`, `χ(y)` at `|D₀ + [x ↦ y]⟩`. -/
def blockΦ (χ : Y → ℝ) : Option Y → ℝ
  | none => 1
  | some y => χ y

theorem sum_ite_eq_sum_filter {M : Type*} [AddCommMonoid M] (p : Y → Prop) [DecidablePred p]
    (f : Y → M) : ∑ y, (if p y then f y else 0) = ∑ y ∈ univ.filter p, f y :=
  (Finset.sum_filter _ _).symm

theorem sum_ite_zero_eq_sum_filter {M : Type*} [AddCommMonoid M] (p : Y → Prop) [DecidablePred p]
    (f : Y → M) : ∑ y, (if p y then 0 else f y) = ∑ y ∈ univ.filter (fun y => ¬ p y), f y := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun y _ => by by_cases h : p y <;> simp [h]

variable {ρ : ℝ} (hρ : ρ * ρ * Fintype.card Y = 1) (hχ : ∀ y, χ y * χ y = 1)
  (hsum : ∑ y, χ y = 0)
include hρ hχ hsum

/-- **The block bound when `D₀ ∈ P̄`** (CMS19's `Ξ1` and `Ξ3`, merged): the inputs are
`α_⊥` at `|D₀⟩` and `α_w` at `|D₀ + [x ↦ w]⟩` for `w ∈ T`, the outputs `|D₀ + [x ↦ y]⟩` for
`y ∈ S`, and `S, T` are disjoint. -/
theorem block_bound_bot_notMem (S T : Finset Y) (aBot : ℂ) (a : Y → ℂ) :
    ∑ y ∈ S, ‖(ρ * χ y : ℝ) * aBot - ∑ w ∈ T, ((ρ * ρ * (χ y + χ w - 1) : ℝ) : ℂ) * a w‖ ^ 2 ≤
      6 * (S.card / Fintype.card Y) * (‖aBot‖ ^ 2 + ∑ w ∈ T, ‖a w‖ ^ 2) := by
  have hN : (0 : ℝ) < Fintype.card Y := by
    rcases Nat.eq_zero_or_pos (Fintype.card Y) with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hρ
      exact absurd hρ zero_ne_one
    · exact_mod_cast h
  set A := ∑ w ∈ T, ‖a w‖ ^ 2
  have hterm : ∀ y ∈ S, ‖(ρ * χ y : ℝ) * aBot - ∑ w ∈ T, ((ρ * ρ * (χ y + χ w - 1) : ℝ) : ℂ) * a w‖ ^ 2
      ≤ 6 * (ρ * ρ * ‖aBot‖ ^ 2) + 6 * (ρ * ρ * A) := by
    intro y _
    set p := ‖((ρ * χ y : ℝ) : ℂ) * aBot‖
    set q := ‖∑ w ∈ T, ((ρ * ρ * (χ y + χ w - 1) : ℝ) : ℂ) * a w‖
    have hp : p ^ 2 = ρ * ρ * ‖aBot‖ ^ 2 := by
      simp only [p, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [show χ y ^ 2 = 1 by nlinarith [hχ y]]
      ring
    have hq : q ^ 2 ≤ 5 * (ρ * ρ * A) := by
      calc q ^ 2 ≤ (∑ w ∈ T, (ρ * ρ * (χ y + χ w - 1)) ^ 2) * A := norm_sum_mul_sq_le _ _ _
        _ ≤ (ρ * ρ) ^ 2 * (5 * Fintype.card Y) * A := by
            gcongr
            calc ∑ w ∈ T, (ρ * ρ * (χ y + χ w - 1)) ^ 2
                = (ρ * ρ) ^ 2 * ∑ w ∈ T, (χ w + χ y - 1) ^ 2 := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun w _ => by ring
              _ ≤ (ρ * ρ) ^ 2 * ∑ w, (χ w + χ y - 1) ^ 2 := by
                  gcongr
                  exact Finset.subset_univ _
              _ ≤ (ρ * ρ) ^ 2 * (5 * Fintype.card Y) := by
                  gcongr
                  exact sum_beta_sq_le hχ hsum y
        _ = 5 * (ρ * ρ * A) := by
            have : (ρ * ρ) ^ 2 * (5 * Fintype.card Y) = 5 * (ρ * ρ) * (ρ * ρ * Fintype.card Y) := by
              ring
            rw [this, hρ]
            ring
    calc ‖(ρ * χ y : ℝ) * aBot - ∑ w ∈ T, ((ρ * ρ * (χ y + χ w - 1) : ℝ) : ℂ) * a w‖ ^ 2
        ≤ (p + q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ 6 * p ^ 2 + 6 / 5 * q ^ 2 := by nlinarith [sq_nonneg (5 * p - q)]
      _ ≤ 6 * (ρ * ρ * ‖aBot‖ ^ 2) + 6 * (ρ * ρ * A) := by rw [hp]; nlinarith
  calc _ ≤ ∑ y ∈ S, (6 * (ρ * ρ * ‖aBot‖ ^ 2) + 6 * (ρ * ρ * A)) := Finset.sum_le_sum hterm
    _ = S.card * (6 * (ρ * ρ) * (‖aBot‖ ^ 2 + A)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ = 6 * (S.card / Fintype.card Y) * (‖aBot‖ ^ 2 + A) := by
        have : ρ * ρ = 1 / Fintype.card Y := by
          field_simp
          linarith
        rw [this]
        ring

/-- **The block bound when `D₀ ∈ P`** (CMS19's `Ψ4` and `Ξ2`): the inputs are `α_w` at
`|D₀ + [x ↦ w]⟩` for `w ∈ T`, the outputs `|D₀⟩` and `|D₀ + [x ↦ y]⟩` for `y ∈ S`. -/
theorem block_bound_bot_mem (S T : Finset Y) (a : Y → ℂ) :
    ‖∑ w ∈ T, ((ρ * χ w : ℝ) : ℂ) * a w‖ ^ 2 +
      ∑ y ∈ S, ‖∑ w ∈ T, ((ρ * ρ * (χ y + χ w - 1) : ℝ) : ℂ) * a w‖ ^ 2 ≤
      6 * (T.card / Fintype.card Y) * ∑ w ∈ T, ‖a w‖ ^ 2 := by
  set A := ∑ w ∈ T, ‖a w‖ ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hρρ : ρ * ρ = 1 / Fintype.card Y := by
    have hN : (Fintype.card Y : ℝ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hρ
      exact zero_ne_one hρ
    field_simp
    linarith
  have h1 : ‖∑ w ∈ T, ((ρ * χ w : ℝ) : ℂ) * a w‖ ^ 2 ≤ T.card / Fintype.card Y * A := by
    refine (norm_sum_mul_sq_le _ _ _).trans_eq ?_
    congr 1
    calc ∑ w ∈ T, (ρ * χ w) ^ 2 = ∑ w ∈ T, ρ * ρ := Finset.sum_congr rfl fun w _ => by
          have := hχ w
          nlinarith
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hρρ]; ring
  have h2 : ∑ y ∈ S, ‖∑ w ∈ T, ((ρ * ρ * (χ y + χ w - 1) : ℝ) : ℂ) * a w‖ ^ 2 ≤
      5 * (T.card / Fintype.card Y) * A := by
    calc _ ≤ ∑ y ∈ S, (∑ w ∈ T, (ρ * ρ * (χ y + χ w - 1)) ^ 2) * A :=
          Finset.sum_le_sum fun y _ => norm_sum_mul_sq_le _ _ _
      _ = (ρ * ρ) ^ 2 * (∑ w ∈ T, ∑ y ∈ S, (χ y + χ w - 1) ^ 2) * A := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ => by ring
      _ ≤ (ρ * ρ) ^ 2 * (∑ w ∈ T, 5 * (Fintype.card Y : ℝ)) * A := by
          gcongr with w _
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            fun _ _ _ => sq_nonneg _).trans (sum_beta_sq_le hχ hsum w)
      _ = 5 * (T.card / Fintype.card Y) * A := by
          rw [Finset.sum_const, nsmul_eq_mul, hρρ]
          have hN : (Fintype.card Y : ℝ) ≠ 0 := by
            intro h
            rw [h, mul_zero] at hρ
            exact zero_ne_one hρ
          field_simp
  linarith


/-- **The bound on one block**: the matrix `−w(o') w(o) (φ(o') + φ(o) − 1)` from the members
outside `S` (`P̄`) to the members in `S` (`P`) moves at most `6 f` of the weight, where `f` is the
fraction of the members `|D₀ + [x ↦ y]⟩` on the other side from `|D₀⟩`. -/
theorem block_fiber (S : Option Y → Prop) [DecidablePred S] (a : Option Y → ℂ) :
    ∑ o', (if S o' then ‖∑ o, (if S o then 0 else
        -(((blockW ρ o' * blockW ρ o : ℝ) : ℂ) * ((blockΦ χ o' + blockΦ χ o - 1 : ℝ) : ℂ)) * a o)‖ ^ 2
      else 0) ≤
      6 * (((if S none then (univ.filter fun y => ¬ S (some y)).card
        else (univ.filter fun y => S (some y)).card : ℕ) : ℝ) / Fintype.card Y) *
        ∑ o, (if S o then 0 else ‖a o‖ ^ 2) := by
  set T := univ.filter fun y => ¬ S (some y)
  set Sf := univ.filter fun y => S (some y)
  by_cases hS : S none
  · have h0 : ∑ o, (if S o then 0 else
        -(((blockW ρ (none : Option Y) * blockW ρ o : ℝ) : ℂ) *
          ((blockΦ χ (none : Option Y) + blockΦ χ o - 1 : ℝ) : ℂ)) * a o) =
        ∑ w ∈ T, ((ρ * χ w : ℝ) : ℂ) * a (some w) := by
      rw [Fintype.sum_option, if_pos hS, zero_add]
      rw [sum_ite_zero_eq_sum_filter (fun w => S (some w))]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [blockW, blockΦ]
      push_cast
      ring
    have hy : ∀ y, ∑ o, (if S o then 0 else
        -(((blockW ρ (some y) * blockW ρ o : ℝ) : ℂ) *
          ((blockΦ χ (some y) + blockΦ χ o - 1 : ℝ) : ℂ)) * a o) =
        -∑ w ∈ T, ((ρ * ρ * (χ y + χ w - 1) : ℝ) : ℂ) * a (some w) := by
      intro y
      rw [Fintype.sum_option, if_pos hS, zero_add, ← Finset.sum_neg_distrib]
      rw [sum_ite_zero_eq_sum_filter (fun w => S (some w))]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [blockW, blockΦ]
      push_cast
      ring
    rw [Fintype.sum_option, if_pos hS, h0, if_pos hS, Fintype.sum_option, if_pos hS, zero_add]
    simp_rw [hy, norm_neg]
    rw [sum_ite_eq_sum_filter (fun y => S (some y)),
      sum_ite_zero_eq_sum_filter (fun w => S (some w)) (fun w => ‖a (some w)‖ ^ 2)]
    exact block_bound_bot_mem hρ hχ hsum Sf T (fun w => a (some w))
  · have hy : ∀ y, ∑ o, (if S o then 0 else
        -(((blockW ρ (some y) * blockW ρ o : ℝ) : ℂ) *
          ((blockΦ χ (some y) + blockΦ χ o - 1 : ℝ) : ℂ)) * a o) =
        ((ρ * χ y : ℝ) : ℂ) * a none - ∑ w ∈ T, ((ρ * ρ * (χ y + χ w - 1) : ℝ) : ℂ) * a (some w) := by
      intro y
      rw [Fintype.sum_option, if_neg hS, sub_eq_add_neg (((ρ * χ y : ℝ) : ℂ) * a none),
        ← Finset.sum_neg_distrib]
      congr 1
      · simp only [blockW, blockΦ]
        push_cast
        ring
      · rw [sum_ite_zero_eq_sum_filter (fun w => S (some w))]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [blockW, blockΦ]
        push_cast
        ring
    rw [Fintype.sum_option, if_neg hS, zero_add, Fintype.sum_option, if_neg hS]
    simp_rw [hy]
    rw [sum_ite_eq_sum_filter (fun y => S (some y)),
      sum_ite_zero_eq_sum_filter (fun w => S (some w)) (fun w => ‖a (some w)‖ ^ 2), if_neg hS]
    exact block_bound_bot_notMem hρ hχ hsum Sf T (a none) (fun w => a (some w))

end Block

/-! ### The matrix of `O` -/

section Matrix

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ} {B : Type}
  (e : BitStr I J ≃ B) {t : ℕ}


/-- `(−1)^z` as a real number. -/
def signR (z : ZMod 2) : ℝ := (-1) ^ z.val

theorem signOf_eq (z : ZMod 2) : signOf z = (signR z : ℂ) := by
  simp [signOf, signR]

theorem signR_mul_self (z : ZMod 2) : signR z * signR z = 1 := by
  have h := signOf_mul_self z
  rw [signOf_eq] at h
  exact_mod_cast h

open Classical in
/-- `Dec_x Φ_u Dec_x` on the database register: the matrix of `O` on `|x, u, z⟩`. -/
noncomputable def qMatrix (x : Bits m) (u : BitStr I J) (s' s : Slots I J m t) : ℂ :=
  ∑ k, reflKernel (decBlock e t x) (decAmp e t x) s' k *
    (dbPhase e u x (slotsDB e k) * reflKernel (decBlock e t x) (decAmp e t x) k s)

open Classical in
/-- **The matrix of `O = Dec ∘ O0 ∘ Dec`**: `qMatrix` on the database register of each
`|x, u, z⟩`. -/
theorem compressedOracle_apply {W : Type} [Fintype W] [DecidableEq W]
    (v : QState (SimRegister W I J m t)) (b' : SimRegister W I J m t) :
    compressedOracle e W t v b' =
      ∑ s, qMatrix e (qIn b'.1) (qAns b'.1) b'.2 s * v (b'.1, s) := by
  set D : SimRegister W I J m t → SimRegister W I J m t → ℂ := fun b' b =>
    if b'.1 = b.1 then reflKernel (decBlock e t (qIn b.1)) (decAmp e t (qIn b.1)) b'.2 b.2 else 0
  set Ph : SimRegister W I J m t → SimRegister W I J m t → ℂ := fun b' b =>
    if b' = b then dbPhase e (qAns b.1) (qIn b.1) (slotsDB e b.2) else 0
  have hPD : ∀ b' k : SimRegister W I J m t, ∑ l, D b' l * Ph l k =
      D b' k * dbPhase e (qAns k.1) (qIn k.1) (slotsDB e k.2) := by
    intro b' k
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ph, hl]) (by simp)]
    simp [Ph]
  have hDPD : ∀ b' b : SimRegister W I J m t, ∑ k, (∑ l, D b' l * Ph l k) * D k b =
      if b'.1 = b.1 then qMatrix e (qIn b.1) (qAns b.1) b'.2 b.2 else 0 := by
    intro b' b
    simp_rw [hPD]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b'.1]
    · by_cases h : b'.1 = b.1
      · rw [if_pos h, qMatrix]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [D, if_pos h, if_true]
        rw [h]
        ring
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [D, h]
    · intro r _ hr
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [D, Ne.symm hr]
    · simp
  rw [compressedOracle, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, decOp_eq,
    phaseOp, kernelOp_kernelOp, kernelOp_kernelOp, kernelOp_apply]
  change ∑ b, (∑ k, (∑ l, D b' l * Ph l k) * D k b) * v b = _
  simp_rw [hDPD]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b'.1]
  · simp
  · intro r _ hr
    exact Finset.sum_eq_zero fun s _ => by simp [Ne.symm hr]
  · simp

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem ne_of_inP {P : Set (DB (Bits m) B)} {s' s : Slots I J m t} (h1 : InP e t P s')
    (h2 : InP e t Pᶜ s) : s' ≠ s := by
  rintro rfl
  obtain ⟨D, hD, hDt, rfl⟩ := h1
  obtain ⟨D', hD', hD't, h⟩ := h2
  exact hD' ((dbSlots_inj e hDt hD't).1 h.symm ▸ hD)

section BlockFacts

variable {x : Bits m} {D₀ : DB (Bits m) B} (hx : x ∉ D₀) (hsz : D₀.size < t)
include hx hsz

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem inP_blockSlot (P : Set (DB (Bits m) B)) (o : Option (BitStr I J)) :
    InP e t P (blockSlot e t x D₀ o) ↔ blockDB e x D₀ o ∈ P := by
  rw [blockSlot_eq e]
  constructor
  · rintro ⟨D, hD, hDt, h⟩
    rwa [(dbSlots_inj e hDt (size_blockDB_le e hx hsz o)).1 h]
  · intro h
    exact ⟨_, h, size_blockDB_le e hx hsz o, rfl⟩

omit [DecidableEq I] [DecidableEq J] in
theorem dbPhase_blockSlot (u : BitStr I J) (o : Option (BitStr I J)) :
    dbPhase e u x (slotsDB e (blockSlot e t x D₀ o)) =
      ((blockΦ (fun y => signR (u.dot y)) o : ℝ) : ℂ) := by
  rw [slotsDB_blockSlot e hx hsz]
  cases o with
  | none =>
    simp [dbPhase, blockDB, blockΦ, Finmap.lookup_eq_none.2 hx]
  | some y =>
    simp [dbPhase, blockDB, blockΦ, DB.lookup_extend_self, signOf_eq]

theorem decAmp_blockSlot (o : Option (BitStr I J)) :
    decAmp e t x (blockSlot e t x D₀ o) = blockW (invSqrtCardR I J) o := by
  cases o with
  | none => exact decAmp_blockSlot_none e hx hsz
  | some y => exact decAmp_blockSlot_some e hx hsz y

end BlockFacts

open Classical in
/-- The fraction of the one-entry extensions of `D₀` that lie in `Q` is at most a flip
probability. -/
theorem card_filter_div_le_flipProb [Fintype B] [Nonempty B] {P' Q : Set (DB (Bits m) B)}
    {x : Bits m} {D₀ : DB (Bits m) B} (hD : D₀ ∈ P') (hsz : D₀.size < t) (hx : x ∉ D₀) :
    ((univ.filter fun y : BitStr I J => DB.extend D₀ x (e y) ∈ Q).card : ℝ) /
      Fintype.card (BitStr I J) ≤ (flipProb P' Q t).toReal := by
  have h := le_flipProb (Q := Q) hD hsz hx
  rw [IOP.probUniform_eq_card_div] at h
  have hcard : (univ.filter fun b : B => DB.extend D₀ x b ∈ Q).card =
      (univ.filter fun y : BitStr I J => DB.extend D₀ x (e y) ∈ Q).card := by
    refine Finset.card_bij' (fun b _ => e.symm b) (fun y _ => e y) ?_ ?_ ?_ ?_ <;> simp
  have hB : Fintype.card B = Fintype.card (BitStr I J) := (Fintype.card_congr e).symm
  rw [hcard, hB] at h
  have hne : flipProb P' Q t ≠ ⊤ := (flipProb_le_one.trans_lt ENNReal.one_lt_top).ne
  have := ENNReal.toReal_mono hne h
  rwa [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this

open Classical in
/-- **One query on one `|x, u, z⟩`, for a state on small databases**: from a state on `P̄` that
vanishes on every block of `Dec_x` whose base database `D₀` has at least `n` entries,
`Dec_x Φ_u Dec_x` puts at most `6 I(P, n)` of its weight on `P`. The matrix splits over the
blocks of `Dec_x` (`reflKernel_sandwich`), each block is `block_fiber`, and its fraction is a flip
probability (`card_filter_div_le_flipProb`) at a base database with fewer than `n` entries. At
`n = t` the hypothesis always holds (`fiber_bound`). -/
theorem fiber_bound_of_small [Fintype B] [Nonempty B] (x : Bits m) (u : BitStr I J)
    (P : Set (DB (Bits m) B)) (α : Slots I J m t → ℂ) (n : ℕ)
    (hα : ∀ s D₀, decBlock e t x s = some D₀ → n ≤ D₀.size → α s = 0) :
    ∑ s', (if InP e t P s' then
        ‖∑ s, (if InP e t Pᶜ s then qMatrix e x u s' s * α s else 0)‖ ^ 2 else 0) ≤
      6 * (instab P n).toReal * ∑ s, (if InP e t Pᶜ s then ‖α s‖ ^ 2 else 0) := by
  set blk := decBlock e t x
  set w := decAmp e t x
  set φ : Slots I J m t → ℂ := fun k => dbPhase e u x (slotsDB e k)
  set c : Option (DB (Bits m) B) → ℂ :=
    fun β => ∑ k, (if blk k = β then ((w k ^ 2 : ℝ) : ℂ) * φ k else 0)
  have hq : ∀ s' s, InP e t P s' → InP e t Pᶜ s → qMatrix e x u s' s =
      -(if blk s' = blk s then ((w s' * w s : ℝ) : ℂ) * (φ s' + φ s - c (blk s)) else 0) :=
    fun s' s h1 h2 => reflKernel_sandwich _ _ φ (ne_of_inP e h1 h2)
  set F : Slots I J m t → ℝ := fun s' => if InP e t P s' then
    ‖∑ s, (if InP e t Pᶜ s then qMatrix e x u s' s * α s else 0)‖ ^ 2 else 0
  set H : Slots I J m t → ℝ := fun s => if InP e t Pᶜ s then ‖α s‖ ^ 2 else 0
  have hfib : ∀ G : Slots I J m t → ℝ,
      ∑ s, G s = ∑ β ∈ univ.image blk, ∑ s, (if blk s = β then G s else 0) := by
    intro G
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image blk) (g := blk)
      (fun s _ => Finset.mem_image_of_mem _ (Finset.mem_univ s)) G]
    simp_rw [Finset.sum_filter]
  have hI : 0 ≤ (instab P n).toReal := ENNReal.toReal_nonneg
  change ∑ s', F s' ≤ 6 * (instab P n).toReal * ∑ s, H s
  rw [hfib F, hfib H, Finset.mul_sum]
  refine Finset.sum_le_sum fun β hβ => ?_
  have hH : 0 ≤ ∑ s, (if blk s = β then H s else 0) := Finset.sum_nonneg fun s _ => by
    simp only [H]
    split_ifs <;> positivity
  obtain ⟨s₀, -, hs₀⟩ := Finset.mem_image.1 hβ
  cases β with
  | none =>
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun s' _ => ?_)) (by positivity)
    by_cases hb : blk s' = none
    · rw [if_pos hb]
      simp only [F]
      by_cases h1 : InP e t P s'
      · have hw : w s' = 0 := by simp [w, decAmp, blk, hb]
        rw [if_pos h1, Finset.sum_eq_zero fun s _ => ?_, norm_zero]
        · norm_num
        · by_cases h2 : InP e t Pᶜ s
          · rw [if_pos h2, hq s' s h1 h2]
            simp [hw]
          · rw [if_neg h2]
      · rw [if_neg h1]
    · rw [if_neg hb]
  | some D₀ =>
    obtain ⟨hx, hsz⟩ := decBlock_eq_some e hs₀
    by_cases hn : D₀.size < n
    swap
    · -- a block on databases with at least `n` entries carries no weight
      have h0 : ∀ s, decBlock e t x s = some D₀ → α s = 0 := fun s hs => hα s D₀ hs (not_lt.1 hn)
      refine le_trans (le_of_eq (Finset.sum_eq_zero fun s' _ => ?_)) (mul_nonneg (by positivity) hH)
      by_cases hb : blk s' = some D₀
      · rw [if_pos hb]
        simp only [F]
        split_ifs with h1
        · rw [Finset.sum_eq_zero fun s _ => ?_, norm_zero]
          · norm_num
          · by_cases h2 : InP e t Pᶜ s
            · rw [if_pos h2]
              by_cases hbs : blk s = some D₀
              · rw [h0 s hbs, mul_zero]
              · rw [hq s' s h1 h2, if_neg (fun h => hbs (h.symm.trans hb)), neg_zero, zero_mul]
            · rw [if_neg h2]
        · rfl
      · rw [if_neg hb]
    set g := blockSlot e t x D₀
    set S : Option (BitStr I J) → Prop := fun o => blockDB e x D₀ o ∈ P
    set ρ := invSqrtCardR I J
    set χ : BitStr I J → ℝ := fun y => signR (u.dot y)
    have hρ : ρ * ρ * Fintype.card (BitStr I J) = 1 := invSqrtCardR_sq_mul_card
    have hχ : ∀ y, χ y * χ y = 1 := fun y => signR_mul_self _
    have hblk : ∀ o, blk (g o) = some D₀ := decBlock_blockSlot e hx hsz
    have hwg : ∀ o, w (g o) = blockW ρ o := decAmp_blockSlot e hx hsz
    have hφg : ∀ o, φ (g o) = ((blockΦ χ o : ℝ) : ℂ) := dbPhase_blockSlot e hx hsz u
    have hc : c (some D₀) = ∑ o, ((blockW ρ o ^ 2 * blockΦ χ o : ℝ) : ℂ) := by
      simp only [c]
      rw [sum_block e hx hsz (fun k => ((w k ^ 2 : ℝ) : ℂ) * φ k)]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [hwg, hφg]
      push_cast
      ring
    have hS : ∀ o, InP e t P (g o) ↔ S o := inP_blockSlot e hx hsz P
    have hSc : ∀ o, InP e t Pᶜ (g o) ↔ ¬ S o := inP_blockSlot e hx hsz Pᶜ
    -- the inner sums, on the block
    have hinner : ∀ o', S o' → ∑ s, (if InP e t Pᶜ s then qMatrix e x u (g o') s * α s else 0) =
        ∑ o, (if S o then 0 else -(((blockW ρ o' * blockW ρ o : ℝ) : ℂ) *
          (((blockΦ χ o' + blockΦ χ o : ℝ) : ℂ) - c (some D₀))) * α (g o)) := by
      intro o' hSo'
      have hP' : InP e t P (g o') := (hS o').2 hSo'
      calc ∑ s, (if InP e t Pᶜ s then qMatrix e x u (g o') s * α s else 0)
          = ∑ s, (if blk s = some D₀ then
              (if InP e t Pᶜ s then qMatrix e x u (g o') s * α s else 0) else 0) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases hb : blk s = some D₀
            · rw [if_pos hb]
            · rw [if_neg hb]
              by_cases h2 : InP e t Pᶜ s
              · rw [if_pos h2, hq _ s hP' h2, hblk o', if_neg (fun h => hb h.symm)]
                simp
              · rw [if_neg h2]
        _ = ∑ o, (if InP e t Pᶜ (g o) then qMatrix e x u (g o') (g o) * α (g o) else 0) :=
            sum_block e hx hsz (fun s => if InP e t Pᶜ s then qMatrix e x u (g o') s * α s else 0)
        _ = _ := by
            refine Finset.sum_congr rfl fun o _ => ?_
            by_cases ho : S o
            · rw [if_pos ho, if_neg (fun h => ((hSc o).1 h) ho)]
            · rw [if_neg ho, if_pos ((hSc o).2 ho), hq _ _ hP' ((hSc o).2 ho), hblk, hblk, if_pos rfl,
                hwg, hwg, hφg, hφg]
              push_cast
              ring
    have hLHS : ∑ s', (if blk s' = some D₀ then F s' else 0) =
        ∑ o', (if S o' then ‖∑ o, (if S o then 0 else -(((blockW ρ o' * blockW ρ o : ℝ) : ℂ) *
          (((blockΦ χ o' + blockΦ χ o : ℝ) : ℂ) - c (some D₀))) * α (g o))‖ ^ 2 else 0) := by
      rw [sum_block e hx hsz F]
      refine Finset.sum_congr rfl fun o' _ => ?_
      simp only [F]
      by_cases ho : S o'
      · rw [if_pos ((hS o').2 ho), if_pos ho, hinner o' ho]
      · rw [if_neg (fun h => ho ((hS o').1 h)), if_neg ho]
    have hRHS : ∑ s, (if blk s = some D₀ then H s else 0) =
        ∑ o, (if S o then 0 else ‖α (g o)‖ ^ 2) := by
      rw [sum_block e hx hsz H]
      refine Finset.sum_congr rfl fun o _ => ?_
      simp only [H]
      by_cases ho : S o
      · rw [if_pos ho, if_neg (fun h => ((hSc o).1 h) ho)]
      · rw [if_neg ho, if_pos ((hSc o).2 ho)]
    rw [hLHS, hRHS]
    by_cases hu : u = 0
    · -- `u = 0^n`: `O` is the identity on the block, and no weight moves
      have hχ1 : ∀ y, χ y = 1 := fun y => by
        simp only [χ, hu, BitStr.dot_comm 0 y, BitStr.dot_zero, signR, ZMod.val_zero, pow_zero]
      have hc2 : c (some D₀) = 2 := by
        rw [hc, Fintype.sum_option]
        simp only [blockW, blockΦ, hχ1]
        push_cast
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : ((ρ : ℂ) * ρ * Fintype.card (BitStr I J)) = 1 := by exact_mod_cast hρ
        linear_combination this
      have hzero : ∀ o' o, ((blockΦ χ o' + blockΦ χ o : ℝ) : ℂ) - c (some D₀) = 0 := by
        intro o' o
        rw [hc2]
        cases o' <;> cases o <;> simp [blockΦ, hχ1] <;> norm_num
      refine le_trans (le_of_eq (Finset.sum_eq_zero fun o' _ => ?_)) ?_
      · split_ifs
        · rw [Finset.sum_eq_zero fun o _ => ?_, norm_zero]
          · norm_num
          · split_ifs
            · rfl
            · rw [hzero o' o, mul_zero, neg_zero, zero_mul]
        · rfl
      · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun o _ => by split_ifs <;> positivity)
    · -- `u ≠ 0^n`: `c = 1`, and the block bound applies
      have hsum : ∑ y, χ y = 0 := by
        have h := sum_signOf_dot u
        rw [if_neg hu] at h
        have : ∑ y, (χ y : ℂ) = 0 := by
          rw [← h]
          refine Finset.sum_congr rfl fun y _ => ?_
          simp only [χ, BitStr.dot_comm u y, signOf_eq]
        exact_mod_cast this
      have hc1 : c (some D₀) = 1 := by
        rw [hc, Fintype.sum_option]
        simp only [blockW, blockΦ]
        push_cast
        rw [← Finset.mul_sum]
        have : ∑ y, (χ y : ℂ) = 0 := by exact_mod_cast hsum
        rw [this]
        ring
      have hconv : ∀ o' o, ((blockΦ χ o' + blockΦ χ o : ℝ) : ℂ) - c (some D₀) =
          ((blockΦ χ o' + blockΦ χ o - 1 : ℝ) : ℂ) := by
        intro o' o
        rw [hc1]
        push_cast
        ring
      simp_rw [hconv]
      refine (block_fiber hρ hχ hsum S (fun o => α (g o))).trans ?_
      gcongr
      · by_cases hS0 : S none
        · rw [if_pos hS0, show (univ.filter fun y => ¬ S (some y)) =
              univ.filter fun y : BitStr I J => DB.extend D₀ x (e y) ∈ Pᶜ from
            Finset.filter_congr fun y _ => Iff.rfl]
          convert (card_filter_div_le_flipProb e (P' := P) (Q := Pᶜ) (D₀ := D₀) hS0 hn hx).trans
            (ENNReal.toReal_mono (instab_le_one.trans_lt ENNReal.one_lt_top).ne
              flipProb_to_compl_le_instab)
        · rw [if_neg hS0, show (univ.filter fun y => S (some y)) =
              univ.filter fun y : BitStr I J => DB.extend D₀ x (e y) ∈ P from
            Finset.filter_congr fun y _ => Iff.rfl]
          convert (card_filter_div_le_flipProb e (P' := Pᶜ) (Q := P) (D₀ := D₀) hS0 hn hx).trans
            (ENNReal.toReal_mono (instab_le_one.trans_lt ENNReal.one_lt_top).ne
              flipProb_compl_le_instab)
open Classical in
/-- **One query on one `|x, u, z⟩`**: from a state on `P̄`, `Dec_x Φ_u Dec_x` puts at most
`6 I(P, t)` of its weight on `P` (`fiber_bound_of_small` at `n = t`: every block's base database
has fewer than `t` entries). -/
theorem fiber_bound [Fintype B] [Nonempty B] (x : Bits m) (u : BitStr I J)
    (P : Set (DB (Bits m) B)) (α : Slots I J m t → ℂ) :
    ∑ s', (if InP e t P s' then
        ‖∑ s, (if InP e t Pᶜ s then qMatrix e x u s' s * α s else 0)‖ ^ 2 else 0) ≤
      6 * (instab P t).toReal * ∑ s, (if InP e t Pᶜ s then ‖α s‖ ^ 2 else 0) :=
  fiber_bound_of_small e x u P α t fun _ _ hs ht => absurd (decBlock_eq_some e hs).2 (not_lt.2 ht)

open Classical in
/-- **One query step on small databases**: `‖P O P̄ v‖² ≤ 6 I(P, n) ‖v‖²` for a state `v` that
vanishes on the basis states whose database register lies in a block of `Dec` at the query input
with base database of at least `n` entries (`fiber_bound_of_small` on each `|x, u, z⟩`). Every
block's base has fewer than `t` entries, so at `n = t` this holds for every state
(`query_step_le`). -/
theorem norm_dbProj_compressedOracle_sq_le [Fintype B] [Nonempty B] (W : Type) [Fintype W]
    [DecidableEq W] (P : Set (DB (Bits m) B)) (n : ℕ) (v : QState (SimRegister W I J m t))
    (hv : ∀ b D₀, decBlock e t (qIn b.1) b.2 = some D₀ → n ≤ D₀.size → v b = 0) :
    ‖dbProj e W t P (compressedOracle e W t (dbProj e W t Pᶜ v))‖ ^ 2 ≤
      6 * (instab P n).toReal * ‖v‖ ^ 2 := by
  set κ := (instab P n).toReal
  have hκ : 0 ≤ κ := ENNReal.toReal_nonneg
  have hPc : ∀ (r : QueryReg W 1 (Bits m) (BitStr I J)) (s : Slots I J m t),
      dbProj e W t Pᶜ v (r, s) = if InP e t Pᶜ s then v (r, s) else 0 := by
    intro r s
    rw [dbProj_eq, mask_apply]
    rfl
  rw [dbProj_eq, norm_mask_sq, Finset.sum_filter, Fintype.sum_prod_type]
  calc ∑ r, ∑ s', (if (r, s') ∈ dbSet e W t P then
          ‖compressedOracle e W t (dbProj e W t Pᶜ v) (r, s')‖ ^ 2 else 0)
      = ∑ r, ∑ s', (if InP e t P s' then ‖∑ s, (if InP e t Pᶜ s then
          qMatrix e (qIn r) (qAns r) s' s * v (r, s) else 0)‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s' _ => ?_
        rw [compressedOracle_apply]
        simp only [hPc, mul_ite, mul_zero]
        rfl
    _ ≤ ∑ r, 6 * κ * ∑ s, (if InP e t Pᶜ s then ‖v (r, s)‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun r _ => fiber_bound_of_small e (qIn r) (qAns r) P
          (fun s => v (r, s)) n fun s D₀ hs hn => hv (r, s) D₀ hs hn
    _ = 6 * κ * ∑ b : SimRegister W I J m t, (if InP e t Pᶜ b.2 then ‖v b‖ ^ 2 else 0) := by
        rw [← Finset.mul_sum]
        congr 1
        exact (Fintype.sum_prod_type (fun b : SimRegister W I J m t =>
          if InP e t Pᶜ b.2 then ‖v b‖ ^ 2 else 0)).symm
    _ = 6 * κ * ‖dbProj e W t Pᶜ v‖ ^ 2 := by
        rw [dbProj_eq, norm_mask_sq, Finset.sum_filter]
        rfl
    _ ≤ 6 * κ * ‖v‖ ^ 2 := by
        gcongr
        exact norm_mask_le _ _

open Classical in
/-- **CMS19 Lemma 5.10** (p. 22): "For any database property P, ‖P(P_t O P_t)P̄‖² ≤ 6 I(P, t)."

Here `P` is `dbProj e W t P`, `P̄` is `dbProj e W t Pᶜ`, `P_t` is `sizeProj`, `O` is
`compressedOracle` with bound `t` (App. A's `Dec ∘ O0 ∘ Dec`), on the adversary's registers with any
work register `W` and the `t`-slot database register, and `I(P, t)` is `instab P t` (Def 5.6).
The paper's proof (pp. 25–29) omits the inputs with `|D| = t`, `D(x) ≠ ⊥`, `u ≠ 0^n`; this proof
includes them: `O` acts on each `|x, u, z⟩` by `qMatrix`, which splits
over the blocks of `Dec_x`, and each block moves at most `6 I(P, t)` of the weight
(`fiber_bound`). -/
theorem query_step_le [Fintype B] [Nonempty B] (W : Type) [Fintype W] [DecidableEq W] (t : ℕ)
    (P : Set (DB (Bits m) B)) :
    ‖dbProj e W t P ∘L queryStepOp e W t ∘L
      dbProj e W t Pᶜ‖ₑ ^ 2 ≤ 6 * instab P t := by
  set T := dbProj e W t P ∘L queryStepOp e W t ∘L
    dbProj e W t Pᶜ
  set κ := (instab P t).toReal
  have hκ : 0 ≤ κ := ENNReal.toReal_nonneg
  have hT : ∀ v, T v = dbProj e W t P (compressedOracle e W t (dbProj e W t Pᶜ v)) := by
    intro v
    simp only [T, queryStepOp, ContinuousLinearMap.comp_apply, sizeProj, dbProj_eq]
    rw [(mask_mask_of_subset (dbSet_subset_sizeSet e Pᶜ) v).2,
      (mask_mask_of_subset (dbSet_subset_sizeSet e P) _).1]
  have key : ∀ v, ‖T v‖ ^ 2 ≤ 6 * κ * ‖v‖ ^ 2 := fun v => by
    rw [hT]
    exact norm_dbProj_compressedOracle_sq_le e W P t v fun _ _ hs ht =>
      absurd (decBlock_eq_some e hs).2 (not_lt.2 ht)
  have hop : ‖T‖ ≤ Real.sqrt (6 * κ) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    rw [← Real.sqrt_sq (norm_nonneg (T v)), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul
      (by positivity)]
    exact Real.sqrt_le_sqrt (key v)
  have hne : instab P t ≠ ⊤ := (instab_le_one.trans_lt ENNReal.one_lt_top).ne
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  calc ENNReal.ofReal (‖T‖ ^ 2) ≤ ENNReal.ofReal (6 * κ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖T‖ ^ 2 ≤ Real.sqrt (6 * κ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
          _ = 6 * κ := Real.sq_sqrt (by positivity)
    _ = 6 * instab P t := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hne]
        norm_num

end Matrix

end GordieHowe.QROM
