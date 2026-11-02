-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.InformationSet

@[expose] public section

/-!
# Fibre sums over a code with information sets

Product weights `H v = ∏_i h i (ω v i)` on a parameter group `V`, read through an injective
additive map `ω : V → (ι → A)`, summed over the fibres `p + Q` of a code `P ⊕ Q`:

- `sum_sq_fibreSum_le` (H2 and H3 of the hybrid bound): if `ω (P + Q)` has an information set
  `J` and `ω Q` an information set `J₁ ⊆ J`, then
  `∑_{p ∈ P} (∑_{q ∈ Q} H (p + q))² ≤ S₂ ^ (#J - #J₁) · S₁ ^ (2 #J₁)`,
  for `0 ≤ h ≤ 1`, `∑_a h i a ≤ S₁` and `∑_a h i a² ≤ S₂`. Expanding the square and writing the
  second point of the fibre as a shift `e ∈ Q` of the first turns the sum into
  `∑_{e ∈ Q} ∑_{u ∈ P + Q} H u · H (u + e)`; the window `J` factors the inner sum into the
  autocorrelations `R_i (ω e i) = ∑_a h i a · h i (a + ω e i)`, each at most `S₂`, and the window
  `J₁` factors the remaining sum over `e` into `∏_{i ∈ J₁} ∑_d R_i d = ∏_{i ∈ J₁} (∑_a h i a)²`.
- `sum_fibreSum_mul_fibreSum_le` (H1 and the hybrid row bound): for an injective self-map `Φ`
  of `P` and two such codes `P ⊕ Q`, `P ⊕ Q'` with `#J - #J₁ = #J' - #J₁' = d`,
  `∑_{p ∈ P} (∑_{q ∈ Q} H (p + q)) (∑_{q ∈ Q'} H' (Φ p + q)) ≤ S₂ ^ d · S₁ ^ (#J₁ + #J₁')`,
  by Cauchy–Schwarz over `P`.

The bound pays `S₂` (the `ℓ²` mass) per coordinate of the shared part `P` and `S₁` (the `ℓ¹` mass)
per coordinate of the fibres, in place of `S₁` for every coordinate of the whole code.
-/

open Finset
open scoped BigOperators

namespace GordieHowe

section Autocorrelation

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The autocorrelation `R h d = ∑_a h a · h (a + d)` of a weight on a finite group. -/
def autocorrelation (h : A → ℝ) (d : A) : ℝ := ∑ a, h a * h (a + d)

theorem autocorrelation_nonneg {h : A → ℝ} (h0 : ∀ a, 0 ≤ h a) (d : A) :
    0 ≤ autocorrelation h d :=
  Finset.sum_nonneg fun a _ => mul_nonneg (h0 a) (h0 _)

/-- `R h d ≤ ∑_a h a ^ 2`, by `xy ≤ (x² + y²) / 2` and translation invariance. -/
theorem autocorrelation_le_sum_sq (h : A → ℝ) (d : A) :
    autocorrelation h d ≤ ∑ a, h a ^ 2 := by
  have hshift : ∑ a, h (a + d) ^ 2 = ∑ a, h a ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight d) _ _ fun a => rfl
  have : ∑ a, h a * h (a + d) ≤ ∑ a, (h a ^ 2 + h (a + d) ^ 2) / 2 :=
    Finset.sum_le_sum fun a _ => by nlinarith [sq_nonneg (h a - h (a + d))]
  rw [autocorrelation]
  refine this.trans (le_of_eq ?_)
  rw [← Finset.sum_div, Finset.sum_add_distrib, hshift]
  ring

/-- `∑_d R h d = (∑_a h a) ^ 2`. -/
theorem sum_autocorrelation (h : A → ℝ) : ∑ d, autocorrelation h d = (∑ a, h a) ^ 2 := by
  unfold autocorrelation
  rw [Finset.sum_comm, sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.addLeft a) _ _ fun d => rfl

end Autocorrelation

section Fibres

variable {ι A V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A] [Fintype A]
  [DecidableEq A] [AddCommGroup V] [DecidableEq V]

/-- Weights `0 ≤ h ≤ 1` with `ℓ¹` mass at most `S₁` and `ℓ²` mass at most `S₂` at every
coordinate. -/
structure WeightBounds (h : ι → A → ℝ) (S₁ S₂ : ℝ) : Prop where
  nonneg : ∀ i a, 0 ≤ h i a
  le_one : ∀ i a, h i a ≤ 1
  sum_le : ∀ i, ∑ a, h i a ≤ S₁
  sum_sq_le : ∀ i, ∑ a, h i a ^ 2 ≤ S₂

omit [Fintype ι] [DecidableEq ι] [DecidableEq A] [AddCommGroup A] in
/-- A power of `S₁` indexed by coordinates is nonnegative (it is `1` when there are none). -/
theorem WeightBounds.pow_card_nonneg_left {h : ι → A → ℝ} {S₁ S₂ : ℝ} (hh : WeightBounds h S₁ S₂)
    (K : Finset ι) : 0 ≤ S₁ ^ #K := by
  rcases K.eq_empty_or_nonempty with he | ⟨i, -⟩
  · rw [he, Finset.card_empty, pow_zero]
    exact zero_le_one
  · exact pow_nonneg ((Finset.sum_nonneg fun a _ => hh.nonneg i a).trans (hh.sum_le i)) _

omit [Fintype ι] [DecidableEq ι] [DecidableEq A] [AddCommGroup A] in
/-- A power of `S₂` indexed by coordinates is nonnegative. -/
theorem WeightBounds.pow_card_nonneg_right {h : ι → A → ℝ} {S₁ S₂ : ℝ}
    (hh : WeightBounds h S₁ S₂) (K : Finset ι) : 0 ≤ S₂ ^ #K := by
  rcases K.eq_empty_or_nonempty with he | ⟨i, -⟩
  · rw [he, Finset.card_empty, pow_zero]
    exact zero_le_one
  · exact pow_nonneg ((Finset.sum_nonneg fun a _ => sq_nonneg (h i a)).trans (hh.sum_sq_le i)) _

/-- A fibred code: parameters `P` and a fibre group `Q` (closed under `+` and `-`) whose sums
`p + q` are distinct and lie in `U`, with an information set `J` of `ω U` and an information set
`J₁ ⊆ J` of `ω Q`. -/
structure IsFibredCode (ω : V →+ (ι → A)) (P Q U : Finset V) (J J₁ : Finset ι) : Prop where
  add_mem : ∀ a ∈ Q, ∀ b ∈ Q, a + b ∈ Q
  sub_mem : ∀ a ∈ Q, ∀ b ∈ Q, a - b ∈ Q
  add_mem_total : ∀ p ∈ P, ∀ q ∈ Q, p + q ∈ U
  add_injOn : Set.InjOn (fun x : V × V => x.1 + x.2) (P ×ˢ Q : Finset (V × V))
  total : IsInformationSet (U.image ω) J
  fibre : IsInformationSet (Q.image ω) J₁
  subset : J₁ ⊆ J

/-- The fibre sum `∑_{q ∈ Q} ∏_i h i (ω (v + q) i)` over the translate `v + Q`. -/
def fibreSum (ω : V →+ (ι → A)) (Q : Finset V) (h : ι → A → ℝ) (v : V) : ℝ :=
  ∑ q ∈ Q, ∏ i, h i (ω (v + q) i)

omit [DecidableEq ι] [Fintype A] [DecidableEq A] [DecidableEq V] in
theorem fibreSum_nonneg (ω : V →+ (ι → A)) (Q : Finset V) {h : ι → A → ℝ}
    (h0 : ∀ i a, 0 ≤ h i a) (v : V) : 0 ≤ fibreSum ω Q h v :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun i _ => h0 i _

/-- **Squared fibre sums** (H2, H3): over a fibred code,
`∑_{p ∈ P} (∑_{q ∈ Q} ∏_i h i (ω (p + q) i))² ≤ S₂ ^ (#J - #J₁) · S₁ ^ (2 #J₁)`. -/
theorem sum_sq_fibreSum_le {ω : V →+ (ι → A)} (hω : Function.Injective ω) {P Q U : Finset V}
    {J J₁ : Finset ι} (hC : IsFibredCode ω P Q U J J₁) {h : ι → A → ℝ} {S₁ S₂ : ℝ}
    (hh : WeightBounds h S₁ S₂) :
    ∑ p ∈ P, fibreSum ω Q h p ^ 2 ≤ S₂ ^ (#J - #J₁) * S₁ ^ (2 * #J₁) := by
  set H : V → ℝ := fun v => ∏ i, h i (ω v i)
  set R : ι → A → ℝ := fun i => autocorrelation (h i)
  have hH0 : ∀ v, 0 ≤ H v := fun v => Finset.prod_nonneg fun i _ => hh.nonneg i _
  have hR0 : ∀ i d, 0 ≤ R i d := fun i d => autocorrelation_nonneg (hh.nonneg i) d
  -- the second point of a fibre as a shift of the first
  have hshift : ∀ v, ∀ q ∈ Q, ∑ q' ∈ Q, H (v + q') = ∑ e ∈ Q, H (v + q + e) := by
    intro v q hq
    refine Finset.sum_nbij' (fun q' => q' - q) (fun e => q + e)
      (fun q' hq' => hC.sub_mem q' hq' q hq) (fun e he => hC.add_mem q hq e he)
      (fun q' _ => by abel) (fun e _ => by abel) (fun q' _ => ?_)
    congr 1
    abel
  -- one shift `e`: the window `J` factors the sum over `U`
  have hwin : ∀ e, ∑ u ∈ U, H u * H (u + e) ≤ ∏ i ∈ J, R i (ω e i) := by
    intro e
    set ψ : ι → A → ℝ := fun i a => h i a * h i (a + ω e i)
    have hψ0 : ∀ i a, 0 ≤ ψ i a := fun i a => mul_nonneg (hh.nonneg i a) (hh.nonneg i _)
    have hψ1 : ∀ i a, ψ i a ≤ 1 := fun i a =>
      (mul_le_mul (hh.le_one i a) (hh.le_one i _) (hh.nonneg i _) zero_le_one).trans_eq (one_mul 1)
    calc ∑ u ∈ U, H u * H (u + e) = ∑ w ∈ U.image ω, ∏ i, ψ i (w i) := by
          rw [Finset.sum_image fun x _ y _ hxy => hω hxy]
          refine Finset.sum_congr rfl fun u _ => ?_
          simp only [H, ψ, map_add, Pi.add_apply, ← Finset.prod_mul_distrib]
      _ ≤ ∏ i ∈ J, ∑ a, ψ i a := sum_prod_le_window hC.total hψ0 hψ1
      _ = ∏ i ∈ J, R i (ω e i) := rfl
  -- the factors off `J₁` are at most `S₂`
  have hsplit : ∀ e, ∏ i ∈ J, R i (ω e i) ≤ S₂ ^ (#J - #J₁) * ∏ i ∈ J₁, R i (ω e i) := by
    intro e
    rw [← Finset.prod_sdiff hC.subset, ← Finset.card_sdiff_of_subset hC.subset]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => hR0 i _)
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ => hR0 i _) fun i _ =>
      (autocorrelation_le_sum_sq (h i) _).trans (hh.sum_sq_le i)
  have hpow : 0 ≤ S₂ ^ (#J - #J₁) := by
    rw [← Finset.card_sdiff_of_subset hC.subset]
    exact hh.pow_card_nonneg_right _
  calc ∑ p ∈ P, fibreSum ω Q h p ^ 2
      = ∑ e ∈ Q, ∑ x ∈ P ×ˢ Q, H (x.1 + x.2) * H (x.1 + x.2 + e) := by
        rw [Finset.sum_comm, Finset.sum_product]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [fibreSum, sq, Finset.sum_mul, Finset.sum_comm]
        rw [← Finset.sum_comm]
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [← Finset.mul_sum]
        exact congrArg (H (p + q) * ·) (hshift p q hq)
    _ ≤ ∑ e ∈ Q, ∑ u ∈ U, H u * H (u + e) := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [← Finset.sum_image (f := fun u => H u * H (u + e)) hC.add_injOn]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u _ _ =>
          mul_nonneg (hH0 u) (hH0 _)
        intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hp, hq⟩ := Finset.mem_product.mp hx
        exact hC.add_mem_total _ hp _ hq
    _ ≤ ∑ e ∈ Q, S₂ ^ (#J - #J₁) * ∏ i ∈ J₁, R i (ω e i) :=
        Finset.sum_le_sum fun e _ => (hwin e).trans (hsplit e)
    _ = S₂ ^ (#J - #J₁) * ∏ i ∈ J₁, (∑ a, h i a) ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_image (f := fun w : ι → A => ∏ i ∈ J₁, R i (w i))
          fun x _ y _ hxy => hω hxy, sum_prod_window_eq hC.fibre R]
        exact Finset.prod_congr rfl fun i _ => sum_autocorrelation (h i)
    _ ≤ S₂ ^ (#J - #J₁) * S₁ ^ (2 * #J₁) := by
        refine mul_le_mul_of_nonneg_left ?_ hpow
        rw [pow_mul, ← Finset.prod_const]
        exact Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) fun i _ =>
          pow_le_pow_left₀ (Finset.sum_nonneg fun a _ => hh.nonneg i a) (hh.sum_le i) 2

/-- **Hybrid row bound** (H1 with H2, H3 on both factors): for an injective self-map `Φ` of `P`
and fibred codes `P ⊕ Q`, `P ⊕ Q'` whose windows exceed their fibre windows by `d` coordinates,
`∑_{p ∈ P} (∑_{q ∈ Q} H (p + q)) (∑_{q ∈ Q'} H' (Φ p + q)) ≤ S₂ ^ d · S₁ ^ (#J₁ + #J₁')`. -/
theorem sum_fibreSum_mul_fibreSum_le {ω : V →+ (ι → A)} (hω : Function.Injective ω)
    {P Q U Q' U' : Finset V} {J J₁ J' J₁' : Finset ι} (hC : IsFibredCode ω P Q U J J₁)
    (hC' : IsFibredCode ω P Q' U' J' J₁') {d : ℕ} (hd : #J - #J₁ = d) (hd' : #J' - #J₁' = d)
    {Φ : V → V} (hΦ : ∀ p ∈ P, Φ p ∈ P) (hΦinj : Set.InjOn Φ P) {h h' : ι → A → ℝ} {S₁ S₂ : ℝ}
    (hh : WeightBounds h S₁ S₂) (hh' : WeightBounds h' S₁ S₂) :
    ∑ p ∈ P, fibreSum ω Q h p * fibreSum ω Q' h' (Φ p) ≤ S₂ ^ d * S₁ ^ (#J₁ + #J₁') := by
  have h1 := sum_sq_fibreSum_le hω hC hh
  have h2 := sum_sq_fibreSum_le hω hC' hh'
  rw [hd] at h1
  rw [hd'] at h2
  have hΦsum : ∑ p ∈ P, fibreSum ω Q' h' (Φ p) ^ 2 ≤ ∑ p ∈ P, fibreSum ω Q' h' p ^ 2 := by
    rw [← Finset.sum_image (f := fun v => fibreSum ω Q' h' v ^ 2) hΦinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun v _ _ => sq_nonneg _
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact hΦ p hp
  have hS : 0 ≤ S₂ ^ d * S₁ ^ (2 * #J₁) :=
    (Finset.sum_nonneg fun p _ => sq_nonneg _).trans h1
  have hS' : 0 ≤ S₂ ^ d * S₁ ^ (2 * #J₁') :=
    (Finset.sum_nonneg fun p _ => sq_nonneg _).trans h2
  calc ∑ p ∈ P, fibreSum ω Q h p * fibreSum ω Q' h' (Φ p)
      ≤ √(∑ p ∈ P, fibreSum ω Q h p ^ 2) * √(∑ p ∈ P, fibreSum ω Q' h' (Φ p) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √(S₂ ^ d * S₁ ^ (2 * #J₁)) * √(S₂ ^ d * S₁ ^ (2 * #J₁')) := by
        gcongr
        exact hΦsum.trans h2
    _ = √((S₂ ^ d * S₁ ^ (#J₁ + #J₁')) ^ 2) := by
        rw [← Real.sqrt_mul hS]
        congr 1
        ring
    _ ≤ S₂ ^ d * S₁ ^ (#J₁ + #J₁') := by
        rw [Real.sqrt_sq_eq_abs]
        refine le_of_eq (abs_of_nonneg ?_)
        rw [← hd, ← Finset.card_sdiff_of_subset hC.subset, pow_add]
        exact mul_nonneg (hh.pow_card_nonneg_right _)
          (mul_nonneg (hh.pow_card_nonneg_left _) (hh.pow_card_nonneg_left _))

end Fibres

end GordieHowe
