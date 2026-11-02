-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# Boxes meeting the common zero set of linear forms, by Fourier inversion

For a finite field `F`, a nontrivial additive character `ψ : F → ℂ` and a subspace `Λ` of linear
forms on `ι → F` (written as coefficient vectors `a`, `a · x = ∑_i a i * x i`):

- `AddChar.sum_mem_submodule_eq`: orthogonality on `Λ`, `∑_{a ∈ Λ} ψ (a · x) = #Λ` when every form
  of `Λ` vanishes at `x` and `0` otherwise;
- `AddChar.card_filter_forall_dot_eq_zero_le`: a box `∏_i S i` meets the translate `w + Λ^⊥` in at
  most `#B / #Λ · ∑_{a ∈ Λ} ∏_i f (a i)` points, whenever every side satisfies
  `‖∑_{x ∈ S i} ψ (a x)‖ ≤ #(S i) · f a`.

With `f ≡ 1` this is the trivial bound `#B`; with the interval bound `f a = min 1 (q / (2 #S |a|))`
of an interval side (`ZMod.norm_sum_stdAddChar_le`) it recovers the count `#B / #Λ · (1 + small)`
of a box meeting an affine subspace of codimension `dim Λ` when the forms of `Λ` have large
coefficients. This sharpens the rank bound `Submodule.card_filter_sub_mem_le_pow_finrank`
(`BoxSubspace.lean`), which pays `G` instead of `q` per condition.
-/

open Finset
open scoped BigOperators

namespace AddChar

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]

omit [Fintype ι] in
/-- A character turns a finite sum into a product. -/
theorem map_sum_eq_prod {A M : Type*} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M)
    (s : Finset ι) (g : ι → A) : ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, map_add_eq_mul, ih]

/-- **Orthogonality on a subspace of forms**: for a nontrivial additive character `ψ`,
`∑_{a ∈ Λ} ψ (a · x)` is `#Λ` if every form of `Λ` vanishes at `x`, and `0` otherwise. -/
theorem sum_mem_submodule_eq (ψ : AddChar F ℂ) (hψ : ψ ≠ 0) (Λ : Submodule F (ι → F))
    [DecidablePred (· ∈ Λ)] (x : ι → F) :
    ∑ a ∈ univ.filter (· ∈ Λ), ψ (∑ i, a i * x i) =
      if ∀ a ∈ Λ, ∑ i, a i * x i = 0 then (#(univ.filter (· ∈ Λ)) : ℂ) else 0 := by
  split_ifs with h
  · rw [Finset.sum_congr rfl fun a ha => by
      rw [h a (Finset.mem_filter.mp ha).2, AddChar.map_zero_eq_one]]
    simp
  · push Not at h
    obtain ⟨a₀, ha₀, hne⟩ := h
    obtain ⟨b, hb⟩ := (AddChar.ne_zero_iff).mp hψ
    set a₁ : ι → F := (b / ∑ i, a₀ i * x i) • a₀
    have ha₁ : a₁ ∈ Λ := Λ.smul_mem _ ha₀
    have hval : ∑ i, a₁ i * x i = b := by
      simp only [a₁, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      exact div_mul_cancel₀ b hne
    set S := ∑ a ∈ univ.filter (· ∈ Λ), ψ (∑ i, a i * x i)
    have hshift : S = ∑ a ∈ univ.filter (· ∈ Λ), ψ (∑ i, (a + a₁) i * x i) := by
      refine (Finset.sum_equiv (Equiv.addRight a₁) (fun a => ?_) (fun a _ => rfl)).symm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight]
      exact (Λ.add_mem_iff_left ha₁).symm
    have hmul : S = ψ b * S := by
      conv_lhs => rw [hshift]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show ∑ i, (a + a₁) i * x i = ∑ i, a i * x i + b by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hval],
        AddChar.map_add_eq_mul, mul_comm]
    have h0 : (1 - ψ b) * S = 0 := by
      rw [sub_mul, one_mul, ← hmul, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1).symm hb
    · exact h1

/-- **A box meets `w + Λ^⊥` in at most `#B / #Λ · ∑_{a ∈ Λ} ∏_i f (a i)` points**, when every
side has `‖∑_{x ∈ S i} ψ (a x)‖ ≤ #(S i) · f a` for a nontrivial additive character `ψ`. Fourier
inversion of the indicator of `w + Λ^⊥` (`sum_mem_submodule_eq`) factors over the coordinates of
the box. -/
theorem card_filter_forall_dot_eq_zero_le (ψ : AddChar F ℂ) (hψ : ψ ≠ 0)
    (Λ : Submodule F (ι → F)) [DecidablePred (· ∈ Λ)] (S : ι → Finset F) {f : F → ℝ}
    (hf : ∀ i a, ‖∑ x ∈ S i, ψ (a * x)‖ ≤ #(S i) * f a) (w : ι → F) :
    (#((Fintype.piFinset S).filter fun z => ∀ a ∈ Λ, ∑ i, a i * (z i - w i) = 0) : ℝ) ≤
      #(Fintype.piFinset S) / #(univ.filter (· ∈ Λ)) *
        ∑ a ∈ univ.filter (· ∈ Λ), ∏ i, f (a i) := by
  set B := Fintype.piFinset S
  set Λs := univ.filter (· ∈ Λ)
  have hN : (0 : ℝ) < #Λs := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Λ.zero_mem⟩⟩
  -- the count times `#Λ` is the double character sum
  have hcount : ((#(B.filter fun z => ∀ a ∈ Λ, ∑ i, a i * (z i - w i) = 0) : ℂ) * #Λs) =
      ∑ a ∈ Λs, ∏ i, ∑ x ∈ S i, ψ (a i * (x - w i)) := by
    have h1 : ∀ z : ι → F, ∑ a ∈ Λs, ψ (∑ i, a i * (z i - w i)) =
        if ∀ a ∈ Λ, ∑ i, a i * (z i - w i) = 0 then (#Λs : ℂ) else 0 :=
      fun z => sum_mem_submodule_eq ψ hψ Λ (fun i => z i - w i)
    calc ((#(B.filter fun z => ∀ a ∈ Λ, ∑ i, a i * (z i - w i) = 0) : ℂ) * #Λs)
        = ∑ z ∈ B, if ∀ a ∈ Λ, ∑ i, a i * (z i - w i) = 0 then (#Λs : ℂ) else 0 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ = ∑ z ∈ B, ∑ a ∈ Λs, ψ (∑ i, a i * (z i - w i)) :=
          Finset.sum_congr rfl fun z _ => (h1 z).symm
      _ = ∑ a ∈ Λs, ∑ z ∈ B, ∏ i, ψ (a i * (z i - w i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun z _ => ?_
          exact map_sum_eq_prod ψ _ _
      _ = ∑ a ∈ Λs, ∏ i, ∑ x ∈ S i, ψ (a i * (x - w i)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          exact (Finset.prod_univ_sum S fun i x => ψ (a i * (x - w i))).symm
  have hside : ∀ (a : ι → F) i, ‖∑ x ∈ S i, ψ (a i * (x - w i))‖ ≤ #(S i) * f (a i) := by
    intro a i
    have : ∑ x ∈ S i, ψ (a i * (x - w i)) = ψ (-(a i * w i)) * ∑ x ∈ S i, ψ (a i * x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← AddChar.map_add_eq_mul]
      ring_nf
    rw [this, norm_mul, AddChar.norm_apply, one_mul]
    exact hf i (a i)
  have hB : (#B : ℝ) = ∏ i, (#(S i) : ℝ) := by
    rw [Fintype.card_piFinset]
    push_cast
    rfl
  have hle : ((#(B.filter fun z => ∀ a ∈ Λ, ∑ i, a i * (z i - w i) = 0) : ℝ) * #Λs) ≤
      #B * ∑ a ∈ Λs, ∏ i, f (a i) := by
    have hn : ((#(B.filter fun z => ∀ a ∈ Λ, ∑ i, a i * (z i - w i) = 0) : ℝ) * #Λs) =
        ‖((#(B.filter fun z => ∀ a ∈ Λ, ∑ i, a i * (z i - w i) = 0) : ℂ) * #Λs)‖ := by
      rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [hn, hcount, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_prod, hB, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hside a i
  rw [div_mul_eq_mul_div, le_div_iff₀ hN]
  exact hle

end AddChar
