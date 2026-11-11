-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.UniformFunction
public import GordieHowe.Foundations.ToMathlib.PMFUniform
public import GordieHowe.Foundations.ToMathlib.PMFCoupling

public section

/-!
# Pullbacks and coordinates of uniform and product laws

* `map_uniformOfFintype_comp_embedding`: the pullback of a uniform function along an embedding is
  uniform (`splitAlong`).
* `pi_map_eval`: a coordinate of a product law has the coordinate's law.
* `map_prodMap_uniformOfFintype`: a product of maps that push uniform laws to uniform laws.
* `uniformOfFintype_bind_map_eq`: a uniform law followed by a map of a second uniform coordinate
  is a map of the uniform law on pairs.

About Mathlib objects only.
-/

open Finset
open scoped ENNReal BigOperators

namespace PMF

section Uniform

variable {A A' Y : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype Y]
  [Nonempty Y]

/-- **The pullback of a uniform function along an embedding is uniform** (`splitAlong`). -/
theorem map_uniformOfFintype_comp_embedding (e : A' ↪ A) :
    (uniformOfFintype (A → Y)).map (fun g a => g (e a)) = uniformOfFintype (A' → Y) := by
  rw [← map_uniformOfFintype_equiv (GordieHowe.splitAlong (Y' := Y) e).symm, map_comp]
  have h : ((fun g a => g (e a)) ∘ (GordieHowe.splitAlong (Y' := Y) e).symm) = Prod.snd := by
    funext q a
    exact GordieHowe.splitAlong_symm_apply_embed e q.1 q.2 a
  rw [h, map_snd_uniformOfFintype]

end Uniform

/-- **A coordinate of a product law has the coordinate's law.** -/
theorem pi_map_eval {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {δ : ι' → Type*}
    [∀ i, Fintype (δ i)] [∀ i, DecidableEq (δ i)] (ν : ∀ i, PMF (δ i)) (j : ι') :
    (pi ν).map (fun T => T j) = ν j := by
  ext x
  simp only [map_apply, tsum_fintype]
  have := sum_pi_mul_apply_coord ν j fun b => if x = b then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
  rw [← this]
  exact Finset.sum_congr rfl fun T _ => by split_ifs <;> simp

/-- **A product of maps that push uniform laws to uniform laws** pushes the uniform law on pairs
to the uniform law on pairs. -/
theorem map_prodMap_uniformOfFintype {α β γ δ : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] [Fintype γ] [Nonempty γ] [Fintype δ] [Nonempty δ] {g : α → γ} {h : β → δ}
    (hg : (uniformOfFintype α).map g = uniformOfFintype γ)
    (hh : (uniformOfFintype β).map h = uniformOfFintype δ) :
    (uniformOfFintype (α × β)).map (Prod.map g h) = uniformOfFintype (γ × δ) := by
  rw [uniformOfFintype_prod_eq_bind, map_bind, uniformOfFintype_prod_eq_bind, ← hg, bind_map]
  congr 1
  funext a
  rw [Function.comp_apply, ← hh, PMF.map_comp, PMF.map_comp]
  rfl

/-- A uniform law followed by a map of a second uniform coordinate is the uniform law on pairs. -/
theorem uniformOfFintype_bind_map_eq {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] (f : α → β → γ) :
    (uniformOfFintype α).bind (fun a => (uniformOfFintype β).map (f a)) =
      (uniformOfFintype (α × β)).map fun q => f q.1 q.2 := by
  rw [uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp]
  rfl

end PMF
