-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-!
# Boxes meeting affine subspaces

A product set (a "box") `∏_i S i ⊆ ι → F` with every side `#(S i) ≤ G` meets each translate
`w + U` of a subspace `U` in at most `G ^ dim U` points (`card_filter_sub_mem_le_pow_finrank`).
The proof picks `dim U` coordinates on which `U` projects injectively
(`exists_finset_card_le_finrank_injOn`) and observes that a point of the box in `w + U` is
determined by those coordinates. This is the rank bound of the HighBits regularity argument ("A
shorter proof of the stated HighBits regularity claim", 10 September 2026, Section 3: "a rank-`R`
system has at most `G^(d - R)` solutions in a translated `d`-dimensional `G`-box").

`finrank_pi_univ`: the subspace `{y | ∀ j, y j ∈ L j}` of a finite product has dimension
`∑_j dim L j`, which computes `dim U` for constraints imposed coordinate by coordinate.
-/

open Finset
open scoped BigOperators

namespace Submodule

variable {ι F : Type*} [Fintype ι] [Field F]

/-- A subspace `U ⊆ ι → F` projects injectively onto at most `dim U` coordinates: some `P` with
`#P ≤ dim U` has `u ∈ U ∧ (∀ p ∈ P, u p = 0) → u = 0`. The coordinate functionals restricted to `U`
span its dual; a linearly independent subfamily spanning the same space has at most `dim U`
members, and the coordinates it indexes already separate `U`. -/
theorem exists_finset_card_le_finrank_injOn (U : Submodule F (ι → F)) :
    ∃ P : Finset ι, #P ≤ Module.finrank F U ∧
      ∀ u ∈ U, (∀ p ∈ P, u p = 0) → u = 0 := by
  classical
  let v : ι → Module.Dual F U := fun i => (LinearMap.proj i).comp U.subtype
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ha, Finset.card_univ,
      ← Subspace.dual_finrank_eq (K := F) (V := U)]
    exact hli.fintype_card_le_finrank
  · intro u hu hP
    have hker : ∀ φ ∈ Submodule.span F (Set.range (v ∘ a)), φ ⟨u, hu⟩ = 0 := by
      intro φ hφ
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
      · rintro _ ⟨k, rfl⟩
        exact hP (a k) (Finset.mem_image_of_mem a (Finset.mem_univ k))
      · rfl
      · intro x y _ _ hx hy
        rw [LinearMap.add_apply, hx, hy, add_zero]
      · intro c x _ hx
        rw [LinearMap.smul_apply, hx, smul_zero]
    funext i
    exact hker (v i) (hsp ▸ Submodule.subset_span ⟨i, rfl⟩)

/-- A box `∏_i S i` with sides `#(S i) ≤ G` (`1 ≤ G`) meets the translate `w + U` of a subspace in
at most `G ^ dim U` points. -/
theorem card_filter_sub_mem_le_pow_finrank [DecidableEq ι] [DecidableEq F]
    (U : Submodule F (ι → F)) [DecidablePred (· ∈ U)] (S : ι → Finset F) {G : ℕ} (hG : 1 ≤ G)
    (hS : ∀ i, #(S i) ≤ G) (w : ι → F) :
    #((Fintype.piFinset S).filter (fun x => x - w ∈ U)) ≤ G ^ Module.finrank F U := by
  obtain ⟨P, hP, hinj⟩ := U.exists_finset_card_le_finrank_injOn
  set Fib := (Fintype.piFinset S).filter (fun x => x - w ∈ U)
  have hmaps : ∀ x ∈ Fib, (fun p : P => x p) ∈ Fintype.piFinset (fun p : P => S p) := by
    intro x hx
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hx
    rw [Fintype.mem_piFinset]
    exact fun p => hx.1 p
  have hinjOn : Set.InjOn (fun x : ι → F => fun p : P => x p) Fib := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hd : x - y ∈ U := by
      have := U.sub_mem hx' hy'
      rwa [sub_sub_sub_cancel_right] at this
    have h0 := hinj (x - y) hd fun p hp => by
      have := congrFun hxy ⟨p, hp⟩
      simp only at this
      rw [Pi.sub_apply, this, sub_self]
    exact sub_eq_zero.mp h0
  calc #Fib ≤ #(Fintype.piFinset fun p : P => S p) :=
        Finset.card_le_card_of_injOn _ hmaps hinjOn
    _ = ∏ p : P, #(S p) := Fintype.card_piFinset _
    _ ≤ G ^ #(Finset.univ : Finset P) := Finset.prod_le_pow_card _ _ _ fun p _ => hS p
    _ = G ^ #P := by rw [Finset.card_univ, Fintype.card_coe]
    _ ≤ G ^ Module.finrank F U := Nat.pow_le_pow_right hG hP

end Submodule

namespace Submodule

variable {J F : Type*} [Fintype J] [Field F] {V : J → Type*} [∀ j, AddCommGroup (V j)]
  [∀ j, Module F (V j)] [∀ j, Module.Finite F (V j)]

/-- The subspace `{y | ∀ j, y j ∈ L j}` of a finite product has dimension `∑_j dim L j`. -/
theorem finrank_pi_univ (L : ∀ j, Submodule F (V j)) :
    Module.finrank F (Submodule.pi Set.univ L) = ∑ j, Module.finrank F (L j) := by
  let e : Submodule.pi Set.univ L ≃ₗ[F] ∀ j, L j :=
    { toFun := fun y j => ⟨y.1 j, y.2 j (Set.mem_univ j)⟩
      invFun := fun z => ⟨fun j => z j, fun j _ => (z j).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

end Submodule

namespace Submodule

/-- **Separation by a dot product**: if `v ∉ span {s}` in `F^ℓ`, some `u` has `u · s = 0` and
`u · v ≠ 0`. -/
theorem exists_dotProduct_separating {F ℓ : Type*} [Field F] [Fintype ℓ] [DecidableEq ℓ]
    {s v : ℓ → F} (hv : v ∉ Submodule.span F {s}) :
    ∃ u : ℓ → F, (∑ b, u b * s b) = 0 ∧ (∑ b, u b * v b) ≠ 0 := by
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hsingle : ∀ i : ℓ, (fun j => if i = j then (1 : F) else 0) = Pi.single i 1 := fun i => by
    funext j
    simp [Pi.single_apply, eq_comm]
  have happ : ∀ w : ℓ → F, f w = ∑ b, f (Pi.single b 1) * w b := fun w => by
    rw [LinearMap.pi_apply_eq_sum_univ f w]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsingle, smul_eq_mul, mul_comm]
  refine ⟨fun b => f (Pi.single b 1), ?_, ?_⟩
  · have hs : f s = 0 := by
      have : f s ∈ (Submodule.span F {s}).map f :=
        Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self s)
      rw [hmap] at this
      exact (Submodule.mem_bot F).mp this
    rw [← happ, hs]
  · rw [← happ]
    exact hf

end Submodule
