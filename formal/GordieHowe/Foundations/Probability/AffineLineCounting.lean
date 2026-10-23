-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Counting affine coefficient families

Translation along a fixed direction preserves the uniform count of coefficient
vectors. A dense good set therefore has a line with many good points. If a
line theorem makes that direction good, every generated direction is good.
Scalar invariance extends the same argument to the span containing the offset.
These statements do not require independent generators or an injective map.
-/

namespace GordieHowe.AffineLineCounting

open scoped Classical

variable {F V W : Type} [Field F] [Fintype F]
  [AddCommGroup V] [Module F V] [Fintype V]
  [AddCommGroup W] [Module F W]

abbrev goodFiber (P : V → Prop) (v : V) (a : V) : Type :=
  {z : F // P (a + z • v)}

abbrev goodLines (P : V → Prop) (v : V) : Type :=
  {p : V × F // P (p.1 + p.2 • v)}

noncomputable abbrev goodPoints (P : V → Prop) : Finset V :=
  Finset.univ.filter P

omit [Fintype V] in
theorem card_goodFiber (P : V → Prop) (v a : V) :
    Fintype.card (goodFiber (F := F) P v a) =
      (Finset.univ.filter fun z : F => P (a + z • v)).card := by
  let s : Finset F := Finset.univ.filter fun z : F => P (a + z • v)
  let e : goodFiber (F := F) P v a ≃ s :=
    { toFun := fun z => ⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩⟩
      invFun := fun z => ⟨z.1, (Finset.mem_filter.mp z.2).2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  calc
    Fintype.card (goodFiber (F := F) P v a) = Fintype.card s := Fintype.card_congr e
    _ = s.card := Fintype.card_coe s
    _ = _ := rfl

theorem card_pred_subtype {α : Type} [Fintype α] (Q : α → Prop) :
    Fintype.card {x // Q x} = (Finset.univ.filter Q).card := by
  let s : Finset α := Finset.univ.filter Q
  let e : {x // Q x} ≃ s :=
    { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
      invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  calc
    Fintype.card {x // Q x} = Fintype.card s := Fintype.card_congr e
    _ = s.card := Fintype.card_coe s
    _ = _ := rfl

theorem card_goodLines (P : V → Prop) (v : V) :
    Fintype.card (goodLines (F := F) P v) =
      (goodPoints P).card * Fintype.card F := by
  let good : Type := {x // x ∈ goodPoints P}
  let e₁ : goodLines (F := F) P v ≃ {p : V × F // P p.1} :=
    { toFun := fun z => ⟨(z.1.1 + z.1.2 • v, z.1.2), z.2⟩
      invFun := fun z => ⟨(z.1.1 - z.1.2 • v, z.1.2), by
        simpa [sub_add_cancel] using z.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · exact add_sub_cancel_right _ _
        · rfl
      right_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · exact sub_add_cancel _ _
        · rfl }
  let e₂ : {p : V × F // P p.1} ≃ good × F :=
    { toFun := fun z =>
        ⟨⟨z.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩⟩, z.1.2⟩
      invFun := fun z =>
        ⟨(z.1.1, z.2), (Finset.mem_filter.mp z.1.2).2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  calc
    Fintype.card (goodLines (F := F) P v) = Fintype.card {p : V × F // P p.1} :=
      Fintype.card_congr e₁
    _ = Fintype.card (good × F) := Fintype.card_congr e₂
    _ = Fintype.card good * Fintype.card F := Fintype.card_prod _ _
    _ = (goodPoints P).card * Fintype.card F := by
      rw [Fintype.card_coe]

theorem card_goodLines_sigma (P : V → Prop) (v : V) :
    Fintype.card (Σ a : V, goodFiber (F := F) P v a) =
      Fintype.card (goodLines (F := F) P v) := by
  let e : (Σ a : V, goodFiber (F := F) P v a) ≃ goodLines (F := F) P v :=
    { toFun := fun z => ⟨(z.1, z.2.1), z.2.2⟩
      invFun := fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  exact Fintype.card_congr e

-- Key finite averaging fact; no nonzero requirement on direction.
theorem exists_dense_line (P : V → Prop) (v : V) (n : ℕ)
    (h : n * Fintype.card V <
      (Finset.univ.filter P).card * Fintype.card F) :
    ∃ a : V, n < (Finset.univ.filter fun z : F => P (a + z • v)).card := by
  classical
  by_contra hline
  push Not at hline
  have hfiber : ∀ a : V,
      Fintype.card (goodFiber (F := F) P v a) ≤ n := by
    intro a
    rw [card_goodFiber]
    exact hline a
  have hsum : Fintype.card (goodLines (F := F) P v) ≤ Fintype.card V * n := by
    rw [← card_goodLines_sigma (F := F) P v]
    rw [Fintype.card_sigma]
    calc
      (∑ a : V, Fintype.card (goodFiber (F := F) P v a)) ≤ ∑ _a : V, n :=
        Finset.sum_le_sum (fun a _ => hfiber a)
      _ = Fintype.card V * n := by simp
  have hsum' : (goodPoints P).card * Fintype.card F ≤ Fintype.card V * n := by
    calc
      (goodPoints P).card * Fintype.card F = Fintype.card (goodLines (F := F) P v) :=
        (card_goodLines (F := F) P v).symm
      _ ≤ Fintype.card V * n := hsum
  have hle : (Finset.univ.filter P).card * Fintype.card F ≤
      n * Fintype.card V := by
    simpa [goodPoints, Nat.mul_comm] using hsum'
  exact (Nat.not_lt_of_ge hle) h

-- If a translated affine line has more than n good points, its direction is good.
theorem directions_near (P : W → Prop) (n : ℕ)
    (hline : ∀ u v : W,
      n < (Finset.univ.filter fun z : F => P (u + z • v)).card → P v)
    (L : V →ₗ[F] W) (u : W)
    (h : n * Fintype.card V <
      (Finset.univ.filter fun r : V => P (u + L r)).card * Fintype.card F) :
    ∀ v, P (L v) := by
  intro v
  obtain ⟨a, ha⟩ := exists_dense_line
    (P := fun r : V => P (u + L r)) (v := v) n h
  apply hline (u + L a) (L v)
  simpa only [map_add, map_smul, add_assoc] using ha

-- Homogeneous affine-line conclusion. The same counting argument is applied to
-- every nonzero scalar slice, using the scaling invariance of P.
theorem homogeneous_near (P : W → Prop) (n : ℕ)
    (hline : ∀ u v : W,
      n < (Finset.univ.filter fun z : F => P (u + z • v)).card → P v)
    (hscale : ∀ (s : F), s ≠ 0 → ∀ w, P (s • w) ↔ P w)
    (L : V →ₗ[F] W) (u : W)
    (h : n * Fintype.card V <
      (Finset.univ.filter fun r : V => P (u + L r)).card * Fintype.card F) :
    ∀ (s : F) (r : V), P (s • u + L r) := by
  classical
  have hdir : ∀ r : V, P (L r) := directions_near P n hline L u h
  let H : (F × V) →ₗ[F] W :=
    { toFun := fun p => p.1 • u + L p.2
      map_add' := by
        intro x y
        simp [add_smul, map_add, add_assoc, add_comm, add_left_comm]
      map_smul' := by
        intro c x
        simp [smul_add, smul_smul, map_smul] }
  let A : Type := {r : V // P (u + L r)}
  let B : Type := {p : F × V // P (H p)}
  let f : F × A → B := fun x =>
    ⟨(x.1, if x.1 = 0 then x.2.1 else x.1 • x.2.1), by
      by_cases hs : x.1 = 0
      · simp [H, hs, hdir]
      · have hx := (hscale x.1 hs (u + L x.2.1)).mpr x.2.2
        simpa [H, hs, map_smul, smul_add] using hx⟩
  have hf : Function.Injective f := by
    rintro ⟨s, a⟩ ⟨t, b⟩ hxy
    have hxy' : (f (s, a)).1 = (f (t, b)).1 :=
      congrArg (fun z : B => z.1) hxy
    have hs : s = t := congrArg (fun z : F × V => z.1) hxy'
    subst t
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      have hz' := congrArg (fun z : F × V => z.2) hxy'
      by_cases hz : s = 0
      · simpa [f, hz] using hz'
      · simp [f, hz] at hz'
        apply congrArg (fun z : V => s⁻¹ • z) at hz'
        simpa only [inv_smul_smul₀ hz] using hz'
  have hcard : Fintype.card (F × A) ≤ Fintype.card B :=
    Fintype.card_le_of_injective f hf
  have hcard' :
      (Finset.univ.filter fun r : V => P (u + L r)).card * Fintype.card F ≤
        Fintype.card B := by
    have := hcard
    rw [Fintype.card_prod, card_pred_subtype] at this
    simpa [Nat.mul_comm] using this
  have hhom : n * Fintype.card (F × V) <
      (Finset.univ.filter fun p : F × V => P (H p)).card * Fintype.card F := by
    have hmul := Nat.mul_lt_mul_of_pos_right h (Fintype.card_pos : 0 < Fintype.card F)
    have hmul' := Nat.mul_le_mul_right (Fintype.card F) hcard'
    have hlt : n * Fintype.card (F × V) <
        Fintype.card B * Fintype.card F := by
      calc
        n * Fintype.card (F × V) =
            (n * Fintype.card V) * Fintype.card F := by
              simp [Fintype.card_prod, Nat.mul_left_comm, Nat.mul_comm]
        _ < (Finset.univ.filter fun r : V => P (u + L r)).card *
              Fintype.card F * Fintype.card F := by simpa [Nat.mul_assoc] using hmul
        _ ≤ Fintype.card B * Fintype.card F := hmul'
    calc
      n * Fintype.card (F × V) < Fintype.card B * Fintype.card F := hlt
      _ = (Finset.univ.filter fun p : F × V => P (H p)).card * Fintype.card F := by
        rw [card_pred_subtype]
  have hall : ∀ p : F × V, P (H p) :=
    directions_near P n hline H 0 (by simpa [zero_add] using hhom)
  intro s r
  simpa [H] using hall (s, r)

-- Every affine point is good under the same hypotheses.
theorem affine_near (P : W → Prop) (n : ℕ)
    (hline : ∀ u v : W,
      n < (Finset.univ.filter fun z : F => P (u + z • v)).card → P v)
    (hscale : ∀ (s : F), s ≠ 0 → ∀ w, P (s • w) ↔ P w)
    (L : V →ₗ[F] W) (u : W)
    (h : n * Fintype.card V <
      (Finset.univ.filter fun r : V => P (u + L r)).card * Fintype.card F) :
    ∀ r, P (u + L r) := by
  simpa using homogeneous_near P n hline hscale L u h 1

end GordieHowe.AffineLineCounting
