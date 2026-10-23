-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Counting bad challenges along lines and over repetitions

The challenge counts of a repeated algebraic test (AHIV22's `σ` repetitions, ePrint 2022/1608,
section 4.7) reduce to three facts.

* **Lines** (`card_mul_card_le_of_line`): a set of vectors meeting every line in a fixed
  direction at most once has at most `|V|/|F|` elements. The map `(x, α) ↦ x + α • s` is
  injective on `B × F`.
* **Affine conditions** (`card_filter_sum_mul_eq_mul_le`): a condition `Σ_i r_i a_i = y` with a
  nonzero coefficient vector `a` holds for at most a `1/|F|` fraction of `r`.
* **Repetitions** (`card_piFinset_mul_pow_le`, `card_biUnion_piFinset_mul_pow_le`): if each
  repetition's bad set has density at most `1/c`, the challenges bad in every repetition have
  density at most `1/c^σ`, and a union of `J` such events at most `#J/c^σ`.

`card_filter_exists_mul_le_of_subsingleton` counts an event `∃ y, Cand y ∧ Cond y x` whose
candidates `y` are fixed before the challenge and unique; `card_filter_fst_equiv` counts an event
that reads one component of a product of challenge spaces.
-/

namespace GordieHowe.RepetitionCounting

open Finset

section Line

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Fintype V]

/-- **Line counting.** If no two distinct points of `B` lie on a common line in direction `s`
(`x ∈ B`, `α ≠ 0` imply `x + α • s ∉ B`), then `#B · |F| ≤ |V|`. -/
theorem card_mul_card_le_of_line (B : Finset V) (s : V)
    (hB : ∀ x ∈ B, ∀ α : F, α ≠ 0 → x + α • s ∉ B) :
    #B * Fintype.card F ≤ Fintype.card V := by
  classical
  have hinj : Set.InjOn (fun p : V × F => p.1 + p.2 • s) ↑(B ×ˢ (univ : Finset F)) := by
    rintro ⟨x, α⟩ hx ⟨x', α'⟩ hx' h
    simp only [coe_product, Set.mem_prod, mem_coe, coe_univ, Set.mem_univ, and_true] at hx hx'
    simp only at h
    by_cases hα : α = α'
    · subst hα
      simpa using h
    · exfalso
      have hx'' : x' + (α' - α) • s = x := by
        rw [sub_smul, add_sub, ← h, add_sub_cancel_right]
      exact hB x' hx' (α' - α) (sub_ne_zero.mpr (Ne.symm hα)) (hx''.symm ▸ hx)
  calc #B * Fintype.card F = #(B ×ˢ (univ : Finset F)) := by rw [card_product, card_univ]
    _ = #((B ×ˢ (univ : Finset F)).image fun p : V × F => p.1 + p.2 • s) :=
        (card_image_of_injOn hinj).symm
    _ ≤ Fintype.card V := card_le_univ _

end Line

section Affine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Affine-condition count.** For a nonzero coefficient vector `a`, the condition
`Σ_i r_i a_i = y` holds for at most `|F|^{|ι|} / |F|` vectors `r`. -/
theorem card_filter_sum_mul_eq_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → F}
    (ha : a ≠ 0) (y : F) :
    #{r : ι → F | ∑ i, r i * a i = y} * Fintype.card F ≤ Fintype.card F ^ Fintype.card ι := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha
  rw [← Fintype.card_fun]
  refine card_mul_card_le_of_line _ (Pi.single i₀ (1 : F) : ι → F) fun x hx α hα hx' => ?_
  simp only [mem_filter, mem_univ, true_and] at hx hx'
  have hsum : ∑ i, (x + α • (Pi.single i₀ (1 : F) : ι → F)) i * a i =
      (∑ i, x i * a i) + α * a i₀ := by
    simp [add_mul, sum_add_distrib, Pi.single_apply]
  rw [hsum, hx, add_eq_left] at hx'
  exact mul_ne_zero hα hi₀ hx'

end Affine

section Repetition

variable {X : Type*} [Fintype X]

/-- The number of `σ`-tuples: `|Fin σ → X| = |X|^σ`. -/
theorem card_fin_fun {σ : ℕ} : Fintype.card (Fin σ → X) = Fintype.card X ^ σ := by
  rw [Fintype.card_fun, Fintype.card_fin]

/-- **Repetitions.** If each of `σ` bad sets satisfies `#(B h) · c ≤ |X|`, the challenge
tuples bad in every repetition satisfy `#(piFinset B) · c^σ ≤ |X|^σ`. -/
theorem card_piFinset_mul_pow_le {σ : ℕ} (B : Fin σ → Finset X) {c : ℕ}
    (hB : ∀ h, #(B h) * c ≤ Fintype.card X) :
    #(Fintype.piFinset B) * c ^ σ ≤ Fintype.card X ^ σ := by
  rw [Fintype.card_piFinset]
  calc (∏ h, #(B h)) * c ^ σ = ∏ h, (#(B h) * c) := by
        rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    _ ≤ ∏ _h : Fin σ, Fintype.card X := prod_le_prod fun h _ => hB h
    _ = Fintype.card X ^ σ := by rw [prod_const, card_univ, Fintype.card_fin]

/-- **A union of repetition events.** If for each `j ∈ J` the bad sets `B j h` satisfy
`#(B j h) · c ≤ |X|`, the challenge tuples bad in every repetition for some `j ∈ J` satisfy
`# · c^σ ≤ #J · |X|^σ`. -/
theorem card_biUnion_piFinset_mul_pow_le [DecidableEq X] {σ : ℕ} {κ : Type*} [DecidableEq κ]
    (J : Finset κ)
    (B : κ → Fin σ → Finset X) {c : ℕ} (hB : ∀ j ∈ J, ∀ h, #(B j h) * c ≤ Fintype.card X) :
    #(J.biUnion fun j => Fintype.piFinset (B j)) * c ^ σ ≤ #J * Fintype.card X ^ σ := by
  calc #(J.biUnion fun j => Fintype.piFinset (B j)) * c ^ σ
      ≤ (∑ j ∈ J, #(Fintype.piFinset (B j))) * c ^ σ :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ j ∈ J, #(Fintype.piFinset (B j)) * c ^ σ := sum_mul _ _ _
    _ ≤ ∑ _j ∈ J, Fintype.card X ^ σ :=
        sum_le_sum fun j hj => card_piFinset_mul_pow_le (B j) (hB j hj)
    _ = #J * Fintype.card X ^ σ := by rw [sum_const, smul_eq_mul]

/-- **A unique candidate.** If the candidates `y` with `Cand y` are unique and each candidate's
event `Cond y` satisfies `# · c ≤ |X|`, then so does the event that some candidate's event
holds. -/
theorem card_filter_exists_mul_le_of_subsingleton {Y : Type*} (Cand : Y → Prop)
    (hCand : ∀ y y', Cand y → Cand y' → y = y') (Cond : Y → X → Prop) {c : ℕ}
    (hc : ∀ y, Cand y → ∀ [DecidablePred (Cond y)], #{x | Cond y x} * c ≤ Fintype.card X)
    [DecidablePred fun x => ∃ y, Cand y ∧ Cond y x] :
    #{x | ∃ y, Cand y ∧ Cond y x} * c ≤ Fintype.card X := by
  classical
  by_cases hy : ∃ y, Cand y
  · obtain ⟨y₀, hy₀⟩ := hy
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) (hc y₀ hy₀)
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨y, hy, hxy⟩ := hx
    exact hCand y y₀ hy hy₀ ▸ hxy
  · simp only [not_exists] at hy
    have : (univ.filter fun x => ∃ y, Cand y ∧ Cond y x) = ∅ :=
      filter_eq_empty_iff.mpr fun x _ ⟨y, hy', _⟩ => hy y hy'
    rw [this, card_empty, zero_mul]
    exact Nat.zero_le _

end Repetition

/-- **One component of a product.** An event that reads only the first component of
`e a ∈ X × Y` has `#{x | Q x} · |Y|` elements. -/
theorem card_filter_fst_equiv {α X Y : Type*} [Fintype α] [Fintype X] [Fintype Y]
    (e : α ≃ X × Y) (Q : X → Prop) [DecidablePred Q] :
    #{a | Q (e a).1} = #{x | Q x} * Fintype.card Y := by
  classical
  rw [← card_univ (α := Y), ← card_product, ← card_map e.toEmbedding]
  congr 1
  ext ⟨x, y⟩
  simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.coe_toEmbedding, mem_product,
    and_true]
  constructor
  · rintro ⟨a, ha, hax⟩
    rw [hax] at ha
    exact ha
  · intro hx
    exact ⟨e.symm (x, y), by simpa using hx, by simp⟩

/-- An event that reads one component of a product has the density of its count on that
component: `#{x | Q x} · a ≤ c · |X|` gives `#{z | Q (e z).1} · a ≤ c · |α|`. -/
theorem card_filter_fst_mul_le {α X Y : Type*} [Fintype α] [Fintype X] [Fintype Y]
    (e : α ≃ X × Y) (Q : X → Prop) [DecidablePred Q] {a c : ℕ}
    (h : #{x | Q x} * a ≤ c * Fintype.card X) :
    #{z | Q (e z).1} * a ≤ c * Fintype.card α := by
  rw [card_filter_fst_equiv e Q, Fintype.card_congr e, Fintype.card_prod]
  calc #{x | Q x} * Fintype.card Y * a = (#{x | Q x} * a) * Fintype.card Y := by ring
    _ ≤ (c * Fintype.card X) * Fintype.card Y := Nat.mul_le_mul_right _ h
    _ = c * (Fintype.card X * Fintype.card Y) := by ring

end GordieHowe.RepetitionCounting
