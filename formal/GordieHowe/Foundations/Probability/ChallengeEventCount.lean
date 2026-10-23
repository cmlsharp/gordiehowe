-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.Foundations.Probability.Probability
public import Mathlib.Data.Finset.Prod
public import Mathlib.Basic.NNReal.Basic

@[expose] public section

/-!
# Counting bad challenges on products

`TwoChallengeEvent.badSet` is the set of bad pairs of a bivariate event as a finset of `K × K`,
with at most `deg · |K|` elements (Schwartz–Zippel, `TwoChallengeEvent.card_zeros_le`).
`ChallengeEvent.card_filter_badAt_le` is the univariate count.
`ChallengeEvent.probUniform_badAt_le_compl` is the univariate bound for a challenge uniform
outside a set `U`. `card_filter_prod_le` counts the pairs of `α × β` whose first coordinate
lies in `s` or whose second lies in `t`: at most `|s| · |β| + |α| · |t|`.
-/

namespace GordieHowe

open scoped NNReal ENNReal Classical
open IOP

namespace ChallengeEvent

variable {K : Type*} [Field K] [Fintype K]

/-- Schwartz–Zippel for a univariate event: at most `deg` of the `|K|` challenges are bad. -/
theorem card_filter_badAt_le (ev : ChallengeEvent K) :
    ((Finset.univ.filter ev.BadAt).card : ℝ≥0) ≤ (ev.deg / Fintype.card K : ℝ≥0) * Fintype.card K := by
  have hK : (Fintype.card K : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_cancel₀ _ hK]
  have hs : Finset.univ.filter ev.BadAt = ev.badSet := by
    ext δ
    simp [ChallengeEvent.mem_badSet_iff]
  rw [hs]
  exact_mod_cast ev.badSet_card_le

/-- **A challenge event under a uniform challenge**: probability at most the degree over the field
size (`ChallengeEvent.card_filter_badAt_le`). -/
theorem probUniform_badAt_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ev : ChallengeEvent F) :
    Pr[a ← F : ev.BadAt a] ≤ ((ev.deg / Fintype.card F : ℝ≥0) : ℝ≥0∞) := by
  classical
  exact (card_le_iff_probUniform_le F _ _).mp ev.card_filter_badAt_le

/-- The challenges outside `U`: `|F| - |U|` of them. -/
theorem card_notMem {F : Type} [Fintype F] [DecidableEq F] (U : Finset F) :
    Fintype.card {x : F // x ∉ U} = Fintype.card F - U.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe]

/-- Outside a set `U`, still at most `deg` challenges are bad. -/
theorem card_filter_badAt_compl_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ev : ChallengeEvent F) (U : Finset F) :
    (Finset.univ.filter fun a : {x : F // x ∉ U} => ev.BadAt a).card ≤ ev.deg :=
  (Finset.card_le_card_of_injOn Subtype.val
    (fun a ha => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
      exact ChallengeEvent.mem_badSet_iff.mpr ha)
    fun a _ b _ h => Subtype.ext h).trans ev.badSet_card_le

/-- **A challenge event under a challenge uniform outside `U`**: probability at most the degree
over `|F| - |U|`, the number of challenges outside `U` (at most `deg` of them are bad). -/
theorem probUniform_badAt_le_compl {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ev : ChallengeEvent F) (U : Finset F) [Nonempty {x : F // x ∉ U}] :
    Pr[a ← {x : F // x ∉ U} : ev.BadAt a] ≤
      ((ev.deg / (Fintype.card F - U.card : ℕ) : ℝ≥0) : ℝ≥0∞) := by
  classical
  refine (card_le_iff_probUniform_le _ _ _).mp ?_
  have hpos : (0 : ℝ≥0) < (Fintype.card F - U.card : ℕ) := by
    rw [← card_notMem]
    exact_mod_cast Fintype.card_pos
  rw [card_notMem, div_mul_cancel₀ _ hpos.ne']
  exact_mod_cast ev.card_filter_badAt_compl_le U

end ChallengeEvent

namespace TwoChallengeEvent

variable {K : Type*} [Field K] [Fintype K]

/-- The bad pairs `(δ₁, δ₂)`, as a finset. -/
noncomputable def badSet (ev : TwoChallengeEvent K) : Finset (K × K) :=
  Finset.univ.filter fun p => ev.BadAt p.1 p.2

theorem mem_badSet_iff {ev : TwoChallengeEvent K} {p : K × K} : p ∈ ev.badSet ↔ ev.BadAt p.1 p.2 := by
  simp [badSet]

/-- A nonzero bivariate polynomial of total degree at most `deg` has at most `deg · |K|`
zeros in `K × K`. -/
theorem badSet_card_le (ev : TwoChallengeEvent K) : ev.badSet.card ≤ ev.deg * Fintype.card K := by
  by_cases hne : ev.poly = 0
  · have : ev.badSet = ∅ := by
      ext p
      simp [mem_badSet_iff, BadAt, hne]
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  · refine le_trans ?_ (ev.card_zeros_le hne)
    refine Finset.card_le_card_of_injOn (fun p => ![p.1, p.2]) (fun p hp => ?_) (fun p _ q _ h => ?_)
    · rw [Finset.mem_coe, mem_badSet_iff] at hp
      simpa using hp.2
    · have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      exact Prod.ext h0 h1

end TwoChallengeEvent

open Finset in
/-- Pairs whose first or second coordinate lies in a given set: at most
`|s| · |β| + |α| · |t|`. A statement about Mathlib objects only, a candidate for
`GordieHowe/Foundations/ToMathlib`. -/
theorem card_filter_prod_le {α β : Type*} [Fintype α] [Fintype β] (s : Finset α) (t : Finset β)
    (p : α × β → Prop) [DecidablePred p] (h : ∀ x, p x → x.1 ∈ s ∨ x.2 ∈ t) :
    #{x | p x} ≤ #s * Fintype.card β + Fintype.card α * #t := by
  calc #{x | p x} ≤ #(s ×ˢ (univ : Finset β) ∪ (univ : Finset α) ×ˢ t) := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        rcases h x hx with h1 | h2
        · exact mem_union_left _ (mem_product.mpr ⟨h1, mem_univ _⟩)
        · exact mem_union_right _ (mem_product.mpr ⟨mem_univ _, h2⟩)
    _ ≤ #(s ×ˢ (univ : Finset β)) + #((univ : Finset α) ×ˢ t) := card_union_le _ _
    _ = #s * Fintype.card β + Fintype.card α * #t := by
        rw [card_product, card_product, card_univ, card_univ]

end GordieHowe
