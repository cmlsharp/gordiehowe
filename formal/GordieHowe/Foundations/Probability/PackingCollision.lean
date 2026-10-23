-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.Probability
public import GordieHowe.Foundations.Algebra.RecordPacking

@[expose] public section

/-!
# Collisions of a record packing at a uniform challenge

A record `(a_0, …, a_{A−1})` packed at the powers `pw` is `Σ_c pw_c · a_c` (`packWith`; the
`gamma` packing of `assert_in`, `lib/gordiehowe/compiler/assert_in.h`, packs at `pw_c = γ^c`).
Two distinct records of length `A` pack equally at `γ` only at a root of their difference's
polynomial, nonzero of degree below `A` (`card_packCollide_le`), so among `n` records some two
distinct ones collide at a uniform `γ` with probability at most `C(n, 2) · (A − 1) / |K|`
(`prob_packCollision_le`). A uniform draw from a product read at one coordinate is a uniform draw
of that coordinate (`probUniform_pi_apply`).
-/

namespace GordieHowe

open Polynomial IOP
open scoped ENNReal NNReal

/-- **A list read below its length** is its entry. -/
theorem List.getD_of_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

variable {K : Type*} [Field K]

/-- **A record packed at the powers `pw`**: `Σ_c pw_c · a_c`. -/
def packWith (pw : ℕ → K) (a : List K) : K :=
  ((List.range a.length).map fun c => pw c * a.getD c 0).sum

/-- **A record packed at the powers of `γ`** is the record packing at `γ` (`RecordPacking.pack`) of
its entries. -/
theorem packWith_pow_eq_pack (γ : K) {A : ℕ} (a : List K) (ha : a.length = A) :
    packWith (γ ^ ·) a = RecordPacking.pack γ fun c : Fin A => a.getD c 0 := by
  subst ha
  unfold packWith RecordPacking.pack
  rw [Fin.sum_univ_eq_sum_range (fun i => γ ^ i * a.getD i 0)]
  rfl

/-- **Two distinct records of length `A` collide at at most `A − 1` points.** -/
theorem card_packCollide_le [Fintype K] [DecidableEq K] {A : ℕ} {a b : List K}
    (ha : a.length = A) (hb : b.length = A) (hab : a ≠ b) :
    (Finset.univ.filter fun γ : K => packWith (γ ^ ·) a = packWith (γ ^ ·) b).card ≤ A - 1 := by
  set c : Fin A → K := fun i => a.getD i 0 - b.getD i 0
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hab (List.ext_getElem (ha.trans hb.symm) fun i h1 h2 => ?_)
    have := hall ⟨i, ha ▸ h1⟩
    simp only [c, sub_eq_zero] at this
    rwa [List.getD_of_lt h1, List.getD_of_lt h2] at this
  obtain ⟨i₀, hi₀⟩ := hc0
  have hA : 0 < A := Nat.lt_of_le_of_lt (Nat.zero_le _) i₀.isLt
  have hP0 : RecordPacking.poly c ≠ 0 := fun h0 =>
    hi₀ (by rw [← RecordPacking.coeff_poly c i₀, h0, coeff_zero])
  have hsub : (Finset.univ.filter fun γ : K => packWith (γ ^ ·) a = packWith (γ ^ ·) b) ⊆
      (RecordPacking.poly c).roots.toFinset := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, RecordPacking.eval_poly]
    have hpc : RecordPacking.pack γ c = RecordPacking.pack γ (fun i : Fin A => a.getD i 0) -
        RecordPacking.pack γ (fun i : Fin A => b.getD i 0) := RecordPacking.pack_sub γ _ _
    rw [hpc, ← packWith_pow_eq_pack γ a ha, ← packWith_pow_eq_pack γ b hb, hγ, sub_self]
  refine (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((card_roots' _).trans ?_))
  have := RecordPacking.natDegree_poly_lt hA c
  omega

/-- **Some two distinct records of a list collide at a uniform challenge** with probability at most
`C(n, 2) · (A − 1) / |K|`, `n` the list's length, every record of length `A`: a union over the
`C(n, 2)` pairs of positions of `card_packCollide_le`. -/
theorem prob_packCollision_le [Fintype K] [DecidableEq K] {A : ℕ} (S : List (List K))
    (hS : ∀ a ∈ S, a.length = A) :
    Pr[γ ← K : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ packWith (γ ^ ·) a = packWith (γ ^ ·) b] ≤
      ((S.length.choose 2 * (A - 1) : ℕ) : ℝ≥0∞) / Fintype.card K := by
  classical
  rw [probUniform_eq_card_div]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  -- The pairs of positions `i < j`.
  set pairs := (Finset.range S.length).sigma fun j => Finset.range j
  have hpairs : pairs.card = S.length.choose 2 := by
    rw [Finset.card_sigma]
    simp only [Finset.card_range]
    rw [Nat.choose_two_right, ← Finset.sum_range_id_mul_two, Nat.mul_div_cancel _ (by norm_num)]
  set bad : (Σ _ : ℕ, ℕ) → Finset K := fun p =>
    Finset.univ.filter fun γ : K => S.getD p.1 [] ≠ S.getD p.2 [] ∧
      packWith (γ ^ ·) (S.getD p.1 []) = packWith (γ ^ ·) (S.getD p.2 [])
  have hsub : (Finset.univ.filter fun γ : K =>
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ packWith (γ ^ ·) a = packWith (γ ^ ·) b) ⊆ pairs.biUnion bad := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    obtain ⟨a, ha, b, hb, hne, heq⟩ := hγ
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    have hij : i ≠ j := fun h => hne (by subst h; rfl)
    simp only [Finset.mem_biUnion, Finset.mem_sigma, Finset.mem_range, bad, Finset.mem_filter,
      Finset.mem_univ, true_and, pairs]
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · refine ⟨⟨j, i⟩, ⟨hj, h⟩, ?_⟩
      rw [List.getD_of_lt hi, List.getD_of_lt hj]
      exact ⟨fun h' => hne h'.symm, heq.symm⟩
    · refine ⟨⟨i, j⟩, ⟨hi, h⟩, ?_⟩
      rw [List.getD_of_lt hi, List.getD_of_lt hj]
      exact ⟨hne, heq⟩
  have hbad : ∀ p ∈ pairs, (bad p).card ≤ A - 1 := by
    intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, pairs] at hp
    have h1 : p.1 < S.length := hp.1
    have h2 : p.2 < S.length := by omega
    by_cases hne : S.getD p.1 [] = S.getD p.2 []
    · have : bad p = ∅ := by
        ext γ
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        exact fun h => absurd hne h
      rw [this, Finset.card_empty]
      exact Nat.zero_le _
    · refine le_trans (Finset.card_le_card fun γ hγ => ?_) (card_packCollide_le
        (hS _ (List.getD_of_lt h1 [] ▸ List.getElem_mem h1))
        (hS _ (List.getD_of_lt h2 [] ▸ List.getElem_mem h2)) hne)
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      exact hγ.2
  calc _ ≤ (pairs.biUnion bad).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ pairs, (bad p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, (A - 1) := Finset.sum_le_sum hbad
    _ = S.length.choose 2 * (A - 1) := by rw [Finset.sum_const, hpairs, smul_eq_mul]

namespace IOP

/-- **A uniform draw read through an equivalence** is a uniform draw. -/
theorem probUniform_comp_equiv {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (p : β → Prop) : Pr[a ← α : p (e a)] = Pr[b ← β : p b] := by
  classical
  rw [probUniform_eq_card_div, probUniform_eq_card_div, Fintype.card_congr e]
  congr 2
  exact_mod_cast Finset.card_bij (fun a _ => e a) (by simp) (fun _ _ _ _ h => e.injective h)
    fun b hb => ⟨e.symm b, by simpa using hb, by simp⟩

/-- **A uniform draw from a product read at its first coordinate** is a uniform draw of it. -/
theorem probUniform_fst {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (p : α → Prop) : Pr[u ← (α × β) : p u.1] = Pr[a ← α : p a] := by
  classical
  rw [probUniform_eq_card_div, probUniform_eq_card_div, Fintype.card_prod]
  have h : (Finset.univ.filter fun u : α × β => p u.1) =
      (Finset.univ.filter p) ×ˢ (Finset.univ : Finset β) := by
    ext u
    simp
  rw [h, Finset.card_product, Finset.card_univ, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

/-- **A uniform draw from a product of types read at one coordinate** is a uniform draw of that
coordinate (`Equiv.piSplitAt`). -/
theorem probUniform_pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] (i₀ : ι) (p : β i₀ → Prop) :
    Pr[c ← (∀ i, β i) : p (c i₀)] = Pr[b ← β i₀ : p b] := by
  rw [← probUniform_fst (β := ∀ i : {j // j ≠ i₀}, β i) p,
    ← probUniform_comp_equiv (Equiv.piSplitAt i₀ β) fun u => p u.1]
  rfl

end IOP

end GordieHowe
