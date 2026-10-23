-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.Decoder
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Lists of polynomials agreeing with an arbitrary word

The list bound follows by counting incidences between agreement subsets and
columns. Distinct degree-at-most-d polynomials share at most d agreement
columns. No proximity assumption on the received word is imposed.
-/

namespace GordieHowe.PolynomialAgreementList
open scoped Classical
section

variable {F : Type} [Field F] {N : ℕ}

noncomputable def agreements (D : Fin N → F) (u : Fin N → F) (p : Polynomial F) : Finset (Fin N) :=
  Finset.univ.filter (fun j => p.eval (D j) = u j)

def coefficientVector (d : ℕ) (p : {p : Polynomial F // p.natDegree ≤ d}) :
    Fin (d + 1) → F := fun i => p.val.coeff i

theorem coefficientVector_injective (d : ℕ) :
    Function.Injective (coefficientVector (F := F) d) := by
  intro p q h
  apply Subtype.ext
  apply Polynomial.ext
  intro i
  by_cases hi : i < d + 1
  · exact congrFun h ⟨i, hi⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := p.property; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by have := q.property; omega)]

noncomputable instance boundedFintype [Fintype F] (d : ℕ) :
    Fintype {p : Polynomial F // p.natDegree ≤ d} :=
  Fintype.ofInjective (coefficientVector d) (coefficientVector_injective d)

noncomputable def candidates [Fintype F] (D : Fin N → F) (d a : ℕ) (u : Fin N → F) :
    Finset (Polynomial F) :=
  (Finset.univ.filter (fun p : {p : Polynomial F // p.natDegree ≤ d} =>
    a < (agreements D u p.val).card)).image Subtype.val

@[simp] theorem mem_candidates [Fintype F] (D : Fin N → F) (d a : ℕ)
    (u : Fin N → F) (p : Polynomial F) :
    p ∈ candidates D d a u ↔ p.natDegree ≤ d ∧ a < (agreements D u p).card := by
  simp [candidates, and_comm]

theorem agreement_inter_le (D : Fin N → F) (hD : Function.Injective D)
    (u : Fin N → F) {p q : Polynomial F} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hne : p ≠ q) :
    ((agreements D u p) ∩ (agreements D u q)).card ≤ d := by
  let S := ((agreements D u p) ∩ (agreements D u q)).image D
  have hcard : S.card = ((agreements D u p) ∩ (agreements D u q)).card :=
    Finset.card_image_of_injective _ hD
  have hroot : S.val ⊆ (p - q).roots := by
    intro x hx
    change x ∈ ((agreements D u p) ∩ (agreements D u q)).image D at hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have he := Finset.mem_inter.mp hj
    exact (Polynomial.mem_roots (sub_ne_zero.mpr hne)).mpr (by
      simpa only [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero] using
        (Finset.mem_filter.mp he.1).2.trans (Finset.mem_filter.mp he.2).2.symm)
  have hh := Polynomial.card_le_degree_of_subset_roots hroot
  rw [hcard] at hh
  exact hh.trans ((Polynomial.natDegree_sub_le _ _).trans (max_le hp hq))

/-- Incidence counting for equal-size subsets with bounded intersections. -/
theorem incidence_bound {ι : Type} (s : Finset ι) (B : ι → Finset (Fin N))
    (A d : ℕ) (hsize : ∀ i ∈ s, (B i).card = A)
    (hinter : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ((B i) ∩ (B j)).card ≤ d) :
    (s.card * A) ^ 2 ≤ N * (s.card * (A + (s.card - 1) * d)) := by
  let n : Fin N → ℕ := fun j => ∑ i ∈ s, if j ∈ B i then 1 else 0
  have hsum : ∑ j, n j = s.card * A := by
    dsimp [n]
    rw [Finset.sum_comm]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
    rw [Finset.sum_congr rfl hsize]
    simp
  have hsquare : ∑ j, n j ^ 2 = ∑ i ∈ s, ∑ l ∈ s, ((B i) ∩ (B l)).card := by
    simp only [n, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [ite_mul, one_mul, zero_mul, ← ite_and]
    simp only [Finset.sum_boole]
    simp only [Nat.cast_id]
    congr 1
    ext j
    simp [and_comm]
  have hrow : ∀ i ∈ s, (∑ l ∈ s, ((B i) ∩ (B l)).card) ≤ A + (s.card - 1) * d := by
    intro i hi
    rw [← Finset.sum_erase_add _ _ hi]
    have hb : (∑ l ∈ s.erase i, ((B i) ∩ (B l)).card) ≤ (s.card - 1) * d := by
      calc
        _ ≤ ∑ _l ∈ s.erase i, d := Finset.sum_le_sum (fun l hl =>
          hinter i hi l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl).symm)
        _ = _ := by simp [Finset.card_erase_of_mem hi]
    simpa [hsize i hi, Nat.add_comm] using Nat.add_le_add_right hb A
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := n)
  rw [hsum, hsquare] at hs
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  exact hs.trans (Nat.mul_le_mul_left N (by
    calc
      _ ≤ ∑ _i ∈ s, (A + (s.card - 1) * d) := Finset.sum_le_sum hrow
      _ = _ := by simp))

/-- Rearrange the incidence inequality into the integral Johnson list bound. -/
theorem cardinal_bound {L A d N : ℕ} (hA : A ≤ N) (hJ : N * d < A ^ 2)
    (h : (L * A) ^ 2 ≤ N * (L * (A + (L - 1) * d))) :
    L ≤ N * (A - d) / (A ^ 2 - N * d) := by
  by_cases hL : L = 0
  · simp [hL]
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  have hAd : d ≤ A := by
    by_contra hn
    have hm := Nat.mul_le_mul hA (show A ≤ d by omega)
    nlinarith
  have hcancel : L * (L * A ^ 2) ≤ L * (N * (A + (L - 1) * d)) := by
    nlinarith [h]
  have hh : L * A ^ 2 ≤ N * (A + (L - 1) * d) :=
    Nat.le_of_mul_le_mul_left hcancel hLpos
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hJ)).mpr
  have hsubJ := Nat.sub_add_cancel (Nat.le_of_lt hJ)
  have hsubA := Nat.sub_add_cancel hAd
  have hsubL := Nat.sub_add_cancel hLpos
  nlinarith

/-- Explicit finite list bound for agreement on more than a columns. -/
theorem card_candidates_le [Fintype F] (D : Fin N → F) (hD : Function.Injective D)
    (d a : ℕ) (u : Fin N → F) (hA : a + 1 ≤ N) (hJ : N * d < (a + 1) ^ 2) :
    (candidates D d a u).card ≤ N * (a + 1 - d) / ((a + 1) ^ 2 - N * d) := by
  let I := {p : Polynomial F // p ∈ candidates D d a u}
  have hlarge : ∀ p : I, a + 1 ≤ (agreements D u p.val).card := by
    intro p
    have hp := (mem_candidates D d a u p.val).mp p.property
    omega
  choose B hsub hcard using fun p : I => Finset.exists_subset_card_eq (hlarge p)
  have hinter : ∀ p ∈ (Finset.univ : Finset I), ∀ q ∈ (Finset.univ : Finset I),
      p ≠ q → ((B p) ∩ (B q)).card ≤ d := by
    intro p _ q _ hpq
    have hp := (mem_candidates D d a u p.val).mp p.property
    have hq := (mem_candidates D d a u q.val).mp q.property
    exact (Finset.card_le_card (Finset.inter_subset_inter (hsub p) (hsub q))).trans
      (agreement_inter_le D hD u hp.1 hq.1 (fun h => hpq (Subtype.ext h)))
  have hc := incidence_bound Finset.univ B (a + 1) d (fun p _ => hcard p) hinter
  have hb := cardinal_bound hA hJ hc
  simpa only [Finset.card_univ, I, Fintype.card_coe] using hb

end
end GordieHowe.PolynomialAgreementList
