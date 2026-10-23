-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.SubfieldCode
public import Mathlib.Data.NNReal.Basic
public import GordieHowe.Headline

@[expose] public section

/-!
# Soundness of a subfield check on opened Ligero columns

A Ligero row is committed as a Reed–Solomon codeword: a polynomial `f` of degree `< k` over `F`,
evaluated at the domain points `D`. For `GF(2^128)` the domain lies in the subfield `E = GF(2^16)`
(`lib/gf2k/gf2_128.h`: `of_scalar` decomposes over the subfield basis, `max_rs_domain = 2^16`). The
proximity test gives that each committed row `u` is close to some codeword; the extractor decodes
`f`.

A proposed packed-witness format for the H proofs checks that every opened entry of a packed row
lies in `E`. This file proves the check sound: if the decoded polynomial does not have coefficients
in `E`, then fewer than `e + k` entries of a row within distance `e` lie in `E` (by
`Polynomial.coeff_mem_of_eval_mem`), so `t` columns opened without replacement (`Random::choose`,
`third_party/longfellow/lib/random/random.h:93-105`, over the encoding positions past the message block,
`lib/ligero/ligero_transcript.h`, `gen_idx`) all land in `E` with probability at most
`(e+k).descFactorial t / N.descFactorial t`. This retains the exact sampling-without-replacement
denominator. One bad row suffices; no union bound over rows is needed.

The honest prover holds in the C++ prover: rows below the subfield boundary use subfield randomness
and subfield interpolation (`lib/ligero/ligero_prover.h`, `random_subfield_row`), so honest openings
are `E`-valued.
-/

open Polynomial

namespace GordieHowe.Ligero.SubfieldTest

variable {F : Type*} [Field F]

open scoped Classical

/-- Entries of a row within distance `e` of the evaluations of `f` that lie in
`E`: fewer than `e + k` when `f` has degree `< k`, the domain lies in `E`, and
some coefficient of `f` is outside `E`. -/
theorem card_filter_mem_lt (E : Subfield F) {N k e : ℕ} {D : Fin N → F}
    (hD : Function.Injective D) (hDE : ∀ j, D j ∈ E) {f : F[X]} (hf : f.natDegree < k)
    (hbad : ∃ i, f.coeff i ∉ E) {u : Fin N → F}
    (hclose : (Finset.univ.filter fun j => u j ≠ f.eval (D j)).card ≤ e) :
    (Finset.univ.filter fun j => u j ∈ E).card < e + k := by
  by_contra hcontra
  rw [not_lt] at hcontra
  set A := Finset.univ.filter fun j : Fin N => u j ∈ E with hAdef
  set B := Finset.univ.filter fun j : Fin N => u j ≠ f.eval (D j) with hBdef
  have hsdiff : A.card - B.card ≤ (A \ B).card := Finset.le_card_sdiff B A
  have hk : k ≤ (A \ B).card := by omega
  set S := (A \ B).image D with hSdef
  have hScard : S.card = (A \ B).card := Finset.card_image_of_injective _ hD
  have hSE : ∀ x ∈ S, x ∈ E := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hDE j
  have hval : ∀ x ∈ S, f.eval x ∈ E := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjA : j ∈ A := (Finset.mem_sdiff.mp hj).1
    have hjB : j ∉ B := (Finset.mem_sdiff.mp hj).2
    have huE : u j ∈ E := (Finset.mem_filter.mp hjA).2
    have heq : u j = f.eval (D j) := by
      by_contra hne
      exact hjB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    rwa [← heq]
  have hk' : k ≤ S.card := by rw [hScard]; exact hk
  have hdeg : f.natDegree < S.card := lt_of_lt_of_le hf hk'
  obtain ⟨i, hi⟩ := hbad
  exact hi (Polynomial.coeff_mem_of_eval_mem E hSE hdeg hval i)

/-- Exact-query budget. When there are no injective queries (`t > N`), the
ratio is zero; the corresponding challenge space is empty. -/
noncomputable def queryError (e k N t : ℕ) : NNReal :=
  ((e + k).descFactorial t : NNReal) / N.descFactorial t

/-- Exact distinct-column count, retaining a convenient non-strict `e+k`
upper bound on the number of subfield-valued entries. -/
theorem subfieldCheck_sound_exact (E : Subfield F) {N k e : ℕ} {D : Fin N → F}
    (hD : Function.Injective D) (hDE : ∀ j, D j ∈ E) {f : F[X]} (hf : f.natDegree < k)
    (hbad : ∃ i, f.coeff i ∉ E) {u : Fin N → F}
    (hclose : (Finset.univ.filter fun j => u j ≠ f.eval (D j)).card ≤ e) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, u (q s) ∈ E).card ≤
      (e + k).descFactorial t := by
  let G := Finset.univ.filter fun j : Fin N => u j ∈ E
  have he : (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, u (q s) ∈ E) =
      Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, q s ∈ G := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, G]
  rw [he, Fintype.card_embedding_filter_mem]
  exact Nat.descFactorial_le t (card_filter_mem_lt E hD hDE hf hbad hclose).le

/-! ### The subfield check charged jointly with the low-degree test -/

/-- **A row that agrees on `S` with a polynomial outside the subfield**: `f` has degree `< k` and a
coefficient outside the subfield `E`, and the row `u` equals the evaluations of `f` at the domain
`D` on the columns `S`. -/
structure AgreesWithNonSubfield (E : Subfield F) {N : ℕ} (D : Fin N → F) (k : ℕ)
    (S : Finset (Fin N)) (u : Fin N → F) (f : F[X]) : Prop where
  natDegree_lt : f.natDegree < k
  exists_coeff_not_mem : ∃ i, f.coeff i ∉ E
  eq_eval : ∀ j ∈ S, u j = f.eval (D j)

/-- Columns of `S` at which a row agreeing on `S` with a polynomial outside the subfield takes a
value in `E`: fewer than `k`, when the domain lies in `E`. They are points of `E` at which `f`
takes values in `E`, and `k` of them would put every coefficient of `f` in `E`
(`Polynomial.coeff_mem_of_eval_mem`). -/
theorem card_filter_mem_lt_of_agrees (E : Subfield F) {N k : ℕ} {D : Fin N → F}
    (hD : Function.Injective D) (hDE : ∀ j, D j ∈ E) {S : Finset (Fin N)} {u : Fin N → F}
    {f : F[X]} (h : AgreesWithNonSubfield E D k S u f) :
    (S.filter fun j => u j ∈ E).card < k := by
  by_contra hcontra
  rw [not_lt] at hcontra
  set G := S.filter fun j => u j ∈ E
  have hdeg : f.natDegree < (G.image D).card := by
    rw [Finset.card_image_of_injective _ hD]
    exact h.natDegree_lt.trans_le hcontra
  obtain ⟨i, hi⟩ := h.exists_coeff_not_mem
  refine hi (Polynomial.coeff_mem_of_eval_mem E ?_ hdeg ?_ i)
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hDE j
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hjS, hjE⟩ := Finset.mem_filter.mp hj
    rw [← h.eq_eval j hjS]
    exact hjE

/-- **Paper `lem:subfield-test`**, counting form: the joint subfield count. If
the domain lies in `E` and the row `u` agrees on the columns `S` with a polynomial of degree `< k`
with a coefficient outside `E`, then among the injective samples of `t` columns, those lying in `S`
with every opened entry in `E` number at most `(k - 1).descFactorial t`: they are samples of the
fewer than `k` columns of `S` where `u` takes a value in `E` (`card_filter_mem_lt_of_agrees`). -/
@[headline]
theorem card_filter_mem_le_of_agrees (E : Subfield F) {N k : ℕ} {D : Fin N → F}
    (hD : Function.Injective D) (hDE : ∀ j, D j ∈ E) {S : Finset (Fin N)} {u : Fin N → F}
    {f : F[X]} (h : AgreesWithNonSubfield E D k S u f) (t : ℕ) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, q s ∈ S ∧ u (q s) ∈ E).card ≤
      (k - 1).descFactorial t := by
  let G := S.filter fun j => u j ∈ E
  have he : (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, q s ∈ S ∧ u (q s) ∈ E) =
      Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, q s ∈ G := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, G]
  rw [he, Fintype.card_embedding_filter_mem]
  exact Nat.descFactorial_le t (Nat.le_sub_one_of_lt (card_filter_mem_lt_of_agrees E hD hDE h))

/-- **The joint subfield error**: `(k - 1).descFactorial t / N.descFactorial t`, the fraction of
the samples of `t` distinct columns out of `N` counted by `card_filter_mem_le_of_agrees`. -/
noncomputable def jointSubfieldError (k N t : ℕ) : NNReal :=
  ((k - 1).descFactorial t : NNReal) / N.descFactorial t

end GordieHowe.Ligero.SubfieldTest
