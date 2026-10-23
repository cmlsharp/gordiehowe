-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.Decoder

@[expose] public section

/-!
# Minimum distance of a row from a Reed–Solomon code

Distance minimizes over all degree-bounded polynomials. It does not assume
that the received row is nearby, and is independent of the decoding radius.
Nonzero scaling preserves it. A smaller-radius code retains the same domain
and polynomial space, although its partial decoder may of course change.
-/
namespace GordieHowe.RSCode
open Polynomial
open scoped Classical
variable {F : Type*} [Field F] {N : ℕ}

noncomputable def errorSet (C : RSCode F N) (u : Fin N → F) (p : F[X]) : Finset (Fin N) :=
  Finset.univ.filter fun j => u j ≠ p.eval (C.D j)

@[simp] theorem mem_errorSet (C : RSCode F N) (u : Fin N → F) (p : F[X]) (j : Fin N) :
    j ∈ errorSet C u p ↔ u j ≠ p.eval (C.D j) := by simp [errorSet]

noncomputable def errorCount (C : RSCode F N) (u : Fin N → F) (p : F[X]) : ℕ :=
  (errorSet C u p).card

/-- A common error set cannot add positions to a row already attaining the
allowed error count. -/
theorem errorSet_subset_of_union_card_le (C : RSCode F N) (u v : Fin N → F) (p q : F[X])
    (h : (errorSet C u p ∪ errorSet C v q).card ≤ errorCount C u p) :
    errorSet C v q ⊆ errorSet C u p := by
  have he : errorSet C u p = errorSet C u p ∪ errorSet C v q :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_left h
  rw [he]
  exact Finset.subset_union_right

theorem errorCount_le (C : RSCode F N) (u : Fin N → F) (p : F[X]) :
    errorCount C u p ≤ N := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem exists_row_error (C : RSCode F N) (u : Fin N → F) :
    ∃ e : ℕ, ∃ p : F[X], p.natDegree < C.k ∧ errorCount C u p = e :=
  ⟨errorCount C u 0, 0, by simpa using C.k_pos, rfl⟩

noncomputable def rowDistance (C : RSCode F N) (u : Fin N → F) : ℕ :=
  Nat.find (exists_row_error C u)

theorem rowDistance_le_errorCount (C : RSCode F N) (u : Fin N → F)
    (p : F[X]) (hp : p.natDegree < C.k) : rowDistance C u ≤ errorCount C u p :=
  Nat.find_min' (exists_row_error C u) ⟨p, hp, rfl⟩

noncomputable def closestPolynomial (C : RSCode F N) (u : Fin N → F) : F[X] :=
  (Nat.find_spec (exists_row_error C u)).choose

theorem closestPolynomial_degree (C : RSCode F N) (u : Fin N → F) :
    (closestPolynomial C u).natDegree < C.k :=
  (Nat.find_spec (exists_row_error C u)).choose_spec.1

@[simp] theorem closestPolynomial_errorCount (C : RSCode F N) (u : Fin N → F) :
    errorCount C u (closestPolynomial C u) = rowDistance C u :=
  (Nat.find_spec (exists_row_error C u)).choose_spec.2

theorem rowDistance_le_iff (C : RSCode F N) (u : Fin N → F) (e : ℕ) :
    rowDistance C u ≤ e ↔ ∃ p : F[X], p.natDegree < C.k ∧ errorCount C u p ≤ e := by
  constructor
  · intro h
    exact ⟨closestPolynomial C u, closestPolynomial_degree C u,
      (closestPolynomial_errorCount C u).trans_le h⟩
  · rintro ⟨p,hp,he⟩
    exact (rowDistance_le_errorCount C u p hp).trans he

theorem rowDistance_le (C : RSCode F N) (u : Fin N → F) : rowDistance C u ≤ N :=
  (closestPolynomial_errorCount C u).symm.trans_le (errorCount_le C u _)

/-- Scaling the received word and its candidate polynomial preserves every
error position when the scalar is nonzero. -/
theorem errorCount_smul (C : RSCode F N) (u : Fin N → F) (p : F[X])
    (s : F) (hs : s ≠ 0) : errorCount C (s • u) (s • p) = errorCount C u p := by
  unfold errorCount errorSet
  congr 1
  ext j
  simp [Polynomial.eval_smul, hs]

theorem rowDistance_smul_le (C : RSCode F N) (u : Fin N → F) (s : F) (hs : s ≠ 0) :
    rowDistance C (s • u) ≤ rowDistance C u := by
  apply (rowDistance_le_iff C _ _).mpr
  refine ⟨s • closestPolynomial C u,
    (Polynomial.natDegree_smul_le _ _).trans_lt (closestPolynomial_degree C u), ?_⟩
  rw [errorCount_smul C u _ s hs, closestPolynomial_errorCount]

theorem rowDistance_smul (C : RSCode F N) (u : Fin N → F) (s : F) (hs : s ≠ 0) :
    rowDistance C (s • u) = rowDistance C u := by
  apply le_antisymm (rowDistance_smul_le C u s hs)
  have h := rowDistance_smul_le C (s • u) s⁻¹ (inv_ne_zero hs)
  simpa only [inv_smul_smul₀ hs] using h

/-- Change only the radius used by the canonical decoder. -/
def codeWithRadius (C : RSCode F N) (e : ℕ) (he : 2*e+C.k ≤ N) : RSCode F N :=
  { C with e := e, radius := he }

@[simp] theorem codeWithRadius_D (C : RSCode F N) (e : ℕ) (he : 2*e+C.k ≤ N) :
    (codeWithRadius C e he).D = C.D := rfl

@[simp] theorem codeWithRadius_k (C : RSCode F N) (e : ℕ) (he : 2*e+C.k ≤ N) :
    (codeWithRadius C e he).k = C.k := rfl

@[simp] theorem codeWithRadius_e (C : RSCode F N) (e : ℕ) (he : 2*e+C.k ≤ N) :
    (codeWithRadius C e he).e = e := rfl

@[simp] theorem errorCount_codeWithRadius (C : RSCode F N) (e : ℕ)
    (he : 2*e+C.k ≤ N) (u : Fin N → F) (p : F[X]) :
    errorCount (codeWithRadius C e he) u p = errorCount C u p := rfl

@[simp] theorem distance_codeWithRadius (C : RSCode F N) (e : ℕ)
    (he : 2*e+C.k ≤ N) (u : Fin N → F) :
    rowDistance (codeWithRadius C e he) u = rowDistance C u := rfl

/-- Degree-bounded polynomials within any valid unique-decoding radius agree. -/
theorem polynomial_unique_at (C : RSCode F N) (e : ℕ) (he : 2*e+C.k≤N)
    (u : Fin N → F) (p q : F[X]) (hp : p.natDegree<C.k) (hq : q.natDegree<C.k)
    (hep : errorCount C u p≤e) (heq : errorCount C u q≤e) : p=q := by
  let C' := codeWithRadius C e he
  have hp' : Nearby C' (fun _ : Fin 1 => u) (fun _ => p) := by
    refine ⟨fun _ => hp, ?_⟩
    simpa [columnErrors, errorCount, errorSet, C'] using hep
  have hq' : Nearby C' (fun _ : Fin 1 => u) (fun _ => q) := by
    refine ⟨fun _ => hq, ?_⟩
    simpa [columnErrors, errorCount, errorSet, C'] using heq
  exact congrFun (nearby_unique hp' hq') 0

end GordieHowe.RSCode
