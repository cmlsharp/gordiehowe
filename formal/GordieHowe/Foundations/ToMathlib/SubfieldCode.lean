-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Fintype.CardEmbedding

@[expose] public section

/-!
# Subfield subcodes of polynomial evaluation codes, and sampling without replacement

Two general facts, candidates for upstreaming to Mathlib (next to
`Mathlib.LinearAlgebra.Lagrange` and `Mathlib.Data.Fintype.CardEmbedding`):

* a polynomial of degree `< |S|` over a field `F` that takes values in a
  subfield `E` at every point of a set `S ⊆ E` has all its coefficients in `E`
  (its Lagrange interpolant on `S` is built from `E`-points and `E`-values);
* among the injective samples of `t` positions from `N`, the fraction landing
  entirely in a set of size `g` is at most `(g / N) ^ t`.
-/

open Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- A polynomial with coefficients in the subfield `E` takes values in `E` at
points of `E`. -/
theorem eval_mem_of_coeff_mem (E : Subfield F) {f : F[X]} (hc : ∀ i, f.coeff i ∈ E)
    {x : F} (hx : x ∈ E) : f.eval x ∈ E := by
  rw [Polynomial.eval_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hc i) (pow_mem hx i)

/-- A polynomial of degree less than `|S|` taking values in the subfield `E` at
the points of `S ⊆ E` has coefficients in `E`.

The Lagrange interpolant of `f` on `S`, built over the field `E` from the
`E`-points of `S` and their `E`-values, agrees with `f` on `S` and has degree
`< |S|`; mapping it back into `F` reproduces `f`, so `f`'s coefficients are the
images of the interpolant's `E`-coefficients. -/
theorem coeff_mem_of_eval_mem (E : Subfield F) {f : F[X]} {S : Finset F}
    (hSE : ∀ x ∈ S, x ∈ E) (hdeg : f.natDegree < S.card) (hval : ∀ x ∈ S, f.eval x ∈ E)
    (i : ℕ) : f.coeff i ∈ E := by
  classical
  set S' : Finset ↥E := S.subtype (· ∈ E) with hS'def
  have hS'map : S'.map (Function.Embedding.subtype _) = S := Finset.subtype_map_of_mem hSE
  have hS'card : S'.card = S.card := by rw [← hS'map, Finset.card_map]
  set r' : ↥E → ↥E := fun y => if h : (y : F) ∈ S then (⟨f.eval (y : F), hval _ h⟩ : ↥E) else 0
    with hr'def
  set g : (↥E)[X] := Lagrange.interpolate S' (id : ↥E → ↥E) r' with hgdef
  have hginj : Set.InjOn (id : ↥E → ↥E) S' := Set.injOn_id _
  have hgdeg : g.degree < (S'.card : WithBot ℕ) := Lagrange.degree_interpolate_lt r' hginj
  have hfdeg : f.degree < (S.card : WithBot ℕ) := by
    rcases eq_or_ne f 0 with hf0 | hf0
    · simp [hf0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hf0).mp hdeg
  have hmapdeg : (Polynomial.map E.subtype g).degree < (S.card : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le (hS'card ▸ hgdeg)
  have heval : ∀ x ∈ S, f.eval x = (Polynomial.map E.subtype g).eval x := by
    intro x hx
    have hxE : x ∈ E := hSE x hx
    have hxeq : (⟨x, hxE⟩ : ↥E) ∈ S' := by simpa [S'] using hx
    have hgeval : g.eval (⟨x, hxE⟩ : ↥E) = r' ⟨x, hxE⟩ :=
      Lagrange.eval_interpolate_at_node r' hginj hxeq
    have hr'eval : r' (⟨x, hxE⟩ : ↥E) = (⟨f.eval x, hval x hx⟩ : ↥E) := by
      simp [r', hx]
    have hstep : (Polynomial.map E.subtype g).eval x = E.subtype (g.eval (⟨x, hxE⟩ : ↥E)) :=
      Polynomial.eval_map_apply (f := E.subtype) (⟨x, hxE⟩ : ↥E)
    rw [hstep, hgeval, hr'eval]
    rfl
  have hfg : f = Polynomial.map E.subtype g := by
    apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq S
    · exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hfdeg hmapdeg)
    · exact heval
  rw [hfg, Polynomial.coeff_map]
  exact (g.coeff i).2

end Polynomial

namespace Nat

/-- The descending factorial and power cross-inequality behind sampling without
replacement: among `t`-samples of `N` positions, restricting to a subset of
size `g ≤ N` (equivalently, samples of `g` positions) shrinks the descending
factorial count by at least the factor `(g / N) ^ t` shrinks `N`'s. -/
theorem descFactorial_mul_pow_le {g N : ℕ} (hgN : g ≤ N) :
    ∀ t : ℕ, g.descFactorial t * N ^ t ≤ g ^ t * N.descFactorial t
  | 0 => by simp
  | t + 1 => by
      have hstep : (g - t) * N ≤ g * (N - t) := by
        by_cases htg : t ≤ g
        · have htN : t ≤ N := htg.trans hgN
          zify [htg, htN]
          nlinarith [mul_nonneg (Nat.cast_nonneg t : (0 : ℤ) ≤ t)
            (sub_nonneg.mpr (show (g : ℤ) ≤ N from by exact_mod_cast hgN))]
        · simp [Nat.sub_eq_zero_of_le (not_le.mp htg).le]
      have IH := descFactorial_mul_pow_le hgN t
      calc g.descFactorial (t + 1) * N ^ (t + 1)
          = (g - t) * N * (g.descFactorial t * N ^ t) := by
            rw [Nat.descFactorial_succ]; ring
        _ ≤ g * (N - t) * (g ^ t * N.descFactorial t) :=
            Nat.mul_le_mul hstep IH
        _ = g ^ (t + 1) * N.descFactorial (t + 1) := by
            rw [Nat.descFactorial_succ]; ring

end Nat

namespace Fintype

/-- Exact count of distinct ordered queries landing in a fixed set. -/
theorem card_embedding_filter_mem {N t : ℕ} (G : Finset (Fin N)) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, q s ∈ G).card =
      G.card.descFactorial t := by
  classical
  have hequiv : {q : Fin t ↪ Fin N // ∀ s, q s ∈ G} ≃ (Fin t ↪ (G : Finset (Fin N))) := {
    toFun := fun q =>
      ⟨fun s => ⟨q.1 s, q.2 s⟩, fun a b hab => q.1.injective (congrArg Subtype.val hab)⟩
    invFun := fun q => ⟨q.trans (Function.Embedding.subtype _), fun s => (q s).2⟩
    left_inv := fun q => by
      apply Subtype.ext
      apply Function.Embedding.ext
      intro s
      rfl
    right_inv := fun q => by
      apply Function.Embedding.ext
      intro s
      rfl }
  have hcard1 : Fintype.card {q : Fin t ↪ Fin N // ∀ s, q s ∈ G} =
      Fintype.card (Fin t ↪ (G : Finset (Fin N))) := Fintype.card_congr hequiv
  have hcard2 : Fintype.card {q : Fin t ↪ Fin N // ∀ s, q s ∈ G} =
      (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, q s ∈ G).card := Fintype.card_subtype _
  have hcard3 : Fintype.card (Fin t ↪ (G : Finset (Fin N))) = G.card.descFactorial t := by
    rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin]
  rw [← hcard2, hcard1, hcard3]

/-- Injective samples landing in `G` occupy at most a `(|G|/N)^t`
fraction; the exact count is `card_embedding_filter_mem`. -/
theorem card_embedding_filter_mem_mul_le {N t : ℕ} (G : Finset (Fin N)) :
    (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, q s ∈ G).card * N ^ t ≤
      G.card ^ t * Fintype.card (Fin t ↪ Fin N) := by
  classical
  rw [card_embedding_filter_mem, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin]
  have hgN : G.card ≤ N := by simpa using Finset.card_le_univ G
  exact Nat.descFactorial_mul_pow_le hgN t

end Fintype
