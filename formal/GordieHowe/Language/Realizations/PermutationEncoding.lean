-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.PermutationEvent
public import GordieHowe.Foundations.Probability.ChallengeEventCount
public import GordieHowe.Headline

@[expose] public section

/-!
# The permutation check with a random encoding point

A record of arity `ℓ` is `r : Fin ℓ → F`, encoded at a point `X` as
`encAt X r = ∑_{c < ℓ} X^c r_c`. `MSet ζ X L R` is the equation of the permutation check:
`∏ (ζ - encAt X l) = ∏ (ζ - encAt X r)` over the records of the lists `L` and `R`.

For lists that are not permutations of each other and a uniform encoding point `γ`
(the paper's `lem:o-multiset`, part 2):
- `probUniform_prodPoly_eq_le`: the two products, as polynomials in `ζ`, agree with probability
  at most `N (ℓ - 1) / |F|`, with `N` the length of the longer list;
- `probUniform_mset_le_of_prodPoly_ne`: at a point where they differ, the equation holds with
  probability at most `N / |F|` over a uniform `ζ`;
- `probUniform_mset_joint_le`: for `γ` and `ζ` drawn together, the equation holds with
  probability at most `N ℓ / |F|`.

The proof works in `F[X][X]`, the polynomials in `ζ` whose coefficients are polynomials in `γ`.
Records encode to distinct polynomials `encPoly r` in `γ`, so the difference `encDiff L R` of the
two products is nonzero (`OfflineMemory.multiset_ofList_eq_of_prod_X_sub_C_eq`). Its leading
coefficient in `ζ` is a nonzero polynomial in `γ` of degree at most `N (ℓ - 1)` (`encEvent`),
and the products at `γ` agree only at a root of it.
-/

namespace GordieHowe.PermutationEvent

open Polynomial IOP
open scoped NNReal ENNReal

variable {F : Type*} [Field F] {ℓ : ℕ}

/-- The encoding `enc_X(r) = ∑_{c < ℓ} X^c r_c` of a record of arity `ℓ` at the point `X`. -/
def encAt (X : F) (r : Fin ℓ → F) : F := ∑ c : Fin ℓ, X ^ c.val * r c

/-- The permutation-check equation `MSet_{ζ, X}(L, R)`: the product of `ζ - encAt X l` over the
records of `L` equals the product over the records of `R`. -/
def MSet (ζ X : F) (L R : List (Fin ℓ → F)) : Prop :=
  (L.map fun l => ζ - encAt X l).prod = (R.map fun r => ζ - encAt X r).prod

/-- The encoding of a record as a polynomial in the encoding point: `∑_{c < ℓ} r_c X^c`. -/
noncomputable def encPoly (r : Fin ℓ → F) : F[X] := ∑ c : Fin ℓ, C (r c) * X ^ c.val

theorem eval_encPoly (γ : F) (r : Fin ℓ → F) : (encPoly r).eval γ = encAt γ r := by
  simp only [encPoly, encAt, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem coeff_encPoly (r : Fin ℓ → F) (c : Fin ℓ) : (encPoly r).coeff c = r c := by
  simp [encPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj]

theorem natDegree_encPoly_le (r : Fin ℓ → F) : (encPoly r).natDegree ≤ ℓ - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun c _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- Distinct records encode to distinct polynomials. -/
theorem encPoly_injective : Function.Injective (encPoly : (Fin ℓ → F) → F[X]) := fun r s h =>
  funext fun c => by rw [← coeff_encPoly r c, ← coeff_encPoly s c, h]

/-- The difference of the two products as a polynomial in `ζ` whose coefficients are polynomials
in the encoding point. -/
noncomputable def encDiff (L R : List (Fin ℓ → F)) : F[X][X] :=
  prodPoly (L.map encPoly) - prodPoly (R.map encPoly)

/-- Evaluating the coefficients of `encDiff` at `γ` gives the difference of the two products at
`γ`, as polynomials in `ζ`. -/
theorem map_encDiff (γ : F) (L R : List (Fin ℓ → F)) :
    (encDiff L R).map (evalRingHom γ) = prodPoly (L.map (encAt γ)) - prodPoly (R.map (encAt γ)) := by
  have he : (evalRingHom γ : F[X] →+* F) ∘ encPoly = encAt γ (ℓ := ℓ) :=
    funext fun r => eval_encPoly γ r
  rw [encDiff, Polynomial.map_sub, map_prodPoly, map_prodPoly, List.map_map, List.map_map, he]

/-- Lists that are not permutations of each other have distinct products in `F[X][X]`. -/
theorem encDiff_ne_zero {L R : List (Fin ℓ → F)} (hLR : ¬ L.Perm R) : encDiff L R ≠ 0 := by
  intro h
  have hm := OfflineMemory.multiset_ofList_eq_of_prod_X_sub_C_eq (sub_eq_zero.mp h)
  rw [← Multiset.map_coe, ← Multiset.map_coe] at hm
  exact hLR (Multiset.coe_eq_coe.mp (Multiset.map_injective encPoly_injective hm))

/-- Every coefficient of `encDiff L R` has degree at most `N (ℓ - 1)` in the encoding point. -/
theorem natDegree_coeff_encDiff_le (L R : List (Fin ℓ → F)) (k : ℕ) :
    ((encDiff L R).coeff k).natDegree ≤ max L.length R.length * (ℓ - 1) := by
  have hd : ∀ M : List (Fin ℓ → F), ∀ a ∈ M.map encPoly, a.natDegree ≤ ℓ - 1 := fun M a ha => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
    exact natDegree_encPoly_le r
  have hL := natDegree_coeff_prodPoly_le (hd L) k
  have hR := natDegree_coeff_prodPoly_le (hd R) k
  rw [List.length_map] at hL hR
  rw [encDiff, coeff_sub]
  exact (natDegree_sub_le _ _).trans
    (max_le (hL.trans (Nat.mul_le_mul_right _ (le_max_left _ _)))
      (hR.trans (Nat.mul_le_mul_right _ (le_max_right _ _))))

/-- **The encoding event**: the leading coefficient in `ζ` of `encDiff L R`, a polynomial in the
encoding point of degree at most `N (ℓ - 1)`. -/
noncomputable def encEvent (L R : List (Fin ℓ → F)) : ChallengeEvent F :=
  ⟨(encDiff L R).leadingCoeff, max L.length R.length * (ℓ - 1),
    natDegree_coeff_encDiff_le L R _⟩

/-- For lists that are not permutations of each other, the two products agree as polynomials in
`ζ` at an encoding point `γ` only when `γ` is a root of the encoding event. -/
theorem encEvent_badAt_of_prodPoly_eq [DecidableEq F] {L R : List (Fin ℓ → F)} (hLR : ¬ L.Perm R)
    {γ : F} (h : prodPoly (L.map (encAt γ)) = prodPoly (R.map (encAt γ))) :
    (encEvent L R).BadAt γ := by
  refine ⟨leadingCoeff_ne_zero.mpr (encDiff_ne_zero hLR), ?_⟩
  have h0 : (encDiff L R).map (evalRingHom γ) = 0 := by rw [map_encDiff, h, sub_self]
  have hc := congrArg (fun p => p.coeff (encDiff L R).natDegree) h0
  rw [coeff_map, coeff_zero] at hc
  exact hc

/-- **lem:o-multiset (2), the encoding point**: for lists `L` and `R` of records of arity `ℓ`
that are not permutations of each other, the two products of the permutation check, as
polynomials in `ζ`, agree at a uniform encoding point `γ` with probability at most
`N (ℓ - 1) / |F|`, where `N` is the length of the longer list. -/
@[headline]
theorem probUniform_prodPoly_eq_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {L R : List (Fin ℓ → F)} (hLR : ¬ L.Perm R) :
    Pr[γ ← F : prodPoly (L.map (encAt γ)) = prodPoly (R.map (encAt γ))] ≤
      (((max L.length R.length * (ℓ - 1) : ℕ) / Fintype.card F : ℝ≥0) : ℝ≥0∞) :=
  ((PMF.uniformOfFintype F).toOuterMeasure.mono fun _ hγ =>
    encEvent_badAt_of_prodPoly_eq hLR hγ).trans (encEvent L R).probUniform_badAt_le

/-- **lem:o-multiset (2), the challenge**: at an encoding point `γ` where the two products differ
as polynomials in `ζ`, the permutation-check equation holds with probability at most `N / |F|`
over a uniform `ζ`, where `N` is the length of the longer list. -/
@[headline]
theorem probUniform_mset_le_of_prodPoly_ne {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {L R : List (Fin ℓ → F)} {γ : F}
    (h : prodPoly (L.map (encAt γ)) ≠ prodPoly (R.map (encAt γ))) :
    Pr[ζ ← F : MSet ζ γ L R] ≤ ((max L.length R.length / Fintype.card F : ℝ≥0) : ℝ≥0∞) := by
  have hb := (permEvent (L.map (encAt γ)) (R.map (encAt γ))).probUniform_badAt_le
  simp only [permEvent, List.length_map] at hb
  refine ((PMF.uniformOfFintype F).toOuterMeasure.mono fun ζ hζ => ?_).trans hb
  refine ⟨sub_ne_zero.mpr h, ?_⟩
  change (prodPoly _ - prodPoly _).eval ζ = 0
  rw [eval_sub, eval_prodPoly, eval_prodPoly, List.map_map, List.map_map, sub_eq_zero]
  exact hζ

/-- **lem:o-multiset (2), joint draw**: for lists `L` and `R` of records of arity `ℓ ≥ 1` that are
not permutations of each other, with `γ` and `ζ` drawn together uniformly, the permutation-check
equation `MSet ζ γ L R` holds with probability at most `N ℓ / |F|`, where `N` is the length of
the longer list. -/
@[headline]
theorem probUniform_mset_joint_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {L R : List (Fin ℓ → F)} (hℓ : 1 ≤ ℓ) (hLR : ¬ L.Perm R) :
    Pr[p ← F × F : MSet p.2 p.1 L R] ≤
      (((max L.length R.length * ℓ : ℕ) / Fintype.card F : ℝ≥0) : ℝ≥0∞) := by
  refine (probUniform_prod_le_add (fun p : F × F => MSet p.2 p.1 L R) (encEvent L R).BadAt
    fun γ hγ => probUniform_mset_le_of_prodPoly_ne
      fun h => hγ (encEvent_badAt_of_prodPoly_eq hLR h)).trans ?_
  refine (add_le_add le_rfl (encEvent L R).probUniform_badAt_le).trans ?_
  rw [← ENNReal.coe_add, ENNReal.coe_le_coe, ← add_div]
  gcongr
  change ((max L.length R.length : ℕ) : ℝ≥0) + ((max L.length R.length * (ℓ - 1) : ℕ) : ℝ≥0) ≤ _
  rw [← Nat.cast_add, Nat.cast_le]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  rw [Nat.add_sub_cancel_left, mul_add, mul_one]

end GordieHowe.PermutationEvent
