-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Emulated.Rows
public import GordieHowe.Foundations.Algebra.DFT
public import GordieHowe.Foundations.Algebra.DFTExtra
public import GordieHowe.Foundations.Algebra.BitReverse
public import GordieHowe.Applications.MLDSA44.Spec.NTT

@[expose] public section

/-!
# Native signature relations as Ligero linear rows

`native_linear::Relation` (`lib/circuits/ntt/native_linear.h`) specifies coefficient equations over
`F[X]/(X^n + 1)` to Ligero: `groups` groups of `n` rows, each row the signed sum of its group's
terms at one coefficient, equal to zero. A term is a witness polynomial itself, or its negacyclic
product with a public polynomial. Row `k` of group `r` has index `r·n + k` (`finProdFinEquiv`). Both
native arms use it: Falcon-512 native (`GordieHowe.Falcon512.Native.Rows`) and ML-DSA-44 native.

The verifier never forms the rows. `extra()` defines them through `accumulate` and `gen`: `gen` is
zero on every row; `accumulate λ` adds `sign·λ(r,k)` to coefficient `k` of a plain term's
polynomial, and for a product term puts the weights `NTT⁻¹(sign · NTT(λ_r) ⊙ spectrum)` on its
polynomial, where the spectrum is the forward negacyclic transform of the reversed public polynomial
`a* = [a₀, −a_{n−1}, …, −a₁]` (`native_linear.h:121-189`; the negacyclic plan is
`host_ntt::NegacyclicPlan`, the same twist-and-cyclic transform as the emulated arm's
`emulated_ntt::Plan`). The C++ shares one inverse transform among the product terms on the same
witness polynomial. Here a row is stated by its meaning: coefficient `k` of a product term is
coefficient `k` of the negacyclic product (`Term.coeff`), and row `r·n + k` is the signed sum of
group `r`'s terms at coefficient `k` (`rows`, `rows_flatMap`).

A public polynomial is given in coefficient form or in NTT form (`Public`, the C++ `PublicForm`,
`native_linear.h:23-25`; ML-DSA native gives `Â` in NTT form, `signature_relation` in
`lib/gordiehowe/examples/mldsa/mldsa_native.h`). An NTT-form input `d` holds the evaluations at
`ψ^(2·σ(k) + 1)`, the negacyclic plan's order `σ`. `extra()` then takes the spectrum of
`a* = a(x⁻¹)` to be `d[n - 1 - k]` with no transform (`native_linear.h:133-137`): that is correct
because inversion sends `ψ^(2·σ(k) + 1)` to `ψ^(2·σ(n - 1 - k) + 1)` when `σ` commutes with
`k ↦ n - 1 - k`, as bit reversal does (`bitRev_rev`). The term records the data `d` the verifier
reads and the coefficient polynomial `a` the row means, and the rows read `a`. For ML-DSA the
vendored `NTT` produces the spectrum of `a` at `σ = bitRev 8` and `ψ = ζ`.
-/

namespace GordieHowe.NativeLinear

variable {F : Type*} [Field F] {Wit : Type*} [AddCommGroup Wit] [Module F Wit]
  {n groups : ℕ}

/-! ### The negacyclic transforms

Both relation evaluators transform with the same plan: `host_ntt::NegacyclicPlan` in the native arms
and `emulated_ntt::Plan` (`lib/circuits/ntt/emulated_signature.h:36-64`) in the emulated arms. The
forward transform multiplies coordinate `j` by `ψ^j` and applies the cyclic transform with root
`ψ²`; the inverse applies the unnormalized cyclic inverse and multiplies coordinate `j` by
`n⁻¹ ψ^(−j)`. -/

/-- A public polynomial in one of the two `PublicForm`s: its coefficients `a`, or the NTT-form
data `d` the verifier reads together with the coefficient polynomial `a` it denotes. -/
inductive Public (F : Type*) (n : ℕ) where
  | coeffs (a : Fin n → F)
  | ntt (d a : Fin n → F)

/-- One term of a group: a witness polynomial (its `n` coefficients as functionals),
a sign, and an optional public polynomial it is multiplied by. -/
structure Term (F Wit : Type*) [Field F] [AddCommGroup Wit] [Module F Wit] (n groups : ℕ) where
  row : Fin groups
  poly : Fin n → (Wit →ₗ[F] F)
  sign : F
  pub : Option (Public F n)

/-- Coefficient `k` of a term, as a functional on the witness: the polynomial's
coefficient, or coefficient `k` of its negacyclic product with the public polynomial. -/
def Term.coeff (t : Term F Wit n groups) (k : Fin n) : Wit →ₗ[F] F :=
  match t.pub with
  | none => t.poly k
  | some (.coeffs a) => ∑ j, LatticeCrypto.negacyclicConvCoeff a (Pi.single j 1) k • t.poly j
  | some (.ntt _ a) => ∑ j, LatticeCrypto.negacyclicConvCoeff a (Pi.single j 1) k • t.poly j

/-- Row `r·n + k`: the signed sum of group `r`'s terms at coefficient `k`, equal to
zero. -/
def rows (terms : List (Term F Wit n groups)) (i : Fin (groups * n)) : Row F Wit :=
  let rk := finProdFinEquiv.symm i
  (((terms.filter fun t => t.row = rk.1).map fun t => t.sign • t.coeff rk.2).sum, 0)

/-- Filtering a list assembled group by group to the items of group `r` and summing keeps
exactly group `r`'s items. -/
theorem sum_map_filter_flatMap {α M : Type*} [AddCommMonoid M] (row : α → Fin groups)
    (g : Fin groups → List α) (hg : ∀ a, ∀ t ∈ g a, row t = a) (r : Fin groups) (h : α → M) :
    ((((List.finRange groups).flatMap g).filter fun t => row t = r).map h).sum =
      ((g r).map h).sum := by
  have key : ∀ l : List (Fin groups), (((l.flatMap g).filter fun t => row t = r).map h).sum =
      (l.map fun a => if a = r then ((g a).map h).sum else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, List.filter_append, List.map_append, List.sum_append, ih,
        List.map_cons, List.sum_cons]
      congr 1
      split_ifs with har
      · subst har
        rw [List.filter_eq_self.mpr fun t ht => by simpa using hg a t ht]
      · rw [List.filter_eq_nil_iff.mpr fun t ht => by simpa [hg a t ht] using har]
        rfl
  rw [key, ← Fin.sum_univ_def, Finset.sum_ite_eq']
  simp

/-- Row `(r, k)` of a term list assembled group by group is the signed sum of group `r`'s
terms at coefficient `k`. -/
theorem rows_flatMap (g : Fin groups → List (Term F Wit n groups))
    (hg : ∀ a, ∀ t ∈ g a, t.row = a) (r : Fin groups) (k : Fin n) :
    (rows ((List.finRange groups).flatMap g) (finProdFinEquiv (r, k))).1 =
      ((g r).map fun t => t.sign • t.coeff k).sum := by
  unfold rows
  rw [Equiv.symm_apply_apply]
  exact sum_map_filter_flatMap Term.row g hg r _

end GordieHowe.NativeLinear
