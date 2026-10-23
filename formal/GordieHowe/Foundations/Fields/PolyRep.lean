-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Finiteness
public import GordieHowe.Foundations.Fields.ExecField

@[expose] public section

/-!
# Power-basis representation of a simple extension

An element of `K[X] / (f)`, `f` monic of degree `n` with `X ^ n = ∑ i, r i · X ^ i` modulo `f`,
is stored as its vector of coefficients in the power basis `1, X, …, X ^ (n - 1)`
(V. Shoup, *A Computational Introduction to Number Theory and Algebra*, 2nd ed., section 17.1,
p. 466). Addition is coefficientwise; multiplication is Horner's rule on the second factor's
coefficients, multiplying the accumulator by `X` with `timesX` (shift, and fold the top
coefficient back with `r`); inversion is exponentiation to `q ^ n - 2` for `q` the size of `K`
(`inv_eq_pow_natCard_sub_two`).

`toSpec f` sends a coefficient vector to `∑ i, a i · root f ^ i` in `AdjoinRoot f`; it preserves
the operations (`toSpec_add`, `toSpec_mul`, …) and is a bijection (`toSpec_bijective`, through the
power basis `AdjoinRoot.powerBasis'`). A `PolyRep.Spec` bundles `f` with these facts and with the
size of `K`; `Spec.hom` is `toSpec` as an `ExecOps.Hom` to `AdjoinRoot f`, and `Spec.isField`
states that the concrete operations `ops r card` satisfy the field laws (`ExecOps.IsField`).
-/

namespace GordieHowe.PolyRep

open Polynomial

variable {K : Type} [CommRing K] {n : ℕ}

/-! ## The operations -/

/-- The coefficient of `X ^ i` (`0` from `i = n` on). -/
def coeff (a : Vector K n) (i : ℕ) : K := if h : i < n then a[i] else 0

/-- The zero vector. -/
def zero : Vector K n := Vector.ofFn fun _ => 0

/-- The constant `c`: coefficient `c` at `X ^ 0`. -/
def const (c : K) : Vector K n := Vector.ofFn fun i => if (i : ℕ) = 0 then c else 0

/-- Coefficientwise addition. -/
def add (a b : Vector K n) : Vector K n := Vector.ofFn fun i => a[i] + b[i]

/-- Coefficientwise negation. -/
def neg (a : Vector K n) : Vector K n := Vector.ofFn fun i => -a[i]

/-- Multiplication of every coefficient by `c`. -/
def smul (c : K) (a : Vector K n) : Vector K n := Vector.ofFn fun i => c * a[i]

/-- Multiplication by `X`: shift every coefficient up by one and fold the coefficient of `X ^ n`
back with `X ^ n = ∑ i, r i · X ^ i`. -/
def timesX (r : Fin n → K) (a : Vector K n) : Vector K n :=
  Vector.ofFn fun i => (if (i : ℕ) = 0 then 0 else coeff a ((i : ℕ) - 1)) + coeff a (n - 1) * r i

/-- One step of Horner's rule for `mul r a b`: multiply the accumulator by `X` and add
`coeff b i · a`. -/
def mulStep (r : Fin n → K) (a b : Vector K n) (i : ℕ) (acc : Vector K n) : Vector K n :=
  add (timesX r acc) (smul (coeff b i) a)

/-- Multiplication modulo `X ^ n - ∑ i, r i · X ^ i`: Horner's rule on the coefficients of `b`
from `X ^ (n - 1)` down to `X ^ 0`. -/
def mul (r : Fin n → K) (a b : Vector K n) : Vector K n :=
  (List.range n).foldr (mulStep r a b) zero

/-- The coefficient vector and the coefficient function determine each other. -/
def coordsEquiv : Vector K n ≃ (Fin n → K) where
  toFun a i := a[i]
  invFun := Vector.ofFn
  left_inv a := by ext i hi; simp
  right_inv g := by funext i; simp

@[simp] theorem coordsEquiv_apply (a : Vector K n) (i : Fin n) : coordsEquiv a i = a[i] := rfl

@[simp] theorem coordsEquiv_symm_apply (g : Fin n → K) : coordsEquiv.symm g = Vector.ofFn g :=
  rfl

/-! ## The map to the specification -/

variable (f : K[X])

/-- The element `∑ i, a i · root f ^ i` of `AdjoinRoot f`. -/
noncomputable def toSpec (a : Vector K n) : AdjoinRoot f :=
  ∑ i : Fin n, AdjoinRoot.of f a[i] * AdjoinRoot.root f ^ (i : ℕ)

variable {f}

theorem coeff_fin (a : Vector K n) (i : Fin n) : coeff a i = a[i] := by
  simp [coeff, i.isLt]

@[simp] theorem getElem_ofFn_fin (g : Fin n → K) (i : Fin n) : (Vector.ofFn g)[i] = g i := by
  simp [Fin.getElem_fin]

theorem toSpec_add (a b : Vector K n) : toSpec f (add a b) = toSpec f a + toSpec f b := by
  simp only [toSpec, add, getElem_ofFn_fin, map_add, add_mul, Finset.sum_add_distrib]

theorem toSpec_neg (a : Vector K n) : toSpec f (neg a) = -toSpec f a := by
  simp only [toSpec, neg, getElem_ofFn_fin, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem toSpec_smul (c : K) (a : Vector K n) :
    toSpec f (smul c a) = AdjoinRoot.of f c * toSpec f a := by
  simp only [toSpec, smul, getElem_ofFn_fin, map_mul, Finset.mul_sum, mul_assoc]

theorem toSpec_zero : toSpec f (zero : Vector K n) = 0 := by
  simp only [toSpec, zero, getElem_ofFn_fin, map_zero, zero_mul, Finset.sum_const_zero]

theorem toSpec_const (hn : 0 < n) (c : K) : toSpec f (const c : Vector K n) = AdjoinRoot.of f c := by
  rw [toSpec, Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj => by
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp only [const, getElem_ofFn_fin, this, if_false, map_zero, zero_mul]) (by simp)]
  simp only [const, getElem_ofFn_fin, if_true, pow_zero, mul_one]

/-- Multiplying by `X` is multiplying by the root. -/
theorem toSpec_timesX {r : Fin n → K}
    (hr : AdjoinRoot.root f ^ n = ∑ i : Fin n, AdjoinRoot.of f (r i) * AdjoinRoot.root f ^ (i : ℕ))
    (a : Vector K n) : toSpec f (timesX r a) = AdjoinRoot.root f * toSpec f a := by
  cases n with
  | zero => simp only [toSpec, Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
  | succ m =>
    have htop : coeff a (m + 1 - 1) = a[m] := by simp [coeff]
    have hsplit : toSpec f (timesX r a) =
        (∑ i : Fin (m + 1), AdjoinRoot.of f (if (i : ℕ) = 0 then 0 else coeff a ((i : ℕ) - 1)) *
          AdjoinRoot.root f ^ (i : ℕ)) + AdjoinRoot.of f a[m] * AdjoinRoot.root f ^ (m + 1) := by
      simp only [toSpec, timesX, getElem_ofFn_fin, map_add, map_mul, add_mul,
        Finset.sum_add_distrib, htop, hr, Finset.mul_sum, mul_assoc]
    have hshift : (∑ i : Fin (m + 1), AdjoinRoot.of f (if (i : ℕ) = 0 then 0 else coeff a ((i : ℕ) - 1)) *
          AdjoinRoot.root f ^ (i : ℕ)) =
        ∑ j : Fin m, AdjoinRoot.of f a[(j : ℕ)] * AdjoinRoot.root f ^ ((j : ℕ) + 1) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, ite_true, map_zero, zero_mul, zero_add, Fin.val_succ,
        Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show coeff a j = a[(j : ℕ)] by simp [coeff]]
    have hroot : AdjoinRoot.root f * toSpec f a =
        (∑ j : Fin m, AdjoinRoot.of f a[(j : ℕ)] * AdjoinRoot.root f ^ ((j : ℕ) + 1)) +
          AdjoinRoot.of f a[m] * AdjoinRoot.root f ^ (m + 1) := by
      rw [toSpec, Finset.mul_sum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Fin.getElem_fin, pow_succ]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · ring
    rw [hsplit, hshift, hroot]

theorem toSpec_mulStep {r : Fin n → K}
    (hr : AdjoinRoot.root f ^ n = ∑ i : Fin n, AdjoinRoot.of f (r i) * AdjoinRoot.root f ^ (i : ℕ))
    (a b : Vector K n) (i : ℕ) (acc : Vector K n) :
    toSpec f (mulStep r a b i acc) =
      AdjoinRoot.root f * toSpec f acc + AdjoinRoot.of f (coeff b i) * toSpec f a := by
  rw [mulStep, toSpec_add, toSpec_timesX hr, toSpec_smul]

/-- The Horner loop over the coefficients `s, …, s + m - 1` of `b` multiplies `a` by the
polynomial with those coefficients. -/
theorem toSpec_foldr_mulStep {r : Fin n → K}
    (hr : AdjoinRoot.root f ^ n = ∑ i : Fin n, AdjoinRoot.of f (r i) * AdjoinRoot.root f ^ (i : ℕ))
    (a b : Vector K n) (s m : ℕ) :
    toSpec f ((List.range' s m).foldr (mulStep r a b) zero) =
      toSpec f a *
        ∑ j ∈ Finset.range m, AdjoinRoot.of f (coeff b (s + j)) * AdjoinRoot.root f ^ j := by
  induction m generalizing s with
  | zero => simp [toSpec_zero]
  | succ m ih =>
    rw [List.range'_succ, List.foldr_cons, toSpec_mulStep hr, ih, Finset.sum_range_succ',
      mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show s + 1 + j = s + (j + 1) by omega, pow_succ]
      ring
    · simp only [add_zero, pow_zero, mul_one]
      ring

theorem toSpec_eq_sum_range (b : Vector K n) :
    toSpec f b = ∑ j ∈ Finset.range n, AdjoinRoot.of f (coeff b j) * AdjoinRoot.root f ^ j := by
  rw [toSpec, ← Fin.sum_univ_eq_sum_range (fun j => AdjoinRoot.of f (coeff b j) *
    AdjoinRoot.root f ^ j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_fin]

/-- `mul` is multiplication in `AdjoinRoot f`. -/
theorem toSpec_mul {r : Fin n → K}
    (hr : AdjoinRoot.root f ^ n = ∑ i : Fin n, AdjoinRoot.of f (r i) * AdjoinRoot.root f ^ (i : ℕ))
    (a b : Vector K n) : toSpec f (mul r a b) = toSpec f a * toSpec f b := by
  rw [mul, List.range_eq_range', toSpec_foldr_mulStep hr, toSpec_eq_sum_range b]
  simp only [zero_add]

/-- The generator `X`: coefficient `1` at `X ^ 1`. -/
def gen : Vector K n := Vector.ofFn fun i => if (i : ℕ) = 1 then 1 else 0

theorem toSpec_gen (hn : 1 < n) : toSpec f (gen : Vector K n) = AdjoinRoot.root f := by
  rw [toSpec, Finset.sum_eq_single ⟨1, hn⟩ (fun j _ hj => by
    have : (j : ℕ) ≠ 1 := fun h => hj (Fin.ext h)
    simp only [gen, getElem_ofFn_fin, this, ite_false, map_zero, zero_mul]) (by simp)]
  simp only [gen, getElem_ofFn_fin, ite_true, map_one, one_mul, pow_one]

theorem const_add (a b : K) : add (const a : Vector K n) (const b) = const (a + b) := by
  ext i hi
  by_cases h : i = 0 <;> simp [add, const, h]

theorem const_zero : (const 0 : Vector K n) = zero := by
  ext i hi
  simp [const, zero]

/-- The reduction coefficients of `X ^ n - c`: `X ^ n = c`. -/
def binomial (c : K) : Fin n → K := fun i => if (i : ℕ) = 0 then c else 0

theorem root_pow_binomial (hn : 0 < n) (c : K) :
    AdjoinRoot.root (X ^ n - C c) ^ n =
      ∑ i : Fin n, AdjoinRoot.of (X ^ n - C c) (binomial c i) *
        AdjoinRoot.root (X ^ n - C c) ^ (i : ℕ) := by
  have h := AdjoinRoot.eval₂_root (X ^ n - C c)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  rw [h, Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj => by
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp [binomial, this]) (by simp)]
  simp [binomial]

/-! ## Bijectivity through the power basis -/

/-- The power basis `1, root f, …, root f ^ (n - 1)` of `AdjoinRoot f` over `K`, indexed by
`Fin n`. -/
noncomputable def basis (hf : f.Monic) (hd : f.natDegree = n) :
    Module.Basis (Fin n) K (AdjoinRoot f) :=
  (AdjoinRoot.powerBasis' hf).basis.reindex (finCongr (by rw [AdjoinRoot.powerBasis'_dim, hd]))

theorem basis_apply (hf : f.Monic) (hd : f.natDegree = n) (i : Fin n) :
    basis hf hd i = AdjoinRoot.root f ^ (i : ℕ) := by
  rw [basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

/-- `toSpec` is the inverse of the power-basis coordinate map, read through `coordsEquiv`. -/
theorem toSpec_eq_basis (hf : f.Monic) (hd : f.natDegree = n) (a : Vector K n) :
    toSpec f a = (basis hf hd).equivFun.symm (coordsEquiv a) := by
  rw [Module.Basis.equivFun_symm_apply, toSpec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basis_apply, coordsEquiv_apply, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem toSpec_bijective (hf : f.Monic) (hd : f.natDegree = n) :
    Function.Bijective (toSpec (n := n) f) := by
  have : toSpec (n := n) f = (basis hf hd).equivFun.symm ∘ coordsEquiv :=
    funext (toSpec_eq_basis hf hd)
  rw [this]
  exact (basis hf hd).equivFun.symm.bijective.comp coordsEquiv.bijective

/-- The coordinates of `toSpec f a` in the power basis are the entries of `a`. -/
theorem basis_repr_toSpec (hf : f.Monic) (hd : f.natDegree = n) (a : Vector K n) (i : Fin n) :
    (basis hf hd).repr (toSpec f a) i = a[i] := by
  rw [toSpec_eq_basis hf hd, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
    coordsEquiv_apply]

/-! ## The executable field -/

/-- The operations: coefficientwise addition, Horner multiplication modulo
`X ^ n - ∑ i, r i · X ^ i`, inverse by exponentiation to `card ^ n - 2`. -/
def ops (r : Fin n → K) (card : ℕ) : ExecOps (Vector K n) where
  zero := zero
  one := const 1
  add := add
  neg := neg
  mul := mul r
  inv a := powBySquaring (const 1) (mul r) a (card ^ n - 2)
  natCast m := const (m : K)

/-- **The facts that make `ops r card` a field**: `f` is monic irreducible of degree `n` with
`X ^ n = ∑ i, r i · X ^ i` modulo `f`, and `K` has `card` elements. A `Prop`, so the field
structure built from it depends computationally on `r` and `card` only. -/
structure Spec {K : Type} [Field K] (r : Fin n → K) (card : ℕ) (f : K[X]) : Prop where
  monic : f.Monic
  natDegree_eq : f.natDegree = n
  root_pow : AdjoinRoot.root f ^ n = ∑ i : Fin n, AdjoinRoot.of f (r i) * AdjoinRoot.root f ^ (i : ℕ)
  irreducible : Irreducible f
  natCard_eq : Nat.card K = card
  two_lt : 2 < card ^ n

namespace Spec

variable {K : Type} [Field K] {r : Fin n → K} {card : ℕ} {f : K[X]} (S : Spec r card f)

include S in
theorem n_pos : 0 < n := by
  rw [← S.natDegree_eq]
  exact Irreducible.natDegree_pos S.irreducible

include S in
theorem natCard_adjoinRoot : Nat.card (AdjoinRoot f) = card ^ n := by
  have : Module.Finite K (AdjoinRoot f) := S.monic.finite_adjoinRoot
  rw [Module.natCard_eq_pow_finrank (K := K), S.natCard_eq,
    Module.finrank_eq_card_basis (basis S.monic S.natDegree_eq), Fintype.card_fin]

include S in
theorem toSpec_one : toSpec f (const (1 : K) : Vector K n) = 1 := by
  rw [toSpec_const S.n_pos, map_one]

/-- `toSpec` as an `ExecOps.Hom` to `AdjoinRoot f`. -/
noncomputable def hom : letI := Fact.mk S.irreducible; (ops r card).Hom (AdjoinRoot f) :=
  letI := Fact.mk S.irreducible
  { toFun := toSpec f
    injective := (toSpec_bijective S.monic S.natDegree_eq).1
    map_zero := toSpec_zero
    map_one := S.toSpec_one
    map_add := toSpec_add
    map_neg := toSpec_neg
    map_mul := toSpec_mul S.root_pow
    map_inv := fun a => by
      have : Finite (AdjoinRoot f) := by
        have : Module.Finite K (AdjoinRoot f) := S.monic.finite_adjoinRoot
        have : Finite K := Nat.finite_of_card_ne_zero (by
          rw [S.natCard_eq]
          rintro rfl
          have := S.two_lt
          rw [zero_pow S.n_pos.ne'] at this
          omega)
        exact Module.finite_of_finite K
      change toSpec f (powBySquaring _ _ a _) = _
      rw [map_powBySquaring S.toSpec_one (toSpec_mul S.root_pow), inv_eq_pow_natCard_sub_two
        (by rw [S.natCard_adjoinRoot]; exact S.two_lt), S.natCard_adjoinRoot]
    map_natCast := fun m => by
      change toSpec f (const (m : K)) = _
      rw [toSpec_const S.n_pos, map_natCast] }

include S in
theorem isField : (ops r card).IsField :=
  letI := Fact.mk S.irreducible
  S.hom.isField

include S in
theorem const_mul (a b : K) : mul r (const a : Vector K n) (const b) = const (a * b) :=
  (toSpec_bijective S.monic S.natDegree_eq).1 (by
    rw [toSpec_mul S.root_pow, toSpec_const S.n_pos, toSpec_const S.n_pos, toSpec_const S.n_pos,
      map_mul])

end Spec

/-- The data of a binomial field `K[X] / (X ^ n - c)`. -/
theorem Spec.of_binomial {K : Type} [Field K] {c : K} {card : ℕ}
    (hirr : Irreducible (X ^ n - C c)) (hcard : Nat.card K = card) (hn : 2 ≤ n)
    (htwo : 2 < card ^ n) : Spec (binomial c : Fin n → K) card (X ^ n - C c) where
  monic := monic_X_pow_sub_C c (by omega)
  natDegree_eq := natDegree_X_pow_sub_C
  root_pow := root_pow_binomial (by omega) c
  irreducible := hirr
  natCard_eq := hcard
  two_lt := htwo

end GordieHowe.PolyRep
