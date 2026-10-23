-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.BitVec
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.AdjoinRoot
public import GordieHowe.Foundations.Fields.ExecField

@[expose] public section

/-!
# Bit-vector representation of a binary field

An element of `GF(2)[X] / (f)`, `f` monic of degree `w` with `X ^ w = tap` modulo `f` for a
polynomial `tap` of degree below `w`, is stored as a `BitVec w`, bit `i` the coefficient of
`X ^ i` (the layout of the C++ classes `GF2_128<>` and `GF2_256<>`). Addition is exclusive or;
multiplication is shift-and-add (Horner's rule on the bits of the second factor), multiplying the
accumulator by `X` with `timesX` (shift left, and add the bits of `tap` when bit `w - 1`
overflows); inversion is exponentiation to `2 ^ w - 2` (`inv_eq_pow_natCard_sub_two`).

`toSpec f` sends a bit vector to `∑ i, (bit i) · root f ^ i` in `AdjoinRoot f`; it preserves the
operations (`toSpec_xor`, `toSpec_mul`, …) and is injective (`toSpec_injective`, through the power
basis) and bijective (`toSpec_bijective`, by counting). `BinaryRep.Spec tap f` bundles the facts
that make `ops tap` a field; `Spec.hom` is the `ExecOps.Hom` to `AdjoinRoot f`.
-/

namespace GordieHowe.BinaryRep

open Polynomial

variable {w : ℕ}

/-! ## The operations -/

/-- Multiplication by `X`: shift left by one, adding `tap` (the reduction `X ^ w = tap`) when
bit `w - 1` overflows. -/
def timesX (tap r : BitVec w) : BitVec w :=
  if r.getLsbD (w - 1) then (r <<< 1) ^^^ tap else r <<< 1

/-- One step of Horner's rule for `mul tap a b`: multiply the accumulator `r` by `X`, then add
`a` if bit `i` of `b` is set. -/
def mulStep (tap a b : BitVec w) (i : ℕ) (r : BitVec w) : BitVec w :=
  if b.getLsbD i then timesX tap r ^^^ a else timesX tap r

/-- Carry-less multiplication modulo `X ^ w - tap`: Horner's rule on the bits of `b` from
`w - 1` down to `0`. -/
def mul (tap a b : BitVec w) : BitVec w :=
  (List.range w).foldr (mulStep tap a b) 0

/-- The operations: exclusive or, shift-and-add multiplication, inverse by exponentiation to
`2 ^ w - 2`; negation is the identity and a natural maps to its parity. -/
def ops (tap : BitVec w) : ExecOps (BitVec w) where
  zero := 0
  one := 1
  add a b := a ^^^ b
  neg a := a
  mul := mul tap
  inv a := powBySquaring 1 (mul tap) a (2 ^ w - 2)
  natCast m := if m % 2 = 1 then 1 else 0

/-- The bits of a bit vector as `GF(2)` coordinates, coordinate `i` the coefficient of `X ^ i`:
the bit vector is the little-endian integer `∑ i, c i · 2 ^ i`. -/
def coordsEquiv : BitVec w ≃ (Fin w → ZMod 2) :=
  (BitVec.equivFin (m := w)).toEquiv.trans finFunctionFinEquiv.symm

/-! ## The map to the specification -/

variable (f : (ZMod 2)[X])

/-- The element of `AdjoinRoot f` with power-basis coordinates the bits of `v`, bit `i` the
coefficient of `root f ^ i`. -/
noncomputable def toSpec (v : BitVec w) : AdjoinRoot f :=
  ∑ i : Fin w, if v.getLsbD i then AdjoinRoot.root f ^ (i : ℕ) else 0

variable {f}

theorem adjoinRoot_two_eq_zero : (2 : AdjoinRoot f) = 0 := by
  rw [← map_ofNat (AdjoinRoot.of f) 2, show (OfNat.ofNat 2 : ZMod 2) = 0 from rfl, map_zero]

theorem adjoinRoot_add_self (x : AdjoinRoot f) : x + x = 0 := by
  rw [← two_mul, adjoinRoot_two_eq_zero, zero_mul]

/-- A term selected by the exclusive or of two conditions is the sum of the terms selected by
each, in a ring where `x + x = 0`. -/
theorem ite_xor_eq_add_of_add_self {R : Type*} [Ring R] (h : ∀ x : R, x + x = 0) (p q : Bool)
    (x : R) : (if (p ^^ q) then x else 0) = (if p then x else 0) + (if q then x else 0) := by
  cases p <;> cases q <;> simp [h]

theorem toSpec_xor (a b : BitVec w) : toSpec f (a ^^^ b) = toSpec f a + toSpec f b := by
  simp only [toSpec, BitVec.getLsbD_xor, ite_xor_eq_add_of_add_self adjoinRoot_add_self,
    Finset.sum_add_distrib]

theorem toSpec_zero : toSpec f (0 : BitVec w) = 0 := by
  simp [toSpec]

theorem toSpec_twoPow {i : ℕ} (hi : i < w) :
    toSpec f (BitVec.twoPow w i) = AdjoinRoot.root f ^ i := by
  rw [toSpec, Finset.sum_eq_single_of_mem ⟨i, hi⟩ (Finset.mem_univ _)]
  · simp [hi]
  · intro j _ hj
    have hji : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
    simp [hji]

theorem toSpec_one (hw : 0 < w) : toSpec f (1 : BitVec w) = 1 := by
  rw [show (1 : BitVec w) = BitVec.twoPow w 0 from BitVec.twoPow_zero.symm, toSpec_twoPow hw,
    pow_zero]

theorem toSpec_two (hw : 1 < w) : toSpec f (2 : BitVec w) = AdjoinRoot.root f := by
  have h2 : (2 : BitVec w) = BitVec.twoPow w 1 := by
    refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
    rw [BitVec.getLsbD_twoPow, show (2 : BitVec w) = BitVec.ofNat w (2 ^ 1) from rfl,
      BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
    simp [hi, hw]
  rw [h2, toSpec_twoPow hw, pow_one]

/-- Shifting left by one multiplies by the root, except that the coefficient of `root ^ w` is
dropped. -/
theorem toSpec_shiftLeft_one (hw : 0 < w) (r : BitVec w) :
    toSpec f (r <<< 1) + (if r.getLsbD (w - 1) then AdjoinRoot.root f ^ w else 0) =
      AdjoinRoot.root f * toSpec f r := by
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  simp only [toSpec, Finset.mul_sum, mul_ite, mul_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (n := m)]
  simp only [BitVec.getLsbD_shiftLeft]
  simp [pow_succ']

theorem toSpec_timesX (hw : 0 < w) {tap : BitVec w}
    (hroot : AdjoinRoot.root f ^ w = toSpec f tap) (r : BitVec w) :
    toSpec f (timesX tap r) = AdjoinRoot.root f * toSpec f r := by
  rw [← toSpec_shiftLeft_one hw, timesX]
  split_ifs <;> simp [toSpec_xor, hroot]

theorem toSpec_mulStep (hw : 0 < w) {tap : BitVec w}
    (hroot : AdjoinRoot.root f ^ w = toSpec f tap) (a b : BitVec w) (i : ℕ) (r : BitVec w) :
    toSpec f (mulStep tap a b i r) =
      AdjoinRoot.root f * toSpec f r + if b.getLsbD i then toSpec f a else 0 := by
  rw [mulStep]
  split_ifs <;> simp [toSpec_xor, toSpec_timesX hw hroot]

/-- The Horner loop of `mul tap a b` over the bits `s, …, s + m - 1` of `b` multiplies `a` by
the polynomial with those bits as coefficients. -/
theorem toSpec_foldr_mulStep (hw : 0 < w) {tap : BitVec w}
    (hroot : AdjoinRoot.root f ^ w = toSpec f tap) (a b : BitVec w) (s m : ℕ) :
    toSpec f ((List.range' s m).foldr (mulStep tap a b) 0) =
      toSpec f a *
        ∑ j ∈ Finset.range m, if b.getLsbD (s + j) then AdjoinRoot.root f ^ j else 0 := by
  induction m generalizing s with
  | zero => simp [toSpec]
  | succ m ih =>
    rw [List.range'_succ, List.foldr_cons, toSpec_mulStep hw hroot, ih, Finset.sum_range_succ',
      mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show s + 1 + j = s + (j + 1) by omega]
      split_ifs <;> ring
    · rw [add_zero]
      split_ifs <;> simp

/-- `mul` is multiplication in `AdjoinRoot f`. -/
theorem toSpec_mul (hw : 0 < w) {tap : BitVec w}
    (hroot : AdjoinRoot.root f ^ w = toSpec f tap) (a b : BitVec w) :
    toSpec f (mul tap a b) = toSpec f a * toSpec f b := by
  rw [mul, List.range_eq_range', toSpec_foldr_mulStep hw hroot]
  simp only [zero_add, toSpec,
    Fin.sum_univ_eq_sum_range (fun j => if b.getLsbD j then AdjoinRoot.root f ^ j else 0)]

theorem toSpec_natCast (hw : 0 < w) (m : ℕ) :
    toSpec f (if m % 2 = 1 then (1 : BitVec w) else 0) = (m : AdjoinRoot f) := by
  rw [← map_natCast (AdjoinRoot.of f), ← ZMod.natCast_mod m 2]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · simp [h, toSpec]
  · simpa [h] using toSpec_one (f := f) hw

/-! ## Bijectivity -/

/-- The power basis `1, root f, …, root f ^ (w - 1)` of `AdjoinRoot f` over `GF(2)`, indexed by
`Fin w`. -/
noncomputable def basis (hf : f.Monic) (hd : f.natDegree = w) :
    Module.Basis (Fin w) (ZMod 2) (AdjoinRoot f) :=
  (AdjoinRoot.powerBasis' hf).basis.reindex (finCongr (by rw [AdjoinRoot.powerBasis'_dim, hd]))

theorem basis_apply (hf : f.Monic) (hd : f.natDegree = w) (i : Fin w) :
    basis hf hd i = AdjoinRoot.root f ^ (i : ℕ) := by
  rw [basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

/-- A sum of selected powers of the root is the element with those `0`/`1` power-basis
coordinates. -/
theorem sum_ite_eq_basis (hf : f.Monic) (hd : f.natDegree = w) (b : Fin w → Bool) :
    (∑ i : Fin w, if b i then AdjoinRoot.root f ^ (i : ℕ) else 0) =
      (basis hf hd).equivFun.symm (fun i => if b i then 1 else 0) := by
  rw [Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basis_apply]
  split_ifs <;> simp

/-- The sums of selected powers of the root determine the selection. -/
theorem sum_ite_injective (hf : f.Monic) (hd : f.natDegree = w) {b b' : Fin w → Bool}
    (h : (∑ i : Fin w, if b i then AdjoinRoot.root f ^ (i : ℕ) else 0) =
      ∑ i : Fin w, if b' i then AdjoinRoot.root f ^ (i : ℕ) else 0) : b = b' := by
  rw [sum_ite_eq_basis hf hd, sum_ite_eq_basis hf hd] at h
  have h' := (basis hf hd).equivFun.symm.injective h
  funext i
  have := congrFun h' i
  revert this
  cases b i <;> cases b' i <;> simp

theorem toSpec_injective (hf : f.Monic) (hd : f.natDegree = w) :
    Function.Injective (toSpec (w := w) f) := fun a b h =>
  BitVec.eq_of_getLsbD_eq fun i hi =>
    congrFun (sum_ite_injective hf hd (b := fun i : Fin w => a.getLsbD i)
      (b' := fun i : Fin w => b.getLsbD i) h) ⟨i, hi⟩

theorem natCard_adjoinRoot (hf : f.Monic) (hd : f.natDegree = w) :
    Nat.card (AdjoinRoot f) = 2 ^ w := by
  have : Module.Finite (ZMod 2) (AdjoinRoot f) := hf.finite_adjoinRoot
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Module.finrank_eq_card_basis (basis hf hd), Fintype.card_fin]

theorem toSpec_bijective (hf : f.Monic) (hd : f.natDegree = w) :
    Function.Bijective (toSpec (w := w) f) := by
  have : Module.Finite (ZMod 2) (AdjoinRoot f) := hf.finite_adjoinRoot
  have : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod 2)
  refine (toSpec_injective hf hd).bijective_of_nat_card_le ?_
  rw [natCard_adjoinRoot hf hd, Nat.card_congr BitVec.equivFin.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-! ## The executable field -/

/-- **The facts that make `ops tap` a field**: `f` is monic irreducible of degree `w ≥ 2` with
`root f ^ w = toSpec f tap`. A `Prop`, so the field structure built from it depends
computationally on `tap` only. -/
structure Spec (tap : BitVec w) (f : (ZMod 2)[X]) : Prop where
  monic : f.Monic
  natDegree_eq : f.natDegree = w
  root_pow : AdjoinRoot.root f ^ w = toSpec f tap
  irreducible : Irreducible f
  two_le : 2 ≤ w

namespace Spec

variable {tap : BitVec w} (S : Spec tap f)

include S in
theorem w_pos : 0 < w := by have := S.two_le; omega

/-- `toSpec` as an `ExecOps.Hom` to `AdjoinRoot f`. -/
noncomputable def hom : letI := Fact.mk S.irreducible; (ops tap).Hom (AdjoinRoot f) :=
  letI := Fact.mk S.irreducible
  { toFun := toSpec f
    injective := toSpec_injective S.monic S.natDegree_eq
    map_zero := toSpec_zero
    map_one := toSpec_one S.w_pos
    map_add := toSpec_xor
    map_neg := fun a => by
      change toSpec f a = -toSpec f a
      rw [eq_neg_iff_add_eq_zero, adjoinRoot_add_self]
    map_mul := toSpec_mul S.w_pos S.root_pow
    map_inv := fun a => by
      have : Module.Finite (ZMod 2) (AdjoinRoot f) := S.monic.finite_adjoinRoot
      have : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod 2)
      have hcard := natCard_adjoinRoot S.monic S.natDegree_eq
      change toSpec f (powBySquaring _ _ a _) = _
      rw [map_powBySquaring (toSpec_one S.w_pos) (toSpec_mul S.w_pos S.root_pow),
        inv_eq_pow_natCard_sub_two (by
          rw [hcard]
          calc 2 < 2 ^ 2 := by norm_num
            _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) S.two_le), hcard]
    map_natCast := toSpec_natCast S.w_pos }

include S in
theorem isField : (ops tap).IsField :=
  letI := Fact.mk S.irreducible
  S.hom.isField

end Spec

end GordieHowe.BinaryRep
