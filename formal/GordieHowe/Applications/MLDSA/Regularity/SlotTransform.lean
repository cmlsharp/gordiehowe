-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Surrogate
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.Field.ZMod
public import GordieHowe.Applications.Params

@[expose] public section

/-!
# The slot (CRT) transform of `R_q`

`X^256 + 1` splits over `ZMod q` (`q = 8380417`) with roots `r_j = ζ^(2j+1)`, `ζ = 1753` a
primitive `512`-th root of unity (FIPS 204, Section 7.5, the NTT's `ζ`). Evaluation at a root
`r` with `r^256 = -1` is a ring homomorphism `R_q → ZMod q` (`slotEval_mul`, through the
semantic quotient `Z_q[X]/(X^256 + 1)` of the vendored `coeffSemantics`), and evaluation at all
`256` roots is a bijection (`slotVec_bijective`, a Vandermonde matrix).

This is the slot domain of the regularity argument: the matrix `A` acts slot by slot,
`slotEval r_j ((A y)_i) = ∑_b slotEval r_j (A_{ib}) · slotEval r_j (y_b)`.
-/

open Finset Polynomial
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA

instance instFactPrimeCoeffModulus : Fact (Nat.Prime _root_.MLDSA.modulus) := GordieHowe.instFactPrimeMlDsaQ


/-- Evaluation of a coefficient-domain polynomial at `r`: `∑_c f_c r^c`. -/
def slotEval (r : Coeff) (f : Rq) : Coeff :=
  ∑ c : Fin ringDegree, f.get c * r ^ (c : ℕ)

/-- Evaluation at `r` on the semantic quotient, for `r^256 = -1`. -/
noncomputable def quotientEval (r : Coeff) (hr : r ^ ringDegree = -1) :
    LatticeCrypto.NegacyclicQuotient Coeff ringDegree →+* Coeff :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom r) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [LatticeCrypto.negacyclicModulus, hr]

theorem quotientEval_quotientOfRq (r : Coeff) (hr : r ^ ringDegree = -1) (f : Rq) :
    quotientEval r hr (quotientOfRq f) = slotEval r f := by
  change quotientEval r hr (Ideal.Quotient.mk _ (polyBackend.toPolynomial f)) = _
  rw [quotientEval, Ideal.Quotient.lift_mk]
  simp only [LatticeCrypto.PolyBackend.toPolynomial, Polynomial.coe_evalRingHom,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, slotEval]
  rfl

section Hom

variable {r : Coeff} (hr : r ^ ringDegree = -1)
include hr

theorem slotEval_mul (f g : Rq) : slotEval r (f * g) = slotEval r f * slotEval r g := by
  rw [← quotientEval_quotientOfRq r hr, ← quotientEval_quotientOfRq r hr,
    ← quotientEval_quotientOfRq r hr, ← map_mul]
  exact congrArg (quotientEval r hr) (coeffSemantics.mul_sound f g)

theorem slotEval_add (f g : Rq) : slotEval r (f + g) = slotEval r f + slotEval r g := by
  rw [← quotientEval_quotientOfRq r hr, ← quotientEval_quotientOfRq r hr,
    ← quotientEval_quotientOfRq r hr, ← map_add]
  exact congrArg (quotientEval r hr) (coeffSemantics.add_sound f g)

theorem slotEval_zero : slotEval r 0 = 0 := by
  rw [← quotientEval_quotientOfRq r hr, ← map_zero (quotientEval r hr)]
  exact congrArg (quotientEval r hr) coeffSemantics.zero_sound

/-- Evaluation at a root of `X^256 + 1` as a ring homomorphism. -/
noncomputable def slotEvalHom : Rq →+* Coeff :=
  (quotientEval r hr).comp
    { toFun := quotientOfRq
      map_one' := coeffSemantics.one_sound
      map_mul' := coeffSemantics.mul_sound
      map_zero' := coeffSemantics.zero_sound
      map_add' := coeffSemantics.add_sound }

theorem slotEvalHom_apply (f : Rq) : slotEvalHom hr f = slotEval r f :=
  quotientEval_quotientOfRq r hr f

end Hom

/-! ### The roots `ζ^(2j+1)` -/

/-- `ζ = 1753`, a primitive `512`-th root of unity modulo `q` (FIPS 204, Section 7.5). -/
def zeta : Coeff := 1753

theorem zeta_pow_256 : zeta ^ 256 = -1 := by
  have h : ((1753 ^ 256 : ℕ) : Coeff) = ((8380416 : ℕ) : Coeff) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by norm_num [modulus])
  rw [zeta, show (1753 : Coeff) = ((1753 : ℕ) : Coeff) by norm_num, ← Nat.cast_pow, h]
  rw [show ((8380416 : ℕ) : Coeff) = ((modulus - 1 : ℕ) : Coeff) by norm_num [modulus],
    Nat.cast_sub (by norm_num [modulus]), ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem orderOf_zeta : orderOf zeta = 2 ^ 9 := by
  refine orderOf_eq_prime_pow (p := 2) (n := 8) ?_ ?_
  · rw [show (2 : ℕ) ^ 8 = 256 by norm_num, zeta_pow_256]
    decide
  · rw [show (2 : ℕ) ^ (8 + 1) = 256 * 2 by norm_num, pow_mul, zeta_pow_256]
    norm_num

/-- The slot roots `r_j = ζ^(2j+1)`, the roots of `X^256 + 1`. -/
def slotRoot (j : Fin ringDegree) : Coeff := zeta ^ (2 * (j : ℕ) + 1)

theorem slotRoot_pow (j : Fin ringDegree) : slotRoot j ^ ringDegree = -1 := by
  rw [slotRoot, ← pow_mul]
  show zeta ^ ((2 * (j : ℕ) + 1) * 256) = -1
  rw [show (2 * (j : ℕ) + 1) * 256 = 256 * (2 * j + 1) by ring, pow_mul,
    zeta_pow_256, Odd.neg_one_pow ⟨j, rfl⟩]

theorem slotRoot_injective : Function.Injective slotRoot := by
  intro j j' h
  simp only [slotRoot] at h
  have hz : IsUnit zeta := IsUnit.of_mul_eq_one (zeta ^ 511) (by
    rw [← pow_succ', show 511 + 1 = 256 * 2 by rfl, pow_mul, zeta_pow_256]; norm_num)
  have h' : hz.unit ^ (2 * (j : ℕ) + 1) = hz.unit ^ (2 * (j' : ℕ) + 1) := by
    ext; simpa using h
  have := (pow_inj_mod).mp h'
  rw [← orderOf_units, IsUnit.unit_spec, orderOf_zeta] at this
  have hj : (j : ℕ) < 256 := j.isLt
  have hj' : (j' : ℕ) < 256 := j'.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact Fin.ext (by omega)

theorem slotRoot_ne_zero (j : Fin ringDegree) : slotRoot j ≠ 0 := by
  intro h
  have := slotRoot_pow j
  rw [h, zero_pow (by decide)] at this
  exact absurd this (by decide)

/-- The slot vector of a polynomial: its values at the `256` roots of `X^256 + 1`. -/
def slotVec (f : Rq) : Fin ringDegree → Coeff := fun j => slotEval (slotRoot j) f

theorem slotVec_injective : Function.Injective slotVec := by
  intro f g h
  have hdet : (Matrix.vandermonde slotRoot).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr slotRoot_injective
  set d : Fin ringDegree → Coeff := fun c => f.get c - g.get c
  have hd : (Matrix.vandermonde slotRoot).mulVec d = 0 := by
    funext j
    have := congrFun h j
    simp only [slotVec, slotEval] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply, d, mul_sub,
      Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    simpa only [mul_comm] using this
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hd
  apply Vector.ext
  intro i hi
  have := congrFun h0 ⟨i, hi⟩
  simp only [d, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem slotVec_bijective : Function.Bijective slotVec := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨slotVec_injective, ?_⟩
  exact Fintype.card_congr (polyBackend.equivPi)

/-! ### Ring identities in `R_q` through the semantic quotient -/

theorem quotientOfRq_injective : Function.Injective quotientOfRq :=
  LatticeCrypto.NegacyclicQuotient.ofBackend_injective _

theorem rq_add_mul (f g h : Rq) : (f + g) * h = f * h + g * h := by
  apply quotientOfRq_injective
  have e1 : quotientOfRq ((f + g) * h) = (quotientOfRq f + quotientOfRq g) * quotientOfRq h := by
    rw [← coeffSemantics.add_sound]; exact coeffSemantics.mul_sound _ _
  have e2 : quotientOfRq (f * h + g * h) =
      quotientOfRq f * quotientOfRq h + quotientOfRq g * quotientOfRq h := by
    rw [← coeffSemantics.mul_sound, ← coeffSemantics.mul_sound]; exact coeffSemantics.add_sound _ _
  rw [e1, e2, add_mul]

theorem rq_zero_mul (f : Rq) : (0 : Rq) * f = 0 := by
  apply quotientOfRq_injective
  have e1 : quotientOfRq ((0 : Rq) * f) = quotientOfRq 0 * quotientOfRq f :=
    coeffSemantics.mul_sound _ _
  rw [e1, show quotientOfRq (0 : Rq) = 0 from coeffSemantics.zero_sound, zero_mul]

/-! ### The matrix product, coefficient domain and slot by slot -/

section MatVec

variable (ops : NTTRingOps)

/-- A transform-domain dot product is the finite sum of the entrywise products (as
`GordieHowe.MLDSA44.dot_eq_sum` for the concrete NTT). -/
theorem dot_eq_sum {k : ℕ} (row v : TqVec k) :
    ops.dot row v = ∑ j : Fin k, ops.mulHat (row.get j) (v.get j) := by
  unfold LatticeCrypto.TransformOps.dot
  have hz : Vector.zipWith ops.mulHat row v = Vector.ofFn fun j => ops.mulHat (row.get j) (v.get j) := by
    apply Vector.ext
    intro i hi
    simp [Vector.get]
  rw [hz, ← Vector.foldl_toList, Vector.toList_ofFn, ← List.sum_ofFn, List.sum_eq_foldl]

/-- **The matrix product in `R_q`**: `(Â · y)_i = ∑_b NTT⁻¹(Â_{ib}) · y_b`, under the transform
laws. -/
theorem coeffMatVecMul_get [hl : NTTRingLaws ops] {k l : ℕ} (aHat : TqMatrix k l) (y : RqVec l)
    (i : Fin k) :
    (ops.coeffMatVecMul aHat y).get i = ∑ b : Fin l, ops.fromHat ((aHat.get i).get b) * y.get b := by
  let F : Tq →+ Rq :=
    { toFun := ops.fromHat
      map_zero' := by rw [← hl.toHat_zero, hl.fromHat_toHat]; rfl
      map_add' := LatticeCrypto.TransformOps.fromHat_addHat ops }
  simp only [LatticeCrypto.TransformOps.coeffMatVecMul, LatticeCrypto.TransformOps.unhatVec_get,
    LatticeCrypto.TransformOps.matVecMul, Vector.get_map]
  rw [dot_eq_sum]
  change F _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  change ops.fromHat _ = _
  rw [LatticeCrypto.TransformOps.hatVec_get, ← hl.toHat_fromHat ((aHat.get i).get b),
    ← hl.toHat_mul, hl.fromHat_toHat, hl.fromHat_toHat]

end MatVec

end GordieHowe.MLDSA.Regularity
