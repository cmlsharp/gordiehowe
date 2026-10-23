-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Two
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Tactic.ComputeDegree
public import GordieHowe.Foundations.Algebra.FrobeniusOrder
public import Mathlib.Algebra.Algebra.ZMod
public import GordieHowe.Foundations.Fields.BinarySpread
public import GordieHowe.Foundations.Fields.GF2_128
public import GordieHowe.Language.Realizations.MAC
public import GordieHowe.Foundations.ToMathlib.Rabin

@[expose] public section

/-!
# The concrete field `GF(2²⁵⁶)`

The specification `GF2_256Spec` is `GF(2)[X] / (f)` for the reduction polynomial of the C++ class
`GF2_256<>` (`lib/gf2k/gf2_256.h` on `main`, commit `783b08e`):

* `f = X²⁵⁶ + X¹⁰ + X⁵ + X² + 1`: `lib/gf2k/sysdep256.h:6`,
  "`GF(2)[X]/(X^256 + X^10 + X^5 + X^2 + 1)`. Little-endian coefficients."; the reduction constant
  `_mm_set_epi64x(0, 0x425)` (`0x425` = bits `10, 5, 2, 0`) at `lib/gf2k/sysdep256.h:62`; the
  inverse of `x`, `x^{-1} = x^255 + x^9 + x^4 + x` (`lib/gf2k/gf2_256.h:111-113`), and the mask
  `0x212` in `byinvx` (`lib/gf2k/gf2_256.h:363-370`) are the same polynomial divided by `x`.
* The element with bit `i` of its `uint64_t[4]` limbs set is `x^i`
  (`operator[]`, `lib/gf2k/gf2_256.h:93-96`); `kx_ = of_scalar_field(0b10)`
  (`lib/gf2k/gf2_256.h:109`) is `x`.

`GF2_256` is the executable field: an element is a `BitVec 256` in that layout, with the
operations of `GordieHowe.Foundations.Fields.BinaryRep` for the reduction bits `0x425`, and `gf2_256ToSpec` is the
polynomial-basis isomorphism with `GF2_256Spec`. The polynomial basis `e i := x ^ i` and the bit
coordinates give the `MACBasis 256`.

Irreducibility is Rabin's test (`Polynomial.irreducible_of_root_pow_card_pow`):
`256 = 2⁸`, so it needs `root ^ 2²⁵⁶ = root` and a unit `root ^ 2¹²⁸ - root`, witnessed
by an explicit inverse. The three identities are checked by `decide +kernel` on the
spread representation of `GordieHowe.Foundations.Fields.BinarySpread` (`gf2_256Exec`, digits of `16` bits):
256 + 128 squarings and one product, about `0.2 s` of kernel time.
-/

namespace GordieHowe

open Polynomial BinarySpread

/-- The reduction polynomial `X²⁵⁶ + X¹⁰ + X⁵ + X² + 1` (`lib/gf2k/sysdep256.h:6`). -/
noncomputable def gf2_256Poly : Polynomial (ZMod 2) := X ^ 256 + X ^ 10 + X ^ 5 + X ^ 2 + 1

theorem gf2_256Poly_monic : gf2_256Poly.Monic := by unfold gf2_256Poly; monicity!

theorem gf2_256Poly_natDegree : gf2_256Poly.natDegree = 256 := by
  unfold gf2_256Poly; compute_degree!

/-- The specification `GF(2)[X] / (X²⁵⁶ + X¹⁰ + X⁵ + X² + 1)`. Its `Field` instance follows
`gf2_256Poly_irreducible`. -/
abbrev GF2_256Spec : Type := AdjoinRoot gf2_256Poly

instance : CharP GF2_256Spec 2 :=
  charP_of_injective_algebraMap (AdjoinRoot.coe_injective (f := gf2_256Poly)
    (natDegree_pos_iff_degree_pos.mp (by rw [gf2_256Poly_natDegree]; norm_num)).ne') 2

/-- The reduction rule `X²⁵⁶ = X¹⁰ + X⁵ + X² + 1` in the specification. -/
theorem gf2_256Spec_root_pow_256 :
    AdjoinRoot.root gf2_256Poly ^ 256 =
      AdjoinRoot.root gf2_256Poly ^ 10 + AdjoinRoot.root gf2_256Poly ^ 5 +
        AdjoinRoot.root gf2_256Poly ^ 2 + 1 := by
  have h := AdjoinRoot.aeval_eq (f := gf2_256Poly) gf2_256Poly
  rw [AdjoinRoot.mk_self] at h
  conv at h =>
    enter [1, 2]
    unfold gf2_256Poly
  simp only [map_add, map_pow, aeval_X, map_one] at h
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  linear_combination h

/-! ## The spread representation -/

set_option exponentiation.threshold 4096 in
/-- The executable parameters of `GF2_256` for `GordieHowe.BinarySpread`: digits of `16` bits,
degree `256`, the tap natural of `X¹⁰ + X⁵ + X² + 1` and the parity mask. -/
def gf2_256Exec : Exec where
  k := 16
  n := 256
  tapN := 1 + 2 ^ 32 + 2 ^ 80 + 2 ^ 160
  mask := (2 ^ 4096 - 1) / (2 ^ 16 - 1)

/-- The low part `X¹⁰ + X⁵ + X² + 1` of the reduction polynomial over `ℕ`. -/
noncomputable def gf2_256Tap : ℕ[X] := X ^ 10 + X ^ 5 + X ^ 2 + 1

theorem gf2_256Tap_coeff (i : ℕ) :
    gf2_256Tap.coeff i = if i = 10 ∨ i = 5 ∨ i = 2 ∨ i = 0 then 1 else 0 := by
  simp only [gf2_256Tap, coeff_add, coeff_X_pow, coeff_one]
  split_ifs <;> omega

theorem gf2_256Exec_mask : gf2_256Exec.mask = Nat.ones 16 256 := by decide +kernel

/-- The facts tying `gf2_256Exec` to `gf2_256Poly`. -/
noncomputable def gf2_256Rep : Rep gf2_256Exec gf2_256Poly where
  tap := gf2_256Tap
  d := 11
  two_le_k := by decide
  tap_bounded := ⟨fun i => by rw [gf2_256Tap_coeff]; split_ifs <;> norm_num,
    fun i hi => by rw [gf2_256Tap_coeff, ite_eq_right (by omega)]⟩
  tapN_eq := by simp only [gf2_256Tap, gf2_256Exec, eval_add, eval_pow, eval_X, eval_one]; norm_num
  mask_eq := gf2_256Exec_mask
  root_pow := by
    simp only [toAdjoin, gf2_256Tap, RingHom.comp_apply, coe_mapRingHom, map_X, map_add, map_pow,
      AdjoinRoot.mk_X, map_one]
    exact gf2_256Spec_root_pow_256
  natDegree_eq := gf2_256Poly_natDegree
  n_pos := by simp only [gf2_256Exec]; norm_num
  deg_le := by simp only [gf2_256Exec]; norm_num
  coeff_le := by simp only [gf2_256Exec]; norm_num

theorem gf2_256SpecVal_ofBits_two :
    val gf2_256Exec gf2_256Poly (gf2_256Exec.ofBits 2) = AdjoinRoot.root gf2_256Poly := by
  rw [gf2_256Rep.val_ofBits]
  simpa using bitsVal_two_pow (f := gf2_256Poly) (n := gf2_256Exec.n) (j := 1) (by decide)

theorem gf2_256SpecVal_ofBits_one : val gf2_256Exec gf2_256Poly (gf2_256Exec.ofBits 1) = 1 := by
  rw [gf2_256Rep.val_ofBits]
  simpa using bitsVal_two_pow (f := gf2_256Poly) (n := gf2_256Exec.n) (j := 0) (by decide)

/-! ## Irreducibility certificate -/

/-- `X^(2¹²⁸)` reduced modulo `gf2_256Poly`, as bits. -/
def gf2_256X128 : ℕ := 0x2220d78c13d87c2ffc1c5bd25e53444bc74da1980d2519c9d41f22f67f2f9863

/-- The inverse of `X^(2¹²⁸) - X` modulo `gf2_256Poly`, as bits. Computed offline as
`(X^(2¹²⁸) - X)^(2²⁵⁶ - 2)`; `gf2_256X128SubXInv_mul` checks it. -/
def gf2_256X128SubXInv : ℕ := 0x41d07da235f08b92d026035887191e2fd91148129c622b9bd3caaa61ed5af509

theorem gf2_256_sqPow_128_two :
    gf2_256Exec.sqPow 128 (gf2_256Exec.ofBits 2) = gf2_256Exec.ofBits gf2_256X128 := by
  decide +kernel

theorem gf2_256_sqPow_128_X128 :
    gf2_256Exec.sqPow 128 (gf2_256Exec.ofBits gf2_256X128) = gf2_256Exec.ofBits 2 := by
  decide +kernel

theorem gf2_256X128SubXInv_mul :
    gf2_256Exec.mul (gf2_256Exec.ofBits gf2_256X128SubXInv)
      (gf2_256Exec.add (gf2_256Exec.ofBits gf2_256X128) (gf2_256Exec.ofBits 2)) =
      gf2_256Exec.ofBits 1 := by
  decide +kernel

theorem gf2_256Spec_root_pow_two_pow_128 :
    AdjoinRoot.root gf2_256Poly ^ 2 ^ 128 =
      val gf2_256Exec gf2_256Poly (gf2_256Exec.ofBits gf2_256X128) := by
  rw [← gf2_256SpecVal_ofBits_two, ← gf2_256Rep.val_sqPow (Rep.canon_ofBits _),
    gf2_256_sqPow_128_two]

/-- Irreducibility of the reduction polynomial, by Rabin's test: `256`'s only prime factor
is `2`, so the test needs `root ^ 2²⁵⁶ = root` and a unit `root ^ 2¹²⁸ - root`. -/
theorem gf2_256Poly_irreducible : Irreducible gf2_256Poly := by
  refine irreducible_of_root_pow_card_pow gf2_256Poly_natDegree (by norm_num) ?_ ?_
  · rw [Nat.card_zmod, show 2 ^ 256 = 2 ^ 128 * 2 ^ 128 by norm_num, pow_mul,
      gf2_256Spec_root_pow_two_pow_128, ← gf2_256Rep.val_sqPow (Rep.canon_ofBits _),
      gf2_256_sqPow_128_X128, gf2_256SpecVal_ofBits_two]
  · rw [show 256 = 2 ^ 8 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
    intro r hr
    rw [Finset.mem_singleton.mp hr, Nat.card_zmod, show 2 ^ 8 / 2 = 128 by norm_num,
      gf2_256Spec_root_pow_two_pow_128, ← gf2_256SpecVal_ofBits_two, CharTwo.sub_eq_add,
      ← gf2_256Rep.val_add (Rep.canon_ofBits _) (Rep.canon_ofBits _)]
    refine IsUnit.of_mul_eq_one_right
      (val gf2_256Exec gf2_256Poly (gf2_256Exec.ofBits gf2_256X128SubXInv)) ?_
    rw [← gf2_256Rep.val_mul (Rep.canon_ofBits _)
        (gf2_256Rep.canon_add (Rep.canon_ofBits _) (Rep.canon_ofBits _)),
      gf2_256X128SubXInv_mul, gf2_256SpecVal_ofBits_one]

instance instFactIrreducibleGf2_256Poly : Fact (Irreducible gf2_256Poly) :=
  ⟨gf2_256Poly_irreducible⟩

noncomputable instance : Field GF2_256Spec := AdjoinRoot.instField

/-- `0x425` holds the low bits `X¹⁰ + X⁵ + X² + 1` of the reduction polynomial, which equal
`X²⁵⁶`. -/
theorem gf2_256Spec_root_pow_256_eq_toSpec :
    AdjoinRoot.root gf2_256Poly ^ 256 = BinaryRep.toSpec gf2_256Poly 0x425#256 := by
  rw [show 0x425#256 = BitVec.twoPow 256 10 ^^^ BitVec.twoPow 256 5 ^^^ BitVec.twoPow 256 2 ^^^
      BitVec.twoPow 256 0 by decide]
  rw [BinaryRep.toSpec_xor, BinaryRep.toSpec_xor, BinaryRep.toSpec_xor,
    BinaryRep.toSpec_twoPow (by norm_num), BinaryRep.toSpec_twoPow (by norm_num),
    BinaryRep.toSpec_twoPow (by norm_num), BinaryRep.toSpec_twoPow (by norm_num),
    pow_zero, gf2_256Spec_root_pow_256]

/-- The facts that make the bit-vector operations with reduction bits `0x425` a field. -/
theorem gf2_256_binarySpec : BinaryRep.Spec 0x425#256 gf2_256Poly where
  monic := gf2_256Poly_monic
  natDegree_eq := gf2_256Poly_natDegree
  root_pow := gf2_256Spec_root_pow_256_eq_toSpec
  irreducible := gf2_256Poly_irreducible
  two_le := by norm_num

/-! ## The executable field -/

/-- `GF(2²⁵⁶)`: a `BitVec 256`, bit `i` the coefficient of `X^i` (the limbs of the C++
`GF2_256<>`), with the operations of `GordieHowe.Foundations.Fields.BinaryRep` for the reduction bits `0x425`. -/
def GF2_256 : Type := BitVec 256

/-- The operations of `GF2_256`, typed on `GF2_256`. -/
abbrev gf2_256Ops : ExecOps GF2_256 := BinaryRep.ops 0x425#256

instance : Field GF2_256 := gf2_256Ops.field gf2_256_binarySpec.isField

instance : DecidableEq GF2_256 := inferInstanceAs (DecidableEq (BitVec 256))

instance : Fintype GF2_256 :=
  Fintype.ofEquiv (Fin (2 ^ 256)) (BitVec.equivFin (m := 256)).symm.toEquiv

instance : Repr GF2_256 := inferInstanceAs (Repr (BitVec 256))

/-- The coordinates of an element: its bits, coordinate `i` the coefficient of `X ^ i`. -/
def gf2_256Coords : GF2_256 ≃ (Fin 256 → ZMod 2) := BinaryRep.coordsEquiv

/-- The element with polynomial-basis coordinates the `256` low bits of `v`. -/
def gf2_256OfNat (v : ℕ) : GF2_256 := BitVec.ofNat 256 v

theorem gf2_256OfNat_one : gf2_256OfNat 1 = 1 :=
  (ExecOps.field_one gf2_256Ops gf2_256_binarySpec.isField).symm

/-- The polynomial variable `x` (`kx_ = of_scalar_field(0b10)`, `lib/gf2k/gf2_256.h:109`). -/
def gf2_256Root : GF2_256 := gf2_256OfNat 2

/-- The polynomial-basis map as a ring isomorphism. -/
noncomputable def gf2_256RingEquiv : GF2_256 ≃+* GF2_256Spec :=
  gf2_256_binarySpec.hom.ringEquiv
    (BinaryRep.toSpec_bijective gf2_256Poly_monic gf2_256Poly_natDegree).2

instance : CharP GF2_256 2 :=
  charP_of_injective_ringHom (f := gf2_256RingEquiv.symm.toRingHom) (RingEquiv.injective _) 2

instance : Algebra (ZMod 2) GF2_256 := ZMod.algebra _ 2

/-- **The polynomial-basis map** `GF2_256 ≃ₐ[ZMod 2] GF2_256Spec`, bit `i` to the coefficient
of `root ^ i` (`BinaryRep.toSpec`). -/
noncomputable def gf2_256ToSpec : GF2_256 ≃ₐ[ZMod 2] GF2_256Spec :=
  AlgEquiv.ofRingEquiv (f := gf2_256RingEquiv) fun x => by
    have := RingHom.congr_fun (Subsingleton.elim (gf2_256RingEquiv.toRingHom.comp
      (algebraMap (ZMod 2) GF2_256)) (algebraMap (ZMod 2) GF2_256Spec)) x
    exact this

theorem gf2_256ToSpec_apply (x : GF2_256) :
    gf2_256ToSpec x = BinaryRep.toSpec gf2_256Poly (w := 256) x := rfl

theorem gf2_256ToSpec_root : gf2_256ToSpec gf2_256Root = AdjoinRoot.root gf2_256Poly := by
  rw [gf2_256ToSpec_apply]
  exact BinaryRep.toSpec_two (by norm_num)

/-- The reduction rule `x²⁵⁶ = x¹⁰ + x⁵ + x² + 1`. -/
theorem gf2_256_root_pow_256 :
    gf2_256Root ^ 256 = gf2_256Root ^ 10 + gf2_256Root ^ 5 + gf2_256Root ^ 2 + 1 :=
  gf2_256ToSpec.injective (by simp only [map_add, map_pow, map_one, gf2_256ToSpec_root,
    gf2_256Spec_root_pow_256])

/-! ## The spread representation read in `GF2_256` (`BinarySpread.valVia`) -/

theorem gf2_256Val_ofBits (v : ℕ) : valVia gf2_256RingEquiv gf2_256Exec (gf2_256Exec.ofBits v) = gf2_256OfNat v := by
  rw [gf2_256Rep.valVia_ofBits, RingEquiv.symm_apply_eq]
  exact (toSpec_ofNat 256 v).symm

theorem gf2_256Val_ofBits_two : valVia gf2_256RingEquiv gf2_256Exec (gf2_256Exec.ofBits 2) = gf2_256Root :=
  gf2_256Val_ofBits 2

/-- A kernel-checked inequality of spread naturals is an inequality in `GF2_256`. -/
theorem gf2_256Val_ne {a b : ℕ} (ha : Canon gf2_256Exec a) (hb : Canon gf2_256Exec b) (h : a ≠ b) :
    valVia gf2_256RingEquiv gf2_256Exec a ≠ valVia gf2_256RingEquiv gf2_256Exec b :=
  fun hv => h (gf2_256Rep.valVia_injective gf2_256RingEquiv ha hb hv)

/-! ## The polynomial basis, cardinality and Frobenius order -/

/-- The polynomial basis element `x^i`. -/
def gf2_256E (i : Fin 256) : GF2_256 := gf2_256Root ^ (i : ℕ)

/-- Coordinates of `x` in the polynomial basis: its bits. -/
def gf2_256Unpack (x : GF2_256) (i : Fin 256) : Bool := BitVec.getLsbD (w := 256) x i

theorem gf2_256ToSpec_sum_ite (b : Fin 256 → Bool) :
    gf2_256ToSpec (∑ i, if b i then gf2_256E i else 0) =
      ∑ i : Fin 256, if b i then AdjoinRoot.root gf2_256Poly ^ (i : ℕ) else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [gf2_256E, gf2_256ToSpec_root]

theorem gf2_256_pack_unpack (x : GF2_256) :
    (∑ i, if gf2_256Unpack x i then gf2_256E i else 0) = x :=
  gf2_256ToSpec.injective (by rw [gf2_256ToSpec_sum_ite, gf2_256ToSpec_apply]; rfl)

theorem gf2_256_pack_injective (b b' : Fin 256 → Bool)
    (h : (∑ i, if b i then gf2_256E i else 0) = (∑ i, if b' i then gf2_256E i else 0)) :
    b = b' := by
  have h' := congrArg gf2_256ToSpec h
  rw [gf2_256ToSpec_sum_ite, gf2_256ToSpec_sum_ite] at h'
  exact BinaryRep.sum_ite_injective gf2_256Poly_monic gf2_256Poly_natDegree h'

/-- The polynomial basis of `GF(2²⁵⁶)` as a `MACBasis 256`: the packing of the 256-bit MAC
chunks (`xp[i] = x^i`, `lib/gordiehowe/compiler/mac.h:335-338`). -/
def gf2_256MACBasis : MACBasis 256 GF2_256 where
  e := gf2_256E
  unpack := gf2_256Unpack
  pack_unpack := gf2_256_pack_unpack
  pack_injective := gf2_256_pack_injective

instance : Module.Finite (ZMod 2) GF2_256 :=
  have : Module.Finite (ZMod 2) GF2_256Spec := gf2_256Poly_monic.finite_adjoinRoot
  Module.Finite.equiv gf2_256ToSpec.symm.toLinearEquiv

theorem gf2_256_card : Fintype.card GF2_256 = 2 ^ 256 :=
  (Fintype.ofEquiv_card _).trans (Fintype.card_fin _)

/-- `GF2_256` has Frobenius order `256`: every element is fixed by the `2²⁵⁶`-power map. -/
instance : FrobeniusOrder GF2_256 256 :=
  .of_card gf2_256_card (by norm_num)

end GordieHowe
