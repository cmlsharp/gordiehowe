-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.BitVec
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Tactic.ComputeDegree
public import GordieHowe.Foundations.Fields.BinaryRep
public import GordieHowe.Foundations.Fields.BinarySpread
public import GordieHowe.Foundations.Fields.GF2_128Exec
public import GordieHowe.Language.Realizations.MAC
public import GordieHowe.Foundations.ToMathlib.Rabin

@[expose] public section

/-!
# The concrete field `GF(2¹²⁸)`

The specification is `GF2_128Spec := GF(2)[X] / (f)` for the reduction polynomial
`f := X¹²⁸ + X⁷ + X² + X + 1`, built as `AdjoinRoot f`.

`GF2_128` is the executable field: an element is a `BitVec 128`, bit `i` the coefficient of
`X^i` (the layout of the C++ class `GF2_128<>`), with exclusive or as addition, the
shift-and-add `GF2_128Exec.gfMul` as multiplication and inversion by exponentiation
(`GordieHowe.Foundations.Fields.BinaryRep`). Its `Field` instance is pulled back along the polynomial-basis map
`BinaryRep.toSpec f`, which carries `^^^` to `+` and `gfMul` to `*`; `gf2_128ToSpec` is that map
as an isomorphism of `ZMod 2`-algebras. `gf2_128OfBitVec` reads a `BitVec 128` as an element (the
identity of carriers), so an identity in `GF2_128` between elements given by bits is checked by
kernel evaluation, through the spread representation `gf2_128Exec`
(`gf2_128OfBitVec_eq_valVia`).

Irreducibility of `f` is proved by Rabin's test (`Polynomial.irreducible_of_root_pow_card_pow`):
`root ^ 2^128 = root`, and `root ^ 2^64 - root` is a unit, witnessed by an explicit inverse. Both
are `gfMul` computations, checked by `decide +kernel` in the spread representation of
`GordieHowe.Foundations.Fields.BinarySpread` (`gf2_128Exec`), where one multiplication is one `Nat.mul`
(`sqPow_eq_of_spread`, `gfMul_eq_of_spread`; `gfPow_eq_of_spread` and `gfPow_ne_of_spread` serve the
certificates of the files that import this one).

The polynomial basis `gf2_128E i := x ^ i` and the bit coordinates `gf2_128Unpack` give the
`Basis128 GF2_128` instance that `GordieHowe.MAC.pack` and `GordieHowe.Conv` need.
-/

namespace GordieHowe

open Polynomial GF2_128Exec

instance instFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The reduction polynomial `X¹²⁸ + X⁷ + X² + X + 1`. -/
noncomputable def gf2_128Poly : Polynomial (ZMod 2) := X ^ 128 + X ^ 7 + X ^ 2 + X + 1

theorem gf2_128Poly_monic : gf2_128Poly.Monic := by unfold gf2_128Poly; monicity!

theorem gf2_128Poly_natDegree : gf2_128Poly.natDegree = 128 := by
  unfold gf2_128Poly; compute_degree!

/-! ## The specification -/

/-- The specification `GF(2)[X] / (X¹²⁸ + X⁷ + X² + X + 1)`. Its `Field` instance follows
`gf2_128Poly_irreducible`; everything before that uses only the ring. -/
abbrev GF2_128Spec : Type := AdjoinRoot gf2_128Poly

instance : CharP GF2_128Spec 2 :=
  charP_of_injective_algebraMap (AdjoinRoot.coe_injective (f := gf2_128Poly)
    (natDegree_pos_iff_degree_pos.mp (by rw [gf2_128Poly_natDegree]; norm_num)).ne') 2

/-- The reduction rule `X¹²⁸ = X⁷ + X² + X + 1` in the specification. -/
theorem gf2_128Spec_root_pow_128 :
    AdjoinRoot.root gf2_128Poly ^ 128 =
      AdjoinRoot.root gf2_128Poly ^ 7 + AdjoinRoot.root gf2_128Poly ^ 2 +
        AdjoinRoot.root gf2_128Poly + 1 := by
  have h := AdjoinRoot.aeval_eq (f := gf2_128Poly) gf2_128Poly
  rw [AdjoinRoot.mk_self] at h
  conv at h =>
    enter [1, 2]
    unfold gf2_128Poly
  simp only [map_add, map_pow, aeval_X, map_one] at h
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  linear_combination h

/-- `0x87` holds the low bits `X⁷ + X² + X + 1` of the reduction polynomial, which equal
`X¹²⁸`. -/
theorem gf2_128Spec_root_pow_128_eq_toSpec :
    AdjoinRoot.root gf2_128Poly ^ 128 = BinaryRep.toSpec gf2_128Poly 0x87#128 := by
  rw [show 0x87#128 = BitVec.twoPow 128 7 ^^^ BitVec.twoPow 128 2 ^^^ BitVec.twoPow 128 1 ^^^
      BitVec.twoPow 128 0 by decide]
  rw [BinaryRep.toSpec_xor, BinaryRep.toSpec_xor, BinaryRep.toSpec_xor,
    BinaryRep.toSpec_twoPow (by norm_num), BinaryRep.toSpec_twoPow (by norm_num),
    BinaryRep.toSpec_twoPow (by norm_num), BinaryRep.toSpec_twoPow (by norm_num),
    pow_one, pow_zero, gf2_128Spec_root_pow_128]

/-- `gfMul` is multiplication in the specification. -/
theorem gf2_128Spec_toSpec_gfMul (a b : BitVec 128) :
    BinaryRep.toSpec gf2_128Poly (gfMul a b) =
      BinaryRep.toSpec gf2_128Poly a * BinaryRep.toSpec gf2_128Poly b :=
  BinaryRep.toSpec_mul (by norm_num) gf2_128Spec_root_pow_128_eq_toSpec a b

theorem gf2_128Spec_toSpec_sqPow (n : ℕ) (r : BitVec 128) :
    BinaryRep.toSpec gf2_128Poly (sqPow n r) = BinaryRep.toSpec gf2_128Poly r ^ 2 ^ n := by
  induction n generalizing r with
  | zero => simp [sqPow]
  | succ n ih => rw [sqPow, ih, gf2_128Spec_toSpec_gfMul, ← sq, ← pow_mul, pow_succ']

/-! ## The spread representation

The certificates about concrete elements are checked in the spread representation of
`GordieHowe.Foundations.Fields.BinarySpread` (`gf2_128Exec`, digits of `16` bits), where one multiplication is one
`Nat.mul`, instead of by the bit-serial `gfMul`. `gf2_128Val_ofBits_toNat` reads the spread
natural of the bits of a `BitVec 128` as the element `BinaryRep.toSpec` gives it. -/

section Spread

open BinarySpread

set_option exponentiation.threshold 2048 in
/-- The executable parameters of `GF2_128` for `GordieHowe.BinarySpread`: digits of `16` bits,
degree `128`, the tap natural of `X⁷ + X² + X + 1` and the parity mask. -/
def gf2_128Exec : Exec where
  k := 16
  n := 128
  tapN := 1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 112
  mask := (2 ^ 2048 - 1) / (2 ^ 16 - 1)

/-- The low part `X⁷ + X² + X + 1` of the reduction polynomial over `ℕ`. -/
noncomputable def gf2_128Tap : ℕ[X] := X ^ 7 + X ^ 2 + X + 1

theorem gf2_128Tap_coeff (i : ℕ) :
    gf2_128Tap.coeff i = if i = 7 ∨ i = 2 ∨ i = 1 ∨ i = 0 then 1 else 0 := by
  simp only [gf2_128Tap, coeff_add, coeff_X_pow, coeff_X, coeff_one]
  split_ifs <;> omega

theorem gf2_128Exec_mask : gf2_128Exec.mask = Nat.ones 16 128 := by decide +kernel

/-- The facts tying `gf2_128Exec` to `gf2_128Poly`. -/
noncomputable def gf2_128Rep : Rep gf2_128Exec gf2_128Poly where
  tap := gf2_128Tap
  d := 8
  two_le_k := by decide
  tap_bounded := ⟨fun i => by rw [gf2_128Tap_coeff]; split_ifs <;> norm_num,
    fun i hi => by rw [gf2_128Tap_coeff, ite_eq_right (by omega)]⟩
  tapN_eq := by simp only [gf2_128Tap, gf2_128Exec, eval_add, eval_pow, eval_X, eval_one]; norm_num
  mask_eq := gf2_128Exec_mask
  root_pow := by
    simp only [toAdjoin, gf2_128Tap, RingHom.comp_apply, coe_mapRingHom, map_X, map_add, map_pow,
      AdjoinRoot.mk_X, map_one]
    exact gf2_128Spec_root_pow_128
  natDegree_eq := gf2_128Poly_natDegree
  n_pos := by simp only [gf2_128Exec]; norm_num
  deg_le := by simp only [gf2_128Exec]; norm_num
  coeff_le := by simp only [gf2_128Exec]; norm_num

theorem gf2_128Val_ofBits_toNat (x : BitVec 128) :
    val gf2_128Exec gf2_128Poly (gf2_128Exec.ofBits x.toNat) = BinaryRep.toSpec gf2_128Poly x :=
  gf2_128Rep.val_ofBits_toNat rfl x

/-- An identity `sqPow n r = s`, checked in the spread representation. -/
theorem sqPow_eq_of_spread {n : ℕ} {r s : BitVec 128}
    (h : gf2_128Exec.sqPow n (gf2_128Exec.ofBits r.toNat) = gf2_128Exec.ofBits s.toNat) :
    sqPow n r = s :=
  BinaryRep.toSpec_injective gf2_128Poly_monic gf2_128Poly_natDegree (by
    rw [gf2_128Spec_toSpec_sqPow, ← gf2_128Val_ofBits_toNat, ← gf2_128Val_ofBits_toNat, ← h,
      gf2_128Rep.val_sqPow (Rep.canon_ofBits _)])

/-- An inequality `sqPow n r ≠ s`, checked in the spread representation. -/
theorem sqPow_ne_of_spread {n : ℕ} {r s : BitVec 128}
    (h : gf2_128Exec.sqPow n (gf2_128Exec.ofBits r.toNat) ≠ gf2_128Exec.ofBits s.toNat) :
    sqPow n r ≠ s := fun he =>
  h (gf2_128Rep.val_injective (gf2_128Rep.canon_sqPow (Rep.canon_ofBits _) n)
    (Rep.canon_ofBits _) (by
      rw [gf2_128Rep.val_sqPow (Rep.canon_ofBits _), gf2_128Val_ofBits_toNat,
        gf2_128Val_ofBits_toNat, ← gf2_128Spec_toSpec_sqPow, he]))

/-- An identity `gfMul a b = c`, checked in the spread representation. -/
theorem gfMul_eq_of_spread {a b c : BitVec 128}
    (h : gf2_128Exec.mul (gf2_128Exec.ofBits a.toNat) (gf2_128Exec.ofBits b.toNat) =
      gf2_128Exec.ofBits c.toNat) :
    gfMul a b = c :=
  BinaryRep.toSpec_injective gf2_128Poly_monic gf2_128Poly_natDegree (by
    rw [gf2_128Spec_toSpec_gfMul, ← gf2_128Val_ofBits_toNat, ← gf2_128Val_ofBits_toNat,
      ← gf2_128Val_ofBits_toNat, ← h, gf2_128Rep.val_mul (Rep.canon_ofBits _) (Rep.canon_ofBits _)])

end Spread

/-! ## Irreducibility certificate -/

/-- `X^(2^64)` reduced modulo `gf2_128Poly`, as bits: `sqPow 64 2`. -/
def gf2_128X64 : BitVec 128 := 0x61651fea6b5832b944e598a795a299f6#128

/-- The inverse of `X^(2^64) - X` modulo `gf2_128Poly`, as bits. Computed as
`(X^(2^64) - X)^(2^128 - 2)` with `gfMul`; `gf2_128X64SubXInv_mul` checks it. -/
def gf2_128X64SubXInv : BitVec 128 := 0x9e4af928ddbc838a41a8cafd2c95b018#128

theorem sqPow_64_two : sqPow 64 2 = gf2_128X64 :=
  sqPow_eq_of_spread (by decide +kernel)

theorem sqPow_64_gf2_128X64 : sqPow 64 gf2_128X64 = 2 :=
  sqPow_eq_of_spread (by decide +kernel)

theorem gf2_128X64SubXInv_mul : gfMul gf2_128X64SubXInv (gf2_128X64 ^^^ 2) = 1 :=
  gfMul_eq_of_spread (by decide +kernel)

theorem gf2_128Spec_root_pow_two_pow_64 :
    AdjoinRoot.root gf2_128Poly ^ 2 ^ 64 = BinaryRep.toSpec gf2_128Poly gf2_128X64 := by
  rw [← BinaryRep.toSpec_two (by norm_num : 1 < 128), ← gf2_128Spec_toSpec_sqPow, sqPow_64_two]

/-- Irreducibility of the reduction polynomial, by Rabin's test: `128`'s only
prime factor is `2`, so the test needs `root ^ 2^128 = root` and a unit
`root ^ 2^64 - root`. -/
theorem gf2_128Poly_irreducible : Irreducible gf2_128Poly := by
  refine irreducible_of_root_pow_card_pow gf2_128Poly_natDegree (by norm_num) ?_ ?_
  · rw [Nat.card_zmod, show 2 ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, pow_mul,
      gf2_128Spec_root_pow_two_pow_64, ← gf2_128Spec_toSpec_sqPow, sqPow_64_gf2_128X64,
      BinaryRep.toSpec_two (by norm_num)]
  · rw [show 128 = 2 ^ 7 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
    intro r hr
    rw [Finset.mem_singleton.mp hr, Nat.card_zmod, show 2 ^ 7 / 2 = 64 by norm_num,
      gf2_128Spec_root_pow_two_pow_64, ← BinaryRep.toSpec_two (f := gf2_128Poly)
        (by norm_num : 1 < 128), CharTwo.sub_eq_add, ← BinaryRep.toSpec_xor]
    refine IsUnit.of_mul_eq_one_right (BinaryRep.toSpec gf2_128Poly gf2_128X64SubXInv) ?_
    rw [← gf2_128Spec_toSpec_gfMul, gf2_128X64SubXInv_mul, BinaryRep.toSpec_one (by norm_num)]

instance instFactIrreducibleGf2_128Poly : Fact (Irreducible gf2_128Poly) :=
  ⟨gf2_128Poly_irreducible⟩

noncomputable instance : Field GF2_128Spec := AdjoinRoot.instField

/-- The facts that make the bit-vector operations with reduction bits `0x87` a field. -/
theorem gf2_128_binarySpec : BinaryRep.Spec 0x87#128 gf2_128Poly where
  monic := gf2_128Poly_monic
  natDegree_eq := gf2_128Poly_natDegree
  root_pow := gf2_128Spec_root_pow_128_eq_toSpec
  irreducible := gf2_128Poly_irreducible
  two_le := by norm_num

/-! ## The executable field -/

/-- `GF(2¹²⁸)`: a `BitVec 128`, bit `i` the coefficient of `X^i`, with the operations of
`GordieHowe.Foundations.Fields.BinaryRep` for the reduction bits `0x87`. -/
def GF2_128 : Type := BitVec 128

/-- The operations of `GF2_128`, typed on `GF2_128` so that the instances below mention the
type `GF2_128` throughout. -/
abbrev gf2_128Ops : ExecOps GF2_128 := BinaryRep.ops 0x87#128

instance : Field GF2_128 := gf2_128Ops.field gf2_128_binarySpec.isField

instance : DecidableEq GF2_128 := inferInstanceAs (DecidableEq (BitVec 128))

instance : Fintype GF2_128 :=
  Fintype.ofEquiv (Fin (2 ^ 128)) (BitVec.equivFin (m := 128)).symm.toEquiv

instance : Repr GF2_128 := inferInstanceAs (Repr (BitVec 128))

/-- The coordinates of an element: its bits, coordinate `i` the coefficient of `X ^ i`. -/
def gf2_128Coords : GF2_128 ≃ (Fin 128 → ZMod 2) := BinaryRep.coordsEquiv

/-- The element of `GF2_128` with polynomial-basis coordinates the bits of `v`, bit `i` the
coefficient of `X^i` (the convention of `GF2_128Exec`). -/
def gf2_128OfBitVec (v : BitVec 128) : GF2_128 := v

theorem gf2_128OfBitVec_injective : Function.Injective gf2_128OfBitVec := fun _ _ h => h

theorem gf2_128OfBitVec_xor (a b : BitVec 128) :
    gf2_128OfBitVec (a ^^^ b) = gf2_128OfBitVec a + gf2_128OfBitVec b :=
  (ExecOps.field_add gf2_128Ops gf2_128_binarySpec.isField a b).symm

/-- `gfMul` is multiplication in `GF2_128`. -/
theorem gf2_128OfBitVec_gfMul (a b : BitVec 128) :
    gf2_128OfBitVec (gfMul a b) = gf2_128OfBitVec a * gf2_128OfBitVec b :=
  (ExecOps.field_mul gf2_128Ops gf2_128_binarySpec.isField a b).symm

theorem gf2_128OfBitVec_zero : gf2_128OfBitVec 0 = 0 :=
  (ExecOps.field_zero gf2_128Ops gf2_128_binarySpec.isField).symm

theorem gf2_128OfBitVec_one : gf2_128OfBitVec 1 = 1 :=
  (ExecOps.field_one gf2_128Ops gf2_128_binarySpec.isField).symm

theorem gf2_128OfBitVec_sqPow (n : ℕ) (r : BitVec 128) :
    gf2_128OfBitVec (sqPow n r) = gf2_128OfBitVec r ^ 2 ^ n := by
  induction n generalizing r with
  | zero => simp [sqPow]
  | succ n ih => rw [sqPow, ih, gf2_128OfBitVec_gfMul, ← sq, ← pow_mul, pow_succ']

theorem gf2_128OfBitVec_gfPow {k n : ℕ} (hn : n < 2 ^ k) (b : BitVec 128) :
    gf2_128OfBitVec (gfPow k n b) = gf2_128OfBitVec b ^ n := by
  induction k generalizing n b with
  | zero =>
    obtain rfl : n = 0 := by simpa using hn
    rw [gfPow, gf2_128OfBitVec_one, pow_zero]
  | succ k ih =>
    have hdiv : n / 2 < 2 ^ k := by rw [pow_succ] at hn; omega
    have hsq : gf2_128OfBitVec (gfPow k (n / 2) (gfMul b b)) =
        gf2_128OfBitVec b ^ (2 * (n / 2)) := by
      rw [ih hdiv, gf2_128OfBitVec_gfMul, ← sq, ← pow_mul]
    conv_rhs => rw [← Nat.div_add_mod n 2]
    rw [gfPow]
    split_ifs with h
    · rw [gf2_128OfBitVec_gfMul, hsq, h, pow_add, pow_one, mul_comm]
    · rw [hsq, Nat.mod_two_ne_one.mp h, add_zero]

/-- The polynomial variable `x` (`kx_ = of_scalar_field(0b10)` in the C++), bits `2`. -/
def gf2_128Root : GF2_128 := gf2_128OfBitVec 2

theorem gf2_128OfBitVec_two : gf2_128OfBitVec 2 = gf2_128Root := rfl

/-! ## The isomorphism with the specification -/

/-- The polynomial-basis map as a ring isomorphism. -/
noncomputable def gf2_128RingEquiv : GF2_128 ≃+* GF2_128Spec :=
  gf2_128_binarySpec.hom.ringEquiv
    (BinaryRep.toSpec_bijective gf2_128Poly_monic gf2_128Poly_natDegree).2

/-- The spread natural of the bits of `x` represents `gf2_128OfBitVec x`. -/
theorem gf2_128OfBitVec_eq_valVia (x : BitVec 128) :
    gf2_128OfBitVec x =
      BinarySpread.valVia gf2_128RingEquiv gf2_128Exec (gf2_128Exec.ofBits x.toNat) := by
  rw [BinarySpread.valVia, gf2_128Val_ofBits_toNat]
  exact (gf2_128RingEquiv.symm_apply_apply x).symm

/-- An identity `gfPow k n b = c`, checked in the spread representation. -/
theorem gfPow_eq_of_spread {k n : ℕ} (hn : n < 2 ^ k) {b c : BitVec 128}
    (h : gf2_128Exec.pow k n (gf2_128Exec.ofBits b.toNat) = gf2_128Exec.ofBits c.toNat) :
    gfPow k n b = c :=
  gf2_128OfBitVec_injective (by
    rw [gf2_128OfBitVec_gfPow hn, gf2_128OfBitVec_eq_valVia b, gf2_128OfBitVec_eq_valVia c, ← h,
      gf2_128Rep.valVia_pow _ (BinarySpread.Rep.canon_ofBits _) hn])

/-- An inequality `gfPow k n b ≠ c`, checked in the spread representation. -/
theorem gfPow_ne_of_spread {k n : ℕ} (hn : n < 2 ^ k) {b c : BitVec 128}
    (h : gf2_128Exec.pow k n (gf2_128Exec.ofBits b.toNat) ≠ gf2_128Exec.ofBits c.toNat) :
    gfPow k n b ≠ c := fun he =>
  h (gf2_128Rep.valVia_injective gf2_128RingEquiv
    (gf2_128Rep.canon_pow (BinarySpread.Rep.canon_ofBits _) k n hn)
    (BinarySpread.Rep.canon_ofBits _) (by
      rw [gf2_128Rep.valVia_pow _ (BinarySpread.Rep.canon_ofBits _) hn,
        ← gf2_128OfBitVec_eq_valVia, ← gf2_128OfBitVec_eq_valVia, ← gf2_128OfBitVec_gfPow hn, he]))

instance : CharP GF2_128 2 :=
  charP_of_injective_ringHom (f := gf2_128RingEquiv.symm.toRingHom) (RingEquiv.injective _) 2

instance : Algebra (ZMod 2) GF2_128 := ZMod.algebra _ 2

/-- **The polynomial-basis map** `GF2_128 ≃ₐ[ZMod 2] GF2_128Spec`, bit `i` to the coefficient
of `root ^ i` (`BinaryRep.toSpec`). -/
noncomputable def gf2_128ToSpec : GF2_128 ≃ₐ[ZMod 2] GF2_128Spec :=
  AlgEquiv.ofRingEquiv (f := gf2_128RingEquiv) fun x => by
    have := RingHom.congr_fun (Subsingleton.elim (gf2_128RingEquiv.toRingHom.comp
      (algebraMap (ZMod 2) GF2_128)) (algebraMap (ZMod 2) GF2_128Spec)) x
    exact this

theorem gf2_128ToSpec_apply (x : GF2_128) :
    gf2_128ToSpec x = BinaryRep.toSpec gf2_128Poly (w := 128) x := rfl

theorem gf2_128ToSpec_root : gf2_128ToSpec gf2_128Root = AdjoinRoot.root gf2_128Poly := by
  rw [gf2_128ToSpec_apply]
  exact BinaryRep.toSpec_two (by norm_num)

/-- The reduction rule `x¹²⁸ = x⁷ + x² + x + 1`. -/
theorem gf2_128_root_pow_128 :
    gf2_128Root ^ 128 = gf2_128Root ^ 7 + gf2_128Root ^ 2 + gf2_128Root + 1 :=
  gf2_128ToSpec.injective (by simp only [map_add, map_pow, map_one, gf2_128ToSpec_root,
    gf2_128Spec_root_pow_128])

/-! ## The polynomial basis -/

/-- The polynomial basis element `x^i`. -/
def gf2_128E (i : Fin 128) : GF2_128 := gf2_128Root ^ (i : ℕ)

/-- Coordinates of `x` in the polynomial basis: its bits. -/
def gf2_128Unpack (x : GF2_128) (i : Fin 128) : Bool := BitVec.getLsbD (w := 128) x i

theorem gf2_128ToSpec_sum_ite (b : Fin 128 → Bool) :
    gf2_128ToSpec (∑ i, if b i then gf2_128E i else 0) =
      ∑ i : Fin 128, if b i then AdjoinRoot.root gf2_128Poly ^ (i : ℕ) else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [gf2_128E, gf2_128ToSpec_root]

theorem gf2_128_pack_unpack (x : GF2_128) :
    (∑ i, if gf2_128Unpack x i then gf2_128E i else 0) = x :=
  gf2_128ToSpec.injective (by rw [gf2_128ToSpec_sum_ite, gf2_128ToSpec_apply]; rfl)

theorem gf2_128_pack_injective (b b' : Fin 128 → Bool)
    (h : (∑ i, if b i then gf2_128E i else 0) = (∑ i, if b' i then gf2_128E i else 0)) :
    b = b' := by
  have h' := congrArg gf2_128ToSpec h
  rw [gf2_128ToSpec_sum_ite, gf2_128ToSpec_sum_ite] at h'
  exact BinaryRep.sum_ite_injective gf2_128Poly_monic gf2_128Poly_natDegree h'

/-- The polynomial basis of `GF(2¹²⁸)` as a `Basis128` instance. -/
def gf2_128Basis128 : Basis128 GF2_128 where
  e := gf2_128E
  unpack := gf2_128Unpack
  pack_unpack := gf2_128_pack_unpack
  pack_injective := gf2_128_pack_injective

instance : Module.Finite (ZMod 2) GF2_128 :=
  have : Module.Finite (ZMod 2) GF2_128Spec := gf2_128Poly_monic.finite_adjoinRoot
  Module.Finite.equiv gf2_128ToSpec.symm.toLinearEquiv

theorem gf2_128_card : Fintype.card GF2_128 = 2 ^ 128 :=
  (Fintype.ofEquiv_card _).trans (Fintype.card_fin _)

end GordieHowe
