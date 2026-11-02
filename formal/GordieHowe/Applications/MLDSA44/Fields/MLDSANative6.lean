-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Algebra.ZMod
public import GordieHowe.Foundations.Fields.PolyRep
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.ComputeDegree
public import GordieHowe.Foundations.Algebra.PowMod
public import GordieHowe.Foundations.Algebra.PowModOrder
public import GordieHowe.Applications.Params
public import GordieHowe.Foundations.ToMathlib.BinomialIrreducible
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity
public import LatticeCrypto.MLDSA.Concrete.NTT

@[expose] public section

/-!
# The native ML-DSA A field, `F_{8380417^6}`

The native ML-DSA system (`MLDSANativeSystem` in `lib/gordiehowe/examples/mldsa/mldsa_native.h`,
benchmarked by `MLDSANative.DISABLED_Bench`) runs its A circuit, at the ROM parameters, over
`MLDSANativeField = Fp24_6` (`lib/params/param_sets.h`). `Fp24_6`
(`lib/algebra/fp24_6.h`) represents `P(x) mod (x^6 - beta)` over `F_8380417` with `beta = 7` fixed
at compile time (`fp24_6.h`, "`x^6 - 7` is irreducible over `F_8380417`"), so
`AF = ZMod 8380417 [X] / (X^6 - 7)`.

`6 = 2 · 3` is not a prime power, so irreducibility comes from
`irreducible_X_pow_two_mul_sub_C_of_not_sq_not_pow` (`GordieHowe/Foundations/ToMathlib/BinomialIrreducible.lean`): `7` is
neither a square nor a cube mod `8380417`, each certified by one modular exponentiation.

Three objects the native verifier uses, all from the base field:

- the signature transform's root, `A.field().of_scalar(kPsi)` with `kPsi = 1753`
  (`lib/gordiehowe/examples/mldsa/mldsa_native.h`, `mldsa_gadgets.h:64`). This is FIPS 204's
  `ζ = 1753`, the vendored `MLDSA.zeta`; its order `512` is the vendored
  `MLDSA.Concrete.zeta_isPrimitiveRoot`;
- the MAC transform's root, `linear_mac::root(const Fp24_6&)` = `f.of_scalar(5801164)`
  (`lib/circuits/mac/linear_mac.h:56`), the root of order `2W = 256` of the 128-bit MAC
  (`mac_root<128>`): order `256`, certified by `5801164^128 = -1`;
- the prime subfield `F_8380417`, the designated subfield of domain A.
-/

namespace GordieHowe

open Polynomial

theorem powMod_seven_mlDsaQ_sub_one_div_two : powMod 7 ((8380417 - 1) / 2) 8380417 ≠ 1 := by
  decide +kernel

theorem powMod_seven_mlDsaQ_sub_one_div_three : powMod 7 ((8380417 - 1) / 3) 8380417 ≠ 1 := by
  decide +kernel

theorem pow_seven_mlDsaQ_sub_one_div_two_ne_one :
    (7 : ZMod 8380417) ^ ((8380417 - 1) / 2) ≠ 1 :=
  powMod_ne_one_of_ne (by norm_num) powMod_seven_mlDsaQ_sub_one_div_two

theorem pow_seven_mlDsaQ_sub_one_div_three_ne_one :
    (7 : ZMod 8380417) ^ ((8380417 - 1) / 3) ≠ 1 :=
  powMod_ne_one_of_ne (by norm_num) powMod_seven_mlDsaQ_sub_one_div_three

theorem seven_not_square_mlDsaQ : ∀ b : ZMod 8380417, b ^ 2 ≠ 7 :=
  not_isNthPow_of_pow_ne_one (by norm_num) (by decide) pow_seven_mlDsaQ_sub_one_div_two_ne_one

theorem seven_not_cube_mlDsaQ : ∀ b : ZMod 8380417, b ^ 3 ≠ 7 :=
  not_isNthPow_of_pow_ne_one (by norm_num) (by decide) pow_seven_mlDsaQ_sub_one_div_three_ne_one

/-- `X^6 - 7`, the native ML-DSA A field's defining polynomial (`Fp24_6`, `beta_ = 7`). -/
noncomputable def mldsaNativePoly : (ZMod 8380417)[X] := X ^ 6 - C 7

theorem mldsaNativePoly_monic : mldsaNativePoly.Monic := by
  unfold mldsaNativePoly; monicity!

theorem mldsaNativePoly_natDegree : mldsaNativePoly.natDegree = 6 := by
  unfold mldsaNativePoly; compute_degree!

/-- `6 = 2 · 3` with `3` an odd prime, and `7` is neither a square nor a cube mod `8380417`. -/
theorem mldsaNativePoly_irreducible : Irreducible mldsaNativePoly := by
  unfold mldsaNativePoly
  exact irreducible_X_pow_two_mul_sub_C_of_not_sq_not_pow (p := 3) (by norm_num) (by decide)
    seven_not_square_mlDsaQ seven_not_cube_mlDsaQ

instance instFactIrreducibleMldsaNativePoly : Fact (Irreducible mldsaNativePoly) :=
  ⟨mldsaNativePoly_irreducible⟩

/-- The specification `ZMod 8380417 [X] / (X^6 - 7)`, an `AdjoinRoot` quotient. -/
abbrev MLDSANativeField6Spec : Type := AdjoinRoot mldsaNativePoly

noncomputable instance : Field MLDSANativeField6Spec := AdjoinRoot.instField

/-- The facts that make the coefficient-vector operations of `MLDSANativeField6` a field. -/
theorem mldsaNative6_polySpec :
    PolyRep.Spec (PolyRep.binomial (7 : ZMod 8380417) : Fin 6 → ZMod 8380417) (8380417) mldsaNativePoly :=
  PolyRep.Spec.of_binomial mldsaNativePoly_irreducible (Nat.card_zmod _) (by norm_num)
    (by norm_num)

/-! ## The executable field -/

/-- `ZMod 8380417 [X] / (X^6 - 7)`: an element is its vector of coefficients in the power basis
`1, X, …, X^5` (the layout of the C++ class), with the operations of `GordieHowe.PolyRep`. -/
def MLDSANativeField6 : Type := Vector (ZMod 8380417) 6

/-- The operations of `MLDSANativeField6`, typed on `MLDSANativeField6`. -/
abbrev mldsaNative6Ops : ExecOps MLDSANativeField6 := PolyRep.ops (PolyRep.binomial (7 : ZMod 8380417)) (8380417)

instance : Field MLDSANativeField6 := mldsaNative6Ops.field mldsaNative6_polySpec.isField

instance : DecidableEq MLDSANativeField6 := inferInstanceAs (DecidableEq (Vector (ZMod 8380417) 6))

instance : Fintype MLDSANativeField6 := Fintype.ofEquiv (Fin 6 → ZMod 8380417) PolyRep.coordsEquiv.symm

instance : Repr MLDSANativeField6 := inferInstanceAs (Repr (Vector (ZMod 8380417) 6))

/-- The coordinates of an element: its stored coefficient vector, coordinate `i` the coefficient
of `X ^ i`. -/
def mldsaNative6Coords : MLDSANativeField6 ≃ (Fin 6 → ZMod 8380417) := PolyRep.coordsEquiv

/-- The power-basis map `MLDSANativeField6 → MLDSANativeField6Spec` as a ring isomorphism. -/
noncomputable def mldsaNative6RingEquiv : MLDSANativeField6 ≃+* MLDSANativeField6Spec :=
  ExecOps.Hom.ringEquiv (o := mldsaNative6Ops) mldsaNative6_polySpec.hom
    (PolyRep.toSpec_bijective mldsaNativePoly_monic mldsaNativePoly_natDegree).2

instance : CharP MLDSANativeField6Spec 8380417 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 8380417) MLDSANativeField6Spec).injective 8380417

instance : CharP MLDSANativeField6 8380417 :=
  charP_of_injective_ringHom (f := mldsaNative6RingEquiv.symm.toRingHom) (RingEquiv.injective _) 8380417

instance : Algebra (ZMod 8380417) MLDSANativeField6 := ZMod.algebra _ 8380417

/-- **The power-basis map** `MLDSANativeField6 ≃ₐ[ZMod 8380417] MLDSANativeField6Spec`: coefficient `i` to the coefficient of
`root ^ i` (`PolyRep.toSpec`). -/
noncomputable def mldsaNative6ToSpec : MLDSANativeField6 ≃ₐ[ZMod 8380417] MLDSANativeField6Spec :=
  AlgEquiv.ofRingEquiv (f := mldsaNative6RingEquiv) fun x => by
    have := RingHom.congr_fun (Subsingleton.elim (mldsaNative6RingEquiv.toRingHom.comp
      (algebraMap (ZMod 8380417) MLDSANativeField6)) (algebraMap (ZMod 8380417) MLDSANativeField6Spec)) x
    exact this

theorem mldsaNative6ToSpec_apply (x : MLDSANativeField6) : mldsaNative6ToSpec x = PolyRep.toSpec mldsaNativePoly (n := 6) x := rfl

/-- The generator `X`. -/
def mldsaNative6Gen : MLDSANativeField6 := PolyRep.gen

theorem mldsaNative6ToSpec_gen : mldsaNative6ToSpec mldsaNative6Gen = AdjoinRoot.root mldsaNativePoly :=
  PolyRep.toSpec_gen (by norm_num)

instance : Module.Finite (ZMod 8380417) MLDSANativeField6 :=
  have : Module.Finite (ZMod 8380417) MLDSANativeField6Spec := mldsaNativePoly_monic.finite_adjoinRoot
  Module.Finite.equiv mldsaNative6ToSpec.symm.toLinearEquiv

theorem mldsaNativeField_card : Fintype.card MLDSANativeField6 = 8380417 ^ 6 := by
  rw [show Fintype.card MLDSANativeField6 = Fintype.card (Fin 6 → ZMod 8380417) from Fintype.ofEquiv_card _,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem injective_algebraMap_mldsaNativeField :
    Function.Injective (algebraMap (ZMod 8380417) MLDSANativeField6) :=
  (algebraMap (ZMod 8380417) MLDSANativeField6).injective

/-- The same fact at the vendored `MLDSA.modulus`, the form the ML-DSA gadget theorems use. -/
instance : CharP MLDSANativeField6 _root_.MLDSA.modulus :=
  inferInstanceAs (CharP MLDSANativeField6 8380417)

/-- A natural strictly between `0` and `8380417` casts to a nonzero element of
`MLDSANativeField6`: needed at `256`, the transform length of both the signature and the MAC
transforms, wherever a row evaluator divides by it. -/
theorem mldsaNativeField_natCast_ne_zero {a : ℕ} (ha : 0 < a) (hlt : a < 8380417) :
    (a : MLDSANativeField6) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff MLDSANativeField6 8380417 a]
  intro hdvd
  exact absurd (Nat.le_of_dvd ha hdvd) (not_le.mpr hlt)

/-! ## The signature transform's root -/

/-! ## The MAC transform's root -/

/-! ## The prime subfield -/

end GordieHowe
