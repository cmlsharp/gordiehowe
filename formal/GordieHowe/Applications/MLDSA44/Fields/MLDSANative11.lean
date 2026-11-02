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
# The degree-11 native ML-DSA A field, `F_{8380417^11}`

`MLDSANativeField11 = ZMod 8380417 [X] / (X^11 - 2)`, the C++ `MlDsaField11 =
NativeWide<Fp24, 11, 2, 0, …>` (`lib/algebra/fp_native_wide.h:630-631`, `lib/params/param_sets.h`).

Irreducibility is the prime-degree case of `FiniteField.X_pow_sub_C_irreducible_of_pow_ne_one`:
`11` is prime, `11 ∣ 8380417 - 1`, and `2 ^ ((8380417 - 1) / 11) = 4690951 ≠ 1`
(`powMod`; the certificate of `mldsa11-screen.json`).

The signature transform's root `1753` (order `512`) and the MAC transform's root `1921994`
(order `512`, `1938117^16`; `lib/circuits/mac/linear_mac256.h:34-45`) lie in `F_8380417` and
are embedded unchanged. `6 ∤ 11`, so the degree-6 field does not embed.
-/

namespace GordieHowe

open Polynomial

theorem powMod_two_mlDsaQ_sub_one_div_eleven :
    powMod 2 ((8380417 - 1) / 11) 8380417 = 4690951 := by
  decide +kernel

theorem pow_two_mlDsaQ_sub_one_div_eleven_ne_one :
    (2 : ZMod 8380417) ^ ((8380417 - 1) / 11) ≠ 1 :=
  powMod_ne_one_of_ne (by norm_num) (by rw [powMod_two_mlDsaQ_sub_one_div_eleven]; decide)

/-- `X^11 - 2`, the degree-11 native ML-DSA A field's defining polynomial. -/
noncomputable def mldsaNative11Poly : (ZMod 8380417)[X] := X ^ 11 - C 2

theorem mldsaNative11Poly_monic : mldsaNative11Poly.Monic := by
  unfold mldsaNative11Poly; monicity!

theorem mldsaNative11Poly_natDegree : mldsaNative11Poly.natDegree = 11 := by
  unfold mldsaNative11Poly; compute_degree!

theorem mldsaNative11Poly_irreducible : Irreducible mldsaNative11Poly := by
  unfold mldsaNative11Poly
  refine FiniteField.X_pow_sub_C_irreducible_of_pow_ne_one (by norm_num) (by decide) ?_ ?_ <;>
    rw [ZMod.card]
  · intro r hr hrd
    rw [(Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hrd]
    exact ⟨by norm_num, pow_two_mlDsaQ_sub_one_div_eleven_ne_one⟩
  · intro h
    exact absurd h (by decide)

instance instFactIrreducibleMldsaNative11Poly : Fact (Irreducible mldsaNative11Poly) :=
  ⟨mldsaNative11Poly_irreducible⟩

/-- The specification `ZMod 8380417 [X] / (X^11 - 2)`, an `AdjoinRoot` quotient. -/
abbrev MLDSANativeField11Spec : Type := AdjoinRoot mldsaNative11Poly

noncomputable instance : Field MLDSANativeField11Spec := AdjoinRoot.instField

/-- The facts that make the coefficient-vector operations of `MLDSANativeField11` a field. -/
theorem mldsaNative11_polySpec :
    PolyRep.Spec (PolyRep.binomial (2 : ZMod 8380417) : Fin 11 → ZMod 8380417) (8380417) mldsaNative11Poly :=
  PolyRep.Spec.of_binomial mldsaNative11Poly_irreducible (Nat.card_zmod _) (by norm_num)
    (by norm_num)

/-! ## The executable field -/

/-- `ZMod 8380417 [X] / (X^11 - 2)`: an element is its vector of coefficients in the power basis
`1, X, …, X^10` (the layout of the C++ class), with the operations of `GordieHowe.PolyRep`. -/
def MLDSANativeField11 : Type := Vector (ZMod 8380417) 11

/-- The operations of `MLDSANativeField11`, typed on `MLDSANativeField11`. -/
abbrev mldsaNative11Ops : ExecOps MLDSANativeField11 := PolyRep.ops (PolyRep.binomial (2 : ZMod 8380417)) (8380417)

instance : Field MLDSANativeField11 := mldsaNative11Ops.field mldsaNative11_polySpec.isField

instance : DecidableEq MLDSANativeField11 := inferInstanceAs (DecidableEq (Vector (ZMod 8380417) 11))

instance : Fintype MLDSANativeField11 := Fintype.ofEquiv (Fin 11 → ZMod 8380417) PolyRep.coordsEquiv.symm

instance : Repr MLDSANativeField11 := inferInstanceAs (Repr (Vector (ZMod 8380417) 11))

/-- The coordinates of an element: its stored coefficient vector, coordinate `i` the coefficient
of `X ^ i`. -/
def mldsaNative11Coords : MLDSANativeField11 ≃ (Fin 11 → ZMod 8380417) := PolyRep.coordsEquiv

/-- The power-basis map `MLDSANativeField11 → MLDSANativeField11Spec` as a ring isomorphism. -/
noncomputable def mldsaNative11RingEquiv : MLDSANativeField11 ≃+* MLDSANativeField11Spec :=
  ExecOps.Hom.ringEquiv (o := mldsaNative11Ops) mldsaNative11_polySpec.hom
    (PolyRep.toSpec_bijective mldsaNative11Poly_monic mldsaNative11Poly_natDegree).2

instance : CharP MLDSANativeField11Spec 8380417 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 8380417) MLDSANativeField11Spec).injective 8380417

instance : CharP MLDSANativeField11 8380417 :=
  charP_of_injective_ringHom (f := mldsaNative11RingEquiv.symm.toRingHom) (RingEquiv.injective _) 8380417

instance : Algebra (ZMod 8380417) MLDSANativeField11 := ZMod.algebra _ 8380417

/-- **The power-basis map** `MLDSANativeField11 ≃ₐ[ZMod 8380417] MLDSANativeField11Spec`: coefficient `i` to the coefficient of
`root ^ i` (`PolyRep.toSpec`). -/
noncomputable def mldsaNative11ToSpec : MLDSANativeField11 ≃ₐ[ZMod 8380417] MLDSANativeField11Spec :=
  AlgEquiv.ofRingEquiv (f := mldsaNative11RingEquiv) fun x => by
    have := RingHom.congr_fun (Subsingleton.elim (mldsaNative11RingEquiv.toRingHom.comp
      (algebraMap (ZMod 8380417) MLDSANativeField11)) (algebraMap (ZMod 8380417) MLDSANativeField11Spec)) x
    exact this

theorem mldsaNative11ToSpec_apply (x : MLDSANativeField11) : mldsaNative11ToSpec x = PolyRep.toSpec mldsaNative11Poly (n := 11) x := rfl

/-- The generator `X`. -/
def mldsaNative11Gen : MLDSANativeField11 := PolyRep.gen

theorem mldsaNative11ToSpec_gen : mldsaNative11ToSpec mldsaNative11Gen = AdjoinRoot.root mldsaNative11Poly :=
  PolyRep.toSpec_gen (by norm_num)

instance : Module.Finite (ZMod 8380417) MLDSANativeField11 :=
  have : Module.Finite (ZMod 8380417) MLDSANativeField11Spec := mldsaNative11Poly_monic.finite_adjoinRoot
  Module.Finite.equiv mldsaNative11ToSpec.symm.toLinearEquiv

theorem mldsaNativeField11_card : Fintype.card MLDSANativeField11 = 8380417 ^ 11 := by
  rw [show Fintype.card MLDSANativeField11 = Fintype.card (Fin 11 → ZMod 8380417) from Fintype.ofEquiv_card _,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem injective_algebraMap_mldsaNativeField11 :
    Function.Injective (algebraMap (ZMod 8380417) MLDSANativeField11) :=
  (algebraMap (ZMod 8380417) MLDSANativeField11).injective

/-- The same fact at the vendored `MLDSA.modulus`, the form the ML-DSA gadget theorems use. -/
instance : CharP MLDSANativeField11 _root_.MLDSA.modulus :=
  inferInstanceAs (CharP MLDSANativeField11 8380417)

/-- A natural strictly between `0` and `8380417` casts to a nonzero element of
`MLDSANativeField11` (the transform lengths `256` and `512`). -/
theorem mldsaNativeField11_natCast_ne_zero {a : ℕ} (ha : 0 < a) (hlt : a < 8380417) :
    (a : MLDSANativeField11) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff MLDSANativeField11 8380417 a]
  intro hdvd
  exact absurd (Nat.le_of_dvd ha hdvd) (not_le.mpr hlt)

/-! ## The transform roots, in the base field -/

/-! ## The prime subfield -/

end GordieHowe
