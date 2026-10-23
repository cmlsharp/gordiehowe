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
public import GordieHowe.Applications.Falcon512.Spec.KeyNTT
public import GordieHowe.Foundations.ToMathlib.BinomialIrreducible
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity

@[expose] public section

/-!
# The native Falcon A field, `F_{12289^9}`

The native Falcon construction (`lib/gordiehowe/examples/falcon/falcon_native.h`) runs domain A over
`AF = Fp14_9 = Fp14_N<9, 2>` (`lib/algebra/fp14_n.h:384`; `FalconNativeField = Fp14_9`,
`lib/params/param_sets.h`; and the template's instantiation comment,
`lib/algebra/fp14_n.h:382`: "`x^9 - 2` over `F_12289`: `2` is a
cubic non-residue"). `Fp14_N<kDeg, kBetaN>` (`lib/algebra/fp14_n.h:52-63`) represents
`P(x) mod (x^kDeg - kBetaN)` over the base field, so `AF = ZMod 12289 [X] / (X^9 - 2)`.

`12289` is prime (`falcon512.q_prime`). Irreducibility of `X^9 - C 2` follows from `2` being a
cubic non-residue via `X_pow_sub_C_irreducible_of_prime_pow_of_ne_two` (`9 = 3^2`, odd prime power):
that comment gives the certificate, "`2^4096 != 1`" (`(12289 - 1) / 3 = 4096`).

Two roots the native verifier's transforms use, both base-field elements embedded by
`algebraMap (ZMod 12289) FalconNativeField9`:

- the MAC transform's root, `linear_mac::root(const Fp14_N<D, B>&)`
  (`lib/circuits/mac/linear_mac.h:56-57`): `f.of_scalar(8340)`, "order 256 in `F_12289` itself, so
  the same scalar serves every extension of it" -- confirmed here, order `256`, used at the MAC
  transform length `lib/circuits/mac/linear_mac.h:73` (`fft`, `check(a.size()==256, ...)`);
- the signature transform's root, `falcon_root_2n(512, 12289)`
  (`lib/schemes/falcon/falcon_ntt.h`), passed to `native_linear::Relation` as
  `af.of_scalar(falcon_root_2n(n, Q))` at `n = 512`, `Q = 12289`. This is exactly
  `GordieHowe.Falcon512.KeyNTT.falconRoot2n 512 12289`, already proved a primitive `1024`th root of unity of
  `ZMod 12289` (`GordieHowe.Falcon512.KeyNTT.falconRoot2n_512_isPrimitiveRoot`); reused here rather than
  reproved.
-/

namespace GordieHowe

open Polynomial

instance instFactPrimeFalconQ : Fact (Nat.Prime 12289) := ⟨falcon512.q_prime⟩

/-- `2^((12289 - 1) / 3) ≠ 1`: the flagship's own certificate that `2` is a cubic non-residue mod
`12289` (`lib/algebra/fp14_n.h:382`, "`2^4096 != 1`"; `(12289 - 1) / 3 = 4096`). -/
theorem powMod_two_falconQ_sub_one_div_three : powMod 2 ((12289 - 1) / 3) 12289 ≠ 1 := by
  decide +kernel

theorem pow_two_falconQ_sub_one_div_three_ne_one :
    (2 : ZMod 12289) ^ ((12289 - 1) / 3) ≠ 1 :=
  powMod_ne_one_of_ne (by norm_num) powMod_two_falconQ_sub_one_div_three

/-- `2` is not a cube mod `12289`. -/
theorem two_not_cube_falconQ : ∀ b : ZMod 12289, b ^ 3 ≠ 2 :=
  not_isNthPow_of_pow_ne_one (by norm_num) (by decide) pow_two_falconQ_sub_one_div_three_ne_one

/-- `X^9 - 2`, the native Falcon A field's defining polynomial
(`Fp14_N<9, 2>`, `lib/algebra/fp14_n.h:382`). -/
noncomputable def falconNativePoly : (ZMod 12289)[X] := X ^ 9 - C 2

theorem falconNativePoly_monic : falconNativePoly.Monic := by
  unfold falconNativePoly; monicity!

theorem falconNativePoly_natDegree : falconNativePoly.natDegree = 9 := by
  unfold falconNativePoly; compute_degree!

/-- `9 = 3^2` is an odd prime power and `2` is not a cube mod `12289`
(`two_not_cube_falconQ`), so `X^9 - C 2` is irreducible
(`X_pow_sub_C_irreducible_of_prime_pow_of_ne_two`). -/
theorem falconNativePoly_irreducible : Irreducible falconNativePoly := by
  unfold falconNativePoly
  exact X_pow_sub_C_irreducible_of_prime_pow_of_ne_two (p := 3) (by norm_num) (by norm_num) 2
    two_not_cube_falconQ

instance instFactIrreducibleFalconNativePoly : Fact (Irreducible falconNativePoly) :=
  ⟨falconNativePoly_irreducible⟩

/-- The specification `ZMod 12289 [X] / (X^9 - 2)`, an `AdjoinRoot` quotient. -/
abbrev FalconNativeField9Spec : Type := AdjoinRoot falconNativePoly

noncomputable instance : Field FalconNativeField9Spec := AdjoinRoot.instField

/-- The facts that make the coefficient-vector operations of `FalconNativeField9` a field. -/
theorem falconNative9_polySpec :
    PolyRep.Spec (PolyRep.binomial (2 : ZMod 12289) : Fin 9 → ZMod 12289) (12289) falconNativePoly :=
  PolyRep.Spec.of_binomial falconNativePoly_irreducible (Nat.card_zmod _) (by norm_num)
    (by norm_num)

/-! ## The executable field -/

/-- `ZMod 12289 [X] / (X^9 - 2)`: an element is its vector of coefficients in the power basis
`1, X, …, X^8` (the layout of the C++ class), with the operations of `GordieHowe.PolyRep`. -/
def FalconNativeField9 : Type := Vector (ZMod 12289) 9

/-- The operations of `FalconNativeField9`, typed on `FalconNativeField9`. -/
abbrev falconNative9Ops : ExecOps FalconNativeField9 := PolyRep.ops (PolyRep.binomial (2 : ZMod 12289)) (12289)

instance : Field FalconNativeField9 := falconNative9Ops.field falconNative9_polySpec.isField

instance : DecidableEq FalconNativeField9 := inferInstanceAs (DecidableEq (Vector (ZMod 12289) 9))

instance : Fintype FalconNativeField9 := Fintype.ofEquiv (Fin 9 → ZMod 12289) PolyRep.coordsEquiv.symm

instance : Repr FalconNativeField9 := inferInstanceAs (Repr (Vector (ZMod 12289) 9))

/-- The coordinates of an element: its stored coefficient vector, coordinate `i` the coefficient
of `X ^ i`. -/
def falconNative9Coords : FalconNativeField9 ≃ (Fin 9 → ZMod 12289) := PolyRep.coordsEquiv

/-- The power-basis map `FalconNativeField9 → FalconNativeField9Spec` as a ring isomorphism. -/
noncomputable def falconNative9RingEquiv : FalconNativeField9 ≃+* FalconNativeField9Spec :=
  ExecOps.Hom.ringEquiv (o := falconNative9Ops) falconNative9_polySpec.hom
    (PolyRep.toSpec_bijective falconNativePoly_monic falconNativePoly_natDegree).2

instance : CharP FalconNativeField9Spec 12289 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 12289) FalconNativeField9Spec).injective 12289

instance : CharP FalconNativeField9 12289 :=
  charP_of_injective_ringHom (f := falconNative9RingEquiv.symm.toRingHom) (RingEquiv.injective _) 12289

instance : Algebra (ZMod 12289) FalconNativeField9 := ZMod.algebra _ 12289

/-- **The power-basis map** `FalconNativeField9 ≃ₐ[ZMod 12289] FalconNativeField9Spec`: coefficient `i` to the coefficient of
`root ^ i` (`PolyRep.toSpec`). -/
noncomputable def falconNative9ToSpec : FalconNativeField9 ≃ₐ[ZMod 12289] FalconNativeField9Spec :=
  AlgEquiv.ofRingEquiv (f := falconNative9RingEquiv) fun x => by
    have := RingHom.congr_fun (Subsingleton.elim (falconNative9RingEquiv.toRingHom.comp
      (algebraMap (ZMod 12289) FalconNativeField9)) (algebraMap (ZMod 12289) FalconNativeField9Spec)) x
    exact this

theorem falconNative9ToSpec_apply (x : FalconNativeField9) : falconNative9ToSpec x = PolyRep.toSpec falconNativePoly (n := 9) x := rfl

/-- The generator `X`. -/
def falconNative9Gen : FalconNativeField9 := PolyRep.gen

theorem falconNative9ToSpec_gen : falconNative9ToSpec falconNative9Gen = AdjoinRoot.root falconNativePoly :=
  PolyRep.toSpec_gen (by norm_num)

instance : Module.Finite (ZMod 12289) FalconNativeField9 :=
  have : Module.Finite (ZMod 12289) FalconNativeField9Spec := falconNativePoly_monic.finite_adjoinRoot
  Module.Finite.equiv falconNative9ToSpec.symm.toLinearEquiv

theorem falconNativeField_card : Fintype.card FalconNativeField9 = 12289 ^ 9 := by
  rw [show Fintype.card FalconNativeField9 = Fintype.card (Fin 9 → ZMod 12289) from Fintype.ofEquiv_card _,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem injective_algebraMap_falconNativeField :
    Function.Injective (algebraMap (ZMod 12289) FalconNativeField9) :=
  (algebraMap (ZMod 12289) FalconNativeField9).injective

/-! ## The MAC transform's root -/

/-! ## The signature transform's root -/

/-- A natural strictly between `0` and `12289` casts to a nonzero element of `FalconNativeField9`:
needed at `256` and `512`, the two transform lengths, wherever a row evaluator divides by a
transform length. -/
theorem falconNativeField_natCast_ne_zero {a : ℕ} (ha : 0 < a) (hlt : a < 12289) :
    (a : FalconNativeField9) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff FalconNativeField9 12289 a]
  intro hdvd
  exact absurd (Nat.le_of_dvd ha hdvd) (not_le.mpr hlt)

end GordieHowe
