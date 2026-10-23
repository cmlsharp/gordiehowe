-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Algebra.ZMod
public import GordieHowe.Foundations.Fields.PolyRep
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import GordieHowe.Foundations.Algebra.PowMod
public import GordieHowe.Foundations.Algebra.PowModOrder
public import GordieHowe.Applications.Params
public import GordieHowe.Applications.Falcon512.Spec.KeyNTT
public import GordieHowe.Foundations.ToMathlib.BinomialIrreducible
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity

@[expose] public section

/-!
# The degree-20 native Falcon A field, the tower `F_12289[u]/(u^4 - 11)[v]/(v^5 - (u + 2))`

The C++ `FalconField20 = NativeWide<Fp14, 20, 11, 2, …, kTower = true>`
(`lib/algebra/fp_native_wide.h:627-628`, `lib/params/param_sets.h`): a quartic step `u^4 = 11`
over `F_12289`, then a quintic step `v^5 = u + 2`, with coordinates `e[4j + i] = u^i v^j`
(`fp_native_wide.h:42-44`).

Irreducibility, both steps by `FiniteField.X_pow_sub_C_irreducible_of_pow_ne_one`:
- Quartic: the only prime of `4` is `2`, `11 ^ ((q - 1) / 2) ≠ 1` (`11` is a primitive root
  mod `12289`), and `q ≡ 1 (mod 4)`.
- Quintic, over the quartic field of order `q^4`: `5 ∣ q^4 - 1` and
  `(u + 2) ^ ((q^4 - 1) / 5) ≠ 1`. Since `u ^ (q^2) = -u` (`11 ^ ((q^2 - 1) / 4) = -1`),
  Frobenius gives `(u + 2) ^ (q^2 + 1) = 4 - u^2`, so the power is `(4 - w) ^ ((q^2 - 1) / 5)`
  with `w = u^2`, `w^2 = 11`. That exponentiation is computed by `decide +kernel` on the
  executable model `quadPowMod` of `F_q[w]/(w^2 - 11)` (reduced pairs of naturals), and equals
  `6570 + 5827 w`. It is not `1`, since otherwise `5827^2 · 11 ≡ 6569^2 (mod q)`.

The signature transform's root `falcon_root_2n(512, 12289)` and the MAC transform's root
`3400 = 1331^8` (order `512`, `lib/circuits/mac/linear_mac256.h:34-45`) lie in `F_12289` and
are embedded unchanged. `9 ∤ 20`, so the degree-9 field does not embed.
-/

namespace GordieHowe

open Polynomial

/-! ## An executable model of `ℤ/m [w]/(w^2 - β)` -/

section QuadModel

/-- Multiplication of reduced pairs `a + b w` in `ℤ/m [w]/(w^2 - β)`. -/
def quadMulMod (m β : ℕ) (x y : ℕ × ℕ) : ℕ × ℕ :=
  ((x.1 * y.1 + β * (x.2 * y.2)) % m, (x.1 * y.2 + x.2 * y.1) % m)

/-- Binary exponentiation in `ℤ/m [w]/(w^2 - β)`, structural on a fuel parameter as
`powModAux`. -/
def quadPowModAux (m β : ℕ) (b : ℕ × ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (1 % m, 0)
  | _ + 1, 0 => (1 % m, 0)
  | fuel + 1, e + 1 =>
    let half := quadPowModAux m β b fuel ((e + 1) / 2)
    let sq := quadMulMod m β half half
    if (e + 1) % 2 = 0 then sq else quadMulMod m β sq b

/-- `b ^ e` in `ℤ/m [w]/(w^2 - β)`, kernel-checkable at a depth linear in the bit length of
`e`. -/
def quadPowMod (m β : ℕ) (b : ℕ × ℕ) (e : ℕ) : ℕ × ℕ := quadPowModAux m β b e e

variable {R : Type*} [CommRing R] {m β : ℕ} (hm : (m : R) = 0) {w : R} (hw : w ^ 2 = β)
include hm

/-- A pair read as `a + b w` in a ring `R`. -/
def quadEval (w : R) (x : ℕ × ℕ) : R := (x.1 : R) + (x.2 : R) * w

theorem natCast_mod_eq_of_natCast_eq_zero (a : ℕ) : ((a % m : ℕ) : R) = a := by
  conv_rhs => rw [← Nat.mod_add_div a m]
  rw [Nat.cast_add, Nat.cast_mul, hm, zero_mul, add_zero]

theorem quadEval_one_mod : quadEval w (1 % m, 0) = 1 := by
  simp [quadEval, natCast_mod_eq_of_natCast_eq_zero hm]

include hw

theorem quadEval_quadMulMod (x y : ℕ × ℕ) :
    quadEval w (quadMulMod m β x y) = quadEval w x * quadEval w y := by
  simp only [quadEval, quadMulMod, natCast_mod_eq_of_natCast_eq_zero hm, Nat.cast_add,
    Nat.cast_mul]
  linear_combination (-((x.2 : R) * y.2)) * hw

theorem quadEval_quadPowModAux (b : ℕ × ℕ) :
    ∀ fuel e, e ≤ fuel → quadEval w (quadPowModAux m β b fuel e) = quadEval w b ^ e
  | 0, e, he => by
    rw [Nat.le_zero.mp he, pow_zero]
    exact quadEval_one_mod hm
  | _ + 1, 0, _ => by
    rw [pow_zero]
    exact quadEval_one_mod hm
  | fuel + 1, e + 1, he => by
    have ih := quadEval_quadPowModAux b fuel ((e + 1) / 2) (by omega)
    simp only [quadPowModAux]
    split_ifs with h
    · rw [quadEval_quadMulMod hm hw, ih, ← pow_add]
      congr 1
      omega
    · rw [quadEval_quadMulMod hm hw, quadEval_quadMulMod hm hw, ih, ← pow_add, ← pow_succ]
      congr 1
      omega

theorem quadEval_quadPowMod (b : ℕ × ℕ) (e : ℕ) :
    quadEval w (quadPowMod m β b e) = quadEval w b ^ e :=
  quadEval_quadPowModAux hm hw b e e le_rfl

end QuadModel

/-- `12289` is prime (`falcon512.q_prime`). The degree-9 file declares the same instance; this
file does not import it so that it survives that file's removal. -/
instance instFactPrimeFalconQ20 : Fact (Nat.Prime 12289) := ⟨falcon512.q_prime⟩

/-! ## The quartic step `u^4 = 11` -/

theorem powMod_eleven_falconQ_sub_one_div_two_eq : powMod 11 ((12289 - 1) / 2) 12289 = 12289 - 1 := by
  decide +kernel

theorem pow_eleven_falconQ_sub_one_div_two_eq_neg_one :
    (11 : ZMod 12289) ^ ((12289 - 1) / 2) = -1 := by
  have h := powMod_eq_neg_one_of_eq (by norm_num) powMod_eleven_falconQ_sub_one_div_two_eq
  rwa [Nat.cast_ofNat] at h

theorem powMod_eleven_falconQ_sq_sub_one_div_four :
    powMod 11 ((12289 ^ 2 - 1) / 4) 12289 = 12289 - 1 := by
  decide +kernel

/-- `X^4 - 11`, the quartic step of the degree-20 tower. -/
noncomputable def falconQuarticPoly : (ZMod 12289)[X] := X ^ 4 - C 11

theorem falconQuarticPoly_monic : falconQuarticPoly.Monic := by
  unfold falconQuarticPoly; monicity!

theorem falconQuarticPoly_natDegree : falconQuarticPoly.natDegree = 4 := by
  unfold falconQuarticPoly; compute_degree!

theorem falconQuarticPoly_irreducible : Irreducible falconQuarticPoly := by
  unfold falconQuarticPoly
  refine FiniteField.X_pow_sub_C_irreducible_of_pow_ne_one (by norm_num) (by decide) ?_ ?_ <;>
    rw [ZMod.card]
  · intro r hr hrd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (n := 2) (by norm_num at hrd ⊢; exact hrd)
    rw [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2,
      pow_eleven_falconQ_sub_one_div_two_eq_neg_one]
    exact ⟨by norm_num, by decide⟩
  · intro _
    norm_num

instance instFactIrreducibleFalconQuarticPoly : Fact (Irreducible falconQuarticPoly) :=
  ⟨falconQuarticPoly_irreducible⟩

/-- The specification `F_12289[u]/(u^4 - 11)`, an `AdjoinRoot` quotient. -/
abbrev FalconQuarticSpec : Type := AdjoinRoot falconQuarticPoly

noncomputable instance : Field FalconQuarticSpec := AdjoinRoot.instField

/-- The facts that make the coefficient-vector operations of `FalconQuartic` a field. -/
theorem falconQuartic_polySpec :
    PolyRep.Spec (PolyRep.binomial (11 : ZMod 12289) : Fin 4 → ZMod 12289) (12289) falconQuarticPoly :=
  PolyRep.Spec.of_binomial falconQuarticPoly_irreducible (Nat.card_zmod _) (by norm_num)
    (by norm_num)

/-! ## The executable field -/

/-- `F_12289[u]/(u^4 - 11)`: an element is its vector of coefficients in the power basis
`1, X, …, X^3`, with the operations of `GordieHowe.PolyRep`. It is the inner block of the tower
`FalconField20` (the quartic step `u^4 = 11`), not a C++ class of its own. -/
def FalconQuartic : Type := Vector (ZMod 12289) 4

/-- The operations of `FalconQuartic`, typed on `FalconQuartic`. -/
abbrev falconQuarticOps : ExecOps FalconQuartic := PolyRep.ops (PolyRep.binomial (11 : ZMod 12289)) (12289)

instance : Field FalconQuartic := falconQuarticOps.field falconQuartic_polySpec.isField

instance : DecidableEq FalconQuartic := inferInstanceAs (DecidableEq (Vector (ZMod 12289) 4))

instance : Fintype FalconQuartic := Fintype.ofEquiv (Fin 4 → ZMod 12289) PolyRep.coordsEquiv.symm

instance : Repr FalconQuartic := inferInstanceAs (Repr (Vector (ZMod 12289) 4))

/-- The coordinates of an element: its stored coefficient vector, coordinate `i` the coefficient
of `X ^ i`. -/
def falconQuarticCoords : FalconQuartic ≃ (Fin 4 → ZMod 12289) := PolyRep.coordsEquiv

/-- The power-basis map `FalconQuartic → FalconQuarticSpec` as a ring isomorphism. -/
noncomputable def falconQuarticRingEquiv : FalconQuartic ≃+* FalconQuarticSpec :=
  ExecOps.Hom.ringEquiv (o := falconQuarticOps) falconQuartic_polySpec.hom
    (PolyRep.toSpec_bijective falconQuarticPoly_monic falconQuarticPoly_natDegree).2

instance : CharP FalconQuarticSpec 12289 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 12289) FalconQuarticSpec).injective 12289

instance : CharP FalconQuartic 12289 :=
  charP_of_injective_ringHom (f := falconQuarticRingEquiv.symm.toRingHom) (RingEquiv.injective _) 12289

instance : Algebra (ZMod 12289) FalconQuartic := ZMod.algebra _ 12289

/-- **The power-basis map** `FalconQuartic ≃ₐ[ZMod 12289] FalconQuarticSpec`: coefficient `i` to the coefficient of
`root ^ i` (`PolyRep.toSpec`). -/
noncomputable def falconQuarticToSpec : FalconQuartic ≃ₐ[ZMod 12289] FalconQuarticSpec :=
  AlgEquiv.ofRingEquiv (f := falconQuarticRingEquiv) fun x => by
    have := RingHom.congr_fun (Subsingleton.elim (falconQuarticRingEquiv.toRingHom.comp
      (algebraMap (ZMod 12289) FalconQuartic)) (algebraMap (ZMod 12289) FalconQuarticSpec)) x
    exact this

theorem falconQuarticToSpec_apply (x : FalconQuartic) : falconQuarticToSpec x = PolyRep.toSpec falconQuarticPoly (n := 4) x := rfl

/-- The generator `X`. -/
def falconQuarticGen : FalconQuartic := PolyRep.gen

theorem falconQuarticToSpec_gen : falconQuarticToSpec falconQuarticGen = AdjoinRoot.root falconQuarticPoly :=
  PolyRep.toSpec_gen (by norm_num)

instance : Module.Finite (ZMod 12289) FalconQuartic :=
  have : Module.Finite (ZMod 12289) FalconQuarticSpec := falconQuarticPoly_monic.finite_adjoinRoot
  Module.Finite.equiv falconQuarticToSpec.symm.toLinearEquiv

theorem falconQuartic_card : Fintype.card FalconQuartic = 12289 ^ 4 := by
  rw [show Fintype.card FalconQuartic = Fintype.card (Fin 4 → ZMod 12289) from Fintype.ofEquiv_card _,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem injective_algebraMap_falconQuartic :
    Function.Injective (algebraMap (ZMod 12289) FalconQuartic) :=
  (algebraMap (ZMod 12289) FalconQuartic).injective

/-- The quartic generator `u`. -/
def falconU : FalconQuartic := falconQuarticGen

theorem falconU_pow_four : falconU ^ 4 = 11 :=
  falconQuarticToSpec.injective (by
    have h := root_X_pow_sub_C_pow 4 (11 : ZMod 12289)
    rw [map_ofNat] at h
    rw [map_pow, falconU, falconQuarticToSpec_gen, map_ofNat]
    exact h)

/-- `u ^ (q^2) = -u`, since `11 ^ ((q^2 - 1) / 4) = -1`. -/
theorem falconU_pow_falconQ_sq : falconU ^ (12289 ^ 2) = -falconU := by
  have he : 12289 ^ 2 = 4 * ((12289 ^ 2 - 1) / 4) + 1 := by norm_num
  have h11 : (11 : FalconQuartic) ^ ((12289 ^ 2 - 1) / 4) = -1 := by
    have h := powMod_eq_neg_one_of_eq (by norm_num) powMod_eleven_falconQ_sq_sub_one_div_four
    rw [Nat.cast_ofNat] at h
    rw [← map_ofNat (algebraMap (ZMod 12289) FalconQuartic), ← map_pow, h, map_neg, map_one]
  rw [he, pow_succ, pow_mul, falconU_pow_four, h11]
  ring

/-- Frobenius at `q^2` on `u + 2`: the relative norm to `F_q[u^2]` is `4 - u^2`. -/
theorem falconU_add_two_pow_falconQ_sq_add_one :
    (falconU + 2) ^ (12289 ^ 2 + 1) = 4 - falconU ^ 2 := by
  have h2 : (2 : FalconQuartic) ^ (12289 ^ 2) = 2 := by
    rw [← map_ofNat (algebraMap (ZMod 12289) FalconQuartic), ← map_pow, ZMod.pow_card_pow]
  rw [pow_succ, add_pow_char_pow, falconU_pow_falconQ_sq, h2]
  ring

theorem quadPowMod_falcon_four_sub_w :
    quadPowMod 12289 11 (4, 12289 - 1) ((12289 ^ 2 - 1) / 5) = (6570, 5827) := by
  decide +kernel

theorem falconU_sq_sq : (falconU ^ 2) ^ 2 = ((11 : ℕ) : FalconQuartic) := by
  rw [← pow_mul, falconU_pow_four, Nat.cast_ofNat]

theorem falconU_add_two_pow_ne_one :
    (falconU + 2) ^ ((12289 ^ 4 - 1) / 5) ≠ 1 := by
  have hm : ((12289 : ℕ) : FalconQuartic) = 0 := CharP.cast_eq_zero _ _
  have he : (12289 ^ 4 - 1) / 5 = (12289 ^ 2 + 1) * ((12289 ^ 2 - 1) / 5) := by norm_num
  have hq : ((12289 - 1 : ℕ) : FalconQuartic) = -1 := by
    rw [Nat.cast_sub (by norm_num), hm, Nat.cast_one, zero_sub]
  have hev := quadEval_quadPowMod hm falconU_sq_sq (4, 12289 - 1) ((12289 ^ 2 - 1) / 5)
  rw [quadPowMod_falcon_four_sub_w] at hev
  simp only [quadEval, hq, Nat.cast_ofNat] at hev
  rw [he, pow_mul, falconU_add_two_pow_falconQ_sq_add_one]
  have h4 : (4 : FalconQuartic) - falconU ^ 2 = 4 + -1 * falconU ^ 2 := by ring
  rw [h4, ← hev]
  intro h
  have hc : ((5827 ^ 2 * 11 : ℕ) : FalconQuartic) = ((6569 ^ 2 : ℕ) : FalconQuartic) := by
    push_cast
    linear_combination (5827 * falconU ^ 2 - 6569) * h - 5827 ^ 2 * falconU_pow_four
  exact absurd ((CharP.natCast_eq_natCast FalconQuartic 12289).mp hc) (by decide)

theorem falconU_add_two_ne_zero : falconU + 2 ≠ 0 := by
  intro h
  have hc : ((16 : ℕ) : FalconQuartic) = ((11 : ℕ) : FalconQuartic) := by
    push_cast
    linear_combination falconU_pow_four - (falconU - 2) * (falconU ^ 2 + 4) * h
  exact absurd ((CharP.natCast_eq_natCast FalconQuartic 12289).mp hc) (by decide)

/-! ## The quintic step `v^5 = u + 2` -/

/-- `X^5 - (u + 2)` over the quartic field, the quintic step of the tower. -/
noncomputable def falconQuinticPoly : FalconQuartic[X] := X ^ 5 - C (falconU + 2)

theorem falconQuinticPoly_monic : falconQuinticPoly.Monic := by
  unfold falconQuinticPoly; monicity!

theorem falconQuinticPoly_natDegree : falconQuinticPoly.natDegree = 5 := by
  unfold falconQuinticPoly; compute_degree!

theorem falconQuinticPoly_irreducible : Irreducible falconQuinticPoly := by
  unfold falconQuinticPoly
  refine FiniteField.X_pow_sub_C_irreducible_of_pow_ne_one (by norm_num) falconU_add_two_ne_zero
    ?_ ?_ <;> rw [falconQuartic_card]
  · intro r hr hrd
    rw [(Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hrd]
    exact ⟨by norm_num, falconU_add_two_pow_ne_one⟩
  · intro h
    exact absurd h (by decide)

instance instFactIrreducibleFalconQuinticPoly : Fact (Irreducible falconQuinticPoly) :=
  ⟨falconQuinticPoly_irreducible⟩

/-- The specification `F_12289[u]/(u^4 - 11)[v]/(v^5 - (u + 2))`, an `AdjoinRoot` quotient. -/
abbrev FalconNativeField20Spec : Type := AdjoinRoot falconQuinticPoly

noncomputable instance : Field FalconNativeField20Spec := AdjoinRoot.instField

/-- The facts that make the coefficient-vector operations of `FalconNativeField20` a field. -/
theorem falconNative20_polySpec :
    PolyRep.Spec (PolyRep.binomial (falconU + 2) : Fin 5 → FalconQuartic) (12289 ^ 4)
      falconQuinticPoly :=
  PolyRep.Spec.of_binomial falconQuinticPoly_irreducible
    (Nat.card_eq_fintype_card.trans falconQuartic_card) (by norm_num) (by norm_num)

/-! ### The executable degree-20 field -/

/-- `F_12289[u]/(u^4 - 11)[v]/(v^5 - (u + 2))`, the degree-20 native Falcon A field: an element
is its vector of `5` coefficients in `FalconQuartic` in the basis `1, v, …, v^4`, with the
operations of `GordieHowe.PolyRep`. -/
def FalconNativeField20 : Type := Vector FalconQuartic 5

/-- The operations of `FalconNativeField20`, typed on `FalconNativeField20`. -/
abbrev falconNative20Ops : ExecOps FalconNativeField20 :=
  PolyRep.ops (PolyRep.binomial (falconU + 2)) (12289 ^ 4)

instance : Field FalconNativeField20 := falconNative20Ops.field falconNative20_polySpec.isField

instance : DecidableEq FalconNativeField20 := inferInstanceAs (DecidableEq (Vector FalconQuartic 5))

instance : Fintype FalconNativeField20 :=
  Fintype.ofEquiv (Fin 5 → FalconQuartic) PolyRep.coordsEquiv.symm

instance : Repr FalconNativeField20 := inferInstanceAs (Repr (Vector FalconQuartic 5))

/-- The coordinates of an element: its stored coefficient vector, coordinate `i` the coefficient
of `X ^ i`. -/
def falconNative20Coords : FalconNativeField20 ≃ (Fin 5 → FalconQuartic) := PolyRep.coordsEquiv

/-- The power-basis map `FalconNativeField20 → FalconNativeField20Spec` as a ring isomorphism. -/
noncomputable def falconNative20RingEquiv : FalconNativeField20 ≃+* FalconNativeField20Spec :=
  ExecOps.Hom.ringEquiv (o := falconNative20Ops) falconNative20_polySpec.hom
    (PolyRep.toSpec_bijective falconQuinticPoly_monic falconQuinticPoly_natDegree).2

/-- The embedding of `FalconQuartic` as the constant coefficients. -/
def falconQuarticToField20 : FalconQuartic →+* FalconNativeField20 where
  toFun := PolyRep.const
  map_one' := rfl
  map_mul' a b := (falconNative20_polySpec.const_mul a b).symm
  map_zero' := PolyRep.const_zero
  map_add' a b := (PolyRep.const_add a b).symm

instance : Algebra FalconQuartic FalconNativeField20 := falconQuarticToField20.toAlgebra

/-- **The power-basis map** `FalconNativeField20 ≃ₐ[FalconQuartic] FalconNativeField20Spec`:
coefficient `j` to the coefficient of `root ^ j` (`PolyRep.toSpec`). -/
noncomputable def falconNative20ToSpec :
    FalconNativeField20 ≃ₐ[FalconQuartic] FalconNativeField20Spec :=
  AlgEquiv.ofRingEquiv (f := falconNative20RingEquiv) fun c =>
    PolyRep.toSpec_const (by norm_num) c

theorem falconNative20ToSpec_apply (x : FalconNativeField20) :
    falconNative20ToSpec x = PolyRep.toSpec falconQuinticPoly (n := 5) x := rfl

instance : CharP FalconNativeField20 12289 :=
  charP_of_injective_algebraMap (algebraMap FalconQuartic FalconNativeField20).injective 12289

instance : Algebra (ZMod 12289) FalconNativeField20 := ZMod.algebra _ 12289

instance : IsScalarTower (ZMod 12289) FalconQuartic FalconNativeField20 :=
  IsScalarTower.of_algebraMap_eq fun x => RingHom.congr_fun (Subsingleton.elim
    (algebraMap (ZMod 12289) FalconNativeField20)
    ((algebraMap FalconQuartic FalconNativeField20).comp (algebraMap (ZMod 12289) FalconQuartic))) x

/-- The tower generator `v`. -/
def falconV : FalconNativeField20 := PolyRep.gen

theorem falconNative20ToSpec_falconV :
    falconNative20ToSpec falconV = AdjoinRoot.root falconQuinticPoly :=
  PolyRep.toSpec_gen (by norm_num)

theorem falconV_pow_five :
    falconV ^ 5 = algebraMap FalconQuartic FalconNativeField20 (falconU + 2) :=
  falconNative20ToSpec.injective (by
    rw [map_pow, falconNative20ToSpec_falconV, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq]
    exact root_X_pow_sub_C_pow 5 (falconU + 2))

/-- The quartic generator `u` in the tower, `u^4 = 11`. -/
def falconUTower : FalconNativeField20 :=
  algebraMap FalconQuartic FalconNativeField20 falconU

theorem falconUTower_pow_four : falconUTower ^ 4 = 11 := by
  rw [falconUTower, ← map_pow, falconU_pow_four, map_ofNat]

/-- The coordinate basis `e[4j + i] = u^i v^j` (`lib/algebra/fp_native_wide.h:42-44`):
`e[k] = u^(k mod 4) v^(k / 4)`. -/
def falconCoord (k : Fin 20) : FalconNativeField20 :=
  falconUTower ^ ((k : ℕ) % 4) * falconV ^ ((k : ℕ) / 4)

theorem falconCoord_four_mul_add (i : Fin 4) (j : Fin 5) :
    falconCoord ⟨4 * j + i, by omega⟩ = falconUTower ^ (i : ℕ) * falconV ^ (j : ℕ) := by
  simp only [falconCoord]
  congr 2 <;> omega

theorem injective_algebraMap_falconNativeField20 :
    Function.Injective (algebraMap (ZMod 12289) FalconNativeField20) :=
  (algebraMap (ZMod 12289) FalconNativeField20).injective

instance : Module.Finite FalconQuartic FalconNativeField20 :=
  have : Module.Finite FalconQuartic FalconNativeField20Spec :=
    falconQuinticPoly_monic.finite_adjoinRoot
  Module.Finite.equiv falconNative20ToSpec.symm.toLinearEquiv

instance : Module.Finite (ZMod 12289) FalconNativeField20 :=
  Module.Finite.trans FalconQuartic FalconNativeField20

theorem falconNativeField20_card : Fintype.card FalconNativeField20 = 12289 ^ 20 := by
  rw [show Fintype.card FalconNativeField20 = Fintype.card (Fin 5 → FalconQuartic) from
    Fintype.ofEquiv_card _, Fintype.card_fun, falconQuartic_card, Fintype.card_fin, ← pow_mul]

/-- A natural strictly between `0` and `12289` casts to a nonzero element of
`FalconNativeField20` (the transform lengths `256` and `512`). -/
theorem falconNativeField20_natCast_ne_zero {a : ℕ} (ha : 0 < a) (hlt : a < 12289) :
    (a : FalconNativeField20) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff FalconNativeField20 12289 a]
  intro hdvd
  exact absurd (Nat.le_of_dvd ha hdvd) (not_le.mpr hlt)

/-! ## The transform roots, in the base field -/

/-! ## The prime subfield -/

end GordieHowe
