-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.ToMathlib.BinomialIrreducible

@[expose] public section

/-!
# The Goldilocks quartic extension `F_{p⁴}`

`F_{p⁴}` for the Goldilocks prime `p = 2^64 − 2^32 + 1`, as `ZMod p [X] / (X⁴ − 7)`: the A field
`Fp64G4` of the emulated arms at the QROM parameters (`using EmulatedField = Fp64G4;`,
`lib/params/param_sets.h`). The class `lib/algebra/fp_goldilocks4.h`:

* line 7: "`X^4-7` is irreducible: 7 is a primitive element of F_p, p=1 mod 4.";
* line 8: "Tower representation `(a0+a2*u)+(a1+a3*u)*v`, `u^2=7`, `v^2=u`", so the coordinates
  `e[0..3]` are those of `1, v, v², v³` with `v⁴ = 7`;
* `pu(a) = {7 * a[1], a[0]}` (line 62) and `pm` (lines 63-68) multiply by `u` and in
  `F_p[u]/(u² − 7)`; `reduce` folds coefficient `i + 4` into `i` with the factor `7`
  (lines 124-125);
* `of_scalar(a) = {a, 0, 0, 0}` (line 35): the prime-subfield embedding;
* the subfield `F_p` is `e[1] = e[2] = e[3] = 0` (`in_subfield`, lines 149-151).

Irreducibility is `irreducible_X_pow_four_sub_C_of_not_sq`: `7` is not a square
(`GordieHowe.seven_not_isSquare_pGold`), and neither is `−7`, since `(−7)^((p−1)/2) = 7^((p−1)/2)`
(the exponent `(p − 1)/2 = 2^31 · (2^32 − 1)` is even) and `7^((p−1)/2) ≠ 1`.

`GoldilocksExt2 = F_p[y]/(y² − 7)` embeds by `y ↦ v²` (`goldilocksExt2ToQuartic`), the `u` of the C++
tower.
-/

namespace GordieHowe

open Polynomial

/-- The defining polynomial `X⁴ − 7` (`lib/algebra/fp_goldilocks4.h:7-8`). -/
noncomputable def goldQuarticPoly : (ZMod pGold)[X] := X ^ 4 - C 7

theorem goldQuarticPoly_monic : goldQuarticPoly.Monic := by
  unfold goldQuarticPoly; monicity!

theorem goldQuarticPoly_natDegree : goldQuarticPoly.natDegree = 4 := by
  unfold goldQuarticPoly; compute_degree!

/-- `(p − 1) / 2` is even. -/
theorem even_pGold_sub_one_div_two : Even ((pGold - 1) / 2) := by
  rw [pGold_sub_one]; decide

/-- `−7` is not a square mod `p`: `(−7)^((p−1)/2) = 7^((p−1)/2) ≠ 1` (Euler's criterion). -/
theorem neg_seven_not_isSquare_pGold : ¬ IsSquare (-7 : ZMod pGold) := by
  rw [ZMod.euler_criterion pGold (neg_ne_zero.mpr seven_ne_zero_pGold), pGold_div_two,
    even_pGold_sub_one_div_two.neg_pow]
  exact pow_7_pGold_sub_one_div_two_ne_one

theorem not_sq_eq_of_not_isSquare {a : ZMod pGold} (h : ¬ IsSquare a) :
    ∀ b : ZMod pGold, b ^ 2 ≠ a :=
  fun b hb => h ⟨b, by rw [← hb, sq]⟩

/-- `X⁴ − 7` is irreducible: neither `7` nor `−7` is a square mod `p`. -/
theorem goldQuarticPoly_irreducible : Irreducible goldQuarticPoly :=
  irreducible_X_pow_four_sub_C_of_not_sq (not_sq_eq_of_not_isSquare seven_not_isSquare_pGold)
    (not_sq_eq_of_not_isSquare neg_seven_not_isSquare_pGold)

instance instFactIrreducibleGoldQuarticPoly : Fact (Irreducible goldQuarticPoly) :=
  ⟨goldQuarticPoly_irreducible⟩

/-- The specification `F_p[X] / (X⁴ − 7)`, an `AdjoinRoot` quotient. -/
abbrev GoldilocksExt4Spec : Type := AdjoinRoot goldQuarticPoly

noncomputable instance : Field GoldilocksExt4Spec := AdjoinRoot.instField

/-- The facts that make the coefficient-vector operations of `GoldilocksExt4` a field. -/
theorem goldilocksExt4_polySpec :
    PolyRep.Spec (PolyRep.binomial (7 : ZMod pGold) : Fin 4 → ZMod pGold) (pGold) goldQuarticPoly :=
  PolyRep.Spec.of_binomial goldQuarticPoly_irreducible (Nat.card_zmod _) (by norm_num)
    (by rw [pGold_eq]; norm_num)

/-! ## The executable field -/

/-- `F_p[X] / (X⁴ − 7)`: an element is its vector of coefficients in the power basis
`1, X, …, X^3` (the layout of the C++ class), with the operations of `GordieHowe.Foundations.Fields.PolyRep`. -/
def GoldilocksExt4 : Type := Vector (ZMod pGold) 4

/-- The operations of `GoldilocksExt4`, typed on `GoldilocksExt4`. -/
abbrev goldilocksExt4Ops : ExecOps GoldilocksExt4 := PolyRep.ops (PolyRep.binomial (7 : ZMod pGold)) (pGold)

instance : Field GoldilocksExt4 := goldilocksExt4Ops.field goldilocksExt4_polySpec.isField

instance : DecidableEq GoldilocksExt4 := inferInstanceAs (DecidableEq (Vector (ZMod pGold) 4))

instance : Fintype GoldilocksExt4 := Fintype.ofEquiv (Fin 4 → ZMod pGold) PolyRep.coordsEquiv.symm

instance : Repr GoldilocksExt4 := inferInstanceAs (Repr (Vector (ZMod pGold) 4))

/-- The coordinates of an element: its stored coefficient vector, coordinate `i` the coefficient
of `X ^ i`. -/
def goldilocksExt4Coords : GoldilocksExt4 ≃ (Fin 4 → ZMod pGold) := PolyRep.coordsEquiv

/-- The power-basis map `GoldilocksExt4 → GoldilocksExt4Spec` as a ring isomorphism. -/
noncomputable def goldilocksExt4RingEquiv : GoldilocksExt4 ≃+* GoldilocksExt4Spec :=
  ExecOps.Hom.ringEquiv (o := goldilocksExt4Ops) goldilocksExt4_polySpec.hom
    (PolyRep.toSpec_bijective goldQuarticPoly_monic goldQuarticPoly_natDegree).2

instance : CharP GoldilocksExt4Spec pGold :=
  charP_of_injective_algebraMap (algebraMap (ZMod pGold) GoldilocksExt4Spec).injective pGold

instance : CharP GoldilocksExt4 pGold :=
  charP_of_injective_ringHom (f := goldilocksExt4RingEquiv.symm.toRingHom) (RingEquiv.injective _) pGold

instance : Algebra (ZMod pGold) GoldilocksExt4 := ZMod.algebra _ pGold

/-- **The power-basis map** `GoldilocksExt4 ≃ₐ[ZMod pGold] GoldilocksExt4Spec`: coefficient `i` to the coefficient of
`root ^ i` (`PolyRep.toSpec`). -/
noncomputable def goldilocksExt4ToSpec : GoldilocksExt4 ≃ₐ[ZMod pGold] GoldilocksExt4Spec :=
  AlgEquiv.ofRingEquiv (f := goldilocksExt4RingEquiv) fun x => by
    have := RingHom.congr_fun (Subsingleton.elim (goldilocksExt4RingEquiv.toRingHom.comp
      (algebraMap (ZMod pGold) GoldilocksExt4)) (algebraMap (ZMod pGold) GoldilocksExt4Spec)) x
    exact this

theorem goldilocksExt4ToSpec_apply (x : GoldilocksExt4) : goldilocksExt4ToSpec x = PolyRep.toSpec goldQuarticPoly (n := 4) x := rfl

/-- The generator `X`. -/
def goldilocksExt4Gen : GoldilocksExt4 := PolyRep.gen

theorem goldilocksExt4ToSpec_gen : goldilocksExt4ToSpec goldilocksExt4Gen = AdjoinRoot.root goldQuarticPoly :=
  PolyRep.toSpec_gen (by norm_num)

instance : Module.Finite (ZMod pGold) GoldilocksExt4 :=
  have : Module.Finite (ZMod pGold) GoldilocksExt4Spec := goldQuarticPoly_monic.finite_adjoinRoot
  Module.Finite.equiv goldilocksExt4ToSpec.symm.toLinearEquiv

theorem goldilocksExt4_card : Fintype.card GoldilocksExt4 = pGold ^ 4 := by
  rw [show Fintype.card GoldilocksExt4 = Fintype.card (Fin 4 → ZMod pGold) from Fintype.ofEquiv_card _,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem injective_algebraMap_goldilocksExt4 :
    Function.Injective (algebraMap (ZMod pGold) GoldilocksExt4) :=
  (algebraMap (ZMod pGold) GoldilocksExt4).injective

/-- A natural strictly between `0` and `p` casts to a nonzero element of `GoldilocksExt4`. -/
theorem goldilocksExt4_natCast_ne_zero {a : ℕ} (ha : 0 < a) (hlt : a < pGold) : (a : GoldilocksExt4) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff GoldilocksExt4 pGold a]
  intro hdvd
  exact absurd (Nat.le_of_dvd ha hdvd) (not_le.mpr hlt)

/-! ## `GoldilocksExt2` inside `GoldilocksExt4` -/

/-- `u = v²` satisfies `u² = 7`. -/
theorem goldQuadPoly_aeval_root_sq :
    aeval (AdjoinRoot.root goldQuarticPoly ^ 2) goldQuadPoly = 0 := by
  have h := AdjoinRoot.aeval_eq (f := goldQuarticPoly) goldQuarticPoly
  rw [AdjoinRoot.mk_self] at h
  conv at h =>
    enter [1, 2]
    unfold goldQuarticPoly
  simp only [map_sub, map_pow, aeval_X, aeval_C] at h
  simp only [goldQuadPoly, map_sub, map_pow, aeval_X, aeval_C]
  rw [← pow_mul]
  exact h

/-- `GoldilocksExt2 = F_p[y]/(y² − 7) → GoldilocksExt4`, `y ↦ v²`: the `u` of the C++ tower
`(a0 + a2 u) + (a1 + a3 u) v` (`lib/algebra/fp_goldilocks4.h:8`), through the specifications. -/
noncomputable def goldilocksExt2ToQuartic : GoldilocksExt2 →ₐ[ZMod pGold] GoldilocksExt4 :=
  (goldilocksExt4ToSpec.symm.toAlgHom.comp
    (AdjoinRoot.liftAlgHom goldQuadPoly (Algebra.ofId _ _) (AdjoinRoot.root goldQuarticPoly ^ 2)
      goldQuadPoly_aeval_root_sq)).comp goldilocksExt2ToSpec.toAlgHom

theorem injective_goldilocksExt2ToQuartic : Function.Injective goldilocksExt2ToQuartic :=
  goldilocksExt2ToQuartic.toRingHom.injective

end GordieHowe
