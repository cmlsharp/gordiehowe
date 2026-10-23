-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Algebra.ZMod
public import GordieHowe.Foundations.Fields.PolyRep
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.ComputeDegree
public import GordieHowe.Foundations.Algebra.PowMod
public import GordieHowe.Foundations.Algebra.PowModOrder
public import GordieHowe.Applications.Params
public import GordieHowe.Foundations.ToMathlib.Polynomial

@[expose] public section

/-!
# The Goldilocks field, `F_{p²}`

`F_{p²}` for the Goldilocks prime `p = 2^64 − 2^32 + 1`, as `ZMod p [X] / (X² − 7)` (`7` is a
non-residue mod `p`). The flagship C++ (commit 31cb860) runs the Falcon emulated arm over this
field. The A circuit's no-wrap conditions are about the characteristic `p`; its challenge errors
are about the field size `p²`.

Primality of `p` is a Lucas certificate with witness `7` (`lib/algebra/fp_goldilocks.h:265`,
`Fp64G2::kW = 7`, "generates `F_p^*`"), the same witness the C++ uses as its non-residue generator:
`p − 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`, and `7` has order `p − 1` (checked at each of the six
prime factors by a `powMod` certificate, `GordieHowe/Foundations/Algebra/PowMod.lean`). The factor-`2` check,
`7^((p−1)/2) ≠ 1`, in fact computes the exact value `−1` (`pow_7_pGold_sub_one_div_two_eq_neg_one`),
which is reused twice: as Euler's criterion witness that `7` is a quadratic non-residue (so `X² − 7`
is irreducible, `irreducible_X_sq_sub_C_of_not_isSquare` in `GordieHowe.Foundations.ToMathlib.Polynomial`), and, in
`GordieHowe/Foundations/Fields/GoldilocksRoots.lean`, to certify the order of the flagship's `2^32`-th root of unity
without a second exponentiation certificate.
-/

namespace GordieHowe

open Polynomial

theorem pGold_one_lt : 1 < pGold := by rw [pGold_eq]; norm_num

/-- `p − 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`, the factorization the Lucas
certificate uses. The five odd factors are the Fermat primes `F₀, …, F₄`. -/
theorem pGold_sub_one : pGold - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := by
  unfold pGold; norm_num

/-- Every prime factor of `p − 1` is one of the six primes in its
factorization. -/
theorem pGold_sub_one_prime_dvd {q : ℕ} (hq : q.Prime) (hdvd : q ∣ pGold - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
  rw [pGold_sub_one] at hdvd
  rcases hq.dvd_mul.mp hdvd with h65537c | h65537
  · rcases hq.dvd_mul.mp h65537c with h257c | h257
    · rcases hq.dvd_mul.mp h257c with h17c | h17
      · rcases hq.dvd_mul.mp h17c with h5c | h5
        · rcases hq.dvd_mul.mp h5c with h32 | h3
          · exact Or.inl <| (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h32)
          · exact Or.inr <| Or.inl <| (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3
        · exact Or.inr <| Or.inr <| Or.inl <| (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h17
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h257
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h65537

/-- `7 ^ (p − 1) ≡ 1` and `7 ^ ((p − 1) / q) ≢ 1` for each prime factor `q` of
`p − 1`, computed by binary modular exponentiation (`decide +kernel` checks
the kernel's native `Nat` arithmetic directly, sidestepping the elaborator's
recursion-depth guard). -/
theorem powMod_7_pGold_sub_one : powMod 7 (pGold - 1) pGold = 1 := by decide +kernel

/-- The factor-`2` check computes the exact value `p − 1` (i.e. `−1`), not
merely a value other than `1`: reused by `goldQuadPoly_irreducible` below and
by the root-of-unity order certificates in `GordieHowe/Foundations/Fields/GoldilocksRoots.lean`. -/
theorem powMod_7_pGold_sub_one_div_two :
    powMod 7 ((pGold - 1) / 2) pGold = pGold - 1 := by decide +kernel

theorem powMod_7_pGold_sub_one_div_two_ne_one :
    powMod 7 ((pGold - 1) / 2) pGold ≠ 1 := by
  rw [powMod_7_pGold_sub_one_div_two, pGold_eq]; norm_num

theorem powMod_7_pGold_sub_one_div_three : powMod 7 ((pGold - 1) / 3) pGold ≠ 1 := by
  decide +kernel

theorem powMod_7_pGold_sub_one_div_five : powMod 7 ((pGold - 1) / 5) pGold ≠ 1 := by
  decide +kernel

theorem powMod_7_pGold_sub_one_div_seventeen : powMod 7 ((pGold - 1) / 17) pGold ≠ 1 := by
  decide +kernel

theorem powMod_7_pGold_sub_one_div_two_five_seven :
    powMod 7 ((pGold - 1) / 257) pGold ≠ 1 := by decide +kernel

theorem powMod_7_pGold_sub_one_div_sixtyfivethousandfivehundredthirtyseven :
    powMod 7 ((pGold - 1) / 65537) pGold ≠ 1 := by decide +kernel

/-- Lucas primality (`lucas_primality`), witness `7`: the same base the C++
uses as its non-residue generator (`Fp64G2::kW`, `lib/algebra/fp_goldilocks.h:265`). -/
theorem pGold_prime : Nat.Prime pGold := by
  apply lucas_primality pGold (7 : ZMod pGold) (powMod_eq_one_of_eq powMod_7_pGold_sub_one)
  intro q hq hdvd
  rcases pGold_sub_one_prime_dvd hq hdvd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact powMod_ne_one_of_ne pGold_one_lt powMod_7_pGold_sub_one_div_two_ne_one
  · exact powMod_ne_one_of_ne pGold_one_lt powMod_7_pGold_sub_one_div_three
  · exact powMod_ne_one_of_ne pGold_one_lt powMod_7_pGold_sub_one_div_five
  · exact powMod_ne_one_of_ne pGold_one_lt powMod_7_pGold_sub_one_div_seventeen
  · exact powMod_ne_one_of_ne pGold_one_lt powMod_7_pGold_sub_one_div_two_five_seven
  · exact powMod_ne_one_of_ne pGold_one_lt
      powMod_7_pGold_sub_one_div_sixtyfivethousandfivehundredthirtyseven

instance instFactPrimePGold : Fact (Nat.Prime pGold) := ⟨pGold_prime⟩

theorem pow_7_pGold_sub_one_div_two_ne_one : (7 : ZMod pGold) ^ ((pGold - 1) / 2) ≠ 1 :=
  powMod_ne_one_of_ne pGold_one_lt powMod_7_pGold_sub_one_div_two_ne_one

/-- Euler's-criterion value: `7` is a non-residue mod `p`. Reused in
`GordieHowe/Foundations/Fields/GoldilocksRoots.lean` for the order of `goldilocks_root_2_32`. -/
theorem pow_7_pGold_sub_one_div_two_eq_neg_one : (7 : ZMod pGold) ^ ((pGold - 1) / 2) = -1 :=
  powMod_eq_neg_one_of_eq (by rw [pGold_eq]; norm_num) powMod_7_pGold_sub_one_div_two

theorem seven_ne_zero_pGold : (7 : ZMod pGold) ≠ 0 := by
  have h : ((7 : ℕ) : ZMod pGold) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod pGold) pGold 7]
    intro hdvd
    have h7 : pGold ≤ 7 := Nat.le_of_dvd (by norm_num) hdvd
    rw [pGold_eq] at h7
    omega
  exact_mod_cast h

theorem pGold_div_two : pGold / 2 = (pGold - 1) / 2 := by rw [pGold_eq]

/-- `7` is not a square mod `p` (Euler's criterion, `ZMod.euler_criterion`), so `X² − 7` has no
root. -/
theorem seven_not_isSquare_pGold : ¬ IsSquare (7 : ZMod pGold) := by
  rw [ZMod.euler_criterion pGold seven_ne_zero_pGold, pGold_div_two]
  exact pow_7_pGold_sub_one_div_two_ne_one

/-- The defining polynomial `X² − 7`. -/
noncomputable def goldQuadPoly : (ZMod pGold)[X] := X ^ 2 - C 7

theorem goldQuadPoly_monic : goldQuadPoly.Monic := by
  unfold goldQuadPoly; monicity!

theorem goldQuadPoly_natDegree : goldQuadPoly.natDegree = 2 := by
  unfold goldQuadPoly; compute_degree!

/-- `7` is a quadratic non-residue mod `p`, so `X² − 7` has no root and, being of degree `2`, is
irreducible (`irreducible_X_sq_sub_C_of_not_isSquare`). -/
theorem goldQuadPoly_irreducible : Irreducible goldQuadPoly := by
  unfold goldQuadPoly
  exact irreducible_X_sq_sub_C_of_not_isSquare seven_not_isSquare_pGold

instance instFactIrreducibleGoldQuadPoly : Fact (Irreducible goldQuadPoly) :=
  ⟨goldQuadPoly_irreducible⟩

/-- The specification `F_p[X] / (X² − 7)`, an `AdjoinRoot` quotient. -/
abbrev GoldilocksExt2Spec : Type := AdjoinRoot goldQuadPoly

noncomputable instance : Field GoldilocksExt2Spec := AdjoinRoot.instField

/-- The facts that make the coefficient-vector operations of `GoldilocksExt2` a field. -/
theorem goldilocksExt2_polySpec :
    PolyRep.Spec (PolyRep.binomial (7 : ZMod pGold) : Fin 2 → ZMod pGold) (pGold) goldQuadPoly :=
  PolyRep.Spec.of_binomial goldQuadPoly_irreducible (Nat.card_zmod _) (by norm_num)
    (by rw [pGold_eq]; norm_num)

/-! ## The executable field -/

/-- `F_p[X] / (X² − 7)`: an element is its vector of coefficients in the power basis
`1, X, …, X^1` (the layout of the C++ class), with the operations of `GordieHowe.Foundations.Fields.PolyRep`. -/
def GoldilocksExt2 : Type := Vector (ZMod pGold) 2

/-- The operations of `GoldilocksExt2`, typed on `GoldilocksExt2`. -/
abbrev goldilocksExt2Ops : ExecOps GoldilocksExt2 := PolyRep.ops (PolyRep.binomial (7 : ZMod pGold)) (pGold)

instance : Field GoldilocksExt2 := goldilocksExt2Ops.field goldilocksExt2_polySpec.isField

instance : DecidableEq GoldilocksExt2 := inferInstanceAs (DecidableEq (Vector (ZMod pGold) 2))

instance : Fintype GoldilocksExt2 := Fintype.ofEquiv (Fin 2 → ZMod pGold) PolyRep.coordsEquiv.symm

instance : Repr GoldilocksExt2 := inferInstanceAs (Repr (Vector (ZMod pGold) 2))

/-- The coordinates of an element: its stored coefficient vector, coordinate `i` the coefficient
of `X ^ i`. -/
def goldilocksExt2Coords : GoldilocksExt2 ≃ (Fin 2 → ZMod pGold) := PolyRep.coordsEquiv

/-- The power-basis map `GoldilocksExt2 → GoldilocksExt2Spec` as a ring isomorphism. -/
noncomputable def goldilocksExt2RingEquiv : GoldilocksExt2 ≃+* GoldilocksExt2Spec :=
  ExecOps.Hom.ringEquiv (o := goldilocksExt2Ops) goldilocksExt2_polySpec.hom
    (PolyRep.toSpec_bijective goldQuadPoly_monic goldQuadPoly_natDegree).2

instance : CharP GoldilocksExt2Spec pGold :=
  charP_of_injective_algebraMap (algebraMap (ZMod pGold) GoldilocksExt2Spec).injective pGold

instance : CharP GoldilocksExt2 pGold :=
  charP_of_injective_ringHom (f := goldilocksExt2RingEquiv.symm.toRingHom) (RingEquiv.injective _) pGold

instance : Algebra (ZMod pGold) GoldilocksExt2 := ZMod.algebra _ pGold

/-- **The power-basis map** `GoldilocksExt2 ≃ₐ[ZMod pGold] GoldilocksExt2Spec`: coefficient `i` to the coefficient of
`root ^ i` (`PolyRep.toSpec`). -/
noncomputable def goldilocksExt2ToSpec : GoldilocksExt2 ≃ₐ[ZMod pGold] GoldilocksExt2Spec :=
  AlgEquiv.ofRingEquiv (f := goldilocksExt2RingEquiv) fun x => by
    have := RingHom.congr_fun (Subsingleton.elim (goldilocksExt2RingEquiv.toRingHom.comp
      (algebraMap (ZMod pGold) GoldilocksExt2)) (algebraMap (ZMod pGold) GoldilocksExt2Spec)) x
    exact this

theorem goldilocksExt2ToSpec_apply (x : GoldilocksExt2) : goldilocksExt2ToSpec x = PolyRep.toSpec goldQuadPoly (n := 2) x := rfl

/-- The generator `X`. -/
def goldilocksExt2Gen : GoldilocksExt2 := PolyRep.gen

theorem goldilocksExt2ToSpec_gen : goldilocksExt2ToSpec goldilocksExt2Gen = AdjoinRoot.root goldQuadPoly :=
  PolyRep.toSpec_gen (by norm_num)

instance : Module.Finite (ZMod pGold) GoldilocksExt2 :=
  have : Module.Finite (ZMod pGold) GoldilocksExt2Spec := goldQuadPoly_monic.finite_adjoinRoot
  Module.Finite.equiv goldilocksExt2ToSpec.symm.toLinearEquiv

theorem goldilocksExt2_card : Fintype.card GoldilocksExt2 = pGold ^ 2 := by
  rw [show Fintype.card GoldilocksExt2 = Fintype.card (Fin 2 → ZMod pGold) from Fintype.ofEquiv_card _,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem injective_algebraMap_goldilocksExt2 :
    Function.Injective (algebraMap (ZMod pGold) GoldilocksExt2) :=
  (algebraMap (ZMod pGold) GoldilocksExt2).injective

end GordieHowe
