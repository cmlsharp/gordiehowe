-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.Foundations.Fields.GF2_128Selection
public import GordieHowe.Foundations.Fields.GF2_256Selection
public import GordieHowe.Foundations.Fields.GoldilocksRoots

@[expose] public section

/-!
# Concrete GKR interpolation nodes

The implementation's `Field::poly_evaluation_point` is the source of the three points used by the
GKR sumcheck interpolation. In `lib/gf2k/gf2_128.h:136-141` and `lib/gf2k/gf2_256.h:130-135`, the
binary fields set `poly_evaluation_points_[0] = 0` and `poly_evaluation_points_[i] = g ^ (i - 1)`
for `i ≥ 1`, so the three points are `[0, 1, g]`, where `g` is the subfield generator; in
`lib/algebra/fp_goldilocks.h:186-188,386-388`, the Goldilocks base field and its quadratic extension
use `[0, 1, 2]`. The shared verifier consumes these points through `dot_interpolation`
(`lib/zk/zk_common.h:249`).

The binary-field generator is the polynomial-basis generator initialized by
C++ `of_scalar_field(0b10)` (`lib/gf2k/gf2_128.h:111-124`, `lib/gf2k/gf2_256.h:109-117`), whose formal
identification is `gf2_128OfBitVec_two`; it is not the natural cast `(2 :
GF2_128)`, which is zero in characteristic two.  The formal `g` below is the
same subfield generator and its order certificate supplies all required
distinctness facts.
-/

namespace GordieHowe.GKR.ConcreteNodes
open IOP

open GordieHowe.IOP

/-! ## The binary fields -/

/-- The nodes `![0, 1, g]` from any `g ∉ {0, 1}`. -/
def zeroOneGen {F : Type} [Field F] (g : F) (h0 : g ≠ 0) (h1 : g ≠ 1) :
    Sumcheck.Nodes F where
  point := ![0, 1, g]
  injective := by
    intro i j hij
    have h01 : (0 : F) ≠ 1 := zero_ne_one
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  zero := rfl
  one := rfl

theorem gf2_128SubfieldGen_ne_zero : gf2_128SubfieldGen ≠ (0 : GF2_128) := by
  exact pow_ne_zero _ gf2_128_root_ne_zero

theorem gf2_128SubfieldGen_ne_one : gf2_128SubfieldGen ≠ (1 : GF2_128) := by
  intro h
  have ho := orderOf_gf2_128SubfieldGen
  rw [h, orderOf_one] at ho
  norm_num at ho

theorem gf2_256SubfieldGen_ne_one : gf2_256SubfieldGen ≠ (1 : GF2_256) := by
  intro h
  have ho := orderOf_gf2_256SubfieldGen
  rw [h, orderOf_one] at ho
  norm_num at ho

/-- The GKR sumcheck nodes of `GF2_128`: `poly_evaluation_points_ = [0, 1, g, …]`
(`lib/gf2k/gf2_128.h:136-141`). -/
def gf2_128Nodes : Sumcheck.Nodes GF2_128 :=
  zeroOneGen gf2_128SubfieldGen gf2_128SubfieldGen_ne_zero gf2_128SubfieldGen_ne_one

/-- The GKR sumcheck nodes of `GF2_256`: `poly_evaluation_points_ = [0, 1, g, …]`
(`lib/gf2k/gf2_256.h:130-135`). -/
def gf2_256Nodes : Sumcheck.Nodes GF2_256 :=
  zeroOneGen gf2_256SubfieldGen gf2_256SubfieldGen_ne_zero gf2_256SubfieldGen_ne_one

/-! ## Goldilocks extension -/

theorem goldilocksExt2_two_ne_zero : (2 : GoldilocksExt2) ≠ 0 := by
  apply goldilocksExt2_natCast_ne_zero <;> norm_num [pGold_eq]

theorem goldilocksExt2_two_ne_one : (2 : GoldilocksExt2) ≠ 1 := by
  intro h
  have hz : (1 : GoldilocksExt2) = 0 := by
    calc
      (1 : GoldilocksExt2) = (2 : GoldilocksExt2) - 1 := by ring
      _ = 0 := by rw [h]; ring
  exact (one_ne_zero : (1 : GoldilocksExt2) ≠ 0) hz

theorem goldilocksExt2Nodes_injective :
    Function.Injective (fun i : Fin 3 => ![(0 : GoldilocksExt2), 1, 2] i) := by
  intro i j hij
  have hzero : (0 : GoldilocksExt2) ≠ 2 := Ne.symm goldilocksExt2_two_ne_zero
  have hone : (1 : GoldilocksExt2) ≠ 2 := Ne.symm goldilocksExt2_two_ne_one
  have hzero' : (2 : GoldilocksExt2) ≠ 0 := goldilocksExt2_two_ne_zero
  have hone' : (2 : GoldilocksExt2) ≠ 1 := goldilocksExt2_two_ne_one
  fin_cases i <;> fin_cases j <;> simp_all

/-- The `[0,1,2]` interpolation nodes used by the Goldilocks C++ backend. -/
def goldilocksExt2Nodes : Sumcheck.Nodes GoldilocksExt2 where
  point := fun i => ![(0 : GoldilocksExt2), 1, 2] i
  injective := goldilocksExt2Nodes_injective
  zero := by simp
  one := by simp

end GordieHowe.GKR.ConcreteNodes
