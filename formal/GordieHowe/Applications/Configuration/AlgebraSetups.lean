-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.MaskTest.PiecesHonest
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.ProofSystem.Ligero.Preparation
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Foundations.Algebra.AffineForm
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic
public import GordieHowe.ProofSystem.GKR.TranscriptRouting
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.Foundations.ReedSolomon.AffineProximity
public import GordieHowe.ProofSystem.GKR.OrdinaryCompleteness
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.ProofSystem.Ligero.HVZK
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.MaskedConstraintList
public import GordieHowe.ProofSystem.Ligero.UntestedMaskRow
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.Foundations.Fields.GF2_128
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.ProofSystem.GKR.CircuitBudget
public import GordieHowe.Foundations.Fields.GF2_256
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Applications.Falcon512.PoP.Relation
public import GordieHowe.Foundations.Fields.GF2_128Conv
public import GordieHowe.Applications.Rows.NativeLinear
public import GordieHowe.Applications.Rows.MAC
public import GordieHowe.Foundations.Algebra.DFT
public import GordieHowe.Foundations.Algebra.DFTExtra
public import GordieHowe.Foundations.Algebra.ConvMatrix
public import GordieHowe.Headline
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import GordieHowe.Applications.Falcon512.Circuits.Hash
public import GordieHowe.Applications.Falcon512.Spec.Decoded
public import GordieHowe.Applications.Falcon512.Spec.Encoding
public import GordieHowe.Foundations.Algebra.Conv
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Applications.Configuration.Witness
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebraHonest
public import GordieHowe.Applications.Falcon512.Circuits.NativeAlgebra
public import GordieHowe.Foundations.Fields.GF2_128Selection
public import GordieHowe.Applications.Keccak.Gadgets.Basic
public import GordieHowe.ProofSystem.Zerocheck.ZeroOneTwoNodes
public import GordieHowe.Foundations.Fields.GF2_256Conv
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.Applications.Falcon512.Emulated.Rows
public import GordieHowe.Foundations.ToMathlib.FinFlatten
public import GordieHowe.Applications.Falcon512.Spec.KeyNTT
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebra
public import GordieHowe.ProofSystem.GKR.ConcreteNodes
public import GordieHowe.Foundations.Fields.GoldilocksRoots
public import GordieHowe.Applications.Falcon512.Spec.Completeness
public import GordieHowe.Language.Realizations.Bits
public import Mathlib.Algebra.Field.Subfield.Basic
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra
public import GordieHowe.Applications.MLDSA44.PoP.Native.Algebra
public import GordieHowe.Applications.MLDSA44.Emulated.Rows
public import GordieHowe.Applications.MLDSA44.PoP.Relation
public import GordieHowe.Applications.MLDSA44.PoP.Compose
public import GordieHowe.Applications.MLDSA44.Fields.GF2_128
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20Relative
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9Relative
public import GordieHowe.Foundations.Fields.GoldilocksQuarticRelative
public import GordieHowe.Foundations.Fields.GoldilocksRelative
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11Relative
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6Relative

@[expose] public section

/-!
# The Reed–Solomon points of the Goldilocks extensions

The C++ encoder evaluates the Ligero code of a Goldilocks extension (`GoldilocksExt2`,
`GoldilocksExt4`) at the powers `P_i = g ^ bitrev_32(i)` of `g = goldilocks_root_2_32()`, a
primitive `2^32`-th root of unity of the Goldilocks prime field, embedded in the extension
(`BasicPqFpReedSolomon`). The verifier of the mask test recombines the mask pieces at the
normalized point `Y_i = (P_i − P_0) / (P_1 − P_0)` (`split_points`, `lib/ligero/ligero_param.h`).
This file defines the points `Y_i` (`Ligero.Relative.Shape.goldPoints`, the normalization of the
subgroup points) and proves that they lie in the prime subfield (`goldPoints_mem`), as the relative
layouts over a Goldilocks extension require of their evaluation points. The Lean code of a
Goldilocks tableau lies at the points `Y_i`. Since `Y` is an affine function of `P` with nonzero
slope, a polynomial of degree `< k` in `P` is one of degree `< k` in `Y`, so this code has the
codewords and the message encoding of the C++ code at the points `P_i`, and its mask test
recombines at the C++ point `Y_i`.
-/

namespace GordieHowe

open IOP RelativePacking

/-! ### The Goldilocks points -/

namespace Ligero.Relative.Shape

/-- **The C++ Reed–Solomon points of a Goldilocks extension `F`**: `subgroupPoints` at
`goldilocks_root_2_32()` (`goldRootStored`, embedded), the domain of `BasicPqFpReedSolomon`
(`SubgroupReedSolomonFactory`, `lib/algebra/reed_solomon_fp.h`, at
`goldilocks_root_2_32()` and `K = 32`, applied componentwise). -/
def goldSubgroupPoints (F : Type) [Field F] [Algebra (ZMod pGold) F] : Points F (2 ^ 32) :=
  subgroupPoints (isPrimitiveRoot_goldRootStored.map_of_injective
    (algebraMap (ZMod pGold) F).injective)

/-- **The Ligero points of a Goldilocks extension `F`**: the normalization of the C++
Reed–Solomon points `goldSubgroupPoints` (`Points.normalize`), the C++ split-mask evaluation points
`(P_i − P_0) / (P_1 − P_0)` (`split_points`, `lib/ligero/ligero_param.h` lines 526-538). -/
def goldPoints (F : Type) [Field F] [Algebra (ZMod pGold) F] : Points F (2 ^ 32) :=
  (goldSubgroupPoints F).normalize (by norm_num)

/-- The C++ Reed–Solomon points of a Goldilocks extension lie in the prime subfield. -/
theorem goldSubgroupPoints_mem {F : Type} [Field F] [Algebra (ZMod pGold) F] [ExpChar F pGold]
    (a : ℕ) : (goldSubgroupPoints F).pt a ∈ fixedField F pGold 1 := by
  change algebraMap (ZMod pGold) F goldRootStored ^ bitRevNat 32 a ∈ _
  rw [← map_pow]
  exact algebraMap_mem_fixedField_one _

/-- The Goldilocks points lie in the prime subfield. -/
theorem goldPoints_mem {F : Type} [Field F] [Algebra (ZMod pGold) F] [ExpChar F pGold] (a : ℕ) :
    (goldPoints F).pt a ∈ fixedField F pGold 1 :=
  div_mem (sub_mem (goldSubgroupPoints_mem a) (goldSubgroupPoints_mem 0))
    (sub_mem (goldSubgroupPoints_mem 1) (goldSubgroupPoints_mem 0))

end Ligero.Relative.Shape

end GordieHowe
