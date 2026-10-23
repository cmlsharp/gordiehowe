-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Interp
public import GordieHowe.Foundations.Algebra.RelativePackingAdditive
public import GordieHowe.Language.Export.Valid
public import GordieHowe.Foundations.Fields.GF2_128Relative
public import GordieHowe.Foundations.Fields.GF2_128Dual
public import GordieHowe.Foundations.Fields.GF2_128Skip
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.Interp
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Plan
public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Valid
public import GordieHowe.ProofSystem.Program.FieldHonest
public import GordieHowe.ProofSystem.Program.FieldPackings

@[expose] public section

/-!
# GordieHowe: the interpretation and domain `H` of `MLDSA44.Emulated.ROMParams`

The interpretation of the realized program of the emulated ML-DSA-44 proof of possession at the
ROM parameters
(`GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Program.program`) and its domain `H`'s circuit `c.H` with its
nodes:

* **the interpretation** (`interp`): field `0` is Goldilocks² (`GordieHowe.RealizedProgram.gold2`, the
  registry entry `goldilocksExt2Entry`; the node `GF(p^1)` the prime subfield), field `1` is
  `GF(2^128)` (`gf128`, `GordieHowe/Applications/FieldInterps/Basic.lean`); the opaque function
  `mac.target_bits` returns bit `i` of the integer reading of its argument, the MAC tag's message in
  `GF(2^128)` (`targetBitsFn`), and the program's other opaque values take no arguments (`tr`,
  `key.a`, `key.t1`, read from the statement).

* **domain `H`'s ready data** (`readyH`, `GordieHowe.RealizedProgram.FieldReady`): the packing `gf128Packing` and the
  tableau `gf128K282R2Cert` with the checks `fieldOkH` by `decide +kernel`, from which domain `H`'s
  proof is the generic per-field one (`GordieHowe.RealizedProgram.fieldProof`).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams.HashField

open RealizedProgram.Export RelativePacking Ligero.MaskRow
open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open scoped NNReal

/-! ## The interpretation -/

/-- **The interpretation of the program of `MLDSA44.Emulated.ROMParams`**: field `0` is Goldilocks²
(`RealizedProgram.gold2`), field `1` (and any other identifier) `GF(2^128)`; the opaque
functions `targetBitsFn`. -/
abbrev interp : RealizedProgram.Interp := RealizedProgram.mldsaInterp RealizedProgram.gold2

/-! ## Domain `H`'s ready data -/

/-- Domain `H`'s packing facts. -/
abbrev fieldPkH : (interp.field (program.domainField 1)).Packing := RealizedProgram.gf128Packing

/-- **Domain `H`'s checks** (`RealizedProgram.fieldOkB`). -/
theorem fieldOkH : program.fieldOkB (I := interp) 1 Generated.MLDSA44.Emulated.ROMParams.Plan.plan fieldPkH
    RealizedProgram.gf128K282R2Cert = true := by
  decide +kernel

/-- **Domain `H`'s ready data** (`RealizedProgram.FieldReady`). -/
def readyH :
    program.FieldReady interp 1 Generated.MLDSA44.Emulated.ROMParams.Plan.plan :=
  ⟨fieldPkH, RealizedProgram.gf128K282R2Cert, fieldOkH, Generated.MLDSA44.Emulated.ROMParams.Valid.wellFormed⟩

end GordieHowe.MLDSA44.Emulated.ROMParams.HashField
