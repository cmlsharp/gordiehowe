-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Odd
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Applications.Falcon512.Emulated.System.Params
public import GordieHowe.Foundations.Fields.GoldilocksRelative
public import GordieHowe.Foundations.Fields.GoldilocksCoords
public import GordieHowe.Applications.Configuration.AlgebraSetups
public import GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Program
public import GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Plan
public import GordieHowe.Language.Export.Valid

@[expose] public section

/-!
# GordieHowe: the interpretation and the tableau of `Falcon512.Ring.Carrier.ROMParams`

The interpretation and the Ligero numbers of the realized program of the Falcon ring carrier at the ROM
parameters (`GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Program.program`, export `b65a4929`: one domain
`A` over Goldilocks², one GKR circuit `c.A`, one batch `magnitudes.s2`), whose domain proof is the
generic per-field one (`GordieHowe/Applications/Falcon512/Ring/Carrier/ROMParams/ProofSystem.lean`):

* **the interpretation** (`interpROM`): the field Goldilocks² (`GoldilocksExt2`, the registry
  entry `goldilocksExt2Entry`), constants decoded as casts of naturals, the integer reading the
  constant coordinate, the node `GF(p^1)` the prime subfield `F_p`, every other node the whole field;
  the program's opaque values take no arguments (read from the statement), so the opaque functions
  are never read;
* **the Ligero numbers** (`gold2K512R2Cert`): the shared Goldilocks² tableau at
  `(rate, t, block_enc) = (5, 97, 3583)`, `(N, k) = (2560, 512)`, two low-degree repetitions
  (`Tableau.gold2K512R2Shape`), the normalized Goldilocks subgroup points of the C++
  (`Shape.goldPoints`), the mask test at agreement threshold `1147` with `101777974921` exceptional
  challenges (`GordieHowe.Tableau.gold2K512R2MaskTest`); the commit error `(101777974921/(|F| − 1))^2`
  (`Tableau.gold2K512R2Bounds.commit`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open RealizedProgram.Export RelativePacking Ligero.MaskRow
open Generated.Falcon512.Ring.Carrier.ROMParams.Program (program)
open scoped NNReal

/-! ## The interpretation -/

/-- **The interpretation of the program of the Falcon ring carrier at the ROM parameters**: every field identifier is
Goldilocks² (the program has one field); the opaque functions are never read (the program's opaque
values take no arguments). -/
abbrev interpROM : RealizedProgram.Interp := ⟨fun _ => RealizedProgram.gold2, fun _ _ _ => 0⟩

instance (n : ℕ) : ExpChar (interpROM.field n).K pGold :=
  inferInstanceAs (ExpChar GoldilocksExt2 pGold)

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
