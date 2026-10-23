-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Odd
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.Foundations.Fields.GoldilocksQuarticRelative
public import GordieHowe.Foundations.Fields.GoldilocksCoords
public import GordieHowe.Applications.Configuration.AlgebraSetups
public import GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Program
public import GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Plan
public import GordieHowe.Language.Export.Valid

@[expose] public section

/-!
# GordieHowe: the interpretation and the tableau of `Falcon512.Ring.Carrier.QROMParams`

The interpretation and the Ligero numbers of the realized program of the Falcon ring carrier at the QROM parameters
(`GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Program.program`, export `b65a4929`: one domain `A` over
Goldilocks⁴, one GKR circuit `c.A`, one batch `magnitudes.s2`), whose domain proof is the generic
per-field one (`GordieHowe/Applications/Falcon512/Ring/Carrier/QROMParams/ProofSystem.lean`):

* **the interpretation** (`interpQROM`): the field Goldilocks⁴ (`GoldilocksExt4`, the registry
  entry `goldilocksExt4Entry`), constants decoded as casts of naturals, the integer reading the
  constant coordinate, the node `GF(p^1)` the prime subfield `F_p`, every other node the whole field;
  the program's opaque values take no arguments (read from the statement), so the opaque functions
  are never read;
* **the Ligero numbers** (`gold4K512Cert`): the shared Goldilocks⁴ tableau with `k = 512`
  (`Tableau.gold4K512Shape`) at `(rate, t, block_enc) = (6, 201, 4095)`, `(N, k) = (3072, 512)`,
  the normalized Goldilocks subgroup points of the C++ (`Shape.goldPoints`), the mask test at agreement
  threshold `1418` with `1030262` exceptional challenges (`GordieHowe.Tableau.gold4K512MaskTest`); the commit
  error `1030262/(|F| − 1)` (`Tableau.gold4K512Bounds.commit`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open RealizedProgram.Export RelativePacking Ligero.MaskRow
open Generated.Falcon512.Ring.Carrier.QROMParams.Program (program)
open scoped NNReal

/-! ## The interpretation -/

/-- **The interpretation of the program of the Falcon ring carrier at the QROM parameters**: every field identifier is
Goldilocks⁴ (the program has one field); the opaque functions are never read (the program's opaque
values take no arguments). -/
abbrev interpQROM : RealizedProgram.Interp := ⟨fun _ => RealizedProgram.gold4, fun _ _ _ => 0⟩

instance (n : ℕ) : ExpChar (interpQROM.field n).K pGold :=
  inferInstanceAs (ExpChar GoldilocksExt4 pGold)

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
