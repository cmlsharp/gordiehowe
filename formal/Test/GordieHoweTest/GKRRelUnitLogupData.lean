-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRRelUnitData

/-!
# The range LogUp record of the relational check's family tests

A range LogUp record for circuit `1`'s entry `3` (`.logup 1 0`, 5120 needles), reconstructed by a
scratch generator from the committed DAG with its three value leaves appended
(`GKRRelData/SynthLogup.ghc`), and the mutations of it that the family tests apply.
-/

namespace GordieHoweTest.GKRRelUnit

open GordieHowe GordieHowe.Twin GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold
open GordieHowe.Generated.Falcon512.Native.ROMParams.Program

load_ghc "GKRRelData/SynthLogup.ghc" "335f30d99db967c3"

/-- A range LogUp record changed by `f`. -/
def mutLogup (f : LogupCert → LogupCert) : FamCert → FamCert
  | .logup lc => .logup (f lc)
  | x => x

/-- Inner node `k`'s kids swapped. -/
def swapKids (k : ℕ) (tr : FracTree) : FracTree :=
  ⟨tr.dens, tr.inner.zipIdx.map
    (fun p => cond (Nat.beq p.2 k) ⟨p.1.r, p.1.l, p.1.num, p.1.den⟩ p.1)⟩

end GordieHoweTest.GKRRelUnit
