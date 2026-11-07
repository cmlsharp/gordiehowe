-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweCerts.Generated.Falcon512.Native.ROMParams.Program
import GordieHowe.Language.Realizations.Circuit.RelEntry
import GordieHowe.Applications.FieldInterps.Basic

/-!
# Synthetic node tables for the relational check's unit tests

The code arithmetic of Falcon-512 native's `F_q^9`, the synthetic node tables over the inputs of
its circuit `1` (`GKRRelData/Synth*.ghc`, loaded by `load_ghc`) that the tests of
`GordieHoweTest.GKRRelUnit` read, and `mutFam`, which changes one entry's family record. The tests
are split over several modules so that they build in parallel.
-/

namespace GordieHoweTest.GKRRelUnit

open GordieHowe GordieHowe.Twin GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold
open GordieHowe.Generated.Falcon512.Native.ROMParams.Program

/-- The code arithmetic of `F_q^9`, with the prime-subfield fast path. -/
def ar : CodeArith := CodeArith.withPrime RealizedProgram.fq9Code.arith 12289

load_ghc "GKRRelData/Synth.ghc" "ce7d4bd2f6a8b655"

load_ghc "GKRRelData/SynthWire.ghc" "5c999d4e0f278cf8"

load_ghc "GKRRelData/SynthCode.ghc" "0a1bd2e198a9c00e"

load_ghc "GKRRelData/SynthAux.ghc" "611db00570612408"

load_ghc "GKRRelData/SynthMuxAux.ghc" "3d38ccc883558e3a"

load_ghc "GKRRelData/SynthBlock.ghc" "0dbf8410197f6f3a"

load_ghc "GKRRelData/SynthLate.ghc" "1b0c221e2147d260"

load_ghc "GKRRelData/SynthAssert.ghc" "0095cb1e3035d63d"

load_ghc "GKRRelData/SynthUncutOp.ghc" "7426965583fd5246"

load_ghc "GKRRelData/SynthClone.ghc" "3a7c9e546722be4f"

/-- Entry `k`'s family record changed by `f`. -/
def mutFam (cd : CircuitData) (k : ℕ) (f : FamCert → FamCert) : CircuitData :=
  { cd with entries := cd.entries.zipIdx.map (fun p =>
      cond (Nat.beq p.2 k) { p.1 with fam := p.1.fam.map f } p.1) }

end GordieHoweTest.GKRRelUnit
