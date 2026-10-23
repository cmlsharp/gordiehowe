-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Sampler.ComponentReaders
public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.ProofSystem.Ligero.Routing
public import GordieHowe.Foundations.Algebra.AffineForm
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic
public import GordieHowe.ProofSystem.Ligero.Preparation
public import GordieHowe.ProofSystem.GKR.TranscriptRouting
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.Foundations.ReedSolomon.AffineProximity
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.ProofSystem.Ligero.MaskTest.PiecesHonest
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.ProofSystem.GKR.CircuitBudget

@[expose] public section

/-!
# The challenge readers of a source reduction and the largest loads of the circuits

The readers of the GKR rounds of a source circuit's reduction (`SpecReaders.sourceInteraction`), and
the largest load of a challenge round of the relatively packed A circuit at its soundness setups
(`AlgebraCircuit.RelativeSoundSetup.load`), which bounds the loads
of the circuit proofs' readers (`GordieHowe/ProofSystem/Program/Transcript/CircuitCodecs.lean`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.IOP IOP.ProtocolSpec

namespace SpecReaders

section Source

variable {F : Type} [Field F] [Fintype F] {d : ℕ} (r : SPBCS.CReader F)

/-- **The GKR rounds of a source circuit's GKR protocol** (`GordieHowe.GKR.LayeredCircuit.interaction`,
the circuit's GKR protocol `gkrSpec`). -/
def sourceInteraction [DecidableEq F] (S : GordieHowe.GKR.LayeredCircuit F d)
    (nodes : Sumcheck.Nodes F) : SPBCS.SpecReaders (S.interaction nodes).spec := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact SPBCS.SpecReaders.gkrSpec r (.layer Q tail)

theorem sourceInteraction_allLoads [DecidableEq F] (S : GordieHowe.GKR.LayeredCircuit F d)
    (nodes : Sumcheck.Nodes F) :
    (SPBCS.SpecReaders.sourceInteraction r S nodes).AllLoads
      (· ≤ (SPBCS.SpecReaders.gkrLoad r S.outDim)) := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact SPBCS.SpecReaders.gkrSpec_allLoads r _

end Source

end SpecReaders

end GordieHowe.SPBCS

