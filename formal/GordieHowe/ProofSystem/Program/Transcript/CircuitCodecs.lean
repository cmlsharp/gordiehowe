-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Transcript.Readers
public import GordieHowe.SPBCS.Format.SpecWrites
public import GordieHowe.ProofSystem.Ligero.AgreementThreshold
public import GordieHowe.Model.IOP.AppendView
public import GordieHowe.Foundations.Algebra.RelativePackingBijective
public import GordieHowe.ProofSystem.Ligero.MaskTest.PiecesHonest
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
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
public import GordieHowe.Applications.Falcon512.Circuits.HashStep
public import GordieHowe.Applications.Keccak.HashCircuit.SkipCompleteness
public import GordieHowe.ProofSystem.GKR.HonestTranscript
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.ProofSystem.Ligero.ShapeEncoding
public import GordieHowe.Foundations.ReedSolomon.SubfieldInterpolation
public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.ProofSystem.Ligero.HVZK
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import GordieHowe.ProofSystem.FieldProof.MaskedRowReduction
public import GordieHowe.Applications.Keccak.HashCircuit.SkipHVZK
public import GordieHowe.ProofSystem.GKR.OrdinaryCompleteness
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.ProofSystem.GKR.CircuitBudget
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.Ligero.Tableau

@[expose] public section

/-!
# Write codecs and challenge readers of the circuit proofs' Ligero phases

The codecs of the prover messages (`SpecWrites`) and the readers of the challenge rounds
(`SpecReaders`) of relatively packed Ligero at agreement threshold `A`, the pieces the circuit
proofs' codecs and readers are assembled from:

- the size conditions on the parameters (`LigeroFits`);
- Ligero at agreement threshold `A`: the commit rounds (`GordieHowe.Ligero.AgreementThreshold.commitSpec`: the
  low-degree challenge and response, `SpecWrites.ldtCommit`, `SpecReaders.ldtCommit`) and the proof
  phase (`GordieHowe.Ligero.AgreementThreshold.proofSpec`: the constraint challenge, the masked responses and the
  column query, `SpecWrites.ligeroListRadius`, `SpecReaders.listRadius`);
- the stream grants of the extended points (`StreamGrants`, `StreamRows`);
- either masking (`GordieHowe.Ligero.MaskRow.Setup.writes`, `readers`, `commitWrites`, `commitReaders`, by
  cases on the setup, in `GordieHowe/ProofSystem/Program/Transcript/PrefixCodecs.lean`), with their loads
  (`readers_allLoads`, `commitReaders_allLoads`).

The batched skip's codecs and readers are in `GordieHowe/ProofSystem/Zerocheck/BatchedCodecs.lean`
(`GordieHowe.BatchedZerocheck.writes`, `GordieHowe.BatchedZerocheck.readers`).
-/

namespace GordieHowe.SPBCS.Configurations
open QROM

/-- **The writes of the prepared Ligero tableau fit in `B` bytes**, a condition on the
parameters: the two mask arrays of `N` elements, the masked responses (`2k − 1` and `2k − 1`
coefficients) and the low-degree responses of the `nrep` repetitions (one array of `nrep · k`
coefficients), at `fb`-byte field elements. -/
structure LigeroFits (fb N k nrep B : ℕ) : Prop where
  aux : (9 + N * fb) + (9 + N * fb) ≤ B
  response : (9 + k * fb) + ((9 + (2 * k - 1) * fb) + (9 + (2 * k - 1) * fb)) ≤ B
  /-- The low-degree responses, one array of `nrep · k` field elements. -/
  commit_le : 9 + nrep * k * fb ≤ B

end GordieHowe.SPBCS.Configurations

/-! ### The codecs and readers of Ligero at agreement threshold `A` -/

namespace GordieHowe.SPBCS
open GordieHowe.QROM GordieHowe.IOP IOP.ProtocolSpec

namespace WriteCodec

variable {F : Type} [Field F] {fb : ℕ}

/-- **The masked responses' write**: the linear and the quadratic response at the first `2k − 1`
response nodes, two arrays of field elements. -/
def ligeroMasked (FB : Codec.FieldBytes F fb) (k : ℕ) :
    WriteCodec (Ligero.AgreementThreshold.MaskedResponse F k) :=
  (fieldArray FB (2 * k - 1)).prod (fieldArray FB (2 * k - 1))

end WriteCodec

namespace SpecWrites

variable {F : Type} [Field F] {fb B : ℕ} (FB : Codec.FieldBytes F fb)

/-- **The codecs of the commit rounds of Ligero at agreement threshold `A`**: the low-degree
responses of the `nrep` repetitions, one array of `nrep · k` field elements, repetition-major
(`Tableau.LdtResponse.equivFin`; the C++ writes them in one write in this order). The low-degree
challenges have no codec. -/
def ldtCommit (R k nrep : ℕ) (hB : 9 + nrep * k * fb ≤ B) :
    SpecWrites (Ligero.AgreementThreshold.commitSpec F R k nrep) B where
  write
    | ⟨⟨0, _⟩, h⟩ => absurd h (by simp)
    | ⟨⟨1, _⟩, _⟩ =>
      (WriteCodec.fieldArray FB (nrep * k)).mapEquiv Ligero.Tableau.LdtResponse.equivFin
  le
    | ⟨⟨0, _⟩, h⟩ => absurd h (by simp)
    | ⟨⟨1, _⟩, _⟩ => (WriteCodec.fieldArray_B FB (nrep * k)).trans_le hB

/-- **The codecs of the proof phase of Ligero at agreement threshold `A`**: the two-stage test's
codecs (the IDOT and IQUAD masks, `WriteCodec.ligeroAux`, and the masked responses,
`WriteCodec.ligeroMasked`) without the mask round, whose masks are in the oracle message. -/
def ligeroListRadius {N nL nQ k t : ℕ} (hA : (9 + N * fb) + (9 + N * fb) ≤ B)
    (hR : (9 + (2 * k - 1) * fb) + (9 + (2 * k - 1) * fb) ≤ B) :
    SpecWrites (Ligero.AgreementThreshold.proofSpec F N nL nQ k t) B :=
  (twoStage (WriteCodec.ligeroAux FB N) (WriteCodec.ligeroMasked FB k) hA hR).dropMsg 0

end SpecWrites

namespace SpecReaders

variable {F : Type} [Field F] [Fintype F] (r : CReader F)

/-- **The commit rounds of Ligero at agreement threshold `A`**: the low-degree challenges of the
`nrep` repetitions, `R` elements each, repetition-major (`nrep · R` elements in one draw in the
C++); the responses that follow have no challenge. -/
def ldtCommit (R k nrep : ℕ) : SpecReaders (Ligero.AgreementThreshold.commitSpec F R k nrep)
  | ⟨⟨0, _⟩, _⟩ => CReader.pi nrep (CReader.pi R r)
  | ⟨⟨1, _⟩, h⟩ => absurd h (by simp)

omit [Field F] in
theorem ldtCommit_allLoads (R k nrep : ℕ) :
    (ldtCommit r R k nrep).AllLoads (· ≤ (r.load.nsmul (nrep * R)))
  | ⟨⟨0, _⟩, _⟩ => (CReader.pi_pi_load nrep R r).le
  | ⟨⟨1, _⟩, h⟩ => absurd h (by simp)

/-- **The proof phase of Ligero at agreement threshold `A`**: the constraint challenge (`alphal`
and `alphaq` as one run of `nL` elements, then `uquad`), its point granted `g` stream bytes
(`CReader.extend`; the C++ grants `gen_alphal`'s point), then `choose(N, t)`. -/
def listRadius {N nL nQ k t : ℕ} (htN : t ≤ N) (g : ℕ) :
    SpecReaders (Ligero.AgreementThreshold.proofSpec F N nL nQ k t) :=
  (twoStage (((CReader.pi nL r).prod (CReader.pi nQ r)).extend g)
    (CReader.choose N t htN)).dropMsg 0

end SpecReaders

/-- **The stream grants of a circuit proof's extended points**: the bytes beyond the default budget
`k + e` that the C++ grants the point of the domain's packing stage combination (`stage`), of the
root combination (`root`: Ligero's batching challenge for an A domain, the root stage's combination
of every row for an H domain on the tree layout), and of Ligero's linear test `gen_alphal`, which is
the constraint challenge (`linear`) (`BasicTranscript::extend_point_budget_for`,
`lib/gordiehowe/compiler/tree_zk.h`, `lib/ligero/ligero_transcript.h`). `{}` grants none. -/
structure StreamGrants where
  /-- The packing stage's combination. -/
  stage : ℕ := 0
  /-- The root combination (A: Ligero's batching challenge; H: the root stage's combination). -/
  root : ℕ := 0
  /-- Ligero's linear test (the constraint challenge). -/
  linear : ℕ := 0

/-- **The row counts of a circuit proof's extended points**: the rows `n_i` the C++ grants each
extended point a size for (`TreePlan::stream_rows`): the packing stage's row slots (`0` for a domain
without one), the root's row slots and Ligero's linear rows. -/
structure StreamRows where
  /-- The packing stage's row slots. -/
  stage : ℕ := 0
  /-- The root's row slots. -/
  root : ℕ
  /-- Ligero's linear rows. -/
  linear : ℕ

/-- **The C++ grants of the extended points** at `fb`-byte field elements: `4 · n_i · fb` at each
(`extend_point_budget_for(n, F)`: four times the bytes of `n` elements, `F::kBytes = fb`). -/
def StreamRows.grants (n : StreamRows) (fb : ℕ) : StreamGrants where
  stage := 4 * n.stage * fb
  root := 4 * n.root * fb
  linear := 4 * n.linear * fb

end GordieHowe.SPBCS
