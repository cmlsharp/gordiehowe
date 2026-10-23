-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

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
public import GordieHowe.Applications.Falcon512.Circuits.HashStep
public import GordieHowe.Applications.Keccak.HashCircuit.SkipCompleteness
public import GordieHowe.ProofSystem.GKR.HonestTranscript
public import GordieHowe.ProofSystem.Ligero.ShapeEncoding
public import GordieHowe.Foundations.ReedSolomon.SubfieldInterpolation
public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.ProofSystem.Ligero.HVZK
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import GordieHowe.Applications.Falcon512.PoP.Relation
public import GordieHowe.ProofSystem.Program.AppPhase
public import GordieHowe.Language.Realizations.MAC
public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.Applications.MLDSA44.PoP.Relation
public import GordieHowe.ProofSystem.Ligero.MaskedConstraintList
public import GordieHowe.ProofSystem.Ligero.UntestedMaskRow
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.Foundations.Fields.GF2_128
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.ProofSystem.GKR.CircuitBudget
public import GordieHowe.Foundations.Fields.GF2_256
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Applications.MLDSA44.PoP.Native.Algebra
public import GordieHowe.Applications.MLDSA44.PoP.Compose
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra
public import GordieHowe.Applications.MLDSA44.Emulated.Rows
public import GordieHowe.Foundations.Fields.GF2_256Conv
public import GordieHowe.Foundations.Fields.GF2_128Conv
public import GordieHowe.Foundations.Fields.GF2_256Skip
public import GordieHowe.Foundations.Fields.GF2_128Skip
public import GordieHowe.Applications.MLDSA44.Fields.GF2_128
public import GordieHowe.Applications.MLDSA44.Fields.GF2_256
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11Relative
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6Relative
public import GordieHowe.Foundations.Fields.GoldilocksQuarticRelative
public import GordieHowe.Foundations.Fields.GoldilocksRelative
public import GordieHowe.Applications.Rows.MAC
public import GordieHowe.Foundations.Algebra.DFT
public import GordieHowe.Foundations.Algebra.DFTExtra
public import GordieHowe.Headline
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import GordieHowe.ProofSystem.Zerocheck.ZeroOneTwoNodes
public import GordieHowe.ProofSystem.GKR.ConcreteNodes
public import GordieHowe.Applications.MLDSA44.Circuits.HashStep
public import GordieHowe.Language.Realizations.MemoryShuffleSubfield
public import GordieHowe.Language.Realizations.Bits
public import Mathlib.Algebra.Field.Subfield.Basic
public import GordieHowe.ProofSystem.GKR.OrdinaryCompleteness
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.Applications.MLDSA44.PoP.ComposeHonest
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.Applications.Rows.NativeLinear
public import GordieHowe.Foundations.Algebra.ConvMatrix
public import GordieHowe.Applications.Falcon512.Circuits.Hash
public import GordieHowe.Applications.Falcon512.Spec.Decoded
public import GordieHowe.Applications.Falcon512.Spec.Encoding
public import GordieHowe.Foundations.Algebra.Conv
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Applications.Configuration.Witness
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebraHonest
public import GordieHowe.Applications.Falcon512.Circuits.NativeAlgebra
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9
public import GordieHowe.Foundations.Fields.GF2_128Selection
public import GordieHowe.Applications.Keccak.Gadgets.Basic
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20
public import GordieHowe.Applications.Falcon512.Circuits.NativeAlgebraHonest
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.Applications.Falcon512.Emulated.Rows
public import GordieHowe.Foundations.ToMathlib.FinFlatten
public import GordieHowe.Applications.Falcon512.Spec.KeyNTT
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebra
public import GordieHowe.Foundations.Fields.GoldilocksRoots
public import GordieHowe.Applications.Falcon512.Spec.Completeness
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebraHonest
public import GordieHowe.Applications.MLDSA44.Spec.Sampler
public import GordieHowe.Language.Realizations.MemoryShuffle
public import GordieHowe.Foundations.ToMathlib.OfFn
public import GordieHowe.Applications.Configuration.AlgebraSetups
public import GordieHowe.Applications.Spec.SelectionField
public import GordieHowe.Foundations.Algebra.RelativePacking
public import GordieHowe.ProofSystem.Zerocheck.UnivariateSkip
public import GordieHowe.Foundations.Fields.GF2_128Dual
public import GordieHowe.Foundations.Fields.GF2_128Relative
public import GordieHowe.Foundations.Fields.GF2_256Dual
public import GordieHowe.Foundations.Fields.GF2_256Relative
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.Applications.MLDSA44.System.Hash

@[expose] public section

/-!
# The ML-DSA-44 honest input and its challenge

* `GordieHowe.MLDSA44.PoP.stream` is the `SampleInBall` stream of `c̃` that the H circuit reads, `sibLen = 272`
  bytes (`lib/gordiehowe/examples/mldsa/mldsa_hash.h`, `kSibBytes`: `8` sign bytes and `264` candidates),
  and `GordieHowe.MLDSA44.PoP.challenge` the challenge coefficients the C++ circuit derives from it: the memory
  shuffle of the selected positions and the stream's sign bits. `sampleInBall_eq` identifies a
  successful selection with the vendored `SampleInBall(c̃)`.
* `GordieHowe.MLDSA44.PoP.HonestInput` is the honest prover's private input at the relatively packed
  circuits; `HonestInput.Valid` states that the fixed-stream selection succeeds at its positions
  and that the signature verifies (`MLDSA44.Verifies`), and `HonestInput.Valid.checks` unfolds the
  checks of FIPS 204 Algorithm 8 with `SampleInBall(c̃)` replaced by the selected challenge.
-/

namespace GordieHowe

open IOP
open scoped NNReal

namespace MLDSA44.PoP

open _root_.MLDSA.Concrete (Hint concretePrimitives)

section

/-! ### The challenge of `c̃` -/

/-- The `SampleInBall` stream `SHAKE256(c̃, sibLen)` the H circuit reads (`sibLen = 272`). -/
-- spec-side
def stream (ctilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44) :
    Fin MLDSA44.Native.sibLen → ℕ :=
  xofFin shake256 (List.ofFn fun j => (ctilde.get j).toNat) MLDSA44.Native.sibLen

theorem stream_eq (ctilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44) :
    stream ctilde = xofFin shake256 (ctilde.toList.map UInt8.toNat) MLDSA44.Native.sibLen := by
  rw [stream, Vector.ofFn_get_map]

/-- The challenge coefficients of `c̃` at the selected positions: the memory shuffle of the
positions and the stream's sign bits. -/
-- spec-side
def challenge (ctilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44)
    (pos : Fin mldsa44.τ → ℕ) : Fin mldsa44.N → ℤ :=
  MemoryShuffle.shuffle mldsa44.N mldsa44.τ pos fun s => MLDSA44.sampleInBallSign (stream ctilde) s

theorem challenge_ternary (ctilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44)
    (pos : Fin mldsa44.τ → ℕ) (k : Fin mldsa44.N) :
    challenge ctilde pos k = 0 ∨ challenge ctilde pos k = 1 ∨ challenge ctilde pos k = -1 :=
  MemoryShuffle.shuffle_ternary _ _ _ _ _

/-- A successful selection computes the vendored `SampleInBall(c̃)`. -/
theorem sampleInBall_eq {ctilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44}
    {pos : Fin mldsa44.τ → ℕ} (hpos : MLDSA44.acceptedCandidates mldsa44 (stream ctilde) = some pos) :
    (concretePrimitives _root_.MLDSA.mldsa44).sampleInBall ctilde =
      MLDSA44.ofCoeff fun k => (challenge ctilde pos k : _root_.MLDSA.Coeff) := by
  rw [stream_eq] at hpos
  exact MLDSA44.fixedStreamChallenge_agree_prims (by decide)
    ((MLDSA44.fixedStreamChallenge_eq_some_iff mldsa44).mpr ⟨pos, hpos, by rw [challenge, stream_eq]⟩)

end

/-- **The honest prover's private input** at the relatively packed circuits: the encoded key and context,
the message, the signature `(c̃, z, h)` and the positions of the fixed-stream selection on
`c̃`'s stream. The prover's coins are drawn separately. -/
structure HonestInput (ctxLen msgLen : ℕ) where
  pk : MLDSA44.PoP.Statement ctxLen
  message : Fin msgLen → UInt8
  ctilde : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44
  positions : Fin mldsa44.τ → ℕ
  z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l
  h : Vector Hint _root_.MLDSA.mldsa44.k

namespace HonestInput

variable {ctxLen msgLen : ℕ} (i : HonestInput ctxLen msgLen)

/-- The input's public key, decoded from its encoding (`MLDSA44.pkDecode44`). -/
abbrev key : MLDSA44.PublicKey44 := MLDSA44.pkDecode44 i.pk.key

/-- **Supported honest inputs**: the fixed-stream selection on `c̃`'s `272`-byte stream
(`stream`) succeeds at `positions`, so `SampleInBall(c̃)` finishes within the stream's `264`
candidates, and `(c̃, z, h)` verifies (`MLDSA44.Verifies`, FIPS 204 Algorithm 8 with `ExpandA`
within `1008` SHAKE128 bytes per `RejNTTPoly` call (`ExpandAWithin`)) on the framed message at the
input's key and context. -/
structure Valid : Prop where
  positions : MLDSA44.acceptedCandidates mldsa44 (stream i.ctilde) = some i.positions
  verify : MLDSA44.Verifies i.key
    (MLDSA44.frame (List.ofFn i.pk.ctx) (List.ofFn i.message)) ⟨i.ctilde, i.z, i.h⟩

/-- The challenge coefficients of the honest input. -/
-- spec-side
def c : Fin mldsa44.N → ℤ := challenge i.ctilde i.positions

variable {i}

/-- The checks Algorithm 8 makes on a valid input: the norm bound, the commitment and the hint
weight, with `SampleInBall(c̃)` replaced by the selected challenge. -/
theorem Valid.checks (hi : i.Valid) :
    _root_.MLDSA.polyVecNorm i.z < _root_.MLDSA.mldsa44.gamma1 - _root_.MLDSA.mldsa44.beta ∧
      _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44
          (_root_.MLDSA.Concrete.hashMessage
            ((concretePrimitives _root_.MLDSA.mldsa44).hashPublicKey i.key.rho i.key.t1)
            (MLDSA44.frame (List.ofFn i.pk.ctx) (List.ofFn i.message)))
          (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44
            (Compose.honestW1 i.key i.c i.z i.h)) = i.ctilde ∧
      _root_.MLDSA.Concrete.hintWeightVec i.h ≤ _root_.MLDSA.mldsa44.omega := by
  have hv := hi.verify.checks
  unfold MLDSA44.verifyChecks at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hnorm, hcommit⟩, hweight⟩ := hv
  rw [sampleInBall_eq hi.positions] at hcommit
  exact ⟨hnorm, (congrArg (fun w => _root_.MLDSA.Concrete.hashCommitment _root_.MLDSA.mldsa44 _
    (_root_.MLDSA.Concrete.w1Encode _root_.MLDSA.mldsa44 w))
      (Compose.useHintVec_honestWApprox i.key i.c i.z i.h)).symm.trans hcommit, hweight⟩

/-! ### The honest input of a pair of the relation -/

variable (x : MLDSA44.PoP.Statement ctxLen) (w : MLDSA44.PoP.Witness msgLen) in
/-- **The honest input of a statement and a witness**: the statement, the witness's message,
the signature `(c̃, z, h)` that the vendored `sigDecode` (FIPS 204 Algorithm 27) decodes from the
witness's signature bytes, and the positions the fixed-stream selection takes on `c̃`'s stream.
A pair of the relation decodes and selects (`valid_ofWitness`); elsewhere the defaults are
read.

Running time: one `sigDecode` and one SHAKE256 call of `272` bytes with the selection over its
`264` candidates. -/
def ofWitness : HonestInput ctxLen msgLen :=
  let d := (_root_.MLDSA.Concrete.sigDecode _root_.MLDSA.mldsa44 w.signature).getD
    (default, 0, default)
  { pk := x
    message := w.message
    ctilde := d.1
    positions := (MLDSA44.acceptedCandidates mldsa44 (stream d.1)).getD 0
    z := d.2.1
    h := d.2.2 }

/-- **Every pair of the ML-DSA-44 relation gives a valid honest input** (`ofWitness`): the
signature bytes decode (`VerifiesBytes.decode`), `SampleInBall(c̃)` finishes within the vendored
sampler's `264` candidates, so the fixed-stream selection on the `272`-byte stream succeeds
(`acceptedCandidates_isSome_of_sampleInBallPoly?`), and the decoded signature verifies. No
signature of the relation is excluded. -/
theorem valid_ofWitness {x : MLDSA44.PoP.Statement ctxLen} {w : MLDSA44.PoP.Witness msgLen}
    (h : (x, w) ∈ rel ctxLen msgLen) : (ofWitness x w).Valid := by
  obtain ⟨c, z, hh, hdec, hver⟩ := h.decode
  have hsel : (MLDSA44.acceptedCandidates mldsa44 (stream c)).isSome := by
    rw [stream_eq]
    exact MLDSA44.acceptedCandidates_isSome_of_sampleInBallPoly? hver.sampleInBall
  obtain ⟨pos, hpos⟩ := Option.isSome_iff_exists.mp hsel
  unfold ofWitness
  simp only [hdec, Option.getD_some]
  exact ⟨by rw [hpos, Option.getD_some], hver⟩

end HonestInput

end MLDSA44.PoP

end GordieHowe
