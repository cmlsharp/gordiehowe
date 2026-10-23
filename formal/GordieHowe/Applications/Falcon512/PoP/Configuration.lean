-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.ProofSystem.Ligero.Routing
public import GordieHowe.Foundations.Algebra.AffineForm
public import GordieHowe.Applications.Falcon512.Circuits.HashStep
public import GordieHowe.Applications.Keccak.HashCircuit.SkipCompleteness
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic
public import GordieHowe.ProofSystem.Ligero.Preparation
public import GordieHowe.ProofSystem.GKR.TranscriptRouting
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.Foundations.ReedSolomon.AffineProximity
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.ProofSystem.GKR.HonestTranscript
public import GordieHowe.ProofSystem.Ligero.ShapeEncoding
public import GordieHowe.Foundations.ReedSolomon.SubfieldInterpolation
public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.ProofSystem.Ligero.HVZK
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import GordieHowe.Applications.Falcon512.PoP.Relation
public import GordieHowe.ProofSystem.Ligero.MaskTest.PiecesHonest
public import GordieHowe.ProofSystem.Program.AppPhase
public import GordieHowe.Language.Realizations.MAC
public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.ProofSystem.GKR.Transcript
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
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebra
public import GordieHowe.Foundations.Fields.GF2_256Conv
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20Relative
public import GordieHowe.Foundations.Fields.GoldilocksQuarticRelative
public import GordieHowe.Applications.Rows.NativeLinear
public import GordieHowe.Applications.Rows.MAC
public import GordieHowe.Foundations.Algebra.DFT
public import GordieHowe.Foundations.Algebra.DFTExtra
public import GordieHowe.Foundations.Algebra.ConvMatrix
public import GordieHowe.Headline
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import GordieHowe.ProofSystem.Zerocheck.ZeroOneTwoNodes
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.Applications.Falcon512.Emulated.Rows
public import GordieHowe.Foundations.ToMathlib.FinFlatten
public import GordieHowe.Applications.Falcon512.Spec.KeyNTT
public import GordieHowe.ProofSystem.GKR.ConcreteNodes
public import GordieHowe.Foundations.Fields.GoldilocksRoots
public import GordieHowe.Applications.Falcon512.Spec.Completeness
public import GordieHowe.Language.Realizations.Bits
public import Mathlib.Algebra.Field.Subfield.Basic
public import GordieHowe.Foundations.Fields.GF2_128Conv
public import GordieHowe.Foundations.Fields.GF2_128Skip
public import GordieHowe.Foundations.Fields.GF2_128Relative
public import GordieHowe.Foundations.Fields.GF2_128Dual
public import GordieHowe.Foundations.Fields.GF2_256Dual
public import GordieHowe.Foundations.Fields.GF2_256Skip
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9Relative
public import GordieHowe.Foundations.Fields.GoldilocksRelative
public import GordieHowe.Applications.MLDSA44.Circuits.HashStep
public import GordieHowe.Language.Realizations.MemoryShuffleSubfield
public import GordieHowe.ProofSystem.GKR.OrdinaryCompleteness
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.Applications.MLDSA44.PoP.ComposeHonest
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.Applications.Falcon512.Circuits.NativeAlgebraHonest
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra
public import GordieHowe.Applications.MLDSA44.PoP.Native.Algebra
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebraHonest
public import GordieHowe.Applications.MLDSA44.Emulated.Rows
public import GordieHowe.Applications.MLDSA44.PoP.Relation
public import GordieHowe.Applications.MLDSA44.PoP.Compose
public import GordieHowe.Applications.MLDSA44.Fields.GF2_128
public import GordieHowe.Applications.Configuration.AlgebraSetups
public import GordieHowe.Applications.Spec.SelectionField
public import GordieHowe.Foundations.Algebra.RelativePacking
public import GordieHowe.ProofSystem.Zerocheck.UnivariateSkip
public import GordieHowe.Language.Realizations.MemoryShuffle
public import GordieHowe.Foundations.Fields.GF2_256Relative
public import GordieHowe.Applications.MLDSA44.Fields.GF2_256
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Foundations.ToMathlib.OfFn

@[expose] public section

/-!
# The honest input of the Falcon-512 proofs of possession

The honest prover's private input at the relatively packed circuits (`GordieHowe.Falcon512.PoP.HonestInput`:
public key, nonce, message, samples and signature) and the inputs it supports
(`GordieHowe.Falcon512.PoP.HonestInput.Valid`: bytes, the implemented short sampler succeeds, the signature
satisfies Falcon's algebraic verifier at the input's key, and its payload is encodable). The
honest provers of the Falcon configurations read it (`GordieHowe/Applications/Falcon512/System/Honest.lean`).
-/

namespace GordieHowe

open IOP
open scoped NNReal

namespace Falcon512.PoP

/-- **The honest prover's private input** at the relatively packed circuits: the key, the salt,
the `msgLen`-byte message, the samples and the signature polynomial. The prover's coins (the arm's
pads, the skip pads and opening masks, the H and A proof coins) are drawn separately. -/
structure HonestInput (msgLen : ℕ) where
  pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512
  nonce : Fin falcon512.saltBytes → ℕ
  message : Fin msgLen → ℕ
  samples : Fin falcon512.n → ℕ
  signature : _root_.Falcon.IntPoly falcon512.n

/-- **Supported honest inputs**: bytes, the implemented short sampler succeeds, the signature
satisfies Falcon's algebraic verifier at the input's key, and its payload is encodable. -/
structure HonestInput.Valid {msgLen : ℕ} (i : HonestInput msgLen) : Prop where
  nonce_bytes : ∀ j, i.nonce j < 256
  message_bytes : ∀ j, i.message j < 256
  samples : Falcon512.acceptedCandidates falcon512 shake256 (List.ofFn i.nonce)
    (List.ofFn i.message) = some i.samples
  algebra : Falcon512.algebraOk falcon512 i.pk.h
    (Falcon512.ofCoeff fun j => (i.samples j : _root_.Falcon.Coeff)) i.signature.toRq
  encoding : Falcon512.EncodingBounds falcon512 i.signature

namespace HonestInput

variable {msgLen : ℕ}

variable (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512)
  (w : Falcon512.PoP.Witness msgLen) in
/-- **The honest input of a key and a witness**: the key, the signature's salt as the nonce, the
message bytes, the samples the fixed-stream `HashToPoint` takes on them
(`Falcon512.acceptedCandidates`) and the signature polynomial the vendored `decompress` decodes.
A pair of `relSupported` samples and decodes (`valid_ofWitness`); elsewhere the defaults are
read.

Running time: one SHAKE256 call of `1278` bytes with the selection over its `639` samples, and
one `decompress` of the `625`-byte payload. -/
def ofWitness : HonestInput msgLen where
  pk := pk
  nonce j := (w.signature.salt.get j).toNat
  message j := (w.message j).toNat
  samples := (Falcon512.acceptedCandidates falcon512 shake256
    (w.signature.salt.toList.map UInt8.toNat) ((List.ofFn w.message).map UInt8.toNat)).getD 0
  signature := (Falcon512.prims512.decompress w.signature.compressedS2
    _root_.Falcon.Concrete.params512.sbytelen).getD 0

/-- **Every pair of `relSupported` gives a valid honest input** (`ofWitness`): the salt and
message are bytes, the fixed-stream `HashToPoint` succeeds (the restriction), its point is the
verifier's (`Falcon512.fixedStreamChallenge_agree`), so the decoded signature polynomial passes
the algebraic check, and a decoded polynomial satisfies the encodability bounds
(`Falcon512.encodingBounds_of_decompress`). -/
theorem valid_ofWitness {pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512}
    {w : Falcon512.PoP.Witness msgLen} (h : (pk, w) ∈ relSupported msgLen) :
    (ofWitness pk w).Valid := by
  obtain ⟨hver, hsel⟩ := h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsel
  obtain ⟨s2, c', hdec, hhash, halg⟩ := (Falcon512.verify_iff_algebraOk _ _ _).mp hver
  have hagree := Falcon512.fixedStreamChallenge_agree hc (Falcon512.prims512.publicKeyBytes pk.h)
  obtain rfl := Option.some.inj (hagree.symm.trans hhash)
  have hnonce : List.ofFn (fun j => (w.signature.salt.get j).toNat) =
      w.signature.salt.toList.map UInt8.toNat := by
    rw [Vector.ofFn_get_map]
  have hmsg : List.ofFn (fun j => (w.message j).toNat) = (List.ofFn w.message).map UInt8.toNat := by
    rw [List.map_ofFn]
    rfl
  refine ⟨fun j => UInt8.toNat_lt _, fun j => UInt8.toNat_lt _, ?_, ?_, ?_⟩
  · simp only [ofWitness]
    exact (congrArg₂ (Falcon512.acceptedCandidates falcon512 shake256) hnonce hmsg).trans
      (by rw [hc, Option.getD_some])
  · simp only [ofWitness]
    rw [hc, Option.getD_some, hdec, Option.getD_some]
    exact halg
  · simp only [ofWitness]
    rw [hdec, Option.getD_some]
    exact Falcon512.encodingBounds_of_decompress hdec

end HonestInput

end Falcon512.PoP

end GordieHowe
