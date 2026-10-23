-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.AgreementThreshold
public import GordieHowe.ProofSystem.Ligero.HVZK
public import GordieHowe.Model.IOP.AppendView
public import GordieHowe.ProofSystem.FieldProof.MaskedRowReduction
public import GordieHowe.Foundations.Algebra.RelativePackingBijective
public import GordieHowe.ProofSystem.Ligero.MaskTest.PiecesHonest
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.ProofSystem.Ligero.Preparation
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Foundations.Algebra.AffineForm
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic
public import GordieHowe.ProofSystem.GKR.TranscriptRouting
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.ProofSystem.GKR.CircuitBudget
public import GordieHowe.Foundations.ReedSolomon.AffineProximity
public import GordieHowe.ProofSystem.GKR.OrdinaryCompleteness
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.GKR.HonestTranscript
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.ProofSystem.Zerocheck.SkipBatchPhase
public import GordieHowe.ProofSystem.Zerocheck.SkipBatch
public import GordieHowe.ProofSystem.FieldProof.MaskedReduction
public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.ProofSystem.Ligero.Routing
public import GordieHowe.ProofSystem.Zerocheck.AffineBatch
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Program.Transcript.CircuitCodecs
public import GordieHowe.ProofSystem.Program.Transcript.Format
public import GordieHowe.ProofSystem.Program.Transcript.Readers

@[expose] public section

/-!
# The codecs and challenge readers of the field batch

The write codecs (`SpecWrites`) and challenge readers (`SpecReaders`) of the field batch's phase.
Byte identity with the C++ is not a goal; the codecs are injective, self-delimiting and bounded,
and every challenge is read by a reader of the uniform distribution of its type.

* **The field batch** (`GordieHowe.BatchedZerocheck.writes`, `GordieHowe.BatchedZerocheck.readers`;
  `lib/gordiehowe/compiler/batch.h`, `reduce`): `ρ` (`n` elements), the skip message (`(D − 1)(w − 1)` elements, one
  array), `r`, every round's two coefficients (one array) and `s_i`, the `k` terminal claims (one
  array) and `u` (`k` elements).
-/

namespace GordieHowe.BatchedZerocheck

open GordieHowe.QROM GordieHowe.SPBCS GKR.Schedule

variable {K : Type} [Field K] {fb B : ℕ}

/-- The batch phase's sumcheck rounds: each prover message is `D` field elements (one array). -/
def roundWrites (FB : SPBCS.Codec.FieldBytes K fb) (D : ℕ) (hD : 9 + D * fb ≤ B) :
    (k : ℕ) → SpecWrites (HashCircuit.Skip.alt (Fin D → K) K k) B
  | 0 => SpecWrites.ofNone fun i => i.elim0
  | k + 1 => SpecWrites.one (WriteCodec.fieldArray FB D) ((WriteCodec.fieldArray_B FB D).trans_le hD) ++
      (SpecWrites.oneV (M := K) (B := B) ++ roundWrites FB D hD k)

/-- **The codecs of the batch phase** (`spec`, `lib/gordiehowe/compiler/batch.h`): the skip message (`e` field
elements, one array), every round's `D` coefficients (one array) and the `k` terminal claims (one
array), each at most `B` bytes; the challenges have no codec. -/
def writes (FB : SPBCS.Codec.FieldBytes K fb) (e D n k : ℕ) (he : 9 + e * fb ≤ B)
    (hD : 9 + D * fb ≤ B) (hk : 9 + k * fb ≤ B) : SpecWrites (spec K e D n k) B :=
  SpecWrites.oneV (M := Fin n → K) (B := B) ++
    (SpecWrites.one (WriteCodec.fieldArray FB e) ((WriteCodec.fieldArray_B FB _).trans_le he) ++
      (SpecWrites.oneV (M := K) (B := B) ++ (roundWrites FB D hD n ++
        (SpecWrites.one (WriteCodec.fieldArray FB k) ((WriteCodec.fieldArray_B FB k).trans_le hk) ++
          (SpecWrites.oneV (M := Fin k → K) (B := B) ++
            SpecWrites.ofNone (P := GKR.Schedule.empty) (B := B) fun i => i.elim0)))))

variable [Fintype K] (r : CReader K)

/-- The batch phase's sumcheck rounds: per round the prover's `D` elements, then `s_i`. -/
def roundReaders (D : ℕ) : (k : ℕ) → SpecReaders (HashCircuit.Skip.alt (Fin D → K) K k)
  | 0 => SpecReaders.empty
  | k + 1 => SpecReaders.oneP (Fin D → K) ++ (SpecReaders.one K r ++ roundReaders D k)

/-- **The challenge readers of the batch phase**: `ρ` (`n` elements), `r`, each round's `s_i`,
and `u` (`k` elements), each element by `r`. -/
def readers (e D n k : ℕ) : SpecReaders (spec K e D n k) :=
  SpecReaders.one (Fin n → K) (CReader.pi n r) ++
    (SpecReaders.oneP (Fin e → K) ++
    (SpecReaders.one K r ++ (roundReaders r D n ++ (SpecReaders.oneP (Fin k → K) ++
      (SpecReaders.one (Fin k → K) (CReader.pi k r) ++ SpecReaders.empty)))))

/-- The rounds' loads are at most one element's. -/
theorem roundReaders_allLoads (D : ℕ) (L : Load) (hL : r.load ≤ L) :
    ∀ k, (roundReaders r D k).AllLoads (· ≤ L)
  | 0 => SpecReaders.empty_allLoads _
  | k + 1 => SpecReaders.append_allLoads (SpecReaders.oneP_allLoads _ _)
      (SpecReaders.append_allLoads (SpecReaders.one_allLoads _ hL) (roundReaders_allLoads D L hL k))

/-- The batch phase's loads are at most those of `max (max n k) 3` elements. -/
theorem readers_allLoads {e D n k : ℕ} :
    (readers r e D n k).AllLoads (· ≤ r.load.nsmul (max (max n k) 3)) := by
  have h1 : r.load ≤ r.load.nsmul (max (max n k) 3) := ⟨by
      simp only [Load.nsmul]
      nlinarith [le_max_right (max n k) 3, r.load.draws.zero_le], le_rfl⟩
  refine SpecReaders.append_allLoads (SpecReaders.one_allLoads _ ⟨?_, le_rfl⟩)
    (SpecReaders.append_allLoads (SpecReaders.oneP_allLoads _ _)
    (SpecReaders.append_allLoads (SpecReaders.one_allLoads _ h1)
      (SpecReaders.append_allLoads (roundReaders_allLoads r D _ h1 n)
      (SpecReaders.append_allLoads (SpecReaders.oneP_allLoads _ _)
        (SpecReaders.append_allLoads (SpecReaders.one_allLoads _ ⟨?_, le_rfl⟩)
          (SpecReaders.empty_allLoads _))))))
  · simp only [CReader.pi_load, Load.nsmul]
    exact Nat.mul_le_mul_right _ (le_max_of_le_left (le_max_left _ _))
  · simp only [CReader.pi_load, Load.nsmul]
    exact Nat.mul_le_mul_right _ (le_max_of_le_left (le_max_right _ _))

end GordieHowe.BatchedZerocheck
