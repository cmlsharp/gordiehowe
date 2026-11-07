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
public import GordieHowe.Foundations.Algebra.Rows
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.ProofSystem.Ligero.Preparation
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Foundations.Algebra.AffineForm
public import GordieHowe.ProofSystem.Ligero.SubfieldQuery
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
public import GordieHowe.ProofSystem.Zerocheck.AltRounds
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
  array) and `u` (`k` elements). The moves after `ρ` are `tailWrites` and `tailReaders`.
* **The merged field batch** (`GordieHowe.BatchedZerocheck.fusedWrites`,
  `GordieHowe.BatchedZerocheck.fusedReaders`): the merging coefficient `γ` and `ρ` in one
  verifier move (`1 + n` elements, `γ` first), then the moves after `ρ`.
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

/-- **The codecs of the batch phase after `ρ`**: the skip message (`e` field elements, one array),
every round's `D` coefficients (one array) and the `k` terminal claims (one array), each at most
`B` bytes; the challenges have no codec. -/
def tailWrites (FB : SPBCS.Codec.FieldBytes K fb) (e D n k : ℕ) (he : 9 + e * fb ≤ B)
    (hD : 9 + D * fb ≤ B) (hk : 9 + k * fb ≤ B) :
    SpecWrites (one .P_to_V (Fin e → K) ++ (one .V_to_P K ++
      (HashCircuit.Skip.alt (Fin D → K) K n ++ Tail K k GKR.Schedule.empty))) B :=
  SpecWrites.one (WriteCodec.fieldArray FB e) ((WriteCodec.fieldArray_B FB _).trans_le he) ++
    (SpecWrites.oneV (M := K) (B := B) ++ (roundWrites FB D hD n ++
      (SpecWrites.one (WriteCodec.fieldArray FB k) ((WriteCodec.fieldArray_B FB k).trans_le hk) ++
        (SpecWrites.oneV (M := Fin k → K) (B := B) ++
          SpecWrites.ofNone (P := GKR.Schedule.empty) (B := B) fun i => i.elim0))))

/-- **The codecs of the batch phase** (`spec`, `lib/gordiehowe/compiler/batch.h`): `ρ` (no codec),
then the moves after it (`tailWrites`). -/
def writes (FB : SPBCS.Codec.FieldBytes K fb) (e D n k : ℕ) (he : 9 + e * fb ≤ B)
    (hD : 9 + D * fb ≤ B) (hk : 9 + k * fb ≤ B) : SpecWrites (spec K e D n k) B :=
  SpecWrites.oneV (M := Fin n → K) (B := B) ++ tailWrites FB e D n k he hD hk

/-- **The codecs of the merged batch phase**: `(γ, ρ)` in one verifier move (no codec), then the
moves after `ρ` (`tailWrites`). -/
def fusedWrites (FB : SPBCS.Codec.FieldBytes K fb) (e D n k : ℕ) (he : 9 + e * fb ≤ B)
    (hD : 9 + D * fb ≤ B) (hk : 9 + k * fb ≤ B) :
    SpecWrites (one .V_to_P (K × (Fin n → K)) ++ (one .P_to_V (Fin e → K) ++ (one .V_to_P K ++
      (HashCircuit.Skip.alt (Fin D → K) K n ++ Tail K k GKR.Schedule.empty)))) B :=
  SpecWrites.oneV (M := K × (Fin n → K)) (B := B) ++ tailWrites FB e D n k he hD hk

variable [Fintype K] (r : CReader K)

/-- The batch phase's sumcheck rounds: per round the prover's `D` elements, then `s_i`. -/
def roundReaders (D : ℕ) : (k : ℕ) → SpecReaders (HashCircuit.Skip.alt (Fin D → K) K k)
  | 0 => SpecReaders.empty
  | k + 1 => SpecReaders.oneP (Fin D → K) ++ (SpecReaders.one K r ++ roundReaders D k)

/-- **The challenge readers of the batch phase after `ρ`**: `r`, each round's `s_i`, and `u` (`k`
elements), each element by `r`. -/
def tailReaders (e D n k : ℕ) :
    SpecReaders (one .P_to_V (Fin e → K) ++ (one .V_to_P K ++
      (HashCircuit.Skip.alt (Fin D → K) K n ++ Tail K k GKR.Schedule.empty))) :=
  SpecReaders.oneP (Fin e → K) ++
    (SpecReaders.one K r ++ (roundReaders r D n ++ (SpecReaders.oneP (Fin k → K) ++
      (SpecReaders.one (Fin k → K) (CReader.pi k r) ++ SpecReaders.empty))))

/-- **The challenge readers of the batch phase**: `ρ` (`n` elements), then the moves after it
(`tailReaders`), each element by `r`. -/
def readers (e D n k : ℕ) : SpecReaders (spec K e D n k) :=
  SpecReaders.one (Fin n → K) (CReader.pi n r) ++ tailReaders r e D n k

/-- **The challenge readers of the merged batch phase**: `γ` and `ρ` from one challenge point
(`1 + n` elements, `γ` first; `batch.h`, `BatchKernel::reduce`), then the moves after `ρ`
(`tailReaders`), each element by `r`. -/
def fusedReaders (e D n k : ℕ) :
    SpecReaders (one .V_to_P (K × (Fin n → K)) ++ (one .P_to_V (Fin e → K) ++ (one .V_to_P K ++
      (HashCircuit.Skip.alt (Fin D → K) K n ++ Tail K k GKR.Schedule.empty)))) :=
  SpecReaders.one (K × (Fin n → K)) (r.prod (CReader.pi n r)) ++ tailReaders r e D n k

/-- The rounds' loads are at most one element's. -/
theorem roundReaders_allLoads (D : ℕ) (L : Load) (hL : r.load ≤ L) :
    ∀ k, (roundReaders r D k).AllLoads (· ≤ L)
  | 0 => SpecReaders.empty_allLoads _
  | k + 1 => SpecReaders.append_allLoads (SpecReaders.oneP_allLoads _ _)
      (SpecReaders.append_allLoads (SpecReaders.one_allLoads _ hL) (roundReaders_allLoads D L hL k))

/-- The loads after `ρ` are at most those of `max (max m k) 3` elements, for any `m`. -/
theorem tailReaders_allLoads {e D n k : ℕ} (m : ℕ) :
    (tailReaders r e D n k).AllLoads (· ≤ r.load.nsmul (max (max m k) 3)) := by
  have h1 : r.load ≤ r.load.nsmul (max (max m k) 3) := ⟨by
      simp only [Load.nsmul]
      nlinarith [le_max_right (max m k) 3, r.load.draws.zero_le], le_rfl⟩
  refine SpecReaders.append_allLoads (SpecReaders.oneP_allLoads _ _)
    (SpecReaders.append_allLoads (SpecReaders.one_allLoads _ h1)
      (SpecReaders.append_allLoads (roundReaders_allLoads r D _ h1 n)
      (SpecReaders.append_allLoads (SpecReaders.oneP_allLoads _ _)
        (SpecReaders.append_allLoads (SpecReaders.one_allLoads _ ⟨?_, le_rfl⟩)
          (SpecReaders.empty_allLoads _)))))
  simp only [CReader.pi_load, Load.nsmul]
  exact Nat.mul_le_mul_right _ (le_max_of_le_left (le_max_right _ _))

/-- The batch phase's loads are at most those of `max (max n k) 3` elements. -/
theorem readers_allLoads {e D n k : ℕ} :
    (readers r e D n k).AllLoads (· ≤ r.load.nsmul (max (max n k) 3)) := by
  refine SpecReaders.append_allLoads (SpecReaders.one_allLoads _ ⟨?_, le_rfl⟩)
    (tailReaders_allLoads r n)
  simp only [CReader.pi_load, Load.nsmul]
  exact Nat.mul_le_mul_right _ (le_max_of_le_left (le_max_left _ _))

/-- The merged batch phase's loads are at most those of `max (max (n + 1) k) 3` elements. -/
theorem fusedReaders_allLoads {e D n k : ℕ} :
    (fusedReaders r e D n k).AllLoads (· ≤ r.load.nsmul (max (max (n + 1) k) 3)) := by
  refine SpecReaders.append_allLoads (SpecReaders.one_allLoads _ ?_) (tailReaders_allLoads r _)
  simp only [CReader.prod_load, CReader.pi_load, Load.add, Load.nsmul, Load.le_iff]
  refine ⟨?_, by simp⟩
  have h : n + 1 ≤ max (max (n + 1) k) 3 := le_max_of_le_left (le_max_left _ _)
  nlinarith [Nat.zero_le r.load.draws]

end GordieHowe.BatchedZerocheck
