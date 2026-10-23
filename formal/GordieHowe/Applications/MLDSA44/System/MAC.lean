-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.System.Source
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.MLDSA44.System.Params
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra
public import GordieHowe.Language.Realizations.MACEquality
public import GordieHowe.Applications.MLDSA44.System.SampleInBall
public import GordieHowe.Applications.MLDSA44.System.RisingSelection
public import GordieHowe.Language.Realizations.MaskSubfield
public import GordieHowe.Applications.MLDSA44.PoP.Relation

@[expose] public section

/-!
# ML-DSA: the field data, the statement and the stream readings

The pieces of ML-DSA native's randomized lowerings that ML-DSA
emulated also uses:

* **The field data** (`FieldData`, at a profile `P`): the masking subfield of `F`, H's selection
  field, `θ`, the injectivity of the record packing, the MAC basis and the packing basis of the
  Keccak words.
* **The statement** (`Statement`, `Statement.pk`) and the transcript wires (`trWires`).
* **The readings of the SampleInBall stream** that SampleInBall's memory check and the
  rising-threshold selection read (`sibBytes`, `signsOf`, `streamOf`).

The range lowering, the composite and its honest prover are each configuration's.
-/

namespace GordieHowe.MLDSA44.Native

open IOP RealizedProgram.ProofSystem.PhaseLayout Range Params
open GordieHowe (MaskSubfield)
open scoped NNReal ENNReal

/-! ### The field data -/

variable (P : Profile) (KH F S : Type) [Field KH] [Fintype KH] [DecidableEq KH] [Field F]
  [Fintype F] [DecidableEq F] [Field S] [Fintype S]

variable {P KH F S} {Tα : ℕ}

variable (P) (σ : MaskSubfield S F)

variable {P}

/-- **The field data of ML-DSA native** at a profile `P`: the masking subfield of `A` (`σ`), H's
selection field (`sel`: the subfield `GF(2^16)`, the constant `κ = sel.X` and the embedding basis),
`θ` of order `3` in the subfield, the injectivity of the record packing at `κ` on the subfield's
triples (`permutation.h:28-34`), the MAC basis of `KH` and the packing basis of the Keccak words.
Facts about the fields, discharged once for the concrete fields. -/
structure FieldData (P : Profile) (KH F S : Type) [Field KH] [Field F] [Field S] where
  /-- The masking subfield of `A`. -/
  σ : MaskSubfield S F
  /-- The selection field. -/
  sel : SelectionField KH nSamples
  /-- `θ`, with `θ² + θ + 1 = 0`. -/
  Θ : MemoryShuffle.Theta KH
  θ_mem : Θ.θ ∈ sel.E
  /-- The record packing at `κ` is injective on the subfield's triples. -/
  packing3 : ∀ a b : Fin 3 → KH, (∀ i, a i ∈ sel.E) → (∀ i, b i ∈ sel.E) →
    RecordPacking.pack sel.X a = RecordPacking.pack sel.X b → a = b
  /-- The MAC basis. -/
  basis : Conv.ConvBasis P.macWidth P.macTaps KH
  /-- The packing basis of the Keccak words. -/
  packing : PackedClaim.PackedBasis KH 4

variable (D : FieldData P KH F S) (msgLen : ℕ)

variable [CharP F _root_.MLDSA.modulus]

/-! ### The application constraints -/

section App

variable {msgLen}

/-- The statement: the encoded ML-DSA-44 public key and the empty context. -/
abbrev Statement : Type := MLDSA44.PoP.Statement 0

/-- The decoded public key of a statement (`MLDSA44.pkDecode44`). -/
abbrev Statement.pk (x : Statement) : Rows.PublicKey := MLDSA44.pkDecode44 x.key

/-- **The bits of `tr = H(pk)`** (`mldsa_hash.h:150-163`, `tr`, a public computation of the key):
bit `8k + i` of byte `k`. -/
def trWires (x : Statement) : BitWires KH (8 * 64) :=
  Falcon512.HashCircuit.wiresOfByteVec fun i => (MLDSA44.PoP.Compose.trOf x.pk i).toNat

end App

/-! ### The stream readings -/

section Composite

variable [CharP KH 2] {msgLen}

/-- The SampleInBall stream's output bytes of a source assignment. -/
def sibBytes (a : Source KH F msgLen) : Fin sibLen → BitWires KH 8 := sibOut D.packing a.states

/-- The signs of a source assignment: bits `0 … 38` of the stream's output. -/
def signsOf (a : Source KH F msgLen) : Fin τ → KH := HashCircuit.signWires (sibBytes D a)

/-- The candidate stream of a source assignment: bytes `8 … 271` of the stream's output. -/
def streamOf (a : Source KH F msgLen) : Fin nSamples → BitWires KH 8 :=
  HashCircuit.candidates (sibBytes D a)

end Composite

end GordieHowe.MLDSA44.Native
