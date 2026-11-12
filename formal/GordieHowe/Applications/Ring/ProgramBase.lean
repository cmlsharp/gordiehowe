-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.SPBCSComap
public import GordieHowe.Applications.Ring.Program
public import GordieHowe.Applications.Ring.InsiderTools

@[expose] public section

/-!
# Ring signatures from a GordieHowe program and a base signer

The program form (the paper's Theorem 5.2, `thm:backend`) of the ring signature
`ofBase B PS adm` (`GordieHowe/Model/RingSignature/Base.lean`): a GordieHowe program whose relation
gives the ring relation of a base signer `B` (`BaseVerifiesRing`), compiled by spBCS at a transcript
of its soundness IOP, is the proof system `PS`. The program's IOP
and its transcript `TD` are over the program's statements and do not depend on `B`; the base
signer's oracle is the compiled oracle `Bits (queryBits TD.k (2 TD.k) kS 2^40) → XOut TD.k e` of
`TD`, so `B` is chosen after `TD`.

- `transcriptPST TD kS hb pB R`: the types of the spBCS proof system at the transcript `TD`
  (`spbcsPST` at the model of `TD.setting kS hb`), its proofs and coins the named types
  `TranscriptProof` and `TranscriptCoins` over the transcript, each with its instances.
- `BaseVerifiesRing ir I rel relH B adm`: the program verifies base signatures of `B` for the ring
  relation `ringRel B adm H` at every oracle `H`: a map of ring statements to the program's
  statements, a statement check, a map of the program's witnesses to ring witnesses (soundness at
  every oracle), and a partial map of ring witnesses to honest inputs (the honest direction at every
  oracle).

Both directions of `BaseVerifiesRing` quantify over every oracle. For a base signer whose
verification reads the oracle (the ML-DSA ring publishing `w₁`), the program's relation must then
give and contain the ring relation at every commitment hash; this file constructs no such program.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum RealizedProgram RealizedProgram.ProofSystem
  GordieHowe.RingSignature
open scoped NNReal ENNReal

section TranscriptTypes

variable {X₀ W : Type} {rel₀ : Set (X₀ × W)} {C : RealizedProgram.ProofSystem.IOP X₀ W rel₀}
  (TD : SPBCS.ProofSystemTranscript C) (kS : ℕ) (hb : TD.MergeBounds kS)

/-- **The proofs of the spBCS proof system at a transcript** `TD` of an IOP `C`, at `kS`-byte
salts under the merge bounds `hb`, in the format `pB`: the responses of the model of the setting
`TD.setting kS hb`. A named type over the transcript, with its instances registered once: spelled
through the setting's model, every mention and every instance found by search repeats the setting
with all its implicit arguments. -/
def TranscriptProof (pB : ℕ) : Type := (TD.setting kS hb).model.Response pB

/-- **The coins of the spBCS proof system at a transcript** `TD` with causal-prover coins `R`: the
Fiat–Shamir salt with the prover's coins of the model of the setting `TD.setting kS hb`. A named
type over the transcript, as `TranscriptProof`. -/
def TranscriptCoins (R : Type) : Type :=
  SaltedCoins (FiatShamirSalt kS) ((TD.setting kS hb).model.ProverCoins R)

variable {TD kS hb}

noncomputable instance TranscriptProof.instFintype {pB : ℕ} :
    Fintype (TranscriptProof TD kS hb pB) :=
  inferInstanceAs (Fintype ((TD.setting kS hb).model.Response pB))

instance TranscriptProof.instDecidableEq {pB : ℕ} : DecidableEq (TranscriptProof TD kS hb pB) :=
  inferInstanceAs (DecidableEq ((TD.setting kS hb).model.Response pB))


instance TranscriptCoins.instFintype {R : Type} [Fintype R] :
    Fintype (TranscriptCoins TD kS hb R) :=
  inferInstanceAs
    (Fintype (SaltedCoins (FiatShamirSalt kS) ((TD.setting kS hb).model.ProverCoins R)))

instance TranscriptCoins.instDecidableEq {R : Type} [DecidableEq R] :
    DecidableEq (TranscriptCoins TD kS hb R) :=
  inferInstanceAs
    (DecidableEq (SaltedCoins (FiatShamirSalt kS) ((TD.setting kS hb).model.ProverCoins R)))

instance TranscriptCoins.instNonempty {R : Type} [Nonempty R] :
    Nonempty (TranscriptCoins TD kS hb R) :=
  inferInstanceAs
    (Nonempty (SaltedCoins (FiatShamirSalt kS) ((TD.setting kS hb).model.ProverCoins R)))

variable (TD kS hb)

/-- **The types of the spBCS proof system at a transcript** `TD`, proofs in the format `pB` and
causal-prover coins `R`: `spbcsPST` at the model of the setting `TD.setting kS hb`, with the proofs
and coins named over the transcript (`TranscriptProof`, `TranscriptCoins`). -/
noncomputable abbrev transcriptPST (pB : ℕ) (R : Type) : PSTypes :=
  ⟨TranscriptProof TD kS hb pB, TranscriptCoins TD kS hb R⟩

end TranscriptTypes

/-- **The program verifies base signatures of `B` for the ring relation** `RingSignature.ringRel B adm H` at
every oracle `H` (BKM06 Definition 1, ePrint 2005/304, p. 3, with `Vrfy_R(M, σ)` the program's
verifier on the statement of `(R, M, y)`): for a relation `rel` of the program's statements and
honest inputs `relH`, a map `stmt` of ring statements to the program's statements and a statement
check `check`, with

* soundness: a witness of `rel` at the program's statement of a checked ring statement gives a ring
  witness (`wit`) at every oracle;
* the honest direction: at every oracle, the statements of the ring relation pass the check, and a
  ring witness has an honest input (`input`, defined on the ring relation) of the program's honest
  prover at the program's statement. -/
structure BaseVerifiesRing (ir : RealizedProgram) (I : RealizedProgram.Interp) {W : Type}
    (rel : Set (ir.Valuation I × W)) {Inp : Type} (relH : Set (ir.Valuation I × Inp)) {Xo Yo : Type}
    {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
    (B : BaseSigner Xo Yo N T RMsg) (adm : KeyRing B.PK N → Prop) where
  /-- The program's statement of a ring statement. -/
  stmt : RingSignature.RingStmt B → ir.Valuation I
  /-- The check of a ring statement. -/
  check : RingSignature.RingStmt B → Bool
  /-- The ring witness of a witness of the program's relation. -/
  wit : RingSignature.RingStmt B → W → RingSignature.RingWit B
  /-- A witness of the program's relation at a checked statement gives a ring witness. -/
  sound : ∀ (H : Xo → Yo) x w, check x = true → (stmt x, w) ∈ rel → (x, wit x w) ∈ RingSignature.ringRel B adm H
  /-- The honest input of a ring statement and a ring witness, if any. -/
  input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Inp
  /-- The statements of the ring relation pass the check. -/
  check_eq_true : ∀ (H : Xo → Yo) x w, (x, w) ∈ RingSignature.ringRel B adm H → check x = true
  /-- A ring witness has an honest input. -/
  input_mem : ∀ (H : Xo → Yo) x w, (x, w) ∈ RingSignature.ringRel B adm H →
    ∃ y ∈ input x w, (stmt x, y) ∈ relH


end GordieHowe.Ring
