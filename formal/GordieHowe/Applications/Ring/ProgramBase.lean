-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Program
public import GordieHowe.Applications.Ring.SPBCSComap

@[expose] public section

/-!
# Ring signatures from a GordieHowe program and a base signer

The program form (the paper's Theorem 5.2, `thm:backend`) of the ring signature
`ofBase B PS adm` (`GordieHowe/Model/RingSignature/Base.lean`): a GordieHowe program whose relation
gives the ring relation of a base signer `B` (`BaseVerifiesRing`), compiled by spBCS at a transcript
of its soundness IOP, is the proof system `PS` (`BaseVerifiesRing.proofSystem`). The program's IOP
and its transcript `TD` are over the program's statements and do not depend on `B`; the base
signer's oracle is the compiled oracle `Bits (queryBits TD.k (2 TD.k) kS 2^40) → XOut TD.k e` of
`TD`, so `B` is chosen after `TD`.

- `BaseVerifiesRing ir I rel relH B adm`: the program verifies base signatures of `B` for the ring
  relation `ringRel B adm H` at every oracle `H`: a map of ring statements to the program's
  statements, a statement check, a map of the program's witnesses to ring witnesses (soundness at
  every oracle), and a partial map of ring witnesses to honest inputs (the honest direction at every
  oracle). `BaseVerifiesRing.ofVerifiesWithoutOracle`: for a base signer whose verification and
  public value read no oracle (`BaseSigner.VerifiesWithoutOracle`), the conditions at one oracle
  suffice.
- `BaseVerifiesRing.proofSystem V G hb hf`: the proof system (`spbcsComapProofSystem` at the setting
  with merges of `TD`, the honest prover of the program, proofs in the format `pB`).
  `BaseVerifiesRing.proofSystem_completeWithin`: it is adaptively complete for the ring relation at
  the honest prover's completeness error `errc`.
- Headlines: `BaseVerifiesRing.completeWithin` and `BaseVerifiesRing.completeAtWithin`: under the
  hypotheses of Theorem 5.2 (`G`, the honest prover complete with error `errc`), the ring signature
  `ofBase B (V.proofSystem G hb hf) adm` refuses with probability at most the base signer's refusal
  rate `ρ` (averaged, or per key) and is rejected with probability at most
  `εc + (errc + overrun + keyCollision + (q + qPub) / 2^(8 kS))` for a base signer with correctness
  error `εc`.

Both directions of `BaseVerifiesRing` quantify over every oracle. For a base signer whose
verification reads the oracle (the ML-DSA ring publishing `w₁`), the program's relation must then
give and contain the ring relation at every commitment hash; this file constructs no such program.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum RealizedProgram RealizedProgram.ProofSystem
  GordieHowe.RingSignature
open scoped NNReal ENNReal

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
    {N : ℕ} {TB : BaseTypes} (B : BaseSigner Xo Yo N TB) (adm : KeyRing B.PK N → Prop) where
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

namespace BaseVerifiesRing

variable {ir : RealizedProgram} {I : RealizedProgram.Interp} {W : Type}
  {rel : Set (ir.Valuation I × W)} {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **For a base signer verifying without the oracle, the conditions at one oracle suffice**: the
ring relation is the same at every oracle (`VerifiesWithoutOracle.ringRel_eq`). -/
def ofVerifiesWithoutOracle {Xo Yo : Type} {N : ℕ} {TB : BaseTypes} {B : BaseSigner Xo Yo N TB}
    {adm : KeyRing B.PK N → Prop} (hB : B.VerifiesWithoutOracle) (H₀ : Xo → Yo)
    (stmt : RingSignature.RingStmt B → ir.Valuation I) (check : RingSignature.RingStmt B → Bool) (wit : RingSignature.RingStmt B → W → RingSignature.RingWit B)
    (sound : ∀ x w, check x = true → (stmt x, w) ∈ rel → (x, wit x w) ∈ RingSignature.ringRel B adm H₀)
    (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Inp)
    (check_eq_true : ∀ x w, (x, w) ∈ RingSignature.ringRel B adm H₀ → check x = true)
    (input_mem : ∀ x w, (x, w) ∈ RingSignature.ringRel B adm H₀ →
      ∃ y ∈ input x w, (stmt x, y) ∈ relH) :
    BaseVerifiesRing ir I rel relH B adm where
  stmt := stmt
  check := check
  wit := wit
  sound H x w hx hw := by
    rw [← hB.ringRel_eq adm H₀ H]
    exact sound x w hx hw
  input := input
  check_eq_true H x w h := check_eq_true x w (by rw [hB.ringRel_eq adm H₀ H]; exact h)
  input_mem H x w h := input_mem x w (by rw [hB.ringRel_eq adm H₀ H]; exact h)

variable {Pl : Export.Plan} {PB : ir.ProofSystem Pl I} {F : PB.FieldBranches}
  {proj : ir.Valuation I → ir.Assignment I → W} {errc : ℝ≥0}
  (G : ProgramHypotheses F rel proj relH errc) {TD : SPBCS.ProofSystemTranscript G.iop} {kS : ℕ}
  (hb : TD.MergeBounds kS) {pB : ℕ} (hf : TD.ProofFormat kS hb pB) {N : ℕ}
  {TB : BaseTypes} {B : BaseSigner (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) N TB}
  {adm : KeyRing B.PK N → Prop} (V : BaseVerifiesRing ir I rel relH B adm)

/-- **The proof system of the program for the ring relation**: spBCS at the setting with merges of
the transcript `TD` (`spbcsComapProofSystem`), the program's honest prover
(`RealizedProgram.ProofSystem.IOP.honest` of `G.honestIOP`) on the honest input `V.input x w` (if
any) of a ring witness at the program's statement `V.stmt x`, proofs in the format `pB`,
verification after the check `V.check`. -/
noncomputable abbrev proofSystem :
    RingSignature.ProofSystem (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant))
      (RingSignature.RingStmt B) (RingSignature.RingWit B)
      (spbcsPST (TD.setting kS hb).model pB G.honestIOP.Coins) :=
  spbcsComapProofSystem (TD.setting kS hb).model (TD.setting kS hb).layout
    (TD.setting kS hb).encoder hf (RealizedProgram.ProofSystem.IOP.honest G.honestIOP) V.stmt
    V.check V.input

/-- **The proof system of the program is adaptively complete for the ring relation**, at the
honest prover's completeness error `errc` (Theorem 5.2 (1), `ProgramHypotheses.errorBound`). -/
theorem proofSystem_completeWithin :
    (V.proofSystem G hb hf).CompleteWithin (RingSignature.ringRel B adm) fun T =>
      (errc : ℝ≥0∞) + (TD.setting kS hb).model.overrun +
        SPBCS.keyCollision (G.iop.term.size G.iop.rounds) TD.k + T / 2 ^ (8 * kS) :=
  spbcsComapProofSystem_completeWithin _ _ _ hf _ _ _ _ adm (TD.setting kS hb).viewEncoder
    (rel₀ := fun x y => (x, y) ∈ relH)
    (fun H p hp => ⟨V.check_eq_true H p.1 p.2 hp, V.input_mem H p.1 p.2 hp⟩)
    fun x y hy => ROM.probUniform_prod_le fun c =>
      RealizedProgram.ProofSystem.IOP.completeness_of_errorBound G.honestIOP G.errorBound c x y hy

variable [DecidablePred adm]

/-- **Completeness of the ring signature of a program that verifies base signatures of `B`**
(BKM06 Definition 1 with errors, averaged over honest rings), under the hypotheses of Theorem 5.2
(`G`): for a base signer with refusal rate `ρ` on honest rings (`hρ`) and correctness error `εc`
(`hc`), the ring signature `RingSignature.ofBase B (V.proofSystem G hb hf) adm` refuses an honest supported ring
with probability at most `ρ` and is rejected with probability at most the correctness error plus
the honest prover's completeness error `errc`, spBCS's overrun and key-collision terms, and
`(q + qPub) / 2^(8 kS)`. -/
@[headline]
theorem completeWithin {ρ εc : ℝ≥0∞} (hρ : B.RefuseWithin adm ρ) (hc : B.CorrectWithin εc) :
    (RingSignature.ofBase B (V.proofSystem G hb hf) adm).CompleteWithin ρ
      (εc + ((errc : ℝ≥0∞) + (TD.setting kS hb).model.overrun +
        SPBCS.keyCollision (G.iop.term.size G.iop.rounds) TD.k +
          ((B.q + B.qPub : ℕ) : ℝ≥0∞) / 2 ^ (8 * kS))) :=
  completeWithin_ofBase B _ adm hρ hc (V.proofSystem_completeWithin G hb hf)

/-- **Completeness per key of the ring signature of a program that verifies base signatures of
`B`**: as `completeWithin`, with the per-key refusal rate `ρ` (`RefuseAtWithin`), at every key and
every supported ring holding it. -/
@[headline]
theorem completeAtWithin {ρ εc : ℝ≥0∞} (hρ : B.RefuseAtWithin adm ρ) (hc : B.CorrectWithin εc) :
    (RingSignature.ofBase B (V.proofSystem G hb hf) adm).CompleteAtWithin ρ
      (εc + ((errc : ℝ≥0∞) + (TD.setting kS hb).model.overrun +
        SPBCS.keyCollision (G.iop.term.size G.iop.rounds) TD.k +
          ((B.q + B.qPub : ℕ) : ℝ≥0∞) / 2 ^ (8 * kS))) :=
  completeAtWithin_ofBase B _ adm hρ hc (V.proofSystem_completeWithin G hb hf)

end BaseVerifiesRing

end GordieHowe.Ring
