-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Insider
public import GordieHowe.Applications.Ring.Anonymity
public import GordieHowe.Applications.Ring.Completeness
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# Ring signatures from any GordieHowe program

A GordieHowe program that verifies signatures of a base scheme `Sch` for the ring relation gives a
ring signature (BKM06, Bender, Katz, Morselli, TCC 2006; ePrint 2005/304): the ring signature on
`(R, m, ρ)` is the compiled honest proof of the program's proof system, its statement read off the
ring statement, its honest input off the ring witness `(i, σ)`; verification is the compiled
verifier. The theorems here hold for every plan, realized program, interpretation and proof system
with forked domains, with no particular plan:

- `VerifiesRing`: the program verifies `Sch` signatures for the ring relation `ringRel adm bind`:
  a map of ring statements to the program's statements (the ring, the message and the public value
  `ρ`, which for Falcon is the salt), a statement check, a map of the program's witnesses to ring
  witnesses (soundness), and a map of ring witnesses to honest inputs (the honest direction).
- `ProgramHypotheses`: the hypotheses of the plan-level theorem (the paper's Theorem 5.2,
  `thm:backend`) in the series–parallel order: round-by-round knowledge soundness of the source
  protocol, the honest prover with completeness error `errc` (`HonestCore.Complete`), the soundness
  of the forked domain proofs, the domains' honest provers and simulators, and the trust base
  (`CircuitsEnforce`, `CircuitsAccept`).
- `VerifiesRing.ringIOP`: the soundness IOP of Theorem 5.2 read at ring statements
  (`RealizedProgram.ProofSystem.IOP.comapWith`); `VerifiesRing.prover`: its honest prover on a
  ring witness; `VerifiesRing.signer`: the compiled ring signer (spBCS's honest prover at a
  transcript of `ringIOP`, run through `queryEncoding`), the honest prover of the games.

Theorem 5.2 in the series–parallel order gives the hypotheses of the ring theorems at the
compiled argument: the composite's causal round-by-round knowledge soundness
(`RealizedProgram.ProofSystem.IOP.Sound.causal_rbr`) read through the witness map
(`CausalRBR.mapWit`) is `CausalRBRKnowledgeSound` for `ringRel adm bind` at the extractor
`VerifiesRing.extractor`, and its honest-verifier zero knowledge
(`RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound`) at the honest inputs of ring witnesses is
`CausalHVZK` for `ringRel adm bind` at error `errc` (`causalHVZK_ringHonest`). The headlines:

- `VerifiesRing.insiderWinProb_le`: unforgeability with respect to insider corruption (BKM06
  Definition 7) at every `bind`, converted signatures (`bind R m = m`) included, for a base scheme
  with correctness error `εc` (`SigScheme.CorrectWithin`) whose public values are functions of the
  signing coins (`SigScheme.PubOfCoins`), with the forger of the multi-user game reaching the keys
  only through the base oracles (`RelayForger`).
- `VerifiesRing.insiderWinProb_le_of_bindsRing`: the same for a `bind` that binds the ring
  (`BindsRing`), without the zero-knowledge, simulation-extraction and correctness terms.
- `VerifiesRing.convertedWinProb_le`: the converted-signature game.
- `VerifiesRing.keyedAnon_le`: anonymity against full key exposure (BKM06 Definition 4), in the
  one anonymity game (`PubAnonAdversary.game`).
- `VerifiesRing.ringRejectProb_le`: completeness (BKM06 Definition 1), up to the correctness error
  and the honest prover's completeness error.

The errors are those of the program: the largest of its round errors in the series–parallel order
(`ProgramHypotheses.roundError`, the errors of Theorem 5.2's causal round-by-round knowledge
soundness) and the honest prover's completeness error `errc`.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum
open scoped NNReal ENNReal

/-! ### A program verifying base signatures for the ring relation -/

/-- **The program verifies `Sch` signatures for the ring relation** `ringRel adm bind` (BKM06
Definition 1, ePrint 2005/304, p. 3, with `Vrfy_R(M, σ)` the program's verifier on the statement
of `(R, M, ρ)`): for a program whose source protocol is sound for `rel` and whose honest prover
takes inputs `relH`, a map `stmt` of ring statements `(R, m, ρ)` to the program's statements (for
Falcon, `ρ` is the salt, routed to the program's salt input; `Unit` for ML-DSA) and a statement
check `check`, with

* soundness: a witness of `rel` at the program's statement of a checked ring statement gives a ring
  witness (`wit`);
* the honest direction: the statements of the ring relation pass the check, and a ring witness
  gives an honest input (`input`) of the program's honest prover at the program's statement. -/
structure VerifiesRing (ir : RealizedProgram) (I : RealizedProgram.Interp) {W : Type}
    (rel : Set (ir.Valuation I × W)) {Inp : Type} (relH : Set (ir.Valuation I × Inp))
    (Sch : SigScheme) (RMsg : Type) (N : ℕ) (adm : List Sch.PK → Prop)
    (bind : List Sch.PK → RMsg → Sch.Msg) where
  /-- The program's statement of a ring statement. -/
  stmt : RingStmt Sch RMsg N → ir.Valuation I
  /-- The check of a ring statement. -/
  check : RingStmt Sch RMsg N → Bool
  /-- The ring witness of a witness of the program's relation. -/
  wit : RingStmt Sch RMsg N → W → RingWit Sch
  /-- A witness of the program's relation at a checked statement gives a ring witness. -/
  sound : ∀ x w, check x = true → (stmt x, w) ∈ rel → (x, wit x w) ∈ ringRel adm bind
  /-- The honest input of a ring statement and a ring witness. -/
  input : RingStmt Sch RMsg N → RingWit Sch → Inp
  /-- The statements of the ring relation pass the check. -/
  check_eq_true : ∀ x w, (x, w) ∈ ringRel adm bind → check x = true
  /-- A ring witness gives an honest input. -/
  input_mem : ∀ x w, (x, w) ∈ ringRel adm bind → (stmt x, input x w) ∈ relH

/-! ### The honest prover of a ring witness -/

section RingHonest

variable {Sch : SigScheme} {RMsg : Type} {N : ℕ} {W : Type}
  {relC : Set (RingStmt Sch RMsg N × W)}
  {C : RealizedProgram.ProofSystem.IOP (RingStmt Sch RMsg N) W relC}
  {SD : C.SimData} {Inp : Type} {relI : Set (RingStmt Sch RMsg N × Inp)}

/-- **The honest prover of a ring witness**: at the statement `x`, the honest prover of the
multi-circuit IOP with forked domains `C` (`RealizedProgram.ProofSystem.IOP.honest`) at the honest
input `input x w` of the ring witness `w`, with the coins `c` (`CausalProver.ofStmt`). -/
noncomputable def ringHonest (Hc : C.Honest SD Inp relI)
    (input : RingStmt Sch RMsg N → RingWit Sch → Inp) (w : RingWit Sch) (c : Hc.Coins) :
    CausalProver C.P C.term (RingStmt Sch RMsg N) :=
  CausalProver.ofStmt fun x => RealizedProgram.ProofSystem.IOP.honest Hc (input x w) c

/-- **Honest-verifier zero knowledge for the ring relation** (CY24 Definition 23.1.8 for
composites, `CausalHVZK`): if every pair of the ring relation has an honest input of `Hc`
(`hin`) and the completeness events of `Hc` have together probability at most `errc` (`hE`), the
honest prover of a ring witness (`ringHonest`) is zero knowledge for `ringRel adm bind` at the
simulator of `C` (`RealizedProgram.ProofSystem.IOP.simulator`) with error `errc`. Its view at
`(x, w)` is the honest view at `(x, input x w)` (`CausalProver.run_ofStmt`), so this is
`RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound`. -/
theorem causalHVZK_ringHonest {adm : List Sch.PK → Prop} {bind : List Sch.PK → RMsg → Sch.Msg}
    (Hc : C.Honest SD Inp relI) {input : RingStmt Sch RMsg N → RingWit Sch → Inp}
    (hin : ∀ x w, (x, w) ∈ ringRel adm bind → (x, input x w) ∈ relI) {errc : ℝ≥0}
    (hE : Hc.app.ErrorBound fun _ => errc) :
    CausalHVZK C.toCausalIOP.views (ringRel adm bind) (ringHonest Hc input) id
      (RealizedProgram.ProofSystem.IOP.simulator SD) errc := by
  intro x w hw
  have h := RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE x (input x w) (hin x w hw)
  have heq : C.toCausalIOP.views.honestView (ringHonest Hc input) x w =
      C.toCausalIOP.views.honestView (RealizedProgram.ProofSystem.IOP.honest Hc) x
        (input x w) := by
    rw [CausalViews.honestView_eq_map, CausalViews.honestView_eq_map]
    simp only [ringHonest, CausalProver.run_ofStmt]
  rw [heq]
  exact h

end RingHonest

end GordieHowe.Ring

/-! ### The ring signature at a transcript of a multi-circuit IOP with forked domains -/

namespace GordieHowe.SPBCS.ProofSystemTranscript

open IOP GordieHowe.QROM Quantum GordieHowe.Ring
open scoped NNReal ENNReal

variable {Sch : SigScheme} [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg]
  [DecidableEq Sch.Msg] [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub]
  [DecidableEq Sch.Pub] [Nonempty Sch.Pub] [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins]
  [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins] [DecidableEq Sch.SignCoins]
  [Nonempty Sch.SignCoins] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] {N n : ℕ} {W : Type}
  {relC : Set (RingStmt Sch RMsg N × W)}
  {C : RealizedProgram.ProofSystem.IOP (RingStmt Sch RMsg N) W relC}
  {SD : C.SimData} {Inp : Type} {relI : Set (RingStmt Sch RMsg N × Inp)}
  (TD : SPBCS.ProofSystemTranscript C) {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ}
  (hf : TD.ProofFormat kS hb pB) {adm : List Sch.PK → Prop} {bind : List Sch.PK → RMsg → Sch.Msg}
  (Hc : C.Honest SD Inp relI) (input : RingStmt Sch RMsg N → RingWit Sch → Inp)

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) at every `bind`** of
the ring signature compiled at the transcript `TD` of a multi-circuit IOP with forked domains `C`
over ring statements (`BKMAdversary.insiderWinProb_le_of_zeroKnowledge` at the setting with merges
`TD.setting kS hb`): from the soundness `Sd` of `C` with the witness map `g` into the ring relation
(`hg`, causal round-by-round knowledge soundness by `Sound.causal_rbr`), an honest prover `Hc`
with completeness error `errc` (`hE`) on the honest inputs of ring witnesses (`hin`, zero knowledge
by `causalHVZK_ringHonest`), a base scheme with correctness error `εc` (`hcorr`) whose honest
signatures have public values `pubOf` of their signing coins (`hpub`). -/
theorem insiderWinProb_le [Inhabited W] [Nonempty RMsg] [NeZero n] [Nonempty Sch.Sig]
    {εc : ℝ≥0} (hcorr : Sch.CorrectWithin εc) {pubOf : Sch.SignCoins → Sch.Pub}
    (hpub : Sch.PubOfCoins pubOf) (Sd : C.Sound) {g : RingStmt Sch RMsg N → W → RingWit Sch}
    (hg : ∀ x w, (x, w) ∈ relC → (x, g x w) ∈ ringRel adm bind)
    (hin : ∀ x w, (x, w) ∈ ringRel adm bind → (x, input x w) ∈ relI) {errc : ℝ≥0}
    (hE : Hc.app.ErrorBound fun _ => errc) {t Q : ℕ}
    (A : BKMAdversary ((TD.setting kS hb).model.qVerifier (TD.setting kS hb).queries pB pB)
      ((TD.setting kS hb).model.Response pB) n t Q) :
    A.insiderWinProb (((TD.prover kS hb hf (ringHonest Hc input)).mapOutput some).encode
        queryEncoding) (PMF.uniformOfFintype _) bind adm ≤
      A.simForgerSuccess (TD.setting kS hb).layout (TD.setting kS hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) (TD.preimages kS hb) bind adm pubOf
          (C.extractor.mapWit g) +
        ENNReal.ofReal ((TD.setting kS hb).model.zkError errc t Q) +
        (TD.setting kS hb).model.simExtractionError (kqOf C.merges C.rounds pB pB)
          (maxError Sd.error)
          ((TD.setting kS hb).model.niJointSimulatorProg (TD.setting kS hb).layout
            (TD.setting kS hb).viewEncoder.toViewRead pB id
            (RealizedProgram.ProofSystem.IOP.simulator SD) (TD.preimages kS hb)).q t Q +
        knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (((TD.prover kS hb hf (ringHonest Hc input)).mapOutput some).encode
            queryEncoding).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) +
        2 * Q * (εc : ℝ≥0∞) :=
  BKMAdversary.insiderWinProb_le_of_zeroKnowledge (Λ := (TD.setting kS hb).layout) (hb := hf)
    (honest := ringHonest Hc input) (VE := (TD.setting kS hb).viewEncoder) (pub := id)
    (Sim := RealizedProgram.ProofSystem.IOP.simulator SD) (T := TD.preimages kS hb)
    (bind := bind) (adm := adm) (pubOf := pubOf) (A := A) (hk := hb.k_pos) (hcorr := hcorr)
    (hpub := hpub) (hvzk := causalHVZK_ringHonest Hc hin hE) (hrbr := Sd.causal_rbr.mapWit hg)

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Nonempty Sch.Pub] in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) for a base message
that binds the ring** (`BindsRing`) of the ring signature compiled at the transcript `TD`
(`BKMAdversary.insiderWinProb_le` at the setting with merges), from the soundness `Sd` of `C`
with the witness map `g` into the ring relation (`hg`). -/
theorem insiderWinProb_le_of_bindsRing [Inhabited W] (hbind : BindsRing N bind)
    (Sd : C.Sound) {g : RingStmt Sch RMsg N → W → RingWit Sch}
    (hg : ∀ x w, (x, w) ∈ relC → (x, g x w) ∈ ringRel adm bind) {t Q : ℕ}
    (A : BKMAdversary ((TD.setting kS hb).model.qVerifier (TD.setting kS hb).queries pB pB)
      ((TD.setting kS hb).model.Response pB) n t Q) :
    A.insiderWinProb (((TD.prover kS hb hf (ringHonest Hc input)).mapOutput some).encode
        queryEncoding) (PMF.uniformOfFintype _) bind adm ≤
      (A.forger (((TD.prover kS hb hf (ringHonest Hc input)).mapOutput some).encode
          queryEncoding) (PMF.uniformOfFintype _) bind adm
          ((TD.setting kS hb).model.dbExtractBits (C.extractor.mapWit g))).success +
        knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (((TD.prover kS hb hf (ringHonest Hc input)).mapOutput some).encode
            queryEncoding).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  BKMAdversary.insiderWinProb_le (Λ := (TD.setting kS hb).layout) (hb := hf)
    (honest := ringHonest Hc input) (bind := bind) (adm := adm) (A := A) (hbind := hbind)
    (hrbr := Sd.causal_rbr.mapWit hg)

omit [Nonempty Sch.Pub] in
/-- **Unforgeability in the converted-signature game** of the ring signature compiled at the
transcript `TD` (`RingAdversary.convertedWinProb_le` at the setting with merges), from the
soundness `Sd` of `C` with the witness map `g` into the ring relation (`hg`). -/
theorem convertedWinProb_le [Inhabited W] (Sd : C.Sound) {g : RingStmt Sch RMsg N → W → RingWit Sch}
    (hg : ∀ x w, (x, w) ∈ relC → (x, g x w) ∈ ringRel adm bind) {t Q : ℕ}
    (A : RingAdversary ((TD.setting kS hb).model.qVerifier (TD.setting kS hb).queries pB pB)
      ((TD.setting kS hb).model.Response pB) n t Q) :
    A.convertedWinProb (((TD.prover kS hb hf (ringHonest Hc input)).mapOutput some).encode
        queryEncoding) (PMF.uniformOfFintype _) bind ≤
      (A.forger (((TD.prover kS hb hf (ringHonest Hc input)).mapOutput some).encode
          queryEncoding) (PMF.uniformOfFintype _) bind
          ((TD.setting kS hb).model.dbExtractBits (C.extractor.mapWit g))).success +
        knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (((TD.prover kS hb hf (ringHonest Hc input)).mapOutput some).encode
            queryEncoding).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) :=
  RingAdversary.convertedWinProb_le (Λ := (TD.setting kS hb).layout) (hb := hf)
    (honest := ringHonest Hc input) (bind := bind) (adm := adm) (A := A)
    (hrbr := Sd.causal_rbr.mapWit hg)

omit [Fintype RMsg] in
/-- **Anonymity against full key exposure (BKM06 Definition 4)** of the ring signature compiled at
the transcript `TD` (`keyedAnon_le` at the setting with merges, what the proof reveals read off
the composite view by `viewEncoder.toReveal`): from an honest prover `Hc` with completeness error
`errc` (`hE`) on the honest inputs of ring witnesses (`hin`, zero knowledge by
`causalHVZK_ringHonest`), for a base scheme with correctness error `εc` (`hcorr`) whose honest
signatures have public values `pubOf` of their signing coins (`hpub`), and an adversary with at
most `Cc` valid challenges per vector of keys (`hA`). -/
theorem keyedAnon_le [DecidablePred adm] {εc : ℝ≥0} (hcorr : Sch.CorrectWithin εc)
    {pubOf : Sch.SignCoins → Sch.Pub} (hpub : Sch.PubOfCoins pubOf)
    (hin : ∀ x w, (x, w) ∈ ringRel adm bind → (x, input x w) ∈ relI) {errc : ℝ≥0}
    (hE : Hc.app.ErrorBound fun _ => errc) {Q Cc : ℕ}
    (A : KeyedAnonAdversary (TD.setting kS hb).model adm bind n Q) (hA : A.ValidCountLe Cc)
    (D : (Fin n → Sch.KeyCoins) → _ → PubHist Sch.Pub (TD.setting kS hb).model.NIProof Q → Prop) :
    keyedAnonAdvantage (TD.setting kS hb).model (TD.setting kS hb).encoder
        (TD.setting kS hb).queries (ringHonest Hc input) A D ≤
      Q * (TD.setting kS hb).model.wiError errc (Q * Cc) + 2 * Q * εc :=
  keyedAnon_le_of_correctWithin (TD.setting kS hb).model hcorr hpub
    (TD.setting kS hb).viewEncoder.toReveal (causalHVZK_ringHonest Hc hin hE) A hA D

omit [Fintype RMsg] [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Nonempty Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins] in
/-- **The completeness guarantees of spBCS for the honest prover of a ring witness** at the
transcript `TD` (`SPBCS.completenessGuarantees`): on the ring relation, the composite verifier
rejects the honest run with probability at most `errc` (`RealizedProgram.ProofSystem.IOP.completeness_of_errorBound`
at the honest input of the ring witness, `hin`, `hE`). -/
theorem completenessGuarantees_ringHonest
    (hin : ∀ x w, (x, w) ∈ ringRel adm bind → (x, input x w) ∈ relI) {errc : ℝ≥0}
    (hE : Hc.app.ErrorBound fun _ => errc) :
    (TD.setting kS hb).model.CompletenessGuarantees (TD.setting kS hb).encoder
      (TD.setting kS hb).queries (ringHonest Hc input) (ringRel adm bind) errc :=
  completenessGuarantees fun x w hw => ROM.probUniform_prod_le fun c => by
    have h := RealizedProgram.ProofSystem.IOP.completeness_of_errorBound Hc hE c x (input x w)
      (hin x w hw)
    simp only [ringHonest, CausalProver.run_ofStmt]
    exact h

end GordieHowe.SPBCS.ProofSystemTranscript

/-! ### The ring signature of a program -/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum RealizedProgram RealizedProgram.ProofSystem
open scoped NNReal ENNReal

variable {Pl : Export.Plan} {ir : RealizedProgram} {I : RealizedProgram.Interp}
  {B : ir.ProofSystem Pl I}

/-- **The hypotheses of the plan-level theorem in the series–parallel order** (the paper's
Theorem 5.2, `thm:backend`; `FieldBranches.causal_rbr_knowledge_soundness`,
`FieldBranches.completeness`, `FieldBranches.hvzk`, and the end-to-end theorem
`FieldBranches.e2eWith`) at the proof system `B` with forked domain proofs `F`, for the relation
`rel` with the projection `proj`, and the honest inputs `relH` at completeness error `errc`: the
source protocol `Π_P₀` is round-by-round knowledge sound with errors that vanish at `γ_end`, the
honest prover is complete with error `errc` (`HonestCore.Complete`, `def:o-guarantees` (1)), the
forked domain proofs are sound, with the domains' honest provers and simulators, under the trust
base (`CircuitsEnforce`, `CircuitsAccept`). -/
structure ProgramHypotheses (F : B.FieldBranches) {W : Type} (rel : Set (ir.Valuation I × W))
    (proj : ir.Valuation I → ir.Assignment I → W) {Inp : Type}
    (relH : Set (ir.Valuation I × Inp)) (errc : ℝ≥0) where
  /-- The forked domain proofs are sound. -/
  forkSound : F.Sound
  /-- The state function of the source protocol. -/
  stateFn : KnowledgeStateFunction (ir.sourceVerifier I)
  /-- The round errors of the source protocol. -/
  sourceError : (ir.sourceSpec I).ChallengeIdx → ℝ≥0
  /-- The source protocol is round-by-round knowledge sound for `rel`. -/
  source_rbr : RBRKnowledgeSound rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) stateFn
    sourceError
  /-- Its errors vanish at `γ_end`. -/
  sourceError_final : ∀ i, ir.rounds.get i.1 = .final → sourceError i = 0
  /-- The domains' simulators. -/
  domainSims : B.DomainSims
  /-- The domains' honest provers. -/
  honestDomains : B.HonestDomains domainSims
  /-- The forked domains' simulators. -/
  forkSims : F.ForkSims
  /-- The forked domains' honest provers. -/
  forkHonest : ∀ d, F.ForkDomainHonest d (honestDomains d).In (honestDomains d).dom (forkSims d)
  /-- The honest prover. -/
  honest : ir.HonestCore I relH
  /-- The honest prover is complete with error `errc`. -/
  complete : honest.Complete fun _ => errc

namespace ProgramHypotheses

variable {F : B.FieldBranches} {W : Type} {rel : Set (ir.Valuation I × W)}
  {proj : ir.Valuation I → ir.Assignment I → W} {Inp : Type} {relH : Set (ir.Valuation I × Inp)}
  {errc : ℝ≥0} (G : ProgramHypotheses F rel proj relH errc)

/-- The lowering of the soundness theorem (`ProofSystem.lowering`). -/
abbrev lowering :=
  B.lowering ⟨_, G.source_rbr, G.sourceError_final⟩

/-- **The multi-circuit IOP with forked domains of the soundness theorem**
(`FieldBranches.soundIOP`). -/
abbrev iop : RealizedProgram.ProofSystem.IOP (ir.Valuation I) (ir.Valuation I → W) (relOf rel) :=
  F.soundIOP G.source_rbr G.sourceError_final

/-- Its soundness (`FieldBranches.soundIOPSound`). -/
noncomputable abbrev iopSound : G.iop.Sound :=
  F.soundIOPSound G.forkSound G.source_rbr G.sourceError_final

/-- **The round errors of the program in the series–parallel order** (`IOP.Sound.error`): the
errors of Theorem 5.2's causal round-by-round knowledge soundness
(`FieldBranches.causal_rbr_knowledge_soundness`), every challenge with its own error. -/
noncomputable abbrev roundError := G.iopSound.error

/-- The simulator data of the soundness IOP (`FieldBranches.simDataAt`). -/
abbrev simData : G.iop.SimData := F.simDataAt G.lowering G.forkSims

/-- The honest prover of the soundness IOP (`FieldBranches.honestAt`). -/
abbrev honestIOP : G.iop.Honest G.simData Inp relH :=
  F.honestAt G.lowering G.honestDomains G.forkHonest G.honest

/-- The completeness events of the honest prover have together probability at most `errc`. -/
theorem errorBound : G.honestIOP.app.ErrorBound fun _ => errc :=
  F.errorBound_honestAt G.lowering G.honestDomains G.forkHonest G.honest G.complete

end ProgramHypotheses

namespace VerifiesRing

variable {F : B.FieldBranches} {W : Type} {rel : Set (ir.Valuation I × W)}
  {proj : ir.Valuation I → ir.Assignment I → W} {Inp : Type} {relH : Set (ir.Valuation I × Inp)}
  {errc : ℝ≥0} {Sch : SigScheme} {RMsg : Type} {N : ℕ} {adm : List Sch.PK → Prop}
  {bind : List Sch.PK → RMsg → Sch.Msg} (V : VerifiesRing ir I rel relH Sch RMsg N adm bind)
  (G : ProgramHypotheses F rel proj relH errc)

/-- **The IOP of the ring signature**: the soundness IOP read at ring statements through
`V.stmt` and checked by `V.check` (`RealizedProgram.ProofSystem.IOP.comapWith`). -/
abbrev ringIOP := G.iop.comapWith V.stmt V.check

/-- Its soundness: the program's (`Sound.comapWith`), with the same round errors. -/
noncomputable abbrev ringSound : (V.ringIOP G).Sound := G.iopSound.comapWith V.stmt V.check

/-- Its honest prover on the honest inputs at checked statements (`Honest.comapWith`). -/
abbrev ringHonestIOP := G.honestIOP.comapWith V.stmt V.check

/-- **The ring witness of a witness of the IOP** (a function of the program's statements). -/
def witOf (x : RingStmt Sch RMsg N) (w : ir.Valuation I → W) : RingWit Sch :=
  V.wit x (w (V.stmt x))

/-- The witness map sends the relation of the ring IOP into the ring relation. -/
theorem mem_ringRel (x : RingStmt Sch RMsg N) (w : ir.Valuation I → W)
    (h : V.check x = true ∧ (V.stmt x, w) ∈ relOf rel) : (x, V.witOf x w) ∈ ringRel adm bind :=
  V.sound x _ h.1 h.2

/-- A pair of the ring relation has an honest input of the ring IOP's honest prover. -/
theorem mem_honestRel (x : RingStmt Sch RMsg N) (w : RingWit Sch) (h : (x, w) ∈ ringRel adm bind) :
    V.check x = true ∧ (V.stmt x, V.input x w) ∈ relH :=
  ⟨V.check_eq_true x w h, V.input_mem x w h⟩

/-- **The honest prover of a ring witness** at the ring IOP (`ringHonest` at `V.input`). -/
noncomputable def prover : RingWit Sch → (V.ringHonestIOP G).Coins →
    CausalProver (V.ringIOP G).P (V.ringIOP G).term (RingStmt Sch RMsg N) :=
  ringHonest (V.ringHonestIOP G) V.input

/-- **The simulator of the ring IOP** (`RealizedProgram.ProofSystem.IOP.simulator`).

Running time: that of `RealizedProgram.ProofSystem.IOP.simulator` (its paragraph), with the
application phase's simulator reading the program's statement `V.stmt x` (`Sim.comapWith`).
This running time is argued here, not proved in Lean. -/
abbrev simulator : CausalJointSimulator (V.ringIOP G).toCausalIOP.views (RingStmt Sch RMsg N) :=
  RealizedProgram.ProofSystem.IOP.simulator (G.simData.comapWith V.stmt V.check)

/-- **The extractor of the ring IOP**: the IOP's extractor (`RealizedProgram.ProofSystem.IOP.extractor`)
with its witness read as a ring witness (`witOf`).

Running time: one run of `RealizedProgram.ProofSystem.IOP.extractor` (its paragraph) and one
application of `V.stmt` and `V.wit`. This running time is argued here, not proved in Lean. -/
abbrev extractor [Inhabited W] :
    CausalExtractor (V.ringIOP G).P (V.ringIOP G).term (RingStmt Sch RMsg N) (RingWit Sch) :=
  (V.ringIOP G).extractor.mapWit V.witOf

/-- The verifier's query budget at proofs in the format `pB` (`kqOf`). -/
abbrev kq (pB : ℕ) : ℕ := kqOf (V.ringIOP G).merges (V.ringIOP G).rounds pB pB

variable [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Nonempty Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [DecidableEq Sch.SignCoins] [Nonempty Sch.SignCoins]

variable [Fintype RMsg] [DecidableEq RMsg] {TD : SPBCS.ProofSystemTranscript (V.ringIOP G)}
  {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ} (hf : TD.ProofFormat kS hb pB)

/-- **The compiled ring signer**: spBCS's honest prover at the transcript `TD` of the ring IOP
(`ProofSystemTranscript.prover`, proofs in the format `pB`) at the honest prover of a ring witness
(`prover`), run through `queryEncoding`. It is the honest prover of the ring games: a ring
signature on `(R, m, ρ)` by the member at position `i` with base signature `σ` is its proof on the
statement with the witness `(i, σ)`. -/
noncomputable abbrev signer :=
  ((TD.prover kS hb hf (V.prover G)).mapOutput some).encode queryEncoding

variable (pB) in
/-- The simulator's queries per proof query (`SPBCS.niJointSimulatorProg`). -/
noncomputable abbrev simQueries : ℕ :=
  ((TD.setting kS hb).model.niJointSimulatorProg (TD.setting kS hb).layout
    (TD.setting kS hb).viewEncoder.toViewRead pB id (V.simulator G) (TD.preimages kS hb)).q

variable (pB) in
/-- **The compiled verifier of the ring signature**: spBCS's verifier at the setting with merges of
`TD`, proofs in the format `pB` (`SPBCS.qVerifier`). -/
abbrev verifier :=
  (TD.setting kS hb).model.qVerifier (TD.setting kS hb).queries pB pB

variable (pB) in
/-- The ring signatures' proofs in the format `pB` (`SPBCS.Response`). -/
abbrev Proof : Type := (TD.setting kS hb).model.Response pB

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) at every `bind`, of
the ring signature of a program that verifies `Sch` signatures for the ring relation** (TCC 2006,
LNCS p. 67; ePrint 2005/304, p. 7: adversarially chosen rings, adaptive corruption, ring-signing
queries, no ordinary signing oracle), including converted signatures (`bind R m = m`). For every
plan, realized program, interpretation and proof system `B` with forked domain proofs `F`, if the
program verifies `Sch` signatures for the ring relation (`V`) and the hypotheses of the paper's
Theorem 5.2 (`thm:backend`) hold (`G`: the source protocol round-by-round knowledge sound, the
honest prover complete with error `errc`, the forked domain proofs sound, the trust base), then for
a base scheme with correctness error `εc` (`hcorr`) whose honest signatures have public values
`pubOf` of their signing coins (`hpub`: Falcon's salt, or `Pub = Unit`) and the ring signature
compiled at a transcript `TD` of the ring IOP (`signer`), the probability that an adversary of
BKM06 with at most `Q` requests and `t` queries of its own wins (`insiderWinProb`) is at most

* the success probability of the explicit forger of the multi-user signature game
  (`simForgerSuccess`, `RelayForger.success`: the forger reaches the keys only through public keys
  and corruptions of the base oracles, makes no signing request, simulates the ring signatures by
  the program's simulator, extracts with the program's extractor and outputs one candidate),
* plus the zero-knowledge error `zkError errc t Q` (all `Q` requests counted as proof queries:
  public-key and corruption requests are relayed as proof queries of a statement with no witness),
* plus the simulation-extraction error at the largest round error of the program
  (`ProgramHypotheses.roundError`: the errors of the series–parallel composite, every challenge
  with its own error, `IOP.Sound.error`),
* plus the knowledge error at that round error and `t + Q · q_P + kq` queries (the forgeries on
  the empty ring, which has no witness),
* plus `2 Q εc` (a ring signature whose drawn base signature fails to verify, once in the real and
  once in the simulated game). -/
theorem insiderWinProb_le [Inhabited W] [Nonempty RMsg] {n : ℕ} [NeZero n] [Nonempty Sch.Sig]
    {εc : ℝ≥0} (hcorr : Sch.CorrectWithin εc) {pubOf : Sch.SignCoins → Sch.Pub}
    (hpub : Sch.PubOfCoins pubOf) {t Q : ℕ}
    (A : BKMAdversary (V.verifier G hb pB) (V.Proof G hb pB) n t Q) :
    A.insiderWinProb (V.signer G hb hf) (PMF.uniformOfFintype _) bind adm ≤
      A.simForgerSuccess (TD.setting kS hb).layout (TD.setting kS hb).viewEncoder id
          (V.simulator G) (TD.preimages kS hb) bind adm pubOf (V.extractor G) +
        ENNReal.ofReal ((TD.setting kS hb).model.zkError errc t Q) +
        (TD.setting kS hb).model.simExtractionError (V.kq G pB) (maxError G.roundError)
          (V.simQueries G hb pB) t Q +
        knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant) (V.kq G pB)
          (t + Q * (V.signer G hb hf).q + V.kq G pB) (TD.setting kS hb).model.senc.digestsPerInput
          (V.ringIOP G).merges.nJ (maxError G.roundError) +
        2 * Q * (εc : ℝ≥0∞) :=
  TD.insiderWinProb_le hb hf (V.ringHonestIOP G) V.input hcorr hpub (V.ringSound G)
    (fun x w h => V.mem_ringRel x w h) (fun x w h => V.mem_honestRel x w h)
    (G.errorBound.comapWith _ _) A

omit [Fintype Sch.Msg] [DecidableEq Sch.Msg] [Nonempty Sch.Pub] in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) for a base message
that binds the ring** (`BindsRing`: `bind` injective on the rings of at most `N` keys), of the ring
signature of a program that verifies `Sch` signatures for the ring relation, under the hypotheses
of Theorem 5.2 (`G`): the probability that an adversary of BKM06 wins is at most the success
probability of the explicit forger of the multi-user signature game with adaptive corruption
(`BKMAdversary.forger`, the witness extracted by the program's extractor), plus the knowledge error
at the largest round error of the program and `t + Q · q_P + kq` queries. No correctness of the
base scheme is used: the forger asks the base signatures of the ring-signing requests. -/
theorem insiderWinProb_le_of_bindsRing [Inhabited W] {n : ℕ} (hbind : BindsRing N bind) {t Q : ℕ}
    (A : BKMAdversary (V.verifier G hb pB) (V.Proof G hb pB) n t Q) :
    A.insiderWinProb (V.signer G hb hf) (PMF.uniformOfFintype _) bind adm ≤
      (A.forger (V.signer G hb hf) (PMF.uniformOfFintype _) bind adm
          ((TD.setting kS hb).model.dbExtractBits (V.extractor G))).success +
        knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant) (V.kq G pB)
          (t + Q * (V.signer G hb hf).q + V.kq G pB) (TD.setting kS hb).model.senc.digestsPerInput
          (V.ringIOP G).merges.nJ (maxError G.roundError) :=
  TD.insiderWinProb_le_of_bindsRing hb hf (V.ringHonestIOP G) V.input hbind (V.ringSound G)
    (fun x w h => V.mem_ringRel x w h) A

omit [Nonempty Sch.Pub] in
/-- **Unforgeability in the converted-signature game** (`RingAdversary.convertedWinProb`:
a valid ring signature on `(R*, m*)` by uncorrupted honest keys implies that some member of `R*`
was asked to sign `bind R* m*`), of the ring signature of a program that verifies `Sch` signatures
for the ring relation, under the hypotheses of Theorem 5.2 (`G`): the probability that a ring
adversary wins is at most the success probability of the explicit forger of the multi-user
signature game with adaptive corruption (`RingAdversary.forger`), plus the knowledge error at the
largest round error of the program and `t + Q · q_P + kq` queries. -/
theorem convertedWinProb_le [Inhabited W] {n : ℕ} {t Q : ℕ}
    (A : RingAdversary (V.verifier G hb pB) (V.Proof G hb pB) n t Q) :
    A.convertedWinProb (V.signer G hb hf) (PMF.uniformOfFintype _) bind ≤
      (A.forger (V.signer G hb hf) (PMF.uniformOfFintype _) bind
          ((TD.setting kS hb).model.dbExtractBits (V.extractor G))).success +
        knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant) (V.kq G pB)
          (t + Q * (V.signer G hb hf).q + V.kq G pB) (TD.setting kS hb).model.senc.digestsPerInput
          (V.ringIOP G).merges.nJ (maxError G.roundError) :=
  TD.convertedWinProb_le hb hf (V.ringHonestIOP G) V.input (V.ringSound G)
    (fun x w h => V.mem_ringRel x w h) A

omit [Fintype RMsg] [Fintype Sch.PK] [DecidableEq Sch.PK] [Fintype Sch.Msg] [DecidableEq Sch.Msg]
  [Fintype Sch.Sig] [DecidableEq Sch.Sig] [Fintype Sch.Pub] [DecidableEq Sch.Pub] [Nonempty Sch.Pub]
  [Fintype Sch.KeyCoins] [DecidableEq Sch.KeyCoins] [Nonempty Sch.KeyCoins]
  [DecidableEq Sch.SignCoins] in
/-- **Completeness of the ring signature of a program that verifies `Sch` signatures for the ring
relation** (BKM06 Definition 1, ePrint 2005/304, p. 3), under the hypotheses of Theorem 5.2 (`G`):
on an admissible ring (`hadm`) holding the key of `kc` at position `i` (`hi`, `hR`), the honest
ring signature of the compiled signer is rejected by the compiled verifier with probability at most
the honest prover's completeness error `errc` (Theorem 5.2 (1)) plus spBCS's overrun and
key-collision terms plus the base scheme's correctness error `εc` (`hcorr`), at every Merkle salts
and Fiat–Shamir salt (`ringRejectProb_le`). -/
theorem ringRejectProb_le {εc : ℝ≥0∞} (hcorr : Sch.CorrectWithin εc) {kc : Sch.KeyCoins}
    {Rg : RingOf Sch.PK N} {m : RMsg} {i : ℕ} (hadm : adm Rg.1) (hi : i < Rg.1.length)
    (hR : Rg.1[i] = Sch.pk kc) (ν : (TD.setting kS hb).model.Pos → MerkleSalt (2 * TD.k))
    (σ : FiatShamirSalt kS) :
    ringRejectProb bind (TD.setting kS hb).model (TD.setting kS hb).encoder
        (TD.setting kS hb).queries (V.prover G) kc Rg m i ν σ ≤
      errc + (TD.setting kS hb).model.overrun +
        SPBCS.keyCollision ((V.ringIOP G).term.size (V.ringIOP G).rounds) TD.k + εc :=
  Ring.ringRejectProb_le bind (TD.setting kS hb).model (TD.setting kS hb).encoder
    (TD.setting kS hb).queries (V.prover G) hcorr
    (TD.completenessGuarantees_ringHonest hb (V.ringHonestIOP G) V.input
      (fun x w h => V.mem_honestRel x w h) (G.errorBound.comapWith _ _)) hadm hi hR ν σ

omit [Fintype RMsg] in
/-- **Anonymity against full key exposure (BKM06 Definition 4, ePrint 2005/304, p. 6)**, with the
ring's other members adversarial and `Q` adaptive challenges (`keyedAnonAdvantage`, the game
`PubAnonAdversary.game` at the generic signer; keys given at the start as in CCLM22 Experiment 2,
p. 21; deterministic adversaries given the whole oracle), of the ring signature of a program that
verifies `Sch` signatures for the ring relation, under the hypotheses of Theorem 5.2 (`G`): for a
base scheme with correctness error `εc` (`hcorr`) whose honest signatures have public values
`pubOf` of their signing coins (`hpub`), every adversary with at most `Cc` challenges valid for
each vector of keys (`hA`), and every distinguisher given the users' key-generation coins, the
whole oracle and the history of public values and ring signatures, the advantage is at most
`Q · wiError errc (Q · Cc) + 2 Q εc`: the program's zero knowledge at the honest prover's
completeness error `errc` (Theorem 5.2 (1)) gives unconditional witness indistinguishability of
spBCS (`SPBCS.witnessIndistinguishable`). -/
theorem keyedAnon_le [DecidablePred adm] {εc : ℝ≥0} (hcorr : Sch.CorrectWithin εc)
    {pubOf : Sch.SignCoins → Sch.Pub} (hpub : Sch.PubOfCoins pubOf) {n Q Cc : ℕ}
    (A : KeyedAnonAdversary (TD.setting kS hb).model adm bind n Q) (hA : A.ValidCountLe Cc)
    (D : (Fin n → Sch.KeyCoins) → _ → PubHist Sch.Pub (TD.setting kS hb).model.NIProof Q → Prop) :
    keyedAnonAdvantage (TD.setting kS hb).model (TD.setting kS hb).encoder
        (TD.setting kS hb).queries (V.prover G) A D ≤
      Q * (TD.setting kS hb).model.wiError errc (Q * Cc) + 2 * Q * εc :=
  TD.keyedAnon_le hb (V.ringHonestIOP G) V.input hcorr hpub (fun x w h => V.mem_honestRel x w h)
    (G.errorBound.comapWith _ _) A hA D

end VerifiesRing

end GordieHowe.Ring
