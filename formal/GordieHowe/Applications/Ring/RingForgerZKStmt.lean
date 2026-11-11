-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingInsiderStmt
public import GordieHowe.Applications.Ring.RingForgerZK

@[expose] public section

/-!
# The zero-knowledge route from MU-EUF-CMA^corr for the proof systems of programs

The bound of `RingSignature.Insider.insiderForgeProb_le_zk_muEufProb`
(`GordieHowe/Applications/Ring/RingForgerZK.lean`) for the proof system of a compiled IOP over its
own statements (`Ring.StmtVerifiesRing`), with the hypotheses of the zero-knowledge route from
`Ring.StmtVerifiesRing.zkRingHyps`, zero knowledge from `IOP.hvzk_of_errorBound` and knowledge
soundness from `IOP.Sound.causal_rbr`.

- `Ring.StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb`, and for a base signer whose refusals are
  bounded per key or on average over the key coins
  `Ring.StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb_refuseAt`,
  `Ring.StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb_refuseAvg`.
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature GordieHowe.RingSignature.Insider

namespace StmtVerifiesRing

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum RealizedProgram RealizedProgram.ProofSystem
  GordieHowe.RingSignature Signature
open scoped ENNReal NNReal

variable {X₁ W : Type} [Inhabited W] [DecidableEq X₁] {rel₀ : Set (X₁ × W)}
  {C : RealizedProgram.ProofSystem.IOP X₁ W rel₀}
  {SD : C.SimData} {Inp : Type} [Fintype Inp] [DecidableEq Inp] {relI : Set (X₁ × Inp)}
  (Hc : C.Honest SD Inp relI)
  {TD : SPBCS.ProofSystemTranscript C} {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ}
  (hf : TD.ProofFormat kS hb pB) {N : ℕ}
  {TB₁ : BaseTypes}
  {B₁ : BaseSigner (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40))) (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) N TB₁}
  {adm₁ : KeyRing B₁.PK N → Prop} [DecidablePred adm₁]
  (V : StmtVerifiesRing rel₀ relI B₁ adm₁) [RingSignature.EmptyRingTest V.stmt]

variable [Fintype TB₁.PK] [DecidableEq TB₁.PK] [Fintype TB₁.Msg] [DecidableEq TB₁.Msg]
  [Fintype TB₁.BSig] [DecidableEq TB₁.BSig] [Fintype TB₁.Pub] [DecidableEq TB₁.Pub]
  [Fintype TB₁.KeyCoins] [DecidableEq TB₁.KeyCoins] [Nonempty TB₁.KeyCoins] [Fintype TB₁.Coins]
  [DecidableEq TB₁.Coins] [Nonempty TB₁.Coins]

open Classical in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
of a compiled IOP over its own statements, for every base message, from zero knowledge, simulation
extraction and MU-EUF-CMA^corr** (`RingSignature.Insider.insiderForgeProb_le_zk_muEufProb` at
`V.proofSystem`): the bound of `insiderForgeProb_le_zk` with the extraction forger's term bounded by
the success probability of the explicit multi-user forger `zkForger` with `zkQ'` requests, for an
adversary with the schedule bound `S`, `w`, `P'` (`hS`). The forger's multi-user requests are
`publicKey 0` or corruptions among the adversary's first `Q` requests (`zk_bridge_requests`). -/
@[headline]
theorem insiderForgeProb_le_zk_muEufProb [Nonempty B₁.Msg] [Nonempty B₁.Pub] [Nonempty B₁.BSig]
    (hk : 0 < TD.k) {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (Sd : C.Sound)
    (hB : B₁.OracleFree) {refuses : KeyRing B₁.PK N → ℕ → B₁.Msg → B₁.Coins → Prop}
    {pubOf : B₁.Coins → B₁.Pub} (hpub : B₁.PubOfCoins pubOf) (href : B₁.RefusalOfCoins refuses)
    {εc : ℝ≥0∞} (hcorr : B₁.CorrectWithin εc) (hinj : Function.Injective V.stmt)
    (hnil : ∀ x : RingSignature.RingStmt B₁, x.ring.1 = [] → ∀ y, (V.stmt x, y) ∉ relI)
    (T : (TD.setting kS hb).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (ofBase B₁ (V.proofSystem Hc hb hf) adm₁) n
      (OracleView.queriesOnly _ _) t) [NeZero n]
    [Nonempty (SPBCS.NIProof (k := TD.k) (kN := 2 * TD.k) (kS := kS) (L := 2 ^ 40)
      (e := Configurations.fsExtraBytes + TD.maxGrant) (TD.setting kS hb).model)] (Q : ℕ)
    (f₀ : B₁.PK × B₁.BMsg × B₁.BSig)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (zkForger A (wit := V.wit) refuses pubOf Q
          (zkPsim (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
            (TD.setting kS hb).layout hf (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
            V.check V.input adm₁ (TD.setting kS hb).viewEncoder id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T)
          C.extractor (kqOf C.merges C.rounds pB pB) f₀)
        (zkQ' (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
          (TD.setting kS hb).layout hf (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
          V.check V.input adm₁ (TD.setting kS hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) T Q S w P') +
        ENNReal.ofReal ((TD.setting kS hb).model.zkError errc t Q) +
        (TD.setting kS hb).model.simExtractionError (kqOf C.merges C.rounds pB pB)
          (maxError Sd.error)
          ((TD.setting kS hb).model.niJointSimulatorProg (TD.setting kS hb).layout
            (TD.setting kS hb).viewEncoder.toViewRead pB id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T).q t Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (ofBase B₁ (V.proofSystem Hc hb hf) adm₁).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) +
        2 * Q * εc := by
  have h := RingSignature.Insider.insiderForgeProb_le_zk_muEufProb A hk hB hpub href hcorr
    (V.zkRingHyps hinj hnil) (TD.setting kS hb).viewEncoder id _ T
    (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE) Sd.causal_rbr Q f₀ hS
  -- the terms of `h` and of the statement differ in the spelling of the setting's parameters
  convert h using 6 <;> first | with_reducible_and_instances rfl | (congr 1; done) | rfl


open Classical in
/-- **BKM06 Definition 7 for the ring signature of a compiled IOP over its own statements, from zero
knowledge, simulation extraction and MU-EUF-CMA^corr, for a base signer whose refusals are bounded
per key** (`RingSignature.Insider.insiderForgeProb_le_zk_muEufProb_refuseAt` at `V.proofSystem`):
the multi-user forger at the empty refusal predicate, at the cost `Q · ρ`. -/
theorem insiderForgeProb_le_zk_muEufProb_refuseAt [Nonempty B₁.Msg] [Nonempty B₁.Pub] [Nonempty B₁.BSig]
    (hk : 0 < TD.k) {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (Sd : C.Sound)
    (hB : B₁.OracleFree) {pubOf : B₁.Coins → B₁.Pub} (hpub : B₁.PubOfCoins pubOf) {ρ : ℝ≥0∞}
    (hρ : B₁.RefuseAtWithin adm₁ ρ)
    {εc : ℝ≥0∞} (hcorr : B₁.CorrectWithin εc) (hinj : Function.Injective V.stmt)
    (hnil : ∀ x : RingSignature.RingStmt B₁, x.ring.1 = [] → ∀ y, (V.stmt x, y) ∉ relI)
    (T : (TD.setting kS hb).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (ofBase B₁ (V.proofSystem Hc hb hf) adm₁) n
      (OracleView.queriesOnly _ _) t) [NeZero n]
    [Nonempty (SPBCS.NIProof (k := TD.k) (kN := 2 * TD.k) (kS := kS) (L := 2 ^ 40)
      (e := Configurations.fsExtraBytes + TD.maxGrant) (TD.setting kS hb).model)] (Q : ℕ)
    (f₀ : B₁.PK × B₁.BMsg × B₁.BSig)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (zkForger A (wit := V.wit) (fun _ _ _ _ => False) pubOf Q
          (zkPsim (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
            (TD.setting kS hb).layout hf (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
            V.check V.input adm₁ (TD.setting kS hb).viewEncoder id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T)
          C.extractor (kqOf C.merges C.rounds pB pB) f₀)
        (zkQ' (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
          (TD.setting kS hb).layout hf (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
          V.check V.input adm₁ (TD.setting kS hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) T Q S w P') +
        ENNReal.ofReal ((TD.setting kS hb).model.zkError errc t Q) +
        (TD.setting kS hb).model.simExtractionError (kqOf C.merges C.rounds pB pB)
          (maxError Sd.error)
          ((TD.setting kS hb).model.niJointSimulatorProg (TD.setting kS hb).layout
            (TD.setting kS hb).viewEncoder.toViewRead pB id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T).q t Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (ofBase B₁ (V.proofSystem Hc hb hf) adm₁).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) +
        2 * Q * εc + Q * ρ := by
  have h := RingSignature.Insider.insiderForgeProb_le_zk_muEufProb_refuseAt A hk hB hpub hρ hcorr
    (V.zkRingHyps hinj hnil) (TD.setting kS hb).viewEncoder id _ T
    (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE) Sd.causal_rbr Q f₀ hS
  -- the terms of `h` and of the statement differ in the spelling of the setting's parameters
  convert h using 7 <;> first | with_reducible_and_instances rfl | (congr 1; done) | rfl

open Classical in
/-- **BKM06 Definition 7 for the ring signature of a compiled IOP over its own statements, from zero
knowledge, simulation extraction and MU-EUF-CMA^corr, for a base signer whose refusal rate is bounded
on average over the honest key coins**
(`RingSignature.Insider.insiderForgeProb_le_zk_muEufProb_refuseAvg` at `V.proofSystem`): the
multi-user forger at the empty refusal predicate, at the cost `Q · n · ρ`. -/
theorem insiderForgeProb_le_zk_muEufProb_refuseAvg [Nonempty B₁.Msg] [Nonempty B₁.Pub] [Nonempty B₁.BSig]
    (hk : 0 < TD.k) {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (Sd : C.Sound)
    (hB : B₁.OracleFree) {pubOf : B₁.Coins → B₁.Pub} (hpub : B₁.PubOfCoins pubOf) {ρ : ℝ≥0∞}
    (hρ : B₁.RefuseAvgWithin adm₁ ρ)
    {εc : ℝ≥0∞} (hcorr : B₁.CorrectWithin εc) (hinj : Function.Injective V.stmt)
    (hnil : ∀ x : RingSignature.RingStmt B₁, x.ring.1 = [] → ∀ y, (V.stmt x, y) ∉ relI)
    (T : (TD.setting kS hb).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (ofBase B₁ (V.proofSystem Hc hb hf) adm₁) n
      (OracleView.queriesOnly _ _) t) [NeZero n]
    [Nonempty (SPBCS.NIProof (k := TD.k) (kN := 2 * TD.k) (kS := kS) (L := 2 ^ 40)
      (e := Configurations.fsExtraBytes + TD.maxGrant) (TD.setting kS hb).model)] (Q : ℕ)
    (f₀ : B₁.PK × B₁.BMsg × B₁.BSig)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      muEufProb (zkForger A (wit := V.wit) (fun _ _ _ _ => False) pubOf Q
          (zkPsim (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
            (TD.setting kS hb).layout hf (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
            V.check V.input adm₁ (TD.setting kS hb).viewEncoder id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T)
          C.extractor (kqOf C.merges C.rounds pB pB) f₀)
        (zkQ' (ert := ‹RingSignature.EmptyRingTest V.stmt›) n
          (TD.setting kS hb).layout hf (RealizedProgram.ProofSystem.IOP.honest Hc) V.stmt
          V.check V.input adm₁ (TD.setting kS hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) T Q S w P') +
        ENNReal.ofReal ((TD.setting kS hb).model.zkError errc t Q) +
        (TD.setting kS hb).model.simExtractionError (kqOf C.merges C.rounds pB pB)
          (maxError Sd.error)
          ((TD.setting kS hb).model.niJointSimulatorProg (TD.setting kS hb).layout
            (TD.setting kS hb).viewEncoder.toViewRead pB id
            (RealizedProgram.ProofSystem.IOP.simulator SD) T).q t Q +
        SPBCS.knowledgeError TD.k (Configurations.fsExtraBytes + TD.maxGrant)
          (kqOf C.merges C.rounds pB pB)
          (t + Q * (ofBase B₁ (V.proofSystem Hc hb hf) adm₁).q + kqOf C.merges C.rounds pB pB)
          (TD.setting kS hb).model.senc.digestsPerInput C.merges.nJ (maxError Sd.error) +
        2 * Q * εc + Q * (n * ρ) := by
  have h := RingSignature.Insider.insiderForgeProb_le_zk_muEufProb_refuseAvg A hk hB hpub hρ hcorr
    (V.zkRingHyps hinj hnil) (TD.setting kS hb).viewEncoder id _ T
    (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE) Sd.causal_rbr Q f₀ hS
  -- the terms of `h` and of the statement differ in the spelling of the setting's parameters
  convert h using 7 <;> first | with_reducible_and_instances rfl | (congr 1; done) | rfl

end StmtVerifiesRing

end GordieHowe.Ring
