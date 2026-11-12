-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingInsider
public import GordieHowe.Applications.Ring.StmtBase
public import GordieHowe.ProofSystem.Program.ForkJoinZK

@[expose] public section

/-!
# The zero-knowledge route for the proof systems of programs

The hypotheses `RingSignature.Insider.ZKRingHyps` of the zero-knowledge route
(`GordieHowe/Applications/Ring/RingInsider.lean`, `RingSignature.Insider.insiderForgeProb_le_zk`)
for the proof system of a program over its own statements (`Ring.StmtVerifiesRing`,
`GordieHowe/Applications/Ring/StmtBase.lean`).

- `Ring.StmtVerifiesRing.zkRingHyps`: they hold when the statement map is injective and no
  statement of the empty ring has an honest input; the honest inputs are relayed as themselves,
  encoded by the honest-input map itself (no inhabitant of the input type is needed).
- `Ring.StmtVerifiesRing.insiderForgeProb_le_zk_refuseAt`,
  `Ring.StmtVerifiesRing.insiderForgeProb_le_zk_refuseAvg`: the same for a base signer whose
  refusals are bounded per key or on average over the key coins, at the cost `Q · ρ` or `Q · n · ρ`.
- `Ring.StmtVerifiesRing.insiderForgeProb_le_zk`: the bound at the proof system of a compiled
  IOP over its own statements (`StmtVerifiesRing.proofSystem`), zero knowledge by
  `IOP.hvzk_of_errorBound` and knowledge soundness by `IOP.Sound.causal_rbr`. Its form by
  MU-EUF-CMA^corr (`Ring.StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb`) is the headline.
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature GordieHowe.RingSignature.Insider

variable {Xo Yo : Type} [AddGroup Yo] {N : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner Xo Yo N TS RMsg}
  {adm : KeyRing B.PK N → Prop} {X₀ : Type}

/-- **A program's proof system of `StmtVerifiesRing` meets the hypotheses of the zero-knowledge
route** when its statement map is injective (`hinj`) and no statement of the empty ring has an
honest input in `relI` (`hnil`): the honest inputs are relayed as themselves, encoded by `input`
(no encoding where there is no honest input), the knowledge relation's witnesses decoded by
`V.wit`. -/
theorem StmtVerifiesRing.zkRingHyps {W Inp : Type} {rel₀ : Set (X₀ × W)}
    {relI : Set (X₀ × Inp)} (V : StmtVerifiesRing rel₀ relI B adm)
    (hinj : Function.Injective V.stmt)
    (hnil : ∀ x : RingSignature.RingStmt B, x.ring.1 = [] → ∀ y, (V.stmt x, y) ∉ relI) :
    ZKRingHyps B adm V.stmt V.check V.input id (fun x w => V.input x w.toWit) relI rel₀ V.wit where
  stmt_injective := hinj
  enc_some x w h := by
    obtain ⟨y, hy, hrel⟩ := V.input_mem 0 x w.toWit h
    exact ⟨y, Option.mem_def.1 hy, Option.mem_def.1 hy, hrel⟩
  not_mem_relH_nil := hnil
  sound x w hc h := V.sound 0 x w hc h

/-- **The statement-side facts of the zero-knowledge route** for `V`: a decided test of the
statements of the empty ring (`RingSignature.EmptyRingTest`, read by the simulator of the route),
the statement map is injective, and no statement of the empty ring has an honest input in
`relI`. -/
structure StmtVerifiesRing.ZKFacts {W Inp : Type} {rel₀ : Set (X₀ × W)} {relI : Set (X₀ × Inp)}
    (V : StmtVerifiesRing rel₀ relI B adm) where
  /-- The test of the statements of the empty ring. -/
  emptyTest : RingSignature.EmptyRingTest V.stmt
  /-- The statement map is injective. -/
  stmt_injective : Function.Injective V.stmt
  /-- No statement of the empty ring has an honest input. -/
  not_mem_relH_nil : ∀ x : RingSignature.RingStmt B, x.ring.IsEmpty → ∀ y, (V.stmt x, y) ∉ relI

/-- **The zero-knowledge route's hypotheses from the statement-side facts**
(`StmtVerifiesRing.zkRingHyps`). -/
theorem StmtVerifiesRing.ZKFacts.zkRingHyps {W Inp : Type} {rel₀ : Set (X₀ × W)}
    {relI : Set (X₀ × Inp)} {V : StmtVerifiesRing rel₀ relI B adm} (zkf : V.ZKFacts) :
    ZKRingHyps B adm V.stmt V.check V.input id (fun x w => V.input x w.toWit) relI rel₀ V.wit :=
  V.zkRingHyps zkf.stmt_injective zkf.not_mem_relH_nil

/-! ### The proof system of a compiled IOP over its own statements -/

namespace StmtVerifiesRing

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum RealizedProgram RealizedProgram.ProofSystem
  GordieHowe.RingSignature
open scoped ENNReal NNReal

variable {X₁ W : Type} [Inhabited W] [DecidableEq X₁] {rel₀ : Set (X₁ × W)}
  {C : RealizedProgram.ProofSystem.IOP X₁ W rel₀}
  {SD : C.SimData} {Inp : Type} [Fintype Inp] [DecidableEq Inp] {relI : Set (X₁ × Inp)}
  (Hc : C.Honest SD Inp relI)
  {TD : SPBCS.ProofSystemTranscript C} {kS : ℕ} (hb : TD.MergeBounds kS) {pB : ℕ}
  (hf : TD.ProofFormat kS hb pB) {N : ℕ}
  {TS₁ : Signature.SchemeTypes} {RMsg₁ : Type}
  {B₁ : BaseSigner (Bits (queryBits TD.k (2 * TD.k) kS (2 ^ 40)))
    (XOut TD.k (Configurations.fsExtraBytes + TD.maxGrant)) N TS₁ RMsg₁}
  {adm₁ : KeyRing B₁.PK N → Prop} [DecidablePred adm₁]
  (V : StmtVerifiesRing rel₀ relI B₁ adm₁)

variable [Fintype TS₁.PK] [DecidableEq TS₁.PK] [Fintype RMsg₁] [DecidableEq RMsg₁]
  [Fintype TS₁.BSig] [DecidableEq TS₁.BSig] [Fintype TS₁.Pub] [DecidableEq TS₁.Pub]
  [Fintype TS₁.KeyCoins] [DecidableEq TS₁.KeyCoins] [Nonempty TS₁.KeyCoins] [Fintype TS₁.Coins]
  [DecidableEq TS₁.Coins] [Nonempty TS₁.Coins]

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
of a compiled IOP over its own statements, for every base message, by zero knowledge and
simulation extraction** (`RingSignature.Insider.insiderForgeProb_le_zk` at `V.proofSystem`): for an
oracle-free base signer (`hB`) whose public values are `pubOf` of the coins (`hpub`), whose
refusals are `refuses` (`href`) and with correctness error `εc` (`hcorr`), an injective statement
map (`zkf.stmt_injective`) without honest statements of the empty ring (`zkf.not_mem_relH_nil`), an honest prover with
completeness error `errc` (`hE`; zero knowledge by `IOP.hvzk_of_errorBound` at the IOP's simulator)
and the soundness data `Sd` of `C`, the forgery probability is at most the extraction forger's
term, `zkError errc t Q`, the simulation-extraction error, spBCS's knowledge error at the largest
round error of `C`, and `2 Q εc`. -/
theorem insiderForgeProb_le_zk [Nonempty B₁.Msg] [Nonempty B₁.Pub] [Nonempty B₁.BSig]
    [hk : NeZero TD.k] {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (Sd : C.Sound)
    (hB : B₁.OracleFree) {refuses : KeyRing B₁.PK N → ℕ → B₁.Msg → B₁.Coins → Prop}
    {pubOf : B₁.Coins → B₁.Pub} (hpub : B₁.PubOfCoins pubOf) (href : B₁.RefusalOfCoins refuses)
    {εc : ℝ≥0∞} (hcorr : B₁.CorrectWithin εc) (zkf : V.ZKFacts)
    (T : (TD.setting kS hb).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (ofBase B₁ (V.proofSystem Hc hb hf) adm₁) n
      (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    insiderForgeProb A Q ≤
      zkForgerTerm (ert := zkf.emptyTest) A V.wit refuses pubOf (TD.setting kS hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) T C.extractor Q +
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
        2 * Q * εc :=
  RingSignature.Insider.insiderForgeProb_le_zk (ert := zkf.emptyTest) A hB hpub href hcorr (zkf.zkRingHyps)
    (TD.setting kS hb).viewEncoder id _ T
    (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE) Sd.causal_rbr Q


/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
of a compiled IOP over its own statements, by zero knowledge and simulation extraction, for a base
signer whose refusals are bounded per key** (`RingSignature.Insider.insiderForgeProb_le_zk_refuseAt`
at `V.proofSystem`): the bound of `insiderForgeProb_le_zk` at the empty refusal predicate, for a
per-key refusal rate at most `ρ` (`hρ`), at the cost `Q · ρ`. -/
theorem insiderForgeProb_le_zk_refuseAt [Nonempty B₁.Msg] [Nonempty B₁.Pub] [Nonempty B₁.BSig]
    [hk : NeZero TD.k] {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (Sd : C.Sound)
    (hB : B₁.OracleFree) {pubOf : B₁.Coins → B₁.Pub} (hpub : B₁.PubOfCoins pubOf) {ρ : ℝ≥0∞}
    (hρ : B₁.RefuseAtWithin adm₁ ρ)
    {εc : ℝ≥0∞} (hcorr : B₁.CorrectWithin εc) (zkf : V.ZKFacts)
    (T : (TD.setting kS hb).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (ofBase B₁ (V.proofSystem Hc hb hf) adm₁) n
      (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    insiderForgeProb A Q ≤
      zkForgerTerm (ert := zkf.emptyTest) A V.wit (fun _ _ _ _ => False) pubOf (TD.setting kS
          hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) T C.extractor Q +
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
        2 * Q * εc + Q * ρ :=
  RingSignature.Insider.insiderForgeProb_le_zk_refuseAt (ert := zkf.emptyTest) A hB hpub hρ hcorr (zkf.zkRingHyps)
    (TD.setting kS hb).viewEncoder id _ T
    (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE) Sd.causal_rbr Q

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
of a compiled IOP over its own statements, by zero knowledge and simulation extraction, for a base
signer whose refusal rate is bounded on average over the honest key coins**
(`RingSignature.Insider.insiderForgeProb_le_zk_refuseAvg` at `V.proofSystem`): the bound of
`insiderForgeProb_le_zk` at the empty refusal predicate, for a refusal rate averaged over the key
coins at most `ρ` (`hρ`), at the cost `Q · n · ρ`. -/
theorem insiderForgeProb_le_zk_refuseAvg [Nonempty B₁.Msg] [Nonempty B₁.Pub] [Nonempty B₁.BSig]
    [hk : NeZero TD.k] {errc : ℝ≥0} (hE : Hc.app.ErrorBound fun _ => errc) (Sd : C.Sound)
    (hB : B₁.OracleFree) {pubOf : B₁.Coins → B₁.Pub} (hpub : B₁.PubOfCoins pubOf) {ρ : ℝ≥0∞}
    (hρ : B₁.RefuseAvgWithin adm₁ ρ)
    {εc : ℝ≥0∞} (hcorr : B₁.CorrectWithin εc) (zkf : V.ZKFacts)
    (T : (TD.setting kS hb).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (ofBase B₁ (V.proofSystem Hc hb hf) adm₁) n
      (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    insiderForgeProb A Q ≤
      zkForgerTerm (ert := zkf.emptyTest) A V.wit (fun _ _ _ _ => False) pubOf (TD.setting kS
          hb).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator SD) T C.extractor Q +
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
        2 * Q * εc + Q * (n * ρ) :=
  RingSignature.Insider.insiderForgeProb_le_zk_refuseAvg (ert := zkf.emptyTest) A hB hpub hρ hcorr (zkf.zkRingHyps)
    (TD.setting kS hb).viewEncoder id _ T
    (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE) Sd.causal_rbr Q

end StmtVerifiesRing

end GordieHowe.Ring
