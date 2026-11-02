-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeChainFull
public import GordieHowe.Applications.Ring.SPBCSSplit

@[expose] public section

/-!
# The key-free chain

The key-free unforgeability route composed: the full-oracle half
(`kfChainFull_le`, `GordieHowe/Applications/Ring/KeyFreeChainFull.lean`: the key-free relay
absorbed into the adversary, the oracle split into a base component `ω` and a second component)
followed, at each `ω`, by the chain against `kfMain` on the second component (`kfChainAt_le`,
`GordieHowe/Applications/Ring/KeyFreeChainAt.lean`: zero knowledge, then simulation extraction),
for the spBCS proof system on the second component (`Ring.spbcsSplitProofSystem`,
`GordieHowe/Applications/Ring/SPBCSSplit.lean`).

The test of a key-free win at the final oracle replaces the transcript event through
`QueryBoundedAdversary.transcriptLaw_eq_tsum_test`
(`GordieHowe/Model/RingSignature/Transcript.lean`),
for the absorbed adversary with its table dropped (`QueryBoundedAdversary.mapOut`).

- `kfChain_le` (**the key-free chain**): the key-free ring game at fixed keys and side coins is
  at most the average over `ω` of the forger's win in the extraction run of the adversary with a
  relay `G₂ ω` absorbed that agrees with the key-free relay, plus `simExtractionError` and
  `zkError`, with a caller's side condition on the main requests at `ω` transported from one on
  the outer requests at the final oracle (`fun _ _ _ => True` for none).
-/

open scoped ENNReal

namespace GordieHowe

open Quantum Signature QROM OracleProg RingSignature.OracleSplit

/-! ### The chain -/

namespace RingSignature.KeyFree

open GordieHowe.SPBCS IOP SPTerm RingSignature.Insider

section Chain

variable {k kN kS L e N n t : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes} {B : BaseSigner (Bits (queryBits k kN kS L)) Y N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {R : Type} [Fintype R] [Nonempty R] {honest : Wit₀ → R → CausalProver P τ X₀}
  {Stmt Wit Rq Frg : Type} {rel : Stmt → Wit → Prop}
  {enc : MURequest (SignOracle.none B) n ⊕ Rq → ProofQuery Stmt Wit} {stmtX : Stmt → X₀}
  [DecidableEq X₀] [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt] [Fintype Wit]
  [DecidableEq Wit] [Inhabited (ProofQuery Stmt Wit)] [Fintype Rq] [DecidableEq Rq] [Inhabited Rq]
  [DecidableRel rel] [Inhabited M.NIProof] {dummyS : Stmt} {isDummy : X₀ → Bool}

open Classical in
/-- **The key-free chain** at fixed users' key coins `keys` and side coins
`sc`. For the spBCS proof system on the second component (`spbcsSplitProofSystem`) and an
adversary `𝒜` of the key-free ring game (`kfGame` of the key-free relay over `kfMainFull` with the
compiled spBCS prover), an event `Ev H` of the output `p = (o, x₀)`, the answered requests and the
final oracle in force has, with the oracle `H` uniform, at most the average over a uniform base
component `ω` of the forger's win (`forgerWinsKF` at the goal `Goal ω`) in the extraction run of
`seAlgKF` for the absorbed adversary at `ω` with its table dropped, plus `simExtractionError` and
`zkError`, at `t + Q · qG + Q · qP` queries. The absorbed relay `G₂ ω` is any relay agreeing with
the key-free relay at every oracle of base component `ω` (`hag`, `AssignRelay.AgreeAt`), with at
most `qG` oracle reads and `qP` pad sub-slots per request, whose programs make only main requests
from signed requests (`hA`) and main corruptions only for corruptions (`hAc`); the key-free relay
itself is one (`AssignRelay.AgreeAt.refl`).

Hypotheses on the relay (`kfChainFull_le`): `Ev H` gives the check `checkX`, the claim of `x₀`
with the proof of `o` accepted against the final oracle's second component, that no request
signed `x₀`'s ring and message, and the honest ring (`hE`), and the outer side condition
`sideRing` at the final oracle and `base sp H` (`hEside`); `sideRing` at the oracle read through
the absorbed table, with the table and the main history explained by the tagged requests
(`AssignRelay.Explains` for `G₂`), gives the side condition `side` of the main requests
(`hside`); the signer's
assignments keep the second component (`hpatch`); the main-request encoding is well formed
(`hkf`, `KFEncoding`).
Hypotheses at a fixed base component (`kfChainAt_le`): `rel` is `relH` read through `stmtX` and
`fw` (`hrel`); `enc` is injective (`henc`); the dummy statements satisfy `DummyStmts` (`hd`) and
differ from every checked statement (`hdisj`); the composite is honest-verifier zero knowledge
(`hvzk`) and round-by-round knowledge sound (`hrbr`); digests have at least one byte (`hk`); a
witness at a checked output with `kfFresh` at `ω` (the freshness, the honest ring and `side`)
gives the goal (`hgoal`). The side conditions are the caller's; they should read only statements,
tags and the base component, and nothing here enforces that. -/
theorem kfChain_le (hk : 0 < k) (hb : M.FormatBounds Qs b b)
    (stmtProg : RingStmt B → OracleProg (Bits (queryBits k kN kS L)) Y₁ X₀) (qS : ℕ)
    (hS : ∀ x, (stmtProg x).QueriesLE qS) (check : RingStmt B → Bool)
    (input : RingStmt B → RingWit B → Option Wit₀) {adm : KeyRing B.PK N → Prop}
    [DecidablePred adm]
    [Fintype
      (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n)]
    [DecidableEq
      (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n)]
    [Fintype
      (Resp B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)]
    [DecidableEq
      (Resp B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)]
    [Inhabited
      (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n)]
    [Inhabited (MURequest (SignOracle.none B) n ⊕ Rq)]
    {SC : Type} (pks : Fin n → B.PK)
    (ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
      OracleProg (Bits (queryBits k kN kS L)) Y
        (Option (B.Pub × B.BSig × List (Assignment (Bits (queryBits k kN kS L)) Y))))
    (stmtP : RingStmt B → OracleProg (Bits (queryBits k kN kS L)) Y X₀)
    (toR : X₀ →
      Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n × ℕ →
      B.BSig → Rq)
    (dummyR :
      Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n × ℕ →
      Rq)
    {Q : ℕ} (sc : Fin Q → SC) {qk qs : ℕ} (keys : Fin n → B.KeyCoins)
    (hks : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk)
    (hst : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none B) n ⊕ Rq)
    (fstX : X₀ → RingStmt B)
    {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G₂ : (Bits (queryBits k kN kS L) → Y₁) →
      AssignRelay (Bits (queryBits k kN kS L)) Y
        (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n)
        (Resp B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)
        (MURequest (SignOracle.none B) n ⊕ Rq)
        (MUResponse B ⊕ M.Response b) Xs Ys)
    (qG qP : ℕ) (hG : ∀ ω, (G₂ ω).qG ≤ qG) (hP : ∀ ω, (G₂ ω).qP ≤ qP)
    (hag : ∀ H, (kfRelay B pks ksign stmtP toR dummyR sc hks hst idle).AgreeAt H
      (G₂ (base sp H)))
    (hA : ∀ ω (p : AssignRelay.TaggedReq (Bits (queryBits k kN kS L)) Y
        (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n) Q),
      MultiRelay.AsksIn (MUResponse B ⊕ M.Response b) (((G₂ ω).relayOf Q).prog p)
        (FromSigned B enc stmtX fstX isDummy p.req))
    (hAc : ∀ ω (p : AssignRelay.TaggedReq (Bits (queryBits k kN kS L)) Y
        (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n) Q),
      MultiRelay.AsksIn (MUResponse B ⊕ M.Response b) (((G₂ ω).relayOf Q).prog p)
        fun r' => ∀ i, r' = .inl (.corrupt i) → p.req = .corrupt i)
    {fw : Wit → Wit₀} {relH : Set (X₀ × Wit₀)}
    (hrel : ∀ x w, rel x w ↔ (stmtX x, fw w) ∈ relH) (henc : Function.Injective enc)
    (prfOf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool)
    (hd : DummyStmts B rel enc dummyS stmtX isDummy)
    (hdisj : ∀ x, isDummy x = true → ∀ p : Frg × X₀, checkX p.2 p.1 = true → x ≠ p.2)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub) (Sim : CausalJointSimulator VE.MV Pub)
    (T : M.Preimages) {δ : NNReal} (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {WitK W : Type} {relK : Set (X₀ × WitK)} {Ext : CausalExtractor P τ X₀ WitK}
    {St : CausalStateFn P τ X₀} {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound relK Vr Ext St ε) (wit : X₀ → WitK → W)
    (side : (Bits (queryBits k kN kS L) → Y₁) → Frg × X₀ →
      List (MURequest (SignOracle.none B) n ⊕ Rq) → Prop)
    (Goal : (Bits (queryBits k kN kS L) → Y₁) → Frg × X₀ →
      List (MURequest (SignOracle.none B) n ⊕ Rq) → W → Prop)
    (hgoal : ∀ ω p rs w, checkX p.2 p.1 = true →
      kfFresh enc stmtX isDummy (fun i => B.pk (keys i)) fstX side ω p rs → (p.2, w) ∈ relK →
      Goal ω p rs (wit p.2 w))
    (p₀ : M.Response b)
    (𝒜 : QueryBoundedAdversary (Bits (queryBits k kN kS L)) Y
      (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n)
      (Resp B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm)
      (Frg × X₀) t)
    (hpatch : ∀ pk Rg c msg s H p, (ksign pk Rg c msg s).run H = some p →
      prf sp (H.reprogram p.2.2) = prf sp H)
    (hkf : KFEncoding enc stmtX isDummy idle dummyR toR stmtP fstX)
    (Ev : (Bits (queryBits k kN kS L) → Y) → (Frg × X₀) ×
      List
        (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n) ×
        (Bits (queryBits k kN kS L) → Y) → Prop)
    (sideRing : (Bits (queryBits k kN kS L) → Y) → (Bits (queryBits k kN kS L) → Y₁) →
      Frg × X₀ →
      List
        (Req B (Ring.spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) adm n) →
      Prop)
    (hE : ∀ H p rs G, Ev H (p, rs, G) →
      (∃ π ∈ prfOf p.1, (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ prf sp G) ⟨p.2, π⟩) ∧
        checkX p.2 p.1 = true ∧ (∀ s, UnforgeRequest.sign s (fstX p.2).ring (fstX p.2).msg ∉ rs) ∧
        (∀ pk ∈ (fstX p.2).ring.1, ∃ i, B.pk (keys i) = pk ∧ UnforgeRequest.corrupt i ∉ rs))
    (hEside : ∀ H p rs G, Ev H (p, rs, G) → sideRing G (base sp H) p rs)
    (hside : ∀ H T hP hist' p,
      sideRing (reprogT T H) (base sp H) p (hP.map AssignRelay.TaggedReq.req) →
      (G₂ (base sp H)).Explains Q H T hP hist' →
      side (base sp H) p (hist'.map HistoryEntry.request)) :
    ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → Y) H *
        (𝒜.assignLaw (kfGame (kfMainFull sp B rel ((encProver M Λ E hb honest).comap stmtX fw)
          enc keys Q) (kfRelay B pks ksign stmtP toR dummyR sc hks hst idle) Q) H).toOuterMeasure
          {x | ∃ p ∈ x, Ev H p} ≤
      ∑' ω, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → Y₁) ω *
        (∑' a, (((𝒜.absorbAssign (PMF.pure ())
            (fun _ => G₂ ω) qG (fun _ => hG ω) qP (fun _ => hP ω) Q).restrictAt sp ω).mapOut
              Prod.fst).aux a *
          simProb (outEquiv k e)
            (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prfOf keys Q
              ((((𝒜.absorbAssign (PMF.pure ())
            (fun _ => G₂ ω) qG (fun _ => hG ω) qP (fun _ => hP ω) Q).restrictAt sp ω).mapOut
              Prod.fst).alg a))
              ((inertOnDummy isDummy (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T)
                p₀).comap (stmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
            (forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prfOf keys Q
              ((((𝒜.absorbAssign (PMF.pure ())
            (fun _ => G₂ ω) qG (fun _ => hG ω) qP (fun _ => hP ω) Q).restrictAt sp ω).mapOut
              Prod.fst).alg a)
              ((inertOnDummy isDummy (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T)
                p₀).comap (stmtX ∘ Prod.fst)) Ext wit (Goal ω)) +
          M.simExtractionError (kqOf Mg nr b b) (maxError ε)
            (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q (t + Q * qG + Q * qP) Q +
          ENNReal.ofReal (M.zkError δ (t + Q * qG + Q * qP) Q)) := by
  refine (kfChainFull_le sp B pks ksign stmtP toR dummyR sc hks hst idle enc rel stmtX fstX
    ((encProver M Λ E hb honest).comap stmtX fw) keys 𝒜 hpatch hkf G₂ qG qP hG hP hag hA hAc Ev
    (fun p h => ∃ π ∈ prfOf p.1, (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ h) ⟨p.2, π⟩)
    (fun p => checkX p.2 p.1 = true) sideRing side
    (fun H p rs G h => ⟨(hE H p rs G h).1, (hE H p rs G h).2.1, (hE H p rs G h).2.2.1,
      (hE H p rs G h).2.2.2, hEside H p rs G h⟩) hside).trans ?_
  refine ENNReal.tsum_le_tsum fun ω => mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_
    (kfChainAt_le _ hk hb hrel henc prfOf checkX hd hdisj (fun i => B.pk (keys i)) fstX side ω VE
      pub Sim T hvzk hrbr wit Goal (hgoal ω) p₀ keys Q)) zero_le
  unfold acceptK acceptKAt
  have hbr := fun h => Quantum.QueryBoundedAdversary.transcriptLaw_eq_tsum_test
    (QueryBoundedAdversary.restrictAt sp ω (𝒜.absorbAssign (PMF.pure ())
      (fun _ => G₂ ω) qG (fun _ => hG ω) qP (fun _ => hP ω) Q))
    (C := kfMain B rel ((encProver M Λ E hb honest).comap stmtX fw) enc keys Q)
    (kfMain_noAssign B rel _ enc keys Q) h
    (fun o rs => (∃ π ∈ prfOf o.1, (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ h) ⟨o.2, π⟩) ∧
      checkX o.2 o.1 = true ∧ kfFresh enc stmtX isDummy (fun i => B.pk (keys i)) fstX side ω o rs)
    (kfWinTest M b Qs enc stmtX isDummy (fun i => B.pk (keys i)) fstX side prfOf checkX Q ω)
    fun o rs => by
      rw [run_kfWinTest]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩⟩
  -- TODO(unbundle-M4): at default transparency the match of `hbr`'s side against the goal
  -- unfolds `QueryBoundedAdversary.sh` through `absorbAssign`/`restrictAt` (224k unfolds); the
  -- two sides agree up to reducible unfolding.
  with_reducible refine (tsum_congr fun h => congrArg (PMF.uniformOfFintype _ h * ·) (hbr h)).trans ?_
  rw [GordieHowe.tsum_mul_tsum_mul_comm]

end Chain

end RingSignature.KeyFree

end GordieHowe
