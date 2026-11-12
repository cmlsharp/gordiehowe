-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeChainAt
public import GordieHowe.Applications.Ring.KeyFreeRelay
public import GordieHowe.Applications.Ring.RingInsiderRelays
public import GordieHowe.Applications.Ring.RingForgerSplitChain
public import GordieHowe.Applications.Ring.MLDSAW1SplitRestrict
public import GordieHowe.Model.Quantum.Interactive.AbsorbAssignSwap
public import GordieHowe.Model.Quantum.Pure.MultiRelayOrigin
public import GordieHowe.Model.Quantum.Interactive.ThenProgOut

@[expose] public section

/-!
# The key-free chain on the full oracle

The full-oracle half of the key-free unforgeability route. The ring game against the outer
challenger `kfGame` of the key-free relay (`GordieHowe/Applications/Ring/KeyFreeRelay.lean`)
assigns at points of the base component of a split oracle `sp : OracleSplit Y Y₁ Y₂`
(`GordieHowe/Applications/Ring/MLDSAW1Split.lean`). Absorbing the relay into the adversary
(`QueryBoundedAdversary.assignLaw_le_absorbAssign`,
`GordieHowe/Model/Quantum/Interactive/AbsorbAssign.lean`) leaves the non-assigning main
challenger `kfMainFull`, and fixing the base component
(`QueryBoundedAdversary.transcriptLaw_restrictAt_base`) leaves `kfMain`
(`GordieHowe/Applications/Ring/KeyFreeMain.lean`) on the oracle `X → Y₂`, where the fixed-ω
chain (`GordieHowe/Applications/Ring/KeyFreeChainAt.lean`) applies.

The general tools live with their objects: `OracleProg.AllOut`
(`GordieHowe/Model/NARG/OracleProg.lean`), `MultiRelay.AsksIn.bind_allOut`, `translate_inl`,
`recMain`, `Challenger.KeepsView` (`GordieHowe/Model/Quantum/Interactive/AbsorbRelay.lean`),
`AdaptiveIAlg.toOuterMeasure_outLaw_comp` (`ThenProgOut.lean`),
`AdaptiveIAlg.toOuterMeasure_le_of_keepsView` (`AbsorbAssign.lean`),
`QueryBoundedAdversary.transcriptLaw_requests_congr`
(`GordieHowe/Model/RingSignature/Transcript.lean`) and `kfGame_keepsView` (`KeyFreeRelay.lean`).

- `kfMainFull`: `kfMain` on the full oracle with a prover `P₂` of the oracle `X → Y₂` reading the
  second components. `run_kfMainFull_congr`, `kfMainFull_respond_reprogram` (the hypothesis
  `hresp` of `kfRelay_safeAssign` at the view `prf sp`), `kfMainFull_noAssign`,
  `kfMainFull_readsLength`, `run_respond_restrictAt_kfMainFull`,
  `run_respond_restrictAt_kfMainFull_eq` (at a base part `ω`, the restricted challenger answers
  as `kfMain` on `X → Y₂`).
- `FromSigned`, `allOut_xP`, `fromSigned_reqOf`, `asksIn_kfProg`: every in-relation proof query
  the relay program of a request can make comes from a signing request with its ring and
  message.
- `freshXKF_of_canAsk`: the freshness `freshXKF` of the main requests, from the requests the relay
  programs can make and an outer history that signed no request on the claim's ring and message.
- `asksIn_kfProgK_reqOf`, `asksIn_kfProgK_corrupt`, `asksIn_kfProgK`, `asksIn_relayOf_kfRelay`,
  `asksIn_relayOf_kfRelay_corrupt`: the main requests of the relay programs over base reads.
- `freshXKF_of_canAsk`, `honestKF_of_canAsk`: for any relay whose programs ask only from signed
  requests and corrupt only on corruptions.
- `assignLaw_kfGame_le`, `tsum_assignLaw_kfGame_le`, `kfChainFull_le` (**the full-oracle half**):
  absorbing a relay agreeing with the key-free relay (`AssignRelay.AgreeAt`) at one oracle, then the oracle uniform split into a base component `ω` and
  a second component `h`, the restricted adversary against `kfMain` on `X → Y₂`.
-/

namespace GordieHowe

open Quantum Signature QROM OracleProg RingSignature.OracleSplit

namespace RingSignature.KeyFree

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type} [Fintype TS.PK] [DecidableEq TS.PK]
  [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins]
  (B : BaseSigner X Y N TS RMsg) {Stmt Wit Proof Coins R : Type}
  (rel : Stmt → Wit → Prop)
  [DecidableRel rel] [Fintype Coins] [DecidableEq Coins]
  (P₂ : NARG.Prover X Y₂ Stmt Wit Proof Coins) (μ : PMF Coins)
  (enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit)

/-- **The main challenger of the key-free route on the full oracle**: `kfMain` with the prover
`P₂` of the oracle `X → Y₂`, its coins drawn from `μ`, reading the second components `(sp y).2` of the answers. -/
noncomputable abbrev kfMainFull (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    Challenger X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof) :=
  kfMain B rel (P₂.mapQuery id fun y => (sp y).2) μ enc keys Q

omit [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- **The replies of `kfMainFull` read the oracle only through its second component.** -/
theorem run_kfMainFull_congr (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (c : (kfMainFull sp B rel P₂ μ enc keys Q).Coins)
    (hist : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)))
    (r : MURequest (SignOracle.none B.core) n ⊕ R) {H H' : X → Y} (hH : prf sp H = prf sp H') :
    ((kfMainFull sp B rel P₂ μ enc keys Q).respond c hist r).run H =
      ((kfMainFull sp B rel P₂ μ enc keys Q).respond c hist r).run H' := by
  rcases r with r | q
  · unfold kfMainFull kfMain Challenger.sumDummy
    dsimp only
    rw [run_mapOutput, run_mapOutput]
    unfold muNone
    dsimp only
    split_ifs <;> rfl
  · unfold kfMainFull kfMain Challenger.sumDummy
    dsimp only
    rw [run_mapOutput, run_mapOutput]
    unfold realChallenger
    dsimp only
    split_ifs
    · simp only [run_bind, run_pure, NARG.Prover.mapQuery, run_mapQuery]
      have : ((fun y => (sp y).2) ∘ H ∘ id) = ((fun y => (sp y).2) ∘ H' ∘ id) := hH
      rw [this]
    · rfl
    · rfl

omit [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- **Reprogramming that keeps the second component is not seen by `kfMainFull`** (the
hypothesis `hresp` of `kfRelay_safeAssign` at the view `prf sp`). -/
theorem kfMainFull_respond_reprogram [DecidableEq X] (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (c : (kfMainFull sp B rel P₂ μ enc keys Q).Coins)
    (hist : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)))
    (r : MURequest (SignOracle.none B.core) n ⊕ R) (H : X → Y) (L : List (Assignment X Y))
    (hL : prf sp (H.reprogram L) = prf sp H) :
    ((kfMainFull sp B rel P₂ μ enc keys Q).respond c hist r).run (H.reprogram L) =
      ((kfMainFull sp B rel P₂ μ enc keys Q).respond c hist r).run H :=
  run_kfMainFull_congr sp B rel P₂ μ enc keys Q c hist r hL

variable [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BMsg] [DecidableEq TS.BMsg]
  [Fintype TS.Pub] [DecidableEq TS.Pub] [Nonempty TS.KeyCoins] [Fintype TS.Coins]
  [DecidableEq TS.Coins] [Nonempty TS.Coins]

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BMsg] [DecidableEq TS.BMsg] [Fintype TS.Pub]
  [DecidableEq TS.Pub] [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins]
  [Nonempty TS.Coins] [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- **`kfMainFull` never reprograms.** -/
theorem kfMainFull_noAssign [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (kfMainFull sp B rel P₂ μ enc keys Q).NoAssign :=
  kfMain_noAssign B rel _ μ enc keys Q

omit [Fintype TS.PK] [DecidableEq TS.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BMsg]
  [DecidableEq TS.BMsg] [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.Pub]
  [DecidableEq TS.Pub] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins]
  [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins] in
/-- **`kfMainFull` reads its history only through its length** below the cap. -/
theorem kfMainFull_readsLength (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    ReadsLength (kfMainFull sp B rel P₂ μ enc keys Q) Q :=
  kfMain_readsLength B rel enc _ _ keys Q

omit [Fintype TS.PK] [DecidableEq TS.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BMsg]
  [DecidableEq TS.BMsg] [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.Pub]
  [DecidableEq TS.Pub] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins]
  [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins] in
/-- **The restricted `kfMainFull`**: at the base part `ω` and the second component `h`, its reply
is `kfMainFull`'s at every oracle `H` with second component `h`, with no assignments. -/
theorem run_respond_restrictAt_kfMainFull (keys : Fin n → B.KeyCoins) (Q : ℕ) (ω : X → Y₁)
    (c : (kfMainFull sp B rel P₂ μ enc keys Q).Coins)
    (hist : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)))
    (r : MURequest (SignOracle.none B.core) n ⊕ R) (h : X → Y₂) (H : X → Y) (hH : prf sp H = h) :
    (((kfMainFull sp B rel P₂ μ enc keys Q).restrictAt sp ω).respond c hist r).run h =
      ⟨(((kfMainFull sp B rel P₂ μ enc keys Q).respond c hist r).run H).response, []⟩ := by
  rw [Challenger.run_respond_restrictAt]
  change (⟨(((kfMainFull sp B rel P₂ μ enc keys Q).respond c hist r).run (join sp ω h)).response,
    []⟩ : Reply X Y₂ _) = _
  rw [run_kfMainFull_congr sp B rel P₂ μ enc keys Q c hist r (H' := H) (by rw [prf_join, hH])]



omit [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BMsg] [DecidableEq TS.BMsg] [Fintype TS.Pub]
  [DecidableEq TS.Pub] [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins]
  [Nonempty TS.Coins] [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- **The restricted `kfMainFull` answers as `kfMain` on the second component's oracle**: at the
base part `ω`, every reply runs as the reply of `kfMain` with the prover `P₂` of the oracle
`X → Y₂`. -/
theorem run_respond_restrictAt_kfMainFull_eq [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y₂] [DecidableEq Y₂] [Nonempty Y₂] (keys : Fin n → B.KeyCoins) (Q : ℕ) (ω : X → Y₁)
    (c : (kfMainFull sp B rel P₂ μ enc keys Q).Coins)
    (hist : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)))
    (r : MURequest (SignOracle.none B.core) n ⊕ R) (h : X → Y₂) :
    (((kfMainFull sp B rel P₂ μ enc keys Q).restrictAt sp ω).respond c hist r).run h =
      ((kfMain (X := X) (Y := Y₂) B rel P₂ μ enc keys Q).respond c hist r).run h := by
  rw [run_respond_restrictAt_kfMainFull sp B rel P₂ μ enc keys Q ω c hist r h (join sp ω h)
    (prf_join sp ω h)]
  have hna := kfMain_noAssign (X := X) (Y := Y₂) B rel P₂ μ enc keys Q c hist r h
  have e1 : (((kfMainFull sp B rel P₂ μ enc keys Q).respond c hist r).run (join sp ω h)).response =
      (((kfMain (X := X) (Y := Y₂) B rel P₂ μ enc keys Q).respond c hist r).run h).response := by
    rcases r with r | q
    · unfold kfMainFull kfMain Challenger.sumDummy
      dsimp only
      rw [run_mapOutput, run_mapOutput]
      unfold muNone
      dsimp only
      split_ifs <;> rfl
    · unfold kfMainFull kfMain Challenger.sumDummy
      dsimp only
      rw [run_mapOutput, run_mapOutput]
      unfold realChallenger
      dsimp only
      split_ifs
      · simp only [run_bind, run_pure, NARG.Prover.mapQuery, run_mapQuery]
        have : ((fun y => (sp y).2) ∘ join sp ω h ∘ id) = h := prf_join sp ω h
        rw [this]
      · rfl
      · rfl
  rw [e1, ← hna]

/-! ### The main requests of the key-free relay -/

section Asks

open RingSignature.Insider

-- The proof system's proof and coin types are parameters (`Pf`, `PC`), so that the responses are
-- `MUResponse B ⊕ Pf` and an spBCS proof system instantiates them as `M.Response b`, the spelling of
-- the extraction layers. Their instances are implicit, assigned by unification from the proof
-- system's types record and never synthesized again: the coins' decidable equality is classical
-- there, and a synthesized one would differ wherever `R` has decidable equality.
variable {X Y : Type} [DecidableEq X] [Zero Y] {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type}
  [DecidableEq TS.PK]
  (B : BaseSigner X Y N TS RMsg)
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {SC X₀ R : Type} (pks : Fin n → B.PK)
  (ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y))))
  (stmtP : RingStmt B → OracleProg X Y X₀) (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R)
  (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ} (sc : Fin Q → SC)
  {Stmt Wit : Type} (enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit)
  (rel : Stmt → Wit → Prop) (stmtX : Stmt → X₀) (fstX : X₀ → RingStmt B)

/-- **A main request comes from a signed request with its ring and message**: a proof query `q`
whose statement is not a dummy statement (`isDummy`), among the main requests of request `r`,
has a statement whose ring statement has the ring and the message of `r`, a signing request. It
reads only the statements of the main requests. -/
def FromSigned (isDummy : X₀ → Bool) (r : Req B PS adm n)
    (r' : MURequest (SignOracle.none B.core) n ⊕ R) : Prop :=
  ∀ q, r' = .inr q → isDummy (stmtX (enc (.inr q)).stmt) = false →
    ∃ s Rg msg, r = .sign s Rg msg ∧ (fstX (stmtX (enc (.inr q)).stmt)).ring = Rg ∧
      (fstX (stmtX (enc (.inr q)).stmt)).msg = msg

omit [DecidableEq X] [Zero Y]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The statement program's outputs on every path** read back the signed request's ring
statement and satisfy `Pt`, for a statement program whose outputs on every path read back its
input and satisfy `Pt` (`hfst`). -/
theorem allOut_xP {Pt : X₀ → Prop} (hfst : ∀ x, (stmtP x).AllOut fun x₀ => fstX x₀ = x ∧ Pt x₀)
    (r : Req B PS adm n) (o : Option (B.Pub × B.BSig × List (Assignment X Y))) :
    (xP B stmtP r o).AllOut fun x₀ => ∀ x, x₀ = some x →
      (∃ s Rg msg p, r = .sign s Rg msg ∧ o = some p ∧ fstX x = ⟨Rg, msg, p.1⟩) ∧ Pt x := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p
  · exact fun x h => by cases h
  · exact fun x h => by cases h
  · exact fun x h => by cases h
  · refine OracleProg.AllOut.mapOutput _ ?_
    refine OracleProg.AllOut.mono (hfst _) fun x₀ hx x h => ?_
    cases h
    exact ⟨⟨s, Rg, msg, p, rfl, rfl, hx.1⟩, hx.2⟩
  · exact fun x h => by cases h
  · exact fun x h => by cases h

omit [DecidableEq X] [Zero Y]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The main request of the relay program comes from a signed request** (`FromSigned`), for
dummy requests with dummy statements (`hdumS`), a statement program whose outputs on every path
read back its input and are carried by `toR` (`hx₀`). -/
theorem fromSigned_reqOf {isDummy : X₀ → Bool}
    (hdumS : ∀ r, isDummy (stmtX (enc (.inr (dummyR r))).stmt) = true)
    (c : ℕ) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) (x₀ : Option X₀)
    (hx₀ : ∀ x, x₀ = some x →
      (∃ s Rg msg p, r = .sign s Rg msg ∧ o = some p ∧ fstX x = ⟨Rg, msg, p.1⟩) ∧
        ∀ r' σ, stmtX (enc (.inr (toR x r' σ))).stmt = x) :
    FromSigned B enc stmtX fstX isDummy r (reqOf B toR dummyR c r o x₀) := by
  intro q hq hnd
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · simp [reqOf] at hq
  · rcases o with _ | p
    · simp only [reqOf, Sum.inr.injEq] at hq
      subst hq
      rw [hdumS] at hnd
      cases hnd
    · rcases x₀ with _ | x
      · simp only [reqOf, Sum.inr.injEq] at hq
        subst hq
        rw [hdumS] at hnd
        cases hnd
      · simp only [reqOf, Sum.inr.injEq] at hq
        subst hq
        obtain ⟨⟨s', Rg', msg', p', h1, h2, h3⟩, htoR⟩ := hx₀ x rfl
        cases h1
        refine ⟨s, Rg, msg, rfl, ?_⟩
        rw [htoR, h3]
        exact ⟨rfl, rfl⟩
  · rcases x₀ with _ | x
    · rcases o with _ | p <;>
      · simp only [reqOf, Sum.inr.injEq] at hq
        subst hq
        rw [hdumS] at hnd
        cases hnd
    · obtain ⟨⟨_, _, _, _, h1, -⟩, -⟩ := hx₀ x rfl
      cases h1

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **Every main request of the relay program comes from a signed request** (`FromSigned`). -/
theorem asksIn_kfProg {isDummy : X₀ → Bool}
    (hdumS : ∀ r, isDummy (stmtX (enc (.inr (dummyR r))).stmt) = true)
    (hfst : ∀ x, (stmtP x).AllOut fun x₀ => fstX x₀ = x)
    (htoR : ∀ x, (stmtP x).AllOut fun x₀ => ∀ r σ, stmtX (enc (.inr (toR x₀ r σ))).stmt = x₀)
    (c : ℕ)
    (r : Req B PS adm n) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (kfProg B pks ksign stmtP toR dummyR sc c r)
      (FromSigned B enc stmtX fstX isDummy r) := by
  unfold kfProg
  refine MultiRelay.AsksIn.bind (MultiRelay.AsksIn.translate_inl _ _ _) fun o => ?_
  refine MultiRelay.AsksIn.bind_allOut (MultiRelay.AsksIn.translate_inl _ _ _)
    ((allOut_xP B stmtP fstX (fun x => (hfst x).and (htoR x)) r o).translate _ _)
    fun x₀ hx₀ => ?_
  refine MultiRelay.AsksIn.bind ?_ fun _ => MultiRelay.AsksIn.pure _ _
  refine MultiRelay.AsksIn.query (fun r' h => ?_) fun _ => MultiRelay.AsksIn.pure _ _
  cases h
  exact fromSigned_reqOf B toR dummyR enc stmtX fstX hdumS c r o x₀ hx₀

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **A main corruption comes from a corruption**: the main request `inl (corrupt i)` of the
relay program of request `r` is made only for `r = corrupt i`. -/
theorem asksIn_kfProg_corrupt (c : ℕ) (r : Req B PS adm n) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (kfProg B pks ksign stmtP toR dummyR sc c r)
      fun r' => ∀ i, r' = .inl (.corrupt i) → r = .corrupt i := by
  unfold kfProg
  refine MultiRelay.AsksIn.bind (MultiRelay.AsksIn.translate_inl _ _ _) fun o => ?_
  refine MultiRelay.AsksIn.bind (MultiRelay.AsksIn.translate_inl _ _ _) fun x₀ => ?_
  refine MultiRelay.AsksIn.bind ?_ fun _ => MultiRelay.AsksIn.pure _ _
  refine MultiRelay.AsksIn.query (fun r' h i hi => ?_) fun _ => MultiRelay.AsksIn.pure _ _
  cases h
  rcases r with j | ⟨s, Rg, msg⟩ | ⟨j, bm⟩
  · simp only [reqOf, Sum.inl.injEq, MURequest.corrupt.injEq] at hi
    rw [hi]
  · rcases o with _ | p <;> rcases x₀ with _ | x <;> simp [reqOf] at hi
  · rcases o with _ | p <;> rcases x₀ with _ | x <;> simp [reqOf] at hi

section Over

variable {Yb Xs Ys : Type}
  (sgn : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg (X ⊕ X) (Y ⊕ Yb) (Option (B.Pub × B.BSig × List (Assignment X Y))))
  (stp : RingStmt B → OracleProg (X ⊕ X) (Y ⊕ Yb) X₀) (Rd : KFReads X Y Yb Xs Ys)

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **Every main request of the relay program over base reads comes from a signed request**
(`FromSigned`), for dummy requests with dummy statements (`hdumS`) and a statement program whose
outputs on every path read back its input and are carried by `toR` (`hfst`, `htoR`). -/
theorem asksIn_kfProgK {isDummy : X₀ → Bool}
    (hdumS : ∀ r, isDummy (stmtX (enc (.inr (dummyR r))).stmt) = true)
    (hfst : ∀ x, (stp x).AllOut fun x₀ => fstX x₀ = x)
    (htoR : ∀ x, (stp x).AllOut fun x₀ => ∀ r σ, stmtX (enc (.inr (toR x₀ r σ))).stmt = x₀)
    (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (kfProgK B pks toR dummyR sc sgn stp Rd T c r)
      (FromSigned B enc stmtX fstX isDummy r) := by
  unfold kfProgK
  refine MultiRelay.AsksIn.bind (asksIn_lift B _ _ _ _ _) fun o => ?_
  have hx : (xK B stp r o).AllOut fun x₀ => ∀ x, x₀ = some x →
      (∃ s Rg msg p, r = .sign s Rg msg ∧ o = some p ∧ fstX x = ⟨Rg, msg, p.1⟩) ∧
        ∀ r' σ, stmtX (enc (.inr (toR x r' σ))).stmt = x := by
    rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p
    · exact fun x h => by cases h
    · exact fun x h => by cases h
    · exact fun x h => by cases h
    · refine OracleProg.AllOut.mapOutput _ ?_
      refine OracleProg.AllOut.mono ((hfst _).and (htoR _)) fun x₀ hx x h => ?_
      cases h
      exact ⟨⟨s, Rg, msg, p, rfl, rfl, hx.1⟩, hx.2⟩
    · exact fun x h => by cases h
    · exact fun x h => by cases h
  refine MultiRelay.AsksIn.bind_allOut (asksIn_lift B _ _ _ _ _) (hx.translate _ _)
    fun x₀ hx₀ => ?_
  refine MultiRelay.AsksIn.bind ?_ fun _ => MultiRelay.AsksIn.pure _ _
  refine MultiRelay.AsksIn.query (fun r' h => ?_) fun _ => MultiRelay.AsksIn.pure _ _
  cases h
  exact fromSigned_reqOf B toR dummyR enc stmtX fstX hdumS c r o x₀ hx₀

end Over

end Asks


/-! ### Absorbing the key-free relay -/

section Absorb

open RingSignature.Insider

variable {X Y Y₁ Y₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X]
  [Nonempty Y] [Inhabited X] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : OracleSplit Y Y₁ Y₂) {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type} [Fintype TS.PK]
  [DecidableEq TS.PK]
  [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins]
  (B : BaseSigner X Y N TS RMsg)
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {SC X₀ R : Type} (pks : Fin n → B.PK)
  (ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y))))
  (stmtP : RingStmt B → OracleProg X Y X₀) (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R)
  (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ} (sc : Fin Q → SC) {qk qs : ℕ}
  (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk) (hs : ∀ x, (stmtP x).QueriesLE qs)
  (idle : MURequest (SignOracle.none B.core) n ⊕ R)
  {Stmt Wit : Type} (enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit)
  (rel : Stmt → Wit → Prop) (stmtX : Stmt → X₀) (fstX : X₀ → RingStmt B)
  [Fintype (Req B PS adm n)] [DecidableEq (Req B PS adm n)] [Fintype (Resp B PS adm)]
  [DecidableEq (Resp B PS adm)] [Inhabited (Req B PS adm n)] [Fintype R] [DecidableEq R]
  [Fintype (MUResponse B.core ⊕ Pf)] [DecidableEq (MUResponse B.core ⊕ Pf)]
  [Inhabited (MURequest (SignOracle.none B.core) n ⊕ R)] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys]
  [DecidableEq Ys]

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [Nonempty Y] [Inhabited X]
  [Fintype (Req B PS adm n)] [DecidableEq (Req B PS adm n)] [Fintype (Resp B PS adm)]
  [DecidableEq (Resp B PS adm)] [Inhabited (Req B PS adm n)] [Fintype R] [DecidableEq R]
  [Fintype (MUResponse B.core ⊕ Pf)] [DecidableEq (MUResponse B.core ⊕ Pf)]
  [Inhabited (MURequest (SignOracle.none B.core) n ⊕ R)] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype TS.PK] [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] in
omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The freshness of the main requests**: for a relay `G` whose programs make only main requests
that come from signed requests (`hA`, `FromSigned`), a main request of a history whose entries
are the padding request or requests the relay programs of tagged requests `hP` can make, a proof
query with a statement that is not a dummy statement, differs in its statement from `x₀` when no
request of `hP` signed `x₀`'s ring and message. The padding request has a dummy statement
(`hidleS`). -/
theorem freshXKF_of_canAsk {Frg : Type} {isDummy : X₀ → Bool}
    (G :
      AssignRelay X Y (Req B PS adm n) (Resp B PS adm) (MURequest (SignOracle.none B.core) n ⊕ R)
        (MUResponse B.core ⊕ Pf) Xs Ys)
    (hA : ∀ p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q,
      MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) ((G.relayOf Q).prog p)
        (FromSigned B enc stmtX fstX isDummy p.req))
    (hidleS : ∀ q, G.idle = .inr q → isDummy (stmtX (enc (.inr q)).stmt) = true)
    (hP : List (AssignRelay.TaggedReq X Y (Req B PS adm n) Q))
    (hist' : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf)))
    (hask : ∀ e' ∈ hist', e'.request = G.idle ∨ ∃ p ∈ hP, (G.relayOf Q).CanAsk p e'.request)
    (p : Frg × X₀)
    (hnot : ∀ s, UnforgeRequest.sign s (fstX p.2).ring (fstX p.2).msg ∉
      hP.map AssignRelay.TaggedReq.req) :
    freshXKF enc stmtX isDummy p (hist'.map HistoryEntry.request) := by
  intro q hq hnd he
  obtain ⟨e', he', hreq⟩ := List.mem_map.1 hq
  rcases hask e' he' with hi | ⟨p', hp', hc⟩
  · rw [hidleS q (hreq ▸ hi).symm] at hnd
    cases hnd
  · obtain ⟨s, Rg, msg, h1, h2, h3⟩ := MultiRelay.canAsk_of_asksIn _ (hA p') hc q hreq hnd
    rw [he] at h2 h3
    subst h2 h3
    exact hnot s (h1 ▸ List.mem_map_of_mem hp')

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [Nonempty Y] [Inhabited X]
  [Fintype (Req B PS adm n)] [DecidableEq (Req B PS adm n)] [Fintype (Resp B PS adm)]
  [DecidableEq (Resp B PS adm)] [Inhabited (Req B PS adm n)] [Fintype R] [DecidableEq R]
  [Fintype (MUResponse B.core ⊕ Pf)] [DecidableEq (MUResponse B.core ⊕ Pf)]
  [Inhabited (MURequest (SignOracle.none B.core) n ⊕ R)] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype TS.PK] [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] in
omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The honest ring of the main requests**: for a relay `G` whose programs make a main corruption
only for a corruption (`hA`), when every key of the claim's ring is the key `pkOf i` of a user `i`
with no corruption among the tagged requests `hP`, no main request of a history whose entries are
the padding request or requests the relay programs of `hP` can make corrupts `i` (`honestKF`),
for a padding request that is not a corruption (`hidleC`). -/
theorem honestKF_of_canAsk {Frg : Type} (pkOf : Fin n → B.PK)
    (G :
      AssignRelay X Y (Req B PS adm n) (Resp B PS adm) (MURequest (SignOracle.none B.core) n ⊕ R)
        (MUResponse B.core ⊕ Pf) Xs Ys)
    (hA : ∀ p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q,
      MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) ((G.relayOf Q).prog p)
        fun r' => ∀ i, r' = .inl (.corrupt i) → p.req = .corrupt i)
    (hidleC : ∀ i, G.idle ≠ .inl (.corrupt i))
    (hP : List (AssignRelay.TaggedReq X Y (Req B PS adm n) Q))
    (hist' : List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf)))
    (hask : ∀ e' ∈ hist', e'.request = G.idle ∨ ∃ p ∈ hP, (G.relayOf Q).CanAsk p e'.request)
    (p : Frg × X₀)
    (hon : ∀ pk ∈ (fstX p.2).ring.1, ∃ i, pkOf i = pk ∧
      UnforgeRequest.corrupt i ∉ hP.map AssignRelay.TaggedReq.req) :
    honestKF pkOf fstX p (hist'.map HistoryEntry.request) := by
  intro pk hpk
  obtain ⟨i, hi, hn⟩ := hon pk hpk
  refine ⟨i, hi, fun hm => ?_⟩
  obtain ⟨e', he', hreq⟩ := List.mem_map.1 hm
  rcases hask e' he' with h | ⟨p', hp', hc⟩
  · exact hidleC i (h.symm.trans hreq)
  · exact hn (MultiRelay.canAsk_of_asksIn _ (hA p') hc i hreq ▸ List.mem_map_of_mem hp')

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype TS.PK]
  [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- **Every main request of the key-free relay comes from a signed request** (`FromSigned`). -/
theorem asksIn_relayOf_kfRelay {isDummy : X₀ → Bool}
    (hdumS : ∀ r, isDummy (stmtX (enc (.inr (dummyR r))).stmt) = true)
    (hfst : ∀ x, (stmtP x).AllOut fun x₀ => fstX x₀ = x)
    (htoR : ∀ x, (stmtP x).AllOut fun x₀ => ∀ r σ, stmtX (enc (.inr (toR x₀ r σ))).stmt = x₀)
    (p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf)
      (((kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).relayOf Q).prog p)
      (FromSigned B enc stmtX fstX isDummy p.req) :=
  AssignRelay.asksIn_relayOf _ Q (P := fun _ r => FromSigned B enc stmtX fstX isDummy r)
    (fun T c r => asksIn_kfProgK B pks toR dummyR sc enc stmtX fstX _ _
    (KFReads.real id) hdumS (fun x => (hfst x).translate _ _) (fun x => (htoR x).translate _ _)
    T c r) p

omit [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype Pf] [DecidableEq Pf] [Fintype TS.PK]
  [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- **The key-free relay makes a main corruption only for a corruption.** -/
theorem asksIn_relayOf_kfRelay_corrupt (p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q) :
    MultiRelay.AsksIn (MUResponse B.core ⊕ Pf)
      (((kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).relayOf Q).prog p)
      fun r' => ∀ i, r' = .inl (.corrupt i) → p.req = .corrupt i :=
  AssignRelay.asksIn_relayOf _ Q (P := fun _ (r : Req B PS adm n)
      (r' : MURequest (SignOracle.none B.core) n ⊕ R) => ∀ i, r' = .inl (.corrupt i) → r = .corrupt i)
    (fun T c r => asksIn_kfProgK_corrupt B pks toR dummyR sc _ _ (KFReads.real id) T c r) p

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype TS.PK]
  [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- **Absorbing the key-free relay at one oracle through an agreeing relay**: against the outer
challenger `kfGame` of the key-free relay over a main challenger `C'`, an event `E` of the output
`p = (o, x₀)`, the answered requests and the final oracle in force has at most the probability
that the adversary with a relay `G₂` absorbed (`QueryBoundedAdversary.absorbAssign`, no side
coins), against `C'`, outputs `p` with `acc p (prf sp H)`, `chk p` and `kfFresh` of its main
requests at the base component `base sp H`: the freshness, the honest ring at the keys `pkOf`,
and the side condition `side`. `G₂` agrees with the key-free relay at `H` (`hag`,
`AssignRelay.AgreeAt`), makes at most `qG` oracle reads and `qP` pad sub-slots per request, and its
programs make only main requests from signed requests (`hA`) and main corruptions only for
corruptions (`hAc`). Hypotheses: `E` gives `acc` at the final oracle's second component, `chk`,
that no request signed `x₀`'s ring and message, the honest ring at the requests, and the outer
side condition `sideRing` at the final oracle (`hE`); `sideRing` at the oracle read through the
absorbed table, with the table and the main history explained by the tagged requests
(`AssignRelay.Explains` for `G₂`), gives `side` (`hside`); `C'` reads its history only through its
length below `Q` (`hC`), reprograms nothing (`hNA`), answers at least `Q` requests (`hQ`) and does
not see reprogramming that keeps the second component (`hresp`); the signer's assignments keep the
second component (`hpatch`); the main-request encoding is well formed (`hkf`, `KFEncoding`). The
side conditions are the caller's; they should read only statements, tags and the base component,
and nothing here enforces that. -/
theorem assignLaw_kfGame_le {t : ℕ} {Frg : Type} {isDummy : X₀ → Bool} (pkOf : Fin n → B.PK)
    (𝒜 : QueryBoundedAdversary X Y (Req B PS adm n) (Resp B PS adm) (Frg × X₀) t)
    (C' : Challenger X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf))
    (hC : ReadsLength C' Q) (hNA : C'.NoAssign) (hQ : Q ≤ C'.Q)
    (hresp : ∀ c' hist r' (H : X → Y) (L : List (Assignment X Y)),
      prf sp (H.reprogram L) = prf sp H →
        (C'.respond c' hist r').run (H.reprogram L) = (C'.respond c' hist r').run H)
    (hpatch : ∀ pk Rg c msg s H p, (ksign pk Rg c msg s).run H = some p →
      prf sp (H.reprogram p.2.2) = prf sp H)
    (hkf : KFEncoding enc stmtX isDummy idle dummyR toR stmtP fstX)
    (H : X → Y)
    (G₂ :
      AssignRelay X Y (Req B PS adm n) (Resp B PS adm) (MURequest (SignOracle.none B.core) n ⊕ R)
        (MUResponse B.core ⊕ Pf) Xs Ys) (qG qP : ℕ)
    (hG : G₂.qG ≤ qG) (hP : G₂.qP ≤ qP)
    (hag : (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).AgreeAt H G₂)
    (hA : ∀ p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q,
      MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) ((G₂.relayOf Q).prog p)
        (FromSigned B enc stmtX fstX isDummy p.req))
    (hAc : ∀ p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q,
      MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) ((G₂.relayOf Q).prog p)
        fun r' => ∀ i, r' = .inl (.corrupt i) → p.req = .corrupt i)
    (E : (Frg × X₀) × List (Req B PS adm n) × (X → Y) → Prop)
    (acc : Frg × X₀ → (X → Y₂) → Prop) (chk : Frg × X₀ → Prop)
    (sideRing : (X → Y) → (X → Y₁) → Frg × X₀ → List (Req B PS adm n) → Prop)
    (side : (X → Y₁) → Frg × X₀ → List (MURequest (SignOracle.none B.core) n ⊕ R) → Prop)
    (hE : ∀ p rs G, E (p, rs, G) → acc p (prf sp G) ∧ chk p ∧
      (∀ s, UnforgeRequest.sign s (fstX p.2).ring (fstX p.2).msg ∉ rs) ∧
      (∀ pk ∈ (fstX p.2).ring.1, ∃ i, pkOf i = pk ∧ UnforgeRequest.corrupt i ∉ rs) ∧
      sideRing G (base sp H) p rs)
    (hside : ∀ T hP hist' p,
      sideRing (reprogT T H) (base sp H) p (hP.map AssignRelay.TaggedReq.req) →
      G₂.Explains Q H T hP hist' → side (base sp H) p (hist'.map HistoryEntry.request)) :
    (𝒜.assignLaw (kfGame C' (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle) Q)
        H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbAssign (PMF.pure ()) (fun _ => G₂) qG (fun _ => hG) qP (fun _ => hP)
          Q).transcriptLaw C' H).toOuterMeasure
        {x | ∃ p ∈ x, acc p.1.1 (prf sp H) ∧ chk p.1.1 ∧
          kfFresh enc stmtX isDummy pkOf fstX side (base sp H) p.1.1
            (p.2.map HistoryEntry.request)} := by
  set Gr := kfRelay B pks ksign stmtP toR dummyR sc hk hs idle
  set hS := kfRelay_safeAssign B pks ksign stmtP toR dummyR sc hk hs idle C' (prf sp) hpatch hresp
  set E₀ : (Frg × X₀) × List (Req B PS adm n) × (X → Y) → Prop := fun q =>
    acc q.1 (prf sp H) ∧ chk q.1 ∧
      (∀ s, UnforgeRequest.sign s (fstX q.1.2).ring (fstX q.1.2).msg ∉ q.2.1) ∧
      (∀ pk ∈ (fstX q.1.2).ring.1, ∃ i, pkOf i = pk ∧ UnforgeRequest.corrupt i ∉ q.2.1) ∧
      sideRing q.2.2 (base sp H) q.1 q.2.1
  have h1 : (𝒜.assignLaw (kfGame C' Gr Q) H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      (𝒜.assignLaw (kfGame C' Gr Q) H).toOuterMeasure {x | ∃ p ∈ x, E₀ p} := by
    rw [QueryBoundedAdversary.assignLaw, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
    refine ((𝒜.alg a).toOuterMeasure_le_of_keepsView_and (kfGame C' Gr Q)
      (kfGame_keepsView hS (fun _ _ h => h) Q) H E).trans
      (MeasureTheory.measure_mono fun x hx => ?_)
    obtain ⟨q, hq, hG, h⟩ := hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hE q.1 q.2.1 q.2.2 h
    exact ⟨q, hq, hG ▸ h1, h2, h3, h4, h5⟩
  refine h1.trans ?_
  have hidle : G₂.idle = idle := hag.2.2.symm.trans (idle_kfRelay ..)
  refine 𝒜.assignLaw_le_absorbAssign_swap (PMF.pure ()) (fun _ => Gr) (fun _ => G₂) qG
    (fun _ => hG) qP (fun _ => hP) (Equiv.punitProd C'.Coins).symm
    (fun _ c' => by simp [kfGame]; rfl)
    (fun _ c' => kfGame_relaysChallenger
      (kfRelay_isPlain B pks ksign stmtP toR dummyR sc hk hs idle) hC c') (fun _ => hS) hNA hQ
    H (fun _ => hag) _ _ ?_
  rintro _ o T hP' hist' hE₀ hex
  obtain ⟨h1, h2, h3, h4, h5⟩ := hE₀
  exact ⟨h1, h2, freshXKF_of_canAsk B enc stmtX fstX G₂ hA (hidle ▸ hkf.hidleS) hP' hist' hex.1
    o h3, honestKF_of_canAsk B fstX pkOf G₂ hAc (hidle ▸ hkf.hidleC) hP' hist' hex.1 o h4,
    hside T hP' hist' o h5 hex⟩

variable [Fintype RMsg] [DecidableEq RMsg] [Fintype TS.BMsg] [DecidableEq TS.BMsg]
  [Fintype TS.Pub] [DecidableEq TS.Pub] [Nonempty TS.KeyCoins] [Fintype TS.Coins]
  [DecidableEq TS.Coins] [Nonempty TS.Coins]

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype RMsg]
  [DecidableEq RMsg] [Fintype TS.BMsg] [DecidableEq TS.BMsg] [Fintype TS.Pub] [DecidableEq TS.Pub]
  [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins]
  [Fintype TS.PK] [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] in
/-- **Absorbing the key-free relay through agreeing relays and fixing the base component** (the
full-oracle half of the key-free chain): with the oracle `H` uniform, the event `E H` against
`kfGame` over `kfMainFull` is at most the average, over a uniform base component `ω` and a uniform
second component `h`, of the probability that the adversary with the relay `G₂ ω` absorbed, at
`ω`, against `kfMainFull` at `ω`, outputs `p` with `acc p h`, `chk p` and `kfFresh` of its main
requests at `ω` (the honest ring at the users' keys `B.pk (keys i)`). The hypotheses are those of
`assignLaw_kfGame_le` at each `H`, with `G₂ (base sp H)`; `kfMainFull` satisfies the ones on the
main challenger. -/
theorem tsum_assignLaw_kfGame_le [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Fintype Y₂]
    [DecidableEq Y₂] [Nonempty Y₂] [DecidableRel rel] {Coins : Type} [Fintype Coins]
    [DecidableEq Coins] (P₂ : NARG.Prover X Y₂ Stmt Wit Pf Coins) (μ : PMF Coins)
    (keys : Fin n → B.KeyCoins) {t : ℕ} {Frg : Type} {isDummy : X₀ → Bool}
    (𝒜 : QueryBoundedAdversary X Y (Req B PS adm n) (Resp B PS adm) (Frg × X₀) t)
    (hpatch : ∀ pk Rg c msg s H p, (ksign pk Rg c msg s).run H = some p →
      prf sp (H.reprogram p.2.2) = prf sp H)
    (hkf : KFEncoding enc stmtX isDummy idle dummyR toR stmtP fstX)
    (G₂ : (X → Y₁) →
      AssignRelay X Y (Req B PS adm n) (Resp B PS adm) (MURequest (SignOracle.none B.core) n ⊕ R)
        (MUResponse B.core ⊕ Pf) Xs Ys) (qG qP : ℕ)
    (hG : ∀ ω, (G₂ ω).qG ≤ qG) (hP : ∀ ω, (G₂ ω).qP ≤ qP)
    (hag : ∀ H, (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).AgreeAt H (G₂ (base sp H)))
    (hA : ∀ ω (p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q),
      MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (((G₂ ω).relayOf Q).prog p)
        (FromSigned B enc stmtX fstX isDummy p.req))
    (hAc : ∀ ω (p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q),
      MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (((G₂ ω).relayOf Q).prog p)
        fun r' => ∀ i, r' = .inl (.corrupt i) → p.req = .corrupt i)
    (E : (X → Y) → (Frg × X₀) × List (Req B PS adm n) × (X → Y) → Prop)
    (acc : Frg × X₀ → (X → Y₂) → Prop) (chk : Frg × X₀ → Prop)
    (sideRing : (X → Y) → (X → Y₁) → Frg × X₀ → List (Req B PS adm n) → Prop)
    (side : (X → Y₁) → Frg × X₀ → List (MURequest (SignOracle.none B.core) n ⊕ R) → Prop)
    (hE : ∀ H p rs G, E H (p, rs, G) → acc p (prf sp G) ∧ chk p ∧
      (∀ s, UnforgeRequest.sign s (fstX p.2).ring (fstX p.2).msg ∉ rs) ∧
      (∀ pk ∈ (fstX p.2).ring.1, ∃ i, B.pk (keys i) = pk ∧ UnforgeRequest.corrupt i ∉ rs) ∧
      sideRing G (base sp H) p rs)
    (hside : ∀ H T hP hist' p,
      sideRing (reprogT T H) (base sp H) p (hP.map AssignRelay.TaggedReq.req) →
      (G₂ (base sp H)).Explains Q H T hP hist' →
      side (base sp H) p (hist'.map HistoryEntry.request)) :
    ∑' H, PMF.uniformOfFintype (X → Y) H *
        (𝒜.assignLaw (kfGame (kfMainFull sp B rel P₂ μ enc keys Q)
          (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle) Q) H).toOuterMeasure
          {x | ∃ p ∈ x, E H p} ≤
      ∑' ω, PMF.uniformOfFintype (X → Y₁) ω * ∑' h, PMF.uniformOfFintype (X → Y₂) h *
        (((𝒜.absorbAssign (PMF.pure ()) (fun _ => G₂ ω) qG (fun _ => hG ω) qP (fun _ => hP ω)
            Q).restrictAt sp ω).transcriptLaw
          ((kfMainFull sp B rel P₂ μ enc keys Q).restrictAt sp ω) h).toOuterMeasure
          {x | ∃ p ∈ x, acc p.1.1 h ∧ chk p.1.1 ∧
            kfFresh enc stmtX isDummy (fun i => B.pk (keys i)) fstX side ω p.1.1
              (p.2.map HistoryEntry.request)} := by
  refine (ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left
    (assignLaw_kfGame_le sp B pks ksign stmtP toR dummyR sc hk hs idle enc stmtX fstX
      (fun i => B.pk (keys i)) 𝒜
      (kfMainFull sp B rel P₂ μ enc keys Q) (kfMainFull_readsLength sp B rel P₂ μ enc keys Q)
      (kfMainFull_noAssign sp B rel P₂ μ enc keys Q) le_rfl
      (kfMainFull_respond_reprogram sp B rel P₂ μ enc keys Q) hpatch hkf H (G₂ (base sp H)) qG qP
      (hG _) (hP _) (hag H) (hA _) (hAc _)
      (E H) acc chk sideRing side (hE H) (hside H)) zero_le).trans (le_of_eq ?_)
  rw [tsum_uniform_split sp]
  refine tsum_congr fun ω => congrArg _ (tsum_congr fun h => congrArg _ ?_)
  have hres := Quantum.QueryBoundedAdversary.transcriptLaw_restrictAt_base sp
    (𝒜.absorbAssign (PMF.pure ()) (fun _ => G₂ ω) qG (fun _ => hG ω) qP (fun _ => hP ω) Q)
    (kfMainFull sp B rel P₂ μ enc keys Q) (kfMainFull_noAssign sp B rel P₂ μ enc keys Q)
    (join sp ω h)
  rw [base_join, prf_join] at hres
  simp only [base_join, prf_join]
  rw [← hres]

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype RMsg]
  [DecidableEq RMsg] [Fintype TS.BMsg] [DecidableEq TS.BMsg] [Fintype TS.Pub] [DecidableEq TS.Pub]
  [Nonempty TS.KeyCoins] [Fintype TS.Coins] [DecidableEq TS.Coins] [Nonempty TS.Coins]
  [Fintype TS.PK] [Fintype TS.BSig] [DecidableEq TS.BSig] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] in
/-- **The full-oracle half of the key-free chain**: with the oracle `H` uniform, an event `E H`
of the output `p = (o, x₀)`, the answered requests and the final oracle in force, for the
adversary `𝒜` against `kfGame` of the key-free relay over `kfMainFull`, is at most the average,
over a uniform base component `ω` and a uniform second component `h`, of the probability that the
adversary with the relay `G₂ ω` absorbed, at `ω` (`(𝒜.absorbAssign …).restrictAt sp ω`), against
`kfMain` on the oracle `X → Y₂` with the prover `P₂`, outputs `p` with `acc p h`, `chk p` and
`kfFresh` of its main requests at `ω`: the freshness, the honest ring at the users' keys and the
side condition `side`. `G₂ (base sp H)` agrees with the key-free relay at every `H` (`hag`). The
hypotheses are those of `tsum_assignLaw_kfGame_le`. -/
theorem kfChainFull_le [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Fintype Y₂]
    [DecidableEq Y₂] [Nonempty Y₂] [DecidableRel rel] {Coins : Type} [Fintype Coins]
    [DecidableEq Coins] (P₂ : NARG.Prover X Y₂ Stmt Wit Pf Coins) (μ : PMF Coins)
    (keys : Fin n → B.KeyCoins) {t : ℕ} {Frg : Type} {isDummy : X₀ → Bool}
    (𝒜 : QueryBoundedAdversary X Y (Req B PS adm n) (Resp B PS adm) (Frg × X₀) t)
    (hpatch : ∀ pk Rg c msg s H p, (ksign pk Rg c msg s).run H = some p →
      prf sp (H.reprogram p.2.2) = prf sp H)
    (hkf : KFEncoding enc stmtX isDummy idle dummyR toR stmtP fstX)
    (G₂ : (X → Y₁) →
      AssignRelay X Y (Req B PS adm n) (Resp B PS adm) (MURequest (SignOracle.none B.core) n ⊕ R)
        (MUResponse B.core ⊕ Pf) Xs Ys) (qG qP : ℕ)
    (hG : ∀ ω, (G₂ ω).qG ≤ qG) (hP : ∀ ω, (G₂ ω).qP ≤ qP)
    (hag : ∀ H, (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle).AgreeAt H (G₂ (base sp H)))
    (hA : ∀ ω (p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q),
      MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (((G₂ ω).relayOf Q).prog p)
        (FromSigned B enc stmtX fstX isDummy p.req))
    (hAc : ∀ ω (p : AssignRelay.TaggedReq X Y (Req B PS adm n) Q),
      MultiRelay.AsksIn (MUResponse B.core ⊕ Pf) (((G₂ ω).relayOf Q).prog p)
        fun r' => ∀ i, r' = .inl (.corrupt i) → p.req = .corrupt i)
    (E : (X → Y) → (Frg × X₀) × List (Req B PS adm n) × (X → Y) → Prop)
    (acc : Frg × X₀ → (X → Y₂) → Prop) (chk : Frg × X₀ → Prop)
    (sideRing : (X → Y) → (X → Y₁) → Frg × X₀ → List (Req B PS adm n) → Prop)
    (side : (X → Y₁) → Frg × X₀ → List (MURequest (SignOracle.none B.core) n ⊕ R) → Prop)
    (hE : ∀ H p rs G, E H (p, rs, G) → acc p (prf sp G) ∧ chk p ∧
      (∀ s, UnforgeRequest.sign s (fstX p.2).ring (fstX p.2).msg ∉ rs) ∧
      (∀ pk ∈ (fstX p.2).ring.1, ∃ i, B.pk (keys i) = pk ∧ UnforgeRequest.corrupt i ∉ rs) ∧
      sideRing G (base sp H) p rs)
    (hside : ∀ H T hP hist' p,
      sideRing (reprogT T H) (base sp H) p (hP.map AssignRelay.TaggedReq.req) →
      (G₂ (base sp H)).Explains Q H T hP hist' →
      side (base sp H) p (hist'.map HistoryEntry.request)) :
    ∑' H, PMF.uniformOfFintype (X → Y) H *
        (𝒜.assignLaw (kfGame (kfMainFull sp B rel P₂ μ enc keys Q)
          (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle) Q) H).toOuterMeasure
          {x | ∃ p ∈ x, E H p} ≤
      ∑' ω, PMF.uniformOfFintype (X → Y₁) ω * ∑' h, PMF.uniformOfFintype (X → Y₂) h *
        (((𝒜.absorbAssign (PMF.pure ()) (fun _ => G₂ ω) qG (fun _ => hG ω) qP (fun _ => hP ω)
            Q).restrictAt sp ω).transcriptLaw
          (kfMain (X := X) (Y := Y₂) B rel P₂ μ enc keys Q) h).toOuterMeasure
          {x | ∃ p ∈ x, acc p.1.1 h ∧ chk p.1.1 ∧
            kfFresh enc stmtX isDummy (fun i => B.pk (keys i)) fstX side ω p.1.1
              (p.2.map HistoryEntry.request)} := by
  refine (tsum_assignLaw_kfGame_le sp B pks ksign stmtP toR dummyR sc hk hs idle enc rel stmtX
    fstX P₂ μ keys 𝒜 hpatch hkf G₂ qG qP hG hP hag hA hAc E acc chk sideRing side hE hside).trans
    (le_of_eq ?_)
  refine tsum_congr fun ω => congrArg _ (tsum_congr fun h => congrArg _ ?_)
  exact Quantum.QueryBoundedAdversary.transcriptLaw_requests_congr (X := X) (Y := Y₂)
    (C := (kfMainFull sp B rel P₂ μ enc keys Q).restrictAt sp ω)
    (C' := kfMain (X := X) (Y := Y₂) B rel P₂ μ enc keys Q) id (PMF.map_id _) rfl
    (fun c hist r G => run_respond_restrictAt_kfMainFull_eq sp B rel P₂ μ enc keys Q ω c hist r G)
    ((𝒜.absorbAssign (PMF.pure ()) (fun _ => G₂ ω) qG (fun _ => hG ω) qP (fun _ => hP ω)
      Q).restrictAt sp ω) h
    fun p => acc p.1.1 h ∧ chk p.1.1 ∧
      kfFresh enc stmtX isDummy (fun i => B.pk (keys i)) fstX side ω p.1.1 p.2

end Absorb

end RingSignature.KeyFree

end GordieHowe
