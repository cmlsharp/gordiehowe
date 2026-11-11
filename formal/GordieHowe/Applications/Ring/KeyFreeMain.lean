-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.SumDummy
public import GordieHowe.Model.Signature.NMA
public import GordieHowe.Model.Signature.RejectionRelay
public import GordieHowe.Applications.Ring.RingStrongMain

@[expose] public section

/-!
# The main challenger of the key-free unforgeability route

The main challenger of the key-free route: the sum (`Quantum.Challenger.sumDummy`,
`GordieHowe/Model/Quantum/Interactive/SumDummy.lean`) of the multi-user challenger at the signing
oracle without messages (`Signature.SignOracle.none`, `GordieHowe/Model/Signature/NMA.lean`:
public keys and corruptions, no signing) and a challenger of proof queries, the real one
(`QROM.realChallenger`) or the simulated one (`QROM.simChallenger`). Every request, a multi-user
request or a proof query, is one entry of the proof part's history, so the proof part reads its
coins by the global request count; a multi-user request `r` stands for the dummy proof query
`enc (inl r)`. The route ends in MU-EUF-NMA^corr (the multi-user part makes no signatures); this
is not a strong-unforgeability game.

- `instInhabitedMURequestSum`: the requests are inhabited through the proof queries.
- `keyReplyNone keys`: the replies of the multi-user game without messages, the public key of
  user `i` and the key coins of a corrupted user. `muNone`: the multi-user challenger without
  messages, for a base signer of any oracle, as a challenger of the oracle `X → Y`.
  `respond_muChallenger_none`, `muNone_noAssign`: below the cap it answers by `keyReplyNone`,
  with no assignments, under every oracle.
- `QROM.realChallenger_respondsByRequests`, `QROM.simChallenger_respondsByRequests`: the proof
  challengers read their history only through its length.
- `kfMain`, `kfMainSim`: the main challengers, real and simulated. `kfMain_noAssign`.
- `kfMain_dummyHyps`, `kfMainSim_dummyHyps`: the hypotheses of the absorption of the multi-user
  part (`Quantum.DummyHyps`), for an injective `enc` and, for the simulated challenger, dummy
  proof queries outside the relation.
- `outLaw_kfMain`, `outLaw_kfMainSim`, `transcriptLaw_le_kfMain`, `transcriptLaw_le_kfMainSim`:
  L1 for the two main challengers, the multi-user requests absorbed through
  `SideRelay.dummyRelay (keyReplyNone keys) enc Q`.
- `kfTwo_atC`: L2, the multi-user requests as outer requests (`TwoRelay.dummyTwo`), at the outer
  replies `keyReplyNone keys`.
-/

namespace GordieHowe

open Quantum Signature QROM

/-! ### The proof challengers read their history through its length -/

namespace QROM

variable {X Y Stmt Wit Proof Coins SC : Type} (rel : Stmt → Wit → Prop) [DecidableRel rel]

/-- **The real challenger reads its history only through its length.** -/
theorem realChallenger_respondsByRequests [Fintype Coins] [DecidableEq Coins]
    (P : NARG.Prover X Y Stmt Wit Proof Coins) (μ : PMF Coins) (Q : ℕ) :
    (realChallenger rel P μ Q).RespondsByRequests := by
  intro c hist hist' req h
  have hl : hist.length = hist'.length := by simpa using congrArg List.length h
  simp only [realChallenger, hl]

/-- **The simulated challenger reads its history only through its length.** -/
theorem simChallenger_respondsByRequests [Fintype SC] [DecidableEq SC]
    (S : NARG.Simulator X Y Stmt Proof SC) (Q : ℕ) :
    (simChallenger rel S Q).RespondsByRequests := by
  intro c hist hist' req h
  have hl : hist.length = hist'.length := by simpa using congrArg List.length h
  simp only [simChallenger, hl]

end QROM

namespace RingSignature

variable {X Y Xb Yb : Type} {N n : ℕ} {TB : BaseTypes}
  (B : BaseSigner Xb Yb N TB)

/-- **The requests of the key-free route are inhabited through their second part** (the proof
queries, `Sum.inhabitedRight`), not through the multi-user requests: the one instance of
`Inhabited (MURequest (SignOracle.none B) n ⊕ R)`, so that the generic layers and the concrete
statements spell it as one term (with `instInhabitedOfMonad` at `Sum` the two spellings were
compared by unfolding). -/
instance (priority := high) instInhabitedMURequestSum {R : Type} [Inhabited R] :
    Inhabited (MURequest (SignOracle.none B.core) n ⊕ R) :=
  Sum.inhabitedRight


/-- **The replies of the multi-user game without messages** from the users' key coins `keys`:
the public key of user `i`, the key coins of a corrupted user. -/
def keyReplyNone (keys : Fin n → B.KeyCoins) :
    MURequest (SignOracle.none B.core) n → Option (MUResponse B.core)
  | .publicKey i => some (.publicKey (B.pk (keys i)))
  | .sign _ sm => sm.elim
  | .corrupt i => some (.keyCoins (keys i))

/-- **The multi-user challenger without messages on any oracle**: the requests and replies of the
multi-user game of `B` without messages (`Signature.SignOracle.none B`), `B` of any oracle, as a
challenger of the oracle `X → Y`. Its coins are those of `muChallenger (SignOracle.none B)`; below
the cap `Q` it answers by `keyReplyNone keys` (the public key of user `i`, the key coins of a
corrupted user), with no queries and no assignments. -/
noncomputable def muNone (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    Challenger X Y (MURequest (SignOracle.none B.core) n) (MUResponse B.core) where
  Coins := Fin Q → (SignOracle.none B.core).Coins
  coins := PMF.uniformOfFintype _
  Q := Q
  q := 0
  respond _ hist r :=
    if hist.length < Q then .pure ⟨keyReplyNone B keys r, []⟩ else .pure ⟨none, []⟩
  respond_queries _ hist r _ := by split_ifs <;> simp [OracleProg.trace]

/-- **Below the cap the multi-user challenger without messages answers by `keyReplyNone`**, with
no assignments, under every oracle. -/
theorem respond_muChallenger_none (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (c : (muNone (X := X) (Y := Y) B keys Q).Coins)
    (hist : List (HistoryEntry (MURequest (SignOracle.none B.core) n) (MUResponse B.core)))
    (r : MURequest (SignOracle.none B.core) n) (G : X → Y) (h : hist.length < Q) :
    ((muNone B keys Q).respond c hist r).run G = ⟨keyReplyNone B keys r, []⟩ := by
  simp only [muNone, h, ↓reduceIte]
  rfl

/-- **The multi-user challenger without messages reprograms nothing.** -/
theorem muNone_noAssign [DecidableEq X] (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (muNone (X := X) (Y := Y) B keys Q).NoAssign := by
  intro c hist r G
  simp only [muNone]
  split_ifs <;> rfl

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

variable {Stmt Wit Proof Coins SC R : Type} (rel : Stmt → Wit → Prop) [DecidableRel rel]
  [Fintype Coins] [DecidableEq Coins] [Fintype SC] [DecidableEq SC]
  (P : NARG.Prover X Y Stmt Wit Proof Coins) (μ : PMF Coins) (S : NARG.Simulator X Y Stmt Proof SC)
  (enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit)

/-- **The main challenger of the key-free route**: the multi-user challenger without messages at
the users' key coins `keys` (`muNone`, MU-EUF-NMA^corr: public keys and corruptions, for a base
signer `B` of any oracle) and the real
challenger of `Q` proof queries of `P`, its coins drawn from `μ`, a multi-user request `r` read by the proof part as the dummy
proof query `enc (inl r)` and a proof query `q` as `enc (inr q)` (`Challenger.sumDummy`). -/
noncomputable def kfMain (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    Challenger X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof) :=
  Challenger.sumDummy (muNone B keys Q) (realChallenger rel P μ Q) enc

/-- **The simulated main challenger of the key-free route**: `kfMain` with the simulated
challenger of `Q` proof queries in place of the real one. -/
noncomputable def kfMainSim (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    Challenger X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof) :=
  Challenger.sumDummy (muNone B keys Q) (simChallenger rel S Q) enc

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The main challenger of the key-free route never reprograms.** -/
theorem kfMain_noAssign [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
    [AddGroup Y] [Nonempty Y] (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (kfMain B rel P μ enc keys Q).NoAssign :=
  (muNone_noAssign B keys Q).sumDummy (realChallenger_noAssign rel P μ Q)

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The absorption hypotheses for the main challenger**, for an injective `enc`. -/
theorem kfMain_dummyHyps (henc : Function.Injective enc) (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    DummyHyps (muNone B keys Q) (realChallenger rel P μ Q) enc
      (keyReplyNone B keys) where
  enc_injective := henc
  respond₁ c hist r G h := respond_muChallenger_none B keys Q c hist r G h
  byRequests₂ := realChallenger_respondsByRequests rel P μ Q
  dummy_noAssign c hist _ G := realChallenger_noAssign rel P μ Q c hist _ G

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The absorption hypotheses for the simulated main challenger**, for an injective `enc`
whose dummy proof queries are outside the relation (`hd`), so that the simulator never runs on
them. -/
theorem kfMainSim_dummyHyps (henc : Function.Injective enc)
    (hd : ∀ r, ¬ rel (enc (.inl r)).stmt (enc (.inl r)).wit) (keys : Fin n → B.KeyCoins)
    (Q : ℕ) :
    DummyHyps (muNone B keys Q) (simChallenger rel S Q) enc
      (keyReplyNone B keys) where
  enc_injective := henc
  respond₁ c hist r G h := respond_muChallenger_none B keys Q c hist r G h
  byRequests₂ := simChallenger_respondsByRequests rel S Q
  dummy_noAssign c hist r G := by
    simp only [simChallenger]
    split_ifs with h₁ h₂
    · exact absurd h₂ (hd r)
    · rfl
    · rfl

/-! ### L1 and L2 for the main challengers -/

section Absorb

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [Fintype R] [DecidableEq R]
  [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit] [Fintype Proof]
  [DecidableEq Proof] [Inhabited (ProofQuery Stmt Wit)] [DecidableEq Xb] [DecidableEq Yb]
  {O : Type}

/-- **L1 for the main challenger**: on events that do not read the multi-user coins, the output
law of `A` against `kfMain` is that of `A` absorbed through
`dummyRelay (keyReplyNone keys) enc Q` against the real challenger. -/
theorem outLaw_kfMain (henc : Function.Injective enc) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)} (A : AdaptiveIAlg shA O)
    (H : X → Y)
    (Pr : DReg A.toKindAlg.W A.width X Y (MURequest (SignOracle.none B.core) n ⊕ R)
        (MUResponse B.core ⊕ Proof) → LogReg (MURequest (SignOracle.none B.core) n ⊕ R) A.slots →
      LogReg (ProofQuery Stmt Wit) A.slots → (realChallenger rel P μ Q).Coins → (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut (kfMain B rel P μ enc keys Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Pr v.adv v.chal.logs
          ((SideRelay.dummyRelay (Resp₂ := Proof) (keyReplyNone B keys) enc Q).logs v.chal.logs)
          v.chal.coins.2 (H.reprogram (A.toKindAlg.postAss _ v.chal))} =
      (((A.absorb (SideRelay.dummyRelay (keyReplyNone B keys) enc Q)).toKindAlg.composeBothOut
          (realChallenger rel P μ Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Pr (A.absorbedAdv (SideRelay.dummyRelay (keyReplyNone B keys) enc Q) v.adv)
          v.adv.1.1.1.logs v.chal.logs v.chal.coins
          (H.reprogram
            ((A.absorb (SideRelay.dummyRelay (keyReplyNone B keys) enc Q)).toKindAlg.postAss
              (realChallenger rel P μ Q) v.chal))} :=
  A.outLaw_sumDummy_of_main (kfMain_dummyHyps B rel P μ enc henc keys Q) H Pr

/-- **L1 for the simulated main challenger**: as `outLaw_kfMain`, against `kfMainSim` and the
simulated challenger, for dummy proof queries outside the relation (`hd`). -/
theorem outLaw_kfMainSim (henc : Function.Injective enc)
    (hd : ∀ r, ¬ rel (enc (.inl r)).stmt (enc (.inl r)).wit) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)} (A : AdaptiveIAlg shA O)
    (H : X → Y)
    (Pr : DReg A.toKindAlg.W A.width X Y (MURequest (SignOracle.none B.core) n ⊕ R)
        (MUResponse B.core ⊕ Proof) → LogReg (MURequest (SignOracle.none B.core) n ⊕ R) A.slots →
      LogReg (ProofQuery Stmt Wit) A.slots → (simChallenger rel S Q).Coins → (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut (kfMainSim B rel S enc keys Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Pr v.adv v.chal.logs
          ((SideRelay.dummyRelay (Resp₂ := Proof) (keyReplyNone B keys) enc Q).logs v.chal.logs)
          v.chal.coins.2 (H.reprogram (A.toKindAlg.postAss _ v.chal))} =
      (((A.absorb (SideRelay.dummyRelay (keyReplyNone B keys) enc Q)).toKindAlg.composeBothOut
          (simChallenger rel S Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Pr (A.absorbedAdv (SideRelay.dummyRelay (keyReplyNone B keys) enc Q) v.adv)
          v.adv.1.1.1.logs v.chal.logs v.chal.coins
          (H.reprogram
            ((A.absorb (SideRelay.dummyRelay (keyReplyNone B keys) enc Q)).toKindAlg.postAss
              (simChallenger rel S Q) v.chal))} :=
  A.outLaw_sumDummy_of_main (kfMainSim_dummyHyps B rel S enc henc hd keys Q) H Pr

/-- **L1 for transcripts against the main challenger** (`transcriptLaw_le_sumDummy`). -/
theorem transcriptLaw_le_kfMain {t : ℕ} (henc : Function.Injective enc)
    (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (𝒜 : QueryBoundedAdversary X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof) O t)
    (H : X → Y)
    (E : O × List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)) →
      Prop)
    (E' : O × List (HistoryEntry (ProofQuery Stmt Wit) Proof) → Prop)
    (himp : ∀ o hist (hist' : List (HistoryEntry (ProofQuery Stmt Wit) Proof)), E (o, hist) →
        hist'.map HistoryEntry.request = (hist.map HistoryEntry.request).map enc → E' (o, hist')) :
    (𝒜.transcriptLaw (kfMain B rel P μ enc keys Q) H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbSide (muNone (X := X) (Y := Y) B keys Q).coins
        (fun _ => SideRelay.dummyRelay (keyReplyNone B keys) enc Q)
        (fun _ _ => henc)).transcriptLaw (realChallenger rel P μ Q) H).toOuterMeasure
        {x | ∃ p ∈ x, E' p} :=
  𝒜.transcriptLaw_le_sumDummy (kfMain_dummyHyps B rel P μ enc henc keys Q) H E E' himp

/-- **L1 for transcripts against the simulated main challenger** (`transcriptLaw_le_sumDummy`),
for dummy proof queries outside the relation (`hd`). -/
theorem transcriptLaw_le_kfMainSim {t : ℕ} (henc : Function.Injective enc)
    (hd : ∀ r, ¬ rel (enc (.inl r)).stmt (enc (.inl r)).wit) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (𝒜 : QueryBoundedAdversary X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof) O t)
    (H : X → Y)
    (E : O × List (HistoryEntry (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)) →
      Prop)
    (E' : O × List (HistoryEntry (ProofQuery Stmt Wit) Proof) → Prop)
    (himp : ∀ o hist (hist' : List (HistoryEntry (ProofQuery Stmt Wit) Proof)), E (o, hist) →
        hist'.map HistoryEntry.request = (hist.map HistoryEntry.request).map enc → E' (o, hist')) :
    (𝒜.transcriptLaw (kfMainSim B rel S enc keys Q) H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbSide (muNone (X := X) (Y := Y) B keys Q).coins
        (fun _ => SideRelay.dummyRelay (keyReplyNone B keys) enc Q)
        (fun _ _ => henc)).transcriptLaw (simChallenger rel S Q) H).toOuterMeasure
        {x | ∃ p ∈ x, E' p} :=
  𝒜.transcriptLaw_le_sumDummy (kfMainSim_dummyHyps B rel S enc henc hd keys Q) H E E' himp

end Absorb

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **L2 for the main challengers**: the relay with the multi-user requests as outer requests
(`TwoRelay.dummyTwo`), at the outer replies `keyReplyNone keys`, is
`dummyRelay (keyReplyNone keys) enc Q`. -/
theorem kfTwo_atC (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (TwoRelay.dummyTwo (Resp₂ := Proof) enc Q).atC (fun _ q => keyReplyNone B keys q) =
      SideRelay.dummyRelay (keyReplyNone B keys) enc Q :=
  TwoRelay.dummyTwo_atC _ enc Q

end RingSignature

end GordieHowe
