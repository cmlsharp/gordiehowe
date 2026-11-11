-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.InsiderRelays
public import GordieHowe.Model.RingSignature.Unforgeability
public import GordieHowe.Model.Signature.Properties
public import GordieHowe.Model.RingSignature.BaseCompleteness
public import GordieHowe.Foundations.ToMathlib.PMFFiber
public import GordieHowe.Model.Quantum.Interactive.ReqBridge
public import GordieHowe.Model.RingSignature.Transcript
public import GordieHowe.Model.Signature.MultiUser

@[expose] public section

/-!
# The requests of the insider unforgeability game of `ofBase` and their relays

The insider unforgeability game of `GordieHowe/Model/RingSignature/Unforgeability.lean` (BKM06
Definition 7) for `ofBase B PS adm`, at fixed users' key coins, as split challengers, and the relays
of its requests to the challengers of zero knowledge and simulation extraction
(`GordieHowe/Model/Quantum/Interactive/ZeroKnowledge.lean`, `SimChallenger.lean`), for the
zero-knowledge route of `GordieHowe/Applications/Ring/RingInsider.lean`. This mirrors
`GordieHowe/Applications/Ring/InsiderRelays.lean` for the earlier interface.

- `Quantum.Challenger.oracleIn_toPureEnv_congr`, `answer_toPureEnv_congr`, `oracle_toPureEnv_congr`,
  `Quantum.KindAlg.toOuterMeasure_outLaw_congr`: challengers whose replies agree along an
  equivalence of their coins give the composition the same law on events of the adversary's
  registers, the logs and the coins.
- `RingSignature.RingStmt.equivProd` and the finite type of ring statements.
- `RingScheme.unforgeReply`, `respond_unforgeChallenger`, `RingScheme.gameSplit`,
  `toOuterMeasure_outLaw_unforge_eq_split`: the game's challenger at fixed keys is a split
  challenger. `sign_ofBase_of_not_supported`.
- `Insider.Req`, `Resp`, `RelayStmt` (a ring statement with the request), `RelayWit` (a position
  below `N + 1` and a base signature), `dummyStmt` (the empty ring).
- `signerIn`: a ring-signing request by a member of a supported ring that signs (no refusal at the
  coins); `stmtAt`: its statement `(R, m, pubOf c)`; `bsigOf`, `witAt`: the base signature and
  witness at the coins; `drawOk`: the base signature verifies; `zkStmt`: the statement of a proof
  query, `dummyStmt` unless the base signature verifies; `sideAnswer`: the reply from the main
  reply.
- `seRelay` (statements, reading public keys, corrupted users' key coins and coins only) and
  `zkRelay enc` (proof queries with encoded witnesses), injective per request number.
- `drawOkR`, `drawOk_of_drawOkR`: the draw's base signature exists and verifies.
- `mem_ringRel_of`, `mem_relZ_iff`: the relayed query of a member's request that signs, with a base
  signature that exists and verifies, is in the ring relation; the relayed queries are in a relation
  `relH` of program statements and encoded witnesses exactly for those requests.
  `run_unforgeReply_sign`: the game's reply to a ring-signing request.
- `checkedReply`, `checkedSplit`: the game refusing a base signature that fails to verify;
  `simReply`, `simSplit`: the simulated challengers; `inertOnEmpty`: a simulator answering `p₀` on
  the empty ring.
- `relays_real`, `relays_sim_zk`, `relays_sim_se`: the checked game relays the real
  zero-knowledge challenger, the checked simulated game the simulated zero-knowledge challenger,
  the simulated game the simulation-extraction challenger.
- `coinSplit`, `coins_checkedSplit`, `coins_simSplit`: the coins as side coins and main coins;
  `toOuterMeasure_not_drawOk_le`, `game_le_checked`, `simChecked_le`: each checked hybrid costs
  `Q · εc`.
- `Quantum.SplitChallenger.map_coinLaw`: split challengers related by a map of their draws
  (with `Quantum.KindAlg.toOuterMeasure_outLaw_map`,
  `GordieHowe/Model/RingSignature/Transcript.lean`,
  challengers related by a map of their coins give the same law).
- `refuseSplit`, `not_signerIn_and_drawOk`, `run_checkedReply_of_not`, `simReply_of_not`,
  `checked_eq_refuse`, `simChecked_eq_refuse`: without a ring witness, the checked game and the
  checked simulated game are both the refusing game.

## Deliberate differences from `InsiderRelays.lean`

1. The base signer is ring-aware and may refuse; a refused request is answered by `⊥` and relayed
   as a request without a witness. The simulated games decide refusals by `refuses`, a function
   of the ring, the position, the message and the coins (`BaseSigner.RefusalOfCoins`).
2. The base signer, its public values and its verification read no oracle
   (`BaseSigner.OracleFree`); base signatures are read at the zero oracle.
3. The adversary's start input is the users' public keys; the keys are fixed outside the
   challengers, which draw only signing and prover or simulator coins.
-/

namespace GordieHowe

open Quantum
open scoped ENNReal

namespace Quantum.Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **Challengers with the same replies along an equivalence of their coins have the same
states**: after every request list, at the coins `c` and `e c`. -/
theorem oracleIn_toPureEnv_congr {C C' : Challenger X Y Req Resp} (e : C.Coins ≃ C'.Coins)
    (hQ : C.Q = C'.Q) (hresp : ∀ c, C.respond c = C'.respond (e c)) (H : X → Y) (c : C.Coins) :
    ∀ rs : List Req, C.toPureEnv.oracleIn (H, c) rs = C'.toPureEnv.oracleIn (H, e c) rs := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [Env.oracleIn_append_singleton, Env.oracleIn_append_singleton, ih]
    simp only [Env.update, hQ]
    split_ifs
    · simp only [toPureEnv, hresp]
    · rfl

/-- **Challengers with the same replies along an equivalence of their coins give the same
answers.** -/
theorem answer_toPureEnv_congr {C C' : Challenger X Y Req Resp} (e : C.Coins ≃ C'.Coins)
    (hQ : C.Q = C'.Q) (hresp : ∀ c, C.respond c = C'.respond (e c)) (H : X → Y) (c : C.Coins)
    {m : ℕ} (lg : LogReg Req m) (k : Fin m) :
    C.toPureEnv.answer (H, c) lg k = C'.toPureEnv.answer (H, e c) lg k := by
  unfold Env.answer Env.answerAfter
  cases lg k with
  | none => rfl
  | some r =>
    simp only [Option.elim, oracleIn_toPureEnv_congr e hQ hresp H c, hQ]
    split_ifs
    · simp only [toPureEnv, hresp]
    · rfl

/-- **Challengers with the same replies along an equivalence of their coins have the same oracles
in force.** -/
theorem oracle_toPureEnv_congr {C C' : Challenger X Y Req Resp} (e : C.Coins ≃ C'.Coins)
    (hQ : C.Q = C'.Q) (hresp : ∀ c, C.respond c = C'.respond (e c)) (H : X → Y) (c : C.Coins)
    {m : ℕ} (lg : LogReg Req m) :
    C.toPureEnv.oracle (H, c) lg = C'.toPureEnv.oracle (H, e c) lg := by
  unfold Env.oracle
  rw [oracleIn_toPureEnv_congr e hQ hresp H c]

end Quantum.Challenger

namespace Quantum.SplitChallenger

variable {X Y Req Resp K D D' : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D']

/-- **A split challenger's coins read through a map of the draws**: two split challengers with the
same key law and the same number of requests, the second drawing the first's draws read through
`f`, have coin laws related by `f` applied to every draw. -/
theorem map_coinLaw (S : SplitChallenger X Y Req Resp K D) (S' : SplitChallenger X Y Req Resp K D')
    (f : D → D') (hQ : S.Q = S'.Q) (hk : S.keys = S'.keys) (hd : S.draw.map f = S'.draw) :
    S.coinLaw.map (fun c => (c.1, fun i => f (c.2 (Fin.cast hQ.symm i)))) = S'.coinLaw := by
  classical
  ext ⟨u, d'⟩
  rw [PMF.map_apply, tsum_fintype (L := .unconditional _), coinLaw_apply, ← hk, ← hd]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single u (fun κ _ hκ => Finset.sum_eq_zero fun d _ =>
      by rw [if_neg fun h => hκ (Prod.mk.inj h).1.symm]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [coinLaw_apply, PMF.map_apply, tsum_fintype (L := .unconditional _)]
  have hprod : ∀ d : Fin S.Q → D, (if (u, d') = (u, fun i => f (d (Fin.cast hQ.symm i))) then
      S.keys u * ∏ i, S.draw (d i) else 0) =
      S.keys u * ∏ i : Fin S'.Q, (if d' i = f (d (Fin.cast hQ.symm i)) then
        S.draw (d (Fin.cast hQ.symm i)) else 0) := by
    intro d
    by_cases h : d' = fun i => f (d (Fin.cast hQ.symm i))
    · rw [if_pos (by rw [h]), Finset.prod_congr rfl fun i _ => if_pos (congrFun h i)]
      congr 1
      exact (Fintype.prod_equiv (finCongr hQ) _ _ fun i => rfl)
    · obtain ⟨i, hi⟩ : ∃ i, d' i ≠ f (d (Fin.cast hQ.symm i)) := by
        by_contra hc
        push_neg at hc
        exact h (funext hc)
      rw [if_neg fun h' => h (Prod.mk.inj h').2, Finset.prod_eq_zero (Finset.mem_univ i)
        (if_neg hi), mul_zero]
  simp only [hprod, ← Finset.mul_sum]
  congr 1
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv ((finCongr hQ).arrowCongr (Equiv.refl D)) _ _ fun d => by
    simp [Equiv.arrowCongr_apply, finCongr_symm]

end Quantum.SplitChallenger

namespace Quantum.KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)

/-- **A challenger read along an equivalence of its coins**: two challengers that answer the same
number of requests, whose coin laws and replies agree along an equivalence `e` of their coins, give
the composition the same law on every event of the adversary's registers, the logs and the coins
(read back through `e`). -/
theorem toOuterMeasure_outLaw_congr {C C' : Challenger X Y Req Resp} (e : C.Coins ≃ C'.Coins)
    (hcoins : ∀ c, C'.coins (e c) = C.coins c) (hQ : C.Q = C'.Q)
    (hresp : ∀ c, C.respond c = C'.respond (e c)) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → C.Coins → Prop) :
    ((B.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs v.chal.coins} =
      ((B.composeBothOut C' id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs (e.symm v.chal.coins)} := by
  classical
  rw [B.toOuterMeasure_outLaw_composeBothOut_id C H, B.toOuterMeasure_outLaw_composeBothOut_id C' H]
  congr 1
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hcoins]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  have hm : B.mgRun C.toPureEnv (H, c) true = B.mgRun C'.toPureEnv (H, e c) true :=
    B.mgRun_congr _ _ (fun lg k => Challenger.answer_toPureEnv_congr e hQ hresp H c lg k)
      (fun lg => Challenger.oracle_toPureEnv_congr e hQ hresp H c lg) true
  have hc : (B.emb C' H (e c) B.slots r).1.chal.coins = e c := rfl
  simp only [hm, hc, Equiv.symm_apply_apply]
  rfl


end Quantum.KindAlg


/-! ### Ring statements -/

namespace RingSignature

variable {X Y : Type} {N : ℕ}

/-- Ring statements as a product. -/
def RingStmt.equivProd {TB : BaseTypes}
    (B : BaseSigner X Y N TB) : RingStmt B ≃ KeyRing B.PK N × B.Msg × B.Pub
    where
  toFun x := (x.ring, x.msg, x.pub)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The insider game's challenger at fixed keys -/

section GameSplit

variable {TS : RingTypes} (S : RingScheme X Y N TS) (n : ℕ) (O : SideOracle S) [DecidableEq TS.PK]

/-- **The reply of the unforgeability game's challenger** at the users' key coins `keys` to a
request answered with the signing coins `c` (`unforgeChallenger` below its request bound). -/
noncomputable def RingScheme.unforgeReply (keys : Fin n → S.KeyCoins) (c : S.SignCoins) :
    UnforgeRequest n O → OracleProg X Y (Quantum.Reply X Y (UnforgeResponse O))
  | .corrupt i => .pure ⟨some (.keyCoins (keys i)), []⟩
  | .sign s R m =>
    if S.pk (keys s) ∈ R.1 then
      (S.sign (S.keyGen (keys s)) R m c).bind fun o => .pure ⟨o.map .signature, []⟩
    else .pure ⟨none, []⟩
  | .sideSign i bm =>
    (O.sign (S.keyGen (keys i)) bm c).bind fun o => .pure ⟨o.map .sideSignature, []⟩

variable [Fintype TS.SignCoins] [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins]

/-- **The challenger of the unforgeability game answers below its bound by `unforgeReply`.** -/
theorem respond_unforgeChallenger (keys : Fin n → S.KeyCoins) (Q : ℕ) (ω : Fin Q → S.SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest n O) (UnforgeResponse O))) (r : UnforgeRequest n O) :
    (unforgeChallenger S n O keys Q).respond ω hist r =
      if h : hist.length < Q then S.unforgeReply n O keys (ω ⟨hist.length, h⟩) r
      else .pure ⟨none, []⟩ := by
  simp only [unforgeChallenger]
  split_ifs
  · cases r <;> rfl
  · rfl

/-- **The unforgeability game's challenger at fixed keys as a split challenger**: no keys (they
are fixed), per request uniform signing coins, the replies `unforgeReply`. -/
noncomputable def RingScheme.gameSplit (keys : Fin n → S.KeyCoins) (Q : ℕ) :
    SplitChallenger X Y (UnforgeRequest n O) (UnforgeResponse O) Unit S.SignCoins where
  keys := PMF.pure ()
  draw := PMF.uniformOfFintype _
  Q := Q
  q := max S.q O.q
  reply _ c _ r := S.unforgeReply n O keys c r
  reply_queries _ c _ r H := by
    have h := (unforgeChallenger S n O keys (Q + 1)).respond_queries (fun _ => c) [] r H
    simp only [respond_unforgeChallenger, List.length_nil, Nat.zero_lt_succ, ↓reduceDIte] at h
    exact h

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [Fintype TS.PK] [Fintype TS.Msg] [DecidableEq TS.Msg] [Fintype TS.KeyCoins]
  [DecidableEq TS.KeyCoins] [Fintype TS.Sig] [DecidableEq TS.Sig]

variable [Fintype O.BMsg] [DecidableEq O.BMsg] [Fintype O.BSig] [DecidableEq O.BSig]

/-- **The unforgeability game's challenger is its split challenger** on every event of the
adversary's registers and the logs. -/
theorem toOuterMeasure_outLaw_unforge_eq_split {O' : Type}
    {ksK : KindShape X Y (UnforgeRequest n O) (UnforgeResponse O)} (K : KindAlg ksK O') (keys : Fin n → S.KeyCoins)
    (Q : ℕ) (H : X → Y) (P : DReg K.W K.width X Y (UnforgeRequest n O) (UnforgeResponse O) →
      LogReg (UnforgeRequest n O) K.slots → Prop) :
    ((K.composeBothOut (unforgeChallenger S n O keys Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs} =
      ((K.composeBothOut (S.gameSplit n O keys Q).toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs} := by
  have h := K.toOuterMeasure_outLaw_congr (C := unforgeChallenger S n O keys Q)
    (C' := (S.gameSplit n O keys Q).toChallenger)
    ((Equiv.punitProd (Fin Q → S.SignCoins)).symm : (Fin Q → S.SignCoins) ≃ Unit × (Fin Q → S.SignCoins))
    (fun (c : Fin Q → S.SignCoins) => by
      refine ((S.gameSplit n O keys Q).coinLaw_apply () c).trans ?_
      change PMF.pure () () * ∏ i : Fin Q, PMF.uniformOfFintype S.SignCoins (c i) =
        PMF.uniformOfFintype (Fin Q → S.SignCoins) c
      rw [PMF.pure_apply_self, one_mul, ← PMF.pi_uniformOfFintype, PMF.pi_apply])
    rfl (fun c => by
      funext hist r
      refine (respond_unforgeChallenger S n O keys Q c hist r).trans ?_
      rfl) H fun a lg _ => P a lg
  exact h

end GameSplit

namespace Insider

open GordieHowe.QROM

variable {TB : BaseTypes}
  (B : BaseSigner X Y N TB)
  {TPS : PSTypes} (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS)
  (adm : KeyRing B.PK N → Prop) [DecidablePred adm] {n : ℕ}

/-! ### Requests, relayed statements and witnesses -/

variable [DecidableEq TB.PK]

variable (n) in
/-- The requests of the insider unforgeability game of `ofBase B PS adm`. -/
abbrev Req : Type := UnforgeRequest (S := ofBase B PS adm) n (SideOracle.none (ofBase B PS adm))

/-- The replies of the insider unforgeability game of `ofBase B PS adm`. -/
abbrev Resp : Type := UnforgeResponse (SideOracle.none (ofBase B PS adm))

variable (n) in
/-- **The statement register of a relayed request**: a ring statement and the request. The request
makes the relay of each request number injective. -/
abbrev RelayStmt : Type := RingStmt B × Req B PS adm n

/-- **The witness register of a relayed proof query**: a position below `N + 1` and a base
signature. -/
abbrev RelayWit : Type := Fin (N + 1) × B.BSig

variable [DecidableEq TB.Msg] [DecidableEq TB.Pub]

/-- Relayed proof queries have decidable equality (given explicitly: instance search gives up on
the product). -/
instance {W' : Type} [DecidableEq W'] [DecidableEq X] [DecidableEq Y] :
    DecidableEq (ProofQuery (RelayStmt B PS adm n) W') :=
  @QROM.instDecidableEqProofQuery _ _ inferInstance inferInstance

variable [Fintype TB.PK] [Fintype TB.Msg] [Fintype TB.Pub]

/-- Relayed proof queries form a finite type. -/
noncomputable instance {W' : Type} [Fintype W'] [DecidableEq X] [DecidableEq Y] :
    Fintype (ProofQuery (RelayStmt B PS adm n) W') :=
  @QROM.instFintypeProofQuery _ _ inferInstance inferInstance

variable [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins]

variable {B} in
/-- The ring witness of a witness register. -/
def RelayWit.toWit (w : RelayWit B) : RingWit B := ⟨w.1, w.2⟩

variable [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]

/-- **The statement of the requests without a proof**: the empty ring, which has no witness. -/
noncomputable def dummyStmt : RingStmt B :=
  ⟨⟨[], Nat.zero_le _⟩, Classical.arbitrary _, Classical.arbitrary _⟩

variable {PS adm}

open Classical in
/-- **The request is a ring-signing request by a member that signs**: a request `(s, R, m)` with
the signer's key `pkOf s` in the supported ring `R` and no refusal at the signing coins `sc`
(`refuses`, at the key's first position, where `ofBase` signs). -/
def signerIn (pkOf : Fin n → B.PK) (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (sc : B.Coins) : Req B PS adm n → Prop
  | .sign s R m => pkOf s ∈ R.1 ∧ adm R ∧ ¬ refuses R (R.1.idxOf (pkOf s)) m sc
  | _ => False

open Classical in
/-- **The statement of request number `c`**: for a ring-signing request `(s, R, m)` by a member
that signs at the request's coins `ds c`, `(R, m, pubOf (ds c))`; otherwise `dummyStmt`. -/
noncomputable def stmtAt (pkOf : Fin n → B.PK)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) (c : ℕ) (r : Req B PS adm n) : RingStmt B :=
  if h : c < Q then
    if signerIn B pkOf refuses (ds ⟨c, h⟩) r then
      match r with
      | .sign _ R m => ⟨R, m, pubOf (ds ⟨c, h⟩)⟩
      | _ => dummyStmt B
    else dummyStmt B
  else dummyStmt B

variable [AddGroup Y]

/-- **The base signature of user `s` for a ring-signing request** at the coins `sc`: `bsign` at the
first position of the user's key, read at the zero oracle (the oracle-free signers read none). -/
def bsigOf (keys : Fin n → B.KeyCoins) (sc : B.Coins) (s : Fin n) (R : KeyRing B.PK N)
    (m : B.Msg) : Option B.BSig :=
  (B.bsign (B.sk (keys s)) R (R.1.idxOf (B.pk (keys s))) m sc).run 0

open Classical in
/-- **The witness of request number `c`**: for a ring-signing request `(s, R, m)` with the signer's
key in `R`, the key's first position and the base signature `bsigOf` at the request's coins
(an arbitrary signature on a refusal); otherwise position `0` and an arbitrary signature. -/
noncomputable def witAt (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ)
    (r : Req B PS adm n) : RelayWit B :=
  if h : c < Q then
    match r with
    | .sign s R m =>
      if hs : B.pk (keys s) ∈ R.1 then
        (⟨R.1.idxOf (B.pk (keys s)),
          lt_of_lt_of_le (List.idxOf_lt_length_iff.2 hs) (Nat.le_succ_of_le R.2)⟩, (bsigOf B keys (ds ⟨c, h⟩) s R m).getD (Classical.arbitrary _))
      else (0, Classical.arbitrary _)
    | _ => (0, Classical.arbitrary _)
  else (0, Classical.arbitrary _)

/-- **The base signature at the coins `sc` verifies, if output**: for a ring-signing request
`(s, R, m)` of a member of a supported ring, every signature `bsigOf` outputs verifies on
`bmsg R m` under `s`'s key (at the zero oracle); every other request qualifies. -/
def drawOk (keys : Fin n → B.KeyCoins) (sc : B.Coins) : Req B PS adm n → Prop
  | .sign s R m => B.pk (keys s) ∈ R.1 → adm R → ∀ σ, bsigOf B keys sc s R m = some σ →
      B.bverify 0 (B.pk (keys s)) (B.bmsg R m) σ = true
  | _ => True

/-- **The draw signs and verifies**: for a ring-signing request `(s, R, m)` with the signer's key
in the supported ring `R`, the base signature `bsigOf` at the draw exists and verifies; true for the
other requests. It is `drawOk` with the refusals excluded (`drawOk_of_drawOkR`). -/
def drawOkR (keys : Fin n → B.KeyCoins) (sc : B.Coins) : Req B PS adm n → Prop
  | .sign s R m => B.pk (keys s) ∈ R.1 → adm R → ∃ σ, bsigOf B keys sc s R m = some σ ∧
      B.bverify 0 (B.pk (keys s)) (B.bmsg R m) σ = true
  | _ => True

omit [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- A draw that signs and verifies is checked. -/
theorem drawOk_of_drawOkR {keys : Fin n → B.KeyCoins} {sc : B.Coins} {r : Req B PS adm n}
    (h : drawOkR B keys sc r) : drawOk B keys sc r := by
  cases r with
  | sign s R m =>
    intro hs ha σ hσ
    obtain ⟨σ', hσ', hv⟩ := h hs ha
    rw [hσ] at hσ'
    cases hσ'
    exact hv
  | corrupt _ => trivial
  | sideSign _ bm => exact bm.elim

open Classical in
/-- **The reply to request number `c < Q`** from the main reply `a`: the key coins `kcOf i` of a
corrupted user, or for a ring-signing request by a member that signs the main proof with the
public value `pubOf (ds c)` as a ring signature; `none` otherwise and from request `Q` on. -/
noncomputable def sideAnswer (pkOf : Fin n → B.PK) (kcOf : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) (c : ℕ) (r : Req B PS adm n) (a : Option PS.Proof) :
    Option (Resp B PS adm) :=
  if h : c < Q then
    match r with
    | .corrupt i => some (.keyCoins (kcOf i))
    | .sign s R m =>
      if signerIn B pkOf refuses (ds ⟨c, h⟩) (.sign s R m) then
        a.map fun π => .signature ((pubOf (ds ⟨c, h⟩), π) : B.Pub × PS.Proof)
      else none
    | .sideSign _ bm => bm.elim
  else none

/-- **The relay of statements** (to the simulator of the simulation-extraction game): request
number `c` is sent as its statement `stmtAt` with the request, and answered by `sideAnswer` from the
public keys `pkOf`, the key coins `kcOf` (read only for corrupted users), the refusals and the
public values of the coins `ds`. It reads no secret key. -/
noncomputable def seRelay (pkOf : Fin n → B.PK) (kcOf : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) :
    SideRelay (Req B PS adm n) (Resp B PS adm) (RelayStmt B PS adm n) PS.Proof where
  route c r := (stmtAt B pkOf refuses pubOf ds c r, r)
  answer := sideAnswer B pkOf kcOf refuses pubOf ds

omit [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [AddGroup Y] in
/-- **The replies of the multi-user game without signatures** from the key coins `kc`: the public
key of user `i`, the key coins of a corrupted user; `none` to a signing request. -/
def keyReply (kc : Fin n → B.KeyCoins) :
    Signature.MURequest (Signature.SignOracle.ring B) n → Option (Signature.MUResponse B.core)
  | .publicKey i => some (.publicKey (B.pk (kc i)))
  | .corrupt i => some (.keyCoins (kc i))
  | .sign _ _ => none

omit [Nonempty B.BSig] [AddGroup Y] in
open Classical in
/-- **The relay of statements with the corruptions as requests of the multi-user game**: as
`seRelay`, with a corruption of user `i` among the first `Q` requests the outer request `corrupt i`
of MU-EUF-CMA^corr, answered from its reply, the user's key coins (`TwoRelay.answer₂`), and the
other requests (a later corruption among them) answered as by `sideAnswer` (`TwoRelay.answer₁`). It reads no key coins: they come from the outer replies. No
outer request is `publicKey 0` (`seTwo_outer_ne`), the dummy of the bridge. -/
noncomputable def seTwo (pkOf : Fin n → B.PK)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) :
    Quantum.TwoRelay (Req B PS adm n) (Resp B PS adm) (RelayStmt B PS adm n) PS.Proof
      (Signature.MURequest (Signature.SignOracle.ring B) n) (Signature.MUResponse B.core) where
  route₁ c r := (stmtAt B pkOf refuses pubOf ds c r, r)
  answer₁ c r a :=
    if h : c < Q then
      match r with
      | .corrupt _ => none
      | .sign s R m =>
        if signerIn B pkOf refuses (ds ⟨c, h⟩) (.sign s R m) then
          a.map fun π => .signature ((pubOf (ds ⟨c, h⟩), π) : B.Pub × PS.Proof)
        else none
      | .sideSign _ bm => bm.elim
    else none
  outer c r := match r with
    | .corrupt i => if c < Q then some (.corrupt i) else none
    | _ => none
  answer₂ c _ x :=
    if c < Q then
      match x with
      | some (.keyCoins kc) => some (.keyCoins kc)
      | _ => none
    else none

omit [Nonempty B.BSig] [AddGroup Y] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The outer requests of `seTwo` are never the dummy `publicKey 0`**: the hypothesis of the
bridge (`Quantum.ExtBridge`) holds for `seTwo` with the dummy `publicKey 0`. -/
theorem seTwo_outer_ne [NeZero n] (pkOf : Fin n → B.PK)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) :
    ∀ c r q, (seTwo B (PS := PS) (adm := adm) pkOf refuses pubOf ds).outer c r = some q →
      q ≠ .publicKey 0 := by
  intro c r q h
  cases r with
  | corrupt i =>
    by_cases hc : c < Q
    · simp only [seTwo, if_pos hc, Option.some.injEq] at h
      subst h
      simp
    · simp [seTwo, hc] at h
  | sign s R m => simp [seTwo] at h
  | sideSign j bm => exact bm.elim

omit [Nonempty B.BSig] [AddGroup Y] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **At the key coins as outer replies, the relay with outer corruptions is `seRelay`.** -/
theorem seTwo_atC (pkOf : Fin n → B.PK) (kcOf : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) :
    (seTwo B (PS := PS) (adm := adm) pkOf refuses pubOf ds).atC (fun _ => keyReply B kcOf) =
      seRelay B pkOf kcOf refuses pubOf ds := by
  simp only [Quantum.TwoRelay.atC, seTwo, seRelay, Quantum.SideRelay.mk.injEq, true_and]
  funext c r a
  unfold sideAnswer
  cases r with
  | corrupt i => by_cases h : c < Q <;> simp [h, keyReply]
  | sign s R m => by_cases h : c < Q <;> simp [h]
  | sideSign j bm => exact bm.elim

open Classical in
/-- **The statement of a proof query**: the statement `stmtAt` of request number `c` when its base
signature at the request's coins exists and verifies (`drawOkR`), `dummyStmt` otherwise. -/
noncomputable def zkStmt (keys : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) (c : ℕ) (r : Req B PS adm n) : RingStmt B :=
  if h : c < Q then
    if drawOkR B keys (ds ⟨c, h⟩) r then stmtAt B (fun i => B.pk (keys i)) refuses pubOf ds c r
    else dummyStmt B
  else dummyStmt B

/-- **The relay of proof queries** (to the real and the simulated zero-knowledge challengers) at
the users' key coins `keys` and the signing coins `ds`, with the witnesses encoded by `enc` in a
finite type `W'`: request number `c` is sent as the proof query of its statement `zkStmt` (with the
request) and the encoding of its witness `witAt`, and answered by `sideAnswer`. -/
noncomputable def zkRelay {W' : Type} (enc : RingStmt B → RelayWit B → W')
    (keys : Fin n → B.KeyCoins) (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop)
    (pubOf : B.Coins → B.Pub) {Q : ℕ} (ds : Fin Q → B.Coins) :
    SideRelay (Req B PS adm n) (Resp B PS adm) (ProofQuery (RelayStmt B PS adm n) W')
      PS.Proof where
  route c r := ⟨(zkStmt B keys refuses pubOf ds c r, r),
    enc (zkStmt B keys refuses pubOf ds c r) (witAt B keys ds c r)⟩
  answer := sideAnswer B (fun i => B.pk (keys i)) keys refuses pubOf ds

omit [Nonempty B.BSig] [AddGroup Y] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
theorem seRelay_route_injective (pkOf : Fin n → B.PK) (kcOf : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) (c : ℕ) :
    Function.Injective ((seRelay B pkOf kcOf refuses pubOf ds (PS := PS) (adm := adm)).route c) :=
  fun _ _ h => congrArg Prod.snd h

omit [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
theorem zkRelay_route_injective {W' : Type} (enc : RingStmt B → RelayWit B → W')
    (keys : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) {Q : ℕ}
    (ds : Fin Q → B.Coins) (c : ℕ) :
    Function.Injective ((zkRelay B enc keys refuses pubOf ds (PS := PS) (adm := adm)).route c) :=
  fun _ _ h => congrArg (fun q => q.stmt.2) h

omit [AddGroup Y] in
/-- **The signer of `ofBase` refuses unsupported rings.** -/
theorem _root_.GordieHowe.RingSignature.sign_ofBase_of_not_supported {TB : BaseTypes}
    [DecidableEq TB.PK]
    (B : BaseSigner X Y N TB)
    {TPS : PSTypes} (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS) (adm : KeyRing B.PK N → Prop)
    [DecidablePred adm] (kp : B.PK × B.SK) {R : KeyRing B.PK N} (ha : ¬ adm R) (m : B.Msg)
    (c : B.Coins × PS.Coins) : (ofBase B PS adm).sign kp R m c = .pure none := by
  simp only [ofBase_sign]
  rw [if_neg fun h => ha h.2]

/-! ### The relation on the relayed proof queries -/

section Relation

variable {B}

omit [Nonempty B.BSig] [AddGroup Y] [DecidablePred adm] [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] in
/-- **The statement of the requests without a proof has no witness.** -/
theorem dummyStmt_not_mem_ringRel (H : X → Y) (w : RingWit B) :
    (dummyStmt B, w) ∉ ringRel B adm H := fun h => Nat.not_lt_zero _ h.idx_lt

omit [Nonempty B.BSig] [AddGroup Y] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- A request that is not a ring-signing request by a member that signs has the statement
`dummyStmt`. -/
theorem stmtAt_of_not {pkOf : Fin n → B.PK} {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop}
    {pubOf : B.Coins → B.Pub} {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ} {r : Req B PS adm n}
    (h : ¬ ∃ h : c < Q, signerIn B pkOf refuses (ds ⟨c, h⟩) r) :
    stmtAt B pkOf refuses pubOf ds c r = dummyStmt B := by
  unfold stmtAt
  split_ifs with hc hs
  · exact absurd ⟨hc, hs⟩ h
  · rfl
  · rfl

omit [Nonempty B.BSig] [AddGroup Y] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- The statement of a ring-signing request by a member that signs. -/
theorem stmtAt_sign {pkOf : Fin n → B.PK} {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop}
    {pubOf : B.Coins → B.Pub} {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ} (hc : c < Q) {s : Fin n}
    {R : KeyRing (ofBase B PS adm).PK N} {m : (ofBase B PS adm).Msg}
    (h : signerIn (PS := PS) (adm := adm) B pkOf refuses (ds ⟨c, hc⟩) (.sign s R m)) :
    stmtAt (PS := PS) (adm := adm) B pkOf refuses pubOf ds c (.sign s R m) =
      ⟨R, m, pubOf (ds ⟨c, hc⟩)⟩ := by
  unfold stmtAt
  rw [dif_pos hc, if_pos h]

omit [Nonempty B.Msg] [Nonempty B.Pub] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- The witness of a ring-signing request with the signer's key in the ring. -/
theorem witAt_sign (keys : Fin n → B.KeyCoins) {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ} (hc : c < Q)
    {s : Fin n} {R : KeyRing (ofBase B PS adm).PK N} {m : (ofBase B PS adm).Msg}
    (hs : B.pk (keys s) ∈ R.1) :
    (witAt (PS := PS) (adm := adm) B keys ds c (.sign s R m)).toWit =
      ⟨R.1.idxOf (B.pk (keys s)), (bsigOf B keys (ds ⟨c, hc⟩) s R m).getD (Classical.arbitrary _)⟩ := by
  unfold witAt
  simp only [dif_pos hc]
  split_ifs
  rfl

variable {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}

omit [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] in
/-- **An oracle-free signer refusing as `refuses` outputs a signature exactly when it does not
refuse.** -/
theorem bsigOf_eq_none_iff (href : B.RefusalOfCoins refuses) (keys : Fin n → B.KeyCoins)
    (sc : B.Coins) (s : Fin n) {R : KeyRing B.PK N} (hs : B.pk (keys s) ∈ R.1) (m : B.Msg) :
    bsigOf B keys sc s R m = none ↔ refuses R (R.1.idxOf (B.pk (keys s))) m sc :=
  href 0 (keys s) R _ (List.getElem?_idxOf hs) m sc

omit [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The relayed statement of a ring-signing request by a member that signs, numbered below `Q`,
whose base signature exists and verifies (`drawOkR`) is in the ring relation** with its witness,
for an oracle-free base signer (`hB`) whose public values are `pubOf` of the coins (`hpub`). -/
theorem mem_ringRel_of (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf) (H : X → Y)
    (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ) (r : Req B PS adm n)
    (h : ∃ h : c < Q, signerIn B (fun i => B.pk (keys i)) refuses (ds ⟨c, h⟩) r ∧
      drawOkR B keys (ds ⟨c, h⟩) r) :
    (stmtAt B (fun i => B.pk (keys i)) refuses pubOf ds c r, (witAt B keys ds c r).toWit) ∈
      ringRel B adm H := by
  obtain ⟨hc, hsg, hd⟩ := h
  cases r with
  | corrupt i => exact hsg.elim
  | sideSign i bm => exact bm.elim
  | sign s R m =>
    obtain ⟨hs, ha, -⟩ := id hsg
    obtain ⟨σ, hσ, hv⟩ := hd hs ha
    rw [stmtAt_sign hc hsg, witAt_sign keys hc hs, hσ, Option.getD_some]
    have hlt : R.1.idxOf (B.pk (keys s)) < R.1.length := List.idxOf_lt_length_iff.2 hs
    have hget : R.1[R.1.idxOf (B.pk (keys s))]'hlt = B.pk (keys s) := List.getElem_idxOf hlt
    refine ⟨ha, hlt, ?_, ?_⟩
    · rw [← hB.bverify_eq 0 H]
      convert hv using 2
    · rw [hB.run_pub_eq _ _ H 0]
      convert hpub 0 (keys s) R _ (List.getElem?_idxOf hs) m _ σ hσ using 3

omit [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] in
open Classical in
omit [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The game's reply to a ring-signing request, run**, for an oracle-free base signer: the base
signature of the user at the draw (`bsigOf`) with its public value and the prover's proof as a ring
signature, when the user's key is in the supported ring and the base signer does not refuse;
`none` otherwise. -/
theorem run_unforgeReply_sign (hB : B.OracleFree) (keys : Fin n → B.KeyCoins)
    (d : B.Coins × PS.Coins) (s : Fin n) (R : KeyRing (ofBase B PS adm).PK N)
    (m : (ofBase B PS adm).Msg) (G : X → Y) :
    ((ofBase B PS adm).unforgeReply n (SideOracle.none _) keys d (.sign s R m)).run G =
      ⟨if B.pk (keys s) ∈ R.1 ∧ adm R then
          (bsigOf B keys d.1 s R m).map fun σ => .signature (((B.pub (B.pk (keys s)) σ).run 0,
            (PS.prove ⟨R, m, (B.pub (B.pk (keys s)) σ).run 0⟩
              ⟨R.1.idxOf (B.pk (keys s)), σ⟩ d.2).run G) : B.Pub × PS.Proof)
        else none, []⟩ := by
  simp only [RingScheme.unforgeReply]
  split_ifs with h1 h2 h2
  · erw [sign_ofBase_of_mem B PS adm h1 h2.2, OracleProg.run_bind]
    have hb : (B.bsign (B.sk (keys s)) R (R.1.idxOf (B.pk (keys s))) m d.1).run G =
        bsigOf B keys d.1 s R m := hB.run_bsign_eq _ _ _ _ _ G 0
    rcases hσ : bsigOf B keys d.1 s R m with _ | σ
    · rw [hσ] at hb
      erw [(BaseSigner.run_signAt_eq_none_iff B PS).2 hb]
      rfl
    · rw [hσ] at hb
      erw [run_signAt_of_bsign B PS hb, hB.run_pub_eq _ _ G 0]
      rfl
  · erw [sign_ofBase_of_not_supported B PS adm _ fun h => h2 ⟨h1, h⟩]
    rfl
  · exact absurd h2.1 h1
  · rfl

omit [Nonempty B.BSig] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
open Classical in
omit [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- The proof query's statement of a request whose base signature exists and verifies is its
statement. -/
theorem zkStmt_of_drawOk (keys : Fin n → B.KeyCoins) {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ}
    (hc : c < Q) {r : Req B PS adm n} (hd : drawOkR B keys (ds ⟨c, hc⟩) r) :
    zkStmt B keys refuses pubOf ds c r = stmtAt B (fun i => B.pk (keys i)) refuses pubOf ds c r := by
  unfold zkStmt
  rw [dif_pos hc, if_pos hd]

omit [Nonempty B.BSig] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
open Classical in
omit [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The proof query's statement has the empty ring** unless the request is a ring-signing request
by a member that signs whose base signature exists and verifies. -/
theorem zkStmt_ring_nil (keys : Fin n → B.KeyCoins) {Q : ℕ} {ds : Fin Q → B.Coins} {c : ℕ}
    {r : Req B PS adm n}
    (h : ¬ ∃ h : c < Q, signerIn B (fun i => B.pk (keys i)) refuses (ds ⟨c, h⟩) r ∧
      drawOkR B keys (ds ⟨c, h⟩) r) :
    (zkStmt B keys refuses pubOf ds c r).ring.1 = [] := by
  unfold zkStmt
  split_ifs with hc hd
  · rw [stmtAt_of_not fun ⟨hc', hs⟩ => h ⟨hc', hs, hd⟩]
    rfl
  · rfl
  · rfl

omit [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The relayed proof query is in a relation `relH` of statements `stmt x` and encoded witnesses
exactly for a ring-signing request by a member that signs, numbered below `Q`, whose base signature
exists and verifies** (`drawOkR`), when every ring witness's encoding is a witness of `relH`
(`hsign`) and no statement of the empty ring has one (`hnil`), for an oracle-free base signer
(`hB`) whose public values are `pubOf` of the coins (`hpub`). -/
theorem mem_relZ_iff (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf) {X₀ Wit₀ W' : Type} (stmt : RingStmt B → X₀)
    (fw : W' → Wit₀) (enc : RingStmt B → RelayWit B → W') {relH : Set (X₀ × Wit₀)}
    (hsign : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 → (stmt x, fw (enc x w)) ∈ relH)
    (hnil : ∀ x : RingStmt B, x.ring.1 = [] → ∀ y, (stmt x, y) ∉ relH)
    (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ) (r : Req B PS adm n) :
    (stmt (zkStmt B keys refuses pubOf ds c r),
        fw (enc (zkStmt B keys refuses pubOf ds c r) (witAt B keys ds c r))) ∈ relH ↔
      ∃ h : c < Q, signerIn B (fun i => B.pk (keys i)) refuses (ds ⟨c, h⟩) r ∧
        drawOkR B keys (ds ⟨c, h⟩) r := by
  by_cases hex : ∃ h : c < Q, signerIn B (fun i => B.pk (keys i)) refuses (ds ⟨c, h⟩) r ∧
      drawOkR B keys (ds ⟨c, h⟩) r
  · refine iff_of_true ?_ hex
    obtain ⟨hc, hs, hd⟩ := hex
    rw [zkStmt_of_drawOk keys hc hd]
    exact hsign _ _ (mem_ringRel_of hB hpub 0 keys ds c r ⟨hc, hs, hd⟩)
  · exact iff_of_false (hnil _ (zkStmt_ring_nil keys hex) _) hex

end Relation

/-! ### The challengers at fixed keys -/

section Challengers

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins]

variable {B}

/-- **The checked reply** at the key coins `keys` and the draw `d` (base signing coins and prover
coins): the reply of the insider game (`RingScheme.unforgeReply`), and `none` to a ring-signing
request of a member of a supported ring whose base signature at the draw fails to verify
(`drawOk`). A proof device: it differs from the game's reply only on such a draw. -/
noncomputable def checkedReply (keys : Fin n → B.KeyCoins) (d : B.Coins × PS.Coins)
    (r : Req B PS adm n) : OracleProg X Y (Reply X Y (Resp B PS adm)) :=
  open Classical in
  if drawOk B keys d.1 r then (ofBase B PS adm).unforgeReply n (SideOracle.none _) keys d r
  else .pure ⟨none, []⟩

variable (PS adm) in
/-- **The checked game at fixed keys as a split challenger**: the game's split challenger
(`RingScheme.gameSplit`) with the checked replies. -/
noncomputable def checkedSplit (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    SplitChallenger X Y (Req B PS adm n) (Resp B PS adm) Unit (B.Coins × PS.Coins) :=
  ((ofBase B PS adm).gameSplit n (SideOracle.none _) keys Q).withReply
    (fun _ d _ r => checkedReply keys d r) fun κ d i r H => by
      unfold checkedReply
      split_ifs
      · exact ((ofBase B PS adm).gameSplit n (SideOracle.none _) keys Q).reply_queries κ d i r H
      · simp

variable {SC : Type} [Fintype SC] [DecidableEq SC]

open Classical in
/-- **The reply of the simulated challengers** to request number `i` at the key coins `keys` and
the draw `d` (base signing coins and simulator coins), with the test `ok` of the draw: a ring-signing
request by a member that signs (`signerIn`) whose draw passes `ok` runs `Sim` on its statement
`stmtAt` (with the public value `pubOf` of the signing coins), answers with the simulated proof as a
ring signature and appends the simulator's assignments; such a request failing `ok` gets `none`;
any other request is answered by `sideAnswer` without queries or assignments. -/
noncomputable def simReply (keys : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ)
    (ok : B.Coins → Req B PS adm n → Prop) (d : B.Coins × SC) (i : ℕ) (r : Req B PS adm n) :
    OracleProg X Y (Reply X Y (Resp B PS adm)) :=
  if signerIn B (fun i => B.pk (keys i)) refuses d.1 r then
    if ok d.1 r then
      (Sim.prog (stmtAt B (fun i => B.pk (keys i)) refuses pubOf (fun _ : Fin Q => d.1) i r)
          d.2).bind fun o =>
        .pure ⟨sideAnswer B (fun i => B.pk (keys i)) keys refuses pubOf (fun _ : Fin Q => d.1) i r
          (some o.proof), o.assignments⟩
    else .pure ⟨none, []⟩
  else .pure ⟨sideAnswer B (fun i => B.pk (keys i)) keys refuses pubOf (fun _ : Fin Q => d.1) i r
    none, []⟩

variable (PS adm) in
/-- **The simulated challengers at fixed keys as split challengers**: per request uniform base
signing coins and simulator coins, the replies `simReply` with the test `ok`. -/
noncomputable def simSplit (keys : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ)
    (ok : B.Coins → Req B PS adm n → Prop) :
    SplitChallenger X Y (Req B PS adm n) (Resp B PS adm) Unit (B.Coins × SC) where
  keys := PMF.pure ()
  draw := (PMF.uniformOfFintype B.Coins).bind fun c => Sim.coins.map fun d => (c, d)
  Q := Q
  q := Sim.q
  reply _ d i r := simReply keys refuses pubOf Sim Q ok d i r
  reply_queries _ d i r H := by
    unfold simReply
    split_ifs
    · rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
      exact Sim.prog_queries _ _ H
    · simp
    · simp

/-- **The simulator answering `p₀` on the empty ring**: on a statement with the empty ring it
returns `p₀` without queries or assignments; on every other statement it runs `Sim`.

Running time: that of `Sim`, and one test of the ring's emptiness. This running time is argued
here, not proved in Lean. -/
def inertOnEmpty (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (p₀ : PS.Proof) :
    NARG.Simulator X Y (RingStmt B) PS.Proof SC where
  prog x c := if x.ring.1 = [] then .pure ⟨p₀, []⟩ else Sim.prog x c
  coins_nonempty := Sim.coins_nonempty
  q := Sim.q
  prog_queries x c H := by
    split_ifs
    · simp
    · exact Sim.prog_queries x c H

variable (PS adm) in
/-- **The refusing challenger at fixed keys**: per request uniform signing coins, every request
answered by `sideAnswer` without a proof (the key coins of a corrupted user, `none` otherwise). -/
noncomputable def refuseSplit (keys : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) (pubOf : B.Coins → B.Pub) (Q : ℕ) :
    SplitChallenger X Y (Req B PS adm n) (Resp B PS adm) Unit B.Coins where
  keys := PMF.pure ()
  draw := PMF.uniformOfFintype B.Coins
  Q := Q
  q := 0
  reply _ c i r := .pure ⟨sideAnswer B (fun i => B.pk (keys i)) keys refuses pubOf
    (fun _ : Fin Q => c) i r none, []⟩
  reply_queries _ _ _ _ _ := by simp [OracleProg.trace_pure]

/-! ### The relays -/

variable {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop} {pubOf : B.Coins → B.Pub}

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC]
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [AddGroup Y] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- The reply to a request that is not a ring-signing request by a member that signs does not read
the main reply. -/
theorem sideAnswer_of_not {pkOf : Fin n → B.PK} {kcOf : Fin n → B.KeyCoins} {Q : ℕ}
    {ds : Fin Q → B.Coins} {c : ℕ} {r : Req B PS adm n}
    (h : ¬ ∃ h : c < Q, signerIn B pkOf refuses (ds ⟨c, h⟩) r) (a : Option PS.Proof) :
    sideAnswer B pkOf kcOf refuses pubOf ds c r a = sideAnswer B pkOf kcOf refuses pubOf ds c r none := by
  unfold sideAnswer
  split_ifs with hc
  · cases r with
    | corrupt i => rfl
    | sideSign i bm => exact bm.elim
    | sign s R m =>
      dsimp only
      rw [if_neg fun hs => h ⟨hc, hs⟩, if_neg fun hs => h ⟨hc, hs⟩]
  · rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC]
  [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] in
open Classical in
omit [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The checked game at fixed keys relays the real zero-knowledge challenger** of a prover `Pz`
of statements `stmt x` (a program's statements) on the relayed proof queries (`zkRelay` with the
witness encoding `enc`), for the relation `relH` read at the decoding `fw`, at the signing coins `ds`
and the prover coins `pcs`: when every ring witness's encoding is a witness of `relH` (`hsign`), no
statement of the empty ring has one (`hnil`), and on a ring witness the ring prover is `Pz` at
`(stmt x, fw (enc x w))` (`hP`), for an oracle-free base signer (`hB`) whose public values are `pubOf`
of the coins (`hpub`) and which refuses whenever `refuses` predicts it (`hsound`). -/
theorem relays_real (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf)
    (hsound : B.RefusalSound refuses) {X₀ Wit₀ W' : Type} (stmt : RingStmt B → X₀)
    (fw : W' → Wit₀) (enc : RingStmt B → RelayWit B → W') {relH : Set (X₀ × Wit₀)}
    (hsign : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 → (stmt x, fw (enc x w)) ∈ relH)
    (hnil : ∀ x : RingStmt B, x.ring.1 = [] → ∀ y, (stmt x, y) ∉ relH)
    (Pz : NARG.Prover X Y X₀ Wit₀ PS.Proof PS.Coins)
    (hP : ∀ x (w : RelayWit B) c, (x, w.toWit) ∈ ringRel B adm 0 →
      Pz.prog (stmt x) (fw (enc x w)) c = PS.prove x w.toWit c)
    (keys : Fin n → B.KeyCoins) {Q : ℕ} (ds : Fin Q → B.Coins) (pcs : Fin Q → PS.Coins) :
    (zkRelay B enc keys refuses pubOf ds (PS := PS) (adm := adm)).RelaysChallenger
      (checkedSplit PS adm keys Q).toChallenger ((), fun i => (ds i, pcs i))
      (realChallenger (fun x w => (stmt x.1, fw w) ∈ relH) (Pz.comap (stmt ∘ Prod.fst) fw) (PMF.uniformOfFintype _) Q)
        pcs := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [SplitChallenger.toChallenger, checkedSplit, SplitChallenger.withReply, realChallenger,
      RingScheme.gameSplit, zkRelay, dif_pos hQ, dif_pos hQ', hi, NARG.Prover.comap,
      Function.comp_apply]
    have hmem := mem_relZ_iff (PS := PS) (adm := adm) (refuses := refuses) hB hpub stmt fw enc hsign hnil keys ds
      hist.length r
    by_cases hr : ∃ h : hist.length < Q,
        signerIn B (fun i => B.pk (keys i)) refuses (ds ⟨hist.length, h⟩) r ∧
          drawOkR B keys (ds ⟨hist.length, h⟩) r
    · have hxw := mem_ringRel_of hB hpub 0 keys ds hist.length r hr
      obtain ⟨hQ'', hsg, hd⟩ := hr
      rw [if_pos (hmem.2 ⟨hQ'', hsg, hd⟩)]
      rw [zkStmt_of_drawOk keys hQ'' hd, hP _ _ _ hxw]
      cases r with
      | corrupt i => exact hsg.elim
      | sideSign i bm => exact bm.elim
      | sign s R m =>
        obtain ⟨hs, ha, hnr⟩ := id hsg
        obtain ⟨σ, hσ, -⟩ := hd hs ha
        have hp : (B.pub (B.pk (keys s)) σ).run 0 = pubOf (ds ⟨hist.length, hQ⟩) :=
          hpub 0 (keys s) R _ (List.getElem?_idxOf hs) m _ σ hσ
        unfold checkedReply
        rw [if_pos (drawOk_of_drawOkR B hd)]
        erw [run_unforgeReply_sign hB keys _ s R m G]
        rw [if_pos ⟨hs, ha⟩]
        simp only [OracleProg.run_bind, OracleProg.run_pure]
        rw [stmtAt_sign hQ hsg, witAt_sign keys hQ hs, hσ, Option.getD_some, Option.map_some]
        unfold sideAnswer
        rw [dif_pos hQ]
        dsimp only
        rw [if_pos hsg, Option.map_some, hp]
    · rw [if_neg fun h => hr (hmem.1 h)]
      simp only [OracleProg.run_pure]
      cases r with
      | corrupt i =>
        unfold checkedReply
        rw [if_pos (show drawOk (PS := PS) (adm := adm) B keys _ (.corrupt i) from trivial)]
        simp only [RingScheme.unforgeReply, OracleProg.run_pure, sideAnswer, dif_pos hQ]
      | sideSign i bm => exact bm.elim
      | sign s R m =>
        have hn : sideAnswer B (fun i => B.pk (keys i)) keys refuses pubOf ds hist.length
            (.sign s R m) (none : Option PS.Proof) = none := by
          simp only [sideAnswer, dif_pos hQ, Option.map_none, ite_self]
        rw [hn]
        unfold checkedReply
        split_ifs with hd
        · erw [run_unforgeReply_sign hB keys _ s R m G]
          split_ifs with hm
          · have hnone : bsigOf B keys (ds ⟨hist.length, hQ⟩) s R m = none := by
              rcases hσ : bsigOf B keys (ds ⟨hist.length, hQ⟩) s R m with _ | σ
              · rfl
              · refine absurd ⟨hQ, ⟨hm.1, hm.2, fun hrf => ?_⟩,
                  fun _ _ => ⟨σ, hσ, hd hm.1 hm.2 σ hσ⟩⟩ hr
                have h0 : bsigOf B keys (ds ⟨hist.length, hQ⟩) s R m = none :=
                  hsound 0 (keys s) R _ (List.getElem?_idxOf hm.1) m _ hrf
                rw [h0] at hσ
                cases hσ
            rw [hnone]
            rfl
          · rfl
        · rfl
  · intro i r h
    change Q ≤ i at h
    simp only [zkRelay, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC]
  [Nonempty B.BSig] [AddGroup Y] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- The statement of a request depends on the signing coins only at its own number. -/
theorem stmtAt_congr {pkOf : Fin n → B.PK} {Q : ℕ} {ds ds' : Fin Q → B.Coins} {c : ℕ}
    (hc : ∀ h : c < Q, ds ⟨c, h⟩ = ds' ⟨c, h⟩) (r : Req B PS adm n) :
    stmtAt B pkOf refuses pubOf ds c r = stmtAt B pkOf refuses pubOf ds' c r := by
  unfold stmtAt
  split_ifs with h1 h2 h3 h3 <;> first | rfl | (rw [hc h1] at h2; exact absurd h2 h3) |
    (rw [hc h1] at h2; exact absurd h3 h2) | (cases r <;> simp [hc h1])

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC]
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [AddGroup Y] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- The reply to a request depends on the signing coins only at its own number. -/
theorem sideAnswer_congr {pkOf : Fin n → B.PK} {kcOf : Fin n → B.KeyCoins} {Q : ℕ}
    {ds ds' : Fin Q → B.Coins} {c : ℕ} (hc : ∀ h : c < Q, ds ⟨c, h⟩ = ds' ⟨c, h⟩)
    (r : Req B PS adm n) (a : Option PS.Proof) :
    sideAnswer B pkOf kcOf refuses pubOf ds c r a = sideAnswer B pkOf kcOf refuses pubOf ds' c r a := by
  unfold sideAnswer
  split_ifs with h
  · rw [hc h]
  · rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Nonempty B.BSig] [AddGroup Y]
  [Fintype SC] [DecidableEq SC] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The statement of a ring-signing request by a member that signs has a nonempty ring**; every
other request has the empty ring of `dummyStmt`. -/
theorem stmtAt_ring_eq_nil_iff (pkOf : Fin n → B.PK) {Q : ℕ} (ds : Fin Q → B.Coins) (c : ℕ)
    (r : Req B PS adm n) :
    (stmtAt B pkOf refuses pubOf ds c r).ring.1 = [] ↔
      ¬ ∃ h : c < Q, signerIn B pkOf refuses (ds ⟨c, h⟩) r := by
  by_cases h : ∃ h : c < Q, signerIn B pkOf refuses (ds ⟨c, h⟩) r
  · refine iff_of_false ?_ (not_not.2 h)
    obtain ⟨hc, hs⟩ := h
    cases r with
    | corrupt i => exact hs.elim
    | sideSign i bm => exact bm.elim
    | sign s R m =>
      rw [stmtAt_sign hc hs]
      intro hR
      have h2 : pkOf s ∈ R.1 := hs.1
      change R.1 = [] at hR
      rw [hR] at h2
      exact List.not_mem_nil h2
  · rw [stmtAt_of_not h]
    exact iff_of_true rfl h

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] in
open Classical in
omit [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The checked simulated challenger relays the simulated zero-knowledge challenger** of a
simulator `Simz` of statements `stmt x` on the relayed proof queries (`zkRelay` with the witness
encoding `enc`), the simulated ring signatures being `Simz` read at `stmt`, with the test `drawOkR`,
under the hypotheses of `relays_real` but `hsound`. -/
theorem relays_sim_zk (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf) {X₀ Wit₀ W' : Type} (stmt : RingStmt B → X₀)
    (fw : W' → Wit₀) (enc : RingStmt B → RelayWit B → W') {relH : Set (X₀ × Wit₀)}
    (hsign : ∀ x (w : RelayWit B), (x, w.toWit) ∈ ringRel B adm 0 → (stmt x, fw (enc x w)) ∈ relH)
    (hnil : ∀ x : RingStmt B, x.ring.1 = [] → ∀ y, (stmt x, y) ∉ relH)
    (keys : Fin n → B.KeyCoins) (Simz : NARG.Simulator X Y X₀ PS.Proof SC) {Q : ℕ}
    (ds : Fin Q → B.Coins) (scs : Fin Q → SC) :
    (zkRelay B enc keys refuses pubOf ds (PS := PS) (adm := adm)).RelaysChallenger
      (simSplit PS adm keys refuses pubOf (Simz.comap stmt) Q (drawOkR B keys)).toChallenger
        ((), fun i => (ds i, scs i))
      (simChallenger (fun x w => (stmt x.1, fw w) ∈ relH) (Simz.comap (stmt ∘ Prod.fst)) Q)
        scs := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [SplitChallenger.toChallenger, simSplit, simChallenger, zkRelay, dif_pos hQ,
      dif_pos hQ', hi, NARG.Simulator.comap, Function.comp_apply]
    have hst := stmtAt_congr (PS := PS) (adm := adm) (pkOf := fun i => B.pk (keys i))
      (refuses := refuses) (pubOf := pubOf) (ds := fun _ : Fin Q => ds ⟨hist.length, hQ⟩)
      (ds' := ds) (c := hist.length) (fun _ => rfl) r
    have hsa := sideAnswer_congr (PS := PS) (adm := adm) (pkOf := fun i => B.pk (keys i))
      (kcOf := keys) (refuses := refuses) (pubOf := pubOf)
      (ds := fun _ : Fin Q => ds ⟨hist.length, hQ⟩) (ds' := ds) (c := hist.length) (fun _ => rfl) r
    have hmem := mem_relZ_iff (PS := PS) (adm := adm) (refuses := refuses) hB hpub stmt fw enc hsign hnil keys ds
      hist.length r
    unfold simReply
    simp only [hst, hsa]
    by_cases hs : signerIn B (fun i => B.pk (keys i)) refuses (ds ⟨hist.length, hQ⟩) r
    · by_cases hd : drawOkR B keys (ds ⟨hist.length, hQ⟩) r
      · rw [if_pos hs, if_pos hd, if_pos (hmem.2 ⟨hQ, hs, hd⟩), zkStmt_of_drawOk keys hQ hd]
        simp only [OracleProg.run_bind, OracleProg.run_pure]
      · rw [if_pos hs, if_neg hd, if_neg fun h => hd (hmem.1 h).2.2]
        simp only [OracleProg.run_pure]
        cases r with
        | corrupt i => exact hs.elim
        | sideSign i bm => exact bm.elim
        | sign s R m => simp only [sideAnswer, dif_pos hQ, Option.map_none, ite_self]
    · rw [if_neg hs, if_neg fun h => hs (hmem.1 h).2.1]
      rfl
  · intro i r h
    change Q ≤ i at h
    simp only [zkRelay, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

omit [Nonempty B.BSig] [AddGroup Y] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The simulated challenger relays the simulation-extraction challenger** of a simulator `SimE`
that answers `p₀` without queries or assignments on the statements with the empty ring (`hE₀`) and
runs as `Sim` on the others (`hE₁`), on the relayed statements (`seRelay`), which read the public
keys, the corrupted users' key coins and the signing coins, not the secret keys. -/
theorem relays_sim_se (keys : Fin n → B.KeyCoins)
    (Sim SimE : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (p₀ : PS.Proof)
    (hE₀ : ∀ x : RingStmt B, x.ring.1 = [] → ∀ c, SimE.prog x c = .pure ⟨p₀, []⟩)
    (hE₁ : ∀ x : RingStmt B, x.ring.1 ≠ [] → SimE.prog x = Sim.prog x) {Q : ℕ}
    (ds : Fin Q → B.Coins) (scs : Fin Q → SC) :
    (seRelay B (fun i => B.pk (keys i)) keys refuses pubOf ds (PS := PS) (adm := adm)).RelaysChallenger
      (simSplit PS adm keys refuses pubOf Sim Q fun _ _ => True).toChallenger
        ((), fun i => (ds i, scs i))
      (simExtChallenger (SimE.comap Prod.fst) Q) scs := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hist hist' r G hrel hQ
    have hlen : hist.length = hist'.length := by
      simpa using (congrArg List.length hrel).symm
    change hist.length < Q at hQ
    have hQ' : hist'.length < Q := hlen ▸ hQ
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hQ⟩ := Fin.ext hlen.symm
    simp only [SplitChallenger.toChallenger, simSplit, simExtChallenger, simExtRespond, seRelay,
      dif_pos hQ, dif_pos hQ', hi, NARG.Simulator.comap]
    have hst := stmtAt_congr (PS := PS) (adm := adm) (pkOf := fun i => B.pk (keys i))
      (refuses := refuses) (pubOf := pubOf) (ds := fun _ : Fin Q => ds ⟨hist.length, hQ⟩)
      (ds' := ds) (c := hist.length) (fun _ => rfl) r
    have hsa := sideAnswer_congr (PS := PS) (adm := adm) (pkOf := fun i => B.pk (keys i))
      (kcOf := keys) (refuses := refuses) (pubOf := pubOf)
      (ds := fun _ : Fin Q => ds ⟨hist.length, hQ⟩) (ds' := ds) (c := hist.length) (fun _ => rfl) r
    unfold simReply
    simp only [hst, hsa, if_true]
    by_cases hs : signerIn B (fun i => B.pk (keys i)) refuses (ds ⟨hist.length, hQ⟩) r
    · have hne : ¬ (stmtAt B (fun i => B.pk (keys i)) refuses pubOf ds hist.length r).ring.1 = [] :=
        fun h => (stmtAt_ring_eq_nil_iff _ ds _ r).1 h ⟨hQ, hs⟩
      rw [if_pos hs, hE₁ _ hne]
      simp only [OracleProg.run_bind, OracleProg.run_pure]
    · have he : (stmtAt B (fun i => B.pk (keys i)) refuses pubOf ds hist.length r).ring.1 = [] :=
        (stmtAt_ring_eq_nil_iff _ ds _ r).2 fun ⟨_, h⟩ => hs h
      rw [if_neg hs, hE₀ _ he]
      simp only [OracleProg.run_bind, OracleProg.run_pure]
      rw [sideAnswer_of_not (fun ⟨_, h⟩ => hs h) (some p₀)]
  · intro i r h
    change Q ≤ i at h
    simp only [seRelay, sideAnswer, show ¬ i < Q from not_lt.2 h, dite_false]

omit [Nonempty B.BSig] [AddGroup Y] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [Fintype SC] [DecidableEq SC] [Nonempty B.Msg] [Nonempty B.Pub] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] in
/-- The simulator answering `p₀` on the empty ring answers `p₀` there. -/
theorem prog_inertOnEmpty_nil (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (p₀ : PS.Proof)
    (x : RingStmt B) (hx : x.ring.1 = []) (c : SC) :
    (inertOnEmpty Sim p₀).prog x c = .pure ⟨p₀, []⟩ := by
  simp only [inertOnEmpty, if_pos hx]

omit [Nonempty B.BSig] [AddGroup Y] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [Fintype SC] [DecidableEq SC] [Nonempty B.Msg] [Nonempty B.Pub] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] in
/-- The simulator answering `p₀` on the empty ring runs as the simulator elsewhere. -/
theorem prog_inertOnEmpty_ne (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (p₀ : PS.Proof)
    (x : RingStmt B) (hx : x.ring.1 ≠ []) : (inertOnEmpty Sim p₀).prog x = Sim.prog x := by
  funext c
  simp only [inertOnEmpty, if_neg hx]

/-! ### The coins -/

/-- **Per-request pairs as per-request first and second components** (the split challengers' coins
at fixed keys as side coins and main coins). -/
def coinSplit (Q : ℕ) (D₁ D₂ : Type) : Unit × (Fin Q → D₁ × D₂) ≃ (Fin Q → D₁) × (Fin Q → D₂) where
  toFun ω := (fun i => (ω.2 i).1, fun i => (ω.2 i).2)
  invFun p := ((), fun i => (p.1 i, p.2 i))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype SC] [DecidableEq SC] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Fintype X]
  [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] in
/-- **The coins of the checked game are uniform signing coins and independent prover coins.** -/
theorem coins_checkedSplit (keys : Fin n → B.KeyCoins) (Q : ℕ) (ds : Fin Q → B.Coins)
    (pcs : Fin Q → PS.Coins) :
    (checkedSplit PS adm keys Q).toChallenger.coins ((coinSplit Q B.Coins PS.Coins).symm (ds, pcs)) =
      PMF.uniformOfFintype (Fin Q → B.Coins) ds *
          (PMF.pi fun _ => PMF.uniformOfFintype PS.Coins) pcs := by
  change (checkedSplit PS adm keys Q).coinLaw ((), fun i => (ds i, pcs i)) = _
  rw [SplitChallenger.coinLaw_apply, ← PMF.pi_uniformOfFintype, PMF.pi_apply, PMF.pi_apply]
  change PMF.pure () () * ∏ i, PMF.uniformOfFintype (B.Coins × PS.Coins) (ds i, pcs i) = _
  rw [PMF.pure_apply_self, one_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))

omit [Nonempty B.BSig] [AddGroup Y] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **The coins of the simulated challengers are uniform signing coins and independent simulator
coins.** -/
theorem coins_simSplit (keys : Fin n → B.KeyCoins) (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC)
    (Q : ℕ) (ok : B.Coins → Req B PS adm n → Prop) (ds : Fin Q → B.Coins) (scs : Fin Q → SC) :
    (simSplit PS adm keys refuses pubOf Sim Q ok).toChallenger.coins
        ((coinSplit Q B.Coins SC).symm (ds, scs)) =
      PMF.uniformOfFintype (Fin Q → B.Coins) ds * (PMF.pi fun _ => Sim.coins) scs := by
  change (simSplit PS adm keys refuses pubOf Sim Q ok).coinLaw ((), fun i => (ds i, scs i)) = _
  rw [SplitChallenger.coinLaw_apply, ← PMF.pi_uniformOfFintype, PMF.pi_apply, PMF.pi_apply]
  change PMF.pure () () * ∏ i, ((PMF.uniformOfFintype B.Coins).bind fun c =>
    Sim.coins.map fun d => (c, d)) (ds i, scs i) = _
  rw [PMF.pure_apply_self, one_mul, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Ring.bind_map_pair_apply _ _ _ _

/-! ### The hybrids of the correctness error -/

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC]
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [DecidableEq TB.Coins] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] in
/-- **A draw failing `drawOk` has at most the correctness error**, over uniform signing coins, at
every request, for a base signer with correctness error `ε` (`hcorr`). -/
theorem toOuterMeasure_not_drawOk_le {ε : ℝ≥0∞} (hcorr : B.CorrectWithin ε)
    (keys : Fin n → B.KeyCoins) (r : Req B PS adm n) :
    (PMF.uniformOfFintype B.Coins).toOuterMeasure {c | ¬ drawOk B keys c r} ≤ ε := by
  cases r with
  | corrupt i => simp [drawOk]
  | sideSign i bm => exact bm.elim
  | sign s R m =>
    by_cases hs : B.pk (keys s) ∈ R.1
    · refine le_trans (MeasureTheory.measure_mono fun c hc => ?_)
        (hcorr 0 (keys s) R _ (List.getElem?_idxOf hs) m)
      simp only [Set.mem_setOf_eq, drawOk, not_forall] at hc
      obtain ⟨-, -, σ, hσ, hv⟩ := hc
      exact ⟨σ, hσ, Bool.eq_false_iff.2 hv⟩
    · simp [drawOk, hs]

variable (adm) in
/-- **The unpredicted refusal rate at the users' key coins `keys`**: the largest probability, over
uniform signing coins, that the base signer of a user `s` refuses a ring-signing request `(R, m)`
of a supported ring holding its key (at the key's first position) while `refuses` does not predict
it. It is `0` when `refuses` decides refusals (`refusalGap_eq_zero`). -/
noncomputable def refusalGap (keys : Fin n → B.KeyCoins)
    (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) : ℝ≥0∞ :=
  ⨆ (s : Fin n) (R : KeyRing B.PK N) (_ : B.pk (keys s) ∈ R.1) (_ : adm R) (m : B.Msg),
    (PMF.uniformOfFintype B.Coins).toOuterMeasure
      {c | bsigOf B keys c s R m = none ∧ ¬ refuses R (R.1.idxOf (B.pk (keys s))) m c}

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC]
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [DecidableEq TB.Coins]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **No refusal is unpredicted when `refuses` decides refusals.** -/
theorem refusalGap_eq_zero (href : B.RefusalOfCoins refuses) (keys : Fin n → B.KeyCoins) :
    refusalGap adm keys refuses = 0 := by
  refine le_antisymm (iSup_le fun s => iSup_le fun R => iSup_le fun hs => iSup_le fun _ =>
    iSup_le fun m => le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2
      (Set.disjoint_left.2 fun c _ hc => hc.2 ((bsigOf_eq_none_iff href keys c s hs m).1 hc.1))))
    bot_le

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC]
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [DecidableEq TB.Coins]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **Every refusal is unpredicted by the empty predicate, with rate at most the per-key refusal
rate** (`RefuseAtWithin`). -/
theorem refusalGap_false_le {ρ : ℝ≥0∞} (hρ : B.RefuseAtWithin adm ρ) (keys : Fin n → B.KeyCoins) :
    refusalGap adm keys (fun _ _ _ _ => False) ≤ ρ :=
  iSup_le fun s => iSup_le fun R => iSup_le fun hs => iSup_le fun ha => iSup_le fun m =>
    (MeasureTheory.measure_mono fun _ hc => hc.1).trans (hρ 0 (keys s) R hs ha m)

omit [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [AddGroup Y] in
/-- **A sum against a pushforward** is the sum against the law, the summand read at the image. -/
theorem tsum_map_mul {α β : Type} (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑' b, p.map g b * f b = ∑' a, p a * f (g a) := by
  classical
  simp_rw [PMF.map_apply, ENNReal.tsum_mul_right.symm]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  simp_rw [ite_mul, zero_mul]
  rw [tsum_ite_eq]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SC] [DecidableEq SC]
  [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [DecidableEq TB.Coins]
  [DecidableEq TB.KeyCoins] in
/-- **The unpredicted refusals of the empty predicate, averaged over the users' key coins, have rate
at most `n · ρ`** for a refusal rate `ρ` averaged over the honest key coins (`RefuseAvgWithin`): the
largest rate over the users is at most their sum, and each user's key coins are uniform. -/
theorem tsum_refusalGap_false_le {ρ : ℝ≥0∞} (hρ : B.RefuseAvgWithin adm ρ) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        refusalGap adm keys (fun _ _ _ _ => False) ≤ n * ρ := by
  classical
  set g : B.KeyCoins → ℝ≥0∞ := fun kc =>
    ⨆ (H : X → Y) (R : KeyRing B.PK N) (_ : B.pk kc ∈ R.1) (_ : adm R) (m : B.Msg),
      Pr[c ~ PMF.uniformOfFintype B.Coins :
        (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c).run H = none]
  have h1 : ∀ keys : Fin n → B.KeyCoins,
      refusalGap adm keys (fun _ _ _ _ => False) ≤ ∑ s, g (keys s) := fun keys =>
    iSup_le fun s => le_trans (iSup_le fun R => iSup_le fun hs => iSup_le fun ha => iSup_le fun m =>
      le_iSup_of_le (0 : X → Y) (le_iSup_of_le R (le_iSup_of_le hs (le_iSup_of_le ha
        (le_iSup_of_le m (MeasureTheory.measure_mono fun _ hc => hc.1))))))
      (Finset.single_le_sum (f := fun s => g (keys s)) (fun _ _ => zero_le) (Finset.mem_univ s))
  have h2 : ∀ s : Fin n, ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys * g (keys s) ≤ ρ :=
    fun s => by
      rw [← tsum_map_mul, PMF.uniformOfFintype_map_eval]
      exact hρ
  calc _ ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys * ∑ s, g (keys s) :=
        ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left (h1 keys) zero_le
    _ = ∑ s, ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys * g (keys s) := by
        rw [tsum_fintype]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [tsum_fintype]
    _ ≤ ∑ _s : Fin n, ρ := Finset.sum_le_sum fun s _ => h2 s
    _ = n * ρ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [Fintype SC] [DecidableEq SC] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [DecidableEq TB.Coins]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **A member's request that signs fails `drawOkR` with probability at most `ε` plus the unpredicted
refusal rate**: either its base signature exists and fails to verify (correctness error `ε`), or
the base signer refuses although `refuses` does not predict it. -/
theorem toOuterMeasure_signerIn_not_drawOkR_le {ε : ℝ≥0∞} (hcorr : B.CorrectWithin ε)
    (keys : Fin n → B.KeyCoins) (r : Req B PS adm n) :
    (PMF.uniformOfFintype B.Coins).toOuterMeasure
        {c | signerIn B (fun i => B.pk (keys i)) refuses c r ∧ ¬ drawOkR B keys c r} ≤
      ε + refusalGap adm keys refuses := by
  classical
  cases r with
  | corrupt i => simp [signerIn]
  | sideSign i bm => exact bm.elim
  | sign s R m =>
    by_cases hm : B.pk (keys s) ∈ R.1 ∧ adm R
    · refine (MeasureTheory.measure_mono fun c hc => ?_).trans
        ((MeasureTheory.measure_union_le _ _).trans (add_le_add
          (toOuterMeasure_not_drawOk_le hcorr keys (.sign s R m))
          (le_iSup_of_le s (le_iSup_of_le R (le_iSup_of_le hm.1 (le_iSup_of_le hm.2
            (le_iSup_of_le m le_rfl)))))))
      obtain ⟨hsg, hd⟩ := hc
      rcases hσ : bsigOf B keys c s R m with _ | σ
      · exact Or.inr ⟨hσ, hsg.2.2⟩
      · refine Or.inl fun hok => hd fun _ _ => ⟨σ, hσ, hok hm.1 hm.2 σ hσ⟩
    · refine le_of_eq_of_le ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2
        (Set.disjoint_left.2 fun c _ hc => hm ⟨hc.1.1, hc.1.2.1⟩)) zero_le

omit [Fintype SC] [DecidableEq SC] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] in
/-- **An event of the first coordinate of a uniform pair** has the first coordinate's
probability. -/
theorem toOuterMeasure_uniform_prod_fst {α β : Type} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] [DecidableEq α] [DecidableEq β] (p : α → Prop) :
    (PMF.uniformOfFintype (α × β)).toOuterMeasure {d | p d.1} =
      (PMF.uniformOfFintype α).toOuterMeasure {a | p a} := by
  have h : PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).map fun b => (a, b) := by
    ext ⟨a, b⟩
    rw [Ring.bind_map_pair_apply]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
    exact ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))
  rw [h]
  exact Ring.toOuterMeasure_bind_map_fst _ p

variable [Nonempty X] [DecidableEq Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof]

omit [Fintype SC] [DecidableEq SC] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]
  [Nonempty TB.KeyCoins] in
/-- **Replacing the game's replies by the checked ones costs at most `Q · ε`** at fixed keys, for a
base signer with correctness error `ε`: the two disagree on a request only when its base signature
fails to verify (`toOuterMeasure_not_drawOk_le`), and the request is fixed before its draw is read
(`Quantum.SplitChallenger.toOuterMeasure_outLaw_le_add'`). -/
theorem game_le_checked {ε : ℝ≥0∞} (hcorr : B.CorrectWithin ε) {O' : Type}
    {ksK : KindShape X Y (Req B PS adm n) (Resp B PS adm)} (K : KindAlg ksK O') (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (H : X → Y) (P : DReg K.W K.width X Y (Req B PS adm n) (Resp B PS adm) →
      LogReg (Req B PS adm n) K.slots → Prop) :
    ((K.composeBothOut ((ofBase B PS adm).gameSplit n (SideOracle.none _) keys Q).toChallenger
        id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs} ≤
      ((K.composeBothOut (checkedSplit PS adm keys Q).toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs} + Q * ε := by
  classical
  refine ((ofBase B PS adm).gameSplit n (SideOracle.none _) keys Q).toOuterMeasure_outLaw_le_add'
    _ _ (fun κ i r _ => ?_) K H fun a lg _ => P a lg
  refine le_trans (MeasureTheory.measure_mono fun d hd => ?_) ((toOuterMeasure_uniform_prod_fst
    (α := B.Coins) (β := PS.Coins) fun c => ¬ drawOk B keys c r).trans_le
      (toOuterMeasure_not_drawOk_le hcorr keys r))
  change ¬ drawOk B keys d.1 r
  intro h
  apply hd
  change _ = checkedReply keys d r
  unfold checkedReply
  rw [if_pos h]
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Nonempty B.BSig] [Nonempty X]
  [DecidableEq Y] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The simulated replies with the test `drawOkR` and without a test differ only on the bad
event**: on a draw where the request does not both sign (`signerIn`) and fail `drawOkR`, the two
replies are equal. -/
theorem simReply_eq_of_not_bad (keys : Fin n → B.KeyCoins)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ) (d : B.Coins × SC) (i : ℕ)
    (r : Req B PS adm n)
    (h : ¬ (signerIn B (fun i => B.pk (keys i)) refuses d.1 r ∧ ¬ drawOkR B keys d.1 r)) :
    simReply keys refuses pubOf Sim Q (drawOkR B keys) d i r =
      simReply keys refuses pubOf Sim Q (fun _ _ => True) d i r := by
  classical
  unfold simReply
  by_cases hs : signerIn B (fun i => B.pk (keys i)) refuses d.1 r
  · have hd : drawOkR B keys d.1 r := not_not.1 fun hd => h ⟨hs, hd⟩
    simp only [if_pos hs, if_pos hd, if_true]
  · simp only [if_neg hs]

omit [Nonempty B.BSig] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  [Nonempty TB.KeyCoins] in
/-- **Replacing the simulated replies with the test `drawOkR` by the replies without a test costs at
most `Q · (ε + refusalGap)`** at fixed keys, for a base signer with correctness error `ε`: the two
differ on a request only on the bad event of `simReply_eq_of_not_bad`, which has probability at
most `ε + refusalGap adm keys refuses` (`toOuterMeasure_signerIn_not_drawOkR_le`), and the request is
fixed before its draw is read. -/
theorem simChecked_le {ε : ℝ≥0∞} (hcorr : B.CorrectWithin ε) {O' : Type}
    {ksK : KindShape X Y (Req B PS adm n) (Resp B PS adm)} (K : KindAlg ksK O') (keys : Fin n → B.KeyCoins)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ) (H : X → Y)
    (P : DReg K.W K.width X Y (Req B PS adm n) (Resp B PS adm) → LogReg (Req B PS adm n) K.slots →
      (X → Y) → Prop) :
    ((K.composeBothOut (simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).toChallenger
        id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs (H.reprogram (K.postAss
          (simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).toChallenger v.chal))} ≤
      ((K.composeBothOut (simSplit PS adm keys refuses pubOf Sim Q fun _ _ => True).toChallenger
          id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs (H.reprogram (K.postAss
          (simSplit PS adm keys refuses pubOf Sim Q fun _ _ => True).toChallenger v.chal))} +
        Q * (ε + refusalGap adm keys refuses) := by
  classical
  refine (simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).toOuterMeasure_outLaw_le_add
    (simSplit PS adm keys refuses pubOf Sim Q fun _ _ => True).reply
    (simSplit PS adm keys refuses pubOf Sim Q fun _ _ => True).reply_queries
    (fun κ i r _ => ?_) K H fun a lg _ G => P a lg G
  refine le_trans (MeasureTheory.measure_mono fun d hd => ?_)
    ((Ring.toOuterMeasure_bind_map_fst (α := B.Coins) _ fun c =>
      signerIn B (fun i => B.pk (keys i)) refuses c r ∧ ¬ drawOkR B keys c r).trans_le
      (toOuterMeasure_signerIn_not_drawOkR_le hcorr keys r))
  change signerIn B (fun i => B.pk (keys i)) refuses d.1 r ∧ ¬ drawOkR B keys d.1 r
  by_contra h
  exact hd (simReply_eq_of_not_bad keys Sim Q d i r h)

/-! ### The games without a ring witness -/

omit [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **Without a ring witness, no request signs and verifies**: the relayed statement of a
ring-signing request by a member that signs and whose base signature exists and verifies is in the
ring relation (`mem_ringRel_of`). -/
theorem not_signerIn_and_drawOk (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf)
    (hempty : ∀ (x : RingStmt B) (w : RelayWit B), (x, w.toWit) ∉ ringRel B adm 0)
    (keys : Fin n → B.KeyCoins) {Q : ℕ} (c : B.Coins) {i : ℕ} (hi : i < Q)
    (r : Req B PS adm n) :
    ¬ (signerIn B (fun i => B.pk (keys i)) refuses c r ∧ drawOkR B keys c r) := fun h =>
  hempty _ _ (mem_ringRel_of (pubOf := pubOf) hB hpub 0 keys (fun _ : Fin Q => c) i r ⟨hi, h⟩)

omit [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] in
/-- **A checked reply to a request that does not both sign and verify runs to the refusing
reply**, for a base signer that refuses whenever `refuses` predicts it (`hsound`). -/
theorem run_checkedReply_of_not (hB : B.OracleFree) (hsound : B.RefusalSound refuses)
    (keys : Fin n → B.KeyCoins) (d : B.Coins × PS.Coins) {Q i : ℕ} (hi : i < Q)
    (r : Req B PS adm n)
    (hno : ¬ (signerIn B (fun i => B.pk (keys i)) refuses d.1 r ∧ drawOkR B keys d.1 r))
    (G : X → Y) :
    (checkedReply keys d r).run G =
      ⟨sideAnswer B (fun i => B.pk (keys i)) keys refuses pubOf (fun _ : Fin Q => d.1) i r none,
        []⟩ := by
  classical
  cases r with
  | corrupt j =>
    simp only [checkedReply, sideAnswer, dif_pos hi]
    rw [if_pos (show drawOk B keys d.1 (.corrupt j) from trivial)]
    rfl
  | sideSign j bm => exact bm.elim
  | sign s R m =>
    have hside : sideAnswer B (fun i => B.pk (keys i)) keys refuses pubOf (fun _ : Fin Q => d.1)
        i (.sign s R m) none = none := by
      simp only [sideAnswer, dif_pos hi]
      split_ifs <;> rfl
    rw [hside]
    unfold checkedReply
    split_ifs with hd
    · rw [run_unforgeReply_sign hB]
      split_ifs with hm
      · have hnone : bsigOf B keys d.1 s R m = none := by
          rcases hσ : bsigOf B keys d.1 s R m with _ | σ
          · rfl
          · refine absurd ⟨⟨hm.1, hm.2, fun hrf => ?_⟩, fun _ _ => ⟨σ, hσ, hd hm.1 hm.2 σ hσ⟩⟩ hno
            have h0 : bsigOf B keys d.1 s R m = none :=
              hsound 0 (keys s) R _ (List.getElem?_idxOf hm.1) m _ hrf
            rw [h0] at hσ
            cases hσ
        rw [hnone]
        rfl
      · rfl
    · rfl

omit [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **A simulated reply with the test `drawOkR` to a request that does not both sign and verify is
the refusing reply.** -/
theorem simReply_of_not (keys : Fin n → B.KeyCoins) (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC)
    (Q : ℕ) (d : B.Coins × SC) {i : ℕ} (hi : i < Q) (r : Req B PS adm n)
    (hno : ¬ (signerIn B (fun i => B.pk (keys i)) refuses d.1 r ∧ drawOkR B keys d.1 r)) :
    simReply keys refuses pubOf Sim Q (drawOkR B keys) d i r =
      .pure ⟨sideAnswer B (fun i => B.pk (keys i)) keys refuses pubOf (fun _ : Fin Q => d.1) i r
        none, []⟩ := by
  classical
  unfold simReply
  split_ifs with hs hd
  · exact absurd ⟨hs, hd⟩ hno
  · cases r with
    | corrupt j => exact hs.elim
    | sideSign j bm => exact bm.elim
    | sign s R m =>
      simp only [sideAnswer, dif_pos hi, if_pos hs]
      rfl
  · rfl

omit [Nonempty TB.KeyCoins] in
/-- **Without a ring witness, the checked game is the refusing game**: the replies run alike along
the projection of the draws to the signing coins, whose law is the refusing challenger's. -/
theorem checked_eq_refuse (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf)
    (hsound : B.RefusalSound refuses)
    (hempty : ∀ (x : RingStmt B) (w : RelayWit B), (x, w.toWit) ∉ ringRel B adm 0) {O' : Type}
    {ksK : KindShape X Y (Req B PS adm n) (Resp B PS adm)} (K : KindAlg ksK O') (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (H : X → Y) (P : DReg K.W K.width X Y (Req B PS adm n) (Resp B PS adm) →
      LogReg (Req B PS adm n) K.slots → Prop) :
    ((K.composeBothOut (checkedSplit PS adm keys Q).toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs} =
      ((K.composeBothOut (refuseSplit PS adm keys refuses pubOf Q).toChallenger id).outLaw
        H).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs} := by
  classical
  refine K.toOuterMeasure_outLaw_map (C := (checkedSplit PS adm keys Q).toChallenger)
    (C' := (refuseSplit PS adm keys refuses pubOf Q).toChallenger)
    (fun c : Unit × (Fin Q → B.Coins × PS.Coins) => (c.1, fun i => (c.2 (Fin.cast rfl i)).1))
    ((checkedSplit PS adm keys Q).map_coinLaw (refuseSplit PS adm keys refuses pubOf Q) Prod.fst
      rfl rfl ?_) rfl ?_ H P
  · change (PMF.uniformOfFintype (B.Coins × PS.Coins)).map Prod.fst = PMF.uniformOfFintype B.Coins
    exact PMF.map_fst_uniformOfFintype
  · intro c hist r G
    simp only [SplitChallenger.toChallenger, checkedSplit, SplitChallenger.withReply,
      refuseSplit]
    split_ifs with h h'
    · rw [run_checkedReply_of_not hB hsound keys _ h r
        (not_signerIn_and_drawOk hB hpub hempty keys _ h r) G]
      rfl
    all_goals first | rfl | contradiction | simp_all

omit [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Nonempty TB.KeyCoins] in
/-- **Without a ring witness, the simulated game with the test `drawOkR` is the refusing game**,
with the oracle unreprogrammed: its replies are the refusing replies, without assignments. -/
theorem simChecked_eq_refuse (hB : B.OracleFree) (hpub : B.PubOfCoins pubOf)
    (hempty : ∀ (x : RingStmt B) (w : RelayWit B), (x, w.toWit) ∉ ringRel B adm 0) {O' : Type}
    {ksK : KindShape X Y (Req B PS adm n) (Resp B PS adm)} (K : KindAlg ksK O') (keys : Fin n → B.KeyCoins)
    (Sim : NARG.Simulator X Y (RingStmt B) PS.Proof SC) (Q : ℕ) (H : X → Y)
    (P : DReg K.W K.width X Y (Req B PS adm n) (Resp B PS adm) → LogReg (Req B PS adm n) K.slots →
      (X → Y) → Prop) :
    ((K.composeBothOut (simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).toChallenger
        id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs (H.reprogram (K.postAss
          (simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).toChallenger v.chal))} =
      ((K.composeBothOut (refuseSplit PS adm keys refuses pubOf Q).toChallenger id).outLaw
        H).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs H} := by
  classical
  have hresp : ∀ c hist r, (simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).toChallenger.respond
      c hist r = (refuseSplit PS adm keys refuses pubOf Q).toChallenger.respond
        (c.1, fun i => (c.2 (Fin.cast rfl i)).1) hist r := by
    intro c hist r
    simp only [SplitChallenger.toChallenger, simSplit, refuseSplit]
    split_ifs with h h'
    · rw [simReply_of_not keys Sim Q _ h r (not_signerIn_and_drawOk hB hpub hempty keys _ h r)]
      rfl
    all_goals first | rfl | contradiction | simp_all
  have hnil : ∀ u, K.postAss (simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).toChallenger
      u = [] := K.postAss_eq_nil _ fun ω hist req ans => by
    simp only [Challenger.outWith, Challenger.outWithOf, hresp]
    simp only [SplitChallenger.toChallenger, refuseSplit]
    split_ifs <;> simp [OracleProgAns.result]
  have hr : H.reprogram [] = H := rfl
  simp only [hnil, hr]
  refine K.toOuterMeasure_outLaw_map
    (C := (simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).toChallenger)
    (C' := (refuseSplit PS adm keys refuses pubOf Q).toChallenger)
    (fun c : Unit × (Fin Q → B.Coins × SC) => (c.1, fun i => (c.2 (Fin.cast rfl i)).1))
    ((simSplit PS adm keys refuses pubOf Sim Q (drawOkR B keys)).map_coinLaw
      (refuseSplit PS adm keys refuses pubOf Q) Prod.fst rfl rfl ?_) rfl
    (fun c hist r G => congrArg (OracleProg.run G) (hresp c hist r)) H fun a lg => P a lg H
  change ((PMF.uniformOfFintype B.Coins).bind fun c => Sim.coins.map fun d => (c, d)).map
    Prod.fst = PMF.uniformOfFintype B.Coins
  rw [PMF.map_bind]
  simp [PMF.map_comp]

end Challengers

end Insider

end RingSignature

end GordieHowe
