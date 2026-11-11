-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerWin
public import GordieHowe.Model.RingSignature.Schedule
public import GordieHowe.Model.RingSignature.UserEmbed

@[expose] public section

/-!
# The unforgeability game of `ofBase B PS adm` from MU-EUF-CMA^corr

The multi-user forger of the reduction and the bound on the forgery probability of the
unforgeability game of `ofBase B PS adm` with a side oracle `SO` by its success probability in
MU-EUF-CMA^corr with a signing oracle `O` without queries, for a game that passes through the
relayed forger of a relay family `F` (`ThroughRelay`). The bridge statement is
`Quantum.extBridge` and the logs statement `bridgeLogsAt_of_tracePreserving`. The instances are in
`GordieHowe/Applications/Ring/RingForgerGames.lean`.

- `ringAux`: the forger's auxiliary input, the adversary's and the prover's coins.
- `ringBridgeAlg`, `ringBridgeDepth`: the bridge of the relayed forger and its number of request
  points less one.
- `ringMUForger`: the multi-user forger (`Signature.coSimMU` of the bridge, read by `muReadout`).
- `forgeProb_le_muEufProb`: the forgery probability is at most the multi-user forger's
  success probability plus the knowledge error.
- `ringRelAlg_slots`, `ringBridgeDepth_eq`, `ringQ'`, `ringBridgeDepth_add_one_le`,
  `ringRelAlg_slots_le`: the number of requests from a schedule bound.
- `ringMUForger_slots_le`: the multi-user forger sends at most `(S + P) · max w L + kq + 1`
  requests.
- `forgeProb_le_muEufProb_schedule`: the bound with `ringQ'` requests.
-/

namespace GordieHowe

open Quantum Signature RingSignature QROM IOP
open scoped ENNReal

variable {m k e N : ℕ} {TB : BaseTypes} [DecidableEq TB.PK]
  {B : BaseSigner (Bits m) (XOut k e) N TB}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n t : ℕ} [NeZero n]
  {SO : SideOracle (ofBase B PS adm)} {O : SignOracle B.core}
  {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}
  {rel : Set (RingStmt B × RingWit B)}
  {ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B)} {β : ℕ → ℝ≥0∞}

/-! ### The multi-user forger -/

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] [Fintype SO.BMsg] [DecidableEq SO.BMsg] [Fintype SO.BSig] [DecidableEq SO.BSig]

variable [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins]

variable (B PS adm) in
/-- **The multi-user forger's auxiliary input**: the adversary's auxiliary input on the public keys
and uniform prover's coins for `Q` requests. -/
noncomputable def ringAux
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (Q : ℕ) (pks : Fin n → B.PK) : PMF ((A (pks, ())).Aux × (Fin Q → PS.Coins)) :=
  (A (pks, ())).aux.bind fun a => (PMF.uniformOfFintype (Fin Q → PS.Coins)).map fun ρ => (a, ρ)

omit [NeZero n] [DecidableEq TPS.Coins] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The auxiliary input is the product of the adversary's and the uniform coins.** -/
theorem ringAux_apply
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (Q : ℕ) (pks : Fin n → B.PK) (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :
    ringAux B PS adm A Q pks p =
      (A (pks, ())).aux p.1 * PMF.uniformOfFintype (Fin Q → PS.Coins) p.2 := by
  classical
  rw [ringAux, PMF.bind_apply, tsum_eq_single p.1 fun a ha => ?_]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single p.2 fun ρ hρ => ?_]
    · simp
    · simp only [ite_eq_right_iff]
      intro h
      exact absurd (congrArg Prod.snd h) (Ne.symm hρ)
  · rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.2 fun ρ => ?_)
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (congrArg Prod.fst h) (Ne.symm ha)

variable (B PS adm) in
/-- **The number of request points of the bridge, less one**: the depth of the relayed forger's
composition, holding the empty table, with the inert challenger, plus the verifier's `kq`
queries. -/
noncomputable abbrev ringBridgeDepth (V : NARG.QROM.Verifier m k e Cl (RingStmt B))
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (pks : Fin n → B.PK) (i₂ : Fin n)
    (Q Q' : ℕ) (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) : ℕ :=
  (((ringRelAlg B PS adm A F pks Q p).absorbTab (muTwoRelay O n (pks 0) i₂)
    (tab₀ (ringRelAlg B PS adm A F pks Q p))).toTPKindAlg.composeBothOut
    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).depth + V.kq

variable (B PS adm) in
/-- **The bridge of the relayed forger** (`Quantum.bridgeAlg`) on the public keys: through the
relay `muTwoRelay` at the key of user `0`, with the dummy `publicKey 0`, the expansion by the
compiled verifier's queries on the forgery's claim, and the default output of the run holding the
empty table. -/
noncomputable abbrev ringBridgeAlg (hC : PS.CompiledBy V) (c₀ : Cl)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (pks : Fin n → B.PK) (i₂ : Fin n)
    (Q Q' : ℕ) (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :
    ReqQueryAlg (Bits m) (XOut k e) (MURequest O n) (MUResponse B.core)
      (ringBridgeDepth B PS adm V A F pks i₂ Q Q' p)
      (BaseGame.Tuple (Bits m) (Out k e)
        (ExtReg (ringRelAlg B PS adm A F pks Q p)
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
          (MURequest O n) (MUResponse B.core)) V.kq) := by
  -- TODO(unbundle-M4): at default transparency, matching `ringBridgeDepth` against the bridge's
  -- depth unfolds `Nat.add` into the relayed forger's shape; the abbrev unfolds at reducible
  -- transparency
  with_reducible
    exact bridgeAlg (outEquiv k e) (ringRelAlg B PS adm A F pks Q p)
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
      (muTwoRelay O n (pks 0) i₂) (.publicKey 0)
      (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
      (ringDefault B PS adm A F pks i₂ Q Q' p)

variable (B PS adm) in
/-- **The multi-user forger of the reduction** (`Signature.coSimMU`): on the public keys it draws
the adversary's auxiliary input and the prover's coins (`ringAux`), runs the compressed-oracle
simulation of the bridge of the relayed forger with its request points sent to the multi-user
challenger, and outputs the forgery read from the output and the measured database
(`muReadout`, `f₀` if no extracted witness is one of the ring relation at the zero oracle). -/
noncomputable def ringMUForger (hC : PS.CompiledBy V) (c₀ : Cl)
    (ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B))
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (i₂ : Fin n) (Q Q' : ℕ) :
    MUAdversary O n (OracleView.queriesOnly (Bits m) (XOut k e)) 0 :=
  coSimMU O (outEquiv k e)
    (fun pks => (A (pks, ())).Aux × (Fin Q → PS.Coins)) (ringAux B PS adm A Q)
    (fun pks p => ringBridgeDepth B PS adm V A F pks i₂ Q Q' p)
    (fun pks p => BaseGame.Tuple (Bits m) (Out k e)
      (ExtReg (ringRelAlg B PS adm A F pks Q p)
        (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
        (MURequest O n) (MUResponse B.core)) V.kq)
    (fun pks p => ringBridgeAlg B PS adm hC c₀ A F pks i₂ Q Q' p)
    (fun _ _ => muReadout B PS adm hC c₀ ext f₀)

/-- **The query count of a composition with an output**: as `composeBoth_depth`. -/
theorem _root_.GordieHowe.Quantum.KindAlg.composeBothOut_depth {X Y Req Resp O O' : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
    [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y]
    {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O) (C : Challenger X Y Req Resp) (f : A.CW C → O') :
    (A.composeBothOut C f).depth = A.slots * (C.q + A.width) + A.width * A.post :=
  A.composeBoth_depth C

omit [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]
  [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The bridge's request points less one**: the relayed forger's slots plus `kq`. -/
theorem ringBridgeDepth_eq
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (pks : Fin n → B.PK) (i₂ : Fin n)
    (Q Q' : ℕ) (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :
    ringBridgeDepth B PS adm V A F pks i₂ Q Q' p =
      (ringRelAlg B PS adm A F pks Q p).slots + V.kq := by
  rw [ringBridgeDepth, KindAlg.composeBothOut_depth]
  change _ * (0 + 1) + 1 * 0 + V.kq = _
  rw [Nat.zero_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero]

/-! ### The bound -/

/-- **The unforgeability game of `ofBase B PS adm` from MU-EUF-CMA^corr**: for a game through the
relayed forger of `F` (`hgame`) with a signing oracle without queries (`hO`) and relays of at most
`qR` queries per request (`hqR`), a proof system given by a compiled verifier `V` (`hC`) with a
knowledge bound for `rel` at `ext` and `β` (`K`), every witness of `rel` one of the ring relation at
every oracle (`hrel`), `i₂ ≠ 0`, `Q'` requests at least the bridge's request points (`hdepth`) and
the relayed forger's slots (`hslots`), the forgery probability of an adversary with at most `t`
queries and `Q` requests is at most the success probability of the multi-user forger `ringMUForger`
in MU-EUF-CMA^corr with `Q'` requests, plus the knowledge error at `t + Q · qR + kq` queries. -/
theorem forgeProb_le_muEufProb (hO : O.NoQuery)
    (hC : PS.CompiledBy V) (hB : B.VerifiesWithoutOracle)
    (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B))) β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) {qR : ℕ} (hqR : ∀ pks, (F pks).qR ≤ qR)
    {i₂ : Fin n} (hi₂ : i₂ ≠ 0) (Q Q' : ℕ) (hgame : ThroughRelay B PS adm A F Q Q')
    (hdepth : ∀ pks p, ringBridgeDepth B PS adm V A F pks i₂ Q Q' p + 1 ≤ Q')
    (hslots : ∀ pks p, (ringRelAlg B PS adm A F pks Q p).slots ≤ Q') :
    forgeProb A Q ≤ muEufProb (ringMUForger B PS adm hC c₀ ext f₀ A F i₂ Q Q') Q' +
      V.knowledgeError β (t + Q * qR + V.kq) := by
  refine (forgeProb_le_extRun hO hC K c₀ A F hqR i₂ Q Q' hgame).trans (add_le_add ?_ le_rfl)
  rw [ringMUForger, muEufProb_coSimMU _ _ hO _ _ _ _ _ _ _ hdepth]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl ?_
  -- the extraction runs as the bridge against the multi-user challenger
  have hL : ∀ ρ a, _ := fun ρ a => sum_simProb_extRun_eq_bridge hC c₀ A F keys hi₂ Q Q' ρ a
    (by
      have h := hdepth (fun i => B.pk (keys i)) (a, ρ)
      rw [ringBridgeDepth_eq] at h
      rw [KindAlg.composeBothOut_depth]
      change (ringRelAlg B PS adm A F (fun i => B.pk (keys i)) Q (a, ρ)).slots * (0 + 1) + 1 * 0 +
        V.kq + 1 ≤ Q'
      rw [Nat.zero_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      exact h)
    (fun v D => extTest B PS hC c₀ keys Q' v ∧
      NARG.ExtractsAt rel (fun x D => (ext x D : Multiset (RingWit B)))
        (V.stmt (ringClaim B PS hC c₀ (extForgery v))) D)
  simp only [hL]
  -- the oracle's average outside
  rw [← one_mul (∑ ρ, _), ← PMF.tsum_coe (PMF.uniformOfFintype (Bits m → XOut k e)),
    ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_
  -- the auxiliary input as a pair, the prover's coins outside
  rw [← tsum_fintype (L := .unconditional _)
    (f := fun ρ => PMF.uniformOfFintype (Fin Q → PS.Coins) ρ * _), ENNReal.tsum_prod',
    ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun ρ => ?_
  simp only [ringAux_apply]
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_assoc, mul_comm (PMF.uniformOfFintype (Fin Q → PS.Coins) ρ)]
  refine mul_le_mul' le_rfl ?_
  refine Finset.sum_le_sum fun c _ => mul_le_mul' le_rfl ?_
  -- the extraction's event on the bridge is a forgery for the logged requests
  have hTP : (relAlg B PS adm A F keys Q ρ a).TracePreserving :=
    (relayedForgerVia A (F (fun i => B.pk (keys i))) (fun i => B.pk (keys i)) Q ρ).tracePreserving a
  have h := simLaw_bridge_le_forgesReq (rel := rel) (ext := ext) hC c₀ f₀ keys i₂
    (B.pk (keys 0)) H
    hB (fun x w h => hrel x w h 0) Q' (relAlg B PS adm A F keys Q ρ a) (hslots _ (a, ρ))
    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
    (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
    (relDefault B PS adm A F keys i₂ Q Q' ρ a) (muReplyAfter O keys Q' c)
    (bridgeLogsAt_of_tracePreserving (outEquiv k e) hTP
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂) (.publicKey 0)
      (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
      (relDefault B PS adm A F keys i₂ Q Q' ρ a) (muReplyAfter O keys Q' c))
  convert h using 1

/-! ### The number of requests from a schedule bound -/

omit [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]
  [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The slots of the relayed forger**: the adversary's slots and post batches, each split into
at most `max width F.len` single steps (`Distinguisher.relaySlots`). -/
theorem ringRelAlg_slots
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (pks : Fin n → B.PK) (Q : ℕ)
    (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :
    (ringRelAlg B PS adm A F pks Q p).slots =
      (((A (pks, ())).alg p.1).slots + ((A (pks, ())).alg p.1).post) *
        max ((A (pks, ())).alg p.1).width (F pks).len :=
  rfl

/-- **The number of multi-user requests of the reduction** for an adversary with `Q` requests and
the schedule bound `S`, `w`, `P` (`GameAdversary.ScheduleLE`), relays of length at most `L`: at
least `Q`, and at least the bridge's request points `(S + P) · max w L + kq + 1`. -/
def ringQ' (V : NARG.QROM.Verifier m k e Cl (RingStmt B)) (Q S w P L : ℕ) : ℕ :=
  max Q ((S + P) * max w L + V.kq + 1)

omit [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]
  [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The bridge's request points are at most `ringQ'`** under a schedule bound. -/
theorem ringBridgeDepth_add_one_le
    {A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t}
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) {L : ℕ} (hL : ∀ pks, (F pks).len ≤ L)
    (pks : Fin n → B.PK) (i₂ : Fin n) (Q Q' : ℕ) (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :
    ringBridgeDepth B PS adm V A F pks i₂ Q Q' p + 1 ≤ ringQ' V Q S w P L := by
  rw [ringBridgeDepth_eq, ringRelAlg_slots, ringQ']
  refine le_max_of_le_right (Nat.add_le_add_right (Nat.add_le_add_right ?_ _) _)
  exact Nat.mul_le_mul (Nat.add_le_add (hS.slots_le _ p.1) (hS.post_le _ p.1))
    (max_le_max (hS.width_le _ p.1) (hL pks))

omit [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The relayed forger's slots are at most `ringQ'`** under a schedule bound. -/
theorem ringRelAlg_slots_le
    {A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t}
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) {L : ℕ} (hL : ∀ pks, (F pks).len ≤ L)
    (pks : Fin n → B.PK) (Q : ℕ) (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :
    (ringRelAlg B PS adm A F pks Q p).slots ≤ ringQ' V Q S w P L := by
  have h := ringBridgeDepth_add_one_le (V := V) hS F hL pks 0 Q 0 p
  rw [ringBridgeDepth_eq] at h
  omega

omit [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]
  [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The multi-user forger's requests** (the trivial count): on every start input and auxiliary
value, its algorithm has `ringBridgeDepth + 1` slots, each a request, so it sends at most
`(S + P) · max w L + kq + 1` multi-user requests (signing requests among them) under a schedule
bound. -/
theorem ringMUForger_slots_le (hC : PS.CompiledBy V) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    {A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t}
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) {L : ℕ} (hL : ∀ pks, (F pks).len ≤ L)
    (i₂ : Fin n) (Q Q' : ℕ) (pks : Fin n → B.PK)
    (tab : (OracleView.queriesOnly (Bits m) (XOut k e)).Tab)
    (a : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :
    ((ringMUForger B PS adm hC c₀ ext f₀ A F i₂ Q Q' (pks, tab)).alg a).slots ≤
      (S + P) * max w L + V.kq + 1 := by
  have hs : ((ringMUForger B PS adm hC c₀ ext f₀ A F i₂ Q Q' (pks, tab)).alg a).slots =
      ringBridgeDepth B PS adm V A F pks i₂ Q Q' a + 1 :=
    by
      simp only [ringMUForger, Signature.coSimMU]
      -- TODO(unbundle-M4): as in `ringBridgeAlg`, match the depth at reducible transparency
      with_reducible exact ReqQueryAlg.coSimAdv_slots (outEquiv k e)
  rw [hs, ringBridgeDepth_eq, ringRelAlg_slots]
  refine Nat.add_le_add_right (Nat.add_le_add_right ?_ _) _
  exact Nat.mul_le_mul (Nat.add_le_add (hS.slots_le _ a.1) (hS.post_le _ a.1))
    (max_le_max (hS.width_le _ a.1) (hL pks))

/-- **The unforgeability game of `ofBase B PS adm` from MU-EUF-CMA^corr with `ringQ'` requests**
(`forgeProb_le_muEufProb`): for an adversary with the
schedule bound `S`, `w`, `P` (`hS`) and relays of length at most `L` (`hL`), the multi-user game
with `max Q ((S + P) · max w L + kq + 1)` requests. -/
theorem forgeProb_le_muEufProb_schedule (hO : O.NoQuery)
    (hC : PS.CompiledBy V) (hB : B.VerifiesWithoutOracle)
    (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B))) β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) {qR L : ℕ} (hqR : ∀ pks, (F pks).qR ≤ qR)
    (hL : ∀ pks, (F pks).len ≤ L) {i₂ : Fin n} (hi₂ : i₂ ≠ 0) (Q : ℕ)
    (hgame : ThroughRelay B PS adm A F Q (ringQ' V Q S w P L)) :
    forgeProb A Q ≤
      muEufProb (ringMUForger B PS adm hC c₀ ext f₀ A F i₂ Q (ringQ' V Q S w P L))
        (ringQ' V Q S w P L) +
      V.knowledgeError β (t + Q * qR + V.kq) :=
  forgeProb_le_muEufProb hO hC hB K hrel c₀ f₀ A F hqR hi₂ Q _ hgame
    (fun pks p => ringBridgeDepth_add_one_le hS F hL pks i₂ Q _ p)
    (fun pks p => ringRelAlg_slots_le hS F hL pks Q p)

end GordieHowe
