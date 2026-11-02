-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerMUBound
public import GordieHowe.Model.Signature.MultiUserCount
public import GordieHowe.Model.Quantum.Interactive.MultiRelayLogs

@[expose] public section

/-!
# The multi-user forger asks at most `Q` signatures and corruptions on its winning branches

The bound `forgeProb_le_muEufProb` (`GordieHowe/Applications/Ring/RingForgerMUBound.lean`)
runs the multi-user forger `ringMUForger` against the challenger answering `Q'` requests, a number
fixed by the slot schedule. The challenger counts the forger's idle public-key requests too. This
file bounds the forgery probability by the probability that the forger wins with at most `Q`
signing and corruption requests (`Signature.muEufProbWithin`), under a count of the relayed
forger's logged requests (`RelayCountLE`) as an additional hypothesis.

- `RelayCountLE A F i₂ Q`: for every list of public keys and auxiliary value, sets of workspaces and
  absorbed logs of the relayed forger absorbed through `muTwoRelay` carried by its steps
  (`Quantum.AdaptiveIAlg.LogInv`), on whose last one the absorbed logs hold at most `Q` signing and
  corruption requests.
- `countP_requests_bridge_le`: under such sets, on every basis state of the simulated bridge, its
  logged requests hold at most `Q` signing and corruption requests.
- `simLaw_bridge_le_forgesReq_within`: `simLaw_bridge_le_forgesReq` with the count.
- `forgeProb_le_muEufProbWithin`: the forgery probability is at most the multi-user
  forger's success probability with at most `Q` signing and corruption requests plus the knowledge
  error, under `RelayCountLE`.
- `relayCountLE_of_K_one`: `RelayCountLE` holds for relays of one main request per request whose
  idle request is neither a signing nor a corruption request
  (`Quantum.AdaptiveIAlg.relayAdv_logs_le`).
- `forgeProb_le_muEufProbWithin_schedule`: the bound with `ringQ'` requests, for relays
  of one main request per request (no further hypothesis).
- `muLaw_ringMUForger_signCorruptCount`: on every branch, the multi-user forger asks at most `Q`
  signatures and corruptions (the event of more has probability `0`).
-/

namespace GordieHowe

open Quantum Signature RingSignature QROM IOP
open scoped ENNReal

variable {m k e N : ℕ} {TB : BaseTypes} {B : BaseSigner (Bits m) (XOut k e) N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n t : ℕ} [NeZero n]
  {SO : SideOracle (ofBase B PS adm)} {O : SignOracle B}
  {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}
  {rel : Set (RingStmt B × RingWit B)}
  {ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B)} {β : ℕ → ℝ≥0∞}

/-! ### The count of the relayed forger's requests -/

variable (B PS adm) in
/-- **The count of the relayed forger's logged requests**: for every list of public keys `pks` and
auxiliary value `p`, sets `T` of workspaces and absorbed logs of the relayed forger absorbed through
`muTwoRelay` at the key of user `0` with the empty table, carried by its steps (`LogInv`), whose
last one holds at most `Q` signing and corruption requests among the absorbed logs. -/
def RelayCountLE
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (i₂ : Fin n) (Q : ℕ) : Prop :=
  ∀ pks (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)), ∃ T,
    (ringRelAlg B PS adm A F pks Q p).LogInv (muTwoRelay O n (pks 0) i₂) (tab₀ _) T ∧
    ∀ x ∈ T ((ringRelAlg B PS adm A F pks Q p).slots +
        (ringRelAlg B PS adm A F pks Q p).post + 1),
      (Finset.univ.filter fun j => (x.2 j).any MURequest.isSignOrCorrupt = true).card ≤ Q

omit [DecidablePred adm] in
/-- **The bridge's logged requests hold at most `Qs` signing and corruption requests** on every
basis state of nonzero amplitude of its simulation, when sets carried by the absorbed adversary's
steps (`hT`) bound the count of its absorbed logs on the last one (`hTQ`). -/
theorem countP_requests_bridge_le (keys : Fin n → B.KeyCoins) (i₂ : Fin n)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} {A : AdaptiveIAlg shA (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))} (hA : A.TracePreserving)
    (C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit)
    (E : Expansion (Bits m) (Out k e) (ExtReg A C₁ (MURequest O n) (MUResponse B))) (kq : ℕ)
    (d₀ : ExtReg A C₁ (MURequest O n) (MUResponse B))
    {T : ℕ → Set ((A.W × MURequest O n) × LogReg (MURequest O n) A.slots)}
    (hT : A.LogInv (muRelayAt O keys i₂) (tab₀ A) T) {Qs : ℕ}
    (hTQ : ∀ x ∈ T (A.slots + A.post + 1),
      (Finset.univ.filter fun j => (x.2 j).any MURequest.isSignOrCorrupt = true).card ≤ Qs)
    (a : ℕ → MURequest O n → Option (MUResponse B)) {b}
    (hb : simState (outEquiv k e) ((bridgeAlg (outEquiv k e) A C₁
      (muRelayAt O keys i₂) (.publicKey 0) E kq d₀).inst a) b ≠ 0) :
    (requests b.1.1.2).countP MURequest.isSignOrCorrupt ≤ Qs := by
  obtain ⟨hTb, hlg⟩ := bridgeAlg_slotLogs (outEquiv k e) A C₁ (muRelayAt O keys i₂) (.publicKey 0)
    E kq d₀ hA hT a hb
  rw [countP_requests]
  refine (card_bridge_le A C₁ _ (.publicKey 0) b.1.1.2 _
    MURequest.isSignOrCorrupt rfl hlg).trans ?_
  simp only [isSignOrCorrupt_muTwoRelay_outer]
  exact hTQ _ hTb

/-- **The extraction's event on the bridge is a forgery with at most `Qs` signing and corruption
requests** (`simLaw_bridge_le_forgesReq` with the count of `countP_requests_bridge_le`). -/
theorem simLaw_bridge_le_forgesReq_within (hC : PS.CompiledBy V) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (H : Bits m → XOut k e)
    (hB : B.VerifiesWithoutOracle) (hrel : ∀ x w, (x, w) ∈ rel → RingRel B adm 0 x w) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} (A : AdaptiveIAlg shA (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))) (hA : A.TracePreserving)
    (hslots : A.slots ≤ Q')
    (C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit)
    (E : Expansion (Bits m) (Out k e)
      (ExtReg A C₁ (MURequest O n) (MUResponse B))) (kq : ℕ)
    (d₀ : ExtReg A C₁ (MURequest O n) (MUResponse B))
    (a : ℕ → MURequest O n → Option (MUResponse B))
    {T : ℕ → Set ((A.W × MURequest O n) × LogReg (MURequest O n) A.slots)}
    (hT : A.LogInv (muRelayAt O keys i₂) (tab₀ A) T) {Qs : ℕ}
    (hTQ : ∀ x ∈ T (A.slots + A.post + 1),
      (Finset.univ.filter fun j => (x.2 j).any MURequest.isSignOrCorrupt = true).card ≤ Qs) :
    simLaw (outEquiv k e) ((bridgeAlg (outEquiv k e) A C₁ (muRelayAt O keys i₂)
        (.publicKey 0) E kq d₀).inst a)
        {p | extTest B PS hC c₀ keys Q' p.1.out ∧
          NARG.ExtractsAt rel (fun x D => (ext x D : Multiset (RingWit B)))
        (V.stmt (ringClaim B PS hC c₀ (extForgery p.1.out))) p.2} ≤
      bornWeight (simState (outEquiv k e) ((bridgeAlg (outEquiv k e) A C₁
          (muRelayAt O keys i₂) (.publicKey 0) E kq d₀).inst a))
        {b | ForgesReq keys H (muReadout B PS adm hC c₀ ext f₀
          ((bridgeAlg (outEquiv k e) A C₁ (muRelayAt O keys i₂) (.publicKey 0) E
            kq d₀).out b.1.1.1, slotsDB (outEquiv k e) b.2)) (requests b.1.1.2) ∧
          (requests b.1.1.2).countP MURequest.isSignOrCorrupt ≤ Qs} :=
  (simLaw_bridge_le_forgesReq hC c₀ f₀ keys i₂ (B.pk (keys 0)) H hB hrel Q' A hslots C₁ E kq d₀ a
    (bridgeLogsAt_of_tracePreserving (outEquiv k e) hA _ _ _ _ _ _ _)).trans
    (bornWeight_mono_of_support _ fun _ hb hF =>
      ⟨hF, countP_requests_bridge_le keys i₂ hA C₁ E kq d₀ hT hTQ a hb⟩)

/-! ### The bound -/

/-- **The unforgeability game of `ofBase B PS adm` from MU-EUF-CMA^corr with at most `Q` signing and
corruption requests, under the count** (`forgeProb_le_muEufProb`
with `RelayCountLE`): the forgery probability of an adversary with at most `t` queries and `Q`
requests is at most the probability that the multi-user forger `ringMUForger`, against the
challenger answering `Q'` requests, wins with at most `Q` signing and corruption requests, plus the
knowledge error at `t + Q · qR + kq` queries. -/
theorem forgeProb_le_muEufProbWithin (hO : O.NoQuery)
    (hC : PS.CompiledBy V) (hB : B.VerifiesWithoutOracle)
    (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B))) β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) {qR : ℕ} (hqR : ∀ pks, (F pks).qR ≤ qR)
    {i₂ : Fin n} (hi₂ : i₂ ≠ 0) (Q Q' : ℕ) (hgame : ThroughRelay B PS adm A F Q Q')
    (hdepth : ∀ pks p, ringBridgeDepth B PS adm V A F pks i₂ Q Q' p + 1 ≤ Q')
    (hslots : ∀ pks p, (ringRelAlg B PS adm A F pks Q p).slots ≤ Q') (hcount : RelayCountLE B PS adm A F i₂ Q) :
    forgeProb A Q ≤
      muEufProbWithin (ringMUForger B PS adm hC c₀ ext f₀ A F i₂ Q Q') Q' Q +
      V.knowledgeError β (t + Q * qR + V.kq) := by
  refine (forgeProb_le_extRun hO hC K c₀ A F hqR i₂ Q Q' hgame).trans (add_le_add ?_ le_rfl)
  rw [ringMUForger, muEufProbWithin_coSimMU _ _ hO _ _ _ _ _ _ _ _ hdepth]
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
  -- the extraction's event on the bridge is a forgery for the logged requests, within the count
  obtain ⟨T, hT, hTQ⟩ := hcount (fun i => B.pk (keys i)) (a, ρ)
  have h := simLaw_bridge_le_forgesReq_within (rel := rel) (ext := ext) hC c₀ f₀ keys i₂ H
    hB (fun x w h => hrel x w h 0) Q' (relAlg B PS adm A F keys Q ρ a)
    ((relayedForgerVia A (F (fun i => B.pk (keys i))) (fun i => B.pk (keys i)) Q
        ρ).tracePreserving a) (hslots _ (a, ρ))
    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
    (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
    (relDefault B PS adm A F keys i₂ Q Q' ρ a) (muReplyAfter O keys Q' c) hT hTQ
  convert h using 1

/-- **The Born weight of a set missing the support is `0`.** -/
theorem bornWeight_eq_zero_of_support {ι : Type*} [Fintype ι] {v : QState ι} {S : Set ι}
    (h : ∀ i, v i ≠ 0 → i ∉ S) : bornWeight v S = 0 :=
  le_antisymm ((bornWeight_mono_of_support v (S' := ∅) fun i hv hS => absurd hS (h i hv)).trans
    (MeasureTheory.measure_empty (μ := bornWeight v)).le) bot_le

/-! ### The count for relays of one main request per request -/

/-- **The count holds for relays of one main request per request** whose idle request is neither a
signing nor a corruption request (`Quantum.AdaptiveIAlg.relayAdv_logs_le` with `K = 1`). -/
theorem relayCountLE_of_K_one (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O)
    (hK : ∀ pks, (F pks).K = 1) (hidle : ∀ pks, (F pks).idle.isSignOrCorrupt = false)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (i₂ : Fin n) (Q : ℕ) : RelayCountLE B PS adm A F i₂ Q := by
  intro pks p
  have key : ∀ {shB' : AlgShape (Bits m) (XOut k e) (NumReq B PS adm n SO) (RResp B PS adm SO)} (B' : AdaptiveIAlg shB' (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))),
      ∃ T, (B'.relayAdv (F pks) Q (B'.relayOut (F pks))).LogInv (muTwoRelay O n (pks 0) i₂)
          (tab₀ _) T ∧
        ∀ x ∈ T ((B'.relayAdv (F pks) Q (B'.relayOut (F pks))).slots +
          (B'.relayAdv (F pks) Q (B'.relayOut (F pks))).post + 1),
          (Finset.univ.filter fun j => (x.2 j).any MURequest.isSignOrCorrupt = true).card ≤ Q :=
    fun B' => by
      obtain ⟨T, hT, hTQ⟩ := AdaptiveIAlg.relayAdv_logs_le B' (F pks) Q (B'.relayOut (F pks))
        MURequest.isSignOrCorrupt (muTwoRelay O n (pks 0) i₂) (tab₀ _) rfl (hidle pks)
      exact ⟨T, hT, fun x hx => (hTQ x hx).trans (by rw [hK pks, one_mul])⟩
  simp only [ringRelAlg, relayedForgerVia, QueryBoundedAdversary.mono,
    QueryBoundedAdversary.relay]
  exact key _

/-- **The unforgeability game of `ofBase B PS adm` from MU-EUF-CMA^corr with `ringQ'` requests, at
most `Q` of them signing or corruption requests on the winning branches**
(`forgeProb_le_muEufProbWithin` with the schedule bound of
`forgeProb_le_muEufProb_schedule`), for relays of one main request per request whose
idle request is neither a signing nor a corruption request. -/
theorem forgeProb_le_muEufProbWithin_schedule (hO : O.NoQuery)
    (hC : PS.CompiledBy V) (hB : B.VerifiesWithoutOracle)
    (K : V.KnowledgeBound rel (fun x D => (ext x D : Multiset (RingWit B))) β)
    (hrel : ∀ x w, (x, w) ∈ rel → ∀ H, RingRel B adm H x w) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (hK : ∀ pks, (F pks).K = 1)
    (hidle : ∀ pks, (F pks).idle.isSignOrCorrupt = false) {qR L : ℕ}
    (hqR : ∀ pks, (F pks).qR ≤ qR) (hL : ∀ pks, (F pks).len ≤ L) {i₂ : Fin n} (hi₂ : i₂ ≠ 0)
    (Q : ℕ) (hgame : ThroughRelay B PS adm A F Q (ringQ' V Q S w P L)) :
    forgeProb A Q ≤
      muEufProbWithin (ringMUForger B PS adm hC c₀ ext f₀ A F i₂ Q (ringQ' V Q S w P L))
        (ringQ' V Q S w P L) Q +
      V.knowledgeError β (t + Q * qR + V.kq) :=
  forgeProb_le_muEufProbWithin hO hC hB K hrel c₀ f₀ A F hqR hi₂ Q _ hgame
    (fun pks p => ringBridgeDepth_add_one_le hS F hL pks i₂ Q _ p)
    (fun pks p => ringRelAlg_slots_le hS F hL pks Q p)
    (relayCountLE_of_K_one F hK hidle A i₂ Q)

/-- **The simulated bridge holds at most `Q` logged signing and corruption requests**: the Born
weight of the outcomes with more is `0`, for relays of one main request per request whose idle
request is neither a signing nor a corruption request. -/
theorem bornWeight_ringBridgeAlg_count (hC : PS.CompiledBy V) (c₀ : Cl)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (hK : ∀ pks, (F pks).K = 1)
    (hidle : ∀ pks, (F pks).idle.isSignOrCorrupt = false) (i₂ : Fin n) (Q Q' : ℕ)
    (keys : Fin n → B.KeyCoins) (a : (A (fun i => B.pk (keys i), ())).Aux × (Fin Q → PS.Coins))
    (c : Fin Q' → O.Coins) :
    bornWeight (simState (outEquiv k e) ((ringBridgeAlg B PS adm hC c₀ A F
        (fun i => B.pk (keys i)) i₂ Q Q' a).inst (muReplyAfter O keys Q' c)))
      {b | Q < (requests b.1.1.2).countP MURequest.isSignOrCorrupt} = 0 := by
  obtain ⟨T, hT, hTQ⟩ := relayCountLE_of_K_one F hK hidle A i₂ Q (fun i => B.pk (keys i)) a
  have hcount : ∀ b, simState (outEquiv k e) ((ringBridgeAlg B PS adm hC c₀ A F
      (fun i => B.pk (keys i)) i₂ Q Q' a).inst (muReplyAfter O keys Q' c)) b ≠ 0 →
      (requests b.1.1.2).countP MURequest.isSignOrCorrupt ≤ Q := fun b hb => by
    -- TODO(unbundle-M4): as in `ringBridgeAlg`, match the bridge's depth at reducible transparency
    have hTP := (relayedForgerVia A (F (fun i => B.pk (keys i))) (fun i => B.pk (keys i)) Q
      a.2).tracePreserving a.1
    with_reducible
      exact countP_requests_bridge_le keys i₂
        (A := ringRelAlg B PS adm A F (fun i => B.pk (keys i)) Q a) hTP
        (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
        (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
        (ringDefault B PS adm A F (fun i => B.pk (keys i)) i₂ Q Q' a) hT hTQ
        (muReplyAfter O keys Q' c) hb
  exact bornWeight_eq_zero_of_support fun b hb hlt => absurd hlt (not_lt.2 (hcount b hb))


/-- **On every branch, the multi-user forger asks at most `Q` signatures and corruptions**: for a
signing oracle without queries, relays of one main request per request whose idle request is
neither a signing nor a corruption request, and `Q'` at least the bridge's request points, the
probability that the forger `ringMUForger` terminates with a history holding more than `Q` signing
and corruption requests is `0`, against the challenger answering `Q'` requests. -/
theorem muLaw_ringMUForger_signCorruptCount (hO : O.NoQuery) (hC : PS.CompiledBy V) (c₀ : Cl)
    (f₀ : B.PK × B.BMsg × B.BSig)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (hK : ∀ pks, (F pks).K = 1)
    (hidle : ∀ pks, (F pks).idle.isSignOrCorrupt = false) (i₂ : Fin n) (Q Q' : ℕ)
    (hdepth : ∀ pks p, ringBridgeDepth B PS adm V A F pks i₂ Q Q' p + 1 ≤ Q') :
    (muLaw (ringMUForger B PS adm hC c₀ ext f₀ A F i₂ Q Q') Q').toOuterMeasure
      {x | ∃ p ∈ x.2.2, Q < signCorruptCount p.2} = 0 := by
  rw [ringMUForger, toOuterMeasure_muLaw_coSimMU_count _ _ hO _ _ _ _ _ _ _ _ hdepth]
  refine ENNReal.tsum_eq_zero.2 fun keys => mul_eq_zero_of_right _
    (ENNReal.tsum_eq_zero.2 fun H => mul_eq_zero_of_right _
      (ENNReal.tsum_eq_zero.2 fun a => mul_eq_zero_of_right _
        (Finset.sum_eq_zero fun c _ => mul_eq_zero_of_right _ ?_)))
  have h := bornWeight_ringBridgeAlg_count hC c₀ A F hK hidle i₂ Q Q' keys a c
  convert h using 1

end GordieHowe
