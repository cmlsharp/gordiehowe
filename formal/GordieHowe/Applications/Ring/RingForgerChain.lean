-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerBridge

@[expose] public section

/-!
# From the unforgeability game to the extraction runs of the table form

The reduction from the unforgeability game of `ofBase B PS adm` with a side oracle `SO`, through
the relayed forger of a relay family `F` to the multi-user challenger with a signing oracle `O`
without queries (`ThroughRelay`), up to the extraction: the game's forgery probability is at most
the average, over the users' key coins, the prover's coins, the adversary's auxiliary input
and the multi-user challenger's coins `ω`, of the probability that the extraction run of the
relayed forger holding the table of the challenger's replies at `ω` (`Quantum.extRun`) extracts,
from the measured database, a witness for a forgery fresh for its multi-user requests, plus the
knowledge error.

- `extForgery`, `extLogs`: the relayed forger's output and logs in the extraction run's
  registers.
  `ringClaim`: the compiled verifier's claim of a ring signature.
- `transcriptLaw_relayedForger_eq`: the relayed forger's transcripts against the multi-user
  challenger as runs of the table form against the inert challenger.
- `extTest`, `tsum_le_extRun`: the knowledge step at one table.
- `ringRelAlg`, `relAlg`, `ringDefault`, `relDefault`: the relayed forger and its extraction
  run's default output, on the public keys and at the users' key coins.
- `ThroughRelay`, `forgeProb_le_extRun`: the game through the relayed forger, and the chain from
  the game to the extraction runs.
- `sum_simProb_extRun_eq_bridge`: by the bridge statement (`Quantum.extBridge`), the extraction
  runs at the challenger's tables as the bridge against the multi-user challenger.
-/

namespace GordieHowe

open Quantum Signature RingSignature QROM IOP
open scoped ENNReal

variable {m k e N : ℕ} {TB : BaseTypes} {B : BaseSigner (Bits m) (XOut k e) N TB}
  {TPS : PSTypes} {PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n t : ℕ} [NeZero n]
  {SO : SideOracle (ofBase B PS adm)} {O : SignOracle B}

/-! ### The registers of the extraction run -/

section Regs

variable {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁]
  [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  [Inhabited Req₁] {shA : AlgShape (Bits m) (XOut k e) Req Resp} {A : AdaptiveIAlg shA O}
  {C₁ : Challenger (Bits m) (XOut k e) Req₁ Resp₁}

/-- **The adversary's output in the extraction run's registers.** -/
def extForgery (v : ExtReg A C₁ Req₂ Resp₂) : O := A.out v.adv.1.1.1.work

/-- **The adversary's logs (the absorbed copy) in the extraction run's registers.** -/
def extLogs (v : ExtReg A C₁ Req₂ Resp₂) : LogReg Req A.slots := v.adv.1.1.1.logs

end Regs

variable (B PS) in
/-- **The compiled verifier's claim of a ring signature** `(R, m, (y, π))`, the default `c₀` for a
proof without one. -/
def ringClaim {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)} (hC : PS.CompiledBy V)
    (c₀ : Cl) (o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) : Cl :=
  (hC.claim ⟨o.1, o.2.1, o.2.2.1⟩ o.2.2.2).getD c₀

/-- **A verifying ring signature has an accepted claim** (`ProofSystem.CompiledBy`). -/
theorem accepted_ringClaim {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}
    (hC : PS.CompiledBy V) (c₀ : Cl) (H : Bits m → XOut k e)
    {o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)}
    (hv : (ofBase B PS adm).verify H o.1 o.2.1 o.2.2 = true) :
    V.Accepted (outEquiv k e ∘ H) (ringClaim B PS hC c₀ o) ∧
      V.stmt (ringClaim B PS hC c₀ o) = ⟨o.1, o.2.1, o.2.2.1⟩ := by
  obtain ⟨c, hc, hacc⟩ := hC.accepted_of_verify H ⟨o.1, o.2.1, o.2.2.1⟩ o.2.2.2 hv
  have hcl : ringClaim B PS hC c₀ o = c := by simp [ringClaim, Option.mem_def.1 hc]
  exact ⟨hcl ▸ hacc, hcl ▸ hC.stmt_eq _ _ _ hc⟩

/-! ### The relayed forger's transcripts as runs of the table form -/

variable (B PS adm) in
/-- The relayed forger's algorithm on the public keys, at the auxiliary value and the prover's
coins `p`. -/
noncomputable abbrev ringRelAlg
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O)
    (pks : Fin n → B.PK) (Q : ℕ) (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :=
  (relayedForgerVia A (F pks) pks Q p.2).alg p.1

variable (B PS adm) in
/-- The relayed forger's algorithm at the users' key coins, the prover's coins and an auxiliary
value. -/
noncomputable abbrev relAlg (A : UnforgeAdversary (ofBase B PS adm) n SO
    (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O)
    (keys : Fin n → B.KeyCoins)
    (Q : ℕ) (ρ : Fin Q → PS.Coins) (a : (A (fun i => B.pk (keys i), ())).Aux) :=
  ringRelAlg B PS adm A F (fun i => B.pk (keys i)) Q (a, ρ)

/-- **The multi-user challenger's runs as runs of the table form, in the extraction run's
registers** (`toOuterMeasure_outLaw_muChallenger_eq_absorbTab` at a free adversary, for an event
of the output and the first `Q'` logged requests). -/
-- TODO(unbundle-M4): stated at a free adversary so the defeq check against `dropTabCW` does not
-- unfold the relayed forger's shape.
theorem toOuterMeasure_outLaw_muChallenger_eq_absorbTab_ext (hO : O.NoQuery)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} {Ot : Type}
    (A : AdaptiveIAlg shA Ot) (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q' : ℕ)
    (H : Bits m → XOut k e) (E : Ot → List (MURequest O n) → Prop) :
    ((A.toKindAlg.composeBothOut (muChallenger O n keys Q') id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, E (A.out v.adv.1.1.1) ((requests v.chal.logs).take Q')} =
      ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω *
        (((A.absorbTab (muRelayAt O keys i₂) (muTab A keys Q' ω)).toKindAlg.composeBothOut
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, (fun w => E (extForgery w) ((requests (extLogs w)).take Q'))
            (dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
              (muRelayAt O keys i₂) (muTab A keys Q' ω) v)} :=
  toOuterMeasure_outLaw_muChallenger_eq_absorbTab hO A keys i₂ Q' H
    (fun d lg => E (A.out d.1.1.1) ((requests lg).take Q'))

/-- **The relayed forger's transcripts against the multi-user challenger as runs of the table form**
(`toOuterMeasure_outLaw_muChallenger_eq_absorbTab`): for a signing oracle without queries, at the
users' key coins, the oracle and the prover's coins, the probability that the relayed forger outputs
a verifying ring signature fresh for its multi-user requests is the average, over the auxiliary
input and the challenger's coins `ω`, of the probability that the forger holding the table at `ω`,
against the inert challenger, ends with an output and logs of that kind. -/
theorem transcriptLaw_relayedForger_eq (hO : O.NoQuery)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q Q' : ℕ) (ρ : Fin Q → PS.Coins)
    (H : Bits m → XOut k e) :
    ((relayedForgerVia A (F (fun i => B.pk (keys i))) (fun i => B.pk (keys i)) Q ρ).transcriptLaw
        (muChallenger O n keys Q') H).toOuterMeasure
        {x | ∃ p ∈ x, (ofBase B PS adm).verify H p.1.1 p.1.2.1 p.1.2.2 = true ∧
          MUFreshReq B (PS := PS) keys p.1 (p.2.map HistoryEntry.request)} =
      ∑' a, (A (fun i => B.pk (keys i), ())).aux a *
        ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω *
          ((((relAlg B PS adm A F keys Q ρ a).absorbTab (muRelayAt O keys i₂)
            (muTab (relAlg B PS adm A F keys Q ρ a) keys Q' ω)).toKindAlg.composeBothOut
            (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).outLaw
            H).toOuterMeasure
            {o | ∃ v ∈ o, (fun w => (ofBase B PS adm).verify H (extForgery w).1 (extForgery w).2.1
              (extForgery w).2.2 = true ∧
              MUFreshReq B (PS := PS) keys (extForgery w) ((requests (extLogs w)).take Q'))
              (dropTabCW (relAlg B PS adm A F keys Q ρ a)
                (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
                (muTab (relAlg B PS adm A F keys Q ρ a) keys Q' ω) v)} := by
  simp only [QueryBoundedAdversary.transcriptLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => congrArg _ ?_
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  have hR : ∀ {shB' : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} (B' : AdaptiveIAlg shB' (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)))
      (E : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → List (MURequest O n) → Prop),
      ((B'.toKindAlg.composeBothOut (muChallenger O n keys Q') id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, E (B'.output (muChallenger O n keys Q') v)
            ((B'.history (muChallenger O n keys Q') v).map HistoryEntry.request)} =
        ((B'.toKindAlg.composeBothOut (muChallenger O n keys Q') id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, E (B'.out v.adv.1.1.1) ((requests v.chal.logs).take Q')} := by
    intro _ B' E
    refine congrArg _ (Set.ext fun o => exists_congr fun v => and_congr_right fun _ => ?_)
    rw [AdaptiveIAlg.map_request_history]
    rfl
  let Ev : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof) → List (MURequest O n) → Prop :=
    fun x l => (ofBase B PS adm).verify H x.1 x.2.1 x.2.2 = true ∧ MUFreshReq B (PS := PS) keys x l
  -- TODO(unbundle-M4): `relAlg … a` has shape `(relayedForgerVia …).sh (a, ρ).1`; matching it
  -- against `(relayedForgerVia …).alg a` unfolds the relayed forger, so unfold the abbrevs first.
  dsimp only [relAlg, ringRelAlg]
  exact (hR ((relayedForgerVia A (F fun i => B.pk (keys i)) (fun i => B.pk (keys i)) Q ρ).alg a)
    Ev).trans (toOuterMeasure_outLaw_muChallenger_eq_absorbTab_ext hO
      ((relayedForgerVia A (F fun i => B.pk (keys i)) (fun i => B.pk (keys i)) Q ρ).alg a)
      keys i₂ Q' H Ev)

/-! ### The knowledge step at one table -/

section Knowledge

variable {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}
  {rel : Set (RingStmt B × RingWit B)}
  {ext : RingStmt B → DB (Bits m) (Out k e) → Multiset (RingWit B)}
  {β : ℕ → ℝ≥0∞}

variable (B PS) in
/-- **The test of the extraction**: the claim's statement is the forgery's, and the forgery is fresh
for the first `Q'` logged multi-user requests. -/
def extTest (hC : PS.CompiledBy V) (c₀ : Cl) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} {A : AdaptiveIAlg shA (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))}
    {C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit}
    (v : ExtReg A C₁ (MURequest O n) (MUResponse B)) : Prop :=
  V.stmt (ringClaim B PS hC c₀ (extForgery v)) = ⟨(extForgery v).1, (extForgery v).2.1, (extForgery v).2.2.1⟩ ∧
    MUFreshReq B (PS := PS) keys (extForgery v) ((requests (extLogs v)).take Q')

/-- **The knowledge step at one table** (`acceptsTest_le_of_knowledgeBound_default`): averaged over
the oracle, the probability that the forger holding a table, against the inert challenger, outputs
a verifying ring signature fresh for its logged multi-user requests is at most the probability that
its extraction run (`extRun`, the compiled verifier's queries on the forgery's claim) extracts a
witness for the forgery's claim with the test passing, plus the knowledge error at
`t' + kq` queries. -/
theorem tsum_le_extRun (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel ext β) (c₀ : Cl)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B)} (A : AdaptiveIAlg shA (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)))
    (tab : A.OuterTab (MURequest O n) (MUResponse B))
    (d₀ : ExtReg A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
      (MURequest O n) (MUResponse B))
    {t' : ℕ} (ht : A.width * (A.budget + A.post) ≤ t') :
    ∑' H, PMF.uniformOfFintype (Bits m → XOut k e) H *
      (((A.absorbTab (muRelayAt O keys i₂) tab).toKindAlg.composeBothOut
        (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).outLaw
        H).toOuterMeasure
        {o | ∃ v ∈ o, (fun w => (ofBase B PS adm).verify H (extForgery w).1 (extForgery w).2.1
          (extForgery w).2.2 = true ∧
          MUFreshReq B (PS := PS) keys (extForgery w) ((requests (extLogs w)).take Q'))
          (dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
            (muRelayAt O keys i₂) tab v)} ≤
      simProb (outEquiv k e) (extRun (outEquiv k e) A
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
          (muRelayAt O keys i₂)
          (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq d₀ tab)
        (fun v D => extTest B PS hC c₀ keys Q' v ∧
          NARG.ExtractsAt rel ext (V.stmt (ringClaim B PS hC c₀ (extForgery v))) D) +
        V.knowledgeError β (t' + V.kq) := by
  have hK := Quantum.AdaptiveIAlg.acceptsTest_le_of_knowledgeBound_defaultR K
    (A.absorbTab (muRelayAt O keys i₂) tab)
    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
    ((fun v => ringClaim B PS hC c₀ (extForgery v)) ∘
      dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
        tab)
    (fun w => extTest B PS hC c₀ keys Q' (dropTabCW A
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂) tab w))
    (insertTab A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
      tab d₀) ht
  have hE := Quantum.AdaptiveIAlg.simProb_expandAdv_mapOut_drop (V := V)
    (((A.absorbTab (muRelayAt O keys i₂) tab).toTPKindAlg.composeBothOut
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).toQueryAlgCoh)
    (dropTabCW A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
      tab)
    (insertTab A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂)
      tab d₀)
    (extOut A (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂) d₀
      tab) (fun o => by cases o <;> rfl) (fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
    (fun v D => extTest B PS hC c₀ keys Q' v ∧
      NARG.ExtractsAt rel ext (V.stmt (ringClaim B PS hC c₀ (extForgery v))) D)
  have hq : (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q').Q *
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q').q = 0 :=
    Nat.mul_zero _
  rw [hq, Nat.add_zero] at hK
  refine le_trans (ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl
    (MeasureTheory.measure_mono fun o ho => ?_)) (hK.trans_eq (congrArg (· + _) hE))
  obtain ⟨v, hv, hver, hf⟩ := ho
  obtain ⟨hacc, hst⟩ := accepted_ringClaim (adm := adm) hC c₀ H hver
  exact ⟨v, hv, hacc, hst, hf⟩

end Knowledge

/-! ### The chain -/

section Chain

variable {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}
  {rel : Set (RingStmt B × RingWit B)}
  {ext : RingStmt B → DB (Bits m) (Out k e) → Multiset (RingWit B)}
  {β : ℕ → ℝ≥0∞}

variable (B PS adm) in
/-- The default output of the extraction run of the relayed forger on the public keys (that of its
run with the empty table). -/
noncomputable abbrev ringDefault (A : UnforgeAdversary (ofBase B PS adm) n SO
    (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O)
    (pks : Fin n → B.PK) (i₂ : Fin n)
    (Q Q' : ℕ) (p : (A (pks, ())).Aux × (Fin Q → PS.Coins)) :
    ExtReg (ringRelAlg B PS adm A F pks Q p)
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
      (MURequest O n) (MUResponse B) :=
  dropTabCW (ringRelAlg B PS adm A F pks Q p)
    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muTwoRelay O n (pks 0) i₂)
    (tab₀ (ringRelAlg B PS adm A F pks Q p))
    ((((ringRelAlg B PS adm A F pks Q p).absorbTab (muTwoRelay O n (pks 0) i₂)
      (tab₀ (ringRelAlg B PS adm A F pks Q p))).toTPKindAlg.composeBothOut
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id)).defaultOut

variable (B PS adm) in
/-- The default output of the extraction run of the relayed forger at the users' key coins. -/
noncomputable abbrev relDefault (A : UnforgeAdversary (ofBase B PS adm) n SO
    (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n)
    (Q Q' : ℕ) (ρ : Fin Q → PS.Coins) (a : (A (fun i => B.pk (keys i), ())).Aux) :
    ExtReg (relAlg B PS adm A F keys Q ρ a)
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
      (MURequest O n) (MUResponse B) :=
  ringDefault B PS adm A F (fun i => B.pk (keys i)) i₂ Q Q' (a, ρ)

variable (B PS adm) in
/-- **The game through the relayed forger**: the forgery probability of the game with the side
oracle `SO`, `Q` requests, is at most the average, over the users' key coins, the oracle and the
prover's coins, of the probability that the relayed forger through `F` against the multi-user
challenger with `Q'` requests outputs a ring signature that verifies and is fresh for the
multi-user requests of its history (`MUFreshReq`). For BKM06 Definition 7,
`insiderForgeProb_le_relayedForger`. -/
def ThroughRelay
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) (Q Q' : ℕ) : Prop :=
  forgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
    ∑' H, PMF.uniformOfFintype (Bits m → XOut k e) H *
      ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
        ((relayedForgerVia A (F (fun i => B.pk (keys i))) (fun i => B.pk (keys i)) Q
          ρ).transcriptLaw
          (muChallenger O n keys Q') H).toOuterMeasure
          {x | ∃ p ∈ x, (ofBase B PS adm).verify H p.1.1 p.1.2.1 p.1.2.2 = true ∧
            MUFreshReq B (PS := PS) keys p.1 (p.2.map HistoryEntry.request)}

/-- **The game up to the extraction runs of the table form** (module docstring): for a game
through the relayed forger (`hgame`, `ThroughRelay`) with a signing oracle without queries (`hO`)
and relays of at most `qR` queries per request (`hqR`), a proof system given by a compiled verifier
`V` (`hC`) with a knowledge bound for `rel` at `ext` and `β` (`K`), the forgery probability of an
adversary with at most `t` queries and `Q` requests is at most the average, over the users' key
coins, the prover's coins, the auxiliary input and the multi-user challenger's coins `ω`, of the
probability that the extraction run of the relayed forger holding the table `muTab ω` extracts a
witness for the forgery's claim with the test `extTest` passing, plus the knowledge error at
`t + Q · qR + kq` queries. -/
theorem forgeProb_le_extRun (hO : O.NoQuery)
    (hC : PS.CompiledBy V) (K : V.KnowledgeBound rel ext β) (c₀ : Cl)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O) {qR : ℕ} (hqR : ∀ pks, (F pks).qR ≤ qR)
    (i₂ : Fin n) (Q Q' : ℕ) (hgame : ThroughRelay B PS adm A F Q Q') :
    forgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
        ∑' a, (A (fun i => B.pk (keys i), ())).aux a *
          ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω *
            simProb (outEquiv k e) (extRun (outEquiv k e) (relAlg B PS adm A F keys Q ρ a)
                (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
                (muRelayAt O keys i₂)
                (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
                (relDefault B PS adm A F keys i₂ Q Q' ρ a)
                (muTab (relAlg B PS adm A F keys Q ρ a) keys Q' ω))
              (fun v D => extTest B PS hC c₀ keys Q' v ∧
                NARG.ExtractsAt rel ext (V.stmt (ringClaim B PS hC c₀ (extForgery v))) D) +
      V.knowledgeError β (t + Q * qR + V.kq) := by
  refine hgame.trans (Ring.tsum_mul_le_tsum_mul_add _ fun keys => ?_)
  simp only [transcriptLaw_relayedForger_eq hO A F keys i₂ Q Q']
  -- the oracle's average innermost
  rw [← tsum_fintype (L := .unconditional _)
    (f := fun ρ => PMF.uniformOfFintype (Fin Q → PS.Coins) ρ * _)]
  simp only [← tsum_fintype (L := .unconditional _)]
  rw [tsum_mul_tsum_mul_comm]
  refine Ring.tsum_mul_le_tsum_mul_add _ fun ρ => ?_
  rw [tsum_mul_tsum_mul_comm]
  refine Ring.tsum_mul_le_tsum_mul_add _ fun a => ?_
  rw [tsum_mul_tsum_mul_comm]
  refine Ring.tsum_mul_le_tsum_mul_add _ fun ω => ?_
  -- TODO(unbundle-M4): `relDefault` unfolds to `ringDefault … (a, ρ)`, whose type mentions
  -- `(a, ρ).1` and `(a, ρ).2`; matching it against `relAlg … ρ a` unfolds the relayed forger, so
  -- state the knowledge step explicitly and unfold the abbrevs on both sides.
  have ht := ((relayedForgerVia A (F (fun i => B.pk (keys i))) (fun i => B.pk (keys i)) Q
    ρ).queries_le (a, ρ).1).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left Q (hqR (fun i => B.pk (keys i)))) t)
  have h := tsum_le_extRun (adm := adm) hC K c₀ keys i₂ Q' (relAlg B PS adm A F keys Q ρ a)
    (muTab (relAlg B PS adm A F keys Q ρ a) keys Q' ω) (relDefault B PS adm A F keys i₂ Q Q' ρ a) ht
  dsimp only [relDefault, ringDefault, relAlg, ringRelAlg] at h ⊢
  exact h

end Chain

/-! ### The extraction runs as the bridge against the multi-user challenger -/

section Bridge

variable {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)}
  {rel : Set (RingStmt B × RingWit B)}
  {ext : RingStmt B → DB (Bits m) (Out k e) → Multiset (RingWit B)}

/-- **The extraction runs at the multi-user challenger's tables are the bridge against the
multi-user challenger** (`Signature.sum_simLaw_extRun_muTab`): for `i₂ ≠ 0` and at least as many
requests as request points of the bridge (`hQ`), the average over the challenger's coins of any
event `R` of the extraction run's output and database is that of the bridge algorithm answered by
`muReplyAfter`. -/
theorem sum_simProb_extRun_eq_bridge (hC : PS.CompiledBy V) (c₀ : Cl)
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly (Bits m) (XOut k e)) t)
    (F : RelayFam (Bits m) (XOut k e) B PS adm n SO O)
    (keys : Fin n → B.KeyCoins) {i₂ : Fin n} (hi₂ : i₂ ≠ 0) (Q Q' : ℕ)
    (ρ : Fin Q → PS.Coins) (a : (A (fun i => B.pk (keys i), ())).Aux)
    (hQ : ((((relAlg B PS adm A F keys Q ρ a).absorbTab (muRelayAt O keys i₂)
      (tab₀ (relAlg B PS adm A F keys Q ρ a))).toTPKindAlg.composeBothOut
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') id).depth +
      V.kq) + 1 ≤ Q')
    (R : ExtReg (relAlg B PS adm A F keys Q ρ a)
      (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
      (MURequest O n) (MUResponse B) → DB (Bits m) (Out k e) → Prop) :
    ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω *
        simProb (outEquiv k e) (extRun (outEquiv k e) (relAlg B PS adm A F keys Q ρ a)
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
          (muRelayAt O keys i₂)
          (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
          (relDefault B PS adm A F keys i₂ Q Q' ρ a)
          (muTab (relAlg B PS adm A F keys Q ρ a) keys Q' ω)) R =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw (outEquiv k e) ((bridgeAlg (outEquiv k e) (relAlg B PS adm A F keys Q ρ a)
          (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q')
          (muRelayAt O keys i₂) (.publicKey 0)
          (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
          (relDefault B PS adm A F keys i₂ Q Q' ρ a)).inst
          (muReplyAfter O keys Q' c)) {p | R p.1.out p.2} := by
  have hTP : (relAlg B PS adm A F keys Q ρ a).TracePreserving :=
    (relayedForgerVia A (F (fun i => B.pk (keys i))) (fun i => B.pk (keys i)) Q ρ).tracePreserving a
  have h := Signature.sum_simLaw_extRun_muTab (relAlg B PS adm A F keys Q ρ a)
    (inertChallenger (Bits m) (XOut k e) (MURequest O n) Q') (muRelayAt O keys i₂) (outEquiv k e)
    (.publicKey 0) (SPBCS.QROM.expansionVia V fun v => ringClaim B PS hC c₀ (extForgery v)) V.kq
    (relDefault B PS adm A F keys i₂ Q Q' ρ a) hTP (muTwoRelay_outer_ne _ hi₂)
    (fun _ _ h => by cases h) keys hQ
    {p | R p.1.out p.2}
  unfold simProb
  convert h using 3

end Bridge

end GordieHowe
