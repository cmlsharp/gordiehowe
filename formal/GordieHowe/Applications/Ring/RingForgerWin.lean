-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerChain
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeSlots
public import GordieHowe.Model.Signature.MultiUserTableForger
public import GordieHowe.Model.RingSignature.BaseCompleteness

@[expose] public section

/-!
# The extracted witness as a forgery of the multi-user game

The last step of the reduction from the unforgeability game of `ofBase B PS adm` to MU-EUF-CMA^corr
with a signing oracle `O`: on every basis state of the compressed-oracle simulation of the bridge
(`Quantum.bridgeAlg`) whose logged multi-user requests are the dummy or outer requests of the
relayed forger's logged requests (`BridgeLogsAt`, which holds for a trace-preserving adversary,
`bridgeLogsAt_of_tracePreserving`), an output passing the extraction's test with a witness in `rel`
among those `ext` returns is read (`muReadout`: the first returned witness of the ring relation at
the zero oracle, for a base signer verifying without the oracle) as a forgery of MU-EUF-CMA^corr
for the logged multi-user requests.

- `mem_requestsBefore_iff`, `mem_requests_iff`: the requests of logs are their filled entries.
  `mem_take_requests_of_log`: a logged request numbered below `Q` is among the first `Q`
  (`Quantum.requestsBefore_prefix`, `GordieHowe/Model/Quantum/Pure/Game.lean`).
- `BridgeLogsAt`, `bridgeLogsAt_of_tracePreserving`: the logged requests of the bridge's instance are the dummy or outer requests of
  logged requests of the absorbed logs the output reads.
- `muReadout`: the forgery read from the extraction run's output and the measured database.
- `forgesReq_muReadout`: an output passing the test with a witness in `rel` reads as a forgery.
- `mem_requests_of_bridgeLogs`: every corrupting or signing multi-user request of the bridge is a
  logged request of the relayed forger.
- `simLaw_bridge_le_forgesReq`: on the bridge, the extraction's event is within the Born weight of
  the forgeries of the multi-user game for the logged requests.
-/

namespace GordieHowe

open Quantum Signature RingSignature QROM IOP
open scoped ENNReal

/-! ### Requests of logs -/

/-- **The requests before slot `k` are the filled logs of the slots before `k`.** -/
theorem mem_requestsBefore_iff {Req : Type} {m : ℕ} (lg : LogReg Req m) (r : Req) :
    ∀ k, r ∈ requestsBefore lg k ↔ ∃ j : Fin m, (j : ℕ) < k ∧ lg j = some r
  | 0 => by simp [requestsBefore]
  | k + 1 => by
    rw [requestsBefore, List.mem_append, mem_requestsBefore_iff lg r k]
    constructor
    · rintro (⟨j, hj, he⟩ | h)
      · exact ⟨j, by omega, he⟩
      · split_ifs at h with hk
        · exact ⟨⟨k, hk⟩, by simp, Option.mem_toList.1 h⟩
        · simp at h
    · rintro ⟨j, hj, he⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact Or.inl ⟨j, hj, he⟩
      · refine Or.inr ?_
        have hk : k < m := hj ▸ j.2
        rw [dif_pos hk]
        have : (⟨k, hk⟩ : Fin m) = j := Fin.ext hj.symm
        rw [this, he]
        simp

/-- **The requests of logs are their filled entries.** -/
theorem mem_requests_iff {Req : Type} {m : ℕ} (lg : LogReg Req m) (r : Req) :
    r ∈ requests lg ↔ ∃ j, lg j = some r :=
  (mem_requestsBefore_iff lg r m).trans ⟨fun ⟨j, _, h⟩ => ⟨j, h⟩, fun ⟨j, h⟩ => ⟨j, j.2, h⟩⟩

/-- **A logged request numbered below `Q` is among the first `Q` requests.** -/
theorem mem_take_requests_of_log {Req : Type} {m : ℕ} (lg : LogReg Req m) (j : Fin m) {r : Req}
    (hj : lg j = some r) {Q : ℕ} (hQ : (requestsBefore lg j).length < Q) :
    r ∈ (requests lg).take Q := by
  have h1 : requestsBefore lg (j + 1) = requestsBefore lg j ++ [r] := by
    rw [requestsBefore_succ_of_lt lg j.2]
    simp [hj]
  obtain ⟨t, ht⟩ := requestsBefore_prefix lg (k := j + 1) (k' := m) j.2
  rw [requests, ← ht, h1]
  refine List.mem_take_iff_getElem.2 ⟨(requestsBefore lg j).length, by simp; omega, ?_⟩
  simp

/-- **There are at most `m` requests in logs of `m` slots.** -/
theorem length_requests_le {Req : Type} {m : ℕ} (lg : LogReg Req m) : (requests lg).length ≤ m :=
  length_requestsBefore_le lg m

/-! ### The logged requests of the bridge -/

section Logs

variable {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type}
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req₁]
  [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂]
  [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]

/-- **The logged requests of the bridge's instance with the replies `a`** are, on every basis
state of nonzero amplitude of its compressed-oracle simulation, the dummy `d₂` or outer requests of
logged requests of the absorbed logs that the output reads. -/
def BridgeLogsAt (e : BitStr I J ≃ Bd) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
    (E : Expansion (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
    (a : ℕ → Req₂ → Option Resp₂) : Prop :=
  ∀ b, simState e ((bridgeAlg e A C₁ F d₂ E kq d₀).inst a) b ≠ 0 → ∀ i q, b.1.1.2 i = some q →
    q = d₂ ∨ ∃ j r, ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs j = some r ∧
      F.outer (A.reqCount ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs j) r =
        some q

/-- **The logs statement holds for a trace-preserving adversary**
(`Quantum.bridgeAlg_logs`). -/
theorem bridgeLogsAt_of_tracePreserving [Nonempty (Bits m)] (e : BitStr I J ≃ Bd)
    {shA : AlgShape (Bits m) (BitStr I J) Req Resp} {A : AdaptiveIAlg shA O} (hA : A.TracePreserving)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
    (E : Expansion (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
    (a : ℕ → Req₂ → Option Resp₂) : BridgeLogsAt e A C₁ F d₂ E kq d₀ a :=
  fun _ hb _ _ hq => bridgeAlg_logs e A C₁ F d₂ E kq d₀ hA a hb hq

end Logs

/-! ### The forgery read from the extraction -/

variable {m k e N : ℕ} {TB : BaseTypes}
  {B : BaseSigner (Bits m) (XOut k e) N TB}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem (Bits m) (XOut k e) (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n : ℕ} [NeZero n]
  {Cl : Type} {V : NARG.QROM.Verifier m k e Cl (RingStmt B)} {O : SignOracle B.core}

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty O.Coins]

variable (B PS adm) in
/-- **The forgery read from the extraction run** (the multi-user forger's readout): the decoding
(`decodeWit`) of the first witness among those `ext` returns from the measured database for the
forgery's claim that is a witness of the ring relation at the zero oracle, `f₀` if there is none.

Running time: one run of `ext`, then for each returned witness one test of the ring relation (the
support, one base verification and one public value at the zero oracle), and one decoding. This
running time is argued here, not proved in Lean. -/
def muReadout (hC : PS.CompiledBy V) (c₀ : Cl)
    (ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B))
    (f₀ : B.PK × B.BMsg × B.BSig)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B.core)} {A : AdaptiveIAlg shA (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))}
    {C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit} {kq : ℕ}
    (o : BaseGame.Tuple (Bits m) (Out k e)
      (ExtReg A C₁ (MURequest O n) (MUResponse B.core)) kq × DB (Bits m) (Out k e)) :
    B.PK × B.BMsg × B.BSig :=
  (((ext (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))) o.2).find? fun w =>
      decide (RingRel B adm 0 (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))) w)).bind
    (decodeWit (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))))).getD f₀

omit [NeZero n] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
/-- **An output passing the extraction's test with a witness in `rel` reads as a forgery** of
MU-EUF-CMA^corr for multi-user requests `mrs` (`ForgesReq`), at every oracle `H`, for a base signer
verifying without the oracle (`hB`) when every witness of `rel` is one of the ring relation at the
zero oracle (`hrel`), the forger's logs have at most `Q'` requests (`hlen`) and every corrupting or
signing request of `mrs` is one of the forger's logged requests (`hmrs`). -/
theorem forgesReq_muReadout (hC : PS.CompiledBy V) (c₀ : Cl) {rel : Set (RingStmt B × RingWit B)}
    {ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B)} (f₀ : B.PK × B.BMsg × B.BSig)
    (keys : Fin n → B.KeyCoins) (H : Bits m → XOut k e) (hB : B.VerifiesWithoutOracle)
    (hrel : ∀ x w, (x, w) ∈ rel → RingRel B adm 0 x w) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B.core)} {A : AdaptiveIAlg shA (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))}
    {C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit} {kq : ℕ}
    (o : BaseGame.Tuple (Bits m) (Out k e)
      (ExtReg A C₁ (MURequest O n) (MUResponse B.core)) kq × DB (Bits m) (Out k e))
    (mrs : List (MURequest O n))
    (hlen : (requests (extLogs o.1.out)).length ≤ Q')
    (hmrs : ∀ r ∈ mrs, (∀ i, r = .corrupt i → r ∈ requests (extLogs o.1.out)) ∧
      ∀ i sm, r = .sign i sm → r ∈ requests (extLogs o.1.out))
    (ht : extTest B PS hC c₀ keys Q' o.1.out)
    (hx : NARG.ExtractsAt rel (fun x D => (ext x D : Multiset (RingWit B)))
      (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))) o.2) :
    ForgesReq keys H (muReadout B PS adm hC c₀ ext f₀ o) mrs := by
  obtain ⟨hst, hfr⟩ := ht
  rw [List.take_of_length_le hlen] at hfr
  obtain ⟨w₁, hw₁, hrel₁⟩ := hx
  have hsome : ((ext (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))) o.2).find? fun w =>
      decide (RingRel B adm 0 (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))) w)).isSome :=
    List.find?_isSome.2 ⟨w₁, Multiset.mem_coe.1 hw₁, decide_eq_true (hrel _ _ hrel₁)⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hsome
  have hR : RingRel B adm H (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))) w := by
    have h1 := List.find?_some hw
    have h0 : RingRel B adm 0 _ w := of_decide_eq_true h1
    have hset : (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out)), w) ∈ ringRel B adm H := by
      rw [← hB.ringRel_eq adm 0 H]
      exact h0
    exact hset
  have hi := hR.idx_lt
  rw [muReadout, hw, Option.bind_some, decodeWit, dif_pos hi, Option.getD_some]
  refine ⟨hR.verify_eq, ?_⟩
  have hring : (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))).ring = (extForgery o.1.out).1 := by
    rw [hst]
  have hmsg : (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))).msg = (extForgery o.1.out).2.1 := by
    rw [hst]
  have hmem : (V.stmt (ringClaim B PS hC c₀ (extForgery o.1.out))).ring.1[w.idx] ∈
      (extForgery o.1.out).1.1 := by
    rw [← hring]
    exact List.getElem_mem hi
  obtain ⟨i, hpk, hc⟩ := hfr.1 _ hmem
  refine ⟨i, hpk, fun hm => hc ((hmrs _ hm).1 i rfl), fun sm hm hb => ?_⟩
  refine hfr.2 i sm ((hmrs _ hm).2 i sm rfl) (hpk ▸ hmem) ?_
  rw [hb]
  show B.bmsg _ _ = _
  rw [hring, hmsg]

omit [DecidablePred adm] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [DecidableEq TB.Pub] [Fintype O.Coins]
  [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The correspondence of the multi-user requests to the relayed forger's requests**: under the
logs statement (`hlogs`), on every basis state of nonzero amplitude of the bridge's simulation,
every corrupting or signing multi-user request it logs is a logged request of the relayed forger
(in the absorbed logs the output reads). -/
theorem mem_requests_of_bridgeLogs (i₂ : Fin n) {pk₀ : B.PK}
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B.core)} {A : AdaptiveIAlg shA (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))}
    {C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit}
    {E : Expansion (Bits m) (Out k e)
      (ExtReg A C₁ (MURequest O n) (MUResponse B.core))} {kq : ℕ}
    {d₀ : ExtReg A C₁ (MURequest O n) (MUResponse B.core)}
    {a : ℕ → MURequest O n → Option (MUResponse B.core)}
    (hlogs : BridgeLogsAt (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂) (.publicKey 0)
      E kq d₀ a) {b}
    (hb : simState (outEquiv k e) ((bridgeAlg (outEquiv k e) A C₁
      (muTwoRelay O n pk₀ i₂) (.publicKey 0) E kq d₀).inst a) b ≠ 0)
    {r : MURequest O n} (hr : r ∈ requests b.1.1.2)
    (hq : (∃ i, r = .corrupt i) ∨ ∃ i sm, r = .sign i sm) :
    r ∈ requests (extLogs ((bridgeAlg (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂)
      (.publicKey 0) E kq d₀).out b.1.1.1).out) := by
  obtain ⟨i, hi⟩ := (mem_requests_iff _ r).1 hr
  rcases hlogs b hb i r hi with h | ⟨j, r', hj, ho⟩
  · rw [h] at hq
    rcases hq with ⟨_, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
  · rw [← muTwoRelay_outer_eq_self ho hq]
    exact (mem_requests_iff _ _).2 ⟨j, hj⟩

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The extraction's event on the bridge is a forgery of the multi-user game** (module docstring):
for the bridge of an adversary `A` (at most `Q'` slots, `hslots`) through `muTwoRelay O n pk₀ i₂` with
the dummy `publicKey 0`, whose logged requests are read from the absorbed logs at the replies `a`
(`hlogs`), the weight of the outputs passing the test with a witness in `rel` for the claim is at
most the Born weight of the basis states whose readout (`muReadout`) is a forgery of
MU-EUF-CMA^corr for the logged multi-user requests, at every oracle `H`, for a base signer verifying
without the oracle (`hB`) when `rel` is contained in the ring relation at the zero oracle
(`hrel`). -/
theorem simLaw_bridge_le_forgesReq (hC : PS.CompiledBy V) (c₀ : Cl)
    {rel : Set (RingStmt B × RingWit B)}
    {ext : RingStmt B → DB (Bits m) (Out k e) → List (RingWit B)} (f₀ : B.PK × B.BMsg × B.BSig)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (pk₀ : B.PK) (H : Bits m → XOut k e)
    (hB : B.VerifiesWithoutOracle) (hrel : ∀ x w, (x, w) ∈ rel → RingRel B adm 0 x w) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B.core)} (A : AdaptiveIAlg shA (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))) (hslots : A.slots ≤ Q')
    (C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit)
    (E : Expansion (Bits m) (Out k e)
      (ExtReg A C₁ (MURequest O n) (MUResponse B.core))) (kq : ℕ)
    (d₀ : ExtReg A C₁ (MURequest O n) (MUResponse B.core))
    (a : ℕ → MURequest O n → Option (MUResponse B.core))
    (hlogs : BridgeLogsAt (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂) (.publicKey 0)
      E kq d₀ a) :
    simLaw (outEquiv k e) ((bridgeAlg (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂)
        (.publicKey 0) E kq d₀).inst a)
        {p | extTest B PS hC c₀ keys Q' p.1.out ∧
          NARG.ExtractsAt rel (fun x D => (ext x D : Multiset (RingWit B)))
            (V.stmt (ringClaim B PS hC c₀ (extForgery p.1.out))) p.2} ≤
      bornWeight (simState (outEquiv k e) ((bridgeAlg (outEquiv k e) A C₁
          (muTwoRelay O n pk₀ i₂) (.publicKey 0) E kq d₀).inst a))
        {b | ForgesReq keys H (muReadout B PS adm hC c₀ ext f₀
          ((bridgeAlg (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂) (.publicKey 0) E
            kq d₀).out b.1.1.1, slotsDB (outEquiv k e) b.2)) (requests b.1.1.2)} := by
  rw [simLaw, MeasureTheory.OuterMeasure.map_apply]
  refine bornWeight_mono_of_support _ fun b hb hS => ?_
  obtain ⟨ht, hx⟩ := hS
  refine forgesReq_muReadout hC c₀ f₀ keys H hB hrel Q' _ _
    ((length_requests_le _).trans hslots) (fun r hr => ?_) ht hx
  obtain ⟨i, hi⟩ := (mem_requests_iff _ r).1 hr
  have hcases := hlogs b hb i r hi
  refine ⟨fun i' hr' => ?_, fun i' sm hr' => ?_⟩
  · rcases hcases with h | ⟨j, r', hj, ho⟩
    · rw [hr'] at h
      cases h
    · rw [← muTwoRelay_outer_eq_self ho (Or.inl ⟨i', hr'⟩)]
      exact (mem_requests_iff _ _).2 ⟨j, hj⟩
  · rcases hcases with h | ⟨j, r', hj, ho⟩
    · rw [hr'] at h
      cases h
    · rw [← muTwoRelay_outer_eq_self ho (Or.inr ⟨i', sm, hr'⟩)]
      exact (mem_requests_iff _ _).2 ⟨j, hj⟩

end GordieHowe
