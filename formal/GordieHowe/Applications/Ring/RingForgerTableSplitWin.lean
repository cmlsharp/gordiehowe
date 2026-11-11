-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerTableSplit
public import GordieHowe.Applications.Ring.RingForgerWin
public import GordieHowe.Model.Quantum.Interactive.BaseShiftLogs
public import GordieHowe.Model.Signature.MultiUserCount

@[expose] public section

/-!
# The forgery read from the bridge with the drops

The split form of the winning-condition facts of `GordieHowe/Applications/Ring/RingForgerWin.lean`
and `GordieHowe/Applications/Ring/RingForgerCount.lean`, on the basis states of the bridge with the
drops of the local queries (`Quantum.bridgeAlgDrop`, the instances of
`GordieHowe/Applications/Ring/RingForgerTableSplit.lean`):

- `forgesReq_splitReadout_bridgeAlgDrop`: on every basis state of nonzero amplitude, an output
  passing the extraction's test at the base component `ω` with a witness in `rel` reads
  (`splitReadout`) as a forgery for the logged multi-user requests (`Quantum.bridgeAlgDrop_logs`).
- `countP_requests_bridgeAlgDrop_le`: under sets carried by the absorbed adversary's steps that
  writing the part keeps, at most `Qs` signing and corruption requests are logged
  (`Quantum.bridgeAlgDrop_slotLogs`).
- `sum_simLaw_extRun_le_muEufProbWithin_tableForgerSplit`: the bound of the split table forger in
  MU-EUF-CMA^corr with at most `Qs` signing and corruption requests.
-/

namespace GordieHowe

open Quantum QROM Signature RingSignature RingSignature.OracleSplit IOP
open scoped ENNReal

/-! ### The forgery and the count on the bridge with the drops -/

section Win

variable {m k e N n : ℕ} {Y₁ : Type} [AddGroup Y₁] {Y : Type} [AddGroup Y] [Fintype Y]
  [DecidableEq Y] {sp : OracleSplit Y Y₁ (XOut k e)} {TB : BaseTypes}
  {B : BaseSigner (Bits m) Y N TB}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) TPS} {adm : KeyRing B.PK N → Prop}
  [DecidablePred adm] {O : SignOracle B.core} [NeZero n] {X₀ Cl : Type}
  {V : NARG.QROM.Verifier m k e Cl X₀}

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty O.Coins]

omit [Fintype Y] [DecidablePred adm] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
/-- **On the support of the bridge with the drops, an output passing the extraction's test at
`ω` with a witness in `rel` reads as a forgery** for the logged multi-user requests, at every
oracle `H` with base component `ω` at which `rel` is in the ring relation (`hrel`), for a
trace-preserving adversary with at most `Q'` slots (`forgesReq_splitReadout`,
`Quantum.bridgeAlgDrop_logs`). -/
theorem forgesReq_splitReadout_bridgeAlgDrop (hC : PS.CompiledBySplit sp V)
    {cl : X₀ → PS.Proof → Option Cl} (c₀ : Cl) {rel : Set (X₀ × RingWit B)}
    {ext : X₀ → DB (Bits m) (Out k e) → Multiset (RingWit B)} (f₀ : B.PK × B.BMsg × B.BSig)
    (keys : Fin n → B.KeyCoins) (i₂ : Fin n) (pk₀ : B.PK) (ω : Bits m → Y₁) (H : Bits m → Y)
    (hrel : ∀ x w, (hC.stmtAt ω x, w) ∈ rel → RingRel B adm H x w) (Q' : ℕ)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B.core)} (A : AdaptiveIAlg shA (SplitOut B PS X₀))
    (hA : A.TracePreserving) (hslots : A.slots ≤ Q')
    (C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit)
    (E : Expansion (Bits m) (Out k e) (ExtReg A C₁ (MURequest O n) (MUResponse B.core))) (kq : ℕ)
    (d₀ : ExtReg A C₁ (MURequest O n) (MUResponse B.core)) (D : A.BaseW Y₁) (ω' : Bits m → Y₁)
    (a : ℕ → MURequest O n → Option (MUResponse B.core)) {b}
    (hb : simState (outEquiv k e) ((bridgeAlgDrop (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂)
      (.publicKey 0) E kq d₀ D ω').inst a) b ≠ 0)
    (ht : splitTest sp hC cl c₀ ω keys Q' ((bridgeAlgDrop (outEquiv k e) A C₁
      (muTwoRelay O n pk₀ i₂) (.publicKey 0) E kq d₀ D ω').out b.1.1.1).out)
    (hx : NARG.ExtractsAt rel ext (V.stmt (splitClaim cl c₀ (extForgery
      ((bridgeAlgDrop (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂) (.publicKey 0) E kq d₀ D
        ω').out b.1.1.1).out))) (slotsDB (outEquiv k e) b.2)) :
    ForgesReq keys H (splitReadout B PS V cl c₀ rel ext f₀
      ((bridgeAlgDrop (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂) (.publicKey 0) E kq d₀ D
        ω').out b.1.1.1, slotsDB (outEquiv k e) b.2)) (requests b.1.1.2) := by
  refine forgesReq_splitReadout hC c₀ f₀ keys ω H hrel Q' _ _
    ((length_requests_le _).trans hslots) (fun r hr => ?_) ht hx
  obtain ⟨i, hi⟩ := (mem_requests_iff _ r).1 hr
  have hcases := bridgeAlgDrop_logs (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂) (.publicKey 0) E
    kq d₀ D ω' hA a hb hi
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

omit [AddGroup Y] [Fintype Y] [DecidablePred adm] [Fintype TPS.Proof] [DecidableEq TPS.Proof]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype O.Coins]
  [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The bridge with the drops logs at most `Qs` signing and corruption requests** on every basis
state of nonzero amplitude of its simulation, when sets `T` carried by the absorbed adversary's
steps (`hT`), which writing the part keeps (`hTD`), bound the count of its absorbed logs on the
last one (`hTQ`) (`Quantum.bridgeAlgDrop_slotLogs`, `card_bridge_le`). -/
theorem countP_requests_bridgeAlgDrop_le (pk₀ : B.PK) (i₂ : Fin n)
    {shA : AlgShape (Bits m) (XOut k e) (MURequest O n) (MUResponse B.core)} {A : AdaptiveIAlg shA (SplitOut B PS X₀)}
    (hA : A.TracePreserving) (C₁ : Challenger (Bits m) (XOut k e) (MURequest O n) Unit)
    (E : Expansion (Bits m) (Out k e) (ExtReg A C₁ (MURequest O n) (MUResponse B.core))) (kq : ℕ)
    (d₀ : ExtReg A C₁ (MURequest O n) (MUResponse B.core)) (D : A.BaseW Y₁) (ω' : Bits m → Y₁)
    {T : ℕ → Set ((A.W × MURequest O n) × LogReg (MURequest O n) A.slots)}
    (hT : A.LogInv (muTwoRelay O n pk₀ i₂) (tab₀ A) T)
    (hTD : ∀ l (x : (A.W × MURequest O n) × LogReg (MURequest O n) A.slots) v, x ∈ T l →
      ((D.Lw.set x.1.1 v, x.1.2), x.2) ∈ T l)
    {Qs : ℕ}
    (hTQ : ∀ x ∈ T (A.slots + A.post + 1),
      (Finset.univ.filter fun j => (x.2 j).any MURequest.isSignOrCorrupt = true).card ≤ Qs)
    (a : ℕ → MURequest O n → Option (MUResponse B.core)) {b}
    (hb : simState (outEquiv k e) ((bridgeAlgDrop (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂)
      (.publicKey 0) E kq d₀ D ω').inst a) b ≠ 0) :
    (requests b.1.1.2).countP MURequest.isSignOrCorrupt ≤ Qs := by
  obtain ⟨hTb, hlg⟩ := bridgeAlgDrop_slotLogs (outEquiv k e) A C₁ (muTwoRelay O n pk₀ i₂)
    (.publicKey 0) E kq d₀ D ω' T hA hT hTD a hb
  rw [countP_requests]
  refine (card_bridge_le A C₁ _ (.publicKey 0) b.1.1.2 _
    MURequest.isSignOrCorrupt rfl hlg).trans ?_
  simp only [isSignOrCorrupt_muTwoRelay_outer]
  exact hTQ _ hTb

end Win

/-! ### The bound with few signing and corruption requests -/

section Forger

variable {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Y Y₁ : Type} [DecidableEq Y] [AddGroup Y] [AddGroup Y₁] (sp : OracleSplit Y Y₁ (BitStr I J))
  {N n : ℕ} {TB : BaseTypes}
  {B : BaseSigner (Bits m) Y N TB} (O : SignOracle B.core) (e : BitStr I J ≃ Bd)

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]

variable [Fintype Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [NeZero n]
  {Req Resp Req₁ Resp₁ Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁]
  (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
  {shA : ∀ pks, Aux pks → AlgShape (Bits m) Y Req Resp} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) Ot)
  (C₁ : ∀ pks, Aux pks → Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : ∀ pks, Aux pks → TwoRelay Req Resp Req₁ Resp₁ (MURequest O n) (MUResponse B.core))
  (d₂ : MURequest O n)
  (E : ∀ pks p, Expansion (Bits m) Bd
    (ExtReg ((A pks p).restrictAt sp 0) (C₁ pks p) (MURequest O n) (MUResponse B.core)))
  (kq : ℕ) (d₀ : ∀ pks p, ExtReg ((A pks p).restrictAt sp 0) (C₁ pks p) (MURequest O n)
    (MUResponse B.core))
  (g : ∀ pks p, BaseGame.Tuple (Bits m) Bd
    (ExtReg ((A pks p).restrictAt sp 0) (C₁ pks p) (MURequest O n) (MUResponse B.core)) kq ×
      DB (Bits m) Bd → B.PK × B.BMsg × B.BSig)

/-- **The bound in MU-EUF-CMA^corr with at most `Qs` signing and corruption requests**
(`sum_simLaw_extRun_le_muLaw_tableForgerSplit` at the forgery event with the count): the average
of the events' probabilities is at most the probability that the forger with real base queries
wins with at most `Qs` signing and corruption requests. -/
theorem sum_simLaw_extRun_le_muEufProbWithin_tableForgerSplit (hO : O.ReadsBase sp)
    (hTP : ∀ pks p, (A pks p).TracePreserving)
    (hout : ∀ pks p c r q, (F pks p).outer c r = some q → q ≠ d₂) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (t' : ℕ) (ht : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ t')
    {Q' : ℕ} (Qs : ℕ)
    (hQ : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (tab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁),
      (Fin Q' → O.Coins) →
        ((A (fun i => B.pk (keys i)) p).restrictAt sp ω).OuterTab (MURequest O n) (MUResponse B.core))
    (htab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁) c
      (j : Fin ((A (fun i => B.pk (keys i)) p).restrictAt sp ω).slots) q,
      (q = d₂ ∨ ∃ c' r, (F (fun i => B.pk (keys i)) p).outer c' r = some q) →
        tab keys p ω c j q = muReplyAt sp O ω keys Q' c j q)
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      Set (BaseGame.Tuple (Bits m) Bd (ExtReg ((A (fun i => B.pk (keys i)) p).restrictAt sp 0)
        (C₁ (fun i => B.pk (keys i)) p) (MURequest O n) (MUResponse B.core)) kq × DB (Bits m) Bd))
    (hwin : ∀ keys p ω (h : Bits m → BitStr I J) c b,
      simState e ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).inst
        (muReplyAt sp O ω keys Q' c)) b ≠ 0 →
      ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).out b.1.1.1,
        slotsDB e b.2) ∈ W keys p ω →
      ForgesReq keys (join sp ω h) (g (fun i => B.pk (keys i)) p
        ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).out b.1.1.1,
          slotsDB e b.2)) (requests b.1.1.2) ∧
        (requests b.1.1.2).countP MURequest.isSignOrCorrupt ≤ Qs) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
          ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
            simLaw e (extRun e ((A (fun i => B.pk (keys i)) p).restrictAt sp ω)
              (C₁ (fun i => B.pk (keys i)) p) (F (fun i => B.pk (keys i)) p)
              (E (fun i => B.pk (keys i)) p) kq (d₀ (fun i => B.pk (keys i)) p) (tab keys p ω c))
              (W keys p ω) ≤
      muEufProbWithin (tableForgerSplit sp O e Aux aux A C₁ F d₂ E kq d₀ g t' ht) Q' Qs := by
  refine (sum_simLaw_extRun_le_muLaw_tableForgerSplit sp O e Aux aux A C₁ F d₂ E kq d₀ g hO hTP
    hout hd₂ t' ht hQ tab htab W (fun keys H f rs => ForgesReq keys H f rs ∧
      rs.countP MURequest.isSignOrCorrupt ≤ Qs) hwin).trans (le_of_eq ?_)
  simp only [muEufProbWithin, forges_iff_forgesReq, signCorruptCount_eq]

end Forger

end GordieHowe
