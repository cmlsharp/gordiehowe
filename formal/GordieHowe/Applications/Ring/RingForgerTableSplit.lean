-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerSplitChain
public import GordieHowe.Model.Signature.MultiUserTableForger
public import GordieHowe.Model.Quantum.Interactive.BaseShiftRestrict
public import GordieHowe.Model.Quantum.Interactive.BaseShiftDrops

@[expose] public section

/-!
# Extraction runs at a fixed base component as a multi-user forger with real queries

The split form of `GordieHowe/Model/Signature/MultiUserTableForger.lean`, for an oracle split
additively as `sp : Y ≃+ Y₁ × Y₂` and a signing oracle reading only the base component
(`SignOracle.ReadsBase`). The extraction run of `A.restrictAt sp ω`, for an adversary `A` over the
whole oracle, is an instance of the bridge algorithm of `A.restrictAt sp 0` with the drops of the
base parts at `ω` (`Quantum.simLaw_extRun_restrictAt_instLog`). The forger holds the
compressed-oracle simulation of that bridge algorithm with a uniform scratch register `Y₁ × Y₂`,
sends its request points to the multi-user challenger and makes each drop as a real query to the
oracle (`Quantum.ReqQueryAlg.advQ`), which adds the base component of the oracle's answer
(`Quantum.ReqQueryAlg.simLaw_plus_inst`). At an oracle `H` the challenger answers by its coins and
the base component of `H` (`muReplyAt`), so averaging over the second component of the oracle
bounds the extraction runs' events by the forger's.

- `sum_simLaw_countND_muReplyAt`: the reindexing of the challenger's coins
  (`Signature.sum_simLaw_countND_muReply`) for the replies at a fixed base component.
- `bridgeRepliesTabAt`, `instLog_withPerm_tabAt_eq`, `repliesAt_bridgeRepliesTabAt`,
  `sum_simLaw_withPerm_tab_eq`: a bridge algorithm read after permutations of its query registers,
  answered by tables agreeing with the multi-user challenger at a fixed base component.
- `sum_simLaw_extRun_restrictAt_tab`: the extraction runs of `A.restrictAt sp ω` at such tables
  are, on coin average, instances of the bridge of `A.restrictAt sp 0` with the drops at `ω`.
- `sum_simLaw_extRun_withStep_tab`: the same for an adversary whose steps are followed by a sorted
  list of additions (`AdaptiveIAlg.AddsW`), with the bridge with the drops of the additions.
- `simLaw_bridgeAlgAdds_le_plus`, `simLaw_bridgeAlgDrop_le_plus`: an event of the bridge with
  the drops at the base component of `H` is at most an event of the bridge with the scratch
  register after the real queries at `H`.
- `run_respond_muChallenger_base`: the challenger answers by `muReplyAt` at the base component of
  the oracle.
- `tableForgerAdds` (with `addsBridge`, `addsPoints`): the forger at additions `Pb` on the
  bridge's registers, one query per addition; `toOuterMeasure_muLaw_tableForgerAdds`,
  `sum_simLaw_le_muLaw_tableForgerAdds`, `sum_simLaw_le_muEufProb_tableForgerAdds` (for laws equal
  to the bridge read after the additions, `simLaw_withPerm_le_plus`),
  `sum_simLaw_extRun_le_muLaw_tableForgerAdds`, `sum_simLaw_extRun_le_muEufProb_tableForgerAdds`:
  its law and the bounds, for additions whose action is the drops of a list of additions.
- `tableForgerSplit` (with `splitBridge`, `splitPoints`, `splitDrop`): `tableForgerAdds` at the
  drops of the base parts, with `bT + 1` queries; `toOuterMeasure_muLaw_tableForgerSplit`: its law
  on an event of its terminal requests.
- `sum_simLaw_extRun_le_muLaw_tableForgerSplit`: the bound for an event `Ev` of the readout and
  the requests; `sum_simLaw_extRun_le_muEufProb_tableForgerSplit`: at the forgery event.
-/

namespace GordieHowe

open Quantum QROM Signature RingSignature RingSignature.OracleSplit
open scoped ENNReal

variable {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Y Y₁ : Type} [DecidableEq Y] [AddGroup Y] [AddGroup Y₁] (sp : OracleSplit Y Y₁ (BitStr I J))
  {N n : ℕ} {TB : BaseTypes} {B : BaseSigner (Bits m) Y N TB} (O : SignOracle B) (e : BitStr I J ≃ Bd)

/-! ### The reindexing of the coins at a fixed base component -/

open Classical in
/-- **The reindexing of the multi-user challenger's coins at a fixed base component**
(`Signature.sum_simLaw_countND_muReply` with `muReplyAt`): for a dummy request `d₂` that is not a
signing request (`hd₂`) and at least `t + 1` answered requests (`hQ`), the coin average of `simLaw`
of the instance answered with the coins at the number of earlier non-dummy requests is that of the
instance answered with the coins at the step. -/
theorem sum_simLaw_countND_muReplyAt [NeZero n] {t : ℕ} {Ot : Type} (ω : Bits m → Y₁)
    (keys : Fin n → B.KeyCoins) {Q' : ℕ} (hQ : t + 1 ≤ Q') (d₂ : MURequest O n)
    (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (G : ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B) t Ot)
    (S : Set (Ot × DB (Bits m) Bd)) :
    ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e (G.instLog fun _ prev r =>
          muReplyAt sp O ω keys Q' c (ReqQueryAlg.countND d₂ prev) r) S =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e (G.inst (muReplyAt sp O ω keys Q' c)) S := by
  rw [show (fun c => PMF.uniformOfFintype (Fin Q' → O.Coins) c *
      simLaw e (G.inst (muReplyAt sp O ω keys Q' c)) S) =
      fun c => PMF.uniformOfFintype (Fin Q' → O.Coins) c *
      simLaw e (G.instLog fun k _ r => muReplyAt sp O ω keys Q' c k r) S from rfl]
  refine ReqQueryAlg.sum_simLaw_instLog_eq e G _ _ _ _ (fun L _ => ?_) S
  have hcntQ : ∀ k : Fin (t + 1),
      ReqQueryAlg.countND d₂ (requestsBefore (fun j => some (L j)) k) < Q' := fun k =>
    lt_of_le_of_lt (countND_requestsBefore_le d₂ L k) (lt_of_lt_of_le k.2 hQ)
  let T := {k : Fin (t + 1) // L k ≠ d₂}
  let f₁ : T → Fin Q' := fun k => ⟨k.1, lt_of_lt_of_le k.1.2 hQ⟩
  let f₂ : T → Fin Q' := fun k =>
    ⟨ReqQueryAlg.countND d₂ (requestsBefore (fun j => some (L j)) k.1), hcntQ k.1⟩
  have h₁ : Function.Injective f₁ := fun k k' h => Subtype.ext (Fin.ext (by
    simpa [f₁] using congrArg Fin.val h))
  have h₂ : Function.Injective f₂ := by
    intro k k' h
    have hv : ReqQueryAlg.countND d₂ (requestsBefore (fun j => some (L j)) k.1) =
        ReqQueryAlg.countND d₂ (requestsBefore (fun j => some (L j)) k'.1) := by
      simpa [f₂] using congrArg Fin.val h
    rcases lt_trichotomy k.1 k'.1 with hl | hl | hl
    · exact absurd hv (countND_requestsBefore_lt d₂ L hl k.2).ne
    · exact Subtype.ext hl
    · exact absurd hv.symm (countND_requestsBefore_lt d₂ L hl k'.2).ne
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq h₁ h₂
  have hpt : ∀ c : Fin Q' → O.Coins,
      ReqQueryAlg.repliesAt
        (fun _ prev r => muReplyAt sp O ω keys Q' c (ReqQueryAlg.countND d₂ prev) r) L =
        ReqQueryAlg.repliesAt (fun k _ r => muReplyAt sp O ω keys Q' (c ∘ σ) k r) L := by
    intro c
    funext k
    simp only [ReqQueryAlg.repliesAt, muReplyAt, hcntQ k, lt_of_lt_of_le k.2 hQ, ↓reduceDIte]
    rcases hL : L k with i | ⟨i, sm⟩ | i
    · rfl
    · have hk : L k ≠ d₂ := fun h => hd₂ i sm (h.symm.trans hL)
      have := hσ ⟨k, hk⟩
      simp only [f₁, f₂] at this
      simp only [Function.comp_apply, this]
    · rfl
  rw [show (fun c => ReqQueryAlg.repliesAt
      (fun _ prev r => muReplyAt sp O ω keys Q' c (ReqQueryAlg.countND d₂ prev) r) L) =
      (fun c => ReqQueryAlg.repliesAt (fun k _ r => muReplyAt sp O ω keys Q' c k r) L) ∘
        fun c => c ∘ σ
      from funext hpt, ← PMF.map_comp, PMF.map_uniformOfFintype_comp_perm]

/-! ### Bridge algorithms read after permutations, at tables agreeing with the challenger -/

section Bridge

variable {Req Resp Req₁ Resp₁ Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA Ot)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ (MURequest O n) (MUResponse B))
  (d₂ : MURequest O n) (E : Expansion (Bits m) Bd (ExtReg A C₁ (MURequest O n) (MUResponse B)))
  (kq : ℕ) (d₀ : ExtReg A C₁ (MURequest O n) (MUResponse B))

/-- **The replies used against the bridge algorithm for a table `tab` at the base component `ω`**:
as `Signature.bridgeRepliesTab`, with the replies `muReplyAt` off the answer steps. -/
noncomputable def bridgeRepliesTabAt (ω : Bits m → Y₁) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    (c : Fin Q' → O.Coins) (tab : A.OuterTab (MURequest O n) (MUResponse B)) :
    ℕ → List (MURequest O n) → MURequest O n → Option (MUResponse B) := fun k prev q =>
  if answerSlot A C₁ k = none then muReplyAt sp O ω keys Q' c (ReqQueryAlg.countND d₂ prev) q
  else A.tabAt tab (ReqQueryAlg.countND d₂ prev) q

/-- **The table's replies and `bridgeRepliesTabAt` give the same instance** of the bridge algorithm
read after permutations `π` of its query registers. -/
theorem instLog_withPerm_tabAt_eq
    (π : Fin (bT A C₁ F kq + 1) →
      Equiv.Perm (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (ω : Bits m → Y₁) (keys : Fin n → B.KeyCoins) (Q' : ℕ) (c : Fin Q' → O.Coins)
    (tab : A.OuterTab (MURequest O n) (MUResponse B)) :
    ((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).instLog (fun _ prev q => A.tabAt tab
      (ReqQueryAlg.countND d₂ prev) q) =
      ((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).instLog
        (bridgeRepliesTabAt sp O A C₁ d₂ ω keys Q' c tab) := by
  refine ((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).instLog_congr_write
    fun k prev r hne x y => ?_
  have hk : answerSlot A C₁ k = none := by
    by_contra hk
    exact hne (by simp only [bridgeRepliesTabAt, hk, ↓reduceIte])
  exact (bridgeAlg_write_of_none A C₁ F e d₂ E kq d₀ hk x).trans
    (bridgeAlg_write_of_none A C₁ F e d₂ E kq d₀ hk y).symm

/-- **For a table agreeing with the multi-user challenger's replies at the base component `ω`**
(`htab`), `bridgeRepliesTabAt` are the count-indexed replies `muReplyAt` at every pattern of
requests of the bridge algorithm. -/
theorem repliesAt_bridgeRepliesTabAt (ω : Bits m → Y₁) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    (c : Fin Q' → O.Coins) (tab : A.OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ (j : Fin A.slots) q, (q = d₂ ∨ ∃ c r, F.outer c r = some q) →
      tab j q = muReplyAt sp O ω keys Q' c j q)
    (L : Fin (bT A C₁ F kq + 1) → MURequest O n)
    (hL : ∀ k, ∃ w, L k = (bridgeAlg e A C₁ F d₂ E kq d₀).req k w) :
    ReqQueryAlg.repliesAt (bridgeRepliesTabAt sp O A C₁ d₂ ω keys Q' c tab) L =
      ReqQueryAlg.repliesAt (fun _ prev r => muReplyAt sp O ω keys Q' c
        (ReqQueryAlg.countND d₂ prev) r) L := by
  funext k
  simp only [ReqQueryAlg.repliesAt, bridgeRepliesTabAt]
  split_ifs with hk
  · rfl
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hk
    have hc := countND_le_of_answerSlot A C₁ F e d₂ E kq d₀ L hL (k := k) k.2.le hj
    have hlt : ReqQueryAlg.countND d₂ (requestsBefore (fun i => some (L i)) k) < A.slots :=
      lt_of_le_of_lt hc j.2
    simp only [AdaptiveIAlg.tabAt, hlt, ↓reduceDIte]
    obtain ⟨w, hw⟩ := hL k
    refine htab _ _ ?_
    rw [hw]
    exact bridgeAlg_req_mem A C₁ F e d₂ E kq d₀ k w

/-- **The bridge algorithm read after permutations, at tables agreeing with the multi-user
challenger at the base component `ω`**: for a dummy that is not a signing request (`hd₂`), at
least as many answered requests as request points (`hQ`) and tables `tab c` agreeing with the
replies at the coins `c` (`htab`), the coin average of `simLaw` of the instances with the tables'
replies is that of the instances answered as the challenger at `ω` answers. -/
theorem sum_simLaw_withPerm_tab_eq [NeZero n]
    (π : Fin (bT A C₁ F kq + 1) →
      Equiv.Perm (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hd₂ : ∀ i sm, d₂ ≠ .sign i sm) (ω : Bits m → Y₁) (keys : Fin n → B.KeyCoins) {Q' : ℕ}
    (hQ : bT A C₁ F kq + 1 ≤ Q')
    (tab : (Fin Q' → O.Coins) → A.OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ c (j : Fin A.slots) q, (q = d₂ ∨ ∃ c r, F.outer c r = some q) →
      tab c j q = muReplyAt sp O ω keys Q' c j q)
    (S : Set (BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ (MURequest O n) (MUResponse B)) kq ×
      DB (Bits m) Bd)) :
    ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).instLog fun _ prev q =>
          A.tabAt (tab c) (ReqQueryAlg.countND d₂ prev) q) S =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).inst
          (muReplyAt sp O ω keys Q' c)) S := by
  have h1 : ∀ c, simLaw e (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).instLog fun _ prev q =>
      A.tabAt (tab c) (ReqQueryAlg.countND d₂ prev) q) S =
      simLaw e (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).instLog
        (bridgeRepliesTabAt sp O A C₁ d₂ ω keys Q' c (tab c))) S := fun c => by
    rw [instLog_withPerm_tabAt_eq sp O e A C₁ F d₂ E kq d₀ π ω keys Q' c (tab c)]
  rw [Finset.sum_congr rfl fun c _ => congrArg _ (h1 c)]
  have h2 := ReqQueryAlg.sum_simLaw_instLog_eq e ((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π)
    (PMF.uniformOfFintype (Fin Q' → O.Coins)) (PMF.uniformOfFintype (Fin Q' → O.Coins))
    (fun c => bridgeRepliesTabAt sp O A C₁ d₂ ω keys Q' c (tab c))
    (fun c _ prev r => muReplyAt sp O ω keys Q' c (ReqQueryAlg.countND d₂ prev) r)
    (fun L hL => congrArg (fun f => PMF.map f _) (funext fun c =>
      repliesAt_bridgeRepliesTabAt sp O e A C₁ F d₂ E kq d₀ ω keys Q' c (tab c) (htab c) L hL)) S
  exact h2.trans (sum_simLaw_countND_muReplyAt sp O e ω keys hQ d₂ hd₂
    ((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π) S)

/-- **The extraction runs of an adversary with additions after its Kraus maps, at tables agreeing
with the multi-user challenger at `ω`, are, on coin average, the instances of the bridge with the
drops of the additions** (`AdaptiveIAlg.AddsW.simLaw_extRun_instLog`,
`sum_simLaw_withPerm_tab_eq`): for a trace-preserving `A`, steps `st'` that are `A`'s followed by
the sorted list of additions `P` at `ω` (`hst`), none after the last Kraus map (`hlast`), outer
requests never the dummy (`hout`), a dummy that is not a signing request (`hd₂`), at least as many
answered requests as request points (`hQ`) and tables `tab c` agreeing with the replies at `ω` and
the coins `c` (`htab`), the coin averages of `simLaw` agree, the bridge's instance answered as the
challenger at `ω` answers. -/
theorem sum_simLaw_extRun_withStep_tab [NeZero n] (hA : A.TracePreserving)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (P : A.AddsW Y₁) (ω : Bits m → Y₁)
    (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (A.step k))
    (hTP' : (A.withStep st').TracePreserving) (hlast : P.Off lastStep)
    (keys : Fin n → B.KeyCoins) {Q' : ℕ} (hQ : bT A C₁ F kq + 1 ≤ Q')
    (tab : (Fin Q' → O.Coins) → A.OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ c (j : Fin A.slots) q, (q = d₂ ∨ ∃ c r, F.outer c r = some q) →
      tab c j q = muReplyAt sp O ω keys Q' c j q)
    (S : Set (BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ (MURequest O n) (MUResponse B)) kq ×
      DB (Bits m) Bd)) :
    ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ (tab c)) S =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).inst (muReplyAt sp O ω keys Q' c)) S := by
  have h1 : ∀ c, simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ (tab c)) S =
      simLaw e ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).instLog fun _ prev q =>
        A.tabAt (tab c) (ReqQueryAlg.countND d₂ prev) q) S := fun c =>
    congrArg (fun μ => μ S)
      (AdaptiveIAlg.AddsW.simLaw_extRun_instLog e A C₁ F d₂ ω st' P hst hA hTP' hlast hout E kq
        d₀ (tab c))
  rw [Finset.sum_congr rfl fun c _ => congrArg _ (h1 c)]
  exact sum_simLaw_withPerm_tab_eq sp O e A C₁ F d₂ E kq d₀
    (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω) hd₂ ω keys hQ tab htab S

end Bridge

/-! ### Extraction runs of restricted adversaries at tables agreeing with the challenger -/

section Restrict

variable [Fintype Y] [Fintype Y₁] [DecidableEq Y₁]
  {Req Resp Req₁ Resp₁ Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁]

/-- **The extraction runs of `A.restrictAt sp ω` at tables agreeing with the multi-user challenger
at `ω` are, on coin average, the instances of the bridge of `A.restrictAt sp 0` with the drops at
`ω`** (`simLaw_extRun_restrictAt_instLog`, `sum_simLaw_withPerm_tab_eq`): for a trace-preserving
`A`, outer requests never the dummy (`hout`), a dummy
that is not a signing request (`hd₂`), at least as many answered requests as request points
(`hQ`) and tables `tab c` agreeing with the replies at `ω` and the coins `c` (`htab`), the coin
averages of `simLaw` agree, the bridge's instance answered as the challenger at `ω` answers. -/
theorem sum_simLaw_extRun_restrictAt_tab [NeZero n] {shA : AlgShape (Bits m) Y Req Resp} (A : AdaptiveIAlg shA Ot)
    (hA : A.TracePreserving) (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ (MURequest O n) (MUResponse B)) (d₂ : MURequest O n)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (E : Expansion (Bits m) Bd (ExtReg (A.restrictAt sp 0) C₁ (MURequest O n) (MUResponse B)))
    (kq : ℕ) (d₀ : ExtReg (A.restrictAt sp 0) C₁ (MURequest O n) (MUResponse B))
    (ω : Bits m → Y₁) (keys : Fin n → B.KeyCoins) {Q' : ℕ}
    (hQ : bT (A.restrictAt sp 0) C₁ F kq + 1 ≤ Q')
    (tab : (Fin Q' → O.Coins) → (A.restrictAt sp ω).OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ c (j : Fin A.slots) q, (q = d₂ ∨ ∃ c r, F.outer c r = some q) →
      tab c j q = muReplyAt sp O ω keys Q' c j q)
    (S : Set (BaseGame.Tuple (Bits m) Bd
      (ExtReg (A.restrictAt sp 0) C₁ (MURequest O n) (MUResponse B)) kq × DB (Bits m) Bd)) :
    ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e (extRun e (A.restrictAt sp ω) C₁ F E kq d₀ (tab c)) S =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e ((bridgeAlgDrop e (A.restrictAt sp 0) C₁ F d₂ E kq d₀ (A.restrictBaseW sp) ω).inst
          (muReplyAt sp O ω keys Q' c)) S := by
  have h1 : ∀ c, simLaw e (extRun e (A.restrictAt sp ω) C₁ F E kq d₀ (tab c)) S =
      simLaw e ((bridgeAlgDrop e (A.restrictAt sp 0) C₁ F d₂ E kq d₀ (A.restrictBaseW sp)
        ω).instLog fun _ prev q => (A.restrictAt sp 0).tabAt (tab c)
          (ReqQueryAlg.countND d₂ prev) q) S := fun c =>
    congrArg (fun μ => μ S)
      (simLaw_extRun_restrictAt_instLog sp A e C₁ F d₂ ω hA hout E kq d₀ (tab c))
  rw [Finset.sum_congr rfl fun c _ => congrArg _ (h1 c)]
  exact sum_simLaw_withPerm_tab_eq sp O e (A.restrictAt sp 0) C₁ F d₂ E kq d₀
    (bridgeDrop e (A.restrictAt sp 0) C₁ F d₂ E kq d₀ (A.restrictBaseW sp) ω) hd₂ ω keys hQ tab
    htab S

end Restrict

/-! ### The bridge with the drops against the bridge with real queries -/

section Drops

variable [Fintype Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁] [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  [Inhabited Req₂]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA Ot)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)
  (d₂ : Req₂) (E : Expansion (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ)
  (d₀ : ExtReg A C₁ Req₂ Resp₂) (D : A.BaseW Y₁)

/-- **An event of the bridge read after additions at the base component of `H` is at most an
event of the bridge with the scratch register read after the real queries at `H`**
(`simLaw_plus_inst`, `simState_plus_inst_ne`): when on every basis state of nonzero amplitude of
the former the event `S` of the output and the database implies `Pr` of them and the logged
requests (`hw`). -/
theorem simLaw_withPerm_le_plus
    (Pb : StepAdds (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
      (Fin (bT A C₁ F kq + 1)) (Bits m) Y₁)
    (H : Bits m → Y) (a : ℕ → Req₂ → Option Resp₂)
    (S : Set (BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂) kq × DB (Bits m) Bd))
    (Pr : BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂) kq × DB (Bits m) Bd →
      List Req₂ → Prop)
    (hw : ∀ b, simState e (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm (Pb.perm (base sp H))).inst
        a) b ≠ 0 →
      (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm (Pb.perm (base sp H))).out b.1.1.1,
        slotsDB e b.2) ∈ S →
      Pr (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm (Pb.perm (base sp H))).out b.1.1.1,
        slotsDB e b.2) (requests b.1.1.2)) :
    simLaw e (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm (Pb.perm (base sp H))).inst a) S ≤
      bornWeight (simState e
        (((ReqQueryAlg.plusAlg (bridgeAlg e A C₁ F d₂ E kq d₀) (Y₁ × BitStr I J)).withPerm
          fun k => (Pb.plus sp).perm H k).inst a))
        {b | Pr ((((ReqQueryAlg.plusAlg (bridgeAlg e A C₁ F d₂ E kq d₀) (Y₁ × BitStr I J)).withPerm
          fun k => (Pb.plus sp).perm H k).inst a).out b.1.1,
            slotsDB e b.2) (requests b.1.1.2)} := by
  have h := congrArg (fun μ : MeasureTheory.OuterMeasure _ => μ S)
    (ReqQueryAlg.simLaw_plus_inst e sp Pb H a)
  refine (le_of_eq h.symm).trans ?_
  simp only [simLaw, MeasureTheory.OuterMeasure.map_apply]
  exact bornWeight_mono_of_support _ fun b hb hS =>
    hw _ (ReqQueryAlg.simState_plus_inst_ne e sp Pb H a b hb) hS

/-- **An event of the bridge with the drops of additions at the base component of `H` is at most
an event of the bridge with the scratch register read after the real queries at `H`**
(`simLaw_plus_inst`, `simState_plus_inst_ne`): for additions `Pb` on the bridge's registers whose
action at every base component is the drops of the list `P` (`hPb`), when on every basis state of
nonzero amplitude of the former the event `S` of the output and the database implies `Pr` of them
and the logged requests (`hw`). -/
theorem simLaw_bridgeAlgAdds_le_plus (P : A.AddsW Y₁)
    (Pb : StepAdds (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
      (Fin (bT A C₁ F kq + 1)) (Bits m) Y₁)
    (hPb : ∀ ω k, Pb.perm ω k = bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k)
    (H : Bits m → Y) (ω : Bits m → Y₁) (hω : base sp H = ω)
    (a : ℕ → Req₂ → Option Resp₂)
    (S : Set (BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂) kq × DB (Bits m) Bd))
    (Pr : BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂) kq × DB (Bits m) Bd →
      List Req₂ → Prop)
    (hw : ∀ b, simState e ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).inst a) b ≠ 0 →
      ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).out b.1.1.1, slotsDB e b.2) ∈ S →
      Pr ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).out b.1.1.1, slotsDB e b.2)
        (requests b.1.1.2)) :
    simLaw e ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).inst a) S ≤
      bornWeight (simState e
        (((ReqQueryAlg.plusAlg (bridgeAlg e A C₁ F d₂ E kq d₀) (Y₁ × BitStr I J)).withPerm
          fun k => (Pb.plus sp).perm H k).inst a))
        {b | Pr ((((ReqQueryAlg.plusAlg (bridgeAlg e A C₁ F d₂ E kq d₀) (Y₁ × BitStr I J)).withPerm
          fun k => (Pb.plus sp).perm H k).inst a).out b.1.1,
            slotsDB e b.2) (requests b.1.1.2)} := by
  subst hω
  have heq : bridgeAlgAdds e A C₁ F d₂ E kq d₀ P (base sp H) =
      (bridgeAlg e A C₁ F d₂ E kq d₀).withPerm (Pb.perm (base sp H)) := by
    unfold bridgeAlgAdds
    exact congrArg _ (funext fun k => (hPb _ k).symm)
  rw [heq] at hw ⊢
  exact simLaw_withPerm_le_plus sp e A C₁ F d₂ E kq d₀ Pb H a S Pr hw

/-- **An event of the bridge with the drops at the base component of `H` is at most an event of
the bridge with the scratch register read after the real queries at `H`** (`simLaw_plus_inst`,
`simState_plus_inst_ne`): when on every basis state of nonzero amplitude of the former the event
`S` of the output and the database implies `Pr` of them and the logged requests (`hw`). -/
theorem simLaw_bridgeAlgDrop_le_plus (H : Bits m → Y) (ω : Bits m → Y₁) (hω : base sp H = ω)
    (a : ℕ → Req₂ → Option Resp₂)
    (S : Set (BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂) kq × DB (Bits m) Bd))
    (Pr : BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂) kq × DB (Bits m) Bd →
      List Req₂ → Prop)
    (hw : ∀ b, simState e ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).inst a) b ≠ 0 →
      ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1, slotsDB e b.2) ∈ S →
      Pr ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).out b.1.1.1, slotsDB e b.2)
        (requests b.1.1.2)) :
    simLaw e ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).inst a) S ≤
      bornWeight (simState e
        (((ReqQueryAlg.plusAlg (bridgeAlg e A C₁ F d₂ E kq d₀) (Y₁ × BitStr I J)).withPerm
          fun k => ((bridgeDropData e A C₁ F d₂ E kq d₀ D).plus sp).perm H k).inst a))
        {b | Pr ((((ReqQueryAlg.plusAlg (bridgeAlg e A C₁ F d₂ E kq d₀) (Y₁ × BitStr I J)).withPerm
          fun k => ((bridgeDropData e A C₁ F d₂ E kq d₀ D).plus sp).perm H k).inst a).out b.1.1,
            slotsDB e b.2) (requests b.1.1.2)} := by
  subst hω
  rw [bridgeAlgDrop_eq e A C₁ F d₂ E kq d₀ D (base sp H)] at hw ⊢
  have h := congrArg (fun μ : MeasureTheory.OuterMeasure _ => μ S)
    (ReqQueryAlg.simLaw_plus_inst e sp (bridgeDropData e A C₁ F d₂ E kq d₀ D) H a)
  refine (le_of_eq h.symm).trans ?_
  simp only [simLaw, MeasureTheory.OuterMeasure.map_apply]
  exact bornWeight_mono_of_support _ fun b hb hS =>
    hw _ (ReqQueryAlg.simState_plus_inst_ne e sp (bridgeDropData e A C₁ F d₂ E kq d₀ D) H a b hb)
      hS

end Drops

/-! ### The challenger's replies at an oracle -/

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq Y] in
/-- **The multi-user challenger answers by `muReplyAt` at the oracle's base component**, without
assignments, for a signing oracle reading only the base component. -/
theorem run_respond_muChallenger_base (hO : O.ReadsBase sp) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    (c : Fin Q' → O.Coins) (hist : MUHist O n) (r : MURequest O n) (H : Bits m → Y) :
    ((muChallenger O n keys Q').respond c hist r).run H =
      ⟨muReplyAt sp O (base sp H) keys Q' c hist.length r, []⟩ := by
  simp only [muChallenger, muReplyAt]
  split_ifs with h
  · rcases r with i | ⟨i, sm⟩ | i
    · rfl
    · simp only [OracleProg.run_bind, OracleProg.run_pure]
      rw [hO _ _ _ H (join sp (base sp H) 0) (base_join sp _ _).symm]
    · rfl
  · rfl

/-! ### The forger over a list of additions -/

section Adds

variable [Fintype Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [NeZero n]
  {Req Resp Req₁ Resp₁ Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁]
  (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
  {shA : ∀ pks, Aux pks → AlgShape (Bits m) (BitStr I J) Req Resp} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) Ot)
  (C₁ : ∀ pks, Aux pks → Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : ∀ pks, Aux pks → TwoRelay Req Resp Req₁ Resp₁ (MURequest O n) (MUResponse B))
  (d₂ : MURequest O n)
  (E : ∀ pks p, Expansion (Bits m) Bd (ExtReg (A pks p) (C₁ pks p) (MURequest O n) (MUResponse B)))
  (kq : ℕ) (d₀ : ∀ pks p, ExtReg (A pks p) (C₁ pks p) (MURequest O n) (MUResponse B))
  (g : ∀ pks p, BaseGame.Tuple (Bits m) Bd
    (ExtReg (A pks p) (C₁ pks p) (MURequest O n) (MUResponse B)) kq ×
      DB (Bits m) Bd → B.PK × B.BMsg × B.BSig)

/-- The bridge algorithm of the extraction run of `A pks p`. -/
noncomputable abbrev addsBridge (pks : Fin n → B.PK) (p : Aux pks) :
    ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B)
      (bT (A pks p) (C₁ pks p) (F pks p) kq)
      (BaseGame.Tuple (Bits m) Bd (ExtReg (A pks p) (C₁ pks p) (MURequest O n) (MUResponse B))
        kq) :=
  bridgeAlg e (A pks p) (C₁ pks p) (F pks p) d₂ (E pks p) kq (d₀ pks p)

/-- The query points of the bridge with the scratch register `Y₁ × Y₂`: the additions `Pb` as real
queries (`StepAdds.plus`). -/
noncomputable abbrev addsPoints
    (Pb : ∀ pks p, StepAdds (QueryReg (addsBridge O e Aux A C₁ F d₂ E kq d₀ pks p).W 1 (Bits m)
      (BitStr I J)) (Fin (bT (A pks p) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y₁)
    (pks : Fin n → B.PK) (p : Aux pks) :
    StepAdds (QueryReg (ReqQueryAlg.plusAlg (addsBridge O e Aux A C₁ F d₂ E kq d₀ pks p)
      (Y₁ × BitStr I J)).W 1 (Bits m) (BitStr I J))
      (Fin (bT (A pks p) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y :=
  (Pb pks p).plus sp

/-- **The multi-user forger with real queries at a list of additions on the bridge**: on the
public keys `pks` it draws `p` from `aux pks`, runs the compressed-oracle simulation of the bridge
algorithm of the extraction run of `A pks p`, with a uniform scratch register `Y₁ × Y₂`, its
request points sent to the multi-user challenger and the additions `Pb pks p` made as real queries
to the oracle (`ReqQueryAlg.advQ` at `StepAdds.plus`), and outputs `g pks p` of the output and the
measured database. It makes `slotQ (Pb pks p).nb (bT + 1)` queries (one per addition), at most
`t'` (`ht`).

Running time: that of `ReqQueryAlg.advQ` (its paragraph) on the bridge algorithm with the
additions `Pb pks p`, the draw of `p` and the readout `g`; polynomial when the bridge, the
additions and `g` are. This running time is argued here, not proved in Lean. -/
noncomputable def tableForgerAdds
    (Pb : ∀ pks p, StepAdds (QueryReg (addsBridge O e Aux A C₁ F d₂ E kq d₀ pks p).W 1 (Bits m)
      (BitStr I J)) (Fin (bT (A pks p) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y₁)
    (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT (A pks p) (C₁ pks p) (F pks p) kq + 1) ≤
      t') :
    MUAdversary O n (OracleView.queriesOnly (Bits m) Y) t' := fun pv =>
  { Aux := Aux pv.1
    aux := aux pv.1
    sh p := ((ReqQueryAlg.advQ e (addsPoints sp O e Aux A C₁ F d₂ E kq d₀ Pb pv.1 p)).mapOut
      (g pv.1 p)).toShape
    alg p :=
      (ReqQueryAlg.advQ e (addsPoints sp O e Aux A C₁ F d₂ E kq d₀ Pb pv.1 p)).mapOut (g pv.1 p)
    tracePreserving p :=
      ReqQueryAlg.tracePreserving_advQ e (addsPoints sp O e Aux A C₁ F d₂ E kq d₀ Pb pv.1 p)
    withinBudget p := AdaptiveIAlg.mapOut_withinBudget
      (ReqQueryAlg.withinBudget_advQ e (addsPoints sp O e Aux A C₁ F d₂ E kq d₀ Pb pv.1 p))
        (g pv.1 p)
    queries_le p :=
      (ReqQueryAlg.queries_advQ e (addsPoints sp O e Aux A C₁ F d₂ E kq d₀ Pb pv.1 p)).le.trans
        (ht pv.1 p) }

/-- **The law of the forger at a list of additions on an event of its terminal requests**: for a
signing oracle reading only the base component (`hO`) and at least as many answered requests as
request points (`hQ`), averaged over the users' key coins, the oracle `H`, the auxiliary input and
the challenger's coins `c`, the Born weight of `|Sim*⟩` of the bridge with the scratch register
read after the real queries at `H`, answered as the challenger at the base component of `H`
answers (`muReplyAt`), on the outcomes whose readout and logged requests satisfy `Ev`. -/
theorem toOuterMeasure_muLaw_tableForgerAdds (hO : O.ReadsBase sp)
    (Pb : ∀ pks p, StepAdds (QueryReg (addsBridge O e Aux A C₁ F d₂ E kq d₀ pks p).W 1 (Bits m)
      (BitStr I J)) (Fin (bT (A pks p) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y₁)
    (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT (A pks p) (C₁ pks p) (F pks p) kq + 1) ≤
      t')
    {Q' : ℕ} (hQ : ∀ pks p, bT (A pks p) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (Ev : (Fin n → B.KeyCoins) → (Bits m → Y) → B.PK × B.BMsg × B.BSig →
      List (MURequest O n) → Prop) :
    (muLaw (tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g Pb t' ht) Q').toOuterMeasure
        {x | ∃ q ∈ x.2.2, Ev x.1 x.2.1 q.1 (q.2.map HistoryEntry.request)} =
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' H, PMF.uniformOfFintype (Bits m → Y) H *
          ∑' p, aux (fun i => B.pk (keys i)) p *
            ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
              bornWeight (simState e
                (((ReqQueryAlg.plusAlg (addsBridge O e Aux A C₁ F d₂ E kq d₀
                  (fun i => B.pk (keys i)) p) (Y₁ × BitStr I J)).withPerm fun k =>
                    (addsPoints sp O e Aux A C₁ F d₂ E kq d₀ Pb (fun i => B.pk (keys i)) p).perm H
                        k).inst
                      (muReplyAt sp O (base sp H) keys Q' c)))
                {b | Ev keys H (g (fun i => B.pk (keys i)) p
                  ((((ReqQueryAlg.plusAlg (addsBridge O e Aux A C₁ F d₂ E kq d₀
                    (fun i => B.pk (keys i)) p) (Y₁ × BitStr I J)).withPerm fun k =>
                      (addsPoints sp O e Aux A C₁ F d₂ E kq d₀ Pb (fun i => B.pk (keys i)) p).perm H
                        k).inst
                        (muReplyAt sp O (base sp H) keys Q' c)).out b.1.1,
                    slotsDB e b.2))
                  (requests b.1.1.2)} := by
  simp only [muLaw, runLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    QueryBoundedAdversary.transcriptLaw]
  refine tsum_congr fun keys => congrArg _ (tsum_congr fun H => congrArg _ (tsum_congr fun p => ?_))
  congr 1
  set P := addsPoints sp O e Aux A C₁ F d₂ E kq d₀ Pb (fun i => B.pk (keys i)) p
  set g' := g (fun i => B.pk (keys i)) p
  have hset : (fun o => (keys, H, o)) ⁻¹' {x : (Fin n → B.KeyCoins) × (Bits m → Y) ×
      Option ((B.PK × B.BMsg × B.BSig) × MUHist O n) |
        ∃ q ∈ x.2.2, Ev x.1 x.2.1 q.1 (q.2.map HistoryEntry.request)} =
      {o | ∃ q ∈ o, Ev keys H q.1 (q.2.map HistoryEntry.request)} := rfl
  rw [hset]
  -- TODO(unbundle-M4): rewriting `alg` leaves the scheme's `sh a` in the shape argument; state
  -- `composeBothOut_mapOut` at the field shape and go back to `rw`
  dsimp only [tableForgerAdds]
  rw [AdaptiveIAlg.composeBothOut_mapOut, KindAlg.toOuterMeasure_outLaw_composeBothOut]
  exact ReqQueryAlg.toOuterMeasure_outLaw_advQ e P H (StepAdds.allOn_plus _ _)
    (muChallenger O n keys Q')
    (muReplyAt sp O (base sp H) keys Q') (hQ _ p)
    (fun c k hist w hl => (run_respond_muChallenger_base sp O hO keys Q' c hist _ H).trans
      (by rw [hl]))
    (fun c hist r H' => by rw [run_respond_muChallenger_base sp O hO keys Q' c hist r H'])
    (fun o rs => Ev keys H (g' o) rs)

/-- **Laws equal to the bridge read after additions, at tables of the multi-user challenger's
replies, are bounded by the forger at those additions**: for a signing oracle reading only the
base component (`hO`), laws `run keys p ω c` that are those of the instance of the bridge read
after the additions `Pb` at `ω` with the replies of the table `tab keys p ω c` (`hrun`), a dummy
that is not a signing request (`hd₂`), at least as many answered requests as request points
(`hQ`), tables agreeing with the replies at `ω` and the coins `c` (`htab`), and events
`W keys p ω` that make the readout `g` satisfy `Ev` at every oracle with base component `ω` on
every basis state of nonzero amplitude of the bridge read after the additions at `ω` (`hwin`):
the average of the events' probabilities is at most the forger's probability of `Ev`. -/
theorem sum_simLaw_le_muLaw_tableForgerAdds (hO : O.ReadsBase sp)
    (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (Pb : ∀ pks p, StepAdds (QueryReg (addsBridge O e Aux A C₁ F d₂ E kq d₀ pks p).W 1 (Bits m)
      (BitStr I J)) (Fin (bT (A pks p) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y₁)
    (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT (A pks p) (C₁ pks p) (F pks p) kq + 1) ≤
      t')
    {Q' : ℕ} (hQ : ∀ pks p, bT (A pks p) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (tab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      (Fin Q' → O.Coins) → (A _ p).OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁) c
      (j : Fin (A _ p).slots) q,
      (q = d₂ ∨ ∃ c' r, (F (fun i => B.pk (keys i)) p).outer c' r = some q) →
        tab keys p ω c j q = muReplyAt sp O ω keys Q' c j q)
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      Set (BaseGame.Tuple (Bits m) Bd (ExtReg (A _ p) (C₁ (fun i => B.pk (keys i)) p)
        (MURequest O n) (MUResponse B)) kq × DB (Bits m) Bd))
    (run : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      (Fin Q' → O.Coins) → MeasureTheory.OuterMeasure (BaseGame.Tuple (Bits m) Bd
        (ExtReg (A _ p) (C₁ (fun i => B.pk (keys i)) p) (MURequest O n) (MUResponse B)) kq ×
          DB (Bits m) Bd))
    (hrun : ∀ keys p ω c, run keys p ω c = simLaw e
      (((addsBridge O e Aux A C₁ F d₂ E kq d₀ _ p).withPerm ((Pb _ p).perm ω)).instLog
        fun _ prev q => (A _ p).tabAt (tab keys p ω c) (ReqQueryAlg.countND d₂ prev) q))
    (Ev : (Fin n → B.KeyCoins) → (Bits m → Y) → B.PK × B.BMsg × B.BSig →
      List (MURequest O n) → Prop)
    (hwin : ∀ keys p ω (h : Bits m → BitStr I J) c b,
      simState e (((addsBridge O e Aux A C₁ F d₂ E kq d₀ _ p).withPerm ((Pb _ p).perm ω)).inst
        (muReplyAt sp O ω keys Q' c)) b ≠ 0 →
      (((addsBridge O e Aux A C₁ F d₂ E kq d₀ _ p).withPerm ((Pb _ p).perm ω)).out b.1.1.1,
        slotsDB e b.2) ∈ W keys p ω →
      Ev keys (join sp ω h) (g (fun i => B.pk (keys i)) p
        (((addsBridge O e Aux A C₁ F d₂ E kq d₀ _ p).withPerm ((Pb _ p).perm ω)).out b.1.1.1,
          slotsDB e b.2)) (requests b.1.1.2)) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
          ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
            run keys p ω c (W keys p ω) ≤
      (muLaw (tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g Pb t' ht) Q').toOuterMeasure
        {x | ∃ q ∈ x.2.2, Ev x.1 x.2.1 q.1 (q.2.map HistoryEntry.request)} := by
  rw [toOuterMeasure_muLaw_tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g hO Pb t' ht hQ Ev]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl ?_
  rw [tsum_uniform_split sp, tsum_mul_tsum_mul_comm]
  refine ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl ?_
  rw [← one_mul (∑' p, _), ← PMF.tsum_coe (PMF.uniformOfFintype (Bits m → BitStr I J)),
    ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun h => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_
  rw [Finset.sum_congr rfl fun c _ => congrArg _ (congrArg (fun μ => μ (W keys p ω))
    (hrun keys p ω c))]
  rw [sum_simLaw_withPerm_tab_eq sp O e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p)
    ((Pb _ p).perm ω) hd₂ ω keys (hQ _ p) (tab keys p ω) (htab keys p ω) (W keys p ω)]
  refine Finset.sum_le_sum fun c _ => mul_le_mul' le_rfl ?_
  have hb := simLaw_withPerm_le_plus sp e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p)
    (Pb _ p) (join sp ω h) (muReplyAt sp O ω keys Q' c) (W keys p ω)
    (fun o rs => Ev keys (join sp ω h) (g _ p o) rs)
  rw [base_join] at hb
  rw [base_join]
  exact hb (hwin keys p ω h c)


/-- **Extraction runs of adversaries with additions after their Kraus maps, at tables of the
multi-user challenger's replies, are bounded by the forger at a list of additions**: for a
signing oracle reading only the base component (`hO`), trace-preserving adversaries `A` (`hTP`),
steps `st keys p ω` that are `A`'s followed by the sorted list of additions `P` at `ω` (`hst`),
none after the last Kraus map (`hlast`), trace preserving (`hTP'`), additions `Pb` on the bridge's
registers whose action is the drops of `P` (`hPb`), outer requests never the dummy (`hout`), a
dummy that is not a signing request (`hd₂`), at least as many answered requests as request points
(`hQ`), tables `tab keys p ω c` agreeing with the replies at `ω` and the coins `c` (`htab`), and
events `W keys p ω` that make the readout `g` satisfy `Ev` at every oracle with base component `ω`
on every basis state of nonzero amplitude of the bridge with the drops at `ω` (`hwin`): the
average of the events' probabilities is at most the forger's probability of `Ev`. -/
theorem sum_simLaw_extRun_le_muLaw_tableForgerAdds (hO : O.ReadsBase sp)
    (hTP : ∀ pks p, (A pks p).TracePreserving)
    (hout : ∀ pks p c r q, (F pks p).outer c r = some q → q ≠ d₂) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (P : ∀ pks p, (A pks p).AddsW Y₁) (hlast : ∀ pks p, (P pks p).Off lastStep)
    (Pb : ∀ pks p, StepAdds (QueryReg (addsBridge O e Aux A C₁ F d₂ E kq d₀ pks p).W 1 (Bits m)
      (BitStr I J)) (Fin (bT (A pks p) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y₁)
    (hPb : ∀ pks p ω k, (Pb pks p).perm ω k =
      bridgeDropAdds e (A pks p) (C₁ pks p) (F pks p) d₂ (E pks p) kq (d₀ pks p) (P pks p) ω k)
    (st : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      StepIdx (A _ p).slots (A _ p).post → KrausMap (A _ p).R
        (DReg (A _ p).W (A _ p).width (Bits m) (BitStr I J) Req Resp)
        (DReg (A _ p).W (A _ p).width (Bits m) (BitStr I J) Req Resp))
    (hst : ∀ keys p ω k, KrausMap.LeftPerm ((P _ p).toStepAdds.perm ω k) (st keys p ω k)
      ((A _ p).step k))
    (hTP' : ∀ keys p ω, ((A _ p).withStep (st keys p ω)).TracePreserving)
    (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT (A pks p) (C₁ pks p) (F pks p) kq + 1) ≤
      t')
    {Q' : ℕ} (hQ : ∀ pks p, bT (A pks p) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (tab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      (Fin Q' → O.Coins) → (A _ p).OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁) c
      (j : Fin (A _ p).slots) q,
      (q = d₂ ∨ ∃ c' r, (F (fun i => B.pk (keys i)) p).outer c' r = some q) →
        tab keys p ω c j q = muReplyAt sp O ω keys Q' c j q)
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      Set (BaseGame.Tuple (Bits m) Bd (ExtReg (A _ p) (C₁ (fun i => B.pk (keys i)) p)
        (MURequest O n) (MUResponse B)) kq × DB (Bits m) Bd))
    (Ev : (Fin n → B.KeyCoins) → (Bits m → Y) → B.PK × B.BMsg × B.BSig →
      List (MURequest O n) → Prop)
    (hwin : ∀ keys p ω (h : Bits m → BitStr I J) c b,
      simState e ((bridgeAlgAdds e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p) (P _ p) ω).inst
        (muReplyAt sp O ω keys Q' c)) b ≠ 0 →
      ((bridgeAlgAdds e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p) (P _ p) ω).out b.1.1.1,
        slotsDB e b.2) ∈ W keys p ω →
      Ev keys (join sp ω h) (g (fun i => B.pk (keys i)) p
        ((bridgeAlgAdds e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p) (P _ p) ω).out b.1.1.1,
          slotsDB e b.2)) (requests b.1.1.2)) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
          ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
            simLaw e (extRun e ((A (fun i => B.pk (keys i)) p).withStep (st keys p ω))
              (C₁ (fun i => B.pk (keys i)) p) (F (fun i => B.pk (keys i)) p)
              (E (fun i => B.pk (keys i)) p) kq (d₀ (fun i => B.pk (keys i)) p) (tab keys p ω c))
              (W keys p ω) ≤
      (muLaw (tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g Pb t' ht) Q').toOuterMeasure
        {x | ∃ q ∈ x.2.2, Ev x.1 x.2.1 q.1 (q.2.map HistoryEntry.request)} := by
  rw [toOuterMeasure_muLaw_tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g hO Pb t' ht hQ Ev]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl ?_
  rw [tsum_uniform_split sp, tsum_mul_tsum_mul_comm]
  refine ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl ?_
  rw [← one_mul (∑' p, _), ← PMF.tsum_coe (PMF.uniformOfFintype (Bits m → BitStr I J)),
    ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun h => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_
  rw [sum_simLaw_extRun_withStep_tab sp O e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p)
    (hTP _ p) (hout _ p) hd₂ (P _ p) ω (st keys p ω) (hst keys p ω) (hTP' keys p ω) (hlast _ p)
    keys (hQ _ p) (tab keys p ω) (htab keys p ω) (W keys p ω)]
  refine Finset.sum_le_sum fun c _ => mul_le_mul' le_rfl ?_
  rw [base_join]
  exact simLaw_bridgeAlgAdds_le_plus sp e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p)
    (P _ p) (Pb _ p) (hPb _ p) (join sp ω h) ω (base_join sp ω h)
    (muReplyAt sp O ω keys Q' c) (W keys p ω)
    (fun o rs => Ev keys (join sp ω h) (g _ p o) rs) (hwin keys p ω h c)

/-- **The bound in MU-EUF-CMA^corr** (`sum_simLaw_le_muLaw_tableForgerAdds` at the forgery event
`ForgesReq`). -/
theorem sum_simLaw_le_muEufProb_tableForgerAdds (hO : O.ReadsBase sp)
    (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (Pb : ∀ pks p, StepAdds (QueryReg (addsBridge O e Aux A C₁ F d₂ E kq d₀ pks p).W 1 (Bits m)
      (BitStr I J)) (Fin (bT (A pks p) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y₁)
    (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT (A pks p) (C₁ pks p) (F pks p) kq + 1) ≤
      t')
    {Q' : ℕ} (hQ : ∀ pks p, bT (A pks p) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (tab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      (Fin Q' → O.Coins) → (A _ p).OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁) c
      (j : Fin (A _ p).slots) q,
      (q = d₂ ∨ ∃ c' r, (F (fun i => B.pk (keys i)) p).outer c' r = some q) →
        tab keys p ω c j q = muReplyAt sp O ω keys Q' c j q)
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      Set (BaseGame.Tuple (Bits m) Bd (ExtReg (A _ p) (C₁ (fun i => B.pk (keys i)) p)
        (MURequest O n) (MUResponse B)) kq × DB (Bits m) Bd))
    (run : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      (Fin Q' → O.Coins) → MeasureTheory.OuterMeasure (BaseGame.Tuple (Bits m) Bd
        (ExtReg (A _ p) (C₁ (fun i => B.pk (keys i)) p) (MURequest O n) (MUResponse B)) kq ×
          DB (Bits m) Bd))
    (hrun : ∀ keys p ω c, run keys p ω c = simLaw e
      (((addsBridge O e Aux A C₁ F d₂ E kq d₀ _ p).withPerm ((Pb _ p).perm ω)).instLog
        fun _ prev q => (A _ p).tabAt (tab keys p ω c) (ReqQueryAlg.countND d₂ prev) q))
    (hwin : ∀ keys p ω (h : Bits m → BitStr I J) c b,
      simState e (((addsBridge O e Aux A C₁ F d₂ E kq d₀ _ p).withPerm ((Pb _ p).perm ω)).inst
        (muReplyAt sp O ω keys Q' c)) b ≠ 0 →
      (((addsBridge O e Aux A C₁ F d₂ E kq d₀ _ p).withPerm ((Pb _ p).perm ω)).out b.1.1.1,
        slotsDB e b.2) ∈ W keys p ω →
      ForgesReq keys (join sp ω h) (g (fun i => B.pk (keys i)) p
        (((addsBridge O e Aux A C₁ F d₂ E kq d₀ _ p).withPerm ((Pb _ p).perm ω)).out b.1.1.1,
          slotsDB e b.2)) (requests b.1.1.2)) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
          ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
            run keys p ω c (W keys p ω) ≤
      muEufProb (tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g Pb t' ht) Q' := by
  refine (sum_simLaw_le_muLaw_tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g hO hd₂ Pb t' ht hQ
    tab htab W run hrun (fun keys H f rs => ForgesReq keys H f rs) hwin).trans (le_of_eq ?_)
  simp only [muEufProb, forges_iff_forgesReq]

/-- **The bound in MU-EUF-CMA^corr** (`sum_simLaw_extRun_le_muLaw_tableForgerAdds` at the forgery
event `ForgesReq`): the average of the events' probabilities is at most the success probability of
the forger at a list of additions. -/
theorem sum_simLaw_extRun_le_muEufProb_tableForgerAdds (hO : O.ReadsBase sp)
    (hTP : ∀ pks p, (A pks p).TracePreserving)
    (hout : ∀ pks p c r q, (F pks p).outer c r = some q → q ≠ d₂) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (P : ∀ pks p, (A pks p).AddsW Y₁) (hlast : ∀ pks p, (P pks p).Off lastStep)
    (Pb : ∀ pks p, StepAdds (QueryReg (addsBridge O e Aux A C₁ F d₂ E kq d₀ pks p).W 1 (Bits m)
      (BitStr I J)) (Fin (bT (A pks p) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y₁)
    (hPb : ∀ pks p ω k, (Pb pks p).perm ω k =
      bridgeDropAdds e (A pks p) (C₁ pks p) (F pks p) d₂ (E pks p) kq (d₀ pks p) (P pks p) ω k)
    (st : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      StepIdx (A _ p).slots (A _ p).post → KrausMap (A _ p).R
        (DReg (A _ p).W (A _ p).width (Bits m) (BitStr I J) Req Resp)
        (DReg (A _ p).W (A _ p).width (Bits m) (BitStr I J) Req Resp))
    (hst : ∀ keys p ω k, KrausMap.LeftPerm ((P _ p).toStepAdds.perm ω k) (st keys p ω k)
      ((A _ p).step k))
    (hTP' : ∀ keys p ω, ((A _ p).withStep (st keys p ω)).TracePreserving)
    (t' : ℕ)
    (ht : ∀ pks p, CoSimSchedule.slotQ (Pb pks p).nb (bT (A pks p) (C₁ pks p) (F pks p) kq + 1) ≤
      t')
    {Q' : ℕ} (hQ : ∀ pks p, bT (A pks p) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (tab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      (Fin Q' → O.Coins) → (A _ p).OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁) c
      (j : Fin (A _ p).slots) q,
      (q = d₂ ∨ ∃ c' r, (F (fun i => B.pk (keys i)) p).outer c' r = some q) →
        tab keys p ω c j q = muReplyAt sp O ω keys Q' c j q)
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      Set (BaseGame.Tuple (Bits m) Bd (ExtReg (A _ p) (C₁ (fun i => B.pk (keys i)) p)
        (MURequest O n) (MUResponse B)) kq × DB (Bits m) Bd))
    (hwin : ∀ keys p ω (h : Bits m → BitStr I J) c b,
      simState e ((bridgeAlgAdds e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p) (P _ p) ω).inst
        (muReplyAt sp O ω keys Q' c)) b ≠ 0 →
      ((bridgeAlgAdds e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p) (P _ p) ω).out b.1.1.1,
        slotsDB e b.2) ∈ W keys p ω →
      ForgesReq keys (join sp ω h) (g (fun i => B.pk (keys i)) p
        ((bridgeAlgAdds e (A _ p) (C₁ _ p) (F _ p) d₂ (E _ p) kq (d₀ _ p) (P _ p) ω).out b.1.1.1,
          slotsDB e b.2)) (requests b.1.1.2)) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
          ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
            simLaw e (extRun e ((A (fun i => B.pk (keys i)) p).withStep (st keys p ω))
              (C₁ (fun i => B.pk (keys i)) p) (F (fun i => B.pk (keys i)) p)
              (E (fun i => B.pk (keys i)) p) kq (d₀ (fun i => B.pk (keys i)) p) (tab keys p ω c))
              (W keys p ω) ≤
      muEufProb (tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g Pb t' ht) Q' := by
  refine (sum_simLaw_extRun_le_muLaw_tableForgerAdds sp O e Aux aux A C₁ F d₂ E kq d₀ g hO hTP
    hout hd₂ P hlast Pb hPb st hst hTP' t' ht hQ tab htab W
    (fun keys H f rs => ForgesReq keys H f rs)
    hwin).trans (le_of_eq ?_)
  simp only [muEufProb, forges_iff_forgesReq]

end Adds

/-! ### The forger -/

section Forger

variable [Fintype Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [NeZero n]
  {Req Resp Req₁ Resp₁ Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁]
  (Aux : (Fin n → B.PK) → Type) (aux : ∀ pks, PMF (Aux pks))
  {shA : ∀ pks, Aux pks → AlgShape (Bits m) Y Req Resp} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) Ot)
  (C₁ : ∀ pks, Aux pks → Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : ∀ pks, Aux pks → TwoRelay Req Resp Req₁ Resp₁ (MURequest O n) (MUResponse B))
  (d₂ : MURequest O n)
  (E : ∀ pks p, Expansion (Bits m) Bd
    (ExtReg ((A pks p).restrictAt sp 0) (C₁ pks p) (MURequest O n) (MUResponse B)))
  (kq : ℕ) (d₀ : ∀ pks p, ExtReg ((A pks p).restrictAt sp 0) (C₁ pks p) (MURequest O n)
    (MUResponse B))
  (g : ∀ pks p, BaseGame.Tuple (Bits m) Bd
    (ExtReg ((A pks p).restrictAt sp 0) (C₁ pks p) (MURequest O n) (MUResponse B)) kq ×
      DB (Bits m) Bd → B.PK × B.BMsg × B.BSig)

/-- The bridge algorithm of the extraction run of `A pks p` read at the zero base component. -/
noncomputable abbrev splitBridge (pks : Fin n → B.PK) (p : Aux pks) :
    ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B)
      (bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq)
      (BaseGame.Tuple (Bits m) Bd
        (ExtReg ((A pks p).restrictAt sp 0) (C₁ pks p) (MURequest O n) (MUResponse B)) kq) :=
  bridgeAlg e ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) d₂ (E pks p) kq (d₀ pks p)

/-- The query points of the bridge with the scratch register `Y₁ × Y₂`: the drops of the base
parts as real queries (`StepAdds.plus` of `bridgeDropData`). -/
noncomputable abbrev splitPoints (pks : Fin n → B.PK) (p : Aux pks) :
    StepAdds (QueryReg (ReqQueryAlg.plusAlg (splitBridge sp O e Aux A C₁ F d₂ E kq d₀ pks p)
      (Y₁ × BitStr I J)).W 1 (Bits m) (BitStr I J))
      (Fin (bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1)) (Bits m) Y :=
  (bridgeDropData e ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) d₂ (E pks p) kq (d₀ pks p)
    ((A pks p).restrictBaseW sp)).plus sp

/-- **The multi-user forger with real queries for the base component**: on the public keys `pks`
it draws `p` from `aux pks`, runs the compressed-oracle simulation of the bridge algorithm of the
extraction run of `(A pks p).restrictAt sp 0`, with a uniform scratch register `Y₁ × Y₂`, its
request points sent to the multi-user challenger and the drops of the base parts made as real
queries to the oracle (`ReqQueryAlg.advQ`), and outputs `g pks p` of the output and the measured
database: `tableForgerAdds` at the drops of the base parts (`bridgeDropData`). It makes `bT + 1`
queries, at most `t'` (`ht`).

Running time: that of `tableForgerAdds` (its paragraph) at `bridgeDropData`. This running time is
argued here, not proved in Lean. -/
noncomputable def tableForgerSplit (t' : ℕ)
    (ht : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ t') :
    MUAdversary O n (OracleView.queriesOnly (Bits m) Y) t' :=
  tableForgerAdds sp O e Aux aux (fun pks p => (A pks p).restrictAt sp 0) C₁ F d₂ E kq d₀ g
    (fun pks p => bridgeDropData e ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) d₂ (E pks p) kq
      (d₀ pks p) ((A pks p).restrictBaseW sp)) t'
    (fun pks p => (CoSimSchedule.slotQ_one _ le_rfl).le.trans (ht pks p))

-- TODO(unbundle-M4): `convert … using 4`; remove once M1b's named register types and shape-indexed
-- AdaptiveIAlg make both sides one instance path
/-- **The law of the forger with real base queries on an event of its terminal requests**: for a
signing oracle reading only the base component (`hO`) and at least as many answered requests as
request points (`hQ`), averaged over the users' key coins, the oracle `H`, the auxiliary input and
the challenger's coins `c`, the Born weight of `|Sim*⟩` of the bridge with the scratch register
read after the real queries at `H`, answered as the challenger at the base component of `H`
answers (`muReplyAt`), on the outcomes whose readout and logged requests satisfy `Ev`. -/
theorem toOuterMeasure_muLaw_tableForgerSplit (hO : O.ReadsBase sp) (t' : ℕ)
    (ht : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ t') {Q' : ℕ}
    (hQ : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (Ev : (Fin n → B.KeyCoins) → (Bits m → Y) → B.PK × B.BMsg × B.BSig →
      List (MURequest O n) → Prop) :
    (muLaw (tableForgerSplit sp O e Aux aux A C₁ F d₂ E kq d₀ g t' ht) Q').toOuterMeasure
        {x | ∃ q ∈ x.2.2, Ev x.1 x.2.1 q.1 (q.2.map HistoryEntry.request)} =
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' H, PMF.uniformOfFintype (Bits m → Y) H *
          ∑' p, aux (fun i => B.pk (keys i)) p *
            ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
              bornWeight (simState e
                (((ReqQueryAlg.plusAlg (splitBridge sp O e Aux A C₁ F d₂ E kq d₀
                  (fun i => B.pk (keys i)) p) (Y₁ × BitStr I J)).withPerm fun k =>
                    (splitPoints sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p).perm
                      H k).inst (muReplyAt sp O (base sp H) keys Q' c)))
                {b | Ev keys H (g (fun i => B.pk (keys i)) p
                  ((((ReqQueryAlg.plusAlg (splitBridge sp O e Aux A C₁ F d₂ E kq d₀
                    (fun i => B.pk (keys i)) p) (Y₁ × BitStr I J)).withPerm fun k =>
                      (splitPoints sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p).perm
                        H k).inst (muReplyAt sp O (base sp H) keys Q' c)).out b.1.1,
                    slotsDB e b.2))
                  (requests b.1.1.2)} := by
  have h := toOuterMeasure_muLaw_tableForgerAdds sp O e Aux aux
    (fun pks p => (A pks p).restrictAt sp 0) C₁ F d₂ E kq d₀ g hO
    (fun pks p => bridgeDropData e ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) d₂ (E pks p) kq
      (d₀ pks p) ((A pks p).restrictBaseW sp)) t'
    (fun pks p => (CoSimSchedule.slotQ_one _ le_rfl).le.trans (ht pks p)) hQ Ev
  rw [tableForgerSplit]
  convert h using 4

/-- The bridge of `A pks p` read at the zero base component with the drops at `ω`. -/
noncomputable abbrev splitDrop (pks : Fin n → B.PK) (p : Aux pks) (ω : Bits m → Y₁) :
    ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B)
      (bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq)
      (BaseGame.Tuple (Bits m) Bd
        (ExtReg ((A pks p).restrictAt sp 0) (C₁ pks p) (MURequest O n) (MUResponse B)) kq) :=
  bridgeAlgDrop e ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) d₂ (E pks p) kq (d₀ pks p)
    ((A pks p).restrictBaseW sp) ω

-- TODO(unbundle-M4): `convert rfl using 4`; remove once M1b's named register types and
-- shape-indexed AdaptiveIAlg make both sides one instance path
/-- **Extraction runs at a fixed base component, at tables of the multi-user challenger's replies,
are bounded by the forger with real base queries** (module docstring): for a signing oracle
reading only the base component (`hO`), trace-preserving adversaries (`hTP`) over the whole
oracle, outer requests never the dummy (`hout`), a dummy
that is not a signing request (`hd₂`), at least as many answered requests as request points
(`hQ`), tables `tab keys p ω c` agreeing with the replies at `ω` and the coins `c` (`htab`), and
events `W keys p ω` that make the readout `g` satisfy `Ev` at every oracle with base component `ω`
on every basis state of nonzero amplitude of the bridge with the drops at `ω` (`hwin`): the
average of the events' probabilities is at most the forger's probability of `Ev`. -/
theorem sum_simLaw_extRun_le_muLaw_tableForgerSplit (hO : O.ReadsBase sp)
    (hTP : ∀ pks p, (A pks p).TracePreserving)
    (hout : ∀ pks p c r q, (F pks p).outer c r = some q → q ≠ d₂) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (t' : ℕ) (ht : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ t')
    {Q' : ℕ} (hQ : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (tab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁),
      (Fin Q' → O.Coins) →
        ((A (fun i => B.pk (keys i)) p).restrictAt sp ω).OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁) c
      (j : Fin ((A (fun i => B.pk (keys i)) p).restrictAt sp ω).slots) q,
      (q = d₂ ∨ ∃ c' r, (F (fun i => B.pk (keys i)) p).outer c' r = some q) →
        tab keys p ω c j q = muReplyAt sp O ω keys Q' c j q)
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      Set (BaseGame.Tuple (Bits m) Bd (ExtReg ((A (fun i => B.pk (keys i)) p).restrictAt sp 0)
        (C₁ (fun i => B.pk (keys i)) p) (MURequest O n) (MUResponse B)) kq × DB (Bits m) Bd))
    (Ev : (Fin n → B.KeyCoins) → (Bits m → Y) → B.PK × B.BMsg × B.BSig →
      List (MURequest O n) → Prop)
    (hwin : ∀ keys p ω (h : Bits m → BitStr I J) c b,
      simState e ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).inst
        (muReplyAt sp O ω keys Q' c)) b ≠ 0 →
      ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).out b.1.1.1,
        slotsDB e b.2) ∈ W keys p ω →
      Ev keys (join sp ω h) (g (fun i => B.pk (keys i)) p
        ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).out b.1.1.1,
          slotsDB e b.2)) (requests b.1.1.2)) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
          ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
            simLaw e (extRun e ((A (fun i => B.pk (keys i)) p).restrictAt sp ω)
              (C₁ (fun i => B.pk (keys i)) p) (F (fun i => B.pk (keys i)) p)
              (E (fun i => B.pk (keys i)) p) kq (d₀ (fun i => B.pk (keys i)) p) (tab keys p ω c))
              (W keys p ω) ≤
      (muLaw (tableForgerSplit sp O e Aux aux A C₁ F d₂ E kq d₀ g t' ht) Q').toOuterMeasure
        {x | ∃ q ∈ x.2.2, Ev x.1 x.2.1 q.1 (q.2.map HistoryEntry.request)} := by
  have h := sum_simLaw_extRun_le_muLaw_tableForgerAdds sp O e Aux aux
    (fun pks p => (A pks p).restrictAt sp 0)
    C₁ F d₂ E kq d₀ g hO (fun pks p => (A pks p).tracePreserving_restrictAt sp 0 (hTP pks p)) hout
    hd₂ (fun pks p => ((A pks p).restrictBaseW sp).toAddsW)
    (fun pks p _ w => AdaptiveIAlg.stepOn_lastStep (A pks p) w.1)
    (fun pks p => bridgeDropData e ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) d₂ (E pks p) kq
      (d₀ pks p) ((A pks p).restrictBaseW sp))
    (fun pks p ω k => bridgeDropData_perm e ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) d₂
      (E pks p) kq (d₀ pks p) ((A pks p).restrictBaseW sp) ω k)
    (fun keys p ω => ((A _ p).restrictAt sp ω).step)
    (fun keys p ω k => by
      rw [AdaptiveIAlg.BaseW.toStepAdds_perm]
      exact leftPerm_restrictAt_step sp ω (A _ p) k)
    (fun keys p ω => (A _ p).tracePreserving_restrictAt sp ω (hTP _ p)) t'
    (fun pks p => (CoSimSchedule.slotQ_one _ le_rfl).le.trans (ht pks p)) hQ tab htab W Ev hwin
  rw [tableForgerSplit]
  refine (le_of_eq ?_).trans (h.trans (le_of_eq ?_))
  rotate_left
  · convert rfl using 4
  refine tsum_congr fun keys => congrArg _ (tsum_congr fun p => congrArg _ (tsum_congr fun ω =>
    congrArg _ (Finset.sum_congr rfl fun c _ => congrArg _ ?_)))
  exact congrArg (fun x => simLaw e x (W keys p ω)) (extRun_restrictAt_eq_withStep sp (A _ p) e
    (C₁ _ p) (F _ p) ω (E _ p) kq (d₀ _ p) (tab keys p ω c))

/-- **The bound in MU-EUF-CMA^corr** (`sum_simLaw_extRun_le_muLaw_tableForgerSplit` at the forgery
event `ForgesReq`): the average of the events' probabilities is at most the success probability of
the forger with real base queries. -/
theorem sum_simLaw_extRun_le_muEufProb_tableForgerSplit (hO : O.ReadsBase sp)
    (hTP : ∀ pks p, (A pks p).TracePreserving)
    (hout : ∀ pks p c r q, (F pks p).outer c r = some q → q ≠ d₂) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (t' : ℕ) (ht : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ t')
    {Q' : ℕ} (hQ : ∀ pks p, bT ((A pks p).restrictAt sp 0) (C₁ pks p) (F pks p) kq + 1 ≤ Q')
    (tab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁),
      (Fin Q' → O.Coins) →
        ((A (fun i => B.pk (keys i)) p).restrictAt sp ω).OuterTab (MURequest O n) (MUResponse B))
    (htab : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Bits m → Y₁) c
      (j : Fin ((A (fun i => B.pk (keys i)) p).restrictAt sp ω).slots) q,
      (q = d₂ ∨ ∃ c' r, (F (fun i => B.pk (keys i)) p).outer c' r = some q) →
        tab keys p ω c j q = muReplyAt sp O ω keys Q' c j q)
    (W : ∀ (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (_ : Bits m → Y₁),
      Set (BaseGame.Tuple (Bits m) Bd (ExtReg ((A (fun i => B.pk (keys i)) p).restrictAt sp 0)
        (C₁ (fun i => B.pk (keys i)) p) (MURequest O n) (MUResponse B)) kq × DB (Bits m) Bd))
    (hwin : ∀ keys p ω (h : Bits m → BitStr I J) c b,
      simState e ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).inst
        (muReplyAt sp O ω keys Q' c)) b ≠ 0 →
      ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).out b.1.1.1,
        slotsDB e b.2) ∈ W keys p ω →
      ForgesReq keys (join sp ω h) (g (fun i => B.pk (keys i)) p
        ((splitDrop sp O e Aux A C₁ F d₂ E kq d₀ (fun i => B.pk (keys i)) p ω).out b.1.1.1,
          slotsDB e b.2)) (requests b.1.1.2)) :
    ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' p, aux (fun i => B.pk (keys i)) p *
        ∑' ω, PMF.uniformOfFintype (Bits m → Y₁) ω *
          ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
            simLaw e (extRun e ((A (fun i => B.pk (keys i)) p).restrictAt sp ω)
              (C₁ (fun i => B.pk (keys i)) p) (F (fun i => B.pk (keys i)) p)
              (E (fun i => B.pk (keys i)) p) kq (d₀ (fun i => B.pk (keys i)) p) (tab keys p ω c))
              (W keys p ω) ≤
      muEufProb (tableForgerSplit sp O e Aux aux A C₁ F d₂ E kq d₀ g t' ht) Q' := by
  refine (sum_simLaw_extRun_le_muLaw_tableForgerSplit sp O e Aux aux A C₁ F d₂ E kq d₀ g hO hTP
    hout hd₂ t' ht hQ tab htab W (fun keys H f rs => ForgesReq keys H f rs) hwin).trans
    (le_of_eq ?_)
  simp only [muEufProb, forges_iff_forgesReq]

end Forger

end GordieHowe
