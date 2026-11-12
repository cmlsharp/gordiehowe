-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.MultiUserReindex
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeExt

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The bridge algorithm against the multi-user challenger

For an extraction run whose outer requests are requests of the multi-user game (`Quantum.TwoRelay`
with `outer` into `Signature.MURequest`), the table of outer replies of the multi-user challenger at
the users' key coins and its coins (`muTab`, request number `c` answered with coin `c`), and the
bridge algorithm (`Quantum.bridgeAlg`, `GordieHowe/Model/Quantum/Interactive/ReqBridge.lean`): by
the bridge statement (`Quantum.extBridge`), the coin average of `simLaw` of the extraction run at
that table is the coin average of `simLaw` of the bridge algorithm answered as the multi-user
challenger answers it, with coin `k` at step `k` (`sum_simLaw_extRun_muTab`). The bridge algorithm's
request points other than the answer steps (`answerSlot`) send the dummy and ignore its reply
(`bridgeAlg_req_of_none`, `bridgeAlg_write_of_none`), and at the answer step of slot `j` at most `j`
outer requests came before (`countND_le_of_answerSlot`), so the table's cut-off at the number of
slots is never reached at an answer step.

- `sum_simLaw_muReplyAfter_of_agree`: `Signature.sum_simLaw_countND_muReply` for replies that
  agree with the count-indexed ones at every pattern of requests of the algorithm.
- `answerSlot_eq_some`, `lt_of_answerSlot`: the answer step of slot `j` is
  `(j + 1) · (q + width)`.
- `countND_requestsBefore_le_card`, `countND_le_of_answerSlot`.
- `muTab`, `sum_simLaw_extRun_muTab` (**the bridge against the multi-user challenger**).
- `bridgeAlg_req_mem`, `bridgeRepliesTab`, `instLog_tabAt_eq_tab`, `repliesAt_bridgeRepliesTab`,
  `simLaw_extRun_tab_eq_sum`: the same for any table agreeing with the multi-user challenger's
  replies on the dummy and the outer requests.
-/

namespace GordieHowe

open Quantum QROM RingSignature

/-- **The non-dummy requests before step `k` are counted among the steps satisfying `P`**, when
every non-dummy request below `k` is at a step satisfying `P`. -/
theorem countND_requestsBefore_le_card {Req : Type} [DecidableEq Req] {m : ℕ} (d : Req)
    (L : Fin m → Req) (P : ℕ → Prop) [DecidablePred P] :
    ∀ k, k ≤ m → (∀ k' : Fin m, (k' : ℕ) < k → L k' ≠ d → P k') →
      ReqQueryAlg.countND d (requestsBefore (fun j => some (L j)) k) ≤
        ((Finset.range k).filter P).card
  | 0, _, _ => by simp [requestsBefore, ReqQueryAlg.countND]
  | k + 1, hk, h => by
    rw [countND_requestsBefore_succ d L (by omega), Finset.range_add_one, Finset.filter_insert]
    have ih := countND_requestsBefore_le_card d L P k (by omega)
      fun k' hk' hL => h k' (by omega) hL
    split_ifs with h1 h2 h2
    · rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · exact absurd (h ⟨k, by omega⟩ (by simp) h1) h2
    · rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · omega

namespace Signature

variable {N n : ℕ} {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits m) (BitStr I J) N T RMsg} (O : SignOracle B.core) (e : BitStr I J ≃ Bd)
  {t : ℕ}
  {Ot : Type}

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty O.Coins]

/-- **Replies agreeing with the count-indexed multi-user replies** at every pattern of requests of
the algorithm give the coin average of `simLaw` of the step-indexed instance
(`sum_simLaw_countND_muReply`). -/
theorem sum_simLaw_muReplyAfter_of_agree [Inhabited (MURequest O n)] (keys : Fin n → B.KeyCoins)
    {Q' : ℕ} (hQ : t + 1 ≤ Q') (d₂ : MURequest O n) (hd₂ : ∀ i sm, d₂ ≠ .sign i sm)
    (G : ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B.core) t Ot)
    (a : (Fin Q' → O.Coins) → ℕ → List (MURequest O n) → MURequest O n → Option (MUResponse B.core))
    (hag : ∀ L : Fin (t + 1) → MURequest O n, (∀ k, ∃ w, L k = G.req k w) → ∀ ω,
      ReqQueryAlg.repliesAt (a ω) L =
        ReqQueryAlg.repliesAt
          (fun _ prev r => muReplyAfter O keys Q' ω (ReqQueryAlg.countND d₂ prev) r) L)
    (S : Set (Ot × DB (Bits m) Bd)) :
    ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω * simLaw e (G.instLog (a ω)) S =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e (G.inst (muReplyAfter O keys Q' c)) S := by
  refine (ReqQueryAlg.sum_simLaw_instLog_eq e G _ _ a
    (fun ω _ prev r => muReplyAfter O keys Q' ω (ReqQueryAlg.countND d₂ prev) r)
    (fun L hL => ?_) S).trans (sum_simLaw_countND_muReply O e keys hQ d₂ hd₂ G S)
  exact congrArg (fun f => PMF.map f _) (funext (hag L hL))

/-- **The table of outer replies of the multi-user challenger** at the users' key coins `keys` and
its coins `ω`, for an adversary `A`: the reply after `j` requests (`muReplyAfter`, coin `j`). -/
def muTab {X Y : Type} {TB : SchemeTypes}
    {B : BaseScheme X Y TB} {O : SignOracle B} {n : ℕ} [AddGroup Y]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {Req Resp Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA Ot) (keys : Fin n → B.KeyCoins) (Q' : ℕ)
    (ω : Fin Q' → O.Coins) : A.OuterTab (MURequest O n) (MUResponse B) :=
  fun j q => muReplyAfter O keys Q' ω j q

end Signature

/-! ### The answer steps of the bridge algorithm -/

section AnswerSteps

variable {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **The answer step of slot `j` is `(j + 1) · (q + width)`.** -/
theorem answerSlot_eq_some {k : ℕ} {j : Fin A.slots}
    (h : answerSlot A C₁ k = some j) : k = ((j : ℕ) + 1) * (C₁.q + A.width) := by
  rw [answerSlot] at h
  by_cases hc : (C₁.q + A.width) ∣ k ∧ 0 < k / (C₁.q + A.width) ∧
      k / (C₁.q + A.width) - 1 < A.slots
  · rw [dif_pos hc] at h
    have hj : (j : ℕ) = k / (C₁.q + A.width) - 1 := (congrArg Fin.val (Option.some.inj h)).symm
    obtain ⟨hd, hp, -⟩ := hc
    rw [hj, Nat.sub_add_cancel hp]
    exact (Nat.div_mul_cancel hd).symm
  · rw [dif_neg hc] at h
    exact absurd h (by simp)

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **Answer steps come in the order of their slots.** -/
theorem lt_of_answerSlot {k k' : ℕ} {j j' : Fin A.slots}
    (h : answerSlot A C₁ k = some j) (h' : answerSlot A C₁ k' = some j') (hk : k' < k) :
    (j' : ℕ) < j := by
  rw [answerSlot_eq_some A C₁ h, answerSlot_eq_some A C₁ h'] at hk
  have := Nat.lt_of_mul_lt_mul_right hk
  omega

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **At most `j` answer steps come before the answer step of slot `j`.** -/
theorem card_answerSteps_le {k : ℕ} {j : Fin A.slots}
    (h : answerSlot A C₁ k = some j) :
    ((Finset.range k).filter fun k' => answerSlot A C₁ k' ≠ none).card ≤ j := by
  classical
  have hinj : Set.InjOn (fun k' => ((answerSlot A C₁ k').map Fin.val).getD 0)
      ((Finset.range k).filter fun k' => answerSlot A C₁ k' ≠ none) := by
    intro k₁ hk₁ k₂ hk₂ he
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk₁ hk₂
    obtain ⟨j₁, hj₁⟩ := Option.ne_none_iff_exists'.1 hk₁.2
    obtain ⟨j₂, hj₂⟩ := Option.ne_none_iff_exists'.1 hk₂.2
    simp only [hj₁, hj₂, Option.map_some, Option.getD_some] at he
    rw [answerSlot_eq_some A C₁ hj₁, answerSlot_eq_some A C₁ hj₂, he]
  refine (Finset.card_le_card_of_injOn _ (fun k' hk' => ?_) hinj).trans (Finset.card_range j).le
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk'
  obtain ⟨j', hj'⟩ := Option.ne_none_iff_exists'.1 hk'.2
  simp only [Finset.coe_range, Set.mem_Iio, hj', Option.map_some, Option.getD_some]
  exact lt_of_answerSlot A C₁ h hj' hk'.1

variable (e : BitStr I J ≃ Bd) (d₂ : Req₂)
  (E : Expansion (Bits m) Bd (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

/-- **Off the answer steps the bridge algorithm sends the dummy.** -/
theorem bridgeAlg_req_of_none {k : Fin (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut
      C₁ id).depth) + kq) + 1)} (hk : answerSlot A C₁ k = none)
    (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) : (bridgeAlg e A C₁ F d₂ E kq d₀).req k w = d₂ := by
  change (match answerSlot A C₁ k with
    | none => d₂
    | some j => match (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j with
      | none => d₂
      | some r => (F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r).getD d₂) = d₂
  rw [hk]

/-- **Off the answer steps the bridge algorithm ignores the reply.** -/
theorem bridgeAlg_write_of_none {k : Fin (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut
      C₁ id).depth) + kq) + 1)} (hk : answerSlot A C₁ k = none) (x : Option Resp₂) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).write k x = Equiv.refl _ := by
  change (match answerSlot A C₁ k with
    | none => Equiv.refl _
    | some j => liftAbs e A C₁ F E kq d₀ (answerDelta A F j x)) = _
  rw [hk]

/-- **At the answer step of slot `j`, at most `j` non-dummy requests of the bridge algorithm came
before**, at every pattern of its requests. -/
theorem countND_le_of_answerSlot
    (L : Fin (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) +
      kq) + 1) → Req₂)
    (hL : ∀ k, ∃ w, L k = (bridgeAlg e A C₁ F d₂ E kq d₀).req k w) {k : ℕ}
    (hk : k ≤ ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) +
      kq) + 1)
    {j : Fin A.slots} (h : answerSlot A C₁ k = some j) :
    ReqQueryAlg.countND d₂ (requestsBefore (fun i => some (L i)) k) ≤ j := by
  classical
  refine (countND_requestsBefore_le_card d₂ L (fun k' => answerSlot A C₁ k' ≠ none) k hk
    fun k' _ hne hnone => hne ?_).trans (card_answerSteps_le A C₁ h)
  obtain ⟨w, hw⟩ := hL k'
  rw [hw, bridgeAlg_req_of_none A C₁ F e d₂ E kq d₀ hnone]

/-- **Every request of the bridge algorithm is the dummy or an outer request.** -/
theorem bridgeAlg_req_mem (k : Fin (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut
      C₁ id).depth) + kq) + 1)) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).req k w = d₂ ∨
      ∃ c r, F.outer c r = some ((bridgeAlg e A C₁ F d₂ E kq d₀).req k w) := by
  change (match answerSlot A C₁ k with
    | none => d₂
    | some j => match (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j with
      | none => d₂
      | some r => (F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r).getD d₂) =
      d₂ ∨ ∃ c r, F.outer c r = some (match answerSlot A C₁ k with
    | none => d₂
    | some j => match (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j with
      | none => d₂
      | some r => (F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r).getD d₂)
  rcases answerSlot A C₁ k with _ | j
  · exact Or.inl rfl
  · dsimp only
    rcases (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j with _ | r
    · exact Or.inl rfl
    · dsimp only
      rcases h : F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r with _ | q
      · exact Or.inl rfl
      · exact Or.inr ⟨_, r, h⟩

end AnswerSteps

/-! ### The bridge against the multi-user challenger -/

namespace Signature

variable {N n : ℕ} {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.PK] [DecidableEq T.PK]
  [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]
  {B : BaseSigner (Bits m) (BitStr I J) N T RMsg} {O : SignOracle B.core}
  {Req Resp Req₁ Resp₁ Ot : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁] {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA Ot)

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

variable (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ (MURequest O n) (MUResponse B.core)) (e : BitStr I J ≃ Bd)
  (d₂ : MURequest O n) (E : Expansion (Bits m) Bd (ExtReg A C₁ (MURequest O n) (MUResponse B.core)))
  (kq : ℕ) (d₀ : ExtReg A C₁ (MURequest O n) (MUResponse B.core))

omit [Fintype T.PK] [DecidableEq T.PK] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] in
/-- **The replies used against the bridge algorithm**: on the answer steps, the table's at the
count of the earlier non-dummy requests; elsewhere (where the bridge algorithm ignores the reply)
the multi-user challenger's at that count. -/
noncomputable def muBridgeReplies (keys : Fin n → B.KeyCoins) (Q' : ℕ) (ω : Fin Q' → O.Coins) :
    ℕ → List (MURequest O n) → MURequest O n → Option (MUResponse B.core) := fun k prev q =>
  if answerSlot A C₁ k = none then muReplyAfter O keys Q' ω (ReqQueryAlg.countND d₂ prev) q
  else A.tabAt (muTab A keys Q' ω) (ReqQueryAlg.countND d₂ prev) q

omit [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The table's replies and `muBridgeReplies` give the same bridge instance.** -/
theorem instLog_tabAt_eq (keys : Fin n → B.KeyCoins) (Q' : ℕ) (ω : Fin Q' → O.Coins) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).instLog (fun _ prev q => A.tabAt (muTab A keys Q' ω)
      (ReqQueryAlg.countND d₂ prev) q) =
      (bridgeAlg e A C₁ F d₂ E kq d₀).instLog (muBridgeReplies A C₁ d₂ keys Q' ω) := by
  refine (bridgeAlg e A C₁ F d₂ E kq d₀).instLog_congr_write fun k prev r hne x y => ?_
  have hk : answerSlot A C₁ k = none := by
    by_contra hk
    exact hne (by simp only [muBridgeReplies, if_neg hk])
  rw [bridgeAlg_write_of_none A C₁ F e d₂ E kq d₀ hk,
    bridgeAlg_write_of_none A C₁ F e d₂ E kq d₀ hk]

omit [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **`muBridgeReplies` are the count-indexed multi-user replies** at every pattern of requests of
the bridge algorithm. -/
theorem repliesAt_muBridgeReplies (keys : Fin n → B.KeyCoins) (Q' : ℕ) (ω : Fin Q' → O.Coins)
    (L : Fin (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) +
      kq) + 1) → MURequest O n)
    (hL : ∀ k, ∃ w, L k = (bridgeAlg e A C₁ F d₂ E kq d₀).req k w) :
    ReqQueryAlg.repliesAt (muBridgeReplies A C₁ d₂ keys Q' ω) L =
      ReqQueryAlg.repliesAt (fun _ prev r => muReplyAfter O keys Q' ω
        (ReqQueryAlg.countND d₂ prev) r) L := by
  funext k
  simp only [ReqQueryAlg.repliesAt, muBridgeReplies]
  split_ifs with hk
  · rfl
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hk
    have hc := countND_le_of_answerSlot A C₁ F e d₂ E kq d₀ L hL (k := k) k.2.le hj
    have hlt : ReqQueryAlg.countND d₂ (requestsBefore (fun i => some (L i)) k) < A.slots :=
      lt_of_le_of_lt hc j.2
    simp only [AdaptiveIAlg.tabAt, dif_pos hlt, muTab]

/-- **The bridge against the multi-user challenger** (module docstring): by the bridge statement
(`Quantum.extBridge`), for a trace-preserving adversary (`hTP`), outer requests never the dummy `d₂`
(`hout`), a dummy that is not a signing request (`hd₂`) and at least as many answered requests as
request points (`hQ`), the coin average of `simLaw` of the extraction run at the multi-user
challenger's table is that of the bridge algorithm answered as the challenger answers, coin `k` at
step `k`. -/
theorem sum_simLaw_extRun_muTab [Inhabited (MURequest O n)]
    (hTP : A.TracePreserving)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (hd₂ : ∀ i sm, d₂ ≠ .sign i sm) (keys : Fin n → B.KeyCoins) {Q' : ℕ}
    (hQ : ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) +
      kq) + 1 ≤ Q')
    (S : Set (BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ (MURequest O n) (MUResponse B.core)) kq ×
      DB (Bits m) Bd)) :
    ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω *
        simLaw e (extRun e A C₁ F E kq d₀ (muTab A keys Q' ω)) S =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).inst (muReplyAfter O keys Q' c)) S := by
  have h1 : ∀ ω, simLaw e (extRun e A C₁ F E kq d₀ (muTab A keys Q' ω)) S =
      simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).instLog
        (muBridgeReplies A C₁ d₂ keys Q' ω)) S := fun ω =>
    (extBridge e A C₁ F d₂ E kq d₀ hTP hout (muTab A keys Q' ω) S).trans (by rw [instLog_tabAt_eq])
  simp only [h1]
  exact sum_simLaw_muReplyAfter_of_agree O e keys hQ d₂ hd₂ (bridgeAlg e A C₁ F d₂ E kq d₀)
    (muBridgeReplies A C₁ d₂ keys Q') (fun L hL ω => repliesAt_muBridgeReplies A C₁ F e d₂ E kq d₀
      keys Q' ω L hL) S

/-! ### Any table agreeing with the multi-user challenger -/

/-- **The replies used against the bridge algorithm for a table `tab`**: as `muBridgeReplies`,
with `tab` on the answer steps. -/
noncomputable def bridgeRepliesTab (keys : Fin n → B.KeyCoins) (Q' : ℕ) (ω : Fin Q' → O.Coins)
    (tab : A.OuterTab (MURequest O n) (MUResponse B.core)) :
    ℕ → List (MURequest O n) → MURequest O n → Option (MUResponse B.core) := fun k prev q =>
  if answerSlot A C₁ k = none then muReplyAfter O keys Q' ω (ReqQueryAlg.countND d₂ prev) q
  else A.tabAt tab (ReqQueryAlg.countND d₂ prev) q

omit [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The table's replies and `bridgeRepliesTab` give the same bridge instance.** -/
theorem instLog_tabAt_eq_tab (keys : Fin n → B.KeyCoins) (Q' : ℕ) (ω : Fin Q' → O.Coins)
    (tab : A.OuterTab (MURequest O n) (MUResponse B.core)) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).instLog (fun _ prev q => A.tabAt tab
      (ReqQueryAlg.countND d₂ prev) q) =
      (bridgeAlg e A C₁ F d₂ E kq d₀).instLog (bridgeRepliesTab A C₁ d₂ keys Q' ω tab) := by
  refine (bridgeAlg e A C₁ F d₂ E kq d₀).instLog_congr_write fun k prev r hne x y => ?_
  have hk : answerSlot A C₁ k = none := by
    by_contra hk
    exact hne (by simp only [bridgeRepliesTab, if_neg hk])
  rw [bridgeAlg_write_of_none A C₁ F e d₂ E kq d₀ hk,
    bridgeAlg_write_of_none A C₁ F e d₂ E kq d₀ hk]

omit [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **For a table agreeing with the multi-user challenger's replies** (`htab`: below the number
of slots, on the dummy and the outer requests), `bridgeRepliesTab` are the count-indexed
multi-user replies at every pattern of requests of the bridge algorithm. -/
theorem repliesAt_bridgeRepliesTab (keys : Fin n → B.KeyCoins) (Q' : ℕ) (ω : Fin Q' → O.Coins)
    (tab : A.OuterTab (MURequest O n) (MUResponse B.core))
    (htab : ∀ (j : Fin A.slots) q, (q = d₂ ∨ ∃ c r, F.outer c r = some q) →
      tab j q = muReplyAfter O keys Q' ω j q)
    (L : Fin (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) +
      kq) + 1) → MURequest O n)
    (hL : ∀ k, ∃ w, L k = (bridgeAlg e A C₁ F d₂ E kq d₀).req k w) :
    ReqQueryAlg.repliesAt (bridgeRepliesTab A C₁ d₂ keys Q' ω tab) L =
      ReqQueryAlg.repliesAt (fun _ prev r => muReplyAfter O keys Q' ω
        (ReqQueryAlg.countND d₂ prev) r) L := by
  funext k
  simp only [ReqQueryAlg.repliesAt, bridgeRepliesTab]
  split_ifs with hk
  · rfl
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hk
    have hc := countND_le_of_answerSlot A C₁ F e d₂ E kq d₀ L hL (k := k) k.2.le hj
    have hlt : ReqQueryAlg.countND d₂ (requestsBefore (fun i => some (L i)) k) < A.slots :=
      lt_of_le_of_lt hc j.2
    simp only [AdaptiveIAlg.tabAt, dif_pos hlt]
    obtain ⟨w, hw⟩ := hL k
    refine htab _ _ ?_
    rw [hw]
    exact bridgeAlg_req_mem A C₁ F e d₂ E kq d₀ k w

/-- **The bridge against the multi-user challenger for a table agreeing with it**: by the bridge
statement (`Quantum.extBridge`), for a trace-preserving adversary (`hTP`), outer requests never the
dummy (`hout`), a dummy that is not a signing request (`hd₂`), at least as many answered requests as
request points (`hQ`), and a table agreeing with the multi-user challenger's replies at every coins
(`htab`), `simLaw` of the extraction run at the table is the coin average of `simLaw` of the bridge
algorithm answered as the multi-user challenger answers it. -/
theorem simLaw_extRun_tab_eq_sum [Inhabited (MURequest O n)]
    (hTP : A.TracePreserving)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (hd₂ : ∀ i sm, d₂ ≠ .sign i sm) (keys : Fin n → B.KeyCoins) {Q' : ℕ}
    (hQ : ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) +
      kq) + 1 ≤ Q')
    (tab : A.OuterTab (MURequest O n) (MUResponse B.core))
    (htab : ∀ ω (j : Fin A.slots) q, (q = d₂ ∨ ∃ c r, F.outer c r = some q) →
      tab j q = muReplyAfter O keys Q' ω j q)
    (S : Set (BaseGame.Tuple (Bits m) Bd (ExtReg A C₁ (MURequest O n) (MUResponse B.core)) kq ×
      DB (Bits m) Bd)) :
    simLaw e (extRun e A C₁ F E kq d₀ tab) S =
      ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
        simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).inst (muReplyAfter O keys Q' c)) S := by
  have h1 : ∀ ω, simLaw e (extRun e A C₁ F E kq d₀ tab) S =
      simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).instLog
        (bridgeRepliesTab A C₁ d₂ keys Q' ω tab)) S := fun ω =>
    (extBridge e A C₁ F d₂ E kq d₀ hTP hout tab S).trans
      (by rw [instLog_tabAt_eq_tab A C₁ F e d₂ E kq d₀ keys Q' ω tab])
  have hsum : simLaw e (extRun e A C₁ F E kq d₀ tab) S =
      ∑ ω, PMF.uniformOfFintype (Fin Q' → O.Coins) ω * simLaw e (extRun e A C₁ F E kq d₀ tab) S := by
    rw [← Finset.sum_mul, ← tsum_fintype (L := .unconditional _), PMF.tsum_coe, one_mul]
  rw [hsum, Finset.sum_congr rfl fun ω _ => congrArg _ (h1 ω)]
  exact sum_simLaw_muReplyAfter_of_agree O e keys hQ d₂ hd₂ (bridgeAlg e A C₁ F d₂ E kq d₀)
    (fun ω => bridgeRepliesTab A C₁ d₂ keys Q' ω tab) (fun L hL ω =>
      repliesAt_bridgeRepliesTab A C₁ F e d₂ E kq d₀ keys Q' ω tab (htab ω) L hL) S

end Signature

end GordieHowe
