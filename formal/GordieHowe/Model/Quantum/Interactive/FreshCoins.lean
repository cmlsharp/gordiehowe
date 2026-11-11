-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.InteractionFresh
public import GordieHowe.Model.Quantum.Interactive.ClassicalSimLogs
public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Model.Signature.RejectionRelay

@[expose] public section

/-!
# Challengers reading a fresh coin per request

A challenger (`Quantum.Challenger`) **reads fresh coins** (`Challenger.FreshCoins C U`) when its
coins are a uniform `Fin Q → U` and its reply to request number `j < Q` reads only the coin `j`,
through a kernel of the oracle, the history and the request. Every adversary's transcript law
(`QueryBoundedAdversary.transcriptLaw`) against a challenger that reads fresh coins and never
reprograms is the law against the classical **lazy** challenger answering each request from the
kernel averaged over a uniform coin (`transcriptLaw_some_eq_lazy`). So two such challengers with
the same averaged kernels give every adversary the same transcript law
(`transcriptLaw_eq_of_freshCoins`), although which coin a request reads depends on the adaptively
chosen requests before it, so that no fixed bijection of the coins relates them. The classical
step is the lazy sampling of `GordieHowe/Foundations/Probability/InteractionFresh.lean`.

- `isReq`, `entryOf`, `clHist Q h`: the coin-reading moves of the classical simulation (the
  requests), and the challenger's history read from a classical history (its first `Q` requests
  with their responses). `readCount_isReq`, `length_clHist`.
- `Challenger.FreshCoins C U`: the hypotheses; `FreshCoins.avg`: the averaged kernel.
- `lazyAt Q H Kbar`: the lazy classical challenger at the oracle `H` with averaged kernel `Kbar`;
  `lazyAt_congr`. `freshK`, `lazyK`, `idleRep`: its read kernels and its idle replies.
- `FreshCoins.classical`: the classical challenger at `H` reading fresh coins; `HistInv`,
  `histInv_append`, `FreshCoins.reply_classicalAt`: the challenger at `H` answers as it on the
  histories its replies support.
- `FreshCoins.exper_classicalAt`: the adversary's classical interaction with the challenger at `H`
  is the lazy one.
- `KindAlg.toOuterMeasure_outLaw_composeBothOut_congr_emb`: events of the composed registers that
  agree on the placed game registers have the same probability.
- `PMF.toOuterMeasure_congr_support`, `requestsBefore_movesOf`, `TrEvent`: events agreeing on the
  support, the requests of the logs of a classical history, the transcript event.
- `transcriptLaw_some_eq_lazy`, `transcriptLaw_eq_of_freshCoins`,
  `transcriptLaw_eq_bind_of_freshCoins`: the transcript law through the lazy challenger; the
  equality for equal averaged kernels; a family of challengers whose averaged kernel at request `j`
  reads a parameter `ρ j` has, averaged over a uniform `ρ`, the transcript law of the challenger
  whose kernel averages over the parameter too.
- `Signature.muChallengerAt O n keys Q tgt ρ`: the multi-user challenger whose request number `j`
  reads its coin `a j` when `tgt` holds of the request and the parameter `ρ j` otherwise.
  `muChallengerAt_noAssign`, `muKernel`, `muChallenger_freshCoins`, `muChallengerAt_freshCoins`.
  `Signature.transcriptLaw_muChallenger_eq_bind`: the transcript law against `muChallenger` is the
  average over a uniform `ρ` of the transcript laws against `muChallengerAt … ρ`.
-/

open scoped ENNReal BigOperators

namespace GordieHowe.Quantum

open Interaction (Hist readCount)

variable {X Y Req Resp : Type}

/-! ### The challenger's history in the classical simulation -/

/-- **The coin-reading moves of the classical simulation**: the requests (`some r`) read a coin,
the query slots (`none`) do not. -/
def isReq : Option Req → ℕ
  | none => 0
  | some _ => 1

/-- The entry of the challenger's history made by a round of the classical simulation: the request
with its response, for a request. -/
def entryOf (e : Option Req × (Option Resp × (X → Y))) : Option (HistoryEntry Req Resp) :=
  e.1.map fun r => ⟨r, e.2.1⟩

/-- **The challenger's history read from a classical history**: its first `Q` requests with their
responses. -/
def clHist (Q : ℕ) (h : Hist (Option Req) (Option Resp × (X → Y))) :
    List (HistoryEntry Req Resp) :=
  (h.filterMap entryOf).take Q

/-- The number of reads of a classical history is its number of requests. -/
theorem readCount_isReq (h : Hist (Option Req) (Option Resp × (X → Y))) :
    readCount isReq h = (Env.histReqs h).length := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    obtain ⟨_ | r, v⟩ := e <;>
      simp_all [readCount, Env.histReqs, isReq, Nat.add_comm]

/-- A classical history has one history entry per request. -/
theorem length_filterMap_entryOf (h : Hist (Option Req) (Option Resp × (X → Y))) :
    (h.filterMap entryOf).length = (Env.histReqs h).length := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    obtain ⟨_ | r, v⟩ := e <;> simp_all [Env.histReqs, entryOf, List.filterMap_cons]

/-- The history read from a classical history has `min |requests| Q` entries. -/
theorem length_clHist (Q : ℕ) (h : Hist (Option Req) (Option Resp × (X → Y))) :
    (clHist Q h).length = min (Env.histReqs h).length Q := by
  rw [clHist, List.length_take, length_filterMap_entryOf, min_comm]

/-- A query slot adds no history entry. -/
theorem filterMap_entryOf_append_none (h : Hist (Option Req) (Option Resp × (X → Y)))
    (v : Option Resp × (X → Y)) :
    (h ++ [(none, v)]).filterMap entryOf = h.filterMap entryOf := by
  simp [List.filterMap_append, entryOf]

/-- A request adds its entry with its response. -/
theorem filterMap_entryOf_append_some (h : Hist (Option Req) (Option Resp × (X → Y))) (r : Req)
    (v : Option Resp × (X → Y)) :
    (h ++ [(some r, v)]).filterMap entryOf = h.filterMap entryOf ++ [⟨r, v.1⟩] := by
  simp [List.filterMap_append, entryOf]

/-! ### Fresh coins -/

/-- **A challenger reading a fresh coin per request**: its coins are, along `equiv`, a uniform
`Fin Q → U`, and its response to a request after a history of `j < Q` entries, at every oracle,
is `kernel` of the oracle, the history and the request at the coin `j` only. -/
structure Challenger.FreshCoins (C : Challenger X Y Req Resp) (U : Type) [Fintype U]
    [Nonempty U] where
  /-- The coins as a function of the request number. -/
  equiv : C.Coins ≃ (Fin C.Q → U)
  /-- The coins are uniform. -/
  coins_eq : ∀ c, C.coins c = PMF.uniformOfFintype (Fin C.Q → U) (equiv c)
  /-- The response from one coin. -/
  kernel : (X → Y) → List (HistoryEntry Req Resp) → Req → U → Option Resp
  /-- The response reads the coin of its number only. -/
  respond_eq : ∀ H c hist r (hj : hist.length < C.Q),
    ((C.respond c hist r).run H).response = kernel H hist r (equiv c ⟨hist.length, hj⟩)

variable {U : Type} [Fintype U] [Nonempty U]

/-- **The averaged kernel**: the law of the response from a uniform coin. -/
noncomputable def Challenger.FreshCoins.avg {C : Challenger X Y Req Resp} (F : C.FreshCoins U)
    (H : X → Y) (hist : List (HistoryEntry Req Resp)) (r : Req) : PMF (Option Resp) :=
  (PMF.uniformOfFintype U).map (F.kernel H hist r)

/-- The replies to the query slots in the classical simulation of a challenger that never
reprograms at `H`: no response, the oracle `H`. -/
noncomputable def idleRep (H : X → Y) (_ : Hist (Option Req) (Option Resp × (X → Y)))
    (_ : Option Req) : PMF (Option Resp × (X → Y)) :=
  PMF.pure (none, H)

/-- The read kernel of the classical simulation from the responses `κ` of one coin. -/
noncomputable def freshK (Q : ℕ) (H : X → Y)
    (κ : List (HistoryEntry Req Resp) → Req → U → Option Resp)
    (h : Hist (Option Req) (Option Resp × (X → Y))) : Option Req → U → PMF (Option Resp × (X → Y))
  | none => fun _ => PMF.pure (none, H)
  | some r => fun u => PMF.pure (κ (clHist Q h) r u, H)

/-- The lazy read kernel from the averaged responses `Kbar`. -/
noncomputable def lazyK (Q : ℕ) (H : X → Y)
    (Kbar : List (HistoryEntry Req Resp) → Req → PMF (Option Resp))
    (h : Hist (Option Req) (Option Resp × (X → Y))) : Option Req → PMF (Option Resp × (X → Y))
  | none => PMF.pure (none, H)
  | some r => (Kbar (clHist Q h) r).map fun o => (o, H)

/-- **The lazy challenger at the oracle `H`**: the input `H`, a request after fewer than `Q`
requests answered from the averaged responses `Kbar` of the history read from the classical
history (`clHist`), every other move with no response; the oracle in force stays `H`. -/
noncomputable def lazyAt (Q : ℕ) (H : X → Y)
    (Kbar : List (HistoryEntry Req Resp) → Req → PMF (Option Resp)) :
    Interaction.Challenger Unit (X → Y) (Option Req) (Option Resp × (X → Y)) :=
  Interaction.lazy Q isReq H (lazyK Q H Kbar) (idleRep H)

/-- The lazy challenger reads its averaged kernel only at histories of fewer than `Q` entries. -/
theorem lazyAt_congr (Q : ℕ) (H : X → Y)
    {Kbar Kbar' : List (HistoryEntry Req Resp) → Req → PMF (Option Resp)}
    (hK : ∀ hist r, hist.length < Q → Kbar hist r = Kbar' hist r) :
    lazyAt Q H Kbar = lazyAt Q H Kbar' := by
  refine Interaction.lazy_congr isReq H (idleRep H) fun h e he hr => ?_
  rcases e with _ | r
  · simp [isReq] at he
  · rw [readCount_isReq] at hr
    simp only [lazyK]
    rw [hK _ _ (by rw [length_clHist]; omega)]

/-- The read kernel averaged over a uniform coin is the lazy read kernel of the averaged
responses. -/
theorem tsum_uniform_bind_freshK (Q : ℕ) (H : X → Y)
    (κ : List (HistoryEntry Req Resp) → Req → U → Option Resp)
    (h : Hist (Option Req) (Option Resp × (X → Y))) (e : Option Req) :
    (PMF.uniformOfFintype U).bind (freshK Q H κ h e) =
      lazyK Q H (fun hist r => (PMF.uniformOfFintype U).map (κ hist r)) h e := by
  rcases e with _ | r
  · simp [freshK, lazyK]
  · simp only [freshK, lazyK, PMF.map_comp]
    rw [← PMF.bind_pure_comp]
    rfl

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **The classical challenger reading fresh coins at `H`**, built from the kernel (with
`Interaction.Challenger.ofFresh`). -/
noncomputable def Challenger.FreshCoins.classical {C : Challenger X Y Req Resp}
    (F : C.FreshCoins U) (H : X → Y) :
    Interaction.Challenger (Fin C.Q → U) (X → Y) (Option Req) (Option Resp × (X → Y)) :=
  Interaction.Challenger.ofFresh C.Q isReq H (freshK C.Q H (F.kernel H)) (idleRep H)

/-- The challenger's state after the requests of a classical history holds the history read from
it. -/
def HistInv (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins)
    (h : Hist (Option Req) (Option Resp × (X → Y))) : Prop :=
  (C.stateAfter H c (Env.histReqs h)).hist = clHist C.Q h

/-- The empty history holds `HistInv`. -/
theorem histInv_nil (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins) :
    HistInv C H c [] := by
  simp [HistInv, clHist, Env.histReqs, Env.oracleIn_nil, Challenger.toPureEnv]

/-- **The supported replies keep the history read from the classical history**. -/
theorem histInv_append (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins)
    (h : Hist (Option Req) (Option Resp × (X → Y))) (e : Option Req)
    (v : Option Resp × (X → Y)) (hh : HistInv C H c h)
    (hv : v ∈ ((C.classicalAt H).reply c h e).support) : HistInv C H c (h ++ [(e, v)]) := by
  have hv' : v = C.toPureEnv.visReply (H, c) (Env.histReqs h) e :=
    (PMF.mem_support_pure_iff _ _).1 hv
  unfold HistInv at hh ⊢
  rw [Env.histReqs_append_singleton]
  rcases e with _ | r
  · rw [clHist, filterMap_entryOf_append_none]
    simpa [clHist] using hh
  · simp only [Option.toList_some]
    rw [clHist, filterMap_entryOf_append_some]
    have hlen := length_filterMap_entryOf h
    rw [Challenger.stateAfter, Env.oracleIn_append_singleton]
    by_cases hq : (Env.histReqs h).length < C.Q
    · rw [C.update_toPureEnv_of_lt _ _ _ hq]
      have hv1 : v.1 = C.toPureEnv.answerAfter (H, c) (Env.histReqs h) r := by
        rw [hv']
        rfl
      rw [hv1, C.answerAfter_toPureEnv_of_lt _ _ _ hq]
      have hh' : (C.toPureEnv.oracleIn (H, c) (Env.histReqs h)).hist = h.filterMap entryOf := by
        rw [← List.take_of_length_le (l := h.filterMap entryOf) (i := C.Q) (by omega)]
        exact hh
      simp only
      rw [hh', List.take_of_length_le (by simp; omega)]
    · rw [C.update_toPureEnv_of_le _ _ _ (not_lt.1 hq), List.take_append_of_le_length (by omega)]
      exact hh

/-- **The classical challenger at `H` answers as the fresh-coins challenger** at the coins read
along `equiv`, at every history whose requests leave the challenger's history read from it. -/
theorem Challenger.FreshCoins.reply_classicalAt {C : Challenger X Y Req Resp} (hC : C.NoAssign)
    (F : C.FreshCoins U) (H : X → Y) (c : C.Coins)
    (h : Hist (Option Req) (Option Resp × (X → Y))) (e : Option Req) (hh : HistInv C H c h) :
    (C.classicalAt H).reply c h e = (F.classical H).reply (F.equiv c) h e := by
  have hor : ∀ rs, OracleState.toOracle (C.toPureEnv.oracleIn (H, c) rs) = H := fun rs => by
    obtain ⟨h1, h2, -⟩ := hC.oracleIn H c rs
    change (C.toPureEnv.oracleIn (H, c) rs).base.reprogram (C.toPureEnv.oracleIn (H, c) rs).ass = H
    rw [h1, h2]
    rfl
  change PMF.pure (C.toPureEnv.visReply (H, c) (Env.histReqs h) e) = _
  simp only [Challenger.FreshCoins.classical, Interaction.Challenger.ofFresh, readCount_isReq]
  rcases e with _ | r
  · simp [Env.visReply, isReq, idleRep, hor]
  · by_cases hq : (Env.histReqs h).length < C.Q
    · have hc : isReq (some r) ≠ 0 ∧ (Env.histReqs h).length < C.Q := ⟨Nat.one_ne_zero, hq⟩
      rw [dite_eq_left_of_eq_true (eq_true hc)]
      simp only [Env.visReply, freshK, hor]
      have hl : (clHist C.Q h).length < C.Q := by rw [length_clHist]; omega
      have hidx : (⟨(clHist C.Q h).length, hl⟩ : Fin C.Q) = ⟨(Env.histReqs h).length, hq⟩ :=
        Fin.ext (by simp only [length_clHist]; omega)
      rw [hC.answerAfter_eq H c _ r hq, show (C.stateAfter H c (Env.histReqs h)).hist =
        clHist C.Q h from hh, F.respond_eq H c _ r hl, hidx]
    · rw [dite_eq_right_of_eq_false (eq_false fun h' => hq h'.2)]
      simp [Env.visReply, idleRep, hor, C.answerAfter_toPureEnv_of_le _ _ _ (not_lt.1 hq)]

/-- **The classical interaction with a challenger reading fresh coins is the lazy one**: at every
oracle `H`, against the challenger at `H` (`Challenger.classicalAt`) every strategy has the
experiment it has against the lazy challenger with the averaged kernel. -/
theorem Challenger.FreshCoins.exper_classicalAt {C : Challenger X Y Req Resp} (hC : C.NoAssign)
    (F : C.FreshCoins U) (H : X → Y) {O : Type*}
    (σ : Interaction.Strategy (X → Y) (Option Req) (Option Resp × (X → Y)) O) (k : ℕ) :
    Interaction.exper σ (C.classicalAt H) k = Interaction.exper σ (lazyAt C.Q H (F.avg H)) k := by
  have hcont : ∀ c, Interaction.cont σ (C.classicalAt H) c [] k =
      Interaction.cont σ (F.classical H) (F.equiv c) [] k := fun c =>
    Interaction.cont_congr_of_support σ (C.classicalAt H) (F.classical H) (HistInv C H c)
      (fun h m r hh hr => histInv_append C H c h m r hh hr) rfl
      (fun h m hh => F.reply_classicalAt hC H c h m hh) k [] (histInv_nil C H c)
  have h1 : Interaction.exper σ (C.classicalAt H) k = Interaction.exper σ (F.classical H) k := by
    ext x
    simp only [Interaction.exper, PMF.bind_apply, hcont]
    change ∑' c, C.coins c * _ = _
    simp only [F.coins_eq]
    exact F.equiv.tsum_eq (fun a => PMF.uniformOfFintype (Fin C.Q → U) a *
      Interaction.cont σ (F.classical H) a [] k x)
  rw [h1, Challenger.FreshCoins.classical,
    Interaction.exper_eq_lazy σ (Interaction.freshCoins_ofFresh _ _ _ _), lazyAt]
  congr 2
  funext h e
  exact tsum_uniform_bind_freshK C.Q H (F.kernel H) h e

/-! ### The transcript law -/

section Transcript

variable [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Nonempty X] [AddGroup Y]

/-- **Events agreeing on the placed game registers have the same probability**: two events of the
composed registers that hold together at every placement (`KindAlg.emb`) of the game registers. -/
theorem KindAlg.toOuterMeasure_outLaw_composeBothOut_congr_emb {O : Type}
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (C : Challenger X Y Req Resp) (H : X → Y) (P P' : B.CW C → Prop)
    (h : ∀ c r, P (B.emb C H c B.slots r).1 ↔ P' (B.emb C H c B.slots r).1) :
    ((B.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      ((B.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P' v} := by
  classical
  rw [B.toOuterMeasure_outLaw_composeBothOut_id C H P,
    B.toOuterMeasure_outLaw_composeBothOut_id C H P']
  congr 1
  refine Finset.sum_congr rfl fun c _ => congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
  exact if_congr (h c r) rfl rfl

/-- A distribution gives the same mass to two sets with the same points of its support. -/
theorem _root_.PMF.toOuterMeasure_congr_support {α : Type*} (p : PMF α) {s t : Set α}
    (h : ∀ x ∈ p.support, x ∈ s ↔ x ∈ t) : p.toOuterMeasure s = p.toOuterMeasure t := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ p.support
  · simp only [Set.indicator_apply, h x hx]
  · simp [Set.indicator_apply, (PMF.apply_eq_zero_iff _ _).2 hx]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [DecidableEq Req] in
/-- The requests of the logs read from a classical history are its requests. -/
theorem requestsBefore_movesOf (h : Hist (Option Req) (Option Resp × (X → Y))) {m : ℕ} :
    ∀ k ≤ m, k ≤ h.length →
      requestsBefore (Distinguisher.movesOf h : LogReg Req m) k = Env.histReqs (h.take k)
  | 0, _, _ => rfl
  | k + 1, hm, hl => by
    rw [requestsBefore_succ_of_lt _ (by omega), requestsBefore_movesOf h k (by omega) (by omega),
      List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      Env.histReqs_append_singleton]
    simp [Distinguisher.movesOf, List.getElem?_eq_getElem (show k < h.length by omega)]

/-- The event of the classical simulation that the strategy outputs `some o` with `(o, clHist Q h)`
the transcript `x`. -/
def TrEvent {O : Type} (Q : ℕ) (x : O × List (HistoryEntry Req Resp)) :
    Set (Hist (Option Req) (Option Resp × (X → Y)) × Option O) :=
  {p | ∃ o, p.2 = some o ∧ (o, clHist Q p.1) = x}

variable {O : Type} {t : ℕ}

/-- **The transcript law against a challenger reading fresh coins, through the lazy challenger**:
at every oracle `H`, the transcript `x` has the probability, averaged over the auxiliary input,
that the adversary's classical strategy against the lazy challenger with the averaged kernel
outputs `x.1` with the challenger's history `x.2` read from the classical history. -/
theorem transcriptLaw_some_eq_lazy {C : Challenger X Y Req Resp} (hC : C.NoAssign)
    (F : C.FreshCoins U) (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y)
    (x : O × List (HistoryEntry Req Resp)) :
    𝒜.transcriptLaw C H (some x) = ∑' a, 𝒜.aux a *
      (Interaction.exper (𝒜.alg a).toKindAlg.classicalSim (lazyAt C.Q H (F.avg H))
        (𝒜.alg a).slots).toOuterMeasure (TrEvent C.Q x) := by
  classical
  simp only [QueryBoundedAdversary.transcriptLaw, PMF.bind_apply]
  refine tsum_congr fun a => congrArg _ ?_
  set A := 𝒜.alg a
  have hset : ({some x} : Set (Option (O × List (HistoryEntry Req Resp)))) =
      {o | ∃ y ∈ o, y = x} := by
    ext o
    rcases o with _ | y <;> simp [eq_comm]
  rw [← PMF.toOuterMeasure_apply_singleton, hset,
    KindAlg.toOuterMeasure_outLaw_composeBothOut A.toKindAlg C _ H (· = x)]
  let S : O → LogReg Req A.slots → C.Coins → Prop := fun o lg c =>
    (o, (C.stateAfter H c (requestsBefore lg A.slots)).hist) = x
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_congr_emb A.toKindAlg C H _
    (fun v => S (A.toKindAlg.out v.adv.workspace) v.chal.logs v.chal.coins) (fun c r => by
      have hs := A.toKindAlg.regState_eq C H c (splitLogs r).2 (J := A.slots) A.slots le_rfl
      exact Iff.of_eq (congrArg (fun z => (A.toKindAlg.out (A.toKindAlg.emb C H c A.slots r).1.adv.workspace, z) = x)
        (congrArg ChallengerRecord.history hs))),
    A.toOuterMeasure_outLaw_composeBothOut_logs_coins C H S]
  rw [← F.exper_classicalAt hC H, Interaction.exper, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun c => congrArg _ ?_
  refine PMF.toOuterMeasure_congr_support _ fun p hp => ?_
  obtain ⟨hinv, hlen⟩ := Interaction.mem_support_cont_inv _ _ c (HistInv C H c)
    (fun h m r hh hr => histInv_append C H c h m r hh hr) _ [] p (histInv_nil C H c) hp
  simp only [List.length_nil, zero_add] at hlen
  have hreq : requestsBefore (Distinguisher.movesOf p.1 : LogReg Req A.slots) A.slots =
      Env.histReqs p.1 := by
    rw [requestsBefore_movesOf p.1 A.slots le_rfl (by omega), List.take_of_length_le (by omega)]
  simp only [TrEvent, Set.mem_ofPred_eq, S, hreq]
  rw [show (C.stateAfter H c (Env.histReqs p.1)).hist = clHist C.Q p.1 from hinv]

/-- **Two challengers reading fresh coins with the same averaged kernels give every adversary the
same transcript law** at every oracle `H`: neither reprograms, they answer the same number of
requests, and their averaged kernels agree at every history of fewer than `Q` entries. -/
theorem transcriptLaw_eq_of_freshCoins {C C' : Challenger X Y Req Resp} {U' : Type} [Fintype U']
    [Nonempty U'] (hC : C.NoAssign) (hC' : C'.NoAssign) (F : C.FreshCoins U)
    (F' : C'.FreshCoins U') (hQ : C.Q = C'.Q)
    (havg : ∀ H hist r, hist.length < C.Q → F.avg H hist r = F'.avg H hist r)
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y) :
    𝒜.transcriptLaw C H = 𝒜.transcriptLaw C' H := by
  refine PMF.ext_of_some fun x => ?_
  rw [transcriptLaw_some_eq_lazy hC F, transcriptLaw_some_eq_lazy hC' F', ← hQ,
    lazyAt_congr C.Q H (havg H)]

/-- **A family of challengers whose averaged kernel at request `j` reads a parameter `ρ j`**:
averaged over a uniform `ρ`, its transcript laws are the transcript law against a challenger whose
averaged kernel is the average over the parameter, `(uniform V).bind (G H hist r)`. -/
theorem transcriptLaw_eq_bind_of_freshCoins {V U' : Type} [Fintype V] [Nonempty V] [Fintype U']
    [Nonempty U'] (Q : ℕ) (Cρ : (Fin Q → V) → Challenger X Y Req Resp)
    (hCρ : ∀ ρ, (Cρ ρ).NoAssign) (Fρ : ∀ ρ, (Cρ ρ).FreshCoins U) (hQρ : ∀ ρ, (Cρ ρ).Q = Q)
    {C' : Challenger X Y Req Resp} (hC' : C'.NoAssign) (F' : C'.FreshCoins U') (hQ' : C'.Q = Q)
    (G : (X → Y) → List (HistoryEntry Req Resp) → Req → V → PMF (Option Resp))
    (hG : ∀ ρ H hist r (hj : hist.length < Q),
      (Fρ ρ).avg H hist r = G H hist r (ρ ⟨hist.length, hj⟩))
    (hG' : ∀ H hist r, hist.length < Q →
      F'.avg H hist r = (PMF.uniformOfFintype V).bind (G H hist r))
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y) :
    𝒜.transcriptLaw C' H =
      (PMF.uniformOfFintype (Fin Q → V)).bind fun ρ => 𝒜.transcriptLaw (Cρ ρ) H := by
  refine PMF.ext_of_some fun x => ?_
  rw [PMF.bind_apply, transcriptLaw_some_eq_lazy hC' F', hQ']
  simp only [transcriptLaw_some_eq_lazy (hCρ _) (Fρ _), hQρ]
  rw [tsum_mul_tsum_mul_comm]
  refine tsum_congr fun a => congrArg _ ?_
  set σ := (𝒜.alg a).toKindAlg.classicalSim
  set k := (𝒜.alg a).slots
  -- the challenger reading the parameter as its coins
  let K : Hist (Option Req) (Option Resp × (X → Y)) → Option Req → V →
      PMF (Option Resp × (X → Y)) := fun h e v => match e with
    | none => PMF.pure (none, H)
    | some r => (G H (clHist Q h) r v).map fun o => (o, H)
  let χ := Interaction.Challenger.ofFresh Q isReq H K (idleRep H)
  have hfr := Interaction.freshCoins_ofFresh (N := Q) isReq H K (idleRep H)
  have hlazy : Interaction.exper σ χ k = Interaction.exper σ (lazyAt Q H (F'.avg H)) k := by
    rw [Interaction.exper_eq_lazy σ hfr]
    congr 1
    refine Interaction.lazy_congr isReq H (idleRep H) fun h e he hr => ?_
    rcases e with _ | r
    · simp [isReq] at he
    · rw [readCount_isReq] at hr
      simp only [lazyK, K]
      rw [hG' H _ r (by rw [length_clHist]; omega), PMF.map_bind]
  rw [← hlazy, Interaction.exper, PMF.toOuterMeasure_bind_apply, ← hfr.coins]
  change _ = ∑' ρ, PMF.uniformOfFintype (Fin Q → V) ρ * _
  refine tsum_congr fun ρ => congrArg _ ?_
  have hc : Interaction.cont σ χ ρ [] k = Interaction.cont σ (lazyAt Q H ((Fρ ρ).avg H)) () [] k := by
    refine Interaction.cont_congr_of_support σ χ (lazyAt Q H ((Fρ ρ).avg H)) (fun _ => True)
      (fun _ _ _ _ _ => trivial) rfl (fun h e _ => ?_) k [] trivial
    simp only [χ, lazyAt, Interaction.Challenger.ofFresh, Interaction.lazy]
    rcases e with _ | r
    · simp [isReq]
    · by_cases hq : readCount isReq h < Q
      · have hc : isReq (some r) ≠ 0 ∧ readCount isReq h < Q := ⟨Nat.one_ne_zero, hq⟩
        rw [dite_eq_left_of_eq_true (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc)]
        rw [readCount_isReq] at hq
        have hl : (clHist Q h).length < Q := by rw [length_clHist]; omega
        have hidx : (⟨readCount isReq h, hc.2⟩ : Fin Q) = ⟨(clHist Q h).length, hl⟩ :=
          Fin.ext (by simp only [length_clHist, readCount_isReq]; omega)
        simp only [K, lazyK]
        rw [hG ρ H _ r hl, hidx]
      · have hc : ¬ (isReq (some r) ≠ 0 ∧ readCount isReq h < Q) := fun h' => hq h'.2
        rw [dite_eq_right_of_eq_false (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc)]
  rw [hc, Interaction.exper]
  change _ = ((PMF.pure ()).bind fun ω => Interaction.cont σ (lazyAt Q H ((Fρ ρ).avg H)) ω [] k).toOuterMeasure _
  rw [PMF.pure_bind]

end Transcript

end GordieHowe.Quantum

/-! ### The multi-user challenger -/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature

variable {X Y : Type} {TB : SchemeTypes}
  {B : BaseScheme X Y TB} (O : SignOracle B) (n : ℕ)

variable [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]

/-- **The multi-user challenger with a parameter for the other requests**: as `muChallenger`,
except that a signing request `r` numbered `j < Q` is signed with the coin `a j` when `tgt r` holds
and with the parameter `ρ j` otherwise. -/
noncomputable def muChallengerAt (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (tgt : MURequest O n → Bool) (ρ : Fin Q → O.Coins) :
    Challenger X Y (MURequest O n) (MUResponse B) where
  Coins := Fin Q → O.Coins
  coins := PMF.uniformOfFintype _
  Q := Q
  q := O.q
  respond ω hist r :=
    if h : hist.length < Q then
      match r with
      | .publicKey i => .pure ⟨some (.publicKey (B.pk (keys i))), []⟩
      | .sign i sm =>
        (O.sign (B.keyGen (keys i)) sm
          (if tgt (.sign i sm) then ω ⟨hist.length, h⟩ else ρ ⟨hist.length, h⟩)).bind fun o =>
          .pure ⟨o.map .signature, []⟩
      | .corrupt i => .pure ⟨some (.keyCoins (keys i)), []⟩
    else .pure ⟨none, []⟩
  respond_queries ω hist r H := by
    split_ifs with h
    · rcases r with i | ⟨i, sm⟩ | i
      · simp
      · dsimp only
        rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
        exact O.sign_queries _ _ _ H
      · simp
    · simp

variable [Fintype O.SMsg] [DecidableEq O.SMsg]

variable {O n}

omit [Fintype O.SMsg] [DecidableEq O.SMsg] in
/-- **The multi-user challenger with a parameter never reprograms.** -/
theorem muChallengerAt_noAssign (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (tgt : MURequest O n → Bool) (ρ : Fin Q → O.Coins) :
    (muChallengerAt O n keys Q tgt ρ).NoAssign := by
  intro c hist r G
  simp only [muChallengerAt]
  split_ifs
  · rcases r with i | ⟨i, sm⟩ | i <;> simp [OracleProg.run_bind]
  · rfl

/-- The response of the multi-user challenger at the oracle `H` from the coin `u`. -/
noncomputable def muKernel (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y)
    (hist : List (HistoryEntry (MURequest O n) (MUResponse B))) (r : MURequest O n)
    (u : O.Coins) : Option (MUResponse B) :=
  (((muChallenger O n keys Q).respond (fun _ => u) hist r).run H).response

/-- **The multi-user challenger reads a fresh coin per request.** -/
noncomputable def muChallenger_freshCoins (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (muChallenger O n keys Q).FreshCoins O.Coins where
  equiv := Equiv.refl _
  coins_eq _ := rfl
  kernel := muKernel keys Q
  respond_eq H c hist r hj := by
    simp only [muKernel, muChallenger]
    rcases r <;> rfl

/-- **The multi-user challenger with a parameter reads a fresh coin per request**: the response
of `muChallenger` at the coin `u` when `tgt` holds and at the parameter otherwise. -/
noncomputable def muChallengerAt_freshCoins (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (tgt : MURequest O n → Bool) (ρ : Fin Q → O.Coins) :
    (muChallengerAt O n keys Q tgt ρ).FreshCoins O.Coins where
  equiv := Equiv.refl _
  coins_eq _ := rfl
  kernel H hist r u := (((muChallengerAt O n keys Q tgt ρ).respond (fun _ => u) hist r).run H).response
  respond_eq H c hist r hj := by
    simp only [muChallengerAt]
    rcases r <;> rfl

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] {Out : Type} {t : ℕ}

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

/-- **The multi-user transcript law, the other requests' coins drawn outside**: at every oracle
`H`, the transcript law of every adversary against `muChallenger` is the average over a uniform
parameter `ρ` of its transcript laws against `muChallengerAt … tgt ρ`, which signs the requests
outside `tgt` with `ρ`. -/
theorem transcriptLaw_muChallenger_eq_bind (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (tgt : MURequest O n → Bool)
    (𝒜 : QueryBoundedAdversary X Y (MURequest O n) (MUResponse B) Out t) (H : X → Y) :
    𝒜.transcriptLaw (muChallenger O n keys Q) H =
      (PMF.uniformOfFintype (Fin Q → O.Coins)).bind fun ρ =>
        𝒜.transcriptLaw (muChallengerAt O n keys Q tgt ρ) H := by
  refine transcriptLaw_eq_bind_of_freshCoins Q (muChallengerAt O n keys Q tgt)
    (muChallengerAt_noAssign keys Q tgt) (muChallengerAt_freshCoins keys Q tgt) (fun _ => rfl)
    (muChallenger_noAssign O keys Q) (muChallenger_freshCoins keys Q) rfl
    (fun H hist r v => (PMF.uniformOfFintype O.Coins).map fun u =>
      muKernel keys Q H hist r (if tgt r then u else v)) (fun ρ H hist r hj => ?_)
    (fun H hist r hj => ?_) 𝒜 H
  · simp only [Challenger.FreshCoins.avg, muChallengerAt_freshCoins]
    congr 1
    funext u
    simp only [muKernel, muChallengerAt, muChallenger, hj, dite_true]
    rcases r with i | ⟨i, sm⟩ | i
    · rfl
    · dsimp only
    · rfl
  · simp only [Challenger.FreshCoins.avg, muChallenger_freshCoins]
    cases tgt r
    · have hc : ∀ v, PMF.map (fun _ => muKernel keys Q H hist r v)
          (PMF.uniformOfFintype O.Coins) = PMF.pure (muKernel keys Q H hist r v) :=
        fun v => PMF.map_const _ _
      simp only [Bool.false_eq_true, ite_false, hc]
      exact (PMF.bind_pure_comp _ _).symm
    · simp only [ite_true, PMF.bind_const]

/-- **`transcriptLaw_muChallenger_eq_bind` on events** of the output and the history. -/
theorem toOuterMeasure_transcriptLaw_muChallenger (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (tgt : MURequest O n → Bool)
    (𝒜 : QueryBoundedAdversary X Y (MURequest O n) (MUResponse B) Out t) (H : X → Y)
    (E : Set (Option (Out × List (HistoryEntry (MURequest O n) (MUResponse B))))) :
    (𝒜.transcriptLaw (muChallenger O n keys Q) H).toOuterMeasure E =
      ∑' ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
        (𝒜.transcriptLaw (muChallengerAt O n keys Q tgt ρ) H).toOuterMeasure E := by
  rw [transcriptLaw_muChallenger_eq_bind keys Q tgt, PMF.toOuterMeasure_bind_apply]

end GordieHowe.Signature
