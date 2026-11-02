-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.FreshCoins
public import GordieHowe.Model.RingSignature.RevealedReprogram
public import GordieHowe.Foundations.Probability.InteractionFreshTV

@[expose] public section

/-!
# Assigning challengers reading a fresh coin per request

A challenger **reads fresh coins with a key** (`Challenger.FreshCoinsIn C μK ζ`) when its coins
are, along an equivalence, a key `κ ← μK` and independent per-request coins `u_j ← ζ`, and its
reply (response and assignments) to request number `j < Q`, at every oracle in force, reads only
`κ` and `u_j` through a kernel of the oracle, the history and the request. The challenger may
assign. The adversary's transcript with the final oracle in force (`transcriptLawIn`) is then the
law of a classical experiment against the classical challenger `FreshCoinsIn.classical`, which
answers each request from the kernel at the oracle in force read off the classical history
(`curOr`), the oracle after it reprogrammed by the reply's assignments.

- `curOr H h`: the oracle in force read from a classical history (that of its last reply, `H`
  for the empty history). `curOr_nil`, `curOr_append`.
- `Challenger.FreshCoinsIn`: the hypotheses. `FreshCoinsIn.step`, `FreshCoinsIn.classical`: the
  classical challenger at `H`; `FreshCoinsIn.coins_classical`.
- `InvIn`, `invIn_nil`, `invIn_append`, `FreshCoinsIn.reply_classicalAt`: the challenger at `H`
  answers as the classical one on the histories its replies support.
- `FreshCoinsIn.cont_classicalAt`, `FreshCoinsIn.exper_classicalAt`: the adversary's classical
  interaction with the challenger at `H` is the interaction with `FreshCoinsIn.classical`.
- `TrInEvent`, `transcriptLawIn_some_eq`: an event of the answered transcript with the final oracle
  is an event of the classical experiment.
- `FreshCoinsIn.freshCoinsLaw_classical`, `FreshCoinsIn.bind_step`: the classical challenger
  reads fresh coins from its laws (`Interaction.FreshCoinsLaw`,
  `GordieHowe/Foundations/Probability/InteractionFreshTV.lean`), a read being the kernel's law
  mapped.
- `transcriptLawIn_some_le_add`, `PMF.toOuterMeasure_compl`,
  `transcriptLawIn_le_add_of_freshCoinsIn` (**the hybrid**): kernel laws within total variation
  `ε j` at request `j` give transcripts within `∑ j < Q, ε j` on every event (the hybrid of
  `Interaction.toOuterMeasure_exper_le_add`); `transcriptLawIn_le_add_of_freshCoinsIn'` (the
  other direction), `abs_transcriptLawIn_sub_le_of_freshCoinsIn` (two-sided, in the reals),
  `transcriptLawIn_eq_of_freshCoinsIn` (`ε = 0`), `runLawIn_le_add_of_freshCoinsIn` (a game's
  run).
-/

open scoped ENNReal BigOperators

namespace GordieHowe.Quantum

open Interaction (Hist readCount)

variable {X Y Req Resp K U : Type}

/-! ### The oracle in force in a classical history -/

/-- **The oracle in force read from a classical history**: the oracle of its last reply, `H` for
the empty history. -/
def curOr (H : X → Y) (h : Hist (Option Req) (Option Resp × (X → Y))) : X → Y :=
  (h.getLast?.map fun e => e.2.2).getD H

@[simp]
theorem curOr_nil (H : X → Y) : curOr (Req := Req) (Resp := Resp) H [] = H :=
  rfl

@[simp]
theorem curOr_append (H : X → Y) (h : Hist (Option Req) (Option Resp × (X → Y)))
    (e : Option Req × (Option Resp × (X → Y))) : curOr H (h ++ [e]) = e.2.2 := by
  simp [curOr]

/-! ### Fresh coins with a key -/

/-- **A challenger reading a key and a fresh coin per request** (module docstring): along `equiv`,
its coins are a key with law `μK` and independent coins `Fin Q → U` with law `ζ` each; its reply
to a request after a history of `j < Q` entries, at every oracle `O`, is `kernel` of the key, `O`,
the history and the request at the coin `j` only. -/
structure Challenger.FreshCoinsIn (C : Challenger X Y Req Resp) (μK : PMF K) (ζ : PMF U) where
  /-- The coins as a key and one coin per request. -/
  equiv : C.Coins ≃ K × (Fin C.Q → U)
  /-- The key and the coins are independent, the coins with law `ζ` each. -/
  coins_eq : ∀ c, C.coins c = μK (equiv c).1 * ∏ j, ζ ((equiv c).2 j)
  /-- The reply from the key and one coin. -/
  kernel : K → (X → Y) → List (HistoryEntry Req Resp) → Req → U → Reply X Y Resp
  /-- The reply reads the key and the coin of its number only. -/
  respond_eq : ∀ O c hist r (hj : hist.length < C.Q),
    (C.respond c hist r).run O = kernel (equiv c).1 O hist r ((equiv c).2 ⟨hist.length, hj⟩)

namespace Challenger.FreshCoinsIn

variable [DecidableEq X] [Fintype U] {C : Challenger X Y Req Resp} {μK : PMF K} {ζ : PMF U}

/-- **The classical reply to a request read from one coin**: the kernel at the oracle in force,
the response, and the oracle in force reprogrammed by the reply's assignments; a query slot gets
no response and keeps the oracle in force. -/
def step (Q : ℕ) (H : X → Y)
    (kern : (X → Y) → List (HistoryEntry Req Resp) → Req → U → Reply X Y Resp)
    (h : Hist (Option Req) (Option Resp × (X → Y))) : Option Req → U → Option Resp × (X → Y)
  | none => fun _ => (none, curOr H h)
  | some r => fun u =>
    ((kern (curOr H h) (clHist Q h) r u).response,
      (curOr H h).reprogram (kern (curOr H h) (clHist Q h) r u).assignments)

/-- **The classical challenger at the oracle `H`** of a challenger reading a key and fresh coins:
the key and the coins drawn, the input `H`; a request after fewer than `Q` requests answered by
`step` at the coin of its number, every other move with no response and the oracle in force
kept. -/
noncomputable def classical (F : C.FreshCoinsIn μK ζ) (H : X → Y) :
    Interaction.Challenger (K × (Fin C.Q → U)) (X → Y) (Option Req) (Option Resp × (X → Y)) where
  coins := μK.bind fun k => (PMF.pi fun _ => ζ).map fun a => (k, a)
  input _ := H
  reply p h e :=
    if hj : isReq e ≠ 0 ∧ readCount isReq h < C.Q then
      PMF.pure (step C.Q H (F.kernel p.1) h e (p.2 ⟨readCount isReq h, hj.2⟩))
    else PMF.pure (none, curOr H h)

/-- The law of the key and the coins of the classical challenger. -/
theorem coins_classical (F : C.FreshCoinsIn μK ζ) (H : X → Y) (k : K) (a : Fin C.Q → U) :
    (F.classical H).coins (k, a) = μK k * ∏ j, ζ (a j) := by
  classical
  change (μK.bind fun k => (PMF.pi fun _ => ζ).map fun a => (k, a)) (k, a) = _
  rw [PMF.bind_apply, tsum_eq_single k fun k' hk => ?_]
  · rw [PMF.map_apply, tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
    simp [PMF.pi_apply]
  · rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun b => by simp [Ne.symm hk], mul_zero]

end Challenger.FreshCoinsIn

/-! ### The challenger at `H` answers as the classical one -/

section Sim

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype U]
  {C : Challenger X Y Req Resp} {μK : PMF K} {ζ : PMF U}

/-- **The invariant of the classical simulation**: after the requests of a classical history, the
challenger's history is the one read from it and its oracle in force is the one read from it. -/
def InvIn (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins)
    (h : Hist (Option Req) (Option Resp × (X → Y))) : Prop :=
  HistInv C H c h ∧
    (OracleState.toOracle (C.stateAfter H c (Env.histReqs h)) : X → Y) = curOr H h

/-- The empty history holds `InvIn`. -/
theorem invIn_nil (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins) : InvIn C H c [] :=
  ⟨histInv_nil C H c, rfl⟩

/-- **The supported replies keep the invariant.** -/
theorem invIn_append (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins)
    (h : Hist (Option Req) (Option Resp × (X → Y))) (e : Option Req) (v : Option Resp × (X → Y))
    (hh : InvIn C H c h) (hv : v ∈ ((C.classicalAt H).reply c h e).support) :
    InvIn C H c (h ++ [(e, v)]) := by
  refine ⟨histInv_append C H c h e v hh.1 hv, ?_⟩
  have hv' : v = C.toPureEnv.visReply (H, c) (Env.histReqs h) e :=
    (PMF.mem_support_pure_iff _ _).1 hv
  rw [curOr_append, Env.histReqs_append_singleton, hv']
  rcases e with _ | r
  · simp [Env.visReply, Challenger.stateAfter]
  · rfl

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype U] in
/-- The oracle in force of a challenger's state. -/
theorem toOracle_state (s : ChallengerState X Y Req Resp) :
    (OracleState.toOracle s : X → Y) = s.base.reprogram s.ass :=
  rfl

/-- **The challenger at `H` answers as the classical challenger** at the key and coins read along
`equiv`, on every history holding the invariant. -/
theorem Challenger.FreshCoinsIn.reply_classicalAt (F : C.FreshCoinsIn μK ζ) (H : X → Y)
    (c : C.Coins) (h : Hist (Option Req) (Option Resp × (X → Y))) (e : Option Req)
    (hh : InvIn C H c h) :
    (C.classicalAt H).reply c h e = (F.classical H).reply (F.equiv c) h e := by
  obtain ⟨hhist, hor⟩ := hh
  change PMF.pure (C.toPureEnv.visReply (H, c) (Env.histReqs h) e) = _
  simp only [Challenger.FreshCoinsIn.classical, readCount_isReq]
  rcases e with _ | r
  · simp only [isReq, ne_eq, not_true_eq_false, false_and, ↓reduceDIte]
    simp only [Env.visReply]
    rw [show OracleState.toOracle (C.toPureEnv.oracleIn (H, c) (Env.histReqs h)) = curOr H h
      from hor]
  · by_cases hq : (Env.histReqs h).length < C.Q
    · have hc : isReq (some r) ≠ 0 ∧ (Env.histReqs h).length < C.Q := ⟨Nat.one_ne_zero, hq⟩
      rw [dite_eq_left_of_eq_true (eq_true hc)]
      have hl : (clHist C.Q h).length < C.Q := by rw [length_clHist]; omega
      have hidx : (⟨(clHist C.Q h).length, hl⟩ : Fin C.Q) = ⟨(Env.histReqs h).length, hq⟩ :=
        Fin.ext (by simp only [length_clHist]; omega)
      have hst : (C.stateAfter H c (Env.histReqs h)).hist = clHist C.Q h := hhist
      have hor' : (C.stateAfter H c (Env.histReqs h)).base.reprogram
          (C.stateAfter H c (Env.histReqs h)).ass = curOr H h := hor
      have hrun := F.respond_eq (curOr H h) c (clHist C.Q h) r hl
      rw [hidx] at hrun
      simp only [Env.visReply, Challenger.FreshCoinsIn.step]
      congr 2
      · rw [C.answerAfter_toPureEnv_of_lt _ _ _ hq]
        change ((C.respond c (C.stateAfter H c (Env.histReqs h)).hist r).run
          ((C.stateAfter H c (Env.histReqs h)).base.reprogram
            (C.stateAfter H c (Env.histReqs h)).ass)).response = _
        rw [hst, hor', hrun]
      · rw [Env.oracleIn_append_singleton, C.update_toPureEnv_of_lt _ _ _ hq]
        change (C.stateAfter H c (Env.histReqs h)).base.reprogram
          ((C.stateAfter H c (Env.histReqs h)).ass ++
            ((C.respond c (C.stateAfter H c (Env.histReqs h)).hist r).run
              ((C.stateAfter H c (Env.histReqs h)).base.reprogram
                (C.stateAfter H c (Env.histReqs h)).ass)).assignments) = _
        rw [QROM.reprogram_append, hor', hst, hrun]
    · rw [dite_eq_right_of_eq_false (eq_false fun h' => hq h'.2)]
      simp only [Env.visReply]
      rw [C.answerAfter_toPureEnv_of_le _ _ _ (not_lt.1 hq), Env.oracleIn_append_singleton,
        C.update_toPureEnv_of_le _ _ _ (not_lt.1 hq)]
      rw [show OracleState.toOracle (C.toPureEnv.oracleIn (H, c) (Env.histReqs h)) = curOr H h
        from hor]

/-- **The classical continuation against the challenger at `H` is the classical challenger's** at
the key and coins read along `equiv`. -/
theorem Challenger.FreshCoinsIn.cont_classicalAt (F : C.FreshCoinsIn μK ζ) (H : X → Y)
    {O : Type*} (σ : Interaction.Strategy (X → Y) (Option Req) (Option Resp × (X → Y)) O)
    (c : C.Coins) (k : ℕ) :
    Interaction.cont σ (C.classicalAt H) c [] k =
      Interaction.cont σ (F.classical H) (F.equiv c) [] k :=
  Interaction.cont_congr_of_support σ (C.classicalAt H) (F.classical H) (InvIn C H c)
    (fun h m r hh hr => invIn_append C H c h m r hh hr) rfl
    (fun h m hh => F.reply_classicalAt H c h m hh) k [] (invIn_nil C H c)

/-- **The classical interaction with the challenger at `H` is the interaction with the classical
challenger** (`FreshCoinsIn.classical`). -/
theorem Challenger.FreshCoinsIn.exper_classicalAt (F : C.FreshCoinsIn μK ζ) (H : X → Y)
    {O : Type*} (σ : Interaction.Strategy (X → Y) (Option Req) (Option Resp × (X → Y)) O)
    (k : ℕ) : Interaction.exper σ (C.classicalAt H) k = Interaction.exper σ (F.classical H) k := by
  ext x
  simp only [Interaction.exper, PMF.bind_apply, F.cont_classicalAt H σ]
  change ∑' c, C.coins c * _ = _
  rw [← F.equiv.symm.tsum_eq]
  refine tsum_congr fun p => ?_
  rw [F.coins_eq, Equiv.apply_symm_apply, ← F.coins_classical H p.1 p.2]

/-! ### The transcript with the final oracle -/

variable [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Nonempty X] [AddGroup Y] {O : Type} {t : ℕ}

/-- **The event of the classical experiment** that the strategy outputs `some o` with
`P' (o, the first Q requests, the oracle in force)`. -/
def TrInEvent (Q : ℕ) (H : X → Y) (P' : O × List Req × (X → Y) → Prop) :
    Set (Hist (Option Req) (Option Resp × (X → Y)) × Option O) :=
  {p | ∃ o, p.2 = some o ∧ P' (o, (Env.histReqs p.1).take Q, curOr H p.1)}

/-- **An event of the transcript with the final oracle is an event of the classical
experiment**: at every oracle `H`, against a challenger reading a key and fresh coins, the
transcript `some v` with `P' v` has the probability, averaged over the auxiliary input, of
`TrInEvent` in the experiment of the adversary's classical strategy against the classical
challenger. -/
theorem transcriptLawIn_some_eq (F : C.FreshCoinsIn μK ζ)
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y) (P' : O × List Req × (X → Y) → Prop) :
    (𝒜.transcriptLawIn C H).toOuterMeasure {o | ∃ v ∈ o, P' v} = ∑' a, 𝒜.aux a *
      (Interaction.exper (𝒜.alg a).toKindAlg.classicalSim (F.classical H)
        (𝒜.alg a).slots).toOuterMeasure (TrInEvent C.Q H P') := by
  classical
  rw [QueryBoundedAdversary.transcriptLawIn, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => congrArg _ ?_
  set A := 𝒜.alg a
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut A.toKindAlg C _ H P']
  let S : O → LogReg Req A.slots → C.Coins → Prop := fun o lg c =>
    P' (o, (requests lg).take C.Q, C.toPureEnv.oracle (H, c) lg)
  erw [A.toOuterMeasure_outLaw_composeBothOut_logs_coins C H S]
  rw [← F.exper_classicalAt H, Interaction.exper, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun c => congrArg _ ?_
  refine PMF.toOuterMeasure_congr_support _ fun p hp => ?_
  obtain ⟨hinv, hlen⟩ := Interaction.mem_support_cont_inv _ _ c (InvIn C H c)
    (fun h m r hh hr => invIn_append C H c h m r hh hr) _ [] p (invIn_nil C H c) hp
  simp only [List.length_nil, zero_add] at hlen
  have hreq : requests (Distinguisher.movesOf p.1 : LogReg Req A.slots) = Env.histReqs p.1 := by
    rw [requests, requestsBefore_movesOf p.1 A.slots le_rfl (by omega),
      List.take_of_length_le (by omega)]
  have hor : C.toPureEnv.oracle (H, c) (Distinguisher.movesOf p.1 : LogReg Req A.slots) =
      curOr H p.1 := by
    rw [Env.oracle, hreq]
    exact hinv.2
  simp only [TrInEvent, Set.mem_ofPred_eq, S, hreq, hor]

end Sim

/-! ### The hybrid -/

section Hybrid

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype U] {U' : Type}
  [Fintype U'] {C C' : Challenger X Y Req Resp} {μK : PMF K} {ζ : PMF U} {ζ' : PMF U'}

omit [Fintype X] [Fintype Y] [Nonempty Y] in
/-- **The classical challenger reads fresh coins from its laws** (`Interaction.FreshCoinsLaw`),
its reads answered by `step` and its other moves keeping the oracle in force. -/
theorem Challenger.FreshCoinsIn.freshCoinsLaw_classical (F : C.FreshCoinsIn μK ζ) (H : X → Y) :
    Interaction.FreshCoinsLaw (F.classical H) isReq μK ζ H
      (fun κ h m u => PMF.pure (Challenger.FreshCoinsIn.step C.Q H (F.kernel κ) h m u))
      (fun _ h _ => PMF.pure (none, curOr H h)) where
  coins := rfl
  input _ := rfl
  read κ a h m hj hw := by
    simp only [Challenger.FreshCoinsIn.classical,
      dite_eq_left_of_eq_true (eq_true (And.intro hw hj))]
  noRead κ a h m hm := by
    have : ¬ (isReq m ≠ 0 ∧ readCount isReq h < C.Q) := by omega
    simp only [Challenger.FreshCoinsIn.classical, dite_eq_right_of_eq_false (eq_false this)]

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype U] in
/-- **A read of the classical challenger is the kernel's law mapped**: the response and the
oracle in force reprogrammed by the assignments. -/
theorem Challenger.FreshCoinsIn.bind_step (Q : ℕ) (H : X → Y) (ζ : PMF U)
    (kern : (X → Y) → List (HistoryEntry Req Resp) → Req → U → Reply X Y Resp)
    (h : Hist (Option Req) (Option Resp × (X → Y))) (r : Req) :
    ζ.bind (fun u => PMF.pure (Challenger.FreshCoinsIn.step Q H kern h (some r) u)) =
      (ζ.map (kern (curOr H h) (clHist Q h) r)).map
        fun rep => (rep.response, (curOr H h).reprogram rep.assignments) := by
  rw [PMF.map_comp, ← PMF.bind_pure_comp]
  rfl

variable [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Nonempty X] [AddGroup Y] {O : Type} {t : ℕ}

/-- **The hybrid on events of answered transcripts** (`transcriptLawIn_le_add_of_freshCoinsIn`
for the events `some v` with `P' v`). -/
theorem transcriptLawIn_some_le_add (F : C.FreshCoinsIn μK ζ) (F' : C'.FreshCoinsIn μK ζ')
    (hQ : C.Q = C'.Q) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ κ O hist r, hist.length < C.Q →
      ENNReal.ofReal (PMF.tvDist (ζ.map (F.kernel κ O hist r)) (ζ'.map (F'.kernel κ O hist r)))
        ≤ ε hist.length)
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y)
    (P' : O × List Req × (X → Y) → Prop) :
    (𝒜.transcriptLawIn C H).toOuterMeasure {o | ∃ v ∈ o, P' v} ≤
      (𝒜.transcriptLawIn C' H).toOuterMeasure {o | ∃ v ∈ o, P' v} +
        ∑ j ∈ Finset.range C.Q, ε j := by
  obtain ⟨Coins', coins', Q', q', resp', rq'⟩ := C'
  change C.Q = Q' at hQ
  subst hQ
  rw [transcriptLawIn_some_eq F, transcriptLawIn_some_eq F']
  have hyb : ∀ a, (Interaction.exper (𝒜.alg a).toKindAlg.classicalSim (F.classical H)
      (𝒜.alg a).slots).toOuterMeasure (TrInEvent C.Q H P') ≤
      (Interaction.exper (𝒜.alg a).toKindAlg.classicalSim (F'.classical H)
        (𝒜.alg a).slots).toOuterMeasure (TrInEvent C.Q H P') + ∑ j ∈ Finset.range C.Q, ε j :=
    fun a => Interaction.toOuterMeasure_exper_le_add _ (F.freshCoinsLaw_classical H)
      (F'.freshCoinsLaw_classical H) ε (fun κ h m hw hj => by
        rcases m with _ | r
        · exact absurd rfl hw
        · rw [Challenger.FreshCoinsIn.bind_step, Challenger.FreshCoinsIn.bind_step]
          have hl : (clHist C.Q h).length = readCount isReq h := by
            rw [length_clHist, readCount_isReq] at *
            omega
          refine le_trans (ENNReal.ofReal_le_ofReal (PMF.tvDist_map_le _ _ _)) ?_
          rw [← hl]
          exact hε κ _ _ r (by rw [hl]; exact hj)) _ _
  calc _ ≤ ∑' a, (𝒜.aux a * (Interaction.exper (𝒜.alg a).toKindAlg.classicalSim
          (F'.classical H) (𝒜.alg a).slots).toOuterMeasure (TrInEvent C.Q H P') +
          𝒜.aux a * ∑ j ∈ Finset.range C.Q, ε j) :=
        ENNReal.tsum_le_tsum fun a => by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (hyb a) zero_le
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A distribution gives a complement one minus the mass of the set. -/
theorem _root_.PMF.toOuterMeasure_compl {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure sᶜ = 1 - p.toOuterMeasure s := by
  have h : p.toOuterMeasure s + p.toOuterMeasure sᶜ = 1 := by
    simp only [PMF.toOuterMeasure_apply]
    rw [← ENNReal.tsum_add]
    simp only [Set.indicator_self_add_compl_apply]
    exact p.tsum_coe
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _)) (by rw [add_comm]; exact h)

/-- **Fresh coins for assigning challengers** (module docstring): against two challengers reading
a key with the same law and fresh coins, answering the same number of requests, whose kernel
laws at every key, oracle and history of fewer than `Q` entries are within total variation
`ε j` at the request number `j`, the transcript of every adversary with the answered requests
and the final oracle in force lies in an event with probability at most the other's plus
`∑ j < Q, ε j`. -/
theorem transcriptLawIn_le_add_of_freshCoinsIn (F : C.FreshCoinsIn μK ζ)
    (F' : C'.FreshCoinsIn μK ζ') (hQ : C.Q = C'.Q) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ κ O hist r, hist.length < C.Q →
      ENNReal.ofReal (PMF.tvDist (ζ.map (F.kernel κ O hist r)) (ζ'.map (F'.kernel κ O hist r)))
        ≤ ε hist.length)
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y)
    (S : Set (Option (O × List Req × (X → Y)))) :
    (𝒜.transcriptLawIn C H).toOuterMeasure S ≤
      (𝒜.transcriptLawIn C' H).toOuterMeasure S + ∑ j ∈ Finset.range C.Q, ε j := by
  by_cases hS : none ∈ S
  · have hset : S = {o | ∃ v ∈ o, some v ∉ S}ᶜ := by
      ext o
      rcases o with _ | v
      · simp [hS]
      · exact ⟨fun h ⟨w, hw, hn⟩ => by cases hw; exact hn h, fun h => by
          by_contra hn
          exact h ⟨v, rfl, hn⟩⟩
    have hε' : ∀ κ O hist r, hist.length < C'.Q →
        ENNReal.ofReal (PMF.tvDist (ζ'.map (F'.kernel κ O hist r))
          (ζ.map (F.kernel κ O hist r))) ≤ ε hist.length := fun κ O hist r hl => by
      rw [PMF.tvDist_comm]
      exact hε κ O hist r (hQ ▸ hl)
    have hrev := transcriptLawIn_some_le_add F' F hQ.symm ε hε' 𝒜 H fun v => some v ∉ S
    rw [← hQ] at hrev
    rw [hset, PMF.toOuterMeasure_compl, PMF.toOuterMeasure_compl, tsub_le_iff_right]
    calc (1 : ℝ≥0∞) ≤ (1 - (𝒜.transcriptLawIn C' H).toOuterMeasure {o | ∃ v ∈ o, some v ∉ S}) +
          (𝒜.transcriptLawIn C' H).toOuterMeasure {o | ∃ v ∈ o, some v ∉ S} := le_tsub_add
      _ ≤ _ := by
          rw [add_assoc]
          gcongr
          rw [add_comm]
          exact hrev
  · have hset : S = {o | ∃ v ∈ o, some v ∈ S} := by
      ext o
      rcases o with _ | v
      · simp [hS]
      · exact ⟨fun h => ⟨v, rfl, h⟩, fun ⟨w, hw, h⟩ => by cases hw; exact h⟩
    rw [hset]
    exact transcriptLawIn_some_le_add F F' hQ ε hε 𝒜 H _

/-- **The other direction** of `transcriptLawIn_le_add_of_freshCoinsIn`. -/
theorem transcriptLawIn_le_add_of_freshCoinsIn' (F : C.FreshCoinsIn μK ζ)
    (F' : C'.FreshCoinsIn μK ζ') (hQ : C.Q = C'.Q) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ κ O hist r, hist.length < C.Q →
      ENNReal.ofReal (PMF.tvDist (ζ.map (F.kernel κ O hist r)) (ζ'.map (F'.kernel κ O hist r)))
        ≤ ε hist.length)
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y)
    (S : Set (Option (O × List Req × (X → Y)))) :
    (𝒜.transcriptLawIn C' H).toOuterMeasure S ≤
      (𝒜.transcriptLawIn C H).toOuterMeasure S + ∑ j ∈ Finset.range C.Q, ε j := by
  have h := transcriptLawIn_le_add_of_freshCoinsIn F' F hQ.symm ε (fun κ O hist r hl => by
    rw [PMF.tvDist_comm]
    exact hε κ O hist r (hQ ▸ hl)) 𝒜 H S
  rwa [← hQ] at h

/-- **The two-sided bound** of `transcriptLawIn_le_add_of_freshCoinsIn`, in the reals, for a
finite total `∑ j < Q, ε j`. -/
theorem abs_transcriptLawIn_sub_le_of_freshCoinsIn (F : C.FreshCoinsIn μK ζ)
    (F' : C'.FreshCoinsIn μK ζ') (hQ : C.Q = C'.Q) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ κ O hist r, hist.length < C.Q →
      ENNReal.ofReal (PMF.tvDist (ζ.map (F.kernel κ O hist r)) (ζ'.map (F'.kernel κ O hist r)))
        ≤ ε hist.length) (hfin : ∑ j ∈ Finset.range C.Q, ε j ≠ ⊤)
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y)
    (S : Set (Option (O × List Req × (X → Y)))) :
    |((𝒜.transcriptLawIn C H).toOuterMeasure S).toReal -
        ((𝒜.transcriptLawIn C' H).toOuterMeasure S).toReal| ≤
      (∑ j ∈ Finset.range C.Q, ε j).toReal := by
  have h1 := transcriptLawIn_le_add_of_freshCoinsIn F F' hQ ε hε 𝒜 H S
  have h2 := transcriptLawIn_le_add_of_freshCoinsIn' F F' hQ ε hε 𝒜 H S
  have ha : (𝒜.transcriptLawIn C H).toOuterMeasure S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  have hb : (𝒜.transcriptLawIn C' H).toOuterMeasure S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  have r1 := (ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.2 ⟨hb, hfin⟩)).2 h1
  have r2 := (ENNReal.toReal_le_toReal hb (ENNReal.add_ne_top.2 ⟨ha, hfin⟩)).2 h2
  rw [ENNReal.toReal_add hb hfin] at r1
  rw [ENNReal.toReal_add ha hfin] at r2
  rw [abs_le]
  constructor <;> linarith

/-- **Equal kernel laws give equal transcript laws** (`ε = 0`). -/
theorem transcriptLawIn_eq_of_freshCoinsIn (F : C.FreshCoinsIn μK ζ)
    (F' : C'.FreshCoinsIn μK ζ') (hQ : C.Q = C'.Q)
    (hK : ∀ κ O hist r, hist.length < C.Q →
      ζ.map (F.kernel κ O hist r) = ζ'.map (F'.kernel κ O hist r))
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y) :
    𝒜.transcriptLawIn C H = 𝒜.transcriptLawIn C' H := by
  have hε : ∀ κ O hist r, hist.length < C.Q →
      ENNReal.ofReal (PMF.tvDist (ζ.map (F.kernel κ O hist r)) (ζ'.map (F'.kernel κ O hist r)))
        ≤ (fun _ => (0 : ℝ≥0∞)) hist.length := fun κ O hist r hl => by
    rw [hK κ O hist r hl, PMF.tvDist_self, ENNReal.ofReal_zero]
  refine PMF.ext fun x => ?_
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton]
  refine le_antisymm ?_ ?_
  · simpa using transcriptLawIn_le_add_of_freshCoinsIn F F' hQ (fun _ => 0) hε 𝒜 H {x}
  · simpa using transcriptLawIn_le_add_of_freshCoinsIn' F F' hQ (fun _ => 0) hε 𝒜 H {x}

/-- **The hybrid for a game's run** (`RingSignature.runLawIn`): with start draws `k`, for every
`k` challengers reading a key and fresh coins as in `transcriptLawIn_le_add_of_freshCoinsIn`,
with `Q` requests and the same bounds `ε`, the runs differ on every event by at most
`∑ j < Q, ε j`. -/
theorem runLawIn_le_add_of_freshCoinsIn {Kd : Type} [Fintype Kd] [Nonempty Kd]
    {Cd Cd' : Kd → Challenger X Y Req Resp} (F : ∀ k, (Cd k).FreshCoinsIn μK ζ)
    (F' : ∀ k, (Cd' k).FreshCoinsIn μK ζ') {Q : ℕ} (hQ : ∀ k, (Cd k).Q = Q)
    (hQ' : ∀ k, (Cd' k).Q = Q) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ k κ O hist r, hist.length < Q →
      ENNReal.ofReal (PMF.tvDist (ζ.map ((F k).kernel κ O hist r))
        (ζ'.map ((F' k).kernel κ O hist r))) ≤ ε hist.length)
    (A : Kd → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (E : Set (Kd × (X → Y) × Option (O × List Req × (X → Y)))) :
    (RingSignature.runLawIn A Cd).toOuterMeasure E ≤
      (RingSignature.runLawIn A Cd').toOuterMeasure E + ∑ j ∈ Finset.range Q, ε j := by
  rw [RingSignature.toOuterMeasure_runLawIn, RingSignature.toOuterMeasure_runLawIn]
  have hstep : ∀ k H, ((A k H).transcriptLawIn (Cd k) H).toOuterMeasure {o | (k, H, o) ∈ E} ≤
      ((A k H).transcriptLawIn (Cd' k) H).toOuterMeasure {o | (k, H, o) ∈ E} +
        ∑ j ∈ Finset.range Q, ε j := fun k H => by
    have h := transcriptLawIn_le_add_of_freshCoinsIn (F k) (F' k) ((hQ k).trans (hQ' k).symm) ε
      (fun κ O hist r hl => hε k κ O hist r (hQ k ▸ hl)) (A k H) H {o | (k, H, o) ∈ E}
    rwa [hQ k] at h
  have avg : ∀ {β : Type} (p : PMF β) (x y : β → ℝ≥0∞) (s : ℝ≥0∞), (∀ b, x b ≤ y b + s) →
      ∑' b, p b * x b ≤ ∑' b, p b * y b + s := fun p x y s h => by
    calc _ ≤ ∑' b, (p b * y b + p b * s) := ENNReal.tsum_le_tsum fun b => by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left (h b) zero_le
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  exact avg _ _ _ _ fun k => avg _ _ _ _ fun H => hstep k H

end Hybrid

end GordieHowe.Quantum
