-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Absorb
public import GordieHowe.Model.Quantum.Interactive.ZeroKnowledge
public import GordieHowe.Model.Quantum.Pure.GameTape

@[expose] public section

/-!
# Identical until bad, one draw per request

A classical challenger whose coins are keys `κ ← keys` and one independent draw `d_i ← draw` per
request, and which answers request number `i` from the keys and its own draw only
(`SplitChallenger`), is compared with the same challenger with other reply programs
(`SplitChallenger.withReply`). If at every keys, request number and request the two programs
differ with probability at most `ε` over that request's draw, every event of the adversary's
registers, the logs, the keys and the final oracle in force has probability against the first at
most its probability against the second plus `Q * ε`
(`SplitChallenger.toOuterMeasure_outLaw_le_add`): identical until bad, for a bad event of one
request's draw, with each request chosen adaptively by a quantum adversary.

- `Distinguisher.abs_sum_probOracleAt_withResponse_sub_le`: kernel replacement at one request of
  the pure game (`Distinguisher.abs_sum_withResponse_sub_le`) for an accepting set that reads the
  distinguisher's registers, the logs and the final oracle at the logs jointly (`LogLocal`).
- `KindAlg.prob_final_dilate`: the pure game of the dilated adversary gives every set of the mixed
  game's registers its probability in the mixed game (`KindAlg.acceptProbAt_dilate` for a set).
- `KindAlg.unitOut`: the algorithm with its output forgotten; its shape is the algorithm's
  (`unitOut_toShape`).
- `SplitChallenger.toOuterMeasure_outLaw_eq`: an event of the composition is the coin average of
  that pure game against the challenger as an environment whose state is the oracle in force
  (`SplitChallenger.oracleEnv`, bisimilar to `Challenger.toPureEnv`).
- `sum_prod_toReal_mul_eq_sum_update`, `SplitChallenger.abs_evProb_hybReply_sub_le`,
  `SplitChallenger.evProb_le_add`: the hybrid over `j = 0, …, Q`, with requests below `j`
  answered by `reply'`; at step `j` the draw of request `j` is resampled and replaced as a kernel.
-/

open Finset Matrix
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Split challengers -/

/-- **A classical challenger whose coins are keys and one draw per request**: keys `κ ← keys` and
one draw `d_i ← draw` per request, all independent; request number `i < Q` with request `r` is
answered by the classical oracle program `reply κ d_i i r`, which reads its own draw only and
makes at most `q` queries. -/
structure SplitChallenger (X Y Req Resp K D : Type) [Fintype K] [DecidableEq K] [Fintype D]
    [DecidableEq D] where
  /-- The law of the keys. -/
  keys : PMF K
  /-- The law of each request's draw. -/
  draw : PMF D
  /-- The number of requests answered. -/
  Q : ℕ
  /-- The number of classical queries per request. -/
  q : ℕ
  /-- The reply to request number `i` with request `r`, from the keys and its own draw. -/
  reply : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp)
  reply_queries : ∀ κ d i r H, ((reply κ d i r).trace H).length ≤ q

namespace SplitChallenger

variable {X Y Req Resp K D : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
  (S : SplitChallenger X Y Req Resp K D)

/-- The law of the coins: the keys, then `Q` independent draws. -/
noncomputable def coinLaw : PMF (K × (Fin S.Q → D)) :=
  S.keys.bind fun κ => (PMF.pi fun _ => S.draw).map fun d => (κ, d)

theorem coinLaw_apply (κ : K) (d : Fin S.Q → D) :
    S.coinLaw (κ, d) = S.keys κ * ∏ i, S.draw (d i) := by
  rw [coinLaw, PMF.bind_apply, tsum_eq_single κ]
  · rw [PMF.map_apply, tsum_eq_single d (fun d' hd' => by simp [Ne.symm hd'])]
    simp [PMF.pi_apply]
  · intro κ' hκ'
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun d' => by simp [Ne.symm hκ'], mul_zero]

/-- **The split challenger as a challenger**: coins `K × (Fin Q → D)` with law `coinLaw`;
request number `hist.length < Q` with request `r` gets `reply κ (d ⟨hist.length, _⟩)
hist.length r`, later ones `⟨none, []⟩`. -/
noncomputable def toChallenger : Challenger X Y Req Resp where
  Coins := K × (Fin S.Q → D)
  coins := S.coinLaw
  Q := S.Q
  q := S.q
  respond c hist r :=
    if h : hist.length < S.Q then S.reply c.1 (c.2 ⟨hist.length, h⟩) hist.length r
    else .pure ⟨none, []⟩
  respond_queries c hist r H := by
    split_ifs
    · exact S.reply_queries _ _ _ _ H
    · simp [OracleProg.trace_pure]

/-- **The same challenger with other reply programs** `reply'`, making at most `q` queries. -/
def withReply (reply' : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp))
    (h' : ∀ κ d i r H, ((reply' κ d i r).trace H).length ≤ S.q) :
    SplitChallenger X Y Req Resp K D :=
  { S with reply := reply', reply_queries := h' }

variable [DecidableEq X]

/-- **The split challenger with reply programs `R` as an environment of the pure game** whose
state is the oracle in force: the tape is the oracle, the keys and the draws; request number `i`
with request `req` runs `R κ d_i i req` on the oracle in force `H` and reprograms `H` by its
assignments. -/
noncomputable def oracleEnv [Fintype X] [Fintype Y] [Nonempty Y]
    (R : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp)) :
    Env ((X → Y) × K × (Fin S.Q → D)) Req Resp X Y S.Q where
  μ := (PMF.uniformOfFintype (X → Y)).bind fun H => S.coinLaw.map fun c => (H, c)
  oracle₀ ω := ω.1
  respond ω i req H :=
    ⟨((R ω.2.1 (ω.2.2 i) i req).run H).response, H.reprogram ((R ω.2.1 (ω.2.2 i) i req).run H).assignments⟩

/-- **The challenger is bisimilar to its environment with the oracle in force as its state**: the
challenger's state has the tape's oracle as its base, the oracle in force as its base reprogrammed
by its assignments, and one history entry per request numbered below `Q`. -/
theorem bisimulation_toPureEnv [Fintype X] [Fintype Y] [Nonempty Y]
    (ω : (X → Y) × K × (Fin S.Q → D)) :
    (S.oracleEnv S.reply).Bisimulation S.toChallenger.toPureEnv ω ω
      fun i H s => s.base = ω.1 ∧ s.base.reprogram s.ass = H ∧ s.hist.length = min i S.Q where
  init := by simp [oracleEnv, Challenger.toPureEnv, Function.reprogram]
  step i h req H s := by
    rintro ⟨hb, hH, hl⟩
    have hl' : s.hist.length = i := by rw [hl]; exact min_eq_left h.le
    subst hl' hH
    simp only [oracleEnv, Challenger.toPureEnv, toChallenger, h, ↓reduceDIte]
    simp [hb, QROM.reprogram_append, min_eq_left (Nat.succ_le_of_lt h)]
  skip i hi H s := by
    rintro ⟨hb, hH, hl⟩
    exact ⟨hb, hH, by rw [hl, min_eq_right hi, min_eq_right (by omega)]⟩
  reply i h req H s := by
    rintro ⟨hb, hH, hl⟩
    have hl' : s.hist.length = i := by rw [hl]; exact min_eq_left h.le
    subst hl' hH
    simp only [oracleEnv, Challenger.toPureEnv, toChallenger, h, ↓reduceDIte]
  oracle i H s := by
    rintro ⟨-, hH, -⟩
    rw [OracleState.toOracle_fun]
    exact hH.symm

end SplitChallenger

/-! ### Kernel replacement for any set of game registers -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Q : ℕ} (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

section KernelSet

variable {Ω : Type*}

/-- **The probability of a set `S` of game registers** in the final state of the game on tape
`ω` (`acceptProbOnAt` is the case `S = gameAccept ∩ logsIn L`). -/
noncomputable def probAt (E : Env Ω Req A X Y Q) (S : Set (GameReg W n X Y Req A m)) (ω : Ω) : ℝ :=
  prob S (D.final E post ω)

theorem probAt_nonneg (E : Env Ω Req A X Y Q) (S : Set (GameReg W n X Y Req A m)) (ω : Ω) :
    0 ≤ D.probAt post E S ω :=
  prob_nonneg _ _

theorem probAt_le_one (E : Env Ω Req A X Y Q) (S : Set (GameReg W n X Y Req A m)) (ω : Ω) :
    D.probAt post E S ω ≤ 1 := by
  rw [probAt, prob, show (1 : ℝ) = ‖D.final E post ω‖ ^ 2 by
    rw [D.norm_final post E ω, one_pow]]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_mask_le _ _) 2

theorem probAt_eq_of_agree {Ω' : Type*} {E : Env Ω Req A X Y Q} {E' : Env Ω' Req A X Y Q}
    {ω : Ω} {ω' : Ω'} (h0 : E.oracle₀ ω = E'.oracle₀ ω') (hr : E.respond ω = E'.respond ω')
    (S : Set (GameReg W n X Y Req A m)) :
    D.probAt post E S ω = D.probAt post E' S ω' := by
  rw [probAt, probAt, D.final_eq_of_agree post h0 hr]

/-- The probability of `S ∩ logsIn N` depends only on the part of the final state on `N`. -/
theorem probAt_inter_eq {Ω' : Type*} (E : Env Ω Req A X Y Q) (E' : Env Ω' Req A X Y Q)
    {ω : Ω} {ω' : Ω'} {N : Set (LogReg Req m)}
    (h : mask (logsIn N) (D.final E post ω) = mask (logsIn N) (D.final E' post ω'))
    (S : Set (GameReg W n X Y Req A m)) :
    D.probAt post E (S ∩ logsIn N) ω = D.probAt post E' (S ∩ logsIn N) ω' := by
  rw [probAt, probAt, prob_inter_eq_prob_mask, prob_inter_eq_prob_mask, h]

variable [DecidableEq X]

theorem probAt_withResponse_key (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (S : Set (GameReg W n X Y Req A m)) (κ : Req × (X → Y))
    {s s' : Req → (X → Y) → EnvReply A (X → Y)} (hs : s κ.1 κ.2 = s' κ.1 κ.2) :
    D.probAt post (E.withResponse ω₀ j s) (S ∩ logsIn {lg | E.keyOf ω₀ j lg = some κ}) () =
      D.probAt post (E.withResponse ω₀ j s') (S ∩ logsIn {lg | E.keyOf ω₀ j lg = some κ}) () := by
  set N : Set (LogReg Req m) := {lg | E.keyOf ω₀ j lg = none ∨ E.keyOf ω₀ j lg = some κ}
  have horacle : ∀ lg ∈ N, (E.withResponse ω₀ j s).oracle () lg =
      (E.withResponse ω₀ j s').oracle () lg := by
    intro lg hlg
    rcases hlg with h | h
    · have hle := (keyOf_eq_none_iff E ω₀).1 h
      rw [Env.oracle, Env.oracle, oracleIn_withResponse_of_le E ω₀ j s hle,
        oracleIn_withResponse_of_le E ω₀ j s' hle]
    · obtain ⟨hlt, rfl⟩ := keyOf_eq_some E ω₀ h
      exact oracleIn_withResponse_congr E ω₀ j hlt hs
  have hrun : mask (logsIn N) (D.run (E.withResponse ω₀ j s) ()) =
      mask (logsIn N) (D.run (E.withResponse ω₀ j s') ()) := by
    refine D.mask_stage_eq_of_eventPerm _ _ N (fun k r hr hN => ?_) (fun k r hr hN himg => ?_) m
    · have hkey : ∀ (E'' : Env Unit Req A X Y Q), D.eventPerm E'' () k r ∉ logsIn N := by
        intro E'' himg
        simp only [N, mem_logsIn, Set.mem_ofPred_eq, not_or] at hN himg
        have hmade : (j : ℕ) < (requests (splitLogs r).2).length := by
          by_contra h
          exact hN.1 ((keyOf_eq_none_iff E ω₀).2 (not_lt.1 h))
        have hsame : E.keyOf ω₀ j (splitLogs (D.eventPerm E'' () k r)).2 =
            E.keyOf ω₀ j (splitLogs r).2 := by
          have := D.requests_eventPerm E'' () hr
          split_ifs at this
          · exact keyOf_append_of_lt E ω₀ this hmade
          · simp only [Env.keyOf, this]
        rw [hsame] at himg
        tauto
      exact ⟨hkey _, hkey _⟩
    · by_cases hk : k < m
      · refine D.eventPerm_eq_of_agree _ _ hr (fun _ => horacle _ hN) fun hkind => ?_
        set rs := requests (splitLogs r).2
        rcases lt_trichotomy rs.length j with hlt | heq | hgt
        · rw [answerAfter_withResponse_of_lt E ω₀ j s hlt,
            answerAfter_withResponse_of_lt E ω₀ j s' hlt]
        · rw [answerAfter_withResponse_of_eq E ω₀ j s heq,
            answerAfter_withResponse_of_eq E ω₀ j s' heq]
          have hreq : ∀ (E'' : Env Unit Req A X Y Q),
              requests (splitLogs (D.eventPerm E'' () k r)).2 = rs ++ [r.request] := fun E'' => by
            rw [D.requests_eventPerm E'' () hr, ite_eq_left ⟨hkind, hk⟩]
          have hkimg : ∀ (E'' : Env Unit Req A X Y Q), D.eventPerm E'' () k r ∈ logsIn N →
              κ = (r.request, E.oracleIn ω₀ rs) := fun E'' h => by
            simp only [N, mem_logsIn, Set.mem_ofPred_eq] at h
            rw [keyOf_append_of_eq E ω₀ (hreq E'') heq] at h
            rcases h with h | h
            · exact absurd h (by simp)
            · exact (Option.some_inj.1 h).symm
          have := himg.elim (hkimg _) (hkimg _)
          rw [this] at hs
          rw [hs]
        · have hκ : E.keyOf ω₀ j (splitLogs r).2 = some κ := by
            rcases hN with h | h
            · exact absurd ((keyOf_eq_none_iff E ω₀).1 h) (not_le.2 hgt)
            · exact h
          obtain ⟨hlt, hκ'⟩ := keyOf_eq_some E ω₀ hκ
          rw [hκ'] at hs
          exact answerAfter_withResponse_congr E ω₀ j hlt hs _
      · rw [D.eventPerm_of_le _ () (not_lt.1 hk), D.eventPerm_of_le _ () (not_lt.1 hk)]
  have hfin := D.mask_final_eq _ _ post hrun horacle
  have hset : S ∩ logsIn {lg | E.keyOf ω₀ j lg = some κ} =
      (S ∩ logsIn {lg | E.keyOf ω₀ j lg = some κ}) ∩ logsIn N := by
    ext r
    simp only [Set.mem_inter_iff, mem_logsIn, Set.mem_ofPred_eq, N]
    tauto
  rw [hset]
  exact D.probAt_inter_eq post _ _ hfin _

omit [DecidableEq X] in
/-- Two environments that agree before request `j` give the same probability of `S` on the
branches that never make request `j`. -/
theorem probAt_notMade_eq {Ω' : Type*} (E : Env Ω Req A X Y Q) (E' : Env Ω' Req A X Y Q)
    {ω : Ω} {ω' : Ω'} {j : ℕ}
    (hans : ∀ rs req, rs.length < j → E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horacle : ∀ rs, rs.length ≤ j → E.oracleIn ω rs = E'.oracleIn ω' rs)
    (S : Set (GameReg W n X Y Req A m)) :
    D.probAt post E (S ∩ logsIn (madeLogs j)ᶜ) ω = D.probAt post E' (S ∩ logsIn (madeLogs j)ᶜ) ω' :=
  D.probAt_inter_eq post E E' (D.mask_final_eq E E' post
    (D.mask_stage_eq_of_agree E E' hans horacle m) fun lg hlg => by
      simp only [Set.mem_compl_iff, madeLogs, Set.mem_ofPred_eq, not_lt] at hlg
      rw [Env.oracle, Env.oracle, horacle _ hlg]) S

/-- **The split by keys** for a set `S`: the part on the branches that never make request `j`
plus the parts on the keys of request `j`. -/
theorem probAt_eq_add_sum_key (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : ℕ) (E' : Env Unit Req A X Y Q)
    (S : Set (GameReg W n X Y Req A m)) :
    D.probAt post E' S () = D.probAt post E' (S ∩ logsIn (madeLogs j)ᶜ) () +
      ∑ κ : Req × (X → Y), D.probAt post E' (S ∩ logsIn {lg | E.keyOf ω₀ j lg = some κ}) () := by
  classical
  rw [probAt, prob_eq_sum_fiber _ (fun r => E.keyOf ω₀ j (splitLogs r).2), Fintype.sum_option]
  congr 1
  · rw [probAt]
    congr 1
    ext r
    simp [madeLogs, keyOf_eq_none_iff, mem_logsIn]

/-- **The part of the game on one key** for a set `S`, with request `j` answered by the constant
reply `y`. -/
noncomputable def keyPartSet (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (S : Set (GameReg W n X Y Req A m)) (κ : Req × (X → Y)) (y : EnvReply A (X → Y)) : ℝ :=
  D.probAt post (E.withResponse ω₀ j fun _ _ => y) (S ∩ logsIn {lg | E.keyOf ω₀ j lg = some κ}) ()

theorem probAt_withResponse_eq_add_sum (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (S : Set (GameReg W n X Y Req A m)) (s s₀ : Req → (X → Y) → EnvReply A (X → Y)) :
    D.probAt post (E.withResponse ω₀ j s) S () =
      D.probAt post (E.withResponse ω₀ j s₀) (S ∩ logsIn (madeLogs j)ᶜ) () +
        ∑ κ : Req × (X → Y), D.keyPartSet post E ω₀ j S κ (s κ.1 κ.2) := by
  rw [D.probAt_eq_add_sum_key post E ω₀ j]
  congr 1
  · exact D.probAt_notMade_eq post _ _
      (fun rs req h => by rw [answerAfter_withResponse_of_lt _ _ _ _ h,
        answerAfter_withResponse_of_lt _ _ _ _ h])
      (fun rs h => by rw [oracleIn_withResponse_of_le _ _ _ _ h,
        oracleIn_withResponse_of_le _ _ _ _ h]) S
  · exact Finset.sum_congr rfl fun κ _ => D.probAt_withResponse_key post E ω₀ j S κ rfl

theorem sum_keyPartSet_le_one (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (S : Set (GameReg W n X Y Req A m)) (y : Req × (X → Y) → EnvReply A (X → Y)) :
    ∑ κ : Req × (X → Y), D.keyPartSet post E ω₀ j S κ (y κ) ≤ 1 := by
  have h1 := D.probAt_le_one post (E.withResponse ω₀ j fun req H => y (req, H)) S ()
  have h2 := D.probAt_nonneg post (E.withResponse ω₀ j fun req H => y (req, H))
    (S ∩ logsIn (madeLogs j)ᶜ) ()
  have h3 := D.probAt_withResponse_eq_add_sum post E ω₀ j S (fun req H => y (req, H))
    (fun req H => y (req, H))
  linarith

omit [DecidableEq X] in
theorem keyPartSet_eq_zero (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (S : Set (GameReg W n X Y Req A m)) {κ : Req × (X → Y)}
    (hκ : ∀ rs : List Req, rs.length = j → κ.2 ≠ E.oracleIn ω₀ rs) (y : EnvReply A (X → Y)) :
    D.keyPartSet post E ω₀ j S κ y = 0 := by
  have hempty : S ∩ logsIn {lg : LogReg Req m | E.keyOf ω₀ j lg = some κ} = ∅ := by
    ext r
    simp only [Set.mem_inter_iff, mem_logsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro _ hk
    obtain ⟨hlt, hκ'⟩ := keyOf_eq_some E ω₀ hk
    exact hκ ((requests (splitLogs r).2).take j) (List.length_take_of_le hlt.le) (by rw [hκ'])
  rw [keyPartSet, probAt, hempty]
  have hm : ∀ v : QState (GameReg W n X Y Req A m), mask ∅ v = 0 := fun v => by
    ext i
    simp
  simp [prob, hm]

omit [DecidableEq X] in
/-- **The game at a tape is the game with request `j` answered by the tape's kernel**, for a set
`S` (`acceptProbOnAt_eq_withResponse`). -/
theorem probAt_eq_withResponse {Ω' : Type*} (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (E' : Env Ω' Req A X Y Q) {ω : Ω'}
    (h0 : E'.oracle₀ ω = E.oracle₀ ω₀) (hi : ∀ c : Fin Q, c ≠ j → E'.respond ω c = E.respond ω₀ c)
    (S : Set (GameReg W n X Y Req A m)) :
    D.probAt post E' S ω = D.probAt post (E.withResponse ω₀ j (E'.respond ω j)) S () :=
  D.probAt_eq_of_agree post (E := E') (E' := E.withResponse ω₀ j (E'.respond ω j))
    (ω' := ()) h0 (funext fun c => by
      rw [Env.withResponse_respond]
      by_cases hc : c = j
      · simp [hc]
      · simp [hc, hi c hc]) S

/-- **The average over one kernel, split by the key**, for a set `S`. -/
theorem sum_probAt_withResponse {R : Type*} [Fintype R] (E : Env Ω Req A X Y Q) (ω₀ : Ω)
    (j : Fin Q) (S : Set (GameReg W n X Y Req A m)) (ν : PMF R)
    (s : R → Req → (X → Y) → EnvReply A (X → Y)) (y₀ : EnvReply A (X → Y)) :
    ∑ τ, (ν τ).toReal * D.probAt post (E.withResponse ω₀ j (s τ)) S () =
      D.probAt post (E.withResponse ω₀ j fun _ _ => y₀) (S ∩ logsIn (madeLogs j)ᶜ) () +
        ∑ κ : Req × (X → Y), ∑ τ, (ν τ).toReal * D.keyPartSet post E ω₀ j S κ (s τ κ.1 κ.2) := by
  simp only [D.probAt_withResponse_eq_add_sum post E ω₀ j S _ fun _ _ => y₀, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **Kernel replacement at one tape, for any set of game registers** (`abs_sum_withResponse_sub_le`
with the accepting set `S`): if the laws of request `j`'s reply under the two kernels are within
`ε` at every key that a branch can carry, the two averaged games give `S` probabilities within
`ε`. -/
theorem abs_sum_probAt_withResponse_sub_le {R R' : Type*} [Fintype R] [Fintype R']
    (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q) {ν : PMF R} {ν' : PMF R'}
    (S : Set (GameReg W n X Y Req A m))
    (s : R → Req → (X → Y) → EnvReply A (X → Y)) (s' : R' → Req → (X → Y) → EnvReply A (X → Y))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hj : ∀ req (rs : List Req), rs.length = j →
      PMF.tvDist (ν.map fun τ => s τ req (E.oracleIn ω₀ rs))
        (ν'.map fun τ => s' τ req (E.oracleIn ω₀ rs)) ≤ ε) :
    |∑ τ, (ν τ).toReal * D.probAt post (E.withResponse ω₀ j (s τ)) S () -
      ∑ τ, (ν' τ).toReal * D.probAt post (E.withResponse ω₀ j (s' τ)) S ()| ≤ ε := by
  classical
  obtain ⟨y₀⟩ : Nonempty (EnvReply A (X → Y)) := ⟨⟨none, 0⟩⟩
  have hmax : ∀ κ, ∃ y, ∀ y', D.keyPartSet post E ω₀ j S κ y' ≤ D.keyPartSet post E ω₀ j S κ y :=
    fun κ => by
      obtain ⟨y, -, hy⟩ := Finset.exists_max_image Finset.univ (D.keyPartSet post E ω₀ j S κ)
        Finset.univ_nonempty
      exact ⟨y, fun y' => hy y' (Finset.mem_univ _)⟩
  choose ymax hymax using hmax
  rw [D.sum_probAt_withResponse post E ω₀ j S ν s y₀, D.sum_probAt_withResponse post E ω₀ j S ν' s' y₀,
    add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ κ : Req × (X → Y), |∑ τ, (ν τ).toReal * D.keyPartSet post E ω₀ j S κ (s τ κ.1 κ.2) -
        ∑ τ, (ν' τ).toReal * D.keyPartSet post E ω₀ j S κ (s' τ κ.1 κ.2)|
      ≤ ∑ κ : Req × (X → Y), D.keyPartSet post E ω₀ j S κ (ymax κ) * ε :=
        Finset.sum_le_sum fun κ _ => by
        rw [← PMF.sum_toReal_map_mul ν (fun τ => s τ κ.1 κ.2) (D.keyPartSet post E ω₀ j S κ),
          ← PMF.sum_toReal_map_mul ν' (fun τ => s' τ κ.1 κ.2) (D.keyPartSet post E ω₀ j S κ)]
        refine (PMF.abs_sum_toReal_mul_sub_le _ _
          (fun y => D.probAt_nonneg post _ _ _) (hymax κ)).trans ?_
        by_cases hreach : ∃ rs : List Req, rs.length = j ∧ κ.2 = E.oracleIn ω₀ rs
        · obtain ⟨rs, hrs, hκ⟩ := hreach
          refine mul_le_mul_of_nonneg_left ?_ (D.probAt_nonneg post _ _ _)
          have := hj κ.1 rs hrs
          rwa [← hκ] at this
        · push Not at hreach
          rw [D.keyPartSet_eq_zero post E ω₀ j S hreach, zero_mul, zero_mul]
    _ = (∑ κ : Req × (X → Y), D.keyPartSet post E ω₀ j S κ (ymax κ)) * ε := by rw [Finset.sum_mul]
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right (D.sum_keyPartSet_le_one post E ω₀ j S ymax) hε0
    _ = ε := one_mul _

/-! #### Sets that read the oracle in force at the logs -/

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] [DecidableEq X] in
/-- **A family of sets of game registers indexed by an oracle per logs is local in the logs** if
two oracle families that agree on the logs in `N` give the same set on the logs in `N`. -/
def LogLocal (S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)) : Prop :=
  ∀ F F' (N : Set (LogReg Req m)), (∀ lg ∈ N, F lg = F' lg) → S F ∩ logsIn N = S F' ∩ logsIn N

/-- **The probability of a set reading the final oracle in force**: the set `S (E.oracle ω)`
of game registers in the final state on tape `ω`. -/
noncomputable def probOracleAt (E : Env Ω Req A X Y Q)
    (S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)) (ω : Ω) : ℝ :=
  D.probAt post E (S (E.oracle ω)) ω

omit [DecidableEq X] in
theorem probOracleAt_eq_of_agree {Ω' : Type*} {E : Env Ω Req A X Y Q} {E' : Env Ω' Req A X Y Q}
    {ω : Ω} {ω' : Ω'} (h0 : E.oracle₀ ω = E'.oracle₀ ω') (hr : E.respond ω = E'.respond ω')
    (S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)) :
    D.probOracleAt post E S ω = D.probOracleAt post E' S ω' := by
  rw [probOracleAt, probOracleAt, D.probAt_eq_of_agree post h0 hr]
  congr 2
  funext lg
  exact Env.oracle_eq_of_agree h0 hr lg

/-- **The part of the game on one key**, for a set reading the final oracle, with request `j`
answered by the constant reply `y`. -/
noncomputable def keyPartOracle (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)) (κ : Req × (X → Y))
    (y : EnvReply A (X → Y)) : ℝ :=
  D.probAt post (E.withResponse ω₀ j fun _ _ => y)
    (S ((E.withResponse ω₀ j fun _ _ => y).oracle ()) ∩ logsIn {lg | E.keyOf ω₀ j lg = some κ}) ()

theorem probOracleAt_withResponse_eq_add_sum (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    {S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)} (hS : LogLocal S)
    (s s₀ : Req → (X → Y) → EnvReply A (X → Y)) :
    D.probOracleAt post (E.withResponse ω₀ j s) S () =
      D.probAt post (E.withResponse ω₀ j s₀)
        (S ((E.withResponse ω₀ j s₀).oracle ()) ∩ logsIn (madeLogs j)ᶜ) () +
        ∑ κ : Req × (X → Y), D.keyPartOracle post E ω₀ j S κ (s κ.1 κ.2) := by
  rw [probOracleAt, D.probAt_eq_add_sum_key post E ω₀ j]
  congr 1
  · rw [hS _ ((E.withResponse ω₀ j s₀).oracle ()) _ fun lg hlg => by
      simp only [Set.mem_compl_iff, madeLogs, Set.mem_ofPred_eq, not_lt] at hlg
      rw [Env.oracle, Env.oracle, oracleIn_withResponse_of_le _ _ _ _ hlg,
        oracleIn_withResponse_of_le _ _ _ _ hlg]]
    exact D.probAt_notMade_eq post _ _
      (fun rs req h => by rw [answerAfter_withResponse_of_lt _ _ _ _ h,
        answerAfter_withResponse_of_lt _ _ _ _ h])
      (fun rs h => by rw [oracleIn_withResponse_of_le _ _ _ _ h,
        oracleIn_withResponse_of_le _ _ _ _ h]) _
  · refine Finset.sum_congr rfl fun κ _ => ?_
    rw [keyPartOracle, hS _ ((E.withResponse ω₀ j fun _ _ => s κ.1 κ.2).oracle ()) _
      fun lg hlg => by
        obtain ⟨hlt, hκ⟩ := keyOf_eq_some E ω₀ hlg
        subst hκ
        exact oracleIn_withResponse_congr E ω₀ j hlt rfl]
    exact D.probAt_withResponse_key post E ω₀ j _ κ rfl

theorem sum_keyPartOracle_le_one (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    {S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)} (hS : LogLocal S)
    (y : Req × (X → Y) → EnvReply A (X → Y)) :
    ∑ κ : Req × (X → Y), D.keyPartOracle post E ω₀ j S κ (y κ) ≤ 1 := by
  have h1 := D.probAt_le_one post (E.withResponse ω₀ j fun req H => y (req, H))
    (S ((E.withResponse ω₀ j fun req H => y (req, H)).oracle ())) ()
  have h2 := D.probAt_nonneg post (E.withResponse ω₀ j fun req H => y (req, H))
    (S ((E.withResponse ω₀ j fun req H => y (req, H)).oracle ()) ∩ logsIn (madeLogs j)ᶜ) ()
  have h3 := D.probOracleAt_withResponse_eq_add_sum post E ω₀ j hS (fun req H => y (req, H))
    (fun req H => y (req, H))
  rw [probOracleAt] at h3
  linarith

omit [DecidableEq X] in
theorem keyPartOracle_eq_zero (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)) {κ : Req × (X → Y)}
    (hκ : ∀ rs : List Req, rs.length = j → κ.2 ≠ E.oracleIn ω₀ rs) (y : EnvReply A (X → Y)) :
    D.keyPartOracle post E ω₀ j S κ y = 0 := by
  have hempty : S ((E.withResponse ω₀ j fun _ _ => y).oracle ()) ∩
      logsIn {lg : LogReg Req m | E.keyOf ω₀ j lg = some κ} = ∅ := by
    ext r
    simp only [Set.mem_inter_iff, mem_logsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro _ hk
    obtain ⟨hlt, hκ'⟩ := keyOf_eq_some E ω₀ hk
    exact hκ ((requests (splitLogs r).2).take j) (List.length_take_of_le hlt.le) (by rw [hκ'])
  rw [keyPartOracle, probAt, hempty]
  have hm : ∀ v : QState (GameReg W n X Y Req A m), mask ∅ v = 0 := fun v => by
    ext i
    simp
  simp [prob, hm]

omit [DecidableEq X] in
/-- **The game at a tape is the game with request `j` answered by the tape's kernel**, for a set
reading the final oracle. -/
theorem probOracleAt_eq_withResponse {Ω' : Type*} (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (E' : Env Ω' Req A X Y Q) {ω : Ω'}
    (h0 : E'.oracle₀ ω = E.oracle₀ ω₀) (hi : ∀ c : Fin Q, c ≠ j → E'.respond ω c = E.respond ω₀ c)
    (S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)) :
    D.probOracleAt post E' S ω = D.probOracleAt post (E.withResponse ω₀ j (E'.respond ω j)) S () :=
  D.probOracleAt_eq_of_agree post (E := E') (E' := E.withResponse ω₀ j (E'.respond ω j))
    (ω' := ()) h0 (funext fun c => by
      rw [Env.withResponse_respond]
      by_cases hc : c = j
      · simp [hc]
      · simp [hc, hi c hc]) S

/-- **The average over one kernel, split by the key**, for a set reading the final oracle. -/
theorem sum_probOracleAt_withResponse {R : Type*} [Fintype R] (E : Env Ω Req A X Y Q) (ω₀ : Ω)
    (j : Fin Q) {S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)} (hS : LogLocal S)
    (ν : PMF R) (s : R → Req → (X → Y) → EnvReply A (X → Y)) (y₀ : EnvReply A (X → Y)) :
    ∑ τ, (ν τ).toReal * D.probOracleAt post (E.withResponse ω₀ j (s τ)) S () =
      D.probAt post (E.withResponse ω₀ j fun _ _ => y₀)
        (S ((E.withResponse ω₀ j fun _ _ => y₀).oracle ()) ∩ logsIn (madeLogs j)ᶜ) () +
        ∑ κ : Req × (X → Y), ∑ τ, (ν τ).toReal * D.keyPartOracle post E ω₀ j S κ (s τ κ.1 κ.2) := by
  simp only [D.probOracleAt_withResponse_eq_add_sum post E ω₀ j hS _ fun _ _ => y₀, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **Kernel replacement at one tape, for a set reading the final oracle in force**
(`abs_sum_withResponse_sub_le` with an accepting set that may read the adversary's registers, the
logs and the final oracle at the logs, jointly): if the laws of request `j`'s reply under the two
kernels are within `ε` at every key that a branch can carry, the two averaged games give the set
probabilities within `ε`. -/
theorem abs_sum_probOracleAt_withResponse_sub_le {R R' : Type*} [Fintype R] [Fintype R']
    (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q) {ν : PMF R} {ν' : PMF R'}
    {S : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req A m)} (hS : LogLocal S)
    (s : R → Req → (X → Y) → EnvReply A (X → Y)) (s' : R' → Req → (X → Y) → EnvReply A (X → Y))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hj : ∀ req (rs : List Req), rs.length = j →
      PMF.tvDist (ν.map fun τ => s τ req (E.oracleIn ω₀ rs))
        (ν'.map fun τ => s' τ req (E.oracleIn ω₀ rs)) ≤ ε) :
    |∑ τ, (ν τ).toReal * D.probOracleAt post (E.withResponse ω₀ j (s τ)) S () -
      ∑ τ, (ν' τ).toReal * D.probOracleAt post (E.withResponse ω₀ j (s' τ)) S ()| ≤ ε := by
  classical
  obtain ⟨y₀⟩ : Nonempty (EnvReply A (X → Y)) := ⟨⟨none, 0⟩⟩
  have hmax : ∀ κ, ∃ y, ∀ y', D.keyPartOracle post E ω₀ j S κ y' ≤
      D.keyPartOracle post E ω₀ j S κ y := fun κ => by
    obtain ⟨y, -, hy⟩ := Finset.exists_max_image Finset.univ (D.keyPartOracle post E ω₀ j S κ)
      Finset.univ_nonempty
    exact ⟨y, fun y' => hy y' (Finset.mem_univ _)⟩
  choose ymax hymax using hmax
  rw [D.sum_probOracleAt_withResponse post E ω₀ j hS ν s y₀,
    D.sum_probOracleAt_withResponse post E ω₀ j hS ν' s' y₀, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ κ : Req × (X → Y), |∑ τ, (ν τ).toReal * D.keyPartOracle post E ω₀ j S κ (s τ κ.1 κ.2) -
        ∑ τ, (ν' τ).toReal * D.keyPartOracle post E ω₀ j S κ (s' τ κ.1 κ.2)|
      ≤ ∑ κ : Req × (X → Y), D.keyPartOracle post E ω₀ j S κ (ymax κ) * ε :=
        Finset.sum_le_sum fun κ _ => by
        rw [← PMF.sum_toReal_map_mul ν (fun τ => s τ κ.1 κ.2) (D.keyPartOracle post E ω₀ j S κ),
          ← PMF.sum_toReal_map_mul ν' (fun τ => s' τ κ.1 κ.2) (D.keyPartOracle post E ω₀ j S κ)]
        refine (PMF.abs_sum_toReal_mul_sub_le _ _
          (fun y => D.probAt_nonneg post _ _ _) (hymax κ)).trans ?_
        by_cases hreach : ∃ rs : List Req, rs.length = j ∧ κ.2 = E.oracleIn ω₀ rs
        · obtain ⟨rs, hrs, hκ⟩ := hreach
          refine mul_le_mul_of_nonneg_left ?_ (D.probAt_nonneg post _ _ _)
          have := hj κ.1 rs hrs
          rwa [← hκ] at this
        · push Not at hreach
          rw [D.keyPartOracle_eq_zero post E ω₀ j S hreach, zero_mul, zero_mul]
    _ = (∑ κ : Req × (X → Y), D.keyPartOracle post E ω₀ j S κ (ymax κ)) * ε := by
        rw [Finset.sum_mul]
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right (D.sum_keyPartOracle_le_one post E ω₀ j hS ymax) hε0
    _ = ε := one_mul _

end KernelSet

end Distinguisher

/-! ### The dilated game on any set of the mixed game's registers -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)
  [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)

/-- The basis states of the dilated game on a running branch (halting flag clear) whose game
registers lie in `T`. -/
def dilSet (T : Set A.G) : Set (GameReg A.DW A.width X Y Req Resp A.slots) :=
  {x | (A.relG x).1.2 = false ∧ (A.relG x).1.1 ∈ T}

/-- **The pure game of the dilated distinguisher gives every set `T` of the mixed game's
registers the mixed game's probability** (`acceptProbAt_dilate` for the set `T`, without the
measurement of the requests). -/
theorem prob_final_dilate [DecidableEq O] (o : O) (T : Set A.G) [DecidablePred (· ∈ T)] (ω : Ω) :
    prob (A.dilSet T) ((A.dilate o).final E A.postOp ω) =
      ∑ r : A.G, if r ∈ T then (A.mgRun E ω false r r).re else 0 := by
  have hspec := A.gameMixed.hybrid_spec (fun k => A.evPermB E ω k) () A.uG
    (fun k φ hφ => A.uStepD_logControlled k hφ) (A.slots + A.post)
  have hfin : (A.dilate o).final E A.postOp ω = Quantum.relabel A.relG.symm
      (hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
        (A.gameMixed.dilInit ()) (A.slots + A.post)) := by
    rw [← A.final_dilate E o ω, relabel_symm_relabel]
  have hn : ‖hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
      (A.gameMixed.dilInit ()) (A.slots + A.post)‖ = 1 := by
    rw [norm_hybrid, A.gameMixed.norm_dilInit]
  rw [hfin, prob_relabel]
  have hset : (A.relG.symm ⁻¹' A.dilSet T) =
      {p : A.GB × A.DAnc | p.1 ∈ {gb : A.GB | gb.2 = false ∧ gb.1 ∈ T}} := by
    ext ⟨⟨g, b⟩, a⟩
    rfl
  rw [hset, ← probIn_reduceMState _ hn, MState.probIn]
  simp only [reduceMState_mat, hspec.2]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Set.indicator, Set.mem_ofPred_eq, Bool.true_eq_false, false_and,
    ite_false, zero_add, true_and]
  rw [mgRun_false_eq, ← A.ffBlock_stageV E ω]
  rfl

/-- The adversary with its output forgotten: the dilated game needs an output value, and the
mixed game does not read the output. -/
def unitOut : KindAlg ksA Unit :=
  { A with out := fun _ => () }

/-- **The algorithm with its output forgotten has its shape.** -/
theorem unitOut_toShape : A.unitOut.toShape = A.toShape :=
  rfl

/-- The steps of the algorithm with its output forgotten are its steps. -/
theorem unitOut_step : A.unitOut.step = A.step :=
  rfl

end KindAlg

/-! ### Events of a split challenger's game as pure games -/

namespace SplitChallenger

variable {X Y Req Resp K D : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] {O : Type}

/-- The game registers whose adversary's registers, logs and the oracle `F` at the logs satisfy
the event `P` at the keys `κ`. -/
def evSet {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop) (κ : K)
    (F : LogReg Req B.slots → X → Y) : Set B.G :=
  {r | P (splitLogs r).1 (splitLogs r).2 κ (F (splitLogs r).2)}

omit [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D] [Nonempty X] [AddGroup Y]
  [Nonempty Y] in
/-- The family of dilated sets of an event is local in the logs. -/
theorem logLocal_dilSet {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop) (κ : K) :
    Distinguisher.LogLocal (W := B.unitOut.DW) (n := B.width) (A := Resp)
      fun F => B.unitOut.dilSet (evSet B P κ F) := by
  intro F F' N h
  ext x
  have key : x ∈ logsIn N → F (splitLogs (B.unitOut.relG x).1.1).2 =
      F' (splitLogs (B.unitOut.relG x).1.1).2 := fun h2 => h _ h2
  show ((B.unitOut.relG x).1.2 = false ∧ P (splitLogs (B.unitOut.relG x).1.1).1
      (splitLogs (B.unitOut.relG x).1.1).2 κ (F (splitLogs (B.unitOut.relG x).1.1).2)) ∧
      x ∈ logsIn N ↔ ((B.unitOut.relG x).1.2 = false ∧ P (splitLogs (B.unitOut.relG x).1.1).1
      (splitLogs (B.unitOut.relG x).1.1).2 κ (F' (splitLogs (B.unitOut.relG x).1.1).2)) ∧
      x ∈ logsIn N
  constructor
  · rintro ⟨⟨h1, h1'⟩, h2⟩
    exact ⟨⟨h1, key h2 ▸ h1'⟩, h2⟩
  · rintro ⟨⟨h1, h1'⟩, h2⟩
    exact ⟨⟨h1, (key h2).symm ▸ h1'⟩, h2⟩

omit [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D] in
/-- **The final oracle in force read from the composed registers is the pure game's** at the
logs: the base oracle reprogrammed by the post-phase assignments of the placed game registers. -/
theorem _root_.GordieHowe.Quantum.KindAlg.reprogram_postAss_emb {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)
    (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins) (r : B.G) :
    H.reprogram (B.postAss C (B.emb C H c B.slots r).1.chal) =
      C.toPureEnv.oracle (H, c) (splitLogs r).2 := by
  show H.reprogram (B.stateAt C ⟨(splitLogs r).2, B.garFill C H c (splitLogs r).2 B.slots, c⟩
    B.slots).assignments = _
  rw [KindAlg.stateAt]
  rw [B.regState_eq C H c (splitLogs r).2 B.slots le_rfl]
  show H.reprogram (C.stateAfter H c (requestsBefore (splitLogs r).2 B.slots)).ass =
    (C.stateAfter H c (requestsBefore (splitLogs r).2 B.slots)).base.reprogram
      (C.stateAfter H c (requestsBefore (splitLogs r).2 B.slots)).ass
  rw [C.stateAfter_base]

/-- **An event of the adversary's registers, the logs, the keys and the final oracle in force is
the coin average of a pure game**: the dilated adversary (`KindAlg.dilate`) against the split
challenger as an environment with the oracle in force as its state (`oracleEnv`), with the
accepting set the running branches whose game registers and final oracle lie in the event
(`KindAlg.dilSet`). -/
theorem toOuterMeasure_outLaw_eq (S : SplitChallenger X Y Req Resp K D)
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop) :
    ((B.composeBothOut S.toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs v.chal.coins.1
          (H.reprogram (B.postAss S.toChallenger v.chal))} =
      ENNReal.ofReal (∑ c : K × (Fin S.Q → D), (S.coinLaw c).toReal *
        (B.unitOut.dilate ()).probOracleAt B.unitOut.postOp (S.oracleEnv S.reply)
          (fun F => B.unitOut.dilSet (evSet B P c.1 F)) (H, c)) := by
  classical
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_id B S.toChallenger H
    (fun v => P v.adv v.chal.logs v.chal.coins.1 (H.reprogram (B.postAss S.toChallenger v.chal)))]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hbis := S.bisimulation_toPureEnv (H, c)
  have horacle : (S.oracleEnv S.reply).oracle (H, c) =
      S.toChallenger.toPureEnv.oracle (m := B.unitOut.slots) (H, c) :=
    funext fun lg => hbis.oracle_eq lg
  rw [Distinguisher.probOracleAt, Distinguisher.probAt]
  rw [horacle, (B.unitOut.dilate ()).final_eq_of_bisimulation B.unitOut.postOp hbis]
  refine Eq.trans ?_ (B.unitOut.prob_final_dilate S.toChallenger.toPureEnv ()
    (evSet B P c.1 (S.toChallenger.toPureEnv.oracle (H, c))) (H, c)).symm
  refine Finset.sum_congr rfl fun r _ => ?_
  have hd : (B.mgRun S.toChallenger.toPureEnv (H, c) true r r) =
      (B.mgRun S.toChallenger.toPureEnv (H, c) false r r) := by
    rw [B.mgRun_deph, dephase_apply_self]
  rw [hd]
  refine if_congr ?_ rfl rfl
  exact iff_of_eq (congrArg (P (splitLogs r).1 (splitLogs r).2 c.1)
    (B.reprogram_postAss_emb S.toChallenger H c r))

end SplitChallenger

/-! ### One draw resampled -/

/-- **Resampling one coordinate of independent draws**: averaging `g` over independent draws `d`
is averaging, over `d`, the average of `g` with coordinate `j` replaced by a fresh draw. -/
theorem sum_prod_toReal_mul_eq_sum_update {ι D : Type*} [Fintype ι] [DecidableEq ι] [Fintype D]
    [DecidableEq D] (p : PMF D) (j : ι) (g : (ι → D) → ℝ) :
    ∑ d : ι → D, (∏ i, (p (d i)).toReal) * g d =
      ∑ d : ι → D, (∏ i, (p (d i)).toReal) * ∑ τ, (p τ).toReal * g (Function.update d j τ) := by
  have hw : ∀ (d : ι → D) (τ : D), (∏ i, (p (Function.update d j τ i)).toReal) * (p (d j)).toReal =
      (∏ i, (p (d i)).toReal) * (p τ).toReal := by
    intro d τ
    rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j (f := fun i => (p (d i)).toReal),
      Function.update_self, Finset.prod_congr rfl fun i hi => by
        rw [Function.update_of_ne (by simpa using hi)]]
    ring
  let e : (ι → D) × D ≃ (ι → D) × D :=
    { toFun := fun x => (Function.update x.1 j x.2, x.1 j)
      invFun := fun x => (Function.update x.1 j x.2, x.1 j)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  calc ∑ d : ι → D, (∏ i, (p (d i)).toReal) * g d
      = ∑ x : (ι → D) × D, (∏ i, (p (x.1 i)).toReal) * (p x.2).toReal * g x.1 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun d _ => ?_
        dsimp only
        rw [← Finset.sum_mul, ← Finset.mul_sum, PMF.sum_toReal, mul_one]
    _ = ∑ x : (ι → D) × D, (∏ i, (p ((e x).1 i)).toReal) * (p (e x).2).toReal * g (e x).1 :=
        (Fintype.sum_equiv e _ _ fun _ => rfl).symm
    _ = ∑ d : ι → D, (∏ i, (p (d i)).toReal) * ∑ τ, (p τ).toReal * g (Function.update d j τ) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [e, Equiv.coe_fn_mk]
        rw [hw]
        ring

/-! ### The hybrid -/

namespace SplitChallenger

variable {X Y Req Resp K D : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] {O : Type}
  (S : SplitChallenger X Y Req Resp K D)

/-- **Hybrid `j`**: the requests numbered below `j` answered by `reply'`, the others by
`reply`. -/
def hybReply (reply' : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp)) (j : ℕ) :
    K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp) :=
  fun κ d i r => if i < j then reply' κ d i r else S.reply κ d i r

/-- The coin average of the pure game of an event against the environment with reply programs
`R`. -/
noncomputable def evProb {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop)
    (R : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp)) : ℝ :=
  ∑ c : K × (Fin S.Q → D), (S.coinLaw c).toReal *
    (B.unitOut.dilate ()).probOracleAt B.unitOut.postOp (S.oracleEnv R)
      (fun F => B.unitOut.dilSet (evSet B P c.1 F)) (H, c)

omit [DecidableEq Y] [Nonempty X] in
/-- **Request `j` with a fresh draw at the tape `(H, κ, d)`**: the environment with reply
programs `R`, which agree with `R₀` off request `j`, at the draws `d` with draw `j` replaced by
`τ`, is `R₀`'s at `(H, κ, d)` with request `j` answered by `R` at `τ`. -/
theorem probOracleAt_update_eq {W : Type*} [Fintype W] {n m : ℕ}
    (Dd : Distinguisher W X Y Req Resp n m)
    (post : (X → Y) → QState (DReg W n X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req Resp))
    (R R₀ : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp)) (j : Fin S.Q)
    (hR : ∀ κ x (c : Fin S.Q) r, c ≠ j → R κ x c r = R₀ κ x c r)
    (T : (LogReg Req m → X → Y) → Set (GameReg W n X Y Req Resp m))
    (H : X → Y) (κ : K) (d : Fin S.Q → D) (τ : D) :
    Dd.probOracleAt post (S.oracleEnv R) T (H, κ, Function.update d j τ) =
      Dd.probOracleAt post ((S.oracleEnv R₀).withResponse (H, κ, d) j
          ((S.oracleEnv R).respond (H, κ, Function.update d j τ) j)) T () := by
  refine Dd.probOracleAt_eq_withResponse post (S.oracleEnv R₀) (H, κ, d) j (S.oracleEnv R)
    (ω := (H, κ, Function.update d j τ)) rfl (fun c hc => ?_) T
  funext req H'
  simp only [oracleEnv, Function.update_of_ne hc, hR κ _ c req hc]

omit [Nonempty X] in
/-- **One step of the hybrid**: hybrids `j` and `j + 1` differ only at request `j`, whose reply
reads only its own draw; at each keys and each request, the two replies differ with probability
at most `e` over that draw. -/
theorem abs_evProb_hybReply_sub_le (reply' : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp))
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop)
    {j : ℕ} (hj : j < S.Q) {e : ℝ} (he0 : 0 ≤ e)
    (he : ∀ κ r, (S.draw.toOuterMeasure {d | S.reply κ d j r ≠ reply' κ d j r}).toReal ≤ e) :
    |S.evProb B H P (S.hybReply reply' j) - S.evProb B H P (S.hybReply reply' (j + 1))| ≤ e := by
  classical
  set j' : Fin S.Q := ⟨j, hj⟩
  set Dd := B.unitOut.dilate ()
  set Ej := S.oracleEnv (S.hybReply reply' j)
  set Ej1 := S.oracleEnv (S.hybReply reply' (j + 1))
  set w : (Fin S.Q → D) → ℝ := fun d => ∏ i, (S.draw (d i)).toReal
  have hcoin : ∀ (κ : K) (d : Fin S.Q → D), (S.coinLaw (κ, d)).toReal = (S.keys κ).toReal * w d :=
    fun κ d => by rw [coinLaw_apply, ENNReal.toReal_mul, ENNReal.toReal_prod]
  have hw1 : ∑ d, w d = 1 := by
    simpa [w, PMF.toReal_pi_apply] using PMF.sum_toReal (PMF.pi fun _ : Fin S.Q => S.draw)
  have hsplit : ∀ R, S.evProb B H P R = ∑ κ, (S.keys κ).toReal * ∑ d, w d *
      Dd.probOracleAt B.unitOut.postOp (S.oracleEnv R)
        (fun F => B.unitOut.dilSet (evSet B P κ F)) (H, κ, d) := fun R => by
    rw [evProb, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hcoin, mul_assoc]
  have hR0 : ∀ κ x (c : Fin S.Q) r, c ≠ j' →
      S.hybReply reply' j κ x c r = S.hybReply reply' j κ x c r := fun _ _ _ _ _ => rfl
  have hR1 : ∀ κ x (c : Fin S.Q) r, c ≠ j' →
      S.hybReply reply' (j + 1) κ x c r = S.hybReply reply' j κ x c r := by
    intro κ x c r hc
    have hcj : (c : ℕ) ≠ j := fun h => hc (Fin.ext h)
    simp only [hybReply]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩
  rw [hsplit, hsplit, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ κ, |(S.keys κ).toReal * ∑ d, w d * Dd.probOracleAt B.unitOut.postOp
          (S.oracleEnv (S.hybReply reply' j)) (fun F => B.unitOut.dilSet (evSet B P κ F)) (H, κ, d) -
        (S.keys κ).toReal * ∑ d, w d * Dd.probOracleAt B.unitOut.postOp
          (S.oracleEnv (S.hybReply reply' (j + 1))) (fun F => B.unitOut.dilSet (evSet B P κ F))
          (H, κ, d)|
      ≤ ∑ κ, (S.keys κ).toReal * e := Finset.sum_le_sum fun κ _ => by
        rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        rw [sum_prod_toReal_mul_eq_sum_update S.draw j' (fun d => Dd.probOracleAt B.unitOut.postOp
            (S.oracleEnv (S.hybReply reply' j)) (fun F => B.unitOut.dilSet (evSet B P κ F))
            (H, κ, d)),
          sum_prod_toReal_mul_eq_sum_update S.draw j' (fun d => Dd.probOracleAt B.unitOut.postOp
            (S.oracleEnv (S.hybReply reply' (j + 1))) (fun F => B.unitOut.dilSet (evSet B P κ F))
            (H, κ, d)), ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ d, |w d * ∑ τ, (S.draw τ).toReal * Dd.probOracleAt B.unitOut.postOp
                (S.oracleEnv (S.hybReply reply' j)) (fun F => B.unitOut.dilSet (evSet B P κ F))
                (H, κ, Function.update d j' τ) -
              w d * ∑ τ, (S.draw τ).toReal * Dd.probOracleAt B.unitOut.postOp
                (S.oracleEnv (S.hybReply reply' (j + 1)))
                (fun F => B.unitOut.dilSet (evSet B P κ F)) (H, κ, Function.update d j' τ)|
            ≤ ∑ d, w d * e := Finset.sum_le_sum fun d _ => by
              rw [← mul_sub, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun _ _ =>
                ENNReal.toReal_nonneg)]
              refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun _ _ =>
                ENNReal.toReal_nonneg)
              simp only [S.probOracleAt_update_eq Dd B.unitOut.postOp _ _ j' hR0,
                S.probOracleAt_update_eq Dd B.unitOut.postOp _ _ j' hR1]
              refine Dd.abs_sum_probOracleAt_withResponse_sub_le B.unitOut.postOp Ej (H, κ, d) j'
                (logLocal_dilSet B P κ) _ _ he0 fun req rs _ => ?_
              refine (PMF.tvDist_map_map_le _ _ _).trans ((ENNReal.toReal_mono
                (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _))
                ((S.draw.toOuterMeasure).mono fun τ hτ => ?_)).trans (he κ req))
              simp only [Set.mem_ofPred_eq] at hτ ⊢
              intro heq
              apply hτ
              simp only [oracleEnv, hybReply, Function.update_self, j', lt_irrefl, ite_false,
                Nat.lt_succ_self, ite_true, heq]
          _ = e := by rw [← Finset.sum_mul, hw1, one_mul]
    _ = e := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

omit [Nonempty X] in
/-- **The hybrid over the requests**: if at each request number `j < Q` the two replies differ
with probability at most `e` over that request's draw, the event's coin-averaged pure game against
`reply` exceeds that against `reply'` by at most `Q * e`. -/
theorem evProb_le_add (reply' : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp))
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop)
    {e : ℝ} (he0 : 0 ≤ e)
    (he : ∀ j < S.Q, ∀ κ r,
      (S.draw.toOuterMeasure {d | S.reply κ d j r ≠ reply' κ d j r}).toReal ≤ e) :
    S.evProb B H P S.reply ≤ S.evProb B H P reply' + S.Q * e := by
  have h0 : S.hybReply reply' 0 = S.reply := by
    funext κ d i r
    simp [hybReply]
  have hQ : S.evProb B H P (S.hybReply reply' S.Q) = S.evProb B H P reply' := by
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine (B.unitOut.dilate ()).probOracleAt_eq_of_agree B.unitOut.postOp
      (E := S.oracleEnv (S.hybReply reply' S.Q)) (E' := S.oracleEnv reply') rfl
      (funext fun i => ?_) _
    funext req H'
    simp [oracleEnv, hybReply]
  have key : ∀ j ≤ S.Q, S.evProb B H P S.reply ≤ S.evProb B H P (S.hybReply reply' j) + j * e := by
    intro j
    induction j with
    | zero => intro _; rw [h0]; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := (abs_le.1 (S.abs_evProb_hybReply_sub_le reply' B H P (j := j) (by omega) he0
        (he j (by omega)))).2
      push_cast
      linarith
  have := key S.Q le_rfl
  rwa [hQ] at this

/-- **Identical until bad, one draw per request.** Let a split challenger answer request number
`i < Q` by `reply κ d_i i r`, from the keys `κ` and its own draw `d_i`, and let the same challenger
with reply programs `reply'` answer it by `reply' κ d_i i r`. If at each keys, request number and
request the two programs differ with probability at most `ε` over that request's draw, then every
event of the adversary's registers, the logs, the keys and the final oracle in force has
probability against the first at most its probability against the second plus `Q * ε`.

The adversary is quantum and interactive (`KindAlg`, composed by `composeBothOut`), and it chooses
each classical request adaptively: request `j` is prepared in superposition, after its queries, and
measured by the log copy. The bound holds because request `j` is fixed before request `j`'s draw is
read: in the pure game (deferred measurement `mgAccept_deph`, dilation `prob_final_dilate`) the
draw of request `j` is a fresh kernel at that request (`probOracleAt_update_eq`), and kernel
replacement at one request (`abs_sum_probOracleAt_withResponse_sub_le`, the form of
`Distinguisher.abs_acceptProbOn_sub_le_of_kernel` for an accepting set that reads the registers,
the logs and the final oracle jointly) bounds each step of the hybrid over `j = 0, …, Q` by `ε`
(`abs_evProb_hybReply_sub_le`, `evProb_le_add`). This is the identical-until-bad lemma (Shoup 2004,
Lemma 1; Bellare–Rogaway 2006, the fundamental lemma of game playing) with the bad event one
request's draw. -/
theorem toOuterMeasure_outLaw_le_add (reply' : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp))
    (h' : ∀ κ d i r H, ((reply' κ d i r).trace H).length ≤ S.q) {ε : ℝ≥0∞}
    (hε : ∀ κ i r, i < S.Q →
      S.draw.toOuterMeasure {d | S.reply κ d i r ≠ reply' κ d i r} ≤ ε)
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop) :
    ((B.composeBothOut S.toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs v.chal.coins.1
          (H.reprogram (B.postAss S.toChallenger v.chal))} ≤
      ((B.composeBothOut (S.withReply reply' h').toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs v.chal.coins.1
          (H.reprogram (B.postAss (S.withReply reply' h').toChallenger v.chal))} + S.Q * ε := by
  by_cases htop : ε = ⊤ ∧ S.Q ≠ 0
  · rw [htop.1, ENNReal.mul_top (by exact_mod_cast htop.2), add_top]
    exact le_top
  have he : ∀ j < S.Q, ∀ κ r,
      (S.draw.toOuterMeasure {d | S.reply κ d j r ≠ reply' κ d j r}).toReal ≤ ε.toReal := by
    intro j hj κ r
    exact ENNReal.toReal_mono (fun h => htop ⟨h, by omega⟩) (hε κ j r hj)
  have hle := S.evProb_le_add reply' B H P ENNReal.toReal_nonneg he
  rw [S.toOuterMeasure_outLaw_eq B H P, (S.withReply reply' h').toOuterMeasure_outLaw_eq B H P]
  have hnn : 0 ≤ S.evProb B H P reply' := Finset.sum_nonneg fun c _ =>
    mul_nonneg ENNReal.toReal_nonneg (Distinguisher.probAt_nonneg _ _ _ _ _)
  calc ENNReal.ofReal (S.evProb B H P S.reply)
      ≤ ENNReal.ofReal (S.evProb B H P reply' + S.Q * ε.toReal) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (S.evProb B H P reply') + ENNReal.ofReal (S.Q * ε.toReal) :=
        ENNReal.ofReal_add hnn (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
    _ ≤ ENNReal.ofReal (S.evProb B H P reply') + S.Q * ε := by
        gcongr
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        gcongr
        exact ENNReal.ofReal_toReal_le

/-- **Identical until bad, one draw per request**, for an event that does not read the final
oracle (`toOuterMeasure_outLaw_le_add`). -/
theorem toOuterMeasure_outLaw_le_add' (reply' : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp))
    (h' : ∀ κ d i r H, ((reply' κ d i r).trace H).length ≤ S.q) {ε : ℝ≥0∞}
    (hε : ∀ κ i r, i < S.Q →
      S.draw.toOuterMeasure {d | S.reply κ d i r ≠ reply' κ d i r} ≤ ε)
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → Prop) :
    ((B.composeBothOut S.toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs v.chal.coins.1} ≤
      ((B.composeBothOut (S.withReply reply' h').toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs v.chal.coins.1} + S.Q * ε :=
  S.toOuterMeasure_outLaw_le_add reply' h' hε B H fun a lg κ _ => P a lg κ

end SplitChallenger

end GordieHowe.Quantum
