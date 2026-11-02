-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.WholeRun
public import GordieHowe.Model.Quantum.Pure.ClassicalSim
public import GordieHowe.Foundations.ToMathlib.PMFRejectedPoints

@[expose] public section

/-!
# O2H over the whole run at hidden points correlated with the replies

`Distinguisher.advantage_acceptProb_le_of_fresh_secret_budget`
(`GordieHowe/Model/Quantum/O2H/WholeRun.lean`) compares two environments whose oracles differ on a
set fixed by a tape component that the first environment never reads. Here the oracles of the two
environments `E` and `E'` differ, after each request sequence, only on hidden sets of points of
the requests made, and those points are correlated with the responses: the coins of request
number `c` fix both its hidden points and its response (`HiddenSide`). The responses of the two
environments are the same, and the hidden points are never revealed except through them.

**The find condition.** For every request number `c`, every tape, every `c` earlier requests
`rs₀` and every request `req`, every guess `g (response)` computed from the response to `req` is
a hidden point of `req` with probability at most `ε c` over the coins of request `c`, the rest of
the tape fixed. Taking for `g r` a point maximizing `Pr[x hidden ∧ response = r]`, this is
`∑ r, max_x Pr[x hidden ∧ response = r] ≤ ε c`. The condition is stated with the other coins of
the tape fixed and for one request at a time: a bound for each fixed request sequence alone does
not suffice against adaptive requests, since an adversary can choose a later request from an
earlier response that is correlated with the later hidden points.

**The result.** `Distinguisher.advantage_acceptProbOn_le_of_hidden_budget`: a distinguisher
without a final unitary and with a budget of `q` query slots distinguishes the games against `E`
and `E'`, on the branches whose logs lie in any set `L`, with advantage at most
`2 q √(n ∑ c, ε c)`; `Distinguisher.advantage_acceptProb_le_of_hidden_budget` for every log.

**The proof** is `O2HSetting.o2h_of_count` (`GordieHowe/Model/Quantum/O2H/Budget.lean`) for the
game as an oracle algorithm (`Distinguisher.gameAlg`), with the oracles differing on the query
branches at the hidden points of the requests of the branch. Its find term, averaged over the
tape and summed over the slots, is bounded request number by request number
(`Budget.sum_mul_sum_prob_queriedOf_hiddenAt_le`):

- the coins of request `c` are redrawn (`HiddenSide.resample`), and the branches are split by the
  slot `s` of request `c` and the logs `p` up to it (`hiddenPiece`, `prob_queriedOf_hiddenAt_le`);
- on the branches with logs `p` up to slot `s`, the game state is the conditional state of the
  logs' visible history (`slice_stage`, `GordieHowe/Model/Quantum/Pure/ClassicalSim.lean`), so it
  reads the coins of request `c` only through its response (`Env.AgreeAlong`,
  `Env.vis_eq_of_agreeAlong`, `stage_apply_eq_of_agree`), and the probability of those logs
  does not depend on them at all (`prob_logsIn_stage_eq_of_agree`);
- the branches with logs `p` query at no more than `q` slots on average
  (`Budget.sum_prob_query_logsIn_le`, from `OracleAlg.StepCount.sum_prob_pre_inter_le`), so a
  weight that depends on the coins only through the response finds a hidden point no better than
  a guess from the response (`sum_mul_sum_indicator_le_of_guess`): each piece contributes at most
  `q n ε c` times the probability of its logs (`Budget.sum_mul_sum_prob_hiddenPiece_le`), and
  the pieces are disjoint (`sum_prob_hiddenPiece_logs_le`).

`sum_toReal_mul_eq_sum_update_of_prod` gives `HiddenSide.resample` for a tape whose request coins
are drawn independently. The per-request find bound for sequential rejection attempts is
`PMF.toReal_guess_mem_rejectedPoints_le` (`GordieHowe/Foundations/ToMathlib/PMFRejectedPoints.lean`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Guessing a hidden set from a reply -/

section Guess

variable {U R ι : Type*} [Fintype U] [Fintype R] [Fintype ι]

/-- **A weight that reads the coins only through a reply finds a hidden set no better than a
guess from the reply.** Let `a ← ν`, a reply `ρ a`, hidden sets `B a` of a finite type `ι`, and
nonnegative weights `w a` on `ι` of total at most `M` that depend on `a` only through `ρ a`. If
every guess `g (ρ a)` computed from the reply lies in `B a` with probability at most `ε`, the
average weight of `B a` is at most `M ε`. -/
theorem sum_mul_sum_indicator_le_of_guess [Nonempty ι] (ν : PMF U) (ρ : U → R) (B : U → Set ι)
    (w : U → ι → ℝ) (hw : ∀ a r, 0 ≤ w a r) (hρ : ∀ a a', ρ a = ρ a' → w a = w a') {M ε : ℝ}
    (hM : ∀ a, ∑ r, w a r ≤ M)
    (hε : ∀ g : R → ι, (ν.toOuterMeasure {a | g (ρ a) ∈ B a}).toReal ≤ ε) :
    ∑ a, (ν a).toReal * ∑ r, (B a).indicator (w a) r ≤ M * ε := by
  classical
  obtain ⟨a₀, -⟩ := ν.support_nonempty
  have hM0 : 0 ≤ M := (sum_nonneg fun r _ => hw a₀ r).trans (hM a₀)
  set π : R → ι → ℝ := fun ρ₀ r => ∑ a, if ρ a = ρ₀ ∧ r ∈ B a then (ν a).toReal else 0 with hπ
  have hπ0 : ∀ ρ₀ r, 0 ≤ π ρ₀ r := fun ρ₀ r => sum_nonneg fun a _ => by
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  choose g hg using fun ρ₀ => exists_max_image univ (π ρ₀) univ_nonempty
  have key : ∀ ρ₀, ∑ a, (if ρ a = ρ₀ then (ν a).toReal * ∑ r, (B a).indicator (w a) r else 0) ≤
      M * π ρ₀ (g ρ₀) := by
    intro ρ₀
    by_cases h : ∃ a₁, ρ a₁ = ρ₀
    · obtain ⟨a₁, ha₁⟩ := h
      have e1 : ∀ a, (if ρ a = ρ₀ then (ν a).toReal * ∑ r, (B a).indicator (w a) r else 0) =
          ∑ r, w a₁ r * (if ρ a = ρ₀ ∧ r ∈ B a then (ν a).toReal else 0) := by
        intro a
        by_cases ha : ρ a = ρ₀
        · simp only [ha, ↓reduceIte, mul_sum, hρ a a₁ (ha.trans ha₁.symm)]
          refine sum_congr rfl fun r _ => ?_
          by_cases hr : r ∈ B a <;> simp [hr, mul_comm]
        · simp [ha]
      calc ∑ a, (if ρ a = ρ₀ then (ν a).toReal * ∑ r, (B a).indicator (w a) r else 0)
          = ∑ r, w a₁ r * π ρ₀ r := by
            rw [sum_congr rfl fun a _ => e1 a, sum_comm]
            simp only [← mul_sum, hπ]
        _ ≤ ∑ r, w a₁ r * π ρ₀ (g ρ₀) :=
            sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ((hg ρ₀).2 r (mem_univ _)) (hw a₁ r)
        _ = (∑ r, w a₁ r) * π ρ₀ (g ρ₀) := by rw [sum_mul]
        _ ≤ M * π ρ₀ (g ρ₀) := mul_le_mul_of_nonneg_right (hM a₁) (hπ0 _ _)
    · simp only [not_exists] at h
      rw [sum_eq_zero fun a _ => by simp [h a]]
      exact mul_nonneg hM0 (hπ0 _ _)
  have hLHS : ∑ a, (ν a).toReal * ∑ r, (B a).indicator (w a) r =
      ∑ ρ₀, ∑ a, (if ρ a = ρ₀ then (ν a).toReal * ∑ r, (B a).indicator (w a) r else 0) := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ => by simp
  have hpr : ∑ ρ₀, π ρ₀ (g ρ₀) = (ν.toOuterMeasure {a | g (ρ a) ∈ B a}).toReal := by
    rw [PMF.toReal_toOuterMeasure_apply, hπ]
    simp only [Set.mem_ofPred_eq]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (ρ a)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  calc ∑ a, (ν a).toReal * ∑ r, (B a).indicator (w a) r
      ≤ ∑ ρ₀, M * π ρ₀ (g ρ₀) := hLHS ▸ sum_le_sum fun ρ₀ _ => key ρ₀
    _ = M * (ν.toOuterMeasure {a | g (ρ a) ∈ B a}).toReal := by rw [← mul_sum, hpr]
    _ ≤ M * ε := mul_le_mul_of_nonneg_left (hε g) hM0

end Guess

/-! ### The slot of a request -/

section Logs

variable {Req : Type*} {m : ℕ}

/-- A filled slot `s` adds its request to the requests before it. -/
theorem requestsBefore_succ_of_eq_some (lg : LogReg Req m) {s : Fin m} {r : Req}
    (h : lg s = some r) : requestsBefore lg (s + 1) = requestsBefore lg s ++ [r] := by
  rw [requestsBefore_succ_of_lt lg s.2, h]
  rfl

/-- **Request number `c` was made at some slot**: if a branch made more than `c` requests, some
slot `s` is filled with `c` requests before it. -/
theorem exists_slot_of_lt_length (lg : LogReg Req m) {c : ℕ} (h : c < (requests lg).length) :
    ∃ s : Fin m, lg s ≠ none ∧ (requestsBefore lg s).length = c := by
  have key : ∀ k ≤ m, c < (requestsBefore lg k).length →
      ∃ s : Fin m, lg s ≠ none ∧ (requestsBefore lg s).length = c := by
    intro k
    induction k with
    | zero => intro _ h0; simp [requestsBefore] at h0
    | succ k ih =>
      intro hk h1
      by_cases h' : c < (requestsBefore lg k).length
      · exact ih (by omega) h'
      · rw [requestsBefore_succ_of_lt lg (show k < m by omega)] at h1
        refine ⟨⟨k, by omega⟩, fun h0 => ?_, show (requestsBefore lg k).length = c from ?_⟩
        · rw [h0] at h1
          simp at h1
          omega
        · rw [List.length_append] at h1
          rcases hl : lg ⟨k, by omega⟩ with _ | r
          · rw [hl] at h1
            simp at h1
            omega
          · rw [hl] at h1
            simp at h1
            omega
  exact key m le_rfl h

/-- **Request number `c` was made at one slot only.** -/
theorem eq_of_length_requestsBefore_eq {lg : LogReg Req m} {s s' : Fin m} (hs : lg s ≠ none)
    (hs' : lg s' ≠ none)
    (h : (requestsBefore lg s).length = (requestsBefore lg s').length) : s = s' := by
  have hlt : ∀ {a b : Fin m}, lg a ≠ none → a < b →
      (requestsBefore lg a).length < (requestsBefore lg b).length := by
    intro a b ha hab
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 ha
    have h1 := (requestsBefore_prefix lg (show (a : ℕ) + 1 ≤ b from hab)).length_le
    rw [requestsBefore_succ_of_eq_some lg hr, List.length_append] at h1
    simp at h1
    omega
  rcases lt_trichotomy s s' with hlt' | heq | hgt
  · exact absurd h (hlt hs hlt').ne
  · exact heq
  · exact absurd h (hlt hs' hgt).ne'

/-- The request of a filled slot, after the requests before it, is a prefix of the requests of
the branch. -/
theorem requestsBefore_append_prefix (lg : LogReg Req m) {s : Fin m} {r : Req}
    (h : lg s = some r) : requestsBefore lg s ++ [r] <+: requests lg := by
  rw [← requestsBefore_succ_of_eq_some lg h]
  exact requestsBefore_prefix lg (show (s : ℕ) + 1 ≤ m from s.2)

/-- Two prefixes `rs₀ ++ [r]` of a list with `rs₀` of the same length are equal. -/
theorem eq_of_append_singleton_prefix {rs rs₀ rs₁ : List Req} {r r' : Req}
    (h₀ : rs₀ ++ [r] <+: rs) (h₁ : rs₁ ++ [r'] <+: rs) (hl : rs₀.length = rs₁.length) :
    rs₀ = rs₁ ∧ r = r' := by
  have hl' : (rs₀ ++ [r]).length ≤ (rs₁ ++ [r']).length := by simp [hl]
  have he := (List.prefix_of_prefix_length_le h₀ h₁ hl').eq_of_length (by simp [hl])
  obtain ⟨h1, h2⟩ := List.append_inj he hl
  exact ⟨h1, by simpa using h2⟩

/-- The logs `lg` with every slot after `s` blanked. -/
def cutAfter (s : ℕ) (lg : LogReg Req m) : LogReg Req m :=
  fun k => if (k : ℕ) ≤ s then lg k else none

/-- The cut keeps the slots up to `s`. -/
theorem cutAfter_apply_of_le (s : ℕ) (lg : LogReg Req m) {k : Fin m} (hk : (k : ℕ) ≤ s) :
    cutAfter s lg k = lg k := by
  simp [cutAfter, hk]

/-- The logs that agree with `lg` on the slots up to `s` have the same cut. -/
theorem cutAfter_congr {s : ℕ} {lg lg' : LogReg Req m}
    (h : ∀ k : Fin m, (k : ℕ) ≤ s → lg k = lg' k) : cutAfter s lg = cutAfter s lg' := by
  funext k
  unfold cutAfter
  split_ifs with hk
  · exact h k hk
  · rfl

/-- The requests up to slot `s` of the logs and of their cut after `s` are the same. -/
theorem requestsBefore_cutAfter (s : ℕ) (lg : LogReg Req m) {k : ℕ} (hk : k ≤ s + 1) :
    requestsBefore (cutAfter s lg) k = requestsBefore lg k :=
  requestsBefore_congr fun k' hk' => cutAfter_apply_of_le s lg (by omega)

end Logs

/-! ### Two tapes that agree along a request sequence -/

namespace Env

variable {Ω Req A X Y : Type*} {St : Type _} {Q : ℕ} (E : Env Ω Req A X Y Q St)
  [OracleState St X Y]

/-- **Two tapes agree along the requests `rs`**: the oracle in force after every prefix of `rs`,
and the response to every request of `rs` after the requests before it, are the same on both. -/
def AgreeAlong (ω ω' : Ω) (rs : List Req) : Prop :=
  (∀ rs₀, rs₀ <+: rs →
    (OracleState.toOracle (E.oracleIn ω rs₀) : X → Y) = OracleState.toOracle (E.oracleIn ω' rs₀)) ∧
  ∀ rs₀ req, rs₀ ++ [req] <+: rs → E.answerAfter ω rs₀ req = E.answerAfter ω' rs₀ req

variable {E}

/-- Agreement along `rs` gives agreement along every prefix of `rs`. -/
theorem AgreeAlong.mono {ω ω' : Ω} {rs rs' : List Req} (h : E.AgreeAlong ω ω' rs)
    (h' : rs' <+: rs) : E.AgreeAlong ω ω' rs' :=
  ⟨fun rs₀ h₀ => h.1 rs₀ (h₀.trans h'), fun rs₀ req h₀ => h.2 rs₀ req (h₀.trans h')⟩

/-- **The visible history of a log reads the tape only along its requests**: two tapes that
agree along the requests before slot `j` give the same visible history up to slot `j`. -/
theorem vis_eq_of_agreeAlong {m : ℕ} {ω ω' : Ω} {lg : LogReg Req m} :
    ∀ {j : ℕ}, E.AgreeAlong ω ω' (requestsBefore lg j) → E.vis ω lg j = E.vis ω' lg j
  | 0, _ => rfl
  | j + 1, h => by
    have h' := h.mono (requestsBefore_prefix lg (Nat.le_succ j))
    rw [vis, vis, vis_eq_of_agreeAlong h']
    split_ifs with hj
    · have hrep : E.visReply ω (requestsBefore lg j) (lg ⟨j, hj⟩) =
          E.visReply ω' (requestsBefore lg j) (lg ⟨j, hj⟩) := by
        rw [requestsBefore_succ_of_lt lg hj] at h
        rcases hl : lg ⟨j, hj⟩ with _ | r
        · simp only [visReply]
          rw [h.1 _ (List.prefix_append _ _)]
        · rw [hl] at h
          simp only [Option.toList_some] at h
          simp only [visReply]
          rw [h.2 _ _ (List.prefix_refl _), h.1 _ (List.prefix_refl _)]
      rw [hrep]
    · rfl

end Env

/-! ### Probabilities of sets of basis states -/

section ProbSets

variable {ι : Type*} [Fintype ι]

/-- A basis permutation that keeps a set and its complement keeps its probability. -/
theorem prob_permOp_of_iff {π : Equiv.Perm ι} {B : Set ι} (h : ∀ r, π r ∈ B ↔ r ∈ B)
    (v : QState ι) : prob B (permOp π v) = prob B v := by
  rw [prob, prob, mask_comm_of_supported (permOp π) (fun v hv => hv.permOp fun r hr => (h r).2 hr)
    (fun v hv => hv.permOp fun r hr hr' => hr ((h r).1 hr')), LinearIsometryEquiv.norm_map]

/-- **Subadditivity**: the probability of a set covered by the sets `F k` is at most the sum of
their probabilities. -/
theorem prob_le_sum_prob_of_subset {κ : Type*} [Fintype κ] {B : Set ι} {F : κ → Set ι}
    (h : B ⊆ ⋃ k, F k) (v : QState ι) : prob B v ≤ ∑ k, prob (F k) v := by
  classical
  simp only [prob, norm_mask_sq, sum_filter]
  rw [sum_comm]
  refine sum_le_sum fun r _ => ?_
  split_ifs with hr
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (h hr)
    refine le_trans ?_ (single_le_sum (f := fun k => if r ∈ F k then ‖v r‖ ^ 2 else 0)
      (fun k _ => by split_ifs <;> positivity) (mem_univ k))
    simp [hk]
  · exact sum_nonneg fun k _ => by split_ifs <;> positivity

/-- The probabilities of pairwise disjoint sets sum to at most the squared norm. -/
theorem sum_prob_le_of_disjoint {κ : Type*} [Fintype κ] (F : κ → Set ι)
    (h : ∀ r k k', r ∈ F k → r ∈ F k' → k = k') (v : QState ι) :
    ∑ k, prob (F k) v ≤ ‖v‖ ^ 2 := by
  classical
  simp only [prob, norm_mask_sq, sum_filter]
  rw [sum_comm, EuclideanSpace.norm_sq_eq]
  refine sum_le_sum fun r _ => ?_
  by_cases hr : ∃ k, r ∈ F k
  · obtain ⟨k, hk⟩ := hr
    rw [sum_eq_single k (fun k' _ hk' => by
      have : r ∉ F k' := fun h' => hk' (h r k' k h' hk)
      simp [this])
      (fun hk' => absurd (mem_univ k) hk')]
    simp [hk]
  · simp only [not_exists] at hr
    rw [sum_eq_zero fun k _ => by simp [hr k]]
    positivity

end ProbSets

/-! ### The game state on sets of logs -/

/-- **A set of logs read up to slot `s`**: logs that agree on the slots up to `s` are both in it
or both out of it. -/
def ReadsUpTo {Req : Type*} {m : ℕ} (N : Set (LogReg Req m)) (s : ℕ) : Prop :=
  ∀ lg lg' : LogReg Req m, (∀ k : Fin m, (k : ℕ) ≤ s → lg k = lg' k) → (lg ∈ N ↔ lg' ∈ N)

/-- The complement of a set of logs read up to `s` is read up to `s`. -/
theorem ReadsUpTo.compl {Req : Type*} {m : ℕ} {N : Set (LogReg Req m)} {s : ℕ}
    (h : ReadsUpTo N s) : ReadsUpTo Nᶜ s :=
  fun lg lg' h' => not_congr (h lg lg' h')

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω : Type*} {Q : ℕ} {St : Type _} [OracleState St X Y]

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- **The probability of a set of logs is the sum of the squared norms of the slices** at the
logs in the set. -/
theorem prob_logsIn_eq_sum (N : Set (LogReg Req m)) (v : QState (GameReg W n X Y Req A m)) :
    prob (logsIn N) v = ∑ lg, N.indicator (fun lg => ‖slice v lg‖ ^ 2) lg := by
  classical
  rw [prob, norm_mask_sq, sum_filter, ← splitLogs.symm.sum_comp, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun lg _ => ?_
  by_cases h : lg ∈ N
  · rw [Set.indicator_of_mem h, EuclideanSpace.norm_sq_eq]
    simp [h, slice_apply]
  · rw [Set.indicator_of_notMem h]
    simp [h]

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- A log-controlled unitary keeps the probability of every set of logs. -/
theorem prob_logsIn_logControlled (N : Set (LogReg Req m))
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (v : QState (GameReg W n X Y Req A m)) :
    prob (logsIn N) (logControlled U v) = prob (logsIn N) v := by
  rw [prob, mask_logControlled, LinearIsometryEquiv.norm_map, ← prob]

omit [AddGroup Y] [OracleState St X Y] in
/-- A request at a slot after `s` keeps every set of logs read up to `s`. -/
theorem mem_logsIn_requestPerm_iff (E : Env Ω Req A X Y Q St) (ω : Ω) {N : Set (LogReg Req m)}
    {s : ℕ} (hN : ReadsUpTo N s) {k : Fin m} (hk : s < k) (r : GameReg W n X Y Req A m) :
    E.requestPerm D.kind ω k r ∈ logsIn N ↔ r ∈ logsIn N := by
  simp only [mem_logsIn]
  rw [Env.logs_requestPerm]
  split_ifs
  · exact hN _ _ fun k' hk' => Function.update_of_ne (fun e => by subst e; omega) _ _
  · exact Iff.rfl

/-- A slot after `s` keeps every set of logs read up to `s`. -/
theorem mem_logsIn_eventPerm_iff (E : Env Ω Req A X Y Q St) (ω : Ω) {N : Set (LogReg Req m)}
    {s k : ℕ} (hN : ReadsUpTo N s) (hk : s < k) (r : GameReg W n X Y Req A m) :
    D.eventPerm E ω k r ∈ logsIn N ↔ r ∈ logsIn N := by
  by_cases hkm : k < m
  · rw [D.eventPerm_of_lt E ω hkm]
    simp only [mem_logsIn, Env.logs_oraclePerm]
    exact D.mem_logsIn_requestPerm_iff E ω hN (k := ⟨k, hkm⟩) hk r
  · rw [D.eventPerm_of_le E ω (not_lt.1 hkm)]

/-- **After slot `s`, the probability of a set of logs read up to `s` stays fixed.** -/
theorem prob_logsIn_stage_eq (E : Env Ω Req A X Y Q St) (ω : Ω) {N : Set (LogReg Req m)} {s : ℕ}
    (hN : ReadsUpTo N s) {k : ℕ} (hk : s + 1 ≤ k) :
    prob (logsIn N) (D.stage E ω k) = prob (logsIn N) (D.stage E ω (s + 1)) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [stage_succ, liftedStep, prob_logsIn_logControlled,
      prob_permOp_of_iff (D.mem_logsIn_eventPerm_iff E ω hN (by omega)), ih]

/-- **The probability of a set of logs read up to `s` reads the tape only along the requests
before `s`**: for two tapes that agree along the requests before slot `s` of every log in the
set, the game states have the same probability of the set from slot `s + 1` on. -/
theorem prob_logsIn_stage_eq_of_agree (E : Env Ω Req A X Y Q St) {ω ω' : Ω}
    {N : Set (LogReg Req m)} {s : ℕ} (hs : s < m) (hN : ReadsUpTo N s)
    (hag : ∀ lg ∈ N, E.AgreeAlong ω ω' (requestsBefore lg s)) {k : ℕ} (hk : s + 1 ≤ k) :
    prob (logsIn N) (D.stage E ω k) = prob (logsIn N) (D.stage E ω' k) := by
  rw [D.prob_logsIn_stage_eq E ω hN hk, D.prob_logsIn_stage_eq E ω' hN hk, prob_logsIn_eq_sum,
    prob_logsIn_eq_sum]
  refine sum_congr rfl fun lg _ => ?_
  by_cases hlg : lg ∈ N
  · rw [Set.indicator_of_mem hlg, Set.indicator_of_mem hlg]
    by_cases hr : lg ∈ reachableLogs (s + 1)
    · rw [D.slice_stage E ω (s + 1) hs lg hr, D.slice_stage E ω' (s + 1) hs lg hr,
        E.vis_succ_of_lt ω lg hs, E.vis_succ_of_lt ω' lg hs, condState_append_singleton,
        condState_append_singleton, norm_condStep, norm_condStep,
        Env.vis_eq_of_agreeAlong (hag lg hlg)]
    · rw [show slice (D.stage E ω (s + 1)) lg = 0 from
          (D.stage_supported E ω (s + 1)).slice_eq_zero hr,
        show slice (D.stage E ω' (s + 1)) lg = 0 from
          (D.stage_supported E ω' (s + 1)).slice_eq_zero hr]
  · rw [Set.indicator_of_notMem hlg, Set.indicator_of_notMem hlg]

/-- **The game state at a basis state reads the tape only along the requests of its logs.** -/
theorem stage_apply_eq_of_agree (E : Env Ω Req A X Y Q St) {ω ω' : Ω} {i : ℕ} (hi : i ≤ m)
    {r : GameReg W n X Y Req A m}
    (hag : E.AgreeAlong ω ω' (requestsBefore (splitLogs r).2 i)) :
    D.stage E ω i r = D.stage E ω' i r := by
  obtain ⟨d, lg, rfl⟩ : ∃ d lg, r = splitLogs.symm (d, lg) :=
    ⟨_, _, (splitLogs.symm_apply_apply r).symm⟩
  simp only [Equiv.apply_symm_apply] at hag
  rw [← slice_apply, ← slice_apply]
  by_cases hr : lg ∈ reachableLogs i
  · rw [D.slice_stage E ω i hi lg hr, D.slice_stage E ω' i hi lg hr,
      Env.vis_eq_of_agreeAlong hag]
  · rw [show slice (D.stage E ω i) lg = 0 from (D.stage_supported E ω i).slice_eq_zero hr,
      show slice (D.stage E ω' i) lg = 0 from (D.stage_supported E ω' i).slice_eq_zero hr]

end Distinguisher

/-! ### Counting the query slots on a set of logs -/

namespace OracleAlg.StepCount

variable {Z ι : Type*} [Fintype ι] {d : ℕ} {A : OracleAlg Z ι d} {z : Z} {G C : ℕ → Set ι}
  {q : ℕ}

/-- **The query slots on a set kept from step `k0` on number at most `q` on average**: if the
steps after oracle step `k0` and the oracle keep a set `N` and its complement, and no branch
of `N` queries before step `k0`, the probabilities of `C i ∩ N` before step `i` sum to at most
`q` times the final probability of `N`. -/
theorem sum_prob_pre_inter_le (h : A.StepCount z G C q) {π : Equiv.Perm ι} (hπ : Respects π G C)
    {N : Set ι} {k0 : ℕ} (hNπ : ∀ r, π r ∈ N ↔ r ∈ N)
    (hN : ∀ k, k0 ≤ k → k < d → ∀ v, Supported N v → Supported N (A.stepAt z (k + 1) v))
    (hNc : ∀ k, k0 ≤ k → k < d → ∀ v, Supported Nᶜ v → Supported Nᶜ (A.stepAt z (k + 1) v))
    (h0 : ∀ i : Fin d, (i : ℕ) < k0 → prob (C i ∩ N) (A.pre π z i) = 0) :
    ∑ i : Fin d, prob (C i ∩ N) (A.pre π z i) ≤ q * prob N (A.final π z) := by
  classical
  have hmask : ∀ (B B' : Set ι) (v : QState ι), mask (B ∩ B') v = mask B (mask B' v) :=
    fun B B' v => by
      ext r
      by_cases h1 : r ∈ B <;> by_cases h2 : r ∈ B' <;> simp [h1, h2]
  have hcomm : ∀ i k, i ≤ k → k0 ≤ k → k < d → ∀ v,
      mask (C i ∩ N) (A.stepAt z (k + 1) (permOp π v)) =
        A.stepAt z (k + 1) (permOp π (mask (C i ∩ N) v)) := by
    intro i k hik hk0 hk v
    rw [hmask, hmask,
      mask_comm_of_supported (A.stepAt z (k + 1)) (hN k hk0 hk) (hNc k hk0 hk),
      mask_comm_of_supported (permOp π) (fun v hv => hv.permOp fun r hr => (hNπ r).2 hr)
        (fun v hv => hv.permOp fun r hr hr' => hr ((hNπ r).1 hr')),
      mask_comm_of_supported (A.stepAt z (k + 1)) (h.stepC i k hik hk) (h.stepCc i k hik hk),
      mask_comm_of_supported (permOp π) (fun v hv => hv.permOp fun r hr => (hπ.mem_iff i r).2 hr)
        (fun v hv => hv.permOp fun r hr hr' => hr ((hπ.mem_iff i r).1 hr'))]
  have hnorm : ∀ i k, i ≤ k → k0 ≤ i → k ≤ d →
      prob (C i ∩ N) (A.stage π z k) = prob (C i ∩ N) (A.stage π z i) := by
    intro i k hik hi0 hkd
    induction k, hik using Nat.le_induction with
    | base => rfl
    | succ k hik ih =>
      rw [stage_succ, prob, hcomm i k hik (by omega) (by omega), LinearIsometryEquiv.norm_map,
        LinearIsometryEquiv.norm_map, ← prob, ih (by omega)]
  have hfin := h.stage_supported hπ d le_rfl
  have hpt : ∀ r, ∑ i ∈ range d, (if r ∈ C i ∩ N then ‖A.final π z r‖ ^ 2 else 0) ≤
      q * (if r ∈ N then ‖A.final π z r‖ ^ 2 else 0) := by
    intro r
    by_cases hrN : r ∈ N
    · simp only [Set.mem_inter_iff, hrN, and_true, ↓reduceIte]
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      by_cases hr : r ∈ G d
      · gcongr
        exact_mod_cast h.count r hr
      · rw [show A.final π z r = 0 from hfin r hr, norm_zero, zero_pow two_ne_zero, mul_zero,
          mul_zero]
    · simp [hrN]
  calc ∑ i : Fin d, prob (C i ∩ N) (A.pre π z i)
      ≤ ∑ i ∈ range d, prob (C i ∩ N) (A.final π z) := by
        rw [sum_range (fun i => prob (C i ∩ N) (A.final π z))]
        refine sum_le_sum fun i _ => ?_
        by_cases hi : (i : ℕ) < k0
        · rw [h0 i hi]
          exact prob_nonneg _ _
        · exact (hnorm i d i.2.le (by omega) le_rfl).symm.le
    _ = ∑ r, ∑ i ∈ range d, (if r ∈ C i ∩ N then ‖A.final π z r‖ ^ 2 else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [prob, norm_mask_sq, sum_filter]
    _ ≤ ∑ r, q * (if r ∈ N then ‖A.final π z r‖ ^ 2 else 0) := sum_le_sum fun r _ => hpt r
    _ = q * prob N (A.final π z) := by
        rw [← mul_sum, prob, norm_mask_sq, sum_filter]

end OracleAlg.StepCount

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω : Type*} {Q : ℕ}

/-- The final state of the game as an oracle algorithm, run with its own oracle: `post`
controlled by the logs after the game. -/
theorem gameAlg_final_eq (E : Env Ω Req A X Y Q)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (L : Set (LogReg Req m)) (ω : Ω) :
    (D.gameAlg E post L).final (queryPermOf (E.oracleFn D.kind ω)) ω =
      postOp E post ω (D.run E ω) := by
  set A := D.gameAlg E post L
  have hstep : ∀ t (ht : t < m + 1), A.stepAt ω t = D.gameStep E post ω t := fun t ht => by
    rw [OracleAlg.stepAt_of_lt _ ht]
    rfl
  have hlt := D.gameAlg_stage E post E L ω fun _ _ => rfl
  rw [OracleAlg.final, run]
  cases m with
  | zero =>
    rw [OracleAlg.stage, hybrid_zero, hstep 0 (by omega), gameStep, dif_neg (lt_irrefl 0)]
    rfl
  | succ k =>
    rw [OracleAlg.stage, hybrid_succ, ← OracleAlg.stage, hlt k (by omega), hstep _ (by omega),
      gameStep, dif_neg (lt_irrefl _), LinearIsometryEquiv.trans_apply, D.stage_succ,
      eventPerm, dif_pos (show k < k + 1 by omega), permOp_trans]
    simp only [Env.oraclePerm_eq]

omit [AddGroup Y] in
/-- The steps of the game as an oracle algorithm after slot `s` keep the logs read up to `s`. -/
theorem supported_gameStep_of_readsUpTo (E : Env Ω Req A X Y Q)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (ω : Ω) {N : Set (LogReg Req m)} {s k : ℕ} (hN : ReadsUpTo N s) (hk : s < k)
    {v : QState (GameReg W n X Y Req A m)} (hv : Supported (logsIn N) v) :
    Supported (logsIn N) (D.gameStep E post ω k v) := by
  have h1 := hv.logControlled (fun _ => D.stepAt k)
  unfold gameStep
  split_ifs with hkm
  · rw [LinearIsometryEquiv.trans_apply]
    exact h1.permOp fun r hr => (D.mem_logsIn_requestPerm_iff E ω hN (k := ⟨k, hkm⟩) hk r).2 hr
  · rw [LinearIsometryEquiv.trans_apply]
    exact h1.logControlled _

namespace Budget

variable {D} {q : ℕ}

/-- **On a set of logs read up to a filled slot `s`, the branches query at no more than `q`
slots on average**: the probabilities of the query branches with logs in `N` before each slot
sum to at most `q` times the final probability of `N`. -/
theorem sum_prob_query_logsIn_le (bud : D.Budget q) (E : Env Ω Req A X Y Q) (ω : Ω)
    {N : Set (LogReg Req m)} {s : Fin m} (hN : ReadsUpTo N s) (hfill : ∀ lg ∈ N, lg s ≠ none) :
    ∑ i : Fin m, prob ({r | D.kind r.workspace = false} ∩ logsIn N) (D.stage E ω i) ≤
      q * prob (logsIn N) (D.run E ω) := by
  classical
  set Alg := D.gameAlg E noPost Set.univ
  set π := queryPermOf (n := n) (E.oracleFn D.kind ω)
  set K : Set (GameReg W n X Y Req A m) := {r | D.kind r.workspace = false}
  have hc := bud.stepCount_gameAlg noPost E Set.univ ω
  have hres := respects_queryPermOf (n := n) (E.oracleFn D.kind ω)
    (fun k => {s | bud.Holds k s})
    (fun i => {s : W × Req × Option A × LogReg Req m | queriedAt s.2.2.2 i = true})
  have hpre : ∀ i : Fin m, Alg.pre π ω i =
      permOp (E.requestPerm D.kind ω ⟨i, i.2⟩) (D.stage E ω i) := fun i =>
    D.gameAlg_stage E noPost E Set.univ ω (fun _ _ => rfl) i i.2
  have hstep1 : ∀ i : Fin m, prob (K ∩ logsIn N) (D.stage E ω i) ≤
      prob ({r | r.1 ∈ {s : W × Req × Option A × LogReg Req m | queriedAt s.2.2.2 i = true}} ∩
        logsIn N) (Alg.pre π ω i) := by
    intro i
    have heq : prob (K ∩ logsIn N) (D.stage E ω i) = prob (K ∩ logsIn N) (Alg.pre π ω i) := by
      rw [hpre, prob_permOp_of_iff]
      intro r
      cases hk : D.kind r.workspace
      · rw [D.requestPerm_of_query E ω i.2 hk]
      · have hw := E.workspace_requestPerm D.kind ω ⟨i, i.2⟩ r
        simp only [K, Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, -⟩
          change D.kind (E.requestPerm D.kind ω ⟨i, i.2⟩ r).1.1 = false at h1
          rw [hw] at h1
          exact absurd (hk.symm.trans h1) (by simp)
        · rintro ⟨h1, -⟩
          exact absurd (hk.symm.trans h1) (by simp)
    rw [heq]
    refine (hc.stage_supported hres i i.2.le).prob_le_of_inter_subset fun r hr hG => ⟨?_, hr.2⟩
    have := hG.logged i.2
    change queriedAt r.1.2.2.2 i = true
    rw [this, show D.kind r.1.1 = false from hr.1]
    rfl
  have hNc : (logsIn N)ᶜ = logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A) Nᶜ := by
    ext r
    simp [mem_logsIn]
  have hkeep : ∀ N' : Set (LogReg Req m), ReadsUpTo N' s → ∀ k, (s : ℕ) + 1 ≤ k → k < m → ∀ v,
      Supported (logsIn N') v → Supported (logsIn N') (Alg.stepAt ω (k + 1) v) := by
    intro N' hN' k _ hk v hv
    rw [gameAlg_stepAt noPost E Set.univ ω (by omega)]
    exact D.supported_gameStep_of_readsUpTo E noPost ω hN' (by omega) hv
  have h0 : ∀ i : Fin m, (i : ℕ) < (s : ℕ) + 1 → prob ({r | r.1 ∈ {s : W × Req × Option A ×
      LogReg Req m | queriedAt s.2.2.2 i = true}} ∩ logsIn N) (Alg.pre π ω i) = 0 := by
    intro i hi
    refine (hc.stage_supported hres i i.2.le).prob_eq_zero fun r hr hG => ?_
    have hfs := hfill _ hr.2
    have hq : queriedAt r.1.2.2.2 i = true := hr.1
    rcases Nat.lt_or_ge (i : ℕ) s with his | his
    · exact hfs (hG.blank s his)
    · have hie : i = s := Fin.ext (by omega)
      subst hie
      simp only [queriedAt, i.2, ↓reduceDIte, Option.isNone_iff_eq_none] at hq
      exact hfs hq
  have hcount := hc.sum_prob_pre_inter_le hres (N := logsIn N) (k0 := (s : ℕ) + 1) (fun r => Iff.rfl)
    (hkeep N hN) (hNc ▸ hkeep Nᶜ hN.compl) h0
  rw [gameAlg_final_eq, postOp, prob_logsIn_logControlled] at hcount
  exact (sum_le_sum fun i _ => hstep1 i).trans hcount

end Budget

end Distinguisher

/-! ### Environments whose oracles differ at hidden points of each request -/

section Hidden

variable {Ω Req A X Y : Type*} [Fintype Ω] {Q : ℕ} {U : Type*} [Fintype U]

/-- **Two environments whose oracles differ at hidden points of each request.** The environments
`E` and `E'` have the same tape law (`law`) and the same responses (`answer`). After the requests
`rs`, their oracles in force agree outside the sets `hidden ω rs₀ req` of the requests `req` of
`rs` numbered below `Q`, `rs₀` the requests before `req` (`oracle`). The coins of request number
`c` are a component `a ← ν` of the tape that can be redrawn (`res c ω a`: the tape `ω` with
those coins replaced by `a`) without changing the tape law (`resample`), and, on `E`, they reach
the responses and the oracles in force along any request sequence only through the response to
request number `c` (`agree`). -/
structure HiddenSide (E E' : Env Ω Req A X Y Q) (ν : PMF U) (res : Fin Q → Ω → U → Ω)
    (hidden : Ω → List Req → Req → Set X) : Prop where
  /-- The same tape law. -/
  law : E'.μ = E.μ
  /-- The same responses. -/
  answer : ∀ ω rs req, E.answerAfter ω rs req = E'.answerAfter ω rs req
  /-- The oracles in force agree outside the hidden points of the requests. -/
  oracle : ∀ ω rs x, (∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length < Q → x ∉ hidden ω rs₀ req) →
    E.oracleIn ω rs x = E'.oracleIn ω rs x
  /-- Redrawing the coins of request number `c` keeps the tape law. -/
  resample : ∀ (c : Fin Q) (f : Ω → ℝ), ∑ ω, (E.μ ω).toReal * f ω =
    ∑ ω, (E.μ ω).toReal * ∑ a, (ν a).toReal * f (res c ω a)
  /-- On `E`, the coins of request number `c` reach the responses and the oracles in force along
  a request sequence only through the response to request number `c`. -/
  agree : ∀ (c : Fin Q) ω a a' rs, (∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length = (c : ℕ) →
      E.answerAfter (res c ω a) rs₀ req = E.answerAfter (res c ω a') rs₀ req) →
    E.AgreeAlong (res c ω a) (res c ω a') rs

/-- **Redrawing the coins of one request of a product tape keeps its law**: for tapes `(v, u)`
with `v ← μV` and the coins `u c ← ν` of the requests drawn independently, the identity
`HiddenSide.resample` with `res c (v, u) a = (v, Function.update u c a)`. -/
theorem sum_toReal_mul_eq_sum_update_of_prod {V : Type*} [Fintype V] (μ : PMF (V × (Fin Q → U)))
    (μV : PMF V) (ν : PMF U) (hμ : ∀ v u, μ (v, u) = μV v * PMF.pi (fun _ => ν) u) (c : Fin Q)
    (f : V × (Fin Q → U) → ℝ) :
    ∑ ω, (μ ω).toReal * f ω =
      ∑ ω, (μ ω).toReal * ∑ a, (ν a).toReal * f (ω.1, Function.update ω.2 c a) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  simp only [hμ, ENNReal.toReal_mul, mul_assoc, ← mul_sum]
  congr 1
  exact PMF.sum_toReal_pi_mul_eq_sum_update (fun _ => ν) c (fun u => f (v, u))

end Hidden

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω : Type*} {Q : ℕ}

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] in
/-- **The hidden points of request number `c`** on a query branch with work register content
`w`: the points of `hidden ω rs₀ req` for the prefix `rs₀ ++ [req]` of the branch's requests with
`rs₀` of length `c`; no points on a request branch. -/
def hiddenAt (hidden : Ω → List Req → Req → Set X) (c : ℕ) (ω : Ω)
    (w : W × Req × Option A × LogReg Req m) : Set X :=
  if D.kind w.1 = false then
    {x | ∃ rs₀ req, rs₀ ++ [req] <+: requests w.2.2.2 ∧ rs₀.length = c ∧ x ∈ hidden ω rs₀ req}
  else ∅

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] in
/-- **The piece of the hidden points of request number `c` made at slot `s` after the logs
`p`**: the query branches whose logs up to slot `s` are those of `p`, where slot `s` of `p` holds
request number `c`, that query a point of `hidden ω` at that request. -/
def hiddenPiece (hidden : Ω → List Req → Req → Set X) (c : ℕ) (ω : Ω) (s : Fin m)
    (p : LogReg Req m) : Set (GameReg W n X Y Req A m) :=
  {r | ∃ req, p s = some req ∧ (requestsBefore p s).length = c ∧
    r ∈ queried (hidden ω (requestsBefore p s) req) ∧ D.kind r.workspace = false ∧
    cutAfter s (splitLogs r).2 = p}

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- **The hidden points of request number `c` split by the slot of the request and the logs up
to it.** -/
theorem prob_queriedOf_hiddenAt_le (hidden : Ω → List Req → Req → Set X) (c : ℕ) (ω : Ω)
    (v : QState (GameReg W n X Y Req A m)) :
    prob (queriedOf (D.hiddenAt hidden c ω)) v ≤
      ∑ sp : Fin m × LogReg Req m, prob (D.hiddenPiece hidden c ω sp.1 sp.2) v := by
  refine prob_le_sum_prob_of_subset (fun r hr => ?_) v
  obtain ⟨j, hj⟩ := hr
  by_cases hk : D.kind r.1.1 = false
  · have hj' : (r.2 j).1 ∈ {x | ∃ rs₀ req, rs₀ ++ [req] <+: requests r.1.2.2.2 ∧
        rs₀.length = c ∧ x ∈ hidden ω rs₀ req} := by
      have : D.hiddenAt hidden c ω r.1 = _ := if_pos hk
      exact this ▸ hj
    obtain ⟨rs₀, req, hpre, hlen, hx⟩ := hj'
    have hc : c < (requests r.1.2.2.2).length := by
      have := hpre.length_le
      rw [List.length_append, List.length_singleton] at this
      omega
    obtain ⟨s, hs, hsc⟩ := exists_slot_of_lt_length r.1.2.2.2 hc
    obtain ⟨req', hreq'⟩ := Option.ne_none_iff_exists'.1 hs
    obtain ⟨e1, e2⟩ := eq_of_append_singleton_prefix hpre
      (requestsBefore_append_prefix r.1.2.2.2 hreq') (by rw [hlen, hsc])
    have hrb : requestsBefore (cutAfter s r.1.2.2.2) s = requestsBefore r.1.2.2.2 s :=
      requestsBefore_cutAfter _ _ (by omega)
    refine Set.mem_iUnion.2 ⟨(s, cutAfter s r.1.2.2.2), req, ?_, ?_, ⟨j, ?_⟩, hk, rfl⟩
    · show cutAfter s r.1.2.2.2 s = some req
      rw [cutAfter_apply_of_le _ _ le_rfl, hreq', e2]
    · show (requestsBefore (cutAfter s r.1.2.2.2) s).length = c
      rw [hrb, hsc]
    · show (r.2 j).1 ∈ hidden ω (requestsBefore (cutAfter s r.1.2.2.2) s) req
      rw [hrb, ← e1]
      exact hx
  · have : D.hiddenAt hidden c ω r.1 = ∅ := if_neg hk
    rw [this] at hj
    exact absurd hj (Set.notMem_empty _)

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- **The pieces of the hidden points of one request number are disjoint**: a branch made that
request at one slot only, after one log. -/
theorem sum_prob_hiddenPiece_logs_le (c : ℕ) (v : QState (GameReg W n X Y Req A m)) :
    ∑ sp : Fin m × LogReg Req m, prob {r : GameReg W n X Y Req A m | (sp.2 sp.1 ≠ none ∧
      (requestsBefore sp.2 sp.1).length = c) ∧ cutAfter sp.1 (splitLogs r).2 = sp.2} v ≤
      ‖v‖ ^ 2 := by
  refine sum_prob_le_of_disjoint _ (fun r sp sp' h h' => ?_) v
  obtain ⟨⟨hs, hc⟩, hp⟩ := h
  obtain ⟨⟨hs', hc'⟩, hp'⟩ := h'
  set lg := (splitLogs r).2
  have hfill : ∀ (s : Fin m) (p : LogReg Req m), cutAfter s lg = p → p s ≠ none →
      (requestsBefore p s).length = c → lg s ≠ none ∧ (requestsBefore lg s).length = c := by
    intro s p hp hs hc
    subst hp
    rw [cutAfter_apply_of_le _ _ le_rfl] at hs
    rw [requestsBefore_cutAfter _ _ (by omega)] at hc
    exact ⟨hs, hc⟩
  obtain ⟨h1, h2⟩ := hfill _ _ hp hs hc
  obtain ⟨h1', h2'⟩ := hfill _ _ hp' hs' hc'
  have hss : sp.1 = sp'.1 := eq_of_length_requestsBefore_eq h1 h1' (h2.trans h2'.symm)
  refine Prod.ext hss ?_
  rw [← hp, ← hp', hss]

end Distinguisher

/-! ### The find probability of one piece -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} {D : Distinguisher W X Y Req A n m} [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω : Type*} [Fintype Ω] {Q : ℕ} {U : Type*} [Fintype U] {q : ℕ}

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- The probability of a set as a sum of squared amplitudes. -/
theorem prob_eq_sum_indicator {ι : Type*} [Fintype ι] (B : Set ι) (v : QState ι) :
    prob B v = ∑ r, B.indicator (fun r => ‖v r‖ ^ 2) r := by
  classical
  rw [prob, norm_mask_sq, sum_filter]
  exact sum_congr rfl fun r _ => by simp [Set.indicator_apply]

namespace Budget

/-- **One piece of the hidden points, averaged over the coins of its request**: the query
branches whose slot `s` holds request number `c`, after the logs `p`, query a hidden point of
that request, summed over the slots and averaged over the coins `a ← ν` of the request, with
probability at most `q` times the probability of the logs `p` up to slot `s` (which does not
depend on `a`) times `n ε`, for `ε` bounding the probability that a guess computed from the
response to the request is a hidden point of it. -/
theorem sum_mul_sum_prob_hiddenPiece_le (bud : D.Budget q) {E E' : Env Ω Req A X Y Q}
    {ν : PMF U} {res : Fin Q → Ω → U → Ω} {hidden : Ω → List Req → Req → Set X}
    (hE : HiddenSide E E' ν res hidden) (c : Fin Q) {ε : ℝ}
    (hfind : ∀ ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε)
    (ω : Ω) {s : Fin m} {p : LogReg Req m} {req : Req} (hps : p s = some req)
    (hpc : (requestsBefore p s).length = c) (a₀ : U) :
    ∑ a, (ν a).toReal * ∑ i : Fin m, prob (D.hiddenPiece hidden c (res c ω a) s p)
      (D.stage E (res c ω a) i) ≤
      q * prob (logsIn (cutAfter s ⁻¹' {p})) (D.run E (res c ω a₀)) * (n * ε) := by
  classical
  set F : Set (LogReg Req m) := cutAfter s ⁻¹' {p} with hFdef
  have hF : ReadsUpTo F s := fun lg lg' h => by
    simp only [F, Set.mem_preimage, Set.mem_singleton_iff, cutAfter_congr h]
  have hFlg : ∀ lg ∈ F, lg s = some req ∧ requestsBefore lg s = requestsBefore p s :=
    fun lg hlg => by
      have hlg' : cutAfter s lg = p := hlg
      refine ⟨?_, ?_⟩
      · rw [← hps, ← hlg', cutAfter_apply_of_le _ _ le_rfl]
      · rw [← hlg', requestsBefore_cutAfter _ _ (by omega)]
  set K : Set (GameReg W n X Y Req A m) := {r | D.kind r.workspace = false}
  set ω' : U → Ω := res c ω
  set H : U → Set X := fun a => hidden (ω' a) (requestsBefore p s) req
  set ρ : U → Option A := fun a => E.answerAfter (ω' a) (requestsBefore p s) req
  set w : U → GameReg W n X Y Req A m → ℝ := fun a r =>
    ∑ i : Fin m, (K ∩ logsIn F).indicator (fun r => ‖D.stage E (ω' a) i r‖ ^ 2) r
  have hpiece : ∀ a, D.hiddenPiece hidden c (ω' a) s p = queried (H a) ∩ K ∩ logsIn F := by
    intro a
    ext r
    simp only [hiddenPiece, hps, Option.some.injEq, hpc, Set.mem_ofPred_eq, Set.mem_inter_iff,
      mem_logsIn, F, Set.mem_preimage, Set.mem_singleton_iff, K, H]
    constructor
    · rintro ⟨req', rfl, -, h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨req, rfl, trivial, h1, h2, h3⟩
  have hag : ∀ a a', ρ a = ρ a' → ∀ lg ∈ F, ∀ i ≤ m,
      E.AgreeAlong (ω' a) (ω' a') (requestsBefore lg i) := by
    intro a a' hρ lg hlg i hi
    refine hE.agree c ω a a' _ fun rs₀ req' hpre hlen => ?_
    obtain ⟨h1, h2⟩ := hFlg lg hlg
    have hp1 : rs₀ ++ [req'] <+: requests lg := hpre.trans (requestsBefore_prefix lg hi)
    obtain ⟨e1, e2⟩ := eq_of_append_singleton_prefix hp1 (requestsBefore_append_prefix lg h1)
      (by rw [hlen, h2, hpc])
    rw [e1, e2, h2]
    exact hρ
  have hag0 : ∀ a a', ∀ lg ∈ F, E.AgreeAlong (ω' a) (ω' a') (requestsBefore lg s) := by
    intro a a' lg hlg
    refine hE.agree c ω a a' _ fun rs₀ req' hpre hlen => ?_
    have := hpre.length_le
    rw [(hFlg lg hlg).2, hpc] at this
    simp at this
    omega
  have hw : ∀ a r, 0 ≤ w a r := fun a r =>
    sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hρw : ∀ a a', ρ a = ρ a' → w a = w a' := by
    intro a a' hρ
    funext r
    refine sum_congr rfl fun i _ => ?_
    by_cases hr : r ∈ K ∩ logsIn F
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr,
        D.stage_apply_eq_of_agree E i.2.le (hag a a' hρ _ hr.2 i i.2.le)]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
  have hrun : ∀ a, prob (logsIn F) (D.run E (ω' a)) = prob (logsIn F) (D.run E (ω' a₀)) :=
    fun a => D.prob_logsIn_stage_eq_of_agree E s.2 hF (hag0 a a₀) (k := m) (by omega)
  have hM : ∀ a, ∑ r, w a r ≤ q * prob (logsIn F) (D.run E (ω' a₀)) := by
    intro a
    have hsum : ∑ r, w a r = ∑ i : Fin m, prob (K ∩ logsIn F) (D.stage E (ω' a) i) := by
      simp only [w, prob_eq_sum_indicator]
      rw [sum_comm]
    rw [hsum, ← hrun a]
    exact bud.sum_prob_query_logsIn_le E (ω' a) hF fun lg hlg => by
      rw [(hFlg lg hlg).1]
      simp
  have hε : ∀ g : Option A → GameReg W n X Y Req A m,
      (ν.toOuterMeasure {a | g (ρ a) ∈ queried (H a)}).toReal ≤ n * ε := by
    intro g
    have hset : {a | g (ρ a) ∈ queried (W := W × Req × Option A × LogReg Req m) (n := n)
        (Y := Y) (H a)} = ⋃ j : Fin n, {a | ((g (ρ a)).2 j).1 ∈ H a} := by
      ext a
      simp [queried]
    rw [hset]
    refine (PMF.toReal_toOuterMeasure_iUnion_le _ _).trans ?_
    calc ∑ j : Fin n, (ν.toOuterMeasure {a | ((g (ρ a)).2 j).1 ∈ H a}).toReal
        ≤ ∑ _j : Fin n, ε :=
          sum_le_sum fun j _ => hfind ω _ req hpc fun ρ₀ => ((g ρ₀).2 j).1
      _ = n * ε := by simp
  have hL : ∀ a, ∑ i : Fin m, prob (queried (H a) ∩ K ∩ logsIn F) (D.stage E (ω' a) i) =
      ∑ r, (queried (H a)).indicator (w a) r := by
    intro a
    simp only [w, prob_eq_sum_indicator]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    by_cases hB : r ∈ queried (W := W × Req × Option A × LogReg Req m) (n := n) (Y := Y) (H a)
    · rw [Set.indicator_of_mem hB]
      refine sum_congr rfl fun i _ => ?_
      simp only [Set.indicator_apply, Set.mem_inter_iff, hB, true_and]
    · rw [Set.indicator_of_notMem hB]
      exact sum_eq_zero fun i _ => by simp [hB]
  have : Nonempty (GameReg W n X Y Req A m) := by
    obtain ⟨d⟩ := D.nonempty_dReg
    exact ⟨splitLogs.symm (d, fun _ => none)⟩
  simp only [hpiece, hL]
  exact sum_mul_sum_indicator_le_of_guess ν ρ (fun a => queried (H a)) w hw hρw hM hε

end Budget

end Distinguisher

/-! ### The whole run -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} {D : Distinguisher W X Y Req A n m} [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω : Type*} [Fintype Ω] {Q : ℕ} {U : Type*} [Fintype U] {q : ℕ}

omit [Fintype Ω] in
/-- The game state after the last step is a unit vector. -/
theorem norm_run_env {St : Type _} [OracleState St X Y] (E : Env Ω Req A X Y Q St) (ω : Ω) :
    ‖D.run E ω‖ = 1 := by
  have h : ∀ k, ‖D.stage E ω k‖ = 1 := fun k => by
    induction k with
    | zero => rw [stage, hybrid_zero, LinearIsometryEquiv.norm_map, D.norm_gameInit]
    | succ k ih => rw [stage_succ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, ih]
  exact h m

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] [Fintype Ω] in
/-- The empty set has probability zero. -/
theorem prob_empty' {ι : Type*} [Fintype ι] (v : QState ι) : prob ∅ v = 0 := by
  rw [prob_eq_sum_indicator]
  simp

namespace Budget

/-- **The find probability of request number `c`**: averaged over the tape, and summed over the
oracle steps of the game as an oracle algorithm, the probability that a query branch queries a
hidden point of request number `c` is at most `n ε q`. -/
theorem sum_mul_sum_prob_queriedOf_hiddenAt_le (bud : D.Budget q) {E E' : Env Ω Req A X Y Q}
    {ν : PMF U} {res : Fin Q → Ω → U → Ω} {hidden : Ω → List Req → Req → Set X}
    (hE : HiddenSide E E' ν res hidden) (c : Fin Q) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hfind : ∀ ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε)
    (L : Set (LogReg Req m)) :
    ∑ ω, (E.μ ω).toReal * ∑ i : Fin m, prob (queriedOf (D.hiddenAt hidden c ω))
      ((D.gameAlg E noPost L).pre (queryPermOf (E.oracleFn D.kind ω)) ω i) ≤ n * ε * q := by
  classical
  obtain ⟨a₀, -⟩ := ν.support_nonempty
  have hpre : ∀ ω (i : Fin m), prob (queriedOf (D.hiddenAt hidden c ω))
      ((D.gameAlg E noPost L).pre (queryPermOf (E.oracleFn D.kind ω)) ω i) =
      prob (queriedOf (D.hiddenAt hidden c ω)) (D.stage E ω i) := by
    intro ω i
    rw [OracleAlg.pre, D.gameAlg_stage E noPost E L ω (fun _ _ => rfl) i i.2, prob_permOp_of_iff]
    intro r
    cases hk : D.kind r.1.1
    · rw [D.requestPerm_of_query E ω i.2 hk]
    · have hw := E.workspace_requestPerm D.kind ω ⟨i, i.2⟩ r
      have h1 : D.hiddenAt hidden c ω (E.requestPerm D.kind ω ⟨i, i.2⟩ r).1 = ∅ := by
        unfold hiddenAt
        rw [if_neg (by rw [hw]; simp [GameReg.workspace, hk])]
      have h2 : D.hiddenAt hidden c ω r.1 = ∅ := by
        unfold hiddenAt
        rw [if_neg (by simp [hk])]
      constructor
      · rintro ⟨j, hj⟩
        rw [h1] at hj
        exact absurd hj (Set.notMem_empty _)
      · rintro ⟨j, hj⟩
        rw [h2] at hj
        exact absurd hj (Set.notMem_empty _)
  simp only [hpre]
  rw [hE.resample c]
  have inner : ∀ ω, ∑ a, (ν a).toReal * ∑ i : Fin m,
      prob (queriedOf (D.hiddenAt hidden c (res c ω a))) (D.stage E (res c ω a) i) ≤
        n * ε * q := by
    intro ω
    set F : Fin m × LogReg Req m → Set (GameReg W n X Y Req A m) := fun sp =>
      {r | (sp.2 sp.1 ≠ none ∧ (requestsBefore sp.2 sp.1).length = c) ∧
        cutAfter sp.1 (splitLogs r).2 = sp.2} with hFdef
    have hterm : ∀ sp : Fin m × LogReg Req m, ∑ a, (ν a).toReal * ∑ i : Fin m,
        prob (D.hiddenPiece hidden c (res c ω a) sp.1 sp.2) (D.stage E (res c ω a) i) ≤
          q * prob (F sp) (D.run E (res c ω a₀)) * (n * ε) := by
      intro sp
      by_cases hcond : sp.2 sp.1 ≠ none ∧ (requestsBefore sp.2 sp.1).length = c
      · obtain ⟨req, hreq⟩ := Option.ne_none_iff_exists'.1 hcond.1
        have hFeq : F sp = logsIn (cutAfter sp.1 ⁻¹' {sp.2}) := by
          ext r
          simp [F, hcond, mem_logsIn]
        rw [hFeq]
        exact bud.sum_mul_sum_prob_hiddenPiece_le hE c hfind ω hreq hcond.2 a₀
      · have hP : ∀ a, D.hiddenPiece hidden c (res c ω a) sp.1 sp.2 = ∅ := fun a => by
          ext r
          simp only [hiddenPiece, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨req, h1, h2, -⟩
          exact hcond ⟨by rw [h1]; simp, h2⟩
        have hF0 : F sp = ∅ := by
          ext r
          simp only [F, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hcond h.1
        simp only [hP, hF0, prob_empty', sum_const_zero, mul_zero, zero_mul, le_refl]
    have hswap : ∀ a, (ν a).toReal * ∑ i : Fin m, ∑ sp : Fin m × LogReg Req m,
        prob (D.hiddenPiece hidden c (res c ω a) sp.1 sp.2) (D.stage E (res c ω a) i) =
        ∑ sp : Fin m × LogReg Req m, (ν a).toReal * ∑ i : Fin m,
          prob (D.hiddenPiece hidden c (res c ω a) sp.1 sp.2) (D.stage E (res c ω a) i) :=
      fun a => by rw [sum_comm, mul_sum]
    calc ∑ a, (ν a).toReal * ∑ i : Fin m,
          prob (queriedOf (D.hiddenAt hidden c (res c ω a))) (D.stage E (res c ω a) i)
        ≤ ∑ a, (ν a).toReal * ∑ i : Fin m, ∑ sp : Fin m × LogReg Req m,
          prob (D.hiddenPiece hidden c (res c ω a) sp.1 sp.2) (D.stage E (res c ω a) i) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (sum_le_sum fun i _ =>
            D.prob_queriedOf_hiddenAt_le hidden c _ _) ENNReal.toReal_nonneg
      _ = ∑ sp : Fin m × LogReg Req m, ∑ a, (ν a).toReal * ∑ i : Fin m,
          prob (D.hiddenPiece hidden c (res c ω a) sp.1 sp.2) (D.stage E (res c ω a) i) := by
          simp only [hswap]
          rw [sum_comm]
      _ ≤ ∑ sp : Fin m × LogReg Req m, q * prob (F sp) (D.run E (res c ω a₀)) * (n * ε) :=
          sum_le_sum fun sp _ => hterm sp
      _ = q * (n * ε) * ∑ sp : Fin m × LogReg Req m, prob (F sp) (D.run E (res c ω a₀)) := by
          rw [mul_sum]
          exact sum_congr rfl fun sp _ => by ring
      _ ≤ q * (n * ε) * 1 := by
          gcongr
          have h := sum_prob_hiddenPiece_logs_le (W := W) (n := n) (X := X) (Y := Y) (A := A)
            (c : ℕ) (D.run E (res c ω a₀))
          rwa [norm_run_env, one_pow] at h
      _ = n * ε * q := by ring
  calc ∑ ω, (E.μ ω).toReal * ∑ a, (ν a).toReal * ∑ i : Fin m,
        prob (queriedOf (D.hiddenAt hidden c (res c ω a))) (D.stage E (res c ω a) i)
      ≤ ∑ ω, (E.μ ω).toReal * (n * ε * q) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (inner ω) ENNReal.toReal_nonneg
    _ = n * ε * q := by rw [← sum_mul, E.μ.sum_toReal, one_mul]

end Budget

end Distinguisher

/-! ### O2H over the whole run -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} {D : Distinguisher W X Y Req A n m} [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω : Type*} [Fintype Ω] {Q : ℕ} {U : Type*} [Fintype U] {q : ℕ}

/-- **O2H over the whole run at hidden points correlated with the replies, with a query budget**
(module docstring). For two environments whose oracles differ at hidden points of each request
(`HiddenSide`), if for every request number `c`, every tape, every `c` earlier requests `rs₀`
and every request `req`, every guess computed from the response to `req` is a hidden point of
`req` with probability at most `ε c` over the coins of request `c`, then a distinguisher without
a final unitary and with a budget of `q` query slots distinguishes the two games, on the
branches whose logs lie in `L`, with advantage at most `2 q √(n ∑ c, ε c)`. -/
theorem advantage_acceptProbOn_le_of_hidden_budget [Nonempty X] [Nonempty Req]
    (bud : D.Budget q) {E E' : Env Ω Req A X Y Q} {ν : PMF U} {res : Fin Q → Ω → U → Ω}
    {hidden : Ω → List Req → Req → Set X} (hE : HiddenSide E E' ν res hidden) (ε : Fin Q → ℝ)
    (hfind : ∀ (c : Fin Q) ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε c)
    (L : Set (LogReg Req m)) :
    GordieHowe.advantage (D.acceptProbOn E noPost L) (D.acceptProbOn E' noPost L) ≤
      2 * q * √(n * ∑ c, ε c) := by
  classical
  have hε0 : ∀ c, 0 ≤ ε c := fun c => by
    obtain ⟨x₀⟩ := ‹Nonempty X›
    obtain ⟨r₀⟩ := ‹Nonempty Req›
    obtain ⟨ω₀, -⟩ := E.μ.support_nonempty
    exact ENNReal.toReal_nonneg.trans
      (hfind c ω₀ (List.replicate c r₀) r₀ (by simp) fun _ => x₀)
  let S : Ω → W × Req × Option A × LogReg Req m → Set X := fun ω w =>
    if D.kind w.1 = false then
      {x | ∃ rs₀ req, rs₀ ++ [req] <+: requests w.2.2.2 ∧ rs₀.length < Q ∧ x ∈ hidden ω rs₀ req}
    else ∅
  let s : O2HSetting Ω Ω (W × Req × Option A × LogReg Req m) X Y :=
    { μ := E.μ
      S := S
      G := fun ω => E'.oracleFn D.kind ω
      H := fun ω => E.oracleFn D.kind ω
      z := id
      agree := fun ω w x hx => by
        simp only [Env.oracleFn, Env.oracle, OracleState.toOracle_fun]
        split_ifs with hk
        · rfl
        · have hk' : D.kind w.1 = false := by simpa using hk
          refine (hE.oracle ω (requests w.2.2.2) x fun rs₀ req hp hl hmem => hx ?_).symm
          simp only [S, hk', ↓reduceIte]
          exact ⟨rs₀, req, hp, hl, hmem⟩ }
  have hans' : ∀ ω (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω lg k := fun ω lg k => by
    simp only [Env.answer, funext (hE.answer ω (requestsBefore lg k))]
  have hA : D.gameAlg E noPost L = D.gameAlg E' noPost L := by
    unfold gameAlg
    congr 1
    funext ω t
    exact gameStep_noPost_congr (hans' ω) t
  have hpL : s.pLeft (D.gameAlg E noPost L) = D.acceptProbOn E noPost L :=
    sum_congr rfl fun ω _ => by rw [← D.acceptProb_gameAlg_self E noPost _ ω]; rfl
  have hpR : s.pRight (D.gameAlg E noPost L) = D.acceptProbOn E' noPost L := by
    change ∑ ω, (E.μ ω).toReal * _ = ∑ ω, (E'.μ ω).toReal * _
    rw [hE.law]
    refine sum_congr rfl fun ω _ => ?_
    rw [← D.acceptProb_gameAlg_self E' noPost _ ω, ← hA]
    rfl
  have hcount := fun ω => bud.stepCount_gameAlg noPost E L ω
  have hSC : ∀ ω, ∀ k < m, ∀ w ∈ {s | bud.Holds k s}, ∀ x ∈ s.S ω w,
      w ∈ {s : W × Req × Option A × LogReg Req m | queriedAt s.2.2.2 k = true} := by
    intro ω k hk w hw x hx
    by_cases hkd : D.kind w.1 = false
    · have h := hw.logged hk
      rw [hkd] at h
      exact h
    · simp [s, S, hkd] at hx
  have hsplit : ∀ ω (v : QState (GameReg W n X Y Req A m)),
      prob (queriedOf (s.S ω)) v ≤ ∑ c : Fin Q, prob (queriedOf (D.hiddenAt hidden c ω)) v := by
    intro ω v
    refine prob_le_sum_prob_of_subset (fun r hr => ?_) v
    obtain ⟨j, hj⟩ := hr
    by_cases hk : D.kind r.1.1 = false
    · have hj' : (r.2 j).1 ∈ {x | ∃ rs₀ req, rs₀ ++ [req] <+: requests r.1.2.2.2 ∧
          rs₀.length < Q ∧ x ∈ hidden ω rs₀ req} := by
        have : s.S ω r.1 = _ := if_pos hk
        exact this ▸ hj
      obtain ⟨rs₀, req, hp, hl, hmem⟩ := hj'
      refine Set.mem_iUnion.2 ⟨⟨rs₀.length, hl⟩, j, ?_⟩
      have : D.hiddenAt hidden (rs₀.length) ω r.1 = _ := if_pos hk
      rw [this]
      exact ⟨rs₀, req, hp, rfl, hmem⟩
    · have : s.S ω r.1 = ∅ := if_neg hk
      rw [this] at hj
      exact absurd hj (Set.notMem_empty _)
  have hguess : ∑ ω, (s.μ ω).toReal * ∑ i : Fin m, prob (queriedOf (s.S ω))
      ((D.gameAlg E noPost L).pre (queryPermOf (s.H ω)) (s.z ω) i) ≤ n * (∑ c, ε c) * q := by
    calc ∑ ω, (s.μ ω).toReal * ∑ i : Fin m, prob (queriedOf (s.S ω))
          ((D.gameAlg E noPost L).pre (queryPermOf (s.H ω)) (s.z ω) i)
        ≤ ∑ ω, (E.μ ω).toReal * ∑ i : Fin m, ∑ c : Fin Q, prob (queriedOf (D.hiddenAt hidden c ω))
          ((D.gameAlg E noPost L).pre (queryPermOf (E.oracleFn D.kind ω)) ω i) :=
          sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
            (sum_le_sum fun i _ => hsplit ω _) ENNReal.toReal_nonneg
      _ = ∑ c : Fin Q, ∑ ω, (E.μ ω).toReal * ∑ i : Fin m,
          prob (queriedOf (D.hiddenAt hidden c ω))
            ((D.gameAlg E noPost L).pre (queryPermOf (E.oracleFn D.kind ω)) ω i) := by
          rw [sum_comm]
          refine sum_congr rfl fun ω _ => ?_
          rw [sum_comm, mul_sum]
      _ ≤ ∑ c : Fin Q, n * ε c * q := sum_le_sum fun c _ =>
          bud.sum_mul_sum_prob_queriedOf_hiddenAt_le hE c (hε0 c) (hfind c) L
      _ = n * (∑ c, ε c) * q := by rw [mul_sum, sum_mul]
  have hsum0 : 0 ≤ ∑ c, ε c := sum_nonneg fun c _ => hε0 c
  rw [← hpL, ← hpR]
  refine (s.o2h_of_count _ _ _ q hcount hSC).trans ?_
  calc 2 * √q * √(∑ ω, (s.μ ω).toReal * ∑ i : Fin m, prob (queriedOf (s.S ω))
        ((D.gameAlg E noPost L).pre (queryPermOf (s.H ω)) (s.z ω) i))
      ≤ 2 * √q * √(n * (∑ c, ε c) * q) := by
        gcongr
    _ = 2 * q * √(n * ∑ c, ε c) := by
        rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) hsum0) q,
          mul_comm (√(n * ∑ c, ε c)) (√q), ← mul_assoc, mul_assoc 2 (√q) (√q),
          Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-- **O2H over the whole run at hidden points correlated with the replies**, for the whole
acceptance probability (`advantage_acceptProbOn_le_of_hidden_budget` with every log). -/
theorem advantage_acceptProb_le_of_hidden_budget [Nonempty X] [Nonempty Req]
    (bud : D.Budget q) {E E' : Env Ω Req A X Y Q} {ν : PMF U} {res : Fin Q → Ω → U → Ω}
    {hidden : Ω → List Req → Req → Set X} (hE : HiddenSide E E' ν res hidden) (ε : Fin Q → ℝ)
    (hfind : ∀ (c : Fin Q) ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε c) :
    GordieHowe.advantage (D.acceptProb E noPost) (D.acceptProb E' noPost) ≤
      2 * q * √(n * ∑ c, ε c) := by
  rw [← acceptProbOn_univ, ← acceptProbOn_univ]
  exact advantage_acceptProbOn_le_of_hidden_budget bud hE ε hfind Set.univ

end Distinguisher

end GordieHowe.Quantum
