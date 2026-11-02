-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.StepHybrid

@[expose] public section

/-!
# O2H at hidden points correlated with the replies, with the challenger's reads as queries

`GordieHowe/Model/Quantum/O2H/HiddenSide.lean` compares two environments whose oracles differ,
after each request sequence, only at hidden points of the requests made, correlated with the
responses through the coins of each request, and whose responses are the same (`HiddenSide`).
Here the responses may differ too, through the challenger's classical reads
(`HiddenSideReads`): at most `qC` points `reads ω rs req` per request (`reads_card`); the two
environments give the same answer to a request whose reads avoid the hidden points of the
requests numbered below `Q` before it (`answer`); and on `E` the reads after request number `c`
read its coins only through its response (`reads_agree`). The two environments may have
different state types (`OracleState`).

**The find condition** is that of `HiddenSide`: for every request number `c`, every tape, every
`c` earlier requests `rs₀` and every request `req`, every guess computed from the response to
`req` is a hidden point of `req` with probability at most `ε c` over the coins of request `c`.

**The result.** `Distinguisher.advantage_acceptProbOn_le_of_hiddenReads_budget`: a distinguisher
without a final unitary and with a budget of `q` query slots distinguishes the games against `E`
and `E'`, on the branches whose logs lie in any set `L`, with advantage at most
`2 √(q + Q') √((n q + qC Q) ∑ c, ε c)`, with `Q' = 0` if `qC = 0` and `Q' = Q` otherwise;
`Distinguisher.advantage_acceptProb_le_of_hiddenReads_budget` for every log. Without reads
(`HiddenSide.toReads`, `qC = 0`) it is the bound `2 q √(n ∑ c, ε c)` of
`Distinguisher.advantage_acceptProbOn_le_of_hidden_budget`
(`Distinguisher.advantage_acceptProbOn_le_of_hidden_budget'`).

**The proof** compares the two runs tape by tape with step-dependent basis permutations
(Ambainis, Hamburg and Unruh, CRYPTO 2019, ePrint 2018/904, Lemma 8;
`Distinguisher.norm_run_sub_le_of_count`, `GordieHowe/Model/Quantum/O2H/StepHybrid.lean`). The
slots of the two games agree outside the branches that query a hidden point of a request
numbered below `Q` and the answered request branches whose reads hit such a point. A query
branch keeps the log of its slot blank, and an answered request branch fills it with fewer than
`Q` requests before it, so each branch is counted at most `q + Q` times (`q` without reads, when
no request branch differs): at most `q` query slots under the budget (`Budget.holdSet`), at most
`Q` answered requests (`card_filter_answeredLogs_le`). The squared distance is then averaged over
the tape (Jensen), and the find terms are bounded request number by request number, as in
`HiddenSide.lean`: the coins of request `c` are redrawn, the branches are split by the slot of
request `c` and the logs up to it, and on each piece a weight that reads the coins only through
the response finds a hidden point no better than a guess from the response
(`sum_mul_sum_prob_piece_le`). The query find terms are at most `n ε c q`
(`Budget.sum_mul_sum_prob_queriedOf_hiddenAt_stage_le`). The read find terms are bounded through
the same guess from the response (`sum_mul_sum_prob_readHitAt_le`): the reads at an answered
request depend on the coins of request `c` only through its response, so they give at most `qC`
guesses per answered request, and the answered requests number at most `Q` per branch
(`sum_prob_answered_piece_le`), which gives at most `qC Q ε c`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

section Hidden

variable {Ω Req A X Y : Type*} [Fintype Ω] {Q : ℕ} {U : Type*} [Fintype U]
  {St St' : Type _} [OracleState St X Y] [OracleState St' X Y]

/-- **Two environments whose oracles differ at hidden points of each request, whose answers
differ only through the challenger's reads at hidden points.** As `HiddenSide`, without its
equality of the answers: the challenger's classical reads at a request, `reads ω rs req`, are at
most `qC` points (`reads_card`); the two environments give the same answer to a request whose
reads avoid the hidden points of the earlier requests (`answer`); and on `E` the reads at a request
after request number `c` read the coins of request `c` only through its response
(`reads_agree`). The environments may have any state types; their oracles in force are compared
through `OracleState.toOracle`. -/
structure HiddenSideReads (E : Env Ω Req A X Y Q St) (E' : Env Ω Req A X Y Q St') (ν : PMF U)
    (res : Fin Q → Ω → U → Ω) (hidden : Ω → List Req → Req → Set X)
    (reads : Ω → List Req → Req → Finset X) (qC : ℕ) : Prop where
  /-- The same tape law. -/
  law : E'.μ = E.μ
  /-- The oracles in force agree outside the hidden points of the requests. -/
  oracle : ∀ ω rs x, (∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length < Q → x ∉ hidden ω rs₀ req) →
    (OracleState.toOracle (E.oracleIn ω rs) : X → Y) x = OracleState.toOracle (E'.oracleIn ω rs) x
  /-- Redrawing the coins of request number `c` keeps the tape law. -/
  resample : ∀ (c : Fin Q) (f : Ω → ℝ), ∑ ω, (E.μ ω).toReal * f ω =
    ∑ ω, (E.μ ω).toReal * ∑ a, (ν a).toReal * f (res c ω a)
  /-- On `E`, the coins of request number `c` reach the responses and the oracles in force along
  a request sequence only through the response to request number `c`. -/
  agree : ∀ (c : Fin Q) ω a a' rs, (∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length = (c : ℕ) →
      E.answerAfter (res c ω a) rs₀ req = E.answerAfter (res c ω a') rs₀ req) →
    E.AgreeAlong (res c ω a) (res c ω a') rs
  /-- At most `qC` reads per request. -/
  reads_card : ∀ ω rs req, (reads ω rs req).card ≤ qC
  /-- The answers agree when the reads avoid the hidden points of the earlier requests. -/
  answer : ∀ ω rs req, (∀ x ∈ reads ω rs req, ∀ rs₀ req₀, rs₀ ++ [req₀] <+: rs →
      rs₀.length < Q → x ∉ hidden ω rs₀ req₀) →
    E.answerAfter ω rs req = E'.answerAfter ω rs req
  /-- On `E`, the reads after request number `c` read its coins only through its response. -/
  reads_agree : ∀ (c : Fin Q) ω a a' rs req, (c : ℕ) < rs.length →
    (∀ rs₀ req₀, rs₀ ++ [req₀] <+: rs → rs₀.length = (c : ℕ) →
      E.answerAfter (res c ω a) rs₀ req₀ = E.answerAfter (res c ω a') rs₀ req₀) →
    reads (res c ω a) rs req = reads (res c ω a') rs req

variable {ν : PMF U} {res : Fin Q → Ω → U → Ω} {hidden : Ω → List Req → Req → Set X}

omit [OracleState St X Y] [OracleState St' X Y] in
/-- **`HiddenSide` is the case without reads.** -/
theorem HiddenSide.toReads {E E' : Env Ω Req A X Y Q} (h : HiddenSide E E' ν res hidden) :
    HiddenSideReads E E' ν res hidden (fun _ _ _ => ∅) 0 where
  law := h.law
  oracle ω rs x hx := h.oracle ω rs x hx
  resample := h.resample
  agree := h.agree
  reads_card _ _ _ := by simp
  answer ω rs req _ := h.answer ω rs req
  reads_agree _ _ _ _ _ _ _ _ := rfl

omit [OracleState St' X Y] in
/-- **A trivial instance**: an environment against itself, with no hidden points and no reads,
for a tape law that keeps redrawing the coins (`hres`). -/
theorem HiddenSideReads.refl {E : Env Ω Req A X Y Q St}
    (hres : ∀ (c : Fin Q) (f : Ω → ℝ), ∑ ω, (E.μ ω).toReal * f ω =
      ∑ ω, (E.μ ω).toReal * ∑ a, (ν a).toReal * f (res c ω a))
    (hag : ∀ (c : Fin Q) ω a a' rs, (∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length = (c : ℕ) →
      E.answerAfter (res c ω a) rs₀ req = E.answerAfter (res c ω a') rs₀ req) →
      E.AgreeAlong (res c ω a) (res c ω a') rs) :
    HiddenSideReads E E ν res (fun _ _ _ => ∅) (fun _ _ _ => ∅) 0 where
  law := rfl
  oracle _ _ _ _ := rfl
  resample := hres
  agree := hag
  reads_card _ _ _ := by simp
  answer _ _ _ _ := rfl
  reads_agree _ _ _ _ _ _ _ _ := rfl

end Hidden

/-! ### Sets of logs read up to a slot -/

section Logs

variable {Req : Type*} {m : ℕ}

/-- A set of logs read up to `s` is read up to every later slot. -/
theorem ReadsUpTo.mono {N : Set (LogReg Req m)} {s k : ℕ} (h : ReadsUpTo N s) (hsk : s ≤ k) :
    ReadsUpTo N k :=
  fun lg lg' h' => h lg lg' fun k' hk' => h' k' (hk'.trans hsk)

/-- The query slot `k` is read up to `k`. -/
theorem queriedLogs_readsUpTo (k : ℕ) :
    ReadsUpTo {lg : LogReg Req m | queriedAt lg k = true} k := by
  intro lg lg' h
  show queriedAt lg k = true ↔ queriedAt lg' k = true
  unfold queriedAt
  split_ifs with hk
  · rw [h ⟨k, hk⟩ le_rfl]
  · exact Iff.rfl

/-- **The logs whose slot `k` is an answered request**: slot `k` is filled, with fewer than `Q`
requests before it. -/
def answeredLogs (Q k : ℕ) : Set (LogReg Req m) :=
  {lg | ∃ h : k < m, lg ⟨k, h⟩ ≠ none ∧ (requestsBefore lg k).length < Q}

/-- The answered request slot `k` is read up to `k`. -/
theorem answeredLogs_readsUpTo (Q k : ℕ) :
    ReadsUpTo (answeredLogs (Req := Req) (m := m) Q k) k := by
  intro lg lg' h
  have hr : requestsBefore lg k = requestsBefore lg' k :=
    requestsBefore_congr fun k' hk' => h k' hk'.le
  show (∃ hk : k < m, lg ⟨k, hk⟩ ≠ none ∧ (requestsBefore lg k).length < Q) ↔
    (∃ hk : k < m, lg' ⟨k, hk⟩ ≠ none ∧ (requestsBefore lg' k).length < Q)
  rw [hr]
  constructor
  · rintro ⟨hk, h1, h2⟩
    exact ⟨hk, by rwa [← h ⟨k, hk⟩ le_rfl], h2⟩
  · rintro ⟨hk, h1, h2⟩
    exact ⟨hk, by rwa [h ⟨k, hk⟩ le_rfl], h2⟩

open Classical in
/-- **At most `Q` answered request slots**: distinct filled slots have distinct numbers of
requests before them. -/
theorem card_filter_answeredLogs_le (Q : ℕ) (lg : LogReg Req m) :
    ((range m).filter fun k => lg ∈ answeredLogs Q k).card ≤ Q := by
  calc ((range m).filter fun k => lg ∈ answeredLogs Q k).card ≤ (range Q).card := by
        refine card_le_card_of_injOn (fun k => (requestsBefore lg k).length) ?_ ?_
        · intro k hk
          obtain ⟨-, -, -, h⟩ := mem_filter.1 hk
          exact mem_range.2 h
        · intro k hk k' hk' he
          obtain ⟨-, h, h1, -⟩ := mem_filter.1 hk
          obtain ⟨-, h', h1', -⟩ := mem_filter.1 hk'
          exact congrArg Fin.val (eq_of_length_requestsBefore_eq (s := ⟨k, h⟩) (s' := ⟨k', h'⟩)
            h1 h1' he)
    _ = Q := card_range Q

end Logs

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω : Type*} {Q : ℕ}

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] in
/-- **The answered request branches whose reads hit a hidden point of request number `c`**: on a
request branch with fewer than `Q` earlier requests, the reads at its request after the
branch's requests contain a point of `hidden ω rs₀ req₀` for the prefix `rs₀ ++ [req₀]` of those
requests with `rs₀` of length `c`. -/
def readHitAt (hidden : Ω → List Req → Req → Set X) (reads : Ω → List Req → Req → Finset X)
    (c : Fin Q) (ω : Ω) : Set (GameReg W n X Y Req A m) :=
  {r | D.kind r.workspace = true ∧ (requests (splitLogs r).2).length < Q ∧
    ∃ rs₀ req₀, rs₀ ++ [req₀] <+: requests (splitLogs r).2 ∧ rs₀.length = (c : ℕ) ∧
      ∃ x ∈ reads ω (requests (splitLogs r).2) r.request, x ∈ hidden ω rs₀ req₀}

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] in
/-- **The piece of the read hits of request number `c` made at slot `s` after the logs `p`**:
the answered request branches whose logs up to slot `s` are those of `p`, where slot `s` of `p`
holds request number `c`, whose reads contain a hidden point of that request. -/
def readPiece (hidden : Ω → List Req → Req → Set X) (reads : Ω → List Req → Req → Finset X)
    (c : ℕ) (ω : Ω) (s : Fin m) (p : LogReg Req m) : Set (GameReg W n X Y Req A m) :=
  {r | ∃ req, p s = some req ∧ (requestsBefore p s).length = c ∧
    (∃ x ∈ reads ω (requests (splitLogs r).2) r.request, x ∈ hidden ω (requestsBefore p s) req) ∧
    (D.kind r.workspace = true ∧ (requests (splitLogs r).2).length < Q) ∧
    cutAfter s (splitLogs r).2 = p}

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- **The read hits of request number `c` split by the slot of the request and the logs up to
it.** -/
theorem prob_readHitAt_le (hidden : Ω → List Req → Req → Set X)
    (reads : Ω → List Req → Req → Finset X) (c : Fin Q) (ω : Ω)
    (v : QState (GameReg W n X Y Req A m)) :
    prob (D.readHitAt hidden reads c ω) v ≤
      ∑ sp : Fin m × LogReg Req m, prob (D.readPiece (Q := Q) hidden reads c ω sp.1 sp.2) v := by
  refine prob_le_sum_prob_of_subset (fun r hr => ?_) v
  obtain ⟨hk, hQ, rs₀, req, hpre, hlen, x, hx, hmem⟩ := hr
  have hc : (c : ℕ) < (requests (splitLogs r).2).length := by
    have := hpre.length_le
    rw [List.length_append, List.length_singleton] at this
    omega
  obtain ⟨s, hs, hsc⟩ := exists_slot_of_lt_length (splitLogs r).2 hc
  obtain ⟨req', hreq'⟩ := Option.ne_none_iff_exists'.1 hs
  obtain ⟨e1, e2⟩ := eq_of_append_singleton_prefix hpre
    (requestsBefore_append_prefix (splitLogs r).2 hreq') (by rw [hlen, hsc])
  have hrb : requestsBefore (cutAfter s (splitLogs r).2) s = requestsBefore (splitLogs r).2 s :=
    requestsBefore_cutAfter _ _ (by omega)
  refine Set.mem_iUnion.2 ⟨(s, cutAfter s (splitLogs r).2), req, ?_, ?_, ⟨x, hx, ?_⟩, ⟨hk, hQ⟩,
    rfl⟩
  · show cutAfter s (splitLogs r).2 s = some req
    rw [cutAfter_apply_of_le _ _ le_rfl, hreq', e2]
  · show (requestsBefore (cutAfter s (splitLogs r).2) s).length = c
    rw [hrb, hsc]
  · show x ∈ hidden ω (requestsBefore (cutAfter s (splitLogs r).2) s) req
    rw [hrb, ← e1]
    exact hmem

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] in
/-- The hidden points of the requests numbered below `Q` on a query branch with work register
content `w`; no points on a request branch. -/
def hiddenBefore (hidden : Ω → List Req → Req → Set X) (ω : Ω)
    (w : W × Req × Option A × LogReg Req m) : Set X :=
  if D.kind w.1 = false then
    {x | ∃ rs₀ req, rs₀ ++ [req] <+: requests w.2.2.2 ∧ rs₀.length < Q ∧ x ∈ hidden ω rs₀ req}
  else ∅

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- The query hits of the requests numbered below `Q` split by request number. -/
theorem prob_queriedOf_hiddenBefore_le (hidden : Ω → List Req → Req → Set X) (ω : Ω)
    (v : QState (GameReg W n X Y Req A m)) :
    prob (queriedOf (D.hiddenBefore (Q := Q) hidden ω)) v ≤
      ∑ c : Fin Q, prob (queriedOf (D.hiddenAt hidden c ω)) v := by
  refine prob_le_sum_prob_of_subset (fun r hr => ?_) v
  obtain ⟨j, hj⟩ := hr
  by_cases hk : D.kind r.1.1 = false
  · have hj' : (r.2 j).1 ∈ {x | ∃ rs₀ req, rs₀ ++ [req] <+: requests r.1.2.2.2 ∧
        rs₀.length < Q ∧ x ∈ hidden ω rs₀ req} := by
      have : D.hiddenBefore (Q := Q) hidden ω r.1 = _ := if_pos hk
      exact this ▸ hj
    obtain ⟨rs₀, req, hp, hl, hmem⟩ := hj'
    refine Set.mem_iUnion.2 ⟨⟨rs₀.length, hl⟩, j, ?_⟩
    have : D.hiddenAt hidden (rs₀.length) ω r.1 = _ := if_pos hk
    rw [this]
    exact ⟨rs₀, req, hp, rfl, hmem⟩
  · have : D.hiddenBefore (Q := Q) hidden ω r.1 = ∅ := if_neg hk
    rw [this] at hj
    exact absurd hj (Set.notMem_empty _)

/-! ### Counting slots along the game -/

variable {St St' : Type _} [OracleState St X Y] [OracleState St' X Y]

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] in
/-- The probability of a set after a basis permutation is that of its preimage. -/
theorem prob_permOp_eq {ι : Type*} [Fintype ι] (π : Equiv.Perm ι) (T : Set ι) (v : QState ι) :
    prob T (permOp π v) = prob (π ⁻¹' T) v := by
  rw [prob_eq_sum_indicator, prob_eq_sum_indicator, ← Equiv.sum_comp π]
  refine sum_congr rfl fun r _ => ?_
  by_cases h : π r ∈ T <;> simp [h]

/-- **A slot that sends a set into logs read up to the slot**: the probability of the set before
slot `k` is at most the final probability of those logs. -/
theorem prob_stage_le_prob_run (E : Env Ω Req A X Y Q St) (ω : Ω) {k : ℕ} (hk : k < m)
    {B : Set (GameReg W n X Y Req A m)} {N : Set (LogReg Req m)} (hN : ReadsUpTo N k)
    (hB : ∀ r ∈ logsIn (reachableLogs k), r ∈ B → D.eventPerm E ω k r ∈ logsIn N) :
    prob B (D.stage E ω k) ≤ prob (logsIn N) (D.run E ω) := by
  calc prob B (D.stage E ω k) ≤ prob (D.eventPerm E ω k ⁻¹' logsIn N) (D.stage E ω k) :=
        (D.stage_supported E ω k).prob_le_of_inter_subset fun r hr hR => hB r hR hr
    _ = prob (logsIn N) (D.stage E ω (k + 1)) := by
        rw [stage_succ, liftedStep, prob_logsIn_logControlled, prob_permOp_eq]
    _ = prob (logsIn N) (D.run E ω) := (D.prob_logsIn_stage_eq E ω hN (k := m) (by omega)).symm

open Classical in
/-- **Counting slots along the game**: if slot `k` sends `B k` into logs `C k` read up to `k`
and inside `N`, and the final state lies in a set `G` where every branch has logs in at most
`cnt` of the sets `C k`, the probabilities of `B k` before the slots sum to at most `cnt` times
the final probability of `N`. -/
theorem sum_prob_stage_le_of_count (E : Env Ω Req A X Y Q St) (ω : Ω)
    (B : ℕ → Set (GameReg W n X Y Req A m)) (C : ℕ → Set (LogReg Req m)) (N : Set (LogReg Req m))
    (hC : ∀ k, ReadsUpTo (C k) k) (hCN : ∀ k, C k ⊆ N)
    (hB : ∀ k < m, ∀ r ∈ logsIn (reachableLogs k), r ∈ B k → D.eventPerm E ω k r ∈ logsIn (C k))
    (G : Set (GameReg W n X Y Req A m)) (hG : Supported G (D.run E ω)) (cnt : ℕ)
    (hcount : ∀ r ∈ G, ((range m).filter fun k => (splitLogs r).2 ∈ C k).card ≤ cnt) :
    ∑ k ∈ range m, prob (B k) (D.stage E ω k) ≤ cnt * prob (logsIn N) (D.run E ω) := by
  calc ∑ k ∈ range m, prob (B k) (D.stage E ω k)
      ≤ ∑ k ∈ range m, prob (logsIn (C k)) (D.run E ω) :=
        sum_le_sum fun k hk => D.prob_stage_le_prob_run E ω (mem_range.1 hk) (hC k)
          (hB k (mem_range.1 hk))
    _ = ∑ r, ∑ k ∈ range m, (if (splitLogs r).2 ∈ C k then ‖D.run E ω r‖ ^ 2 else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [prob_eq_sum_indicator]
        refine sum_congr rfl fun r _ => ?_
        by_cases h : (splitLogs r).2 ∈ C k <;> simp [mem_logsIn, h]
    _ ≤ ∑ r, cnt * (logsIn N).indicator (fun r => ‖D.run E ω r‖ ^ 2) r := by
        refine sum_le_sum fun r _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        by_cases hr : r ∈ G
        · by_cases h0 : ((range m).filter fun k => (splitLogs r).2 ∈ C k) = ∅
          · rw [h0, card_empty, Nat.cast_zero, zero_mul]
            exact mul_nonneg (Nat.cast_nonneg _) (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
          · obtain ⟨k, hk⟩ := nonempty_iff_ne_empty.2 h0
            have hN : r ∈ logsIn N := hCN k (mem_filter.1 hk).2
            rw [Set.indicator_of_mem hN]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount r hr) (sq_nonneg _)
        · rw [hG r hr, norm_zero, zero_pow two_ne_zero, mul_zero]
          exact mul_nonneg (Nat.cast_nonneg _) (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
    _ = cnt * prob (logsIn N) (D.run E ω) := by rw [← mul_sum, prob_eq_sum_indicator]

/-! ### The budget along the game, for any environment state -/

namespace Budget

variable {D} {q : ℕ} (bud : D.Budget q)

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] [OracleState St X Y] [OracleState St' X Y] in
/-- **The budget before slot `k`**: `HoldsBefore k` before a slot, at most `q` query slots from
slot `m` on. -/
def holdSet (k : ℕ) : Set (GameReg W n X Y Req A m) :=
  {r | (k < m → bud.HoldsBefore k r.1) ∧ (m ≤ k → queriesBefore r.1.2.2.2 m ≤ q)}

/-- A slot of any environment, then the next step, keep the budget. -/
theorem holdSet_step (E : Env Ω Req A X Y Q St) (ω : Ω) {k : ℕ} (hk : k < m)
    {v : QState (GameReg W n X Y Req A m)} (hv : Supported (bud.holdSet k) v) :
    Supported (bud.holdSet (k + 1)) (D.liftedStep (k + 1) (permOp (D.eventPerm E ω k) v)) := by
  have h1 : Supported {r : GameReg W n X Y Req A m | bud.Holds k r.1}
      (permOp (D.eventPerm E ω k) v) := by
    refine hv.permOp fun r hr => ?_
    rw [D.eventPerm_of_lt E ω hk]
    exact bud.holds_requestPerm E ω hk (hr.1 hk)
  by_cases hk1 : k + 1 < m
  · exact (bud.holdsBefore_liftedStep k hk1 h1).mono fun r hr =>
      ⟨fun _ => hr, fun h => absurd h (by omega)⟩
  · have h2 : Supported (logsIn {lg : LogReg Req m | queriesBefore lg m ≤ q})
        (permOp (D.eventPerm E ω k) v) :=
      h1.mono fun r hr => by
        have := hr.count
        show queriesBefore r.1.2.2.2 m ≤ q
        rwa [show k + 1 = m by omega] at this
    exact (h2.logControlled _).mono fun r hr => ⟨fun h => absurd h (by omega), fun _ => hr⟩

/-- **The game of any environment keeps the budget.** -/
theorem stage_supported_holdSet (E : Env Ω Req A X Y Q St) (ω : Ω) :
    ∀ k ≤ m, Supported (bud.holdSet k) (D.stage E ω k)
  | 0, _ => by
    by_cases hm : 0 < m
    · exact (bud.holdsBefore_liftedStep_zero hm).mono fun r hr =>
        ⟨fun _ => hr, fun h => absurd h (by omega)⟩
    · intro r hr
      refine absurd ⟨fun h => absurd h hm, fun _ => ?_⟩ hr
      unfold queriesBefore
      exact (card_filter_le _ _).trans ((card_range m).le.trans (by omega))
  | k + 1, hk => by
    rw [stage_succ]
    exact bud.holdSet_step E ω (by omega) (stage_supported_holdSet E ω k (by omega))

end Budget

/-- **The slots that a hit sends into the counted logs**: a query branch that queries a hidden
point keeps the log of its slot blank, and an answered request branch whose reads hit a hidden
point (so `qC ≠ 0`) fills the log of its slot with fewer than `Q` requests before it. -/
theorem eventPerm_mem_countLogs (E₀ : Env Ω Req A X Y Q St) {hidden : Ω → List Req → Req → Set X}
    {reads : Ω → List Req → Req → Finset X} {qC : ℕ}
    (hcard : ∀ ω rs req, (reads ω rs req).card ≤ qC) (ω : Ω) {k : ℕ} (hk : k < m)
    {r : GameReg W n X Y Req A m} (hR : r ∈ logsIn (reachableLogs k))
    (hr : r ∈ queriedOf (D.hiddenBefore (Q := Q) hidden ω) ∪ ⋃ c : Fin Q,
      D.readHitAt hidden reads c ω) :
    D.eventPerm E₀ ω k r ∈
      logsIn ({lg | queriedAt lg k = true} ∪ {lg | qC ≠ 0 ∧ lg ∈ answeredLogs Q k}) := by
  rcases hr with hr | hr
  · obtain ⟨j, hj⟩ := hr
    have hkind : D.kind r.workspace = false := by
      by_contra h
      have : D.hiddenBefore (Q := Q) hidden ω r.1 = ∅ := if_neg h
      rw [this] at hj
      exact hj
    rw [D.eventPerm_of_query E₀ ω hk hkind, mem_logsIn]
    refine Or.inl ?_
    show queriedAt r.1.2.2.2 k = true
    simp only [queriedAt, hk, ↓reduceDIte, Option.isNone_iff_eq_none]
    exact hR ⟨k, hk⟩ le_rfl
  · obtain ⟨c, hkind, hl, -, -, -, -, x, hx, -⟩ := Set.mem_iUnion.1 hr
    rw [D.eventPerm_of_request E₀ ω hk hR hkind, mem_logsIn]
    refine Or.inr ⟨fun h0 => ?_, hk, by simp [splitLogs], ?_⟩
    · have := hcard ω (requests (splitLogs r).2) r.request
      rw [h0, Nat.le_zero, Finset.card_eq_zero] at this
      rw [this] at hx
      exact absurd hx (Finset.notMem_empty _)
    · show (requestsBefore (Function.update (splitLogs r).2 ⟨k, hk⟩ (some r.request)) k).length < Q
      rw [requestsBefore_congr (lg' := (splitLogs r).2) fun k' hk' =>
        Function.update_of_ne (fun e => by subst e; simp at hk') _ _]
      rw [← requests_eq_requestsBefore hR]
      exact hl

/-! ### The find probability of one piece -/

variable {D} [Fintype Ω] {U : Type*} [Fintype U] {q : ℕ}

omit [Fintype Ω] in
/-- **A weight read through a reply finds a hidden set no better than a guess**, on the game: for
tapes `ω' a` that agree along the requests of the logs `F` whenever the replies `ρ a` agree, the
probabilities of `Bh a ∩ K ∩ logsIn F` before the slots, averaged over `a ← ν`, are at most `M δ`,
for `M` bounding the sum over the slots of the probabilities of `K ∩ logsIn F`, and `δ` bounding
the probability that a guess from the reply lies in `Bh a`. -/
theorem sum_mul_sum_prob_piece_le (E : Env Ω Req A X Y Q St) (ν : PMF U) (ω' : U → Ω)
    (ρ : U → Option A) {F : Set (LogReg Req m)}
    (hag : ∀ a a', ρ a = ρ a' → ∀ lg ∈ F, ∀ i ≤ m,
      E.AgreeAlong (ω' a) (ω' a') (requestsBefore lg i))
    (K : Set (GameReg W n X Y Req A m)) (Bh : U → Set (GameReg W n X Y Req A m)) {M δ : ℝ}
    (hM : ∀ a, ∑ i : Fin m, prob (K ∩ logsIn F) (D.stage E (ω' a) i) ≤ M)
    (hε : ∀ g : Option A → GameReg W n X Y Req A m,
      (ν.toOuterMeasure {a | g (ρ a) ∈ Bh a}).toReal ≤ δ) :
    ∑ a, (ν a).toReal * ∑ i : Fin m, prob (Bh a ∩ (K ∩ logsIn F)) (D.stage E (ω' a) i) ≤
      M * δ := by
  classical
  set w : U → GameReg W n X Y Req A m → ℝ := fun a r =>
    ∑ i : Fin m, (K ∩ logsIn F).indicator (fun r => ‖D.stage E (ω' a) i r‖ ^ 2) r
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
  have hM' : ∀ a, ∑ r, w a r ≤ M := by
    intro a
    have hsum : ∑ r, w a r = ∑ i : Fin m, prob (K ∩ logsIn F) (D.stage E (ω' a) i) := by
      simp only [w, prob_eq_sum_indicator]
      rw [sum_comm]
    rw [hsum]
    exact hM a
  have hL : ∀ a, ∑ i : Fin m, prob (Bh a ∩ (K ∩ logsIn F)) (D.stage E (ω' a) i) =
      ∑ r, (Bh a).indicator (w a) r := by
    intro a
    simp only [w, prob_eq_sum_indicator]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    by_cases hB : r ∈ Bh a
    · rw [Set.indicator_of_mem hB]
      refine sum_congr rfl fun i _ => ?_
      simp only [Set.indicator_apply, Set.mem_inter_iff, hB, true_and]
    · rw [Set.indicator_of_notMem hB]
      exact sum_eq_zero fun i _ => by simp [hB]
  have : Nonempty (GameReg W n X Y Req A m) := by
    obtain ⟨d⟩ := D.nonempty_dReg
    exact ⟨splitLogs.symm (d, fun _ => none)⟩
  simp only [hL]
  exact sum_mul_sum_indicator_le_of_guess ν ρ Bh w hw hρw hM' hε

/-- **A find term split into pieces by the slot of request number `c` and the logs up to it**:
if redrawing the coins of request `c` keeps the tape law and each piece, averaged over those
coins, is at most `M` times the final probability of its logs, the find term is at most `M`. -/
theorem sum_mul_sum_prob_le_of_pieces (E : Env Ω Req A X Y Q St) {ν : PMF U}
    {res : Fin Q → Ω → U → Ω} (c : Fin Q)
    (hres : ∀ f : Ω → ℝ, ∑ ω, (E.μ ω).toReal * f ω =
      ∑ ω, (E.μ ω).toReal * ∑ a, (ν a).toReal * f (res c ω a))
    (Hit : Ω → Set (GameReg W n X Y Req A m))
    (Piece : Ω → Fin m × LogReg Req m → Set (GameReg W n X Y Req A m))
    (hsplit : ∀ ω v, prob (Hit ω) v ≤ ∑ sp, prob (Piece ω sp) v) {M : ℝ} (hM0 : 0 ≤ M) (a₀ : U)
    (hterm : ∀ ω (sp : Fin m × LogReg Req m), ∑ a, (ν a).toReal * ∑ i : Fin m,
        prob (Piece (res c ω a) sp) (D.stage E (res c ω a) i) ≤
        M * prob {r : GameReg W n X Y Req A m | (sp.2 sp.1 ≠ none ∧
          (requestsBefore sp.2 sp.1).length = c) ∧ cutAfter sp.1 (splitLogs r).2 = sp.2}
          (D.run E (res c ω a₀))) :
    ∑ ω, (E.μ ω).toReal * ∑ i : Fin m, prob (Hit ω) (D.stage E ω i) ≤ M := by
  rw [hres]
  have inner : ∀ ω, ∑ a, (ν a).toReal * ∑ i : Fin m,
      prob (Hit (res c ω a)) (D.stage E (res c ω a) i) ≤ M := by
    intro ω
    have hswap : ∀ a, (ν a).toReal * ∑ i : Fin m, ∑ sp : Fin m × LogReg Req m,
        prob (Piece (res c ω a) sp) (D.stage E (res c ω a) i) =
        ∑ sp : Fin m × LogReg Req m, (ν a).toReal * ∑ i : Fin m,
          prob (Piece (res c ω a) sp) (D.stage E (res c ω a) i) :=
      fun a => by rw [sum_comm, mul_sum]
    calc ∑ a, (ν a).toReal * ∑ i : Fin m, prob (Hit (res c ω a)) (D.stage E (res c ω a) i)
        ≤ ∑ a, (ν a).toReal * ∑ i : Fin m, ∑ sp : Fin m × LogReg Req m,
          prob (Piece (res c ω a) sp) (D.stage E (res c ω a) i) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hsplit _ _)
            ENNReal.toReal_nonneg
      _ = ∑ sp : Fin m × LogReg Req m, ∑ a, (ν a).toReal * ∑ i : Fin m,
          prob (Piece (res c ω a) sp) (D.stage E (res c ω a) i) := by
          simp only [hswap]
          rw [sum_comm]
      _ ≤ ∑ sp : Fin m × LogReg Req m, M * prob {r : GameReg W n X Y Req A m |
          (sp.2 sp.1 ≠ none ∧ (requestsBefore sp.2 sp.1).length = c) ∧
            cutAfter sp.1 (splitLogs r).2 = sp.2} (D.run E (res c ω a₀)) :=
          sum_le_sum fun sp _ => hterm ω sp
      _ = M * ∑ sp : Fin m × LogReg Req m, prob {r : GameReg W n X Y Req A m |
          (sp.2 sp.1 ≠ none ∧ (requestsBefore sp.2 sp.1).length = c) ∧
            cutAfter sp.1 (splitLogs r).2 = sp.2} (D.run E (res c ω a₀)) := by rw [mul_sum]
      _ ≤ M * 1 := by
          gcongr
          have h := sum_prob_hiddenPiece_logs_le (W := W) (n := n) (X := X) (Y := Y) (A := A)
            (c : ℕ) (D.run E (res c ω a₀))
          rwa [norm_run_env, one_pow] at h
      _ = M := mul_one M
  calc ∑ ω, (E.μ ω).toReal * ∑ a, (ν a).toReal * ∑ i : Fin m,
        prob (Hit (res c ω a)) (D.stage E (res c ω a) i)
      ≤ ∑ ω, (E.μ ω).toReal * M :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (inner ω) ENNReal.toReal_nonneg
    _ = M := by rw [← sum_mul, E.μ.sum_toReal, one_mul]

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] in
/-- The logs of a piece: the logs whose cut after slot `s` is `p`. -/
theorem pieceLogs_eq {c : ℕ} {s : Fin m} {p : LogReg Req m}
    (hcond : p s ≠ none ∧ (requestsBefore p s).length = c) :
    {r : GameReg W n X Y Req A m | (p s ≠ none ∧ (requestsBefore p s).length = c) ∧
      cutAfter s (splitLogs r).2 = p} = logsIn (cutAfter s ⁻¹' {p}) := by
  ext r
  simp [hcond, mem_logsIn]

omit [Fintype Req] [DecidableEq Req] in
/-- The logs extending `p` up to slot `s` are read up to `s`, and fill slot `s` after the
requests of `p`. -/
theorem cutAfter_preimage_spec {s : Fin m} {p : LogReg Req m} {req : Req}
    (hps : p s = some req) :
    ReadsUpTo (cutAfter s ⁻¹' {p}) s ∧ ∀ lg ∈ cutAfter s ⁻¹' {p},
      lg s = some req ∧ requestsBefore lg s = requestsBefore p s := by
  refine ⟨fun lg lg' h => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, cutAfter_congr h], fun lg hlg => ?_⟩
  have hlg' : cutAfter s lg = p := hlg
  refine ⟨?_, ?_⟩
  · rw [← hps, ← hlg', cutAfter_apply_of_le _ _ le_rfl]
  · rw [← hlg', requestsBefore_cutAfter _ _ (by omega)]

variable {E : Env Ω Req A X Y Q St} {E' : Env Ω Req A X Y Q St'} {ν : PMF U}
  {res : Fin Q → Ω → U → Ω} {hidden : Ω → List Req → Req → Set X}
  {reads : Ω → List Req → Req → Finset X} {qC : ℕ}

omit [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req] [AddGroup Y] in
/-- On the logs extending `p` up to its slot `s` of request number `c`, tapes with redrawn coins
of request `c` agree along the requests of the logs when the responses to request `c` agree, and
always along the requests before `s`. -/
theorem _root_.GordieHowe.Quantum.HiddenSideReads.agree_on_piece (hE : HiddenSideReads E E' ν res hidden reads qC)
    (c : Fin Q) (ω : Ω) {s : Fin m} {p : LogReg Req m} {req : Req} (hps : p s = some req)
    (hpc : (requestsBefore p s).length = c) :
    (∀ a a', E.answerAfter (res c ω a) (requestsBefore p s) req =
        E.answerAfter (res c ω a') (requestsBefore p s) req → ∀ lg ∈ cutAfter s ⁻¹' {p},
        ∀ i ≤ m, E.AgreeAlong (res c ω a) (res c ω a') (requestsBefore lg i)) ∧
    ∀ a a', ∀ lg ∈ cutAfter s ⁻¹' {p},
      E.AgreeAlong (res c ω a) (res c ω a') (requestsBefore lg s) := by
  have hFlg := (cutAfter_preimage_spec hps).2
  refine ⟨fun a a' hρ lg hlg i hi => ?_, fun a a' lg hlg => ?_⟩
  · refine hE.agree c ω a a' _ fun rs₀ req' hpre hlen => ?_
    obtain ⟨h1, h2⟩ := hFlg lg hlg
    have hp1 : rs₀ ++ [req'] <+: requests lg := hpre.trans (requestsBefore_prefix lg hi)
    obtain ⟨e1, e2⟩ := eq_of_append_singleton_prefix hp1 (requestsBefore_append_prefix lg h1)
      (by rw [hlen, h2, hpc])
    rw [e1, e2, h2]
    exact hρ
  · refine hE.agree c ω a a' _ fun rs₀ req' hpre hlen => ?_
    have := hpre.length_le
    rw [(hFlg lg hlg).2, hpc] at this
    simp at this
    omega

namespace Budget

omit [Fintype Ω] [OracleState St' X Y] in
/-- On logs extending `p` up to its filled slot `s`, the query branches before the slots number
at most `q` on average under a budget. -/
theorem sum_prob_query_piece_le (bud : D.Budget q) (E : Env Ω Req A X Y Q St) (ω : Ω)
    {s : Fin m} {p : LogReg Req m} {req : Req} (hps : p s = some req) :
    ∑ i : Fin m, prob ({r : GameReg W n X Y Req A m | D.kind r.workspace = false} ∩
      logsIn (cutAfter s ⁻¹' {p})) (D.stage E ω i) ≤
      q * prob (logsIn (cutAfter s ⁻¹' {p})) (D.run E ω) := by
  classical
  obtain ⟨hF, hFlg⟩ := cutAfter_preimage_spec hps
  rw [Fin.sum_univ_eq_sum_range (fun i => prob ({r : GameReg W n X Y Req A m |
    D.kind r.workspace = false} ∩ logsIn (cutAfter s ⁻¹' {p})) (D.stage E ω i)) m]
  refine D.sum_prob_stage_le_of_count E ω
    (fun _ => {r : GameReg W n X Y Req A m | D.kind r.workspace = false} ∩
      logsIn (cutAfter s ⁻¹' {p}))
    (fun k => {lg | (s : ℕ) < k ∧ queriedAt lg k = true ∧ lg ∈ cutAfter s ⁻¹' {p}})
    (cutAfter s ⁻¹' {p})
    (fun k lg lg' h => ?_) (fun k lg h => h.2.2) (fun k hk r hR hr => ?_) (bud.holdSet m)
    (bud.stage_supported_holdSet E ω m le_rfl) q (fun r hr => ?_)
  · by_cases hsk : (s : ℕ) < k
    · exact and_congr Iff.rfl (and_congr (queriedLogs_readsUpTo k lg lg' h)
        ((hF.mono hsk.le) lg lg' h))
    · exact ⟨fun h' => absurd h'.1 hsk, fun h' => absurd h'.1 hsk⟩
  · have hlog : (splitLogs (D.eventPerm E ω k r)).2 = (splitLogs r).2 := by
      rw [D.eventPerm_of_query E ω hk hr.1]
      rfl
    rw [mem_logsIn, hlog]
    have hsk : (s : ℕ) < k := by
      by_contra h
      have h1 : (splitLogs r).2 s = none := hR s (by omega)
      rw [(hFlg _ hr.2).1] at h1
      exact absurd h1 (by simp)
    refine ⟨hsk, ?_, hr.2⟩
    simp only [queriedAt, hk, ↓reduceDIte, Option.isNone_iff_eq_none]
    exact hR ⟨k, hk⟩ le_rfl
  · have hq := hr.2 le_rfl
    unfold queriesBefore at hq
    refine (card_le_card fun k hk => ?_).trans hq
    simp only [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.2.1⟩

end Budget

omit [Fintype Ω] [OracleState St' X Y] in
/-- On logs extending `p` up to its filled slot `s`, the answered request branches before the
slots number at most `Q` on average. -/
theorem sum_prob_answered_piece_le (E : Env Ω Req A X Y Q St) (ω : Ω)
    {s : Fin m} {p : LogReg Req m} {req : Req} (hps : p s = some req) :
    ∑ i : Fin m, prob ({r : GameReg W n X Y Req A m | D.kind r.workspace = true ∧
      (requests (splitLogs r).2).length < Q} ∩ logsIn (cutAfter s ⁻¹' {p})) (D.stage E ω i) ≤
      Q * prob (logsIn (cutAfter s ⁻¹' {p})) (D.run E ω) := by
  classical
  obtain ⟨hF, hFlg⟩ := cutAfter_preimage_spec hps
  rw [Fin.sum_univ_eq_sum_range (fun i => prob ({r : GameReg W n X Y Req A m |
    D.kind r.workspace = true ∧ (requests (splitLogs r).2).length < Q} ∩
      logsIn (cutAfter s ⁻¹' {p})) (D.stage E ω i)) m]
  refine D.sum_prob_stage_le_of_count E ω
    (fun _ => {r : GameReg W n X Y Req A m | D.kind r.workspace = true ∧
      (requests (splitLogs r).2).length < Q} ∩ logsIn (cutAfter s ⁻¹' {p}))
    (fun k => {lg | (s : ℕ) < k ∧ lg ∈ answeredLogs Q k ∧ lg ∈ cutAfter s ⁻¹' {p}})
    (cutAfter s ⁻¹' {p})
    (fun k lg lg' h => ?_) (fun k lg h => h.2.2) (fun k hk r hR hr => ?_) Set.univ
    (fun r hr => absurd trivial hr) Q (fun r _ => ?_)
  · by_cases hsk : (s : ℕ) < k
    · exact and_congr Iff.rfl (and_congr (answeredLogs_readsUpTo Q k lg lg' h)
        ((hF.mono hsk.le) lg lg' h))
    · exact ⟨fun h' => absurd h'.1 hsk, fun h' => absurd h'.1 hsk⟩
  · have hlog : (splitLogs (D.eventPerm E ω k r)).2 =
        Function.update (splitLogs r).2 ⟨k, hk⟩ (some r.request) := by
      rw [D.eventPerm_of_request E ω hk hR hr.1.1]
      rfl
    rw [mem_logsIn, hlog]
    have hsk : (s : ℕ) < k := by
      by_contra h
      have h1 : (splitLogs r).2 s = none := hR s (by omega)
      rw [(hFlg _ hr.2).1] at h1
      exact absurd h1 (by simp)
    have hrb : requestsBefore (Function.update (splitLogs r).2 ⟨k, hk⟩ (some r.request)) k =
        requestsBefore (splitLogs r).2 k :=
      requestsBefore_congr fun k' hk' =>
        Function.update_of_ne (fun e => by subst e; simp at hk') _ _
    refine ⟨hsk, ⟨hk, by simp, ?_⟩, ?_⟩
    · rw [hrb, ← requests_eq_requestsBefore hR]
      exact hr.1.2
    · exact (hF (Function.update (splitLogs r).2 ⟨k, hk⟩ (some r.request)) (splitLogs r).2
        fun k' hk' => Function.update_of_ne
        (fun e => by subst e; simp at hk'; omega) _ _).2 hr.2
  · refine (card_le_card fun k hk => ?_).trans (card_filter_answeredLogs_le Q (splitLogs r).2)
    simp only [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.2.1⟩

/-! ### The find probabilities of request number `c` -/

namespace Budget

/-- **The query find probability of request number `c`**, for environments of any state:
averaged over the tape and summed over the slots, the probability that a query branch queries a
hidden point of request number `c` is at most `n ε q`. -/
theorem sum_mul_sum_prob_queriedOf_hiddenAt_stage_le (bud : D.Budget q)
    (hE : HiddenSideReads E E' ν res hidden reads qC) (c : Fin Q) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hfind : ∀ ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε) :
    ∑ ω, (E.μ ω).toReal * ∑ i : Fin m,
      prob (queriedOf (D.hiddenAt hidden c ω)) (D.stage E ω i) ≤ n * ε * q := by
  classical
  obtain ⟨a₀, -⟩ := ν.support_nonempty
  refine (D.sum_mul_sum_prob_le_of_pieces E c (hE.resample c) _
    (fun ω sp => D.hiddenPiece hidden c ω sp.1 sp.2)
    (fun ω v => D.prob_queriedOf_hiddenAt_le hidden c ω v)
    (M := q * (n * ε)) (by positivity) a₀ fun ω sp => ?_).trans_eq (by ring)
  obtain ⟨s, p⟩ := sp
  dsimp only
  by_cases hcond : p s ≠ none ∧ (requestsBefore p s).length = c
  · obtain ⟨req, hps⟩ := Option.ne_none_iff_exists'.1 hcond.1
    rw [pieceLogs_eq hcond]
    set F : Set (LogReg Req m) := cutAfter s ⁻¹' {p} with hFdef
    obtain ⟨hF, hFlg⟩ := cutAfter_preimage_spec hps
    obtain ⟨hag, hag0⟩ := hE.agree_on_piece c ω hps hcond.2
    set K : Set (GameReg W n X Y Req A m) := {r | D.kind r.workspace = false} with hK
    set H : U → Set X := fun a => hidden (res c ω a) (requestsBefore p s) req with hH
    set ρ : U → Option A := fun a => E.answerAfter (res c ω a) (requestsBefore p s) req with hρ
    have hpiece : ∀ a, D.hiddenPiece hidden c (res c ω a) s p =
        queried (H a) ∩ (K ∩ logsIn F) := by
      intro a
      ext r
      simp only [hiddenPiece, hps, Option.some.injEq, hcond.2, Set.mem_ofPred_eq,
        Set.mem_inter_iff, mem_logsIn, F, Set.mem_preimage, Set.mem_singleton_iff, K, H]
      constructor
      · rintro ⟨req', rfl, -, h1, h2, h3⟩
        exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨req, rfl, trivial, h1, h2, h3⟩
    have hrun : ∀ a, prob (logsIn F) (D.run E (res c ω a)) =
        prob (logsIn F) (D.run E (res c ω a₀)) :=
      fun a => D.prob_logsIn_stage_eq_of_agree E s.2 hF (hag0 a a₀) (k := m) (by omega)
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
            sum_le_sum fun j _ => hfind ω _ req hcond.2 fun ρ₀ => ((g ρ₀).2 j).1
        _ = n * ε := by simp
    simp only [hpiece]
    refine (D.sum_mul_sum_prob_piece_le E ν (res c ω) ρ hag K (fun a => queried (H a))
      (M := q * prob (logsIn F) (D.run E (res c ω a₀))) (fun a => ?_) hε).trans_eq (by ring)
    rw [← hrun a]
    exact bud.sum_prob_query_piece_le E (res c ω a) hps
  · have hP : ∀ a, D.hiddenPiece hidden c (res c ω a) s p = ∅ := fun a => by
      ext r
      simp only [hiddenPiece, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨req, h1, h2, -⟩
      exact hcond ⟨by rw [h1]; simp, h2⟩
    have hF0 : {r : GameReg W n X Y Req A m | (p s ≠ none ∧
        (requestsBefore p s).length = c) ∧ cutAfter s (splitLogs r).2 = p} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hcond h.1
    simp only [hP, hF0, prob_empty', sum_const_zero, mul_zero, le_refl]

end Budget

/-- **The read find probability of request number `c`**: averaged over the tape and summed over
the slots, the probability that an answered request branch reads a hidden point of request
number `c` is at most `qC Q ε`, for `ε` bounding the probability that a guess computed from the
response to request `c` is a hidden point of it. -/
theorem sum_mul_sum_prob_readHitAt_le
    (hE : HiddenSideReads E E' ν res hidden reads qC) (c : Fin Q) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hfind : ∀ ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε) :
    ∑ ω, (E.μ ω).toReal * ∑ i : Fin m,
      prob (D.readHitAt hidden reads c ω) (D.stage E ω i) ≤ qC * Q * ε := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · have h0 : ∀ ω, D.readHitAt hidden reads c ω = ∅ := fun ω =>
      Set.eq_empty_of_forall_notMem fun r hr => by
        obtain ⟨-, -, -, -, -, -, x, -⟩ := hr
        exact isEmptyElim x
    simp only [h0, prob_empty', sum_const_zero, mul_zero]
    positivity
  obtain ⟨a₀, -⟩ := ν.support_nonempty
  refine D.sum_mul_sum_prob_le_of_pieces E c (hE.resample c) _
    (fun ω sp => D.readPiece (Q := Q) hidden reads c ω sp.1 sp.2)
    (fun ω v => D.prob_readHitAt_le hidden reads c ω v)
    (M := qC * Q * ε) (by positivity) a₀ fun ω sp => ?_
  obtain ⟨s, p⟩ := sp
  dsimp only
  by_cases hcond : p s ≠ none ∧ (requestsBefore p s).length = c
  · obtain ⟨req, hps⟩ := Option.ne_none_iff_exists'.1 hcond.1
    rw [pieceLogs_eq hcond]
    set F : Set (LogReg Req m) := cutAfter s ⁻¹' {p} with hFdef
    obtain ⟨hF, hFlg⟩ := cutAfter_preimage_spec hps
    obtain ⟨hag, hag0⟩ := hE.agree_on_piece c ω hps hcond.2
    set K : Set (GameReg W n X Y Req A m) :=
      {r | D.kind r.workspace = true ∧ (requests (splitLogs r).2).length < Q} with hK
    set ρ : U → Option A := fun a => E.answerAfter (res c ω a) (requestsBefore p s) req with hρ
    set Bh : U → Set (GameReg W n X Y Req A m) := fun a => {r | (splitLogs r).2 ∈ F ∧
      ∃ x ∈ reads (res c ω a) (requests (splitLogs r).2) r.request,
        x ∈ hidden (res c ω a) (requestsBefore p s) req} with hBh
    have hpiece : ∀ a, D.readPiece (Q := Q) hidden reads c (res c ω a) s p =
        Bh a ∩ (K ∩ logsIn F) := by
      intro a
      ext r
      constructor
      · rintro ⟨req', h1, -, hx, hK, h3⟩
        have e : req = req' := Option.some_injective _ (hps.symm.trans h1)
        subst e
        exact ⟨⟨h3, hx⟩, hK, h3⟩
      · rintro ⟨⟨h3, hx⟩, hK, -⟩
        exact ⟨req, hps, hcond.2, hx, hK, h3⟩
    have hrun : ∀ a, prob (logsIn F) (D.run E (res c ω a)) =
        prob (logsIn F) (D.run E (res c ω a₀)) :=
      fun a => D.prob_logsIn_stage_eq_of_agree E s.2 hF (hag0 a a₀) (k := m) (by omega)
    have hε : ∀ g : Option A → GameReg W n X Y Req A m,
        (ν.toOuterMeasure {a | g (ρ a) ∈ Bh a}).toReal ≤ qC * ε := by
      intro g
      set T : Option A → Finset X := fun ρ₀ => if h : ∃ a, ρ a = ρ₀ then
        reads (res c ω h.choose) (requests (splitLogs (g ρ₀)).2) (g ρ₀).request else ∅ with hT
      set guess : Fin qC → Option A → X := fun i ρ₀ => ((T ρ₀).toList).getD i x₀ with hguess
      have hTc : ∀ ρ₀, (T ρ₀).card ≤ qC := fun ρ₀ => by
        simp only [T]
        split_ifs
        · exact hE.reads_card _ _ _
        · simp
      have hsub : {a | g (ρ a) ∈ Bh a} ⊆
          ⋃ i : Fin qC, {a | guess i (ρ a) ∈ hidden (res c ω a) (requestsBefore p s) req} := by
        rintro a ⟨hFa, x, hx, hxh⟩
        have h : ∃ a', ρ a' = ρ a := ⟨a, rfl⟩
        obtain ⟨h1, h2⟩ := hFlg _ hFa
        have hpre := requestsBefore_append_prefix _ h1
        have hclt : (c : ℕ) < (requests (splitLogs (g (ρ a))).2).length := by
          have := hpre.length_le
          rw [List.length_append, List.length_singleton, h2, hcond.2] at this
          omega
        have hreads : reads (res c ω a) (requests (splitLogs (g (ρ a))).2) (g (ρ a)).request =
            reads (res c ω h.choose) (requests (splitLogs (g (ρ a))).2) (g (ρ a)).request := by
          refine hE.reads_agree c ω a h.choose _ _ hclt fun rs₀ req₀ hp hlen => ?_
          obtain ⟨e1, e2⟩ := eq_of_append_singleton_prefix hp hpre (by rw [hlen, h2, hcond.2])
          rw [e1, e2, h2]
          exact h.choose_spec.symm
        have hxT : x ∈ (T (ρ a)).toList := by
          rw [Finset.mem_toList]
          simp only [T, dif_pos h]
          rw [← hreads]
          exact hx
        obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hxT
        have hiq : i < qC := by
          have := hTc (ρ a)
          rw [Finset.length_toList] at hi
          omega
        refine Set.mem_iUnion.2 ⟨⟨i, hiq⟩, ?_⟩
        show ((T (ρ a)).toList).getD i x₀ ∈ hidden (res c ω a) (requestsBefore p s) req
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hix]
        exact hxh
      have hfin : ν.toOuterMeasure (⋃ i : Fin qC, {a | guess i (ρ a) ∈
          hidden (res c ω a) (requestsBefore p s) req}) ≠ ⊤ := by
        rw [PMF.toOuterMeasure_apply]
        exact ν.tsum_coe_indicator_ne_top _
      refine (ENNReal.toReal_mono hfin (MeasureTheory.measure_mono hsub)).trans
        ((PMF.toReal_toOuterMeasure_iUnion_le _ _).trans ?_)
      calc ∑ i : Fin qC, (ν.toOuterMeasure {a | guess i (ρ a) ∈
            hidden (res c ω a) (requestsBefore p s) req}).toReal
          ≤ ∑ _i : Fin qC, ε := sum_le_sum fun i _ => hfind ω _ req hcond.2 (guess i)
        _ = qC * ε := by simp
    simp only [hpiece]
    refine (D.sum_mul_sum_prob_piece_le E ν (res c ω) ρ hag K Bh
      (M := Q * prob (logsIn F) (D.run E (res c ω a₀))) (fun a => ?_) hε).trans_eq (by ring)
    rw [← hrun a]
    exact D.sum_prob_answered_piece_le E (res c ω a) hps
  · have hP : ∀ a, D.readPiece (Q := Q) hidden reads c (res c ω a) s p = ∅ := fun a => by
      ext r
      simp only [readPiece, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨req, h1, h2, -⟩
      exact hcond ⟨by rw [h1]; simp, h2⟩
    have hF0 : {r : GameReg W n X Y Req A m | (p s ≠ none ∧
        (requestsBefore p s).length = c) ∧ cutAfter s (splitLogs r).2 = p} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hcond h.1
    simp only [hP, hF0, prob_empty', sum_const_zero, mul_zero, le_refl]

/-! ### O2H over the whole run -/

/-- **O2H over the whole run at hidden points correlated with the replies, with the challenger's
reads as queries, and a query budget** (module docstring). -/
theorem advantage_acceptProbOn_le_of_hiddenReads_budget [Nonempty X] [Nonempty Req]
    (bud : D.Budget q) {E : Env Ω Req A X Y Q St} {E' : Env Ω Req A X Y Q St'} {ν : PMF U}
    {res : Fin Q → Ω → U → Ω}
    {hidden : Ω → List Req → Req → Set X} {reads : Ω → List Req → Req → Finset X} {qC : ℕ}
    (hE : HiddenSideReads E E' ν res hidden reads qC) (ε : Fin Q → ℝ)
    (hfind : ∀ (c : Fin Q) ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε c)
    (L : Set (LogReg Req m)) :
    GordieHowe.advantage (D.acceptProbOn E noPost L) (D.acceptProbOn E' noPost L) ≤
      2 * √(q + if qC = 0 then 0 else Q) * √((n * q + qC * Q) * ∑ c, ε c) := by
  classical
  have hε0 : ∀ c, 0 ≤ ε c := fun c => by
    obtain ⟨x₀⟩ := ‹Nonempty X›
    obtain ⟨r₀⟩ := ‹Nonempty Req›
    obtain ⟨ω₀, -⟩ := E.μ.support_nonempty
    exact ENNReal.toReal_nonneg.trans
      (hfind c ω₀ (List.replicate c r₀) r₀ (by simp) fun _ => x₀)
  set q' : ℕ := q + if qC = 0 then 0 else Q with hq'
  set Bs : Ω → Set (GameReg W n X Y Req A m) := fun ω =>
    queriedOf (D.hiddenBefore (Q := Q) hidden ω) ∪ ⋃ c : Fin Q, D.readHitAt hidden reads c ω
    with hBs
  set Lc : ℕ → Set (LogReg Req m) := fun k =>
    {lg | queriedAt lg k = true} ∪ {lg | qC ≠ 0 ∧ lg ∈ answeredLogs Q k} with hLcdef
  have hLc : ∀ k, ReadsUpTo (Lc k) k := fun k lg lg' h =>
    or_congr (queriedLogs_readsUpTo k lg lg' h)
      (and_congr Iff.rfl (answeredLogs_readsUpTo Q k lg lg' h))
  have hcnt : ∀ r ∈ bud.holdSet m,
      ((range m).filter fun k => (splitLogs r).2 ∈ Lc k).card ≤ q' := by
    intro r hr
    have hq := hr.2 le_rfl
    unfold queriesBefore at hq
    refine (card_le_card (t := ((range m).filter fun k => queriedAt (splitLogs r).2 k = true) ∪
      ((range m).filter fun k => qC ≠ 0 ∧ (splitLogs r).2 ∈ answeredLogs Q k))
      fun k hk => ?_).trans ((card_union_le _ _).trans (add_le_add ?_ ?_))
    · rcases (mem_filter.1 hk).2 with h | h
      · exact mem_union.2 (Or.inl (mem_filter.2 ⟨(mem_filter.1 hk).1, h⟩))
      · exact mem_union.2 (Or.inr (mem_filter.2 ⟨(mem_filter.1 hk).1, h⟩))
    · exact (card_le_card fun k hk => mem_filter.2 ⟨(mem_filter.1 hk).1, (mem_filter.1 hk).2⟩).trans hq
    · split_ifs with h0
      · exact (card_eq_zero.2 (filter_eq_empty_iff.2 fun k _ h => h.1 h0)).le
      · exact (card_le_card fun k hk => mem_filter.2 ⟨(mem_filter.1 hk).1,
          (mem_filter.1 hk).2.2⟩).trans (card_filter_answeredLogs_le Q (splitLogs r).2)
  have hB : ∀ ω, ∀ k < m, ∀ r ∈ logsIn (reachableLogs k), r ∉ Bs ω →
      D.eventPerm E ω k r = D.eventPerm E' ω k r := by
    intro ω k hk r hR hrB
    cases hkind : D.kind r.workspace
    · rw [D.eventPerm_of_query E ω hk hkind, D.eventPerm_of_query E' ω hk hkind]
      have h : ∀ j, E.oracle ω (splitLogs r).2 (r.2 j).1 =
          E'.oracle ω (splitLogs r).2 (r.2 j).1 :=
        fun j => hE.oracle ω _ _ fun rs₀ req hp hl hmem => hrB (Or.inl ⟨j, by
          have : D.hiddenBefore (Q := Q) hidden ω r.1 = _ := if_pos hkind
          rw [this]
          exact ⟨rs₀, req, hp, hl, hmem⟩⟩)
      simp only [h]
    · refine D.eventPerm_eq_of_agree E E' hR (fun h => absurd (hkind.symm.trans h) (by simp))
        fun _ => ?_
      by_cases hl : (requests (splitLogs r).2).length < Q
      · exact hE.answer ω _ _ fun x hx rs₀ req₀ hp hlen hmem => hrB (Or.inr (Set.mem_iUnion.2
          ⟨⟨rs₀.length, hlen⟩, hkind, hl, rs₀, req₀, hp, rfl, x, hx, hmem⟩))
      · simp only [Env.answerAfter, hl, ↓reduceDIte]
  have hrun : ∀ ω, ‖D.run E ω - D.run E' ω‖ ≤
      2 * √q' * √(∑ k ∈ range m, ‖mask (Bs ω) (D.stage E ω k)‖ ^ 2) := fun ω =>
    D.norm_run_sub_le_of_count E E' (ω := ω) ω (fun _ => Bs ω) Lc bud.holdSet q' (hB ω)
      (fun k hk r hR hr => ⟨D.eventPerm_mem_countLogs E hE.reads_card ω hk hR hr,
        D.eventPerm_mem_countLogs E' hE.reads_card ω hk hR hr⟩) hLc
      (bud.stage_supported_holdSet E ω) (fun k hk v hv => bud.holdSet_step E ω hk hv)
      (fun k hk v hv => bud.holdSet_step E' ω hk hv) fun r hr => by convert hcnt r hr
  have hat : ∀ ω, |D.acceptProbOnAt E noPost L ω - D.acceptProbOnAt E' noPost L ω| ≤
      ‖D.run E ω - D.run E' ω‖ := by
    intro ω
    show |prob (D.gameAccept ∩ logsIn L)
        (logControlled (fun _ => LinearIsometryEquiv.refl ℂ _) (D.run E ω)) -
      prob (D.gameAccept ∩ logsIn L)
        (logControlled (fun _ => LinearIsometryEquiv.refl ℂ _) (D.run E' ω))| ≤ _
    refine (abs_prob_sub_le _ (by rw [LinearIsometryEquiv.norm_map, norm_run_env])
      (by rw [LinearIsometryEquiv.norm_map, norm_run_env])).trans ?_
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  set S : Ω → ℝ := fun ω => ∑ k ∈ range m, ‖mask (Bs ω) (D.stage E ω k)‖ ^ 2 with hSdef
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => sum_nonneg fun _ _ => sq_nonneg _
  have hv : ∀ ω (v : QState (GameReg W n X Y Req A m)), prob (Bs ω) v ≤
      ∑ c : Fin Q, prob (queriedOf (D.hiddenAt hidden c ω)) v +
        ∑ c : Fin Q, prob (D.readHitAt hidden reads c ω) v := by
    intro ω v
    refine (prob_le_sum_prob_of_subset (F := Sum.elim
      (fun _ : Unit => queriedOf (D.hiddenBefore (Q := Q) hidden ω))
      (fun c : Fin Q => D.readHitAt hidden reads c ω)) (fun r hr => ?_) v).trans ?_
    · rcases hr with hr | hr
      · exact Set.mem_iUnion.2 ⟨Sum.inl (), hr⟩
      · obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hr
        exact Set.mem_iUnion.2 ⟨Sum.inr c, hc⟩
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton]
      exact add_le_add (D.prob_queriedOf_hiddenBefore_le hidden ω v) le_rfl
  have hpt : ∀ ω, S ω ≤ ∑ c : Fin Q, ∑ i : Fin m,
      prob (queriedOf (D.hiddenAt hidden c ω)) (D.stage E ω i) +
      ∑ c : Fin Q, ∑ i : Fin m, prob (D.readHitAt hidden reads c ω) (D.stage E ω i) := by
    intro ω
    calc S ω = ∑ i : Fin m, prob (Bs ω) (D.stage E ω i) :=
          (Fin.sum_univ_eq_sum_range (fun k => ‖mask (Bs ω) (D.stage E ω k)‖ ^ 2) m).symm
      _ ≤ ∑ i : Fin m, (∑ c : Fin Q, prob (queriedOf (D.hiddenAt hidden c ω)) (D.stage E ω i) +
          ∑ c : Fin Q, prob (D.readHitAt hidden reads c ω) (D.stage E ω i)) :=
          sum_le_sum fun i _ => hv ω _
      _ = _ := by
          rw [sum_add_distrib]
          congr 1 <;> exact sum_comm
  have hSsum : ∑ ω, (E.μ ω).toReal * S ω ≤ (n * q + qC * Q) * ∑ c, ε c := by
    calc ∑ ω, (E.μ ω).toReal * S ω
        ≤ ∑ ω, (E.μ ω).toReal * (∑ c : Fin Q, ∑ i : Fin m,
          prob (queriedOf (D.hiddenAt hidden c ω)) (D.stage E ω i) +
          ∑ c : Fin Q, ∑ i : Fin m, prob (D.readHitAt hidden reads c ω) (D.stage E ω i)) :=
          sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) ENNReal.toReal_nonneg
      _ = ∑ c : Fin Q, ∑ ω, (E.μ ω).toReal * ∑ i : Fin m,
            prob (queriedOf (D.hiddenAt hidden c ω)) (D.stage E ω i) +
          ∑ c : Fin Q, ∑ ω, (E.μ ω).toReal * ∑ i : Fin m,
            prob (D.readHitAt hidden reads c ω) (D.stage E ω i) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
          congr 1 <;> exact sum_comm
      _ ≤ ∑ c : Fin Q, n * ε c * q + ∑ c : Fin Q, qC * Q * ε c :=
          add_le_add (sum_le_sum fun c _ =>
            Budget.sum_mul_sum_prob_queriedOf_hiddenAt_stage_le bud hE c (hε0 c) (hfind c))
            (sum_le_sum fun c _ => sum_mul_sum_prob_readHitAt_le hE c (hε0 c) (hfind c))
      _ = (n * q + qC * Q) * ∑ c, ε c := by
          rw [add_mul, mul_sum, mul_sum]
          congr 1
          exact sum_congr rfl fun c _ => by ring
  calc GordieHowe.advantage (D.acceptProbOn E noPost L) (D.acceptProbOn E' noPost L)
      = |∑ ω, (E.μ ω).toReal *
          (D.acceptProbOnAt E noPost L ω - D.acceptProbOnAt E' noPost L ω)| := by
        unfold GordieHowe.advantage acceptProbOn
        rw [hE.law, ← sum_sub_distrib]
        simp only [mul_sub]
    _ ≤ ∑ ω, (E.μ ω).toReal *
          |D.acceptProbOnAt E noPost L ω - D.acceptProbOnAt E' noPost L ω| :=
        (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun ω _ => by
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg])
    _ ≤ ∑ ω, (E.μ ω).toReal * (2 * √q' * √(S ω)) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ((hat ω).trans (hrun ω))
          ENNReal.toReal_nonneg
    _ = 2 * √q' * ∑ ω, (E.μ ω).toReal * √(S ω) := by
        rw [mul_sum]
        exact sum_congr rfl fun ω _ => by ring
    _ ≤ 2 * √q' * √(∑ ω, (E.μ ω).toReal * S ω) := by
        gcongr
        exact Real.sum_mul_sqrt_le_sqrt_sum_mul (fun _ => ENNReal.toReal_nonneg) E.μ.sum_toReal hS0
    _ ≤ 2 * √q' * √((n * q + qC * Q) * ∑ c, ε c) := by gcongr
    _ = _ := by simp only [hq', Nat.cast_add, Nat.cast_ite, Nat.cast_zero]

/-- `advantage_acceptProbOn_le_of_hiddenReads_budget` for every log. -/
theorem advantage_acceptProb_le_of_hiddenReads_budget [Nonempty X] [Nonempty Req]
    (bud : D.Budget q) {E : Env Ω Req A X Y Q St} {E' : Env Ω Req A X Y Q St'} {ν : PMF U}
    {res : Fin Q → Ω → U → Ω}
    {hidden : Ω → List Req → Req → Set X} {reads : Ω → List Req → Req → Finset X} {qC : ℕ}
    (hE : HiddenSideReads E E' ν res hidden reads qC) (ε : Fin Q → ℝ)
    (hfind : ∀ (c : Fin Q) ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε c) :
    GordieHowe.advantage (D.acceptProb E noPost) (D.acceptProb E' noPost) ≤
      2 * √(q + if qC = 0 then 0 else Q) * √((n * q + qC * Q) * ∑ c, ε c) := by
  rw [← acceptProbOn_univ, ← acceptProbOn_univ]
  exact advantage_acceptProbOn_le_of_hiddenReads_budget bud hE ε hfind Set.univ

omit [OracleState St X Y] [OracleState St' X Y] in
/-- **Without reads the bound is that of `HiddenSide`**: `2 q √(n ∑ c, ε c)`
(`advantage_acceptProbOn_le_of_hidden_budget` as a special case). -/
theorem advantage_acceptProbOn_le_of_hidden_budget' [Nonempty X] [Nonempty Req]
    (bud : D.Budget q) {E E' : Env Ω Req A X Y Q} {ν : PMF U} {res : Fin Q → Ω → U → Ω}
    {hidden : Ω → List Req → Req → Set X} (hE : HiddenSide E E' ν res hidden) (ε : Fin Q → ℝ)
    (hfind : ∀ (c : Fin Q) ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option A → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε c)
    (L : Set (LogReg Req m)) :
    GordieHowe.advantage (D.acceptProbOn E noPost L) (D.acceptProbOn E' noPost L) ≤
      2 * q * √(n * ∑ c, ε c) := by
  refine (advantage_acceptProbOn_le_of_hiddenReads_budget bud hE.toReads ε hfind L).trans_eq ?_
  simp only [↓reduceIte, add_zero, Nat.cast_zero, zero_mul]
  rw [show (n * q * ∑ c, ε c : ℝ) = (n * ∑ c, ε c) * q by ring,
    Real.sqrt_mul' _ (Nat.cast_nonneg q), mul_comm (√(n * ∑ c, ε c)) (√q), ← mul_assoc,
    mul_assoc 2 (√q) (√q), Real.mul_self_sqrt (Nat.cast_nonneg _)]

end Distinguisher

end GordieHowe.Quantum
