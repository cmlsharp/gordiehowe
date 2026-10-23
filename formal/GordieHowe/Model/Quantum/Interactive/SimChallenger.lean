-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Output
public import GordieHowe.Model.Quantum.Interactive.ZeroKnowledge

@[expose] public section

/-!
# The simulation challenger and its state

The challenger of the simulation-sound extractability game (Unruh 2017, ePrint 2017/398,
Definition 14, p. 21: "the oracle S''(x) invokes S(1^η, x)"): proof query number `c` with statement
`x` runs the simulator's program on `x` and the coins of proof query `c`, with the oracle in force,
answers with its proof and appends its assignment list (`GordieHowe.QROM.simExtChallenger`). Unlike the
zero-knowledge challenger (`GordieHowe.QROM.simChallenger`), a proof query carries no witness: any statement may
be sent to the simulator.

Facts about the challenger's state after a list of logged proof queries (`Challenger.stateAfter`):

- `Challenger.mem_ass_stateAfter`: every assignment in force was appended by the program of one
  logged proof query numbered below `Q`, run on the oracle in force before it;
- `Challenger.map_request_hist_stateAfter`: the proof queries in the history are the first `Q` proof queries;
- `requestsBefore_prefix`, `requestsBefore_succ_of_some`: the logged proof queries of the slots below
  `j` grow with `j`, by one at a logged slot.
-/

open Finset

namespace GordieHowe


/-! ### Logged proof queries -/

section Requests

variable {Req : Type*} {m : ℕ}

theorem Quantum.requestsBefore_prefix (lg : LogReg Req m) {j j' : ℕ} (h : j ≤ j') :
    requestsBefore lg j <+: requestsBefore lg j' := by
  induction j' with
  | zero => obtain rfl : j = 0 := by omega
            exact List.prefix_refl _
  | succ j' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (by omega)).trans (by rw [requestsBefore]; exact List.prefix_append _ _)
    · exact List.prefix_refl _

theorem Quantum.requestsBefore_succ_of_some (lg : LogReg Req m) (j : Fin m) {r : Req}
    (hr : lg j = some r) : requestsBefore lg (j + 1) = requestsBefore lg j ++ [r] := by
  rw [requestsBefore_succ_of_lt lg j.2, hr]
  rfl

/-- **At most `Q` slots hold a proof query numbered below `Q`**, so a list with `q` entries for each
of them has at most `Q · q` entries. -/
theorem Quantum.length_flatMap_logged_le {β : Type*} {Q q : ℕ} (lg : LogReg Req m) (f : Fin m → List β)
    (hf : ∀ j, (f j).length = q) :
    ((List.finRange m).flatMap fun j =>
      if (lg j).isSome ∧ (requestsBefore lg j).length < Q then f j else []).length ≤ Q * q := by
  classical
  set T := Finset.univ.filter fun j : Fin m => (lg j).isSome ∧ (requestsBefore lg j).length < Q
  have hlen : ((List.finRange m).flatMap fun j =>
      if (lg j).isSome ∧ (requestsBefore lg j).length < Q then f j else []).length =
      T.card * q := by
    rw [List.length_flatMap, ← Fin.sum_univ_def]
    simp only [apply_ite List.length, hf, List.length_nil]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul]
  have hlt : ∀ a b : Fin m, (lg a).isSome → (a : ℕ) < b →
      (requestsBefore lg a).length < (requestsBefore lg b).length := by
    intro a b ha hab
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ha
    have h1 := (requestsBefore_prefix lg (show (a : ℕ) + 1 ≤ b from hab)).length_le
    rw [requestsBefore_succ_of_some lg a hr] at h1
    simp at h1
    omega
  have hcard : T.card ≤ Q := by
    have h := Finset.card_le_card_of_injOn (fun j => (requestsBefore lg j).length)
      (s := T) (t := Finset.range Q) (fun j hj => by
        simp only [T, Finset.coe_filter, Finset.mem_univ, true_and] at hj
        simpa using hj.2) (by
        intro j₁ hj₁ j₂ hj₂ heq
        simp only [T, Finset.coe_filter, Finset.mem_univ, true_and] at hj₁ hj₂
        by_contra hne
        rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
        · exact absurd heq (ne_of_lt (hlt j₁ j₂ hj₁.1 h))
        · exact absurd heq (ne_of_gt (hlt j₂ j₁ hj₂.1 h)))
    simpa using h
  rw [hlen]
  exact Nat.mul_le_mul_right _ hcard

end Requests

namespace Quantum.Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C : Challenger X Y Req Resp)

/-- **The proof queries in the history are the first `Q` proof queries.** -/
theorem map_request_hist_stateAfter (H : X → Y) (c : C.Coins) (rs : List Req) :
    (C.stateAfter H c rs).hist.map HistoryEntry.request = rs.take C.Q := by
  induction rs using List.reverseRecOn with
  | nil => simp [stateAfter, Env.oracleIn_nil, Challenger.toPureEnv]
  | append_singleton rs r ih =>
    have hlen := C.stateAfter_hist_length H c rs
    rw [stateAfter, Env.oracleIn_append_singleton, Env.update]
    split_ifs with h
    · have h' : rs.length < C.Q := h
      rw [toPureEnv_respond_state]
      simp only [stateAfter] at ih
      simp only [List.map_append, ih, List.map_cons, List.map_nil]
      rw [List.take_of_length_le (by omega : rs.length ≤ C.Q),
        List.take_of_length_le (by simp; omega)]
    · have h' : ¬ rs.length < C.Q := h
      simp only [stateAfter] at ih
      rw [ih, List.take_append_of_le_length (by omega)]

/-- **Every assignment in force was appended by the program of one logged proof query** numbered
below `Q`, run on the oracle in force before it. -/
theorem mem_ass_stateAfter (H : X → Y) (c : C.Coins) {m : ℕ} (lg : LogReg Req m) :
    ∀ J, ∀ qa ∈ (C.stateAfter H c (requestsBefore lg J)).ass,
      ∃ (j : Fin m) (r : Req), (j : ℕ) < J ∧ lg j = some r ∧
        (requestsBefore lg j).length < C.Q ∧
        qa ∈ ((C.progAfter H c (requestsBefore lg j) r).run
          (C.oracleAfter H c (requestsBefore lg j))).assignments
  | 0, qa, hqa => by simp [requestsBefore, stateAfter, Env.oracleIn_nil, toPureEnv] at hqa
  | J + 1, qa, hqa => by
    by_cases hJ : J < m
    · rw [requestsBefore_succ_of_lt lg hJ] at hqa
      rcases hr : lg ⟨J, hJ⟩ with _ | r
      · rw [hr] at hqa
        simp only [Option.toList_none, List.append_nil] at hqa
        obtain ⟨j, r, hj, h1, h2, h3⟩ := mem_ass_stateAfter H c lg J qa hqa
        exact ⟨j, r, by omega, h1, h2, h3⟩
      · rw [hr] at hqa
        simp only [Option.toList_some] at hqa
        rw [stateAfter, Env.oracleIn_append_singleton, Env.update] at hqa
        split_ifs at hqa with hQ
        · rw [toPureEnv_respond_state] at hqa
          rcases List.mem_append.1 hqa with h | h
          · obtain ⟨j, r', hj, h1, h2, h3⟩ := mem_ass_stateAfter H c lg J qa h
            exact ⟨j, r', by omega, h1, h2, h3⟩
          · refine ⟨⟨J, hJ⟩, r, by simp, hr, hQ, ?_⟩
            have hb := C.stateAfter_base H c (requestsBefore lg J)
            simp only [stateAfter] at hb
            simpa [progAfter, oracleAfter, stateAfter, hb] using h
        · obtain ⟨j, r', hj, h1, h2, h3⟩ := mem_ass_stateAfter H c lg J qa hqa
          exact ⟨j, r', by omega, h1, h2, h3⟩
    · have : requestsBefore lg (J + 1) = requestsBefore lg J := by
        simp [requestsBefore, hJ]
      rw [this] at hqa
      obtain ⟨j, r, hj, h1, h2, h3⟩ := mem_ass_stateAfter H c lg J qa hqa
      exact ⟨j, r, by omega, h1, h2, h3⟩

end Quantum.Challenger

/-! ### The simulation challenger -/

namespace QROM

variable {X Y Stmt Proof SimCoins : Type}

/-- **The reply programs of the simulation challenger** (`simExtChallenger`): proof query number `c`
with statement `x` runs the simulator's program on `x` and the coins of proof query `c`, its proof the
response and its assignment list appended; proof queries numbered `Q` or later get `none`. -/
def simExtRespond (S : NARG.Simulator X Y Stmt Proof SimCoins) (Q : ℕ) (ω : Fin Q → SimCoins)
    (hist : List (Quantum.HistoryEntry Stmt Proof)) (x : Stmt) : GordieHowe.OracleProg X Y (Quantum.Reply X Y Proof) :=
  if h : hist.length < Q then
    (S.prog x (ω ⟨hist.length, h⟩)).bind fun r => .pure ⟨some r.proof, r.assignments⟩
  else .pure ⟨none, []⟩

/-- **The challenger of simulation-sound extractability** answering `Q` proof queries: proof query number
`c` with statement `x` runs the simulator's program on `x` and the coins of proof query `c`, with the
oracle in force, answers with its proof and appends its assignment list (Unruh 2017,
Definition 14, p. 21: "the oracle S''(x) invokes S(1^η, x)"); proof queries numbered `Q` or later are
answered by `none`. -/
noncomputable def simExtChallenger [Fintype SimCoins] [DecidableEq SimCoins]
    (S : NARG.Simulator X Y Stmt Proof SimCoins) (Q : ℕ) : Quantum.Challenger X Y Stmt Proof where
  Coins := Fin Q → SimCoins
  coins := PMF.pi fun _ => S.coins
  Q := Q
  q := S.q
  respond := simExtRespond S Q
  respond_queries ω hist x H := by
    unfold simExtRespond
    split_ifs
    · simpa using S.prog_queries _ _ H
    · simp

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype SimCoins]
  [DecidableEq SimCoins] (S : NARG.Simulator X Y Stmt Proof SimCoins) (Q : ℕ)

/-- The program of proof query number `|rs| < Q` is the simulator's program on the coins of that
proof query, its result paired with its assignment list. -/
theorem progAfter_simExtChallenger (H : X → Y) (c : Fin Q → SimCoins) (rs : List Stmt)
    (x : Stmt) (hQ : rs.length < Q) :
    (simExtChallenger S Q).progAfter H c rs x =
      (S.prog x (c ⟨rs.length, hQ⟩)).bind fun r => .pure ⟨some r.proof, r.assignments⟩ := by
  have hlen := (simExtChallenger S Q).stateAfter_hist_length H c rs
  have hl : ((simExtChallenger S Q).stateAfter H c rs).hist.length = rs.length := by
    rw [hlen]
    exact min_eq_left (le_of_lt hQ)
  have key : ∀ (hist : List (Quantum.HistoryEntry Stmt Proof)), hist.length = rs.length →
      (simExtChallenger S Q).respond c hist x =
        (S.prog x (c ⟨rs.length, hQ⟩)).bind fun r => .pure ⟨some r.proof, r.assignments⟩ := by
    intro hist h
    simp only [simExtChallenger, simExtRespond]
    rw [dif_pos (h ▸ hQ)]
    exact congrArg (fun i => (S.prog x (c i)).bind fun r =>
      .pure (⟨some r.proof, r.assignments⟩ : Quantum.Reply X Y Proof)) (Fin.ext h)
  exact key _ hl

end QROM

end GordieHowe
