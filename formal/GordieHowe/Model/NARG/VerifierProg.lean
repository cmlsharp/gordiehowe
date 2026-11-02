-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.NARG.Verifier

@[expose] public section

/-!
# The verifier as a classical oracle program

- `QROM.Expansion.prog X c k ans`: the expansion run as an oracle program for `k` more steps after
  the answers `ans` (`QROM.Expansion.run_prog`, `QROM.Expansion.length_trace_prog`).
- `NARG.Verifier.prog V c`: the verifier's decision on the claim `c` as a classical oracle
  program: the `kq` adaptive queries of its expansion, then its decision on the answers.
  `NARG.Verifier.run_prog`, `NARG.Verifier.run_prog_eq`: against every oracle `h` it returns
  `true` exactly when `V.Accepted h c`; `NARG.Verifier.prog_queriesLE`: at most `kq` queries.
-/

namespace GordieHowe

/-! ### A verifier as a classical oracle program -/

namespace QROM.Expansion

variable {A B C : Type*} (X : Expansion A B C) (c : C)

/-- **The expansion run as an oracle program** for `k` more steps after the answers `ans`: query
the next query of `X` on the answers so far and append its answer. -/
def prog : ℕ → List B → OracleProg A B (List B)
  | 0, ans => .pure ans
  | k + 1, ans => .query (X.next c ans) fun y => prog k (ans ++ [y])

/-- **The program's answers are the expansion's**: run after the answers to the first `i` queries,
for `k` more steps, it returns the answers to the first `i + k` queries. -/
theorem run_prog (h : A → B) : ∀ k i, (X.prog c k ((X.run h c i).map h)).run h =
    (X.run h c (i + k)).map h := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    have := ih (i + 1)
    simp only [Expansion.run_succ, List.map_append, List.map_cons, List.map_nil] at this
    simp only [prog, OracleProg.run_query, this, Nat.add_right_comm i 1 k, Nat.add_assoc]

/-- The program makes `k` queries. -/
theorem length_trace_prog (h : A → B) : ∀ k ans, ((X.prog c k ans).trace h).length = k := by
  intro k
  induction k with
  | zero => intro ans; rfl
  | succ k ih => intro ans; simp [prog, ih]

end QROM.Expansion

namespace NARG.Verifier

variable {A B Cl Stmt : Type} (V : Verifier A B Cl Stmt)

open Classical in
/-- **The verifier as a classical oracle program** on the claim `c`: its `kq` expansion queries,
then its decision on their answers (`true` when it accepts).

Running time: the verifier's `kq` queries, each computed by its expansion from the earlier
answers, and its decision on the answers; that of the verifier. This running time is argued here,
not proved in Lean. -/
noncomputable def prog (c : Cl) : OracleProg A B Bool :=
  (V.expansion.prog c V.kq []).bind fun ans =>
    .pure (if h : ans.length = V.kq then decide (V.AcceptsOn c fun i => ans[i.1]'(by omega))
      else false)

/-- **The program returns the verifier's decision.** -/
theorem run_prog (c : Cl) (h : A → B) : (V.prog c).run h = true ↔ V.Accepted h c := by
  have hr := V.expansion.run_prog c h V.kq 0
  simp only [QROM.Expansion.run, List.map_nil, Nat.zero_add] at hr
  have hl : ((V.expansion.run h c V.kq).map h).length = V.kq := by simp
  simp only [prog, OracleProg.run_bind, hr, OracleProg.run_pure, hl, dite_true,
    decide_eq_true_eq, Accepted]
  refine iff_of_eq (congrArg _ (funext fun i => ?_))
  simp [answers, QROM.Expansion.queries]

/-- The program makes `kq` queries. -/
theorem prog_queriesLE (c : Cl) : (V.prog c).QueriesLE V.kq := by
  intro h
  simp [prog, QROM.Expansion.length_trace_prog]

open Classical in
/-- **The program outputs the verifier's decision**, as a Boolean. -/
theorem run_prog_eq (c : Cl) (h : A → B) : (V.prog c).run h = decide (V.Accepted h c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact V.run_prog c h

end NARG.Verifier

end GordieHowe
