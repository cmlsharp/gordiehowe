-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.Range
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Classical oracle programs

`OracleProg A B R`: classical oracle programs (a query, then a continuation on the answer),
with their result `run h` and their query list `trace h`, and the padded query sequence
`paddedTrace` with its next-query form `paddedTrace_eq_next`. The challengers of the interactive
model answer requests with such programs (`GordieHowe/Model/Quantum/Interactive/Basic.lean`); the verifier's
queries are given as one (`GordieHowe.SPBCS.FullPast.roundsProgFullPast`, `GordieHowe/SPBCS/FullPast/Verifier.lean`), and
`OracleProg.toExpansion` (`GordieHowe/Model/QROM/Expansion.lean`) turns a program family into a query expansion.
-/

namespace GordieHowe

/-- **A classical oracle program** with queries in `A`, answers in `B` and result in `R`: it
returns, or it queries `a` and continues on the answer. -/
inductive OracleProg (A B R : Type*) where
  | pure : R → OracleProg A B R
  | query : A → (B → OracleProg A B R) → OracleProg A B R

namespace OracleProg

variable {A B R S ι : Type*} (h : A → B)

/-- `p`, then `f` on its result. -/
def bind : OracleProg A B R → (R → OracleProg A B S) → OracleProg A B S
  | pure r, f => f r
  | query a k, f => query a fun b => (k b).bind f

/-- The result of `p` against the oracle `h`. -/
def run : OracleProg A B R → R
  | pure r => r
  | query a k => (k (h a)).run

/-- An oracle program run against an oracle: `p h` is `p.run h`. -/
instance : CoeFun (OracleProg A B R) (fun _ => (A → B) → R) := ⟨fun p h => p.run h⟩

/-- The queries `p` makes against the oracle `h`, in order. -/
def trace : OracleProg A B R → List A
  | pure _ => []
  | query a k => a :: (k (h a)).trace

/-- **The program makes at most `q` queries**: against every oracle its query list has length at
most `q`. The query count of a program is a property of the program, not data beside it. -/
def QueriesLE (p : OracleProg A B R) (q : ℕ) : Prop :=
  ∀ h : A → B, (p.trace h).length ≤ q

/-- A query bound holds at every larger bound. -/
theorem QueriesLE.mono {p : OracleProg A B R} {q q' : ℕ} (hp : p.QueriesLE q) (hq : q ≤ q') :
    p.QueriesLE q' :=
  fun h => (hp h).trans hq

@[simp]
theorem run_pure (r : R) : (pure r : OracleProg A B R).run h = r := rfl

@[simp]
theorem trace_pure (r : R) : (pure r : OracleProg A B R).trace h = [] := rfl

@[simp]
theorem run_query (a : A) (k : B → OracleProg A B R) : (query a k).run h = (k (h a)).run h := rfl

@[simp]
theorem trace_query (a : A) (k : B → OracleProg A B R) :
    (query a k).trace h = a :: (k (h a)).trace h := rfl

@[simp]
theorem run_bind : ∀ (p : OracleProg A B R) (f : R → OracleProg A B S),
    (p.bind f).run h = (f (p.run h)).run h
  | pure _, _ => rfl
  | query a k, f => run_bind (k (h a)) f

@[simp]
theorem trace_bind : ∀ (p : OracleProg A B R) (f : R → OracleProg A B S),
    (p.bind f).trace h = p.trace h ++ (f (p.run h)).trace h
  | pure _, _ => rfl
  | query a k, f => by
    simp only [bind, trace_query, run_query, trace_bind (k (h a)) f, List.cons_append]

/-- Run `f x` for each `x` of `l` in order, discarding the results. -/
def forEach : List ι → (ι → OracleProg A B R) → OracleProg A B Unit
  | [], _ => pure ()
  | x :: l, f => (f x).bind fun _ => forEach l f

@[simp]
theorem trace_forEach : ∀ (l : List ι) (f : ι → OracleProg A B R),
    (forEach l f).trace h = l.flatMap fun x => (f x).trace h
  | [], _ => rfl
  | x :: l, f => by simp only [forEach, trace_bind, trace_forEach l f, List.flatMap_cons]

/-- Query every element of `l` in order and return the answers. -/
def queryAll : List A → OracleProg A B (List B)
  | [] => pure []
  | a :: l => query a fun b => (queryAll l).bind fun bs => pure (b :: bs)

@[simp]
theorem run_queryAll : ∀ l : List A, (queryAll l : OracleProg A B (List B)).run h = l.map h
  | [] => rfl
  | a :: l => by simp only [queryAll, run_query, run_bind, run_queryAll l, run_pure, List.map_cons]

@[simp]
theorem trace_queryAll : ∀ l : List A, (queryAll l : OracleProg A B (List B)).trace h = l
  | [] => rfl
  | a :: l => by
    simp only [queryAll, trace_query, trace_bind, trace_queryAll l, trace_pure, List.append_nil]

/-- The next query of `p` on the answers `ans` to its earlier queries; once `p` has returned,
the fixed query `pad`. -/
def next (pad : A) : OracleProg A B R → List B → A
  | pure _, _ => pad
  | query a _, [] => a
  | query _ k, b :: ans => (k b).next pad ans

/-- The `i`-th query of `p` against `h`, padded with `pad` after the last. -/
def paddedTrace (pad : A) (p : OracleProg A B R) (i : ℕ) : A := ((p.trace h)[i]?).getD pad

/-- Every padded query of `p` is the next query of `p` on the answers to the earlier ones. -/
theorem paddedTrace_eq_next (pad : A) : ∀ (p : OracleProg A B R) (i : ℕ),
    p.paddedTrace h pad i = p.next pad ((List.range i).map (h ∘ p.paddedTrace h pad))
  | pure _, _ => rfl
  | query _ _, 0 => rfl
  | query a k, i + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    exact paddedTrace_eq_next pad (k (h a)) i

/-- **The program with its result mapped by `f`**: the same queries, then `f` of the result. -/
def mapOutput (f : R → S) (p : OracleProg A B R) : OracleProg A B S :=
  p.bind fun r => pure (f r)

@[simp]
theorem run_mapOutput (f : R → S) (p : OracleProg A B R) : (p.mapOutput f).run h = f (p.run h) := by
  simp [mapOutput]

@[simp]
theorem trace_mapOutput (f : R → S) (p : OracleProg A B R) : (p.mapOutput f).trace h = p.trace h := by
  simp [mapOutput]

theorem QueriesLE.mapOutput {p : OracleProg A B R} {q : ℕ} (hp : p.QueriesLE q) (f : R → S) :
    (p.mapOutput f).QueriesLE q :=
  fun h => (trace_mapOutput h f p).symm ▸ hp h

/-! ### Combinators: renaming queries, tabulating, iterating -/

section Combinators

open scoped BigOperators

variable {A' B' : Type*}

/-- **A program run against another oracle**: query `f a` in place of `a` and read the answer
through `g`. -/
def mapQuery (f : A → A') (g : B' → B) : OracleProg A B R → OracleProg A' B' R
  | pure r => pure r
  | query a k => query (f a) fun b => mapQuery f g (k (g b))

theorem run_mapQuery (f : A → A') (g : B' → B) (h' : A' → B') :
    ∀ p : OracleProg A B R, (p.mapQuery f g).run h' = p.run (g ∘ h' ∘ f)
  | pure _ => rfl
  | query a k => run_mapQuery f g h' (k (g (h' (f a))))

theorem trace_mapQuery (f : A → A') (g : B' → B) (h' : A' → B') :
    ∀ p : OracleProg A B R, (p.mapQuery f g).trace h' = (p.trace (g ∘ h' ∘ f)).map f
  | pure _ => rfl
  | query a k => by
    simp only [mapQuery, trace_query, List.map_cons, trace_mapQuery f g h' (k (g (h' (f a))))]
    rfl

theorem length_trace_mapQuery (f : A → A') (g : B' → B) (h' : A' → B') (p : OracleProg A B R) :
    ((p.mapQuery f g).trace h').length = (p.trace (g ∘ h' ∘ f)).length := by
  rw [trace_mapQuery, List.length_map]


variable [DecidableEq ι] {β : Type*}

/-- **Tabulate a function by programs**: `P i` for each `i` of `l` in order; the result is the
result of `P i` at each `i` of `l` and `d i` elsewhere. -/
def tabulate (d : ι → β) : List ι → (ι → OracleProg A B β) → OracleProg A B (ι → β)
  | [], _ => pure d
  | i :: l, P => (P i).bind fun b => (tabulate d l P).bind fun g => pure (Function.update g i b)

theorem run_tabulate (d : ι → β) : ∀ (l : List ι) (P : ι → OracleProg A B β),
    (tabulate d l P).run h = fun j => if j ∈ l then (P j).run h else d j
  | [], _ => by funext j; simp [tabulate]
  | i :: l, P => by
    funext j
    simp only [tabulate, run_bind, run_pure, run_tabulate d l P, List.mem_cons]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

theorem length_trace_tabulate (d : ι → β) : ∀ (l : List ι) (P : ι → OracleProg A B β),
    ((tabulate d l P).trace h).length = (l.map fun i => ((P i).trace h).length).sum
  | [], _ => rfl
  | i :: l, P => by
    simp [tabulate, length_trace_tabulate d l P]

/-- **Iterate steps**: the steps `0, …, m - 1` in order, from the state `s`. -/
def iterate (step : ℕ → S → OracleProg A B S) : ℕ → S → OracleProg A B S
  | 0, s => pure s
  | m + 1, s => (iterate step m s).bind (step m)

theorem run_iterate_zero (step : ℕ → S → OracleProg A B S) (s : S) :
    (iterate step 0 s).run h = s := rfl

theorem run_iterate_succ (step : ℕ → S → OracleProg A B S) (m : ℕ) (s : S) :
    (iterate step (m + 1) s).run h = (step m ((iterate step m s).run h)).run h := by
  simp [iterate]

/-- The queries of `iterate` are at most the sum of per-step bounds. -/
theorem length_trace_iterate_le (step : ℕ → S → OracleProg A B S) (c : ℕ → ℕ)
    (hc : ∀ r s, ((step r s).trace h).length ≤ c r) :
    ∀ m s, ((iterate step m s).trace h).length ≤ ∑ r ∈ Finset.range m, c r
  | 0, _ => by simp [iterate]
  | m + 1, s => by
    simp only [iterate, trace_bind, List.length_append, Finset.sum_range_succ]
    exact Nat.add_le_add (length_trace_iterate_le step c hc m s) (hc _ _)

end Combinators

/-! ### Dependence on the oracle, and translation -/

section Translate

variable {A' B' : Type*}

/-- **A program run on the oracle `h₁` reads it only at its trace**: on an oracle `h₂` agreeing
with `h₁` there, it has the same result. -/
theorem run_congr {h₁ h₂ : A → B} :
    ∀ (p : OracleProg A B R), (∀ a ∈ p.trace h₁, h₁ a = h₂ a) → p.run h₁ = p.run h₂
  | .pure _, _ => rfl
  | .query a k, h => by
    simp only [trace_query, List.mem_cons, forall_eq_or_imp] at h
    rw [run_query, run_query, ← h.1]
    exact run_congr (k (h₁ a)) h.2

/-- A query whose answer can change the result must occur in the original run's trace. -/
theorem mem_trace_of_run_update_ne [DecidableEq A] (p : OracleProg A B R)
    {h : A → B} {a : A} {b : B} (hne : p.run h ≠ p.run (Function.update h a b)) :
    a ∈ p.trace h := by
  by_contra ha
  apply hne
  apply run_congr p
  intro a' ha'
  have hne' : a' ≠ a := fun heq => ha (heq ▸ ha')
  exact (Function.update_of_ne hne' _ _).symm

/-- **A program run on the oracle `h₁` reads it only at its trace**: on an oracle `h₂` agreeing
with `h₁` there, it makes the same queries. -/
theorem trace_congr {h₁ h₂ : A → B} :
    ∀ (p : OracleProg A B R), (∀ a ∈ p.trace h₁, h₁ a = h₂ a) → p.trace h₁ = p.trace h₂
  | .pure _, _ => rfl
  | .query a k, h => by
    simp only [trace_query, List.mem_cons, forall_eq_or_imp] at h
    rw [trace_query, trace_query, ← h.1, trace_congr (k (h₁ a)) h.2]

/-- **A program on another query and answer type**: query `a` becomes the query `ι a`, and its
answer is read as `g a` of the answer there. -/
def translate (ι : A → A') (g : A → B' → B) : OracleProg A B R → OracleProg A' B' R
  | .pure r => .pure r
  | .query a k => .query (ι a) fun b' => translate ι g (k (g a b'))

theorem run_translate (ι : A → A') (g : A → B' → B) (h' : A' → B') :
    ∀ (p : OracleProg A B R), (translate ι g p).run h' = p.run fun a => g a (h' (ι a))
  | .pure _ => rfl
  | .query a k => by
    rw [translate, run_query, run_query]
    exact run_translate ι g h' (k (g a (h' (ι a))))

theorem trace_translate (ι : A → A') (g : A → B' → B) (h' : A' → B') :
    ∀ (p : OracleProg A B R),
      (translate ι g p).trace h' = (p.trace fun a => g a (h' (ι a))).map ι
  | .pure _ => rfl
  | .query a k => by
    rw [translate, trace_query, trace_query, List.map_cons]
    exact congrArg _ (trace_translate ι g h' (k (g a (h' (ι a)))))

end Translate

end OracleProg

end GordieHowe
