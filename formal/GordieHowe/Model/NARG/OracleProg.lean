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
queries are given as one (`GordieHowe.SPBCS.roundsProg`, `GordieHowe/SPBCS/Verifier.lean`), and
`OracleProg.toExpansion` (`GordieHowe/Model/QROM/Expansion.lean`) turns a program family into a query expansion.
`QueriesLE.pure`, `QueriesLE.bind`, `QueriesLE.query`, `QueriesLE.tabulate`: the query bounds of
`pure`, sequential composition, a query and a tabulation.
`AllOut p P`: every output of `p`, on every path of answers, satisfies `P` (`AllOut.run`,
`mono`, `mapOutput`, `translate`).
`InputsBefore Pair Mark L`: every marked entry of a query list has an earlier entry paired with
it, closed under `append` and `flatMap`.
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

/-- A program that returns at once makes no queries. -/
theorem QueriesLE.pure (r : R) (q : ℕ) : (OracleProg.pure r : OracleProg A B R).QueriesLE q :=
  fun _ => Nat.zero_le _

/-- **The query bound of a sequential composition**: `p` with at most `q₁` queries, then a
continuation with at most `q₂` queries on every result, makes at most `q₁ + q₂` queries. -/
theorem QueriesLE.bind {p : OracleProg A B R} {f : R → OracleProg A B S} {q₁ q₂ : ℕ}
    (hp : p.QueriesLE q₁) (hf : ∀ r, (f r).QueriesLE q₂) : (p.bind f).QueriesLE (q₁ + q₂) :=
  fun h => by
    rw [trace_bind, List.length_append]
    exact Nat.add_le_add (hp h) (hf _ h)

/-- **A query, then a continuation with at most `q` queries on every answer**, makes at most
`q + 1` queries. -/
theorem QueriesLE.query (a : A) {k : B → OracleProg A B R} {q : ℕ} (hk : ∀ b, (k b).QueriesLE q) :
    (OracleProg.query a k).QueriesLE (q + 1) :=
  fun h => by
    rw [trace_query, List.length_cons]
    exact Nat.add_le_add_right (hk _ h) 1

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

/-- **The query bound of a tabulation**: programs with at most `q` queries at each of the `|l|`
indices make at most `|l| · q` queries. -/
theorem QueriesLE.tabulate {ι : Type*} [DecidableEq ι] (d : ι → R) (l : List ι)
    {P : ι → OracleProg A B R} {q : ℕ} (hP : ∀ i, (P i).QueriesLE q) :
    (OracleProg.tabulate d l P).QueriesLE (l.length * q) := fun h => by
  rw [length_trace_tabulate]
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm (l.length * q)]
    exact Nat.add_le_add (hP i h) ih

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

/-- **Translating a composed program translates its parts.** -/
theorem translate_bind {S : Type*} (ι : A → A') (g : A → B' → B) :
    ∀ (p : OracleProg A B R) (f : R → OracleProg A B S),
      translate ι g (p.bind f) = (translate ι g p).bind fun r => translate ι g (f r)
  | .pure _, _ => rfl
  | .query a k, f => by
    change OracleProg.query _ _ = OracleProg.query _ _
    exact congrArg _ (funext fun b => translate_bind ι g (k _) f)

/-- **Two translations in a row are one translation.** -/
theorem translate_translate {A'' B'' : Type*} (ι : A → A') (g : A → B' → B) (ι' : A' → A'')
    (g' : A' → B'' → B') :
    ∀ p : OracleProg A B R,
      translate ι' g' (translate ι g p) = translate (ι' ∘ ι) (fun a b => g a (g' (ι a) b)) p
  | .pure _ => rfl
  | .query a k => by
    change OracleProg.query _ _ = OracleProg.query _ _
    exact congrArg _ (funext fun b => translate_translate ι g ι' g' (k _))

/-- **A translation is determined by its query map and its answer maps.** -/
theorem translate_congr {ι : A → A'} {g g' : A → B' → B} (hg : ∀ a b, g a b = g' a b)
    (p : OracleProg A B R) : translate ι g p = translate ι g' p := by
  rw [show g = g' from funext fun a => funext (hg a)]

end Translate

/-! ### Outputs on every path -/


section AllOut

variable {α β : Type*}

/-- **Every output of `p` satisfies `P`**: on every path of answers, not only at an oracle. -/
def AllOut : OracleProg A B α → (α → Prop) → Prop
  | .pure a, P => P a
  | .query _ k, P => ∀ b, AllOut (k b) P

theorem AllOut.mono {P P' : α → Prop} :
    ∀ {p : OracleProg A B α}, p.AllOut P → (∀ a, P a → P' a) → p.AllOut P'
  | .pure _, hp, h => h _ hp
  | .query _ k, hp, h => fun b => AllOut.mono (p := k b) (hp b) h

/-- An output on every path is the output at every oracle. -/
theorem AllOut.run {P : α → Prop} : ∀ {p : OracleProg A B α}, p.AllOut P → ∀ h, P (p.run h)
  | .pure _, hp, _ => hp
  | .query a k, hp, h => AllOut.run (p := k (h a)) (hp (h a)) h

theorem AllOut.mapOutput {P : β → Prop} (f : α → β) :
    ∀ {p : OracleProg A B α}, p.AllOut (fun a => P (f a)) → (p.mapOutput f).AllOut P
  | .pure _, hp => hp
  | .query _ k, hp => fun b => AllOut.mapOutput f (p := k b) (hp b)

/-- **Two properties of every output give their conjunction on every output.** -/
theorem AllOut.and {P P' : α → Prop} :
    ∀ {p : OracleProg A B α}, p.AllOut P → p.AllOut P' → p.AllOut fun a => P a ∧ P' a
  | .pure _, hp, hp' => ⟨hp, hp'⟩
  | .query _ k, hp, hp' => fun b => AllOut.and (p := k b) (hp b) (hp' b)

/-- **Renaming the queries and recoding the answers keeps the outputs on every path.** -/
theorem AllOut.mapQuery {A' B' : Type} (f : A → A') (g : B' → B) {P : α → Prop} :
    ∀ {p : OracleProg A B α}, p.AllOut P → (p.mapQuery f g).AllOut P
  | .pure _, hp => hp
  | .query _ k, hp => fun b => AllOut.mapQuery f g (p := k (g b)) (hp _)

theorem AllOut.translate {A' B' : Type} (ι : A → A') (g : A → B' → B) {P : α → Prop} :
    ∀ {p : OracleProg A B α}, p.AllOut P → (p.translate ι g).AllOut P
  | .pure _, hp => hp
  | .query a k, hp => fun b => AllOut.translate ι g (p := k (g a b)) (hp _)

end AllOut

end OracleProg

/-! ### Paired entries of a list -/

/-- **Every marked entry of `L` has an earlier entry paired with it.** -/
def InputsBefore {A : Type*} (Pair : A → A → Prop) (Mark : A → Prop) (L : List A) : Prop :=
  ∀ i (hi : i < L.length), Mark L[i] → ∃ a ∈ L.take i, Pair a L[i]

namespace InputsBefore

variable {A : Type*} {Pair Pair' : A → A → Prop} {Mark : A → Prop}

/-- A list without marked entries. -/
theorem of_forall_not {L : List A} (h : ∀ x ∈ L, ¬ Mark x) : InputsBefore Pair Mark L :=
  fun _ hi hm => absurd hm (h _ (List.getElem_mem hi))

/-- A weaker pairing. -/
theorem mono {L : List A} (hP : ∀ a b, Pair a b → Pair' a b) (h : InputsBefore Pair Mark L) :
    InputsBefore Pair' Mark L := fun i hi hm => by
  obtain ⟨a, ha, hp⟩ := h i hi hm
  exact ⟨a, ha, hP _ _ hp⟩

/-- **Concatenation**: the earlier entries of the second part include the first part. -/
theorem append {L M : List A} (hL : InputsBefore Pair Mark L) (hM : InputsBefore Pair Mark M) :
    InputsBefore Pair Mark (L ++ M) := by
  intro i hi hm
  by_cases hiL : i < L.length
  · have e : (L ++ M)[i] = L[i] := List.getElem_append_left hiL
    rw [e] at hm ⊢
    obtain ⟨a, ha, hp⟩ := hL i hiL hm
    exact ⟨a, by rw [List.take_append_of_le_length hiL.le]; exact ha, hp⟩
  · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hiL)
    have hi' : i' < M.length := by simp at hi; omega
    have e : (L ++ M)[L.length + i'] = M[i'] := by simp
    rw [e] at hm ⊢
    obtain ⟨a, ha, hp⟩ := hM i' hi' hm
    exact ⟨a, by rw [List.take_append]; exact List.mem_append_right _ (by simpa using ha), hp⟩

/-- **Concatenation of a family.** -/
theorem flatMap {ι : Type*} {f : ι → List A} :
    ∀ {l : List ι}, (∀ x ∈ l, InputsBefore Pair Mark (f x)) →
      InputsBefore Pair Mark (l.flatMap f)
  | [], _ => of_forall_not (by simp)
  | x :: l, h => by
    rw [List.flatMap_cons]
    exact (h x (List.mem_cons_self ..)).append (flatMap fun y hy => h y (List.mem_cons_of_mem _ hy))

end InputsBefore

end GordieHowe
