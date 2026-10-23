-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.Model
public import GordieHowe.Foundations.ToMathlib.PMFUniform

@[expose] public section

/-!
# Lazy sampling of the classical random oracle

The lazily sampled oracle (CY24 section 2.2, p. 22; CMS19 footnote 5, p. 18): the oracle keeps the
table of the queries made so far and their answers (a database `DB A B`); a query already in the
table is answered from it, and a fresh query is answered by a fresh uniform value, which the table
records. At the end, the points nobody queried are filled with independent uniform values, which
gives an oracle that the later parties (the verifier) read.

- `Alg.LazyState`, `Alg.lazyStep`, `Alg.lazyLaw`: the answers and the table of a `t`-query
  algorithm run against the lazily sampled oracle, step by step.
- `DB.fill`: the oracle that answers from a table and from a function elsewhere.
- `Alg.lazyRun`: the lazy run of `n` steps followed by the filling of the unqueried points.

What is proved:
- `Alg.lazyLaw_eq`: after `i` steps the lazy run has the law of the answers and the query log of
  the run against a uniformly random oracle (`Alg.stateOf`). The step is the resampling argument of
  `Alg.prob_step_le`: the answer at a fresh query is uniform and independent of the run so far.
- `Alg.lazyRun_eq`: the lazy run followed by the filling has the joint law of the answers, the
  query log and the whole oracle of the run against a uniformly random oracle. Filling a table
  with a uniform function, and swapping the two functions off the queried points, is an
  involution of uniform pairs (`swapOff`).
-/

namespace GordieHowe.QROM.DB

variable {A B : Type*} [DecidableEq A]

/-- **The oracle of a table completed by `g`**: the table's answer where it has one, `g`
elsewhere. -/
def fill (D : DB A B) (g : A → B) : A → B := fun x => (D.lookup x).getD (g x)

end GordieHowe.QROM.DB

namespace GordieHowe.ROM

open GordieHowe.QROM
open scoped ENNReal

namespace Alg

variable {A B C : Type} {t : ℕ}

/-- **The state of a lazy run**: the answers so far and the table of queries and answers. -/
@[ext]
structure LazyState (A B : Type) where
  /-- The answers so far. -/
  ans : List B
  /-- The table of queries and answers. -/
  log : DB A B

section Congr

variable (𝒜 : Alg A B C t) {h h' : A → B}

/-- **The run reads the oracle only at its queries**: oracles that agree on the first `j` queries
against `h` give the same first `j` queries. -/
theorem queries_congr : ∀ {j}, (∀ x ∈ 𝒜.queries h j, h' x = h x) → 𝒜.queries h' j = 𝒜.queries h j
  | 0, _ => rfl
  | j + 1, hag => by
    rw [queries_succ] at hag
    have ih := queries_congr fun x hx => hag x (List.mem_append_left _ hx)
    have hmap : (𝒜.queries h j).map h' = (𝒜.queries h j).map h :=
      List.map_congr_left fun x hx => hag x (List.mem_append_left _ hx)
    rw [queries_succ, queries_succ, queryAt, queryAt, ih, hmap]

variable [DecidableEq A]

theorem log_congr {j : ℕ} (hag : ∀ x ∈ 𝒜.queries h j, h' x = h x) : 𝒜.log h' j = 𝒜.log h j := by
  rw [log, log, 𝒜.queries_congr hag]
  exact logOf_eq_of_lookup fun x => by
    rw [lookup_logOf, lookup_logOf]
    by_cases hx : x ∈ 𝒜.queries h j
    · simp [hx, hag x hx]
    · simp [hx]

/-- **The answers and the query log after `j` steps against `h`.** -/
def stateOf (h : A → B) (j : ℕ) : LazyState A B := ⟨(𝒜.queries h j).map h, 𝒜.log h j⟩

theorem stateOf_congr {j : ℕ} (hag : ∀ x ∈ 𝒜.queries h j, h' x = h x) :
    𝒜.stateOf h' j = 𝒜.stateOf h j := by
  rw [stateOf, stateOf, 𝒜.log_congr hag, 𝒜.queries_congr hag]
  congr 1
  exact List.map_congr_left hag

end Congr

variable [DecidableEq A] [Fintype A] [Fintype B] [Nonempty B] (𝒜 : Alg A B C t)

/-- **The next state at the answer `y`**: query `next ans`; from the table if it has the query,
otherwise `y`, which the table records. -/
def lazyNext (s : LazyState A B) (y : B) : LazyState A B :=
  match s.log.lookup (𝒜.next s.ans) with
  | some z => ⟨s.ans ++ [z], s.log⟩
  | none => ⟨s.ans ++ [y], s.log.extend (𝒜.next s.ans) y⟩

/-- **One step of the lazy run**: the next query is answered from the table, or by a fresh uniform
value that the table records. -/
noncomputable def lazyStep (s : LazyState A B) : PMF (LazyState A B) :=
  (PMF.uniformOfFintype B).map (𝒜.lazyNext s)

/-- **The lazy run of `i` steps**: from the empty table. -/
noncomputable def lazyLaw : ℕ → PMF (LazyState A B)
  | 0 => PMF.pure ⟨[], ∅⟩
  | i + 1 => (lazyLaw i).bind 𝒜.lazyStep

omit [Fintype A] [Fintype B] [Nonempty B] in
/-- The step from `stateOf h j` at the resampled pair is the next state. -/
theorem stateOf_resample (j : ℕ) (p : (A → B) × B) :
    𝒜.stateOf (𝒜.resample j p).1 (j + 1) = 𝒜.lazyNext (𝒜.stateOf p.1 j) p.2 := by
  obtain ⟨h, y⟩ := p
  have hnext : 𝒜.next (𝒜.stateOf h j).ans = 𝒜.queryAt h j := rfl
  by_cases hq : 𝒜.queryAt h j ∈ 𝒜.queries h j
  · have hl : (𝒜.log h j).lookup (𝒜.queryAt h j) = some (h (𝒜.queryAt h j)) :=
      lookup_logOf_of_mem hq
    simp only [resample, hq, ite_true, lazyNext, hnext]
    change _ = match (𝒜.log h j).lookup (𝒜.queryAt h j) with
      | some z => _ | none => _
    rw [hl, stateOf, queries_succ]
    simp only [stateOf, List.map_append, List.map_cons, List.map_nil]
    congr 1
    exact logOf_append_of_mem hq
  · have hl : (𝒜.log h j).lookup (𝒜.queryAt h j) = none := by
      rw [log, lookup_logOf]
      simp [hq]
    simp only [resample, hq, ite_false, lazyNext, hnext]
    change _ = match (𝒜.log h j).lookup (𝒜.queryAt h j) with
      | some z => _ | none => _
    rw [hl]
    have hs := 𝒜.queries_update (h := h) y hq
    have hq' := 𝒜.queryAt_update (h := h) y hq
    rw [stateOf, queries_succ, hs, hq', log, queries_succ, hs, hq', logOf_append,
      logOf_update hq, Function.update_self]
    simp only [stateOf, List.map_append, List.map_cons, List.map_nil, log]
    congr 2
    exact List.map_congr_left fun x hx =>
      Function.update_of_ne (fun e : x = 𝒜.queryAt h j => hq (e ▸ hx)) _ _
    simp

/-- **Lazy sampling at step `i`**: the lazy run of `i` steps has the law of the answers and the
query log of the run against a uniformly random oracle. -/
theorem lazyLaw_eq : ∀ i, 𝒜.lazyLaw i = (PMF.uniformOfFintype (A → B)).map (𝒜.stateOf · i)
  | 0 => by
    rw [lazyLaw, show (fun h => 𝒜.stateOf h 0) = Function.const (A → B) (⟨[], ∅⟩ : LazyState A B) from rfl,
      PMF.map_const]
  | i + 1 => by
    rw [lazyLaw, lazyLaw_eq i, PMF.bind_map]
    let e : (A → B) × B ≃ (A → B) × B := (𝒜.resample_involutive i).toPerm _
    have hU : (PMF.uniformOfFintype ((A → B) × B)).map e = PMF.uniformOfFintype _ :=
      PMF.map_uniformOfFintype_equiv e
    calc (PMF.uniformOfFintype (A → B)).bind (𝒜.lazyStep ∘ (𝒜.stateOf · i))
        = (PMF.uniformOfFintype ((A → B) × B)).map
            (fun p => 𝒜.lazyNext (𝒜.stateOf p.1 i) p.2) := by
          rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
          congr 1
          funext h
          rw [PMF.map_comp]
          rfl
      _ = (PMF.uniformOfFintype ((A → B) × B)).map
            (fun p => 𝒜.stateOf (e p).1 (i + 1)) := by
          congr 1
          funext p
          exact (𝒜.stateOf_resample i p).symm
      _ = ((PMF.uniformOfFintype ((A → B) × B)).map e).map
            (fun p => 𝒜.stateOf p.1 (i + 1)) := by
          rw [PMF.map_comp]
          rfl
      _ = (PMF.uniformOfFintype (A → B)).map (𝒜.stateOf · (i + 1)) := by
          rw [hU]
          conv_rhs => rw [← PMF.map_fst_uniformOfFintype (β := B), PMF.map_comp]
          rfl

/-! ### Filling the unqueried points -/

/-- **The lazy run of `n` steps, then the unqueried points filled** by a uniform function: the
final state and the oracle `DB.fill log g` that answers every later query. -/
noncomputable def lazyRun (n : ℕ) : PMF (LazyState A B × (A → B)) :=
  (𝒜.lazyLaw n).bind fun s => (PMF.uniformOfFintype (A → B)).map fun g => (s, s.log.fill g)

/-- **Swapping two oracles off the first `n` queries of the first**: an involution of pairs, since
the first oracle's queries depend only on its values at them (`queries_congr`). -/
def swapOff (n : ℕ) (p : (A → B) × (A → B)) : (A → B) × (A → B) :=
  (fun x => if x ∈ 𝒜.queries p.1 n then p.1 x else p.2 x,
    fun x => if x ∈ 𝒜.queries p.1 n then p.2 x else p.1 x)

omit [Fintype A] [Fintype B] [Nonempty B] in
theorem queries_swapOff (n : ℕ) (p : (A → B) × (A → B)) :
    𝒜.queries (𝒜.swapOff n p).1 n = 𝒜.queries p.1 n :=
  𝒜.queries_congr fun x hx => by simp [swapOff, hx]

omit [Fintype A] [Fintype B] [Nonempty B] in
theorem swapOff_involutive (n : ℕ) : Function.Involutive (𝒜.swapOff n) := by
  intro p
  have hq := 𝒜.queries_swapOff n p
  obtain ⟨h, g⟩ := p
  ext x
  · simp only [swapOff] at hq ⊢
    rw [hq]
    split_ifs <;> rfl
  · simp only [swapOff] at hq ⊢
    rw [hq]
    split_ifs <;> rfl

omit [Fintype A] [Fintype B] [Nonempty B] in
/-- The first oracle after the swap is the first one's log filled by the second. -/
theorem fst_swapOff (n : ℕ) (p : (A → B) × (A → B)) :
    (𝒜.swapOff n p).1 = (𝒜.log p.1 n).fill p.2 := by
  funext x
  simp only [swapOff, DB.fill, log, lookup_logOf]
  split_ifs <;> rfl

/-- **Lazy sampling with filling**: the lazy run of `n` steps followed by the filling of the
unqueried points has the joint law of the answers, the query log and the whole oracle of the run
against a uniformly random oracle. -/
theorem lazyRun_eq (n : ℕ) :
    𝒜.lazyRun n = (PMF.uniformOfFintype (A → B)).map fun h => (𝒜.stateOf h n, h) := by
  let e : (A → B) × (A → B) ≃ (A → B) × (A → B) := (𝒜.swapOff_involutive n).toPerm _
  have hU : (PMF.uniformOfFintype ((A → B) × (A → B))).map e = PMF.uniformOfFintype _ :=
    PMF.map_uniformOfFintype_equiv e
  have hfst : ∀ p, 𝒜.stateOf (e p).1 n = 𝒜.stateOf p.1 n := fun p =>
    𝒜.stateOf_congr fun x hx => by
      change (𝒜.swapOff n p).1 x = p.1 x
      simp [swapOff, hx]
  calc 𝒜.lazyRun n
      = (PMF.uniformOfFintype ((A → B) × (A → B))).map
          (fun p => (𝒜.stateOf p.1 n, (𝒜.stateOf p.1 n).log.fill p.2)) := by
        rw [lazyRun, lazyLaw_eq, PMF.bind_map, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
        congr 1
        funext h
        rw [PMF.map_comp]
        rfl
    _ = (PMF.uniformOfFintype ((A → B) × (A → B))).map
          (fun p => (𝒜.stateOf (e p).1 n, (e p).1)) := by
        congr 1
        funext p
        rw [hfst]
        exact congrArg _ (𝒜.fst_swapOff n p).symm
    _ = ((PMF.uniformOfFintype ((A → B) × (A → B))).map e).map
          (fun p => (𝒜.stateOf p.1 n, p.1)) := by
        rw [PMF.map_comp]
        rfl
    _ = _ := by
        rw [hU]
        conv_rhs => rw [← PMF.map_fst_uniformOfFintype (β := A → B), PMF.map_comp]
        rfl

end Alg

end GordieHowe.ROM
