-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.OfFn
public import GordieHowe.Foundations.Probability.Probability
public import GordieHowe.Model.NARG.OracleProg
public import GordieHowe.Model.QROM.Database

@[expose] public section

/-!
# Classical query expansions

The classical computation CMS19 (Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum
Random Oracle Model", ePrint 2019/834; printed pages) appends to a proof-producing adversary in
the proof of Proposition 8.11 (p. 42): `BCSExpand^h(π)` (p. 39) runs the verifier's oracle
queries on the proof `π` and outputs the queries with their answers.

- `Expansion A B C`: a classical adaptive oracle algorithm on inputs `C`, given by its next
  query `next c ans` as a function of the input and the answers to the earlier queries. Run for
  `k` steps against `h : A → B` it makes exactly `k` queries, `X.queries h c : Fin k → A`, and
  `X.expand h c = ⟨a, h ∘ a, c⟩` is the tuple `BCSExpand^h(c)` outputs.
- `OracleProg A B R` (`GordieHowe/Model/NARG/OracleProg.lean`): classical oracle programs.
  `OracleProg.toExpansion` turns a program family into an expansion whose queries are the
  program's queries, padded with a fixed query (`OracleProg.queries_toExpansion`). The verifier's queries are given as a program
  (`GordieHowe.SPBCS.queryProg`, `GordieHowe/SPBCS/Verifier.lean`), which shows that they can be computed by
  an adaptive classical algorithm with one oracle query per listed query.
- `ansList q h m`, `qryList q h m`: the answers and the queries of an adaptive strategy `q`
  (query `i` is `q i ans h`, from the answers `ans` to the earlier queries and the oracle). When
  every query lies in a set `Dom` and depends on the oracle only off `Dom`, the answers to `m`
  distinct queries are dominated by uniform answers: `prob_nodup_ansList_mem_le`,
  `Pr[h : the queries are distinct ∧ ansList q h m ∈ S] ≤ |S| / |B|^m` (lazy sampling, in
  counting form).
-/

namespace GordieHowe.QROM

/-! ### Expansions -/

/-- **A classical adaptive oracle algorithm on inputs `C`** with queries in `A` and answers in
`B`: its next query `next c ans` on the input `c`, where `ans` lists the answers to the earlier
queries in order. Run for `k` steps it makes exactly `k` queries; this is the shape of
`BCSExpand` (CMS19 p. 39), which CMS19's proof of Proposition 8.11 (p. 42) runs on the proof
output by the adversary. -/
structure Expansion (A B C : Type*) where
  /-- The next query, from the input and the answers to the earlier queries. -/
  next : C → List B → A

namespace Expansion

variable {A B C A' : Type*} (X : Expansion A B C) (h : A → B) (c : C)

/-- The first `i` queries of `X` on the input `c` against the oracle `h`. -/
def run (X : Expansion A B C) (h : A → B) (c : C) : ℕ → List A
  | 0 => []
  | i + 1 => run X h c i ++ [X.next c ((run X h c i).map h)]

@[simp]
theorem length_run : ∀ i, (X.run h c i).length = i
  | 0 => rfl
  | i + 1 => by simp [run, length_run i]

/-- The `k` queries of `X` on `c` against `h`. -/
def queries {k : ℕ} (i : Fin k) : A := (X.run h c k)[i.1]'(by simp)

/-- **The output of the expansion** (`BCSExpand^h(c)`, CMS19 p. 39): the `k` queries of `X`
on `c`, their answers under `h`, and the input `c`. -/
def expand {k : ℕ} : BaseGame.Tuple A B C k :=
  ⟨X.queries h c, fun i => h (X.queries h c i), c⟩

/-- A sequence `f` of queries in which every query is the next query of `X` on the answers to
the earlier ones is the run of `X`. -/
theorem run_eq_of_next {f : ℕ → A} (hf : ∀ i, f i = X.next c ((List.range i).map (h ∘ f))) :
    ∀ i, X.run h c i = (List.range i).map f
  | 0 => rfl
  | i + 1 => by
    rw [run, run_eq_of_next hf i, List.range_succ, List.map_append, List.map_map, ← hf i]
    rfl

/-- The queries of `X` are `f` when every term of `f` is the next query of `X` on the answers
to the earlier ones. -/
theorem queries_eq_of_next {f : ℕ → A} (hf : ∀ i, f i = X.next c ((List.range i).map (h ∘ f)))
    {k : ℕ} (i : Fin k) : X.queries h c i = f i := by
  simp only [queries, X.run_eq_of_next h c hf k, List.getElem_map, List.getElem_range]

theorem run_succ (i : ℕ) : X.run h c (i + 1) = X.run h c i ++ [X.next c ((X.run h c i).map h)] :=
  rfl

/-- The first `i` queries are a prefix of the first `n ≥ i`. -/
theorem take_run {i n : ℕ} (hi : i ≤ n) : (X.run h c n).take i = X.run h c i := by
  induction n, hi using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [run_succ, List.take_append_of_le_length (by simp; omega), ih]

/-- Query `i` is the next query on the answers to the queries before it. -/
theorem getElem_run {i n : ℕ} (hi : i < n) :
    (X.run h c n)[i]'(by simp; omega) = X.next c ((X.run h c i).map h) := by
  have h1 := congrArg (fun l => l[i]?) (X.take_run h c (Nat.succ_le_of_lt hi))
  simp only [List.getElem?_take, show i < i + 1 from Nat.lt_succ_self i, if_true] at h1
  rw [run_succ, List.getElem?_append_right (by simp)] at h1
  simp only [length_run, Nat.sub_self, List.getElem?_cons_zero] at h1
  rw [List.getElem?_eq_getElem (by simp; omega)] at h1
  exact Option.some_inj.1 h1

/-- **The queries of `X` computed from answers** `a` to its `k` queries: query `i` on `c` is the
next query of `X` on the answers `a j`, `j < i`, to the queries before it. -/
def queriesOn (c : C) {k : ℕ} (a : Fin k → B) (i : Fin k) : A :=
  X.next c (List.ofFn fun j : Fin i => a (Fin.castLE i.2.le j))

/-- **The queries of `X` against `h` are its queries computed from their answers under `h`.** -/
theorem queries_eq_queriesOn {k : ℕ} (i : Fin k) :
    X.queries h c i = X.queriesOn c (fun j => h (X.queries h c j)) i := by
  simp only [queries, queriesOn]
  rw [X.getElem_run h c i.2]
  congr 1
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  have hj : (X.run h c i)[j]'(by simpa using h1) = (X.run h c k)[j]'(by have := i.2; simp at h1; simp; omega) := by
    simp only [← X.take_run h c i.2.le, List.getElem_take]
  simp only [List.getElem_map, List.getElem_ofFn, Fin.coe_castLE, hj]

/-- **A tuple whose queries are computed from its answers, answered by `h`, is the expansion
against `h`**. -/
theorem expand_eq_of_queries_eq {k : ℕ} {o : BaseGame.Tuple A B C k}
    (hq : o.queries = X.queriesOn o.out o.answers) (hh : ∀ i, h (o.queries i) = o.answers i) :
    X.expand h o.out = o := by
  have hQ : ∀ n (i : Fin k), i.1 = n → X.queries h o.out i = o.queries i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      rw [X.queries_eq_queriesOn h o.out i, hq]
      simp only [queriesOn]
      congr 1
      refine List.ofFn_inj.2 (funext fun j => ?_)
      rw [ih j (by omega) (Fin.castLE _ j) rfl, hh]
  have hqs : X.queries h o.out = o.queries := funext fun i => hQ i.1 i rfl
  rcases o with ⟨q, a, c⟩
  simp only [expand] at hqs hh ⊢
  subst hqs
  congr
  funext i
  exact hh i

/-- `X` with its queries encoded by `ι`. -/
def map (ι : A → A') : Expansion A' B C := ⟨fun c ans => ι (X.next c ans)⟩

theorem run_map (ι : A → A') (h : A' → B) : ∀ i, (X.map ι).run h c i = (X.run (h ∘ ι) c i).map ι
  | 0 => rfl
  | i + 1 => by
    simp only [run, run_map ι h i, List.map_append, List.map_map, List.map_cons, List.map_nil]
    rfl

/-- The queries of the encoded expansion are the encoded queries of `X` against `h ∘ ι`. -/
theorem queries_map (ι : A → A') (h : A' → B) {k : ℕ} (i : Fin k) :
    (X.map ι).queries h c i = ι (X.queries (h ∘ ι) c i) := by
  simp only [queries, run_map, List.getElem_map]

/-- The output of the encoded expansion is the output of `X` against `h ∘ ι` with its queries
encoded by `ι`. -/
theorem expand_map (ι : A → A') (h : A' → B) {k : ℕ} :
    ((X.map ι).expand h c : BaseGame.Tuple A' B C k) =
      ⟨ι ∘ (X.expand (h ∘ ι) c (k := k)).queries, (X.expand (h ∘ ι) c (k := k)).answers, c⟩ := by
  have hq : ((X.map ι).queries h c : Fin k → A') = ι ∘ X.queries (h ∘ ι) c :=
    funext (X.queries_map c ι h)
  rw [expand, expand, hq]
  rfl

end Expansion

/-! ### Classical oracle programs as expansions -/

namespace OracleProg

variable {A B R S ι : Type*} (h : A → B)

/-- The expansion that runs the program `P c` on the input `c`, then queries `pad`. -/
def _root_.GordieHowe.OracleProg.toExpansion {C : Type*} (P : C → GordieHowe.OracleProg A B R) (pad : A) : Expansion A B C :=
  ⟨fun c ans => (P c).next pad ans⟩

/-- **The queries of a program's expansion** are the program's queries, padded with `pad`
(and truncated to `k`). -/
theorem _root_.GordieHowe.OracleProg.queries_toExpansion {C : Type*} (P : C → GordieHowe.OracleProg A B R) (pad : A) (c : C) {k : ℕ}
    (i : Fin k) : (GordieHowe.OracleProg.toExpansion P pad).queries h c i = (((P c).trace h)[i.1]?).getD pad :=
  Expansion.queries_eq_of_next (f := (P c).paddedTrace h pad) (GordieHowe.OracleProg.toExpansion P pad) h c
    ((P c).paddedTrace_eq_next h pad) i

/-- **Every query of a program within the first `k` is in the expanded tuple**, with its
answer. -/
theorem _root_.GordieHowe.OracleProg.mem_expand_toExpansion {C : Type*} (P : C → GordieHowe.OracleProg A B R) (pad : A) (c : C) {k : ℕ}
    (hk : ((P c).trace h).length ≤ k) {x : A} (hx : x ∈ (P c).trace h) :
    ∃ i : Fin k, ((GordieHowe.OracleProg.toExpansion P pad).expand h c).queries i = x ∧
      ((GordieHowe.OracleProg.toExpansion P pad).expand h c).answers i = h x := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  refine ⟨⟨j, by omega⟩, ?_, ?_⟩ <;>
    simp [Expansion.expand, GordieHowe.OracleProg.queries_toExpansion, List.getElem?_eq_getElem hj]

end OracleProg

/-! ### Adaptive fresh queries to a uniform oracle -/

section Fresh

variable {A B : Type*}

/-- **The answers of an adaptive query strategy** `q` against the oracle `h`: query `i` is
`q i ans h`, where `ans` lists the answers to the queries before it. -/
def ansList (q : ℕ → List B → (A → B) → A) (h : A → B) : ℕ → List B
  | 0 => []
  | m + 1 => ansList q h m ++ [h (q m (ansList q h m) h)]

/-- The first `m` queries of the strategy `q` against `h`. -/
def qryList (q : ℕ → List B → (A → B) → A) (h : A → B) (m : ℕ) : List A :=
  (List.range m).map fun i => q i (ansList q h i) h

variable (q : ℕ → List B → (A → B) → A) (h : A → B)

@[simp]
theorem length_ansList : ∀ m, (ansList q h m).length = m
  | 0 => rfl
  | m + 1 => by simp [ansList, length_ansList m]

theorem ansList_succ (m : ℕ) : ansList q h (m + 1) = ansList q h m ++ [h (q m (ansList q h m) h)] :=
  rfl

theorem qryList_succ (m : ℕ) :
    qryList q h (m + 1) = qryList q h m ++ [q m (ansList q h m) h] := by
  simp [qryList, List.range_succ]

/-- The answers to the first `m` queries are a prefix of the answers to the first `m'`. -/
theorem take_ansList {m m' : ℕ} (hm : m ≤ m') : (ansList q h m').take m = ansList q h m := by
  induction m', hm using Nat.le_induction with
  | base => simp
  | succ m' hm ih =>
    rw [ansList_succ, List.take_append_of_le_length (by simp; omega), ih]

/-- Answer `i` of the first `m > i` answers is the oracle at query `i`. -/
theorem getElem_ansList {m i : ℕ} (hi : i < m) :
    (ansList q h m)[i]'(by simp; omega) = h (q i (ansList q h i) h) := by
  have h1 := congrArg (fun l => l[i]?) (take_ansList q h (Nat.succ_le_of_lt hi))
  simp only [List.getElem?_take, show i < i + 1 from Nat.lt_succ_self i, if_true] at h1
  rw [ansList_succ, List.getElem?_append_right (by simp)] at h1
  simp only [length_ansList, Nat.sub_self, List.getElem?_cons_zero] at h1
  rw [List.getElem?_eq_getElem (by simp; omega)] at h1
  exact Option.some_inj.1 h1

/-- Two strategies that agree at the oracle `h` give the same answers against `h`. -/
theorem ansList_congr_fun {q' : ℕ → List B → (A → B) → A} (hq : ∀ i l, q i l h = q' i l h) :
    ∀ m, ansList q h m = ansList q' h m
  | 0 => rfl
  | m + 1 => by rw [ansList_succ, ansList_succ, ansList_congr_fun hq m, hq]

/-- Two oracles that agree on a set `Dom` containing every query give the same answers, when the
strategy's queries are the same under both oracles. -/
theorem ansList_congr_oracle {Dom : A → Prop} {h' : A → B} {m : ℕ}
    (hdom : ∀ i < m, ∀ l, Dom (q i l h)) (hq : ∀ i l, q i l h = q i l h')
    (hh : ∀ a, Dom a → h a = h' a) : ansList q h m = ansList q h' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [ansList_succ, ansList_succ, ih fun i hi => hdom i (by omega), ← hq,
      hh _ (hdom _ (by omega) _)]

variable {q} [DecidableEq A]

/-- Changing the oracle at a point `v` of `Dom` that none of the first `i` queries hits does not
change the first `i` answers, when the queries depend on the oracle only off `Dom`. -/
theorem ansList_update {Dom : A → Prop}
    (hloc : ∀ i l h h', (∀ a, ¬ Dom a → h a = h' a) → q i l h = q i l h') {v : A} (hv : Dom v)
    (b : B) : ∀ i, (∀ j < i, q j (ansList q h j) h ≠ v) →
      ansList q (Function.update h v b) i = ansList q h i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := ansList_update hloc hv b i fun j hj => hi j (Nat.lt_succ_of_lt hj)
    rw [ansList_succ, ansList_succ, ih]
    have hq : q i (ansList q h i) (Function.update h v b) = q i (ansList q h i) h :=
      hloc _ _ _ _ fun a ha => Function.update_of_ne (fun e => ha (by rw [e]; exact hv)) _ _
    rw [hq, Function.update_of_ne (hi i (Nat.lt_succ_self i))]

variable [Fintype A] [Fintype B] [DecidableEq B]

open Classical in
/-- **Adaptive fresh queries, counting form**: if every query of `q` lies in `Dom` and depends on
the oracle only off `Dom`, the oracles on which the first `m` queries are distinct and their
answers lie in `S` number at most `|S| · |B|^|A| / |B|^m`. -/
theorem card_nodup_ansList_mem_le {Dom : A → Prop} (hdom : ∀ i l h, Dom (q i l h))
    (hloc : ∀ i l h h', (∀ a, ¬ Dom a → h a = h' a) → q i l h = q i l h') :
    ∀ (m : ℕ) (S : Finset (List B)),
      (Finset.univ.filter fun h : A → B => (qryList q h m).Nodup ∧ ansList q h m ∈ S).card *
        Fintype.card B ^ m ≤ S.card * Fintype.card (A → B)
  | 0, S => by
    by_cases h0 : ([] : List B) ∈ S
    · rw [pow_zero, mul_one]
      calc _ ≤ Fintype.card (A → B) := (Finset.card_filter_le _ _).trans (by simp)
        _ ≤ _ := Nat.le_mul_of_pos_left _ (Finset.card_pos.2 ⟨_, h0⟩)
    · simp [ansList, h0]
  | m + 1, S => by
    -- the query `m` and the sets of answer prefixes completed by `b`
    let Q : (A → B) → A := fun h => q m (ansList q h m) h
    let T : B → Finset (List B) := fun b => (S.filter fun l => l.getLast? = some b).image
      List.dropLast
    let F : B → Finset (A → B) := fun b => Finset.univ.filter fun h =>
      (qryList q h m).Nodup ∧ Q h ∉ qryList q h m ∧ ansList q h m ∈ T b
    let G : B → B → Finset (A → B) := fun b b' => (F b).filter fun h => h (Q h) = b'
    -- the update at the fresh query moves `G b b'` into `G b b''`
    have hupd : ∀ b b' b'' h, h ∈ G b b' → Function.update h (Q h) b'' ∈ G b b'' ∧
        Q (Function.update h (Q h) b'') = Q h := by
      intro b b' b'' h hh
      simp only [G, F, Finset.mem_filter, Finset.mem_univ, true_and] at hh
      obtain ⟨⟨hnd, hfr, hT⟩, -⟩ := hh
      have hfr' : ∀ j < m, q j (ansList q h j) h ≠ Q h := fun j hj he =>
        hfr (List.mem_map.2 ⟨j, List.mem_range.2 hj, he⟩)
      have hans : ∀ i ≤ m, ansList q (Function.update h (Q h) b'') i = ansList q h i :=
        fun i hi => ansList_update h hloc (hdom _ _ _) b'' i fun j hj => hfr' j (by omega)
      have hqry : qryList q (Function.update h (Q h) b'') m = qryList q h m := by
        refine List.map_congr_left fun j hj => ?_
        have hj' := List.mem_range.1 hj
        rw [hans j hj'.le]
        exact hloc _ _ _ _ fun a ha => Function.update_of_ne (fun e => ha (by rw [e]; exact hdom _ _ _)) _ _
      have hQ : Q (Function.update h (Q h) b'') = Q h := by
        change q m (ansList q _ m) _ = q m (ansList q h m) h
        rw [hans m le_rfl]
        exact hloc _ _ _ _ fun a ha => Function.update_of_ne (fun e => ha (by rw [e]; exact hdom _ _ _)) _ _
      refine ⟨?_, hQ⟩
      simp only [G, F, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hqry, hans m le_rfl, hQ, Function.update_self]
      exact ⟨⟨hnd, hfr, hT⟩, rfl⟩
    have hGle : ∀ b b' b'', (G b b').card ≤ (G b b'').card := by
      intro b b' b''
      refine Finset.card_le_card_of_injOn (fun h => Function.update h (Q h) b'')
        (fun h hh => (hupd b b' b'' h hh).1) ?_
      intro h₁ h₁m h₂ h₂m he
      have hQ₁ := (hupd b b' b'' h₁ h₁m).2
      have hQ₂ := (hupd b b' b'' h₂ h₂m).2
      simp only at he
      have hQ : Q h₁ = Q h₂ := by rw [← hQ₁, ← hQ₂, he]
      have hb₁ : h₁ (Q h₁) = b' := (Finset.mem_filter.1 h₁m).2
      have hb₂ : h₂ (Q h₂) = b' := (Finset.mem_filter.1 h₂m).2
      funext a
      by_cases ha : a = Q h₁
      · rw [ha, hb₁, hQ, hb₂]
      · have := congrFun he a
        rwa [Function.update_of_ne ha, Function.update_of_ne (hQ ▸ ha)] at this
    -- each `G b b` is a `1/|B|` share of `F b`
    have hF : ∀ b, (G b b).card * Fintype.card B = (F b).card := by
      intro b
      have hall : ∀ b', (G b b').card = (G b b).card := fun b' =>
        le_antisymm (hGle b b' b) (hGle b b b')
      calc (G b b).card * Fintype.card B = ∑ b' : B, (G b b').card := by
            simp [hall, Finset.sum_const, mul_comm]
        _ = (F b).card := (Finset.card_eq_sum_card_fiberwise
            (f := fun g : A → B => g (Q g)) (s := F b) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)).symm
    -- the event is covered by the `G b b`
    have hcover : (Finset.univ.filter fun h : A → B =>
        (qryList q h (m + 1)).Nodup ∧ ansList q h (m + 1) ∈ S) ⊆
          Finset.univ.biUnion fun b => G b b := by
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
      obtain ⟨hnd', hS⟩ := hh
      rw [qryList_succ] at hnd'
      obtain ⟨hnd, -, hfr⟩ := List.nodup_append.1 hnd'
      rw [ansList_succ] at hS
      refine Finset.mem_biUnion.2 ⟨h (Q h), Finset.mem_univ _, ?_⟩
      simp only [G, F, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      refine ⟨hnd, fun hm => hfr _ hm _ (List.mem_singleton_self _) rfl, ?_⟩
      exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨hS, by simp [Q]⟩, by simp⟩
    -- the prefix sets `T b` are disjoint images of parts of `S`
    have hT : ∑ b, (T b).card ≤ S.card := by
      calc ∑ b, (T b).card ≤ ∑ b, (S.filter fun l => l.getLast? = some b).card :=
            Finset.sum_le_sum fun b _ => Finset.card_image_le
        _ ≤ S.card := by
          rw [← Finset.card_biUnion]
          · exact Finset.card_le_card (Finset.biUnion_subset.2 fun _ _ => Finset.filter_subset _ _)
          · intro b _ b' _ hbb'
            refine Finset.disjoint_left.2 fun l h1 h2 => hbb' ?_
            exact Option.some_inj.1 ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
    calc _ ≤ (Finset.univ.biUnion fun b => G b b).card * Fintype.card B ^ (m + 1) :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hcover)
      _ ≤ (∑ b, (G b b).card) * Fintype.card B ^ (m + 1) :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ b, (F b).card * Fintype.card B ^ m := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← hF b, pow_succ]
          ring
      _ ≤ ∑ b, (T b).card * Fintype.card (A → B) := by
          refine Finset.sum_le_sum fun b _ => le_trans (Nat.mul_le_mul_right _
            (Finset.card_le_card ?_)) (card_nodup_ansList_mem_le hdom hloc m (T b))
          intro h hh
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
          exact ⟨hh.1, hh.2.2⟩
      _ ≤ S.card * Fintype.card (A → B) := by
          rw [← Finset.sum_mul]
          exact Nat.mul_le_mul_right _ hT

open GordieHowe.IOP in
open Classical in
/-- **Adaptive fresh queries** (lazy sampling): if every query of the strategy `q` lies in `Dom`
and depends on the oracle only off `Dom`, then for a uniform oracle the probability that the first
`m` queries are distinct and their answers lie in `S` is at most `|S| / |B|^m`, the probability
of `S` under uniform independent answers. -/
theorem prob_nodup_ansList_mem_le [Nonempty B] {Dom : A → Prop} (hdom : ∀ i l h, Dom (q i l h))
    (hloc : ∀ i l h h', (∀ a, ¬ Dom a → h a = h' a) → q i l h = q i l h') (m : ℕ)
    (S : Finset (List B)) :
    Pr[h ← (A → B) : (qryList q h m).Nodup ∧ ansList q h m ∈ S] ≤
      (S.card : ENNReal) / (Fintype.card B : ENNReal) ^ m := by
  rw [IOP.probUniform_eq_card_div]
  have hc := card_nodup_ansList_mem_le hdom hloc m S
  have hB : (Fintype.card B : ENNReal) ^ m ≠ 0 := pow_ne_zero _ (by simp)
  have hN : (Fintype.card (A → B) : ENNReal) ≠ 0 := by simp
  have hBt : (Fintype.card B : ENNReal) ^ m ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  calc _ = ((Finset.univ.filter fun h : A → B => (qryList q h m).Nodup ∧ ansList q h m ∈ S).card *
        (Fintype.card B : ENNReal) ^ m) / (Fintype.card (A → B) * (Fintype.card B : ENNReal) ^ m) :=
        (ENNReal.mul_div_mul_right _ _ hB hBt).symm
    _ ≤ (S.card * Fintype.card (A → B) : ENNReal) /
        (Fintype.card (A → B) * (Fintype.card B : ENNReal) ^ m) :=
        ENNReal.div_le_div_right (by exact_mod_cast hc) _
    _ = _ := by rw [mul_comm (Fintype.card (A → B) : ENNReal),
        ENNReal.mul_div_mul_right _ _ hN (by simp)]

omit [Fintype A] [Fintype B] [DecidableEq B] in
/-- If the first `m` queries repeat, some query `j < m` is the first repeat: the queries before
it are distinct and it is one of them. -/
theorem exists_first_dup : ∀ m, ¬ (qryList q h m).Nodup →
    ∃ j < m, (qryList q h j).Nodup ∧ q j (ansList q h j) h ∈ qryList q h j
  | 0, hn => absurd List.nodup_nil hn
  | m + 1, hn => by
    by_cases hm : (qryList q h m).Nodup
    · refine ⟨m, Nat.lt_succ_self m, hm, ?_⟩
      by_contra hnm
      rw [qryList_succ] at hn
      refine hn (List.nodup_append.2 ⟨hm, List.nodup_singleton _, fun a ha b hb => ?_⟩)
      rw [List.mem_singleton] at hb
      subst hb
      exact fun he => hnm (he ▸ ha)
    · obtain ⟨j, hj, h1, h2⟩ := exists_first_dup m hm
      exact ⟨j, by omega, h1, h2⟩

open GordieHowe.IOP in
open Classical in
/-- **Adaptive fresh queries, vector form**: under the hypotheses of `prob_nodup_ansList_mem_le`,
the probability that the first `m` queries are distinct and their answers satisfy `G` is at most
the probability of `G` for uniform independent answers. -/
theorem prob_nodup_ansList_le [Nonempty B] {Dom : A → Prop} (hdom : ∀ i l h, Dom (q i l h))
    (hloc : ∀ i l h h', (∀ a, ¬ Dom a → h a = h' a) → q i l h = q i l h') (m : ℕ)
    (G : (Fin m → B) → Prop) :
    Pr[h ← (A → B) : (qryList q h m).Nodup ∧ G fun j => (ansList q h m)[j.1]'(by simp)] ≤
      Pr[a ← (Fin m → B) : G a] := by
  let S : Finset (List B) := (Finset.univ.filter G).image List.ofFn
  calc _ ≤ Pr[h ← (A → B) : (qryList q h m).Nodup ∧ ansList q h m ∈ S] := by
        refine MeasureTheory.measure_mono fun h hh =>
          ⟨hh.1, Finset.mem_image.2 ⟨_, by simpa using hh.2, ?_⟩⟩
        exact List.ext_getElem (by simp) fun i _ _ => by simp
    _ ≤ (S.card : ENNReal) / (Fintype.card B : ENNReal) ^ m := prob_nodup_ansList_mem_le hdom hloc m S
    _ ≤ _ := by
        rw [IOP.probUniform_eq_card_div, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        exact ENNReal.div_le_div_right (by exact_mod_cast Finset.card_image_le) _

end Fresh

end GordieHowe.QROM

namespace GordieHowe.QROM.Expansion

variable {A B C C' : Type*}

/-- **Expansions with the same next queries on two inputs make the same queries on them.** -/
theorem run_eq_of_next_eq {X : Expansion A B C} {X' : Expansion A B C'} (h : A → B) {c : C}
    {c' : C'} (hn : ∀ ans, X'.next c' ans = X.next c ans) : ∀ i, X'.run h c' i = X.run h c i
  | 0 => rfl
  | i + 1 => by
    rw [run, run, run_eq_of_next_eq h hn i, hn]

theorem queries_eq_of_next_eq {X : Expansion A B C} {X' : Expansion A B C'} (h : A → B) {c : C}
    {c' : C'} (hn : ∀ ans, X'.next c' ans = X.next c ans) {k : ℕ} (i : Fin k) :
    X'.queries h c' i = X.queries h c i := by
  simp only [queries, run_eq_of_next_eq h hn]

end GordieHowe.QROM.Expansion
