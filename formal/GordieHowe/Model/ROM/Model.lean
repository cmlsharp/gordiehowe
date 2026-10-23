-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Instability
public import GordieHowe.Model.QROM.Expansion

@[expose] public section

/-!
# The classical random-oracle model

The classical counterpart of the quantum model of `GordieHowe/Model/QROM/Lifting.lean`: the oracle is a
uniformly random function `h : A → B` on a finite domain (CY24 Definition 2.1.1, p. 20; BCS16
section 2.1, p. 12), and an adversary is a classical oracle algorithm making at most `t` queries
(CY24 p. 20, "an oracle algorithm `A` is `t`-query if `A` makes at most `t` queries"; BCS16
section 2.1, p. 12; CMS19 Definition 4.1, p. 18, the class `C_t`). The query log of a run, the
table of its queries and their answers kept by a lazily sampled oracle (CY24 section 2.2, p. 22;
CMS19 footnote 5, p. 18), is a database `DB A B` (`GordieHowe/Model/QROM/Database.lean`), the
object CMS19's database properties and their flip probabilities (`GordieHowe/Model/QROM/Instability.lean`,
CMS19 section 5) are stated about.

- `Alg A B C t`: a deterministic classical oracle algorithm that makes `t` queries, each computed
  from the answers to the earlier ones (`next`), then outputs `out` of all the answers. Fixing
  exactly `t` queries loses no generality: an algorithm with fewer queries is padded with further
  queries (a repeated one, or a fresh dummy query when it made none) whose answers `out` ignores;
  a dummy query does enter the log, and every bound holds for every `t`-query `Alg`.
- `Alg.queries`, `Alg.output`, `Alg.log`: its queries, output and query log against `h`.
- `Adversary A B C t`: a randomized classical `t`-query algorithm, a law on coins independent of
  the oracle and a deterministic algorithm for each value of the coins.
- `Alg.append`: the algorithm followed by an expansion (`Expansion`, the shape of CMS19's
  `BCSExpand`, p. 39) on its output, the classical expanded adversary of CMS19 Proposition 8.11
  (p. 42).

What is proved:
- **Lazy sampling at a fresh query** (`prob_step_le`): the answer to a query outside the log so
  far is uniform and independent of the run so far, so the step that records it moves the log
  from outside a property `R` into `R` with probability at most `flip(R̄ → R, t)` (CMS19
  Definition 5.4, p. 21). The proof resamples the oracle at that query (`resample`, an involution
  of `(A → B) × B` that preserves the uniform law); the run up to the query reads the oracle only
  on the log (`queries_update`).
- **The classical measured-database bound** (`prob_log_mem_le`): for `∅ ∉ R`,
  `Pr[log ∈ R] ≤ t · flip(R̄ → R, t)`, by a union bound over the `t` steps. It is the classical
  counterpart of CMS19 Lemmas 5.9 and 5.10 (`Pr[D ∈ R] ≤ 6 t² I(R, t)`, `Lifting.measured_le`);
  CMS19 footnote 6 (p. 22) states the classical bound `t · I(P, t)`.
-/

namespace GordieHowe.ROM

open GordieHowe.QROM GordieHowe.IOP
open scoped ENNReal

/-! ### Classical oracle algorithms -/

/-- **A deterministic classical oracle algorithm making `t` queries** with queries in `A`,
answers in `B` and output in `C` (CMS19 Definition 4.1, p. 18: `C_t`, "classical algorithms that
make at most `t` queries to an oracle"): query `i` is `next ans` on the answers `ans` to the
queries before it, and the output is `out` of the `t` answers. An algorithm with fewer queries is
padded to `t` with queries whose answers `out` ignores (a repeated query records nothing new; a
fresh dummy query, needed when it made none, enters the log), so fixing `t` loses no generality.
-/
structure Alg (A B C : Type*) (t : ℕ) where
  /-- The next query, from the answers to the earlier queries. -/
  next : List B → A
  /-- The output, from the answers to the `t` queries. -/
  out : List B → C

/-- **A randomized classical `t`-query adversary**: coins drawn from the law `coins`, independently
of the oracle, then the deterministic algorithm `alg c`. -/
structure Adversary (A B C : Type) (t : ℕ) where
  /-- The coins. -/
  Coins : Type
  /-- The law of the coins. -/
  coins : PMF Coins
  /-- The algorithm at each value of the coins. -/
  alg : Coins → Alg A B C t

namespace Adversary

variable {A B C : Type} {t : ℕ} (𝒜 : Adversary A B C t)

/-- An average over the coins of bounds `x r ≤ y r + c` is a bound `∑ x ≤ ∑ y + c`. -/
theorem tsum_le_tsum_add {x y : 𝒜.Coins → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ r, x r ≤ y r + c) :
    ∑' r, 𝒜.coins r * x r ≤ ∑' r, 𝒜.coins r * y r + c := by
  calc ∑' r, 𝒜.coins r * x r ≤ ∑' r, (𝒜.coins r * y r + 𝒜.coins r * c) :=
        ENNReal.tsum_le_tsum fun r => by rw [← mul_add]; gcongr; exact h r
    _ = ∑' r, 𝒜.coins r * y r + c := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Adversary

/-! ### Query logs -/

section Log

variable {A B : Type*} [DecidableEq A]

/-- **The query log of the queries `l` against `h`**: the database recording `h a` at every
`a ∈ l` (the list of query-answer pairs of a lazily sampled oracle, CY24 section 2.2, p. 22). -/
def logOf (h : A → B) : List A → DB A B
  | [] => ∅
  | a :: l => (logOf h l).extend a (h a)

theorem lookup_logOf (h : A → B) (l : List A) (x : A) :
    (logOf h l).lookup x = if x ∈ l then some (h x) else none := by
  induction l with
  | nil => simp [logOf]
  | cons a l ih =>
    by_cases hxa : x = a
    · subst hxa
      simp [logOf, DB.lookup_extend_self]
    · rw [logOf, DB.lookup_extend_of_ne hxa, ih]
      simp [hxa]

theorem mem_logOf {h : A → B} {l : List A} {x : A} : x ∈ logOf h l ↔ x ∈ l := by
  rw [DB.mem_iff_lookup, lookup_logOf]
  by_cases hx : x ∈ l <;> simp [hx]

theorem lookup_logOf_of_mem {h : A → B} {l : List A} {x : A} (hx : x ∈ l) :
    (logOf h l).lookup x = some (h x) := by
  simp [lookup_logOf, hx]

theorem logOf_nil (h : A → B) : logOf h [] = ∅ := rfl

theorem size_logOf_le (h : A → B) (l : List A) : (logOf h l).size ≤ l.length := by
  induction l with
  | nil => simp [logOf, DB.size]
  | cons a l ih =>
    exact DB.size_extend_le.trans (by simp only [List.length_cons]; omega)

/-- Logs with the same lookups are equal. -/
theorem logOf_eq_of_lookup {h h' : A → B} {l l' : List A}
    (H : ∀ x, (logOf h l).lookup x = (logOf h' l').lookup x) : logOf h l = logOf h' l' :=
  Finmap.ext_lookup H

/-- Appending a query already in the list leaves the log unchanged. -/
theorem logOf_append_of_mem {h : A → B} {l : List A} {a : A} (ha : a ∈ l) :
    logOf h (l ++ [a]) = logOf h l :=
  logOf_eq_of_lookup fun x => by
    rw [lookup_logOf, lookup_logOf]
    by_cases hx : x ∈ l
    · simp [hx]
    · have : x ≠ a := fun e => hx (e ▸ ha)
      simp [hx, this]

/-- Appending a query records its answer. -/
theorem logOf_append (h : A → B) (l : List A) (a : A) :
    logOf h (l ++ [a]) = (logOf h l).extend a (h a) :=
  Finmap.ext_lookup fun x => by
    by_cases hxa : x = a
    · subst hxa
      rw [DB.lookup_extend_self, lookup_logOf_of_mem (by simp)]
    · rw [DB.lookup_extend_of_ne hxa, lookup_logOf, lookup_logOf]
      simp [hxa]

/-- Changing the oracle off the queries does not change the log. -/
theorem logOf_update {h : A → B} {l : List A} {v : A} (hv : v ∉ l) (y : B) :
    logOf (Function.update h v y) l = logOf h l :=
  logOf_eq_of_lookup fun x => by
    rw [lookup_logOf, lookup_logOf]
    by_cases hx : x ∈ l
    · have : x ≠ v := fun e => hv (e ▸ hx)
      simp [hx, Function.update_of_ne this]
    · simp [hx]

end Log

namespace Alg

variable {A B C : Type*} {t : ℕ}

/-- The first `i` queries of `𝒜` against `h`. -/
def queries (𝒜 : Alg A B C t) (h : A → B) : ℕ → List A
  | 0 => []
  | i + 1 => queries 𝒜 h i ++ [𝒜.next ((queries 𝒜 h i).map h)]

variable (𝒜 : Alg A B C t) (h : A → B)

@[simp]
theorem length_queries : ∀ i, (𝒜.queries h i).length = i
  | 0 => rfl
  | i + 1 => by simp [queries, length_queries i]

/-- Query `i` of `𝒜` against `h`, from the answers to the first `i`. -/
def queryAt (i : ℕ) : A := 𝒜.next ((𝒜.queries h i).map h)

theorem queries_succ (i : ℕ) : 𝒜.queries h (i + 1) = 𝒜.queries h i ++ [𝒜.queryAt h i] := rfl

/-- **The output of `𝒜` against `h`**: `out` of the answers to its `t` queries. -/
def output : C := 𝒜.out ((𝒜.queries h t).map h)

variable [DecidableEq A]

/-- **The query log of `𝒜` after `i` queries against `h`**. -/
def log (i : ℕ) : DB A B := logOf h (𝒜.queries h i)

theorem log_zero : 𝒜.log h 0 = ∅ := rfl

theorem size_log_le (i : ℕ) : (𝒜.log h i).size ≤ i :=
  (size_logOf_le h _).trans (by simp)

variable {𝒜 h}

/-- **The run up to step `j` reads the oracle only on its queries**: changing `h` at a point `v`
that none of the first `j` queries hits does not change them. -/
theorem queries_update {v : A} (y : B) :
    ∀ {j}, v ∉ 𝒜.queries h j → 𝒜.queries (Function.update h v y) j = 𝒜.queries h j
  | 0, _ => rfl
  | j + 1, hv => by
    rw [queries_succ, List.mem_append, not_or] at hv
    have ih := queries_update y hv.1
    have hmap : (𝒜.queries h j).map (Function.update h v y) = (𝒜.queries h j).map h :=
      List.map_congr_left fun x hx => Function.update_of_ne (fun (e : x = v) => hv.1 (e ▸ hx)) _ _
    rw [queries_succ, queries_succ, queryAt, queryAt, ih, hmap]

theorem queryAt_update {v : A} (y : B) {j : ℕ} (hv : v ∉ 𝒜.queries h j) :
    𝒜.queryAt (Function.update h v y) j = 𝒜.queryAt h j := by
  have hmap : (𝒜.queries h j).map (Function.update h v y) = (𝒜.queries h j).map h :=
    List.map_congr_left fun x hx => Function.update_of_ne (fun (e : x = v) => hv (e ▸ hx)) _ _
  rw [queryAt, queryAt, queries_update y hv, hmap]

/-! ### Lazy sampling at a fresh query -/

variable (𝒜) (j : ℕ)

/-- **Resampling the oracle at query `j`**: when query `j` is not among the earlier queries, the
oracle's value there is replaced by `y` and the old value returned in place of `y`; otherwise
nothing changes. It is an involution (`resample_involutive`), so it preserves the uniform law on
`(A → B) × B`. -/
def resample (p : (A → B) × B) : (A → B) × B :=
  if 𝒜.queryAt p.1 j ∈ 𝒜.queries p.1 j then p
  else (Function.update p.1 (𝒜.queryAt p.1 j) p.2, p.1 (𝒜.queryAt p.1 j))

theorem resample_involutive : Function.Involutive (𝒜.resample j) := by
  rintro ⟨h, y⟩
  by_cases hq : 𝒜.queryAt h j ∈ 𝒜.queries h j
  · simp only [resample, hq, ite_true]
  · have hq' : 𝒜.queryAt (Function.update h (𝒜.queryAt h j) y) j = 𝒜.queryAt h j :=
      queryAt_update y hq
    have hs : 𝒜.queries (Function.update h (𝒜.queryAt h j) y) j = 𝒜.queries h j :=
      queries_update y hq
    simp only [resample, hq, ite_false, hq', hs, Function.update_idem, Function.update_eq_self,
      Function.update_self]

/-- **One step moves the log into `R`** with probability at most `flip(R̄ → R, t)` (CMS19
Definition 5.4, p. 21), for a step `j < t`: a query already in the log adds nothing, and the answer
to a fresh query is uniform and independent of the run so far (`resample`). -/
theorem prob_step_le [Fintype A] [Fintype B] [Nonempty B] {R : Set (DB A B)} (hj : j < t) :
    Pr[h ← (A → B) : 𝒜.log h j ∉ R ∧ 𝒜.log h (j + 1) ∈ R] ≤ flipProb Rᶜ R t := by
  classical
  set F : (A → B) → Prop := fun h => 𝒜.log h j ∉ R ∧ 𝒜.log h (j + 1) ∈ R
  set G : (A → B) × B → Prop := fun p =>
    𝒜.queryAt p.1 j ∉ 𝒜.queries p.1 j ∧ 𝒜.log p.1 j ∉ R ∧
      (𝒜.log p.1 j).extend (𝒜.queryAt p.1 j) p.2 ∈ R
  have hFG : ∀ p, F (𝒜.resample j p).1 → G p := by
    rintro ⟨h, y⟩ hF
    by_cases hq : 𝒜.queryAt h j ∈ 𝒜.queries h j
    · simp only [resample, hq, ite_true, F] at hF
      have h1 : 𝒜.log h (j + 1) = 𝒜.log h j := logOf_append_of_mem hq
      exact absurd (h1 ▸ hF.2) hF.1
    · simp only [resample, hq, ite_false, F] at hF
      have hs : 𝒜.queries (Function.update h (𝒜.queryAt h j) y) j = 𝒜.queries h j :=
        queries_update y hq
      have hq' : 𝒜.queryAt (Function.update h (𝒜.queryAt h j) y) j = 𝒜.queryAt h j :=
        queryAt_update y hq
      have e1 : 𝒜.log (Function.update h (𝒜.queryAt h j) y) j = 𝒜.log h j := by
        change logOf _ (𝒜.queries _ j) = logOf h (𝒜.queries h j)
        rw [hs, logOf_update hq]
      have e2 : 𝒜.log (Function.update h (𝒜.queryAt h j) y) (j + 1) =
          (𝒜.log h j).extend (𝒜.queryAt h j) y := by
        change logOf _ (𝒜.queries _ j ++ [𝒜.queryAt _ j]) = (logOf h (𝒜.queries h j)).extend _ y
        rw [hs, hq', logOf_append, logOf_update hq, Function.update_self]
      rw [e1, e2] at hF
      exact ⟨hq, hF.1, hF.2⟩
  have hstep : ∀ h, Pr[y ← B : G (h, y)] ≤ flipProb Rᶜ R t := by
    intro h
    by_cases hG : 𝒜.queryAt h j ∉ 𝒜.queries h j ∧ 𝒜.log h j ∉ R
    · have hmem : 𝒜.queryAt h j ∉ 𝒜.log h j := by
        rw [log, mem_logOf]
        exact hG.1
      calc Pr[y ← B : G (h, y)]
          ≤ Pr[y ← B : (𝒜.log h j).extend (𝒜.queryAt h j) y ∈ R] :=
            QROM.probUniform_mono fun y hy => hy.2.2
        _ ≤ flipProb Rᶜ R t := le_flipProb hG.2 ((𝒜.size_log_le h j).trans_lt hj) hmem
    · exact le_of_eq_of_le (probUniform_eq_zero fun y hy => hG ⟨hy.1, hy.2.1⟩) zero_le
  let e : (A → B) × B ≃ (A → B) × B := (resample_involutive 𝒜 j).toPerm _
  calc Pr[h ← (A → B) : F h]
      = Pr[p ← (A → B) × B : F p.1] := (QROM.probUniform_prod_fst F).symm
    _ = Pr[p ← (A → B) × B : F (e p).1] := (QROM.probUniform_equiv e fun p => F p.1).symm
    _ ≤ Pr[p ← (A → B) × B : G p] := QROM.probUniform_mono hFG
    _ = Pr[p ← B × (A → B) : G (Equiv.prodComm B (A → B) p)] :=
        (QROM.probUniform_equiv (Equiv.prodComm B (A → B)) G).symm
    _ ≤ flipProb Rᶜ R t := QROM.probUniform_prod_le _ fun h => hstep h

/-- A property false at `0` and true at `n` turns true at some step below `n`. -/
theorem exists_step_of {P : ℕ → Prop} (h0 : ¬ P 0) :
    ∀ {n}, P n → ∃ j < n, ¬ P j ∧ P (j + 1)
  | 0, hn => absurd hn h0
  | n + 1, hn => by
    by_cases hP : P n
    · obtain ⟨j, hj, h⟩ := exists_step_of h0 hP
      exact ⟨j, by omega, h⟩
    · exact ⟨n, by omega, hP, hn⟩

/-- **The classical measured-database bound**: for a property `R` that the empty database does
not have, the log of a `t`-query algorithm lies in `R` with probability at most
`t · flip(R̄ → R, t)`. The classical counterpart of CMS19 Lemmas 5.9 and 5.10
(`Lifting.measured_le`, `Pr[D ∈ R] ≤ 6 t² I(R, t)`): the log starts empty, and each of the `t`
steps moves it into `R` with probability at most `flip(R̄ → R, t)` (`prob_step_le`). -/
theorem prob_log_mem_le [Fintype A] [Fintype B] [Nonempty B] {R : Set (DB A B)}
    (hR : (∅ : DB A B) ∉ R) :
    Pr[h ← (A → B) : 𝒜.log h t ∈ R] ≤ t * flipProb Rᶜ R t := by
  calc Pr[h ← (A → B) : 𝒜.log h t ∈ R]
      ≤ Pr[h ← (A → B) : ∃ j : Fin t, 𝒜.log h j ∉ R ∧ 𝒜.log h (j + 1) ∈ R] :=
        QROM.probUniform_mono fun h hh => by
          obtain ⟨j, hj, h1, h2⟩ := exists_step_of (P := fun i => 𝒜.log h i ∈ R)
            (by rw [log_zero]; exact hR) hh
          exact ⟨⟨j, hj⟩, h1, h2⟩
    _ ≤ ∑ j : Fin t, Pr[h ← (A → B) : 𝒜.log h j ∉ R ∧ 𝒜.log h (j + 1) ∈ R] :=
        probUniform_exists_le _
    _ ≤ ∑ _j : Fin t, flipProb Rᶜ R t :=
        Finset.sum_le_sum fun j _ => 𝒜.prob_step_le j j.2
    _ = t * flipProb Rᶜ R t := by simp

end Alg

/-! ### The flip probability into a union -/

section Union

variable {X Y : Type*} [DecidableEq X] [Fintype Y] [Nonempty Y] {P Q : Set (DB X Y)} {t : ℕ}

/-- `flip(\overline{P ∪ Q} → P ∪ Q, t) ≤ flip(P | Q̄, t) + flip(Q̄ → Q, t)`, the first half of
CMS19 Proposition 5.12 (3) (p. 24). -/
theorem flipProb_compl_union_le :
    flipProb (P ∪ Q)ᶜ (P ∪ Q) t ≤ condFlip P Qᶜ t + flipProb Qᶜ Q t := by
  have hsplit : P ∪ Q ⊆ (P ∩ Qᶜ) ∪ Q := by
    intro D hD
    by_cases hq : D ∈ Q
    · exact Or.inr hq
    · exact Or.inl ⟨hD.resolve_right hq, hq⟩
  rw [Set.compl_union]
  calc flipProb (Pᶜ ∩ Qᶜ) (P ∪ Q) t
      ≤ flipProb (Pᶜ ∩ Qᶜ) ((P ∩ Qᶜ) ∪ Q) t := flipProb_mono le_rfl hsplit
    _ ≤ flipProb (Pᶜ ∩ Qᶜ) (P ∩ Qᶜ) t + flipProb (Pᶜ ∩ Qᶜ) Q t := flipProb_union_right_le
    _ ≤ condFlip P Qᶜ t + flipProb Qᶜ Q t :=
        add_le_add le_rfl (flipProb_mono Set.inter_subset_right le_rfl)

end Union

/-! ### Appending an expansion -/

namespace Alg

variable {A B C : Type*} {t : ℕ}

/-- **`𝒜` followed by the expansion `X` on its output**: the `t + kq`-query algorithm that runs
`𝒜`, then the `kq` queries of `X` on `𝒜`'s output (the classical expanded adversary of CMS19
Proposition 8.11, p. 42), and outputs `𝒜`'s output.

Running time: that of `𝒜`, then the `kq` queries of `X`, each input computed by `X` from `𝒜`'s
output and the earlier answers; polynomial when `𝒜` and `X` are. This running time is argued here,
not proved in Lean. -/
def append (𝒜 : Alg A B C t) (X : Expansion A B C) (kq : ℕ) : Alg A B C (t + kq) where
  next ans := if ans.length < t then 𝒜.next ans else X.next (𝒜.out (ans.take t)) (ans.drop t)
  out ans := 𝒜.out (ans.take t)

variable (𝒜 : Alg A B C t) (X : Expansion A B C) (kq : ℕ) (h : A → B)

/-- The first `i ≤ t` queries of the appended algorithm are `𝒜`'s. -/
theorem queries_append_of_le : ∀ {i}, i ≤ t → (𝒜.append X kq).queries h i = 𝒜.queries h i
  | 0, _ => rfl
  | i + 1, hi => by
    rw [queries_succ, queries_succ, queryAt, queryAt, queries_append_of_le (by omega)]
    simp only [append, List.length_map, length_queries, show i < t by omega, ite_true]

/-- After `t + i` steps the appended algorithm has made `𝒜`'s queries and the first `i` queries of
`X` on `𝒜`'s output. -/
theorem queries_append_add :
    ∀ i, (𝒜.append X kq).queries h (t + i) = 𝒜.queries h t ++ X.run h (𝒜.output h) i
  | 0 => (queries_append_of_le 𝒜 X kq h le_rfl).trans (List.append_nil _).symm
  | i + 1 => by
    change (𝒜.append X kq).queries h (t + i + 1) = _
    rw [queries_succ, queryAt, queries_append_add i, Expansion.run, ← List.append_assoc]
    congr 2
    have hlen : ((𝒜.queries h t).map h).length = t := by simp
    simp only [append, List.map_append, List.length_append, hlen, List.length_map,
      Expansion.length_run, show ¬ t + i < t by omega, ite_false, output]
    rw [List.take_left' hlen, List.drop_left' hlen]

/-- The appended algorithm outputs `𝒜`'s output. -/
theorem output_append : (𝒜.append X kq).output h = 𝒜.output h := by
  have hlen : ((𝒜.queries h t).map h).length = t := by simp
  rw [output, queries_append_add]
  simp only [append, output, List.map_append]
  rw [List.take_left' hlen]

variable [DecidableEq A]

/-- The log of the appended algorithm records every query of `X` on `𝒜`'s output. -/
theorem lookup_log_append_of_mem {a : A} (ha : a ∈ X.run h (𝒜.output h) kq) :
    ((𝒜.append X kq).log h (t + kq)).lookup a = some (h a) := by
  rw [log, queries_append_add]
  exact lookup_logOf_of_mem (List.mem_append_right _ ha)

end Alg

end GordieHowe.ROM
