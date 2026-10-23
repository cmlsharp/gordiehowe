-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AdaptiveTP

@[expose] public section

/-!
# The per-branch query count of the trace-preserving composition

The composition of the trace-preserving form of an adversary with run-time kinds
(`AdaptiveIAlg.toTPKindAlg`, `GordieHowe/Model/Quantum/Interactive/AdaptiveTP.lean`) with a challenger compiles
`q + width` reprogrammed queries per slot and `width` per post batch. On each branch most of them
are padded: the challenger's queries of a slot without a request, or once the challenger's program
has returned or `Q` requests have been answered, and the adversary's queries of a slot with a
request. This file gives the certificate of `ReprogrammedCircuit.Valid`
(`GordieHowe/Model/QROM/CircuitCount.lean`) for the composed circuit, with the records

- the challenger's query `i` of slot `j` on the branches where its program reads the oracle there
  (`KindAlg.ChalLive`): at most `q` per answered request, so at most `Q * q`;
- the adversary's queries of slot `j` on the branches without a request at slot `j`: at most
  `width` per query slot, and a branch has at most `budget` query slots;
- every post-phase query: `width * post`.

So the pure algorithm of the composition has a per-branch query count (`QueryCount`) of
`width * budget + Q * q + width * post` (`AdaptiveIAlg.tpQueryCount`), whatever the number of
slots.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

/-! ### Counting records over blocks of indices -/

section CountBlocks

variable {W : Type}

open Classical in
theorem countBelow_add (C : ℕ → Set W) (a b : ℕ) (w : W) :
    GordieHowe.QROM.countBelow C (a + b) w =
      GordieHowe.QROM.countBelow C a w + GordieHowe.QROM.countBelow (fun r => C (a + r)) b w := by
  induction b with
  | zero => simp [GordieHowe.QROM.countBelow_zero]
  | succ b ih =>
    rw [← add_assoc, GordieHowe.QROM.countBelow_succ, ih, GordieHowe.QROM.countBelow_succ, add_assoc]

theorem countBelow_le_of_forall (C : ℕ → Set W) (n : ℕ) (w : W) :
    GordieHowe.QROM.countBelow C n w ≤ n := by
  classical
  unfold GordieHowe.QROM.countBelow
  exact (card_filter_le _ _).trans (card_range n).le

theorem countBelow_eq_zero_of_forall (C : ℕ → Set W) (n : ℕ) (w : W)
    (h : ∀ r < n, w ∉ C r) : GordieHowe.QROM.countBelow C n w = 0 := by
  classical
  unfold GordieHowe.QROM.countBelow
  rw [card_eq_zero, filter_eq_empty_iff]
  intro r hr
  exact h r (mem_range.1 hr)

end CountBlocks

/-! ### Certificates of concatenated circuits -/

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y]

/-- **A certificate for a concatenation of circuits with `L` queries each**, from certificates of
the pieces, piece `i` starting at query `k₀ + i * L` between `P i` and `P (i + 1)`. -/
theorem Valid.concat_of {C G : ℕ → Set V} {L : ℕ} :
    ∀ {cs : List (ReprogrammedCircuit V X Y)} {k₀ : ℕ} {P : ℕ → Set V},
      (∀ c ∈ cs, c.queries = L) →
      (∀ i (hi : i < cs.length), Valid C G cs[i] (k₀ + i * L) (P i) (P (i + 1))) →
      Valid C G (concat cs) k₀ (P 0) (P cs.length)
  | [], _, _, _, _ => fun _ h => h
  | c :: cs, k₀, P, hq, h => by
    refine Valid.append (by have := h 0 (by simp); simpa using this) ?_
    rw [hq c (List.mem_cons_self ..)]
    have := Valid.concat_of (cs := cs) (k₀ := k₀ + L) (P := fun i => P (i + 1))
      (fun d hd => hq d (List.mem_cons_of_mem _ hd)) (fun i hi => by
        have h' := h (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at h'
        have e : k₀ + L + i * L = k₀ + (i + 1) * L := by ring
        rw [e]
        exact h')
    simpa using this


/-- `Valid.concat_of` for the circuits of a function on `Fin n`. -/
theorem Valid.concat_finRange {C G : ℕ → Set V} {n L k₀ : ℕ}
    {f : Fin n → ReprogrammedCircuit V X Y} {P : ℕ → Set V} (hq : ∀ i, (f i).queries = L)
    (h : ∀ i : Fin n, Valid C G (f i) (k₀ + i * L) (P i) (P (i + 1))) :
    Valid C G (concat ((List.finRange n).map f)) k₀ (P 0) (P n) := by
  have := Valid.concat_of (C := C) (G := G) (L := L) (cs := (List.finRange n).map f) (k₀ := k₀)
    (P := P) (by
      intro c hc
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
      exact hq i)
    (fun i hi => by
      simp only [List.getElem_map, List.getElem_finRange]
      exact h _)
  simpa using this

omit [AddCommGroup Y] in
theorem queries_concat_finRange {n L : ℕ} {f : Fin n → ReprogrammedCircuit V X Y}
    (hq : ∀ i, (f i).queries = L) : (concat ((List.finRange n).map f)).queries = n * L := by
  rw [queries_concat, List.map_map]
  have : (List.finRange n).map ((fun c => c.queries) ∘ f) = (List.finRange n).map fun _ => L :=
    List.map_congr_left fun i _ => hq i
  rw [this]
  simp

end ReprogrammedCircuit

/-! ### The challenger's state read from the registers -/

namespace Challenger

variable {X Y Req Resp : Type} (C : Challenger X Y Req Resp)

/-- The challenger's state after the slots below `j` reads only the logs and answers below `j`. -/
theorem regState_congr_logs {m : ℕ} (ω : C.Coins) {lg lg' : LogReg Req m}
    {ans ans' : Fin m → List Y} :
    ∀ j : ℕ, (∀ j' : Fin m, (j' : ℕ) < j → lg j' = lg' j' ∧ ans j' = ans' j') →
      C.regState ω lg ans j = C.regState ω lg' ans' j
  | 0, _ => rfl
  | j + 1, h => by
    rw [regState_add_one, regState_add_one, regState_congr_logs ω j fun j' hj' => h j' (by omega)]
    by_cases hj : j < m
    · obtain ⟨h1, h2⟩ := h ⟨j, hj⟩ (by simp)
      simp only [dif_pos hj, h1, h2]
    · simp only [dif_neg hj]

/-- The state after slot `j` from the state before it. -/
theorem regState_succ {m : ℕ} (ω : C.Coins) (lg : LogReg Req m) (ans : Fin m → List Y) (j : Fin m) :
    C.regState ω lg ans (j + 1) =
      match lg j with
      | none => C.regState ω lg ans j
      | some r =>
        if (C.regState ω lg ans j).history.length < C.Q then
          ⟨(C.regState ω lg ans j).history ++
            [⟨r, (C.outWith ω (C.regState ω lg ans j).history r (ans j)).response⟩],
            (C.regState ω lg ans j).assignments ++
              (C.outWith ω (C.regState ω lg ans j).history r (ans j)).assignments⟩
        else C.regState ω lg ans j := by
  rw [regState_add_one, dif_pos j.isLt]
  rfl

/-- At most `Q` requests are answered. -/
theorem length_history_regState_le {m : ℕ} (ω : C.Coins) (lg : LogReg Req m)
    (ans : Fin m → List Y) : ∀ j : ℕ, (C.regState ω lg ans j).history.length ≤ C.Q
  | 0 => by simp [regState, regStateOf]
  | j + 1 => by
    have ih := length_history_regState_le ω lg ans j
    by_cases hj : j < m
    · rw [show j + 1 = ((⟨j, hj⟩ : Fin m) : ℕ) + 1 from rfl, regState_succ]
      rcases lg ⟨j, hj⟩ with _ | r
      · exact ih
      · simp only
        split_ifs with hq
        · simp only [List.length_append, List.length_singleton]
          omega
        · exact ih
    · rw [regState_add_one, dif_neg hj]
      exact ih

/-- The slot `j` answers a request: it holds one and fewer than `Q` were answered before. -/
def Answers {m : ℕ} (ω : C.Coins) (lg : LogReg Req m) (ans : Fin m → List Y) (j : Fin m) :
    Prop :=
  (lg j).isSome ∧ (C.regState ω lg ans j).history.length < C.Q

/-- The history grows by one at a slot that answers a request, and stays otherwise. -/
theorem length_history_succ {m : ℕ} (ω : C.Coins) (lg : LogReg Req m) (ans : Fin m → List Y)
    (j : Fin m) [Decidable (C.Answers ω lg ans j)] :
    (C.regState ω lg ans (j + 1)).history.length =
      (C.regState ω lg ans j).history.length + if C.Answers ω lg ans j then 1 else 0 := by
  rw [regState_succ]
  rcases hl : lg j with _ | r
  · have ha : ¬ C.Answers ω lg ans j := fun h => by
      have := h.1
      rw [hl] at this
      exact absurd this (by simp)
    simp [ha]
  · by_cases hq : (C.regState ω lg ans j).history.length < C.Q
    · have ha : C.Answers ω lg ans j := ⟨by rw [hl]; rfl, hq⟩
      simp [hq, ha]
    · have ha : ¬ C.Answers ω lg ans j := fun h => hq h.2
      simp [hq, ha]

open Classical in
/-- **The answered requests below `n` are the history.** -/
theorem card_answers {m : ℕ} (ω : C.Coins) (lg : LogReg Req m) (ans : Fin m → List Y) :
    ∀ n : ℕ, n ≤ m → ((univ : Finset (Fin m)).filter fun j : Fin m =>
      (j : ℕ) < n ∧ C.Answers ω lg ans j).card = (C.regState ω lg ans n).history.length
  | 0, _ => by simp [regState, regStateOf]
  | n + 1, hn => by
    have ih := card_answers ω lg ans n (by omega)
    set jn : Fin m := ⟨n, by omega⟩
    have hsplit : ((univ : Finset (Fin m)).filter fun j : Fin m =>
        (j : ℕ) < n + 1 ∧ C.Answers ω lg ans j) =
        ((univ : Finset (Fin m)).filter fun j : Fin m => (j : ℕ) < n ∧ C.Answers ω lg ans j) ∪
          ((univ : Finset (Fin m)).filter fun j : Fin m => j = jn ∧ C.Answers ω lg ans j) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hj : (j : ℕ) = n
        · exact Or.inr ⟨Fin.ext hj, h2⟩
        · exact Or.inl ⟨by omega, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
        · exact ⟨by omega, h2⟩
        · exact ⟨by simp [jn], h2⟩
    have hsingle : ((univ : Finset (Fin m)).filter fun j : Fin m =>
        j = jn ∧ C.Answers ω lg ans j).card = if C.Answers ω lg ans jn then 1 else 0 := by
      split_ifs with ha
      · rw [card_eq_one]
        refine ⟨jn, ?_⟩
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro rfl
          exact ⟨rfl, ha⟩
      · rw [card_eq_zero, filter_eq_empty_iff]
        rintro j - ⟨rfl, h⟩
        exact ha h
    rw [hsplit, card_union_of_disjoint, ih, hsingle,
      show n + 1 = (jn : ℕ) + 1 from rfl, length_history_succ]
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [mem_filter, mem_univ, true_and] at hj hj'
    rw [hj'.1] at hj
    simp [jn] at hj

end Challenger

/-! ### The challenger's live queries -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **The challenger's query `i` of slot `j` reads the oracle**: the slot holds a request, fewer
than `Q` were answered before, and the challenger's program makes a further query after the answers
of its first `i` queries. Otherwise the query reads the padding list (`chalAss_of_not_live`). -/
def ChalLive (j : Fin A.slots) (i : ℕ) (u : A.CCl C) : Prop :=
  ∃ r, u.logs j = some r ∧ (A.stateAt C u j).history.length < C.Q ∧
    OracleProgAns.wants (C.respond u.coins (A.stateAt C u j).history r)
      ((A.ansOf C u j).take i) = true

theorem chalAss_of_not_live [Nonempty X] [AddGroup Y] (j : Fin A.slots) (i : Fin C.q)
    (u : A.CCl C) (h : ¬ A.ChalLive C j i u) : A.chalAss C j i u = paddingAssignments X Y := by
  unfold chalAss
  rcases hl : u.logs j with _ | r
  · rfl
  · simp only
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h ⟨r, hl, h1, h2⟩

theorem answers_of_live {j : Fin A.slots} {i : ℕ} {u : A.CCl C} (h : A.ChalLive C j i u) :
    C.Answers u.coins u.logs (A.ansOf C u) j := by
  obtain ⟨r, hr, hq, -⟩ := h
  exact ⟨by rw [hr]; rfl, hq⟩

/-- **A live query depends only on the registers it reads**: the coins, the logs up to slot `j`,
the answers of the slots before `j`, and the first `i` answers of slot `j`. -/
theorem chalLive_congr {j : Fin A.slots} {i : ℕ} {u u' : A.CCl C} (hc : u.coins = u'.coins)
    (hl : ∀ j' : Fin A.slots, j' ≤ j → u.logs j' = u'.logs j')
    (ha : ∀ j' : Fin A.slots, j' < j → A.ansOf C u j' = A.ansOf C u' j')
    (hi : (A.ansOf C u j).take i = (A.ansOf C u' j).take i) :
    A.ChalLive C j i u ↔ A.ChalLive C j i u' := by
  have hs : A.stateAt C u j = A.stateAt C u' j := by
    unfold stateAt
    rw [hc]
    exact C.regState_congr_logs u'.coins (j : ℕ) fun j' hj' =>
      ⟨hl j' (Fin.le_of_lt hj'), ha j' hj'⟩
  unfold ChalLive
  rw [hs, hl j le_rfl, hc, hi]

end KindAlg

/-! ### Trace-preserving Kraus maps -/

namespace KrausMap

variable {R R' ι : Type*} [Fintype R] [Fintype R'] [Fintype ι] [DecidableEq ι]

theorem tp_comp {K₂ : KrausMap R' ι ι} {K₁ : KrausMap R ι ι}
    (h₂ : ∑ r, (K₂.op r)ᴴ * K₂.op r = 1) (h₁ : ∑ r, (K₁.op r)ᴴ * K₁.op r = 1) :
    ∑ r, ((K₂.comp K₁).op r)ᴴ * (K₂.comp K₁).op r = 1 := by
  simp only [KrausMap.comp]
  rw [Fintype.sum_prod_type]
  have h : ∀ r₁, ∑ r₂, (K₂.op r₂ * K₁.op r₁)ᴴ * (K₂.op r₂ * K₁.op r₁) =
      (K₁.op r₁)ᴴ * K₁.op r₁ := fun r₁ => by
    have e : ∀ r₂, (K₂.op r₂ * K₁.op r₁)ᴴ * (K₂.op r₂ * K₁.op r₁) =
        (K₁.op r₁)ᴴ * ((K₂.op r₂)ᴴ * K₂.op r₂) * K₁.op r₁ := fun r₂ => by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    simp only [e]
    rw [← Finset.sum_mul, ← Finset.mul_sum, h₂, Matrix.mul_one]
  simp only [h]
  exact h₁

theorem tp_measureFn {M : Type*} [Fintype M] [DecidableEq M] (f : ι → M) :
    ∑ m, ((KrausMap.measureFn f).op m)ᴴ * (KrausMap.measureFn f).op m = 1 := by
  ext i j
  simp only [KrausMap.measureFn, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j <;> simp [hij, apply_ite]

theorem tp_tensorId_reindex {L κ : Type*} [Fintype L] [DecidableEq L] [Fintype κ] [DecidableEq κ]
    {K : KrausMap R ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1) (e : ι × L ≃ κ) :
    ∑ r, (((K.tensorId L).reindex e).op r)ᴴ * ((K.tensorId L).reindex e).op r = 1 := by
  have : ∑ r, (((K.tensorId L).reindex e).op r)ᴴ * ((K.tensorId L).reindex e).op r =
      ((∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ (1 : Matrix L L ℂ)).submatrix e.symm e.symm := by
    rw [Matrix.sum_kronecker, Matrix.submatrix_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [KrausMap.reindex, KrausMap.tensorId]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, Matrix.one_mul]
  rw [this, h, one_kronecker_one, submatrix_one_equiv]

end KrausMap

/-! ### Counting slots -/

open Classical in
/-- Splitting off the last index of a count below `n + 1`. -/
theorem card_filter_lt_succ {m : ℕ} (P : Fin m → Prop) {n : ℕ} (hn : n < m) :
    ((univ : Finset (Fin m)).filter fun j : Fin m => (j : ℕ) < n + 1 ∧ P j).card =
      ((univ : Finset (Fin m)).filter fun j : Fin m => (j : ℕ) < n ∧ P j).card +
        if P ⟨n, hn⟩ then 1 else 0 := by
  set jn : Fin m := ⟨n, hn⟩
  have hsplit : ((univ : Finset (Fin m)).filter fun j : Fin m => (j : ℕ) < n + 1 ∧ P j) =
      ((univ : Finset (Fin m)).filter fun j : Fin m => (j : ℕ) < n ∧ P j) ∪
        ((univ : Finset (Fin m)).filter fun j : Fin m => j = jn ∧ P j) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hj : (j : ℕ) = n
      · exact Or.inr ⟨Fin.ext hj, h2⟩
      · exact Or.inl ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by simp [jn], h2⟩
  have hsingle : ((univ : Finset (Fin m)).filter fun j : Fin m => j = jn ∧ P j).card =
      if P jn then 1 else 0 := by
    split_ifs with ha
    · rw [card_eq_one]
      refine ⟨jn, ?_⟩
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl, ha⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro j - ⟨rfl, h⟩
      exact ha h
  rw [hsplit, card_union_of_disjoint, hsingle]
  rw [Finset.disjoint_left]
  intro j hj hj'
  simp only [mem_filter, mem_univ, true_and] at hj hj'
  rw [hj'.1] at hj
  simp [jn] at hj

theorem take_ofFn_congr {α : Type*} {n r : ℕ} {f g : Fin n → α} (h : ∀ i : Fin n, (i : ℕ) < r → f i = g i) :
    (List.ofFn f).take r = (List.ofFn g).take r := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at h1
    exact h ⟨i, h1.2⟩ h1.1

/-! ### The certificate of the trace-preserving composition -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : AdaptiveIAlg X Y Req Resp O) (Ch : Challenger X Y Req Resp)

/-- The composed registers of the trace-preserving composition. -/
abbrev TW := A.toTPKindAlg.CW Ch

open Classical in
/-- The number of slots below `n` without a request. -/
noncomputable def noneCnt (n : ℕ) (v : A.TW Ch) : ℕ :=
  ((univ : Finset (Fin A.toTPKindAlg.slots)).filter fun j : Fin A.toTPKindAlg.slots =>
    (j : ℕ) < n ∧ v.chal.logs j = none).card

open Classical in
/-- The number of slots below `n` that answer a request. -/
noncomputable def ansCnt (n : ℕ) (v : A.TW Ch) : ℕ :=
  ((univ : Finset (Fin A.toTPKindAlg.slots)).filter fun j : Fin A.toTPKindAlg.slots =>
    (j : ℕ) < n ∧ Ch.Answers v.chal.coins v.chal.logs (A.toTPKindAlg.ansOf Ch v.chal) j).card

theorem ansCnt_le (n : ℕ) (hn : n ≤ A.toTPKindAlg.slots) (v : A.TW Ch) : A.ansCnt Ch n v ≤ Ch.Q := by
  classical
  unfold ansCnt
  rw [Ch.card_answers _ _ _ n hn]
  exact Ch.length_history_regState_le _ _ _ n

/-- **Before slot `n`** (proof-internal): at most `budget` of the slots below `n` have no request,
the logs from `n` on are blank, and a branch that has not ended has counted the slots below `n`
without a request. -/
def Good (n : ℕ) : Set (A.TW Ch) :=
  {v | A.noneCnt Ch n v ≤ A.budget ∧ (∀ j : Fin A.toTPKindAlg.slots, n ≤ j → v.chal.logs j = none) ∧
    (v.adv.workspace.2 ≠ A.ended → (v.adv.workspace.2 : ℕ) = A.noneCnt Ch n v)}

/-- **After the adversary's Kraus map before slot `n`** (proof-internal): as `Good n`, except that a
branch that has not ended has also counted slot `n` if its kind there is a query, and its counter is
at most `budget`. -/
def Mid (n : ℕ) : Set (A.TW Ch) :=
  {v | A.noneCnt Ch n v ≤ A.budget ∧ (∀ j : Fin A.toTPKindAlg.slots, n ≤ j → v.chal.logs j = none) ∧
    (v.adv.workspace.2 ≠ A.ended →
      (v.adv.workspace.2 : ℕ) = A.noneCnt Ch n v + (if A.kind v.adv.workspace.1 then 0 else 1) ∧
        (v.adv.workspace.2 : ℕ) ≤ A.budget)}

theorem noneCnt_congr {n : ℕ} {v v' : A.TW Ch} (h : v'.chal.logs = v.chal.logs) :
    A.noneCnt Ch n v' = A.noneCnt Ch n v := by
  unfold noneCnt
  rw [h]

theorem good_congr {n : ℕ} {v v' : A.TW Ch} (h : v'.chal.logs = v.chal.logs)
    (hw : v'.adv.workspace = v.adv.workspace) (hv : v ∈ A.Good Ch n) : v' ∈ A.Good Ch n := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨by rwa [A.noneCnt_congr Ch h], fun j hj => by rw [h]; exact h2 j hj, ?_⟩
  rw [hw, A.noneCnt_congr Ch h]
  exact h3

theorem noneCnt_succ {n : ℕ} (hn : n < A.toTPKindAlg.slots) (v : A.TW Ch) :
    A.noneCnt Ch (n + 1) v =
      A.noneCnt Ch n v + if v.chal.logs ⟨n, hn⟩ = none then 1 else 0 := by
  classical
  unfold noneCnt
  convert card_filter_lt_succ (fun j => v.chal.logs j = none) hn using 2 <;>
    first | (ext; simp) | (congr 1; exact Subsingleton.elim _ _) | simp

open Classical in
theorem ansCnt_succ {n : ℕ} (hn : n < A.toTPKindAlg.slots) (v : A.TW Ch) :
    A.ansCnt Ch (n + 1) v = A.ansCnt Ch n v +
      if Ch.Answers v.chal.coins v.chal.logs (A.toTPKindAlg.ansOf Ch v.chal) ⟨n, hn⟩ then 1
      else 0 := by
  classical
  unfold ansCnt
  convert card_filter_lt_succ (fun j => Ch.Answers v.chal.coins v.chal.logs
    (A.toTPKindAlg.ansOf Ch v.chal) j) hn using 2 <;>
    first | (ext; simp) | (congr 1; exact Subsingleton.elim _ _) | simp


/-! #### The counter through the adversary's Kraus maps -/

/-- Within the budget and before the end, the trace-preserving counter step keeps the workspace
and advances the counter on a query branch, which was below `budget`. -/
theorem tpShift_counter {z : A.CReg} (hz : A.inBudget z = true) (ha : z ∈ A.aliveD) :
    (A.tpShift z).workspace.1 = z.workspace.1 ∧
      ((A.tpShift z).workspace.2 : ℕ) = z.workspace.2 + (if A.kind z.workspace.1 then 0 else 1) ∧
      (A.kind z.workspace.1 = false → (z.workspace.2 : ℕ) < A.budget) := by
  obtain ⟨⟨⟨w, c⟩, rq, rs⟩, p⟩ := z
  simp only [aliveD, Set.mem_setOf_eq, DReg.workspace] at ha
  rw [inBudget_of_alive_kind] at hz
  simp only [DReg.workspace] at hz ⊢
  cases hkw : A.kind w
  · have hc : (c : ℕ) < A.budget := by
      have h1 : c ≠ Fin.castSucc (Fin.last A.budget) := by simpa [hkw] using hz
      have h2 : (c : ℕ) ≠ A.budget := fun h => h1 (Fin.ext (by simpa using h))
      have h3 : (c : ℕ) ≠ A.budget + 1 := fun h => ha (Fin.ext (by simpa [ended] using h))
      omega
    have hnl : c ≠ Fin.last (A.budget + 1) := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    have h1 := coe_finRotate_of_ne_last hnl
    have hr0 : finRotate (A.budget + 2) c ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp only [h1, Fin.val_zero] at this
      omega
    have hre : finRotate (A.budget + 2) c ≠ A.ended := fun h => by
      have := congrArg Fin.val h
      simp only [h1, ended, Fin.val_last] at this
      omega
    have hrot : A.rot c = finRotate (A.budget + 2) c := by
      rw [rot, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hr0 hre]
    refine ⟨by simp [tpShift, wPerm], ?_, fun _ => hc⟩
    simp only [tpShift, wPerm, Equiv.prodCongr_apply, Equiv.prodShear_apply, hkw,
      Bool.false_eq_true, if_false, Prod.map_apply, Equiv.coe_refl, id_eq, Equiv.refl_apply, hrot,
      h1]
  · refine ⟨by simp [tpShift, wPerm], ?_, fun h => absurd h (by simp)⟩
    simp [tpShift, wPerm, hkw]

/-- **The counter through the adversary's Kraus map before a slot**: a branch either ends, or had
not ended, keeps its counter on a request and advances it from below `budget` on a query. -/
theorem tp_slot_counter {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots)
    (z : A.R ⊕ (A.R ⊕ Fin (A.budget + 2))) (y x : A.CReg)
    (h : (A.toTPKindAlg.step k).op z y x ≠ 0) :
    y.workspace.2 = A.ended ∨ (x.workspace.2 ≠ A.ended ∧
      (y.workspace.2 : ℕ) = x.workspace.2 + (if A.kind y.workspace.1 then 0 else 1) ∧
      (A.kind y.workspace.1 = false → (x.workspace.2 : ℕ) < A.budget)) := by
  change A.tpOp k z y x ≠ 0 at h
  rcases z with r | r | c
  · simp only [tpOp, hk, if_true, restrict_permConj_op_apply] at h
    set z := A.tpShift.symm y
    have hzy : A.tpShift z = y := Equiv.apply_symm_apply _ _
    have hb : A.inBudget z = true := by
      by_contra hb
      exact h (by simp [hb])
    have hK : (A.cntKraus k).op r z x ≠ 0 := fun h' => h (by rw [h', mul_zero])
    have hc := A.cntKraus_op_ne_zero hK
    by_cases hx : x.workspace.2 = A.ended
    · left
      rw [← hzy]
      exact A.tpShift_ended (hc.trans hx)
    · right
      have ha : z ∈ A.aliveD := by
        simp only [aliveD, Set.mem_setOf_eq, hc]
        exact hx
      obtain ⟨h1, h2, h3⟩ := A.tpShift_counter hb ha
      rw [hzy] at h1 h2
      refine ⟨hx, ?_, ?_⟩
      · rw [h2, h1, hc]
      · rw [h1]
        intro hk'
        rw [← hc]
        exact h3 hk'
  · left
    simp only [tpOp, hk, if_true, restrict_permConj_op_apply] at h
    by_cases hb : A.inBudget (A.endSwap.symm y)
    · exact absurd (by simp [hb]) h
    · have := A.endSwap_ended (Bool.of_not_eq_true hb)
      rwa [Equiv.apply_symm_apply] at this
  · left
    simp only [tpOp, Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
    rw [Matrix.single_apply] at h
    by_contra hne
    exact h (by rw [if_neg (fun h' => hne h'.1.symm), mul_zero])

/-- **The counter through a post-phase Kraus map**: a branch either ends or keeps its counter. -/
theorem tp_post_counter {k : StepIdx A.slots A.post} (hk : ¬ (k : ℕ) < A.slots)
    (z : A.R ⊕ (A.R ⊕ Fin (A.budget + 2))) (y x : A.CReg)
    (h : (A.toTPKindAlg.step k).op z y x ≠ 0) :
    y.workspace.2 = A.ended ∨ y.workspace.2 = x.workspace.2 := by
  change A.tpOp k z y x ≠ 0 at h
  rcases z with r | r | c
  · simp only [tpOp, hk, if_false] at h
    exact Or.inr (A.cntKraus_op_ne_zero h)
  · simp [tpOp, hk] at h
  · left
    simp only [tpOp, Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
    rw [Matrix.single_apply] at h
    by_contra hne
    exact h (by rw [if_neg (fun h' => hne h'.1.symm), mul_zero])

/-! #### Indices -/

theorem slotLen_pos : 0 < Ch.q + A.toTPKindAlg.width := by
  have := A.toTPKindAlg.width_pos
  omega

theorem div_lt_slots {k : ℕ} (h : k < A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width)) :
    k / (Ch.q + A.toTPKindAlg.width) < A.toTPKindAlg.slots :=
  Nat.div_lt_of_lt_mul (by rwa [mul_comm] at h)

open Classical in
/-- **The records** (proof-internal): at the challenger's query `i` of slot `j`, the branches where
it is live; at the adversary's queries of slot `j`, the branches without a request; every
post-phase query. -/
noncomputable def recSet (k : ℕ) : Set (A.TW Ch) :=
  if h : k < A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) then
    if k % (Ch.q + A.toTPKindAlg.width) < Ch.q then
      {v | A.toTPKindAlg.ChalLive Ch ⟨k / (Ch.q + A.toTPKindAlg.width), A.div_lt_slots Ch h⟩
        (k % (Ch.q + A.toTPKindAlg.width)) v.chal}
    else {v | v.chal.logs ⟨k / (Ch.q + A.toTPKindAlg.width), A.div_lt_slots Ch h⟩ = none}
  else Set.univ

open Classical in
/-- **The supports at the queries** (proof-internal): during slot `j`, `Good (j + 1)`; in the post
phase, `Good slots`. -/
noncomputable def supSet (k : ℕ) : Set (A.TW Ch) :=
  if k < A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) then A.Good Ch (k / (Ch.q + A.toTPKindAlg.width) + 1)
  else A.Good Ch A.toTPKindAlg.slots

theorem slot_index_lt (j : Fin A.toTPKindAlg.slots) {r : ℕ} (hr : r < Ch.q + A.toTPKindAlg.width) :
    (j : ℕ) * (Ch.q + A.toTPKindAlg.width) + r < A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) := by
  have hj := j.isLt
  calc (j : ℕ) * (Ch.q + A.toTPKindAlg.width) + r < ((j : ℕ) + 1) * (Ch.q + A.toTPKindAlg.width) := by
        rw [add_mul, one_mul]
        omega
    _ ≤ A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) := Nat.mul_le_mul_right _ hj

theorem slot_index_div (j : Fin A.toTPKindAlg.slots) {r : ℕ} (hr : r < Ch.q + A.toTPKindAlg.width) :
    ((j : ℕ) * (Ch.q + A.toTPKindAlg.width) + r) / (Ch.q + A.toTPKindAlg.width) = j := by
  rw [add_comm, Nat.add_mul_div_right _ _ (A.slotLen_pos Ch), Nat.div_eq_of_lt hr, zero_add]

theorem slot_index_mod (j : Fin A.toTPKindAlg.slots) {r : ℕ} (hr : r < Ch.q + A.toTPKindAlg.width) :
    ((j : ℕ) * (Ch.q + A.toTPKindAlg.width) + r) % (Ch.q + A.toTPKindAlg.width) = r := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem recSet_chal (j : Fin A.toTPKindAlg.slots) {i : ℕ} (hi : i < Ch.q) :
    A.recSet Ch ((j : ℕ) * (Ch.q + A.toTPKindAlg.width) + i) = {v | A.toTPKindAlg.ChalLive Ch j i v.chal} := by
  have hr : i < Ch.q + A.toTPKindAlg.width := by omega
  have hj : (⟨((j : ℕ) * (Ch.q + A.toTPKindAlg.width) + i) / (Ch.q + A.toTPKindAlg.width),
      A.div_lt_slots Ch (A.slot_index_lt Ch j hr)⟩ : Fin A.toTPKindAlg.slots) = j :=
    Fin.ext (A.slot_index_div Ch j hr)
  unfold recSet
  rw [dif_pos (A.slot_index_lt Ch j hr), if_pos (by rw [A.slot_index_mod Ch j hr]; exact hi), hj,
    A.slot_index_mod Ch j hr]

theorem recSet_adv (j : Fin A.toTPKindAlg.slots) {r : ℕ} (hr : r < A.toTPKindAlg.width) :
    A.recSet Ch ((j : ℕ) * (Ch.q + A.toTPKindAlg.width) + (Ch.q + r)) = {v | v.chal.logs j = none} := by
  have hr' : Ch.q + r < Ch.q + A.toTPKindAlg.width := by omega
  have hj : (⟨((j : ℕ) * (Ch.q + A.toTPKindAlg.width) + (Ch.q + r)) / (Ch.q + A.toTPKindAlg.width),
      A.div_lt_slots Ch (A.slot_index_lt Ch j hr')⟩ : Fin A.toTPKindAlg.slots) = j :=
    Fin.ext (A.slot_index_div Ch j hr')
  unfold recSet
  rw [dif_pos (A.slot_index_lt Ch j hr'), if_neg (by rw [A.slot_index_mod Ch j hr']; omega), hj]

theorem supSet_slot (j : Fin A.toTPKindAlg.slots) {r : ℕ} (hr : r < Ch.q + A.toTPKindAlg.width) :
    A.supSet Ch ((j : ℕ) * (Ch.q + A.toTPKindAlg.width) + r) = A.Good Ch (j + 1) := by
  unfold supSet
  rw [if_pos (A.slot_index_lt Ch j hr), A.slot_index_div Ch j hr]

theorem recSet_post {k : ℕ} (hk : A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) ≤ k) : A.recSet Ch k = Set.univ := by
  unfold recSet
  rw [dif_neg (by omega)]

theorem supSet_post {k : ℕ} (hk : A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) ≤ k) :
    A.supSet Ch k = A.Good Ch A.toTPKindAlg.slots := by
  unfold supSet
  rw [if_neg (by omega)]

/-- The records read only the challenger's registers. -/
theorem mem_recSet_congr {k : ℕ} {v v' : A.TW Ch} (h : v'.chal = v.chal) :
    v' ∈ A.recSet Ch k ↔ v ∈ A.recSet Ch k := by
  unfold recSet
  split_ifs <;> simp only [Set.mem_setOf_eq, Set.mem_univ, h]

/-! #### The count -/

open Classical in
/-- **The records of the slots below `n`**: at most `q` per answered request and `width` per slot
without a request. -/
theorem countBelow_slots_le (w : A.TW Ch) :
    ∀ n ≤ A.toTPKindAlg.slots, GordieHowe.QROM.countBelow (A.recSet Ch) (n * (Ch.q + A.toTPKindAlg.width)) w ≤
      Ch.q * A.ansCnt Ch n w + A.toTPKindAlg.width * A.noneCnt Ch n w
  | 0, _ => by simp [GordieHowe.QROM.countBelow_zero]
  | n + 1, hn => by
    have ih := countBelow_slots_le w n (by omega)
    set jn : Fin A.toTPKindAlg.slots := ⟨n, by omega⟩
    rw [add_mul, one_mul, countBelow_add, countBelow_add, A.noneCnt_succ Ch (by omega),
      A.ansCnt_succ Ch (by omega)]
    have hchal : GordieHowe.QROM.countBelow (fun r => A.recSet Ch (n * (Ch.q + A.toTPKindAlg.width) + r)) Ch.q w ≤
        Ch.q * (if Ch.Answers w.chal.coins w.chal.logs (A.toTPKindAlg.ansOf Ch w.chal) jn then 1
          else 0) := by
      split_ifs with ha
      · rw [mul_one]
        exact countBelow_le_of_forall _ _ _
      · rw [mul_zero, Nat.le_zero]
        refine countBelow_eq_zero_of_forall _ _ _ fun r hr hw => ha ?_
        have := A.recSet_chal Ch jn hr
        simp only [jn] at this
        rw [this] at hw
        exact A.toTPKindAlg.answers_of_live Ch hw
    have hadv : GordieHowe.QROM.countBelow (fun r => A.recSet Ch (n * (Ch.q + A.toTPKindAlg.width) + (Ch.q + r)))
        A.toTPKindAlg.width w ≤ A.toTPKindAlg.width * (if w.chal.logs jn = none then 1 else 0) := by
      split_ifs with hl
      · rw [mul_one]
        exact countBelow_le_of_forall _ _ _
      · rw [mul_zero, Nat.le_zero]
        refine countBelow_eq_zero_of_forall _ _ _ fun r hr hw => hl ?_
        have := A.recSet_adv Ch jn hr
        simp only [jn] at this
        rw [this] at hw
        exact hw
    refine le_trans (add_le_add ih (add_le_add hchal hadv)) (le_of_eq ?_)
    ring

/-! #### The nodes of the composed circuit -/

section Nodes

variable [Nonempty X] [AddCommGroup Y]

theorem advKraus_ne_zero {k : StepIdx A.toTPKindAlg.slots A.toTPKindAlg.post}
    {z : A.toTPKindAlg.R} {p' p : QueryReg (A.TW Ch) 1 X Y}
    (h : (A.toTPKindAlg.advKraus Ch k).op z p' p ≠ 0) :
    (A.toTPKindAlg.step k).op z p'.1.adv p.1.adv ≠ 0 ∧ p'.1.chal = p.1.chal ∧ p'.2 = p.2 := by
  rw [KindAlg.advKraus, KrausMap.tensorId_reindex_op_apply] at h
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  refine ⟨h1, ?_, ?_⟩
  · by_contra hne
    exact h2 (Matrix.one_apply_ne fun h' => hne (congrArg Prod.fst h'))
  · by_contra hne
    exact h2 (Matrix.one_apply_ne fun h' => hne (congrArg (fun x => x.2) h'))

theorem tp_advKraus (k : StepIdx A.toTPKindAlg.slots A.toTPKindAlg.post) :
    ∑ r, ((A.toTPKindAlg.advKraus Ch k).op r)ᴴ * (A.toTPKindAlg.advKraus Ch k).op r = 1 :=
  KrausMap.tp_tensorId_reindex (A.toTPKindAlg_step_tp k) _

theorem tp_measReq (j : Fin A.toTPKindAlg.slots) :
    ∑ r, ((A.toTPKindAlg.measReq Ch j).op r)ᴴ * (A.toTPKindAlg.measReq Ch j).op r = 1 :=
  KrausMap.tp_comp (KrausMap.tp_ofPerm _) (KrausMap.tp_measureFn _)

theorem keeps_of_chal {R : Type} [Fintype R]
    (K : KrausMap R (QueryReg (A.TW Ch) 1 X Y) (QueryReg (A.TW Ch) 1 X Y))
    (h : ∀ r p' p, K.op r p' p ≠ 0 → p'.1.chal = p.1.chal) (k : ℕ) :
    ∀ i < k, ∀ r p' p, K.op r p' p ≠ 0 →
      (p'.1 ∈ A.recSet Ch i ↔ p.1 ∈ A.recSet Ch i) :=
  fun _ _ r p' p hne => A.mem_recSet_congr Ch (h r p' p hne)

theorem ofPerm_ne_zero {π : Equiv.Perm (QueryReg (A.TW Ch) 1 X Y)} {r : Unit}
    {p' p : QueryReg (A.TW Ch) 1 X Y} (h : (KrausMap.ofPerm π).op r p' p ≠ 0) : p' = π p := by
  rw [KrausMap.ofPerm_op_apply] at h
  by_contra hne
  exact h (if_neg hne)

/-- The adversary's Kraus map before slot `j` sends `Good j` into `Mid j`. -/
theorem advKraus_slot_supp (j : Fin A.toTPKindAlg.slots) :
    ∀ r (p' p : QueryReg (A.TW Ch) 1 X Y), p.1 ∈ A.Good Ch j →
      (A.toTPKindAlg.advKraus Ch (slotStep j)).op r p' p ≠ 0 → p'.1 ∈ A.Mid Ch j := by
  intro z p' p hp hne
  obtain ⟨hK, hc, -⟩ := A.advKraus_ne_zero Ch hne
  obtain ⟨g1, g2, g3⟩ := hp
  have hn : A.noneCnt Ch j p'.1 = A.noneCnt Ch j p.1 := A.noneCnt_congr Ch (by rw [hc])
  refine ⟨by rw [hn]; exact g1, fun j' hj' => by rw [hc]; exact g2 j' hj', fun ha => ?_⟩
  rcases A.tp_slot_counter (k := slotStep j) j.isLt z p'.1.adv p.1.adv hK with he | ⟨hx, hy, hlt⟩
  · exact absurd he ha
  · have hx' := g3 hx
    rw [hn]
    refine ⟨by rw [hy, hx'], ?_⟩
    rw [hy]
    cases hkw : A.kind p'.1.adv.workspace.1
    · have := hlt hkw
      simp only [Bool.false_eq_true, if_false]
      omega
    · simp only [if_true, add_zero]
      omega

/-- A post-phase Kraus map keeps `Good slots`. -/
theorem advKraus_post_supp (b : Fin A.toTPKindAlg.post) :
    ∀ r (p' p : QueryReg (A.TW Ch) 1 X Y), p.1 ∈ A.Good Ch A.toTPKindAlg.slots →
      (A.toTPKindAlg.advKraus Ch (postStep b)).op r p' p ≠ 0 →
        p'.1 ∈ A.Good Ch A.toTPKindAlg.slots := by
  intro z p' p hp hne
  obtain ⟨hK, hc, -⟩ := A.advKraus_ne_zero Ch hne
  obtain ⟨g1, g2, g3⟩ := hp
  have hn : A.noneCnt Ch A.toTPKindAlg.slots p'.1 = A.noneCnt Ch A.toTPKindAlg.slots p.1 :=
    A.noneCnt_congr Ch (by rw [hc])
  refine ⟨by rw [hn]; exact g1, fun j' hj' => by rw [hc]; exact g2 j' hj', fun ha => ?_⟩
  rcases A.tp_post_counter (k := postStep b) (by simp) z p'.1.adv p.1.adv hK with he | he
  · exact absurd he ha
  · rw [hn, he]
    exact g3 (by rw [← he]; exact ha)

/-- The adversary's last Kraus map keeps `Good slots`. -/
theorem advKraus_last_supp :
    ∀ r (p' p : QueryReg (A.TW Ch) 1 X Y), p.1 ∈ A.Good Ch A.toTPKindAlg.slots →
      (A.toTPKindAlg.advKraus Ch lastStep).op r p' p ≠ 0 →
        p'.1 ∈ A.Good Ch A.toTPKindAlg.slots := by
  intro z p' p hp hne
  obtain ⟨hK, hc, -⟩ := A.advKraus_ne_zero Ch hne
  obtain ⟨g1, g2, g3⟩ := hp
  have hn : A.noneCnt Ch A.toTPKindAlg.slots p'.1 = A.noneCnt Ch A.toTPKindAlg.slots p.1 :=
    A.noneCnt_congr Ch (by rw [hc])
  refine ⟨by rw [hn]; exact g1, fun j' hj' => by rw [hc]; exact g2 j' hj', fun ha => ?_⟩
  rcases A.tp_post_counter (k := lastStep) (by simp) z p'.1.adv p.1.adv hK with he | he
  · exact absurd he ha
  · rw [hn, he]
    exact g3 (by rw [← he]; exact ha)

theorem noneCnt_congr_below {n : ℕ} {v v' : A.TW Ch}
    (h : ∀ j : Fin A.toTPKindAlg.slots, (j : ℕ) < n → v'.chal.logs j = v.chal.logs j) :
    A.noneCnt Ch n v' = A.noneCnt Ch n v := by
  classical
  unfold noneCnt
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← h j h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h j h1]; exact h2⟩

/-- The request measurement of slot `j` sends `Mid j` into `Good (j + 1)`. -/
theorem measReq_supp (j : Fin A.toTPKindAlg.slots) :
    ∀ r (p' p : QueryReg (A.TW Ch) 1 X Y), p.1 ∈ A.Mid Ch j →
      (A.toTPKindAlg.measReq Ch j).op r p' p ≠ 0 → p'.1 ∈ A.Good Ch (j + 1) := by
  intro o p' p hp hne
  rw [measReq_op_apply Ch (B := A.toTPKindAlg) j o p' p] at hne
  have hy : p' = A.toTPKindAlg.copyReq Ch j p := by
    by_contra h
    exact hne (mul_eq_zero_of_left (if_neg h) _)
  subst hy
  obtain ⟨m1, m2, m3⟩ := hp
  have hlj : p.1.chal.logs j = none := m2 j le_rfl
  change (if A.toTPKindAlg.kind p.1.adv.workspace then
      (⟨p.1.adv, p.1.chal.swapLog j p.1.adv.request⟩, p.2) else p).1 ∈ A.Good Ch (j + 1)
  by_cases hk : A.toTPKindAlg.kind p.1.adv.workspace = true
  · rw [if_pos hk]
    set v : A.TW Ch := ⟨p.1.adv, p.1.chal.swapLog j p.1.adv.request⟩
    have hlogs : ∀ j' : Fin A.toTPKindAlg.slots, j' ≠ j → v.chal.logs j' = p.1.chal.logs j' :=
      fun j' hj' => by simp [v, ChallengerRegs.swapLog, Function.update_of_ne hj']
    have hlv : v.chal.logs j = some p.1.adv.request := by
      simp [v, ChallengerRegs.swapLog, hlj]
    have hn : A.noneCnt Ch (j + 1) v = A.noneCnt Ch j p.1 := by
      rw [A.noneCnt_succ Ch j.isLt, hlv]
      simp only [reduceCtorEq, if_false, add_zero]
      exact A.noneCnt_congr_below Ch fun j' hj' => hlogs j' (fun h => by rw [h] at hj'; omega)
    refine ⟨by rw [hn]; exact m1, fun j' hj' => ?_, fun ha => ?_⟩
    · rw [hlogs j' (fun h => by rw [h] at hj'; simp at hj')]
      exact m2 j' (by omega)
    · rw [hn]
      have ha' : p.1.adv.workspace.2 ≠ A.ended := ha
      obtain ⟨h1, -⟩ := m3 ha'
      have hkind : A.kind p.1.adv.workspace.1 = true := by
        change (A.kind p.1.adv.workspace.1 || decide (p.1.adv.workspace.2 = A.ended)) = true at hk
        simpa [ha'] using hk
      change (p.1.adv.workspace.2 : ℕ) = _
      rw [h1, hkind]
      simp
  · rw [if_neg hk]
    have hk' : (A.kind p.1.adv.workspace.1 || decide (p.1.adv.workspace.2 = A.ended)) = false :=
      Bool.of_not_eq_true hk
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hk'
    obtain ⟨hkind, ha⟩ := hk'
    obtain ⟨h1, h2⟩ := m3 ha
    rw [hkind] at h1
    simp only [Bool.false_eq_true, if_false] at h1
    have hn : A.noneCnt Ch (j + 1) p.1 = A.noneCnt Ch j p.1 + 1 := by
      rw [A.noneCnt_succ Ch j.isLt]
      simp only at hlj
      rw [if_pos hlj]
    refine ⟨by rw [hn]; omega, fun j' hj' => m2 j' (by omega), fun _ => by rw [hn]; exact h1⟩

/-- The records of the slots before `j` read only their logs, the answers and the coins. -/
theorem recSet_congr_below (j : Fin A.toTPKindAlg.slots) {i : ℕ}
    (hi : i < (j : ℕ) * (Ch.q + A.toTPKindAlg.width)) {v v' : A.TW Ch}
    (hc : v'.chal.coins = v.chal.coins) (hq : v'.chal.queries = v.chal.queries)
    (hl : ∀ j' : Fin A.toTPKindAlg.slots, j' < j → v'.chal.logs j' = v.chal.logs j') :
    v' ∈ A.recSet Ch i ↔ v ∈ A.recSet Ch i := by
  have hi' : i < A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) :=
    lt_of_lt_of_le hi (Nat.mul_le_mul_right _ j.isLt.le)
  have hj' : i / (Ch.q + A.toTPKindAlg.width) < j := Nat.div_lt_of_lt_mul (by
    rwa [mul_comm] at hi)
  have hans : A.toTPKindAlg.ansOf Ch v'.chal = A.toTPKindAlg.ansOf Ch v.chal := by
    unfold KindAlg.ansOf
    rw [hq]
  unfold recSet
  rw [dif_pos hi']
  split_ifs with hr
  · simp only [Set.mem_setOf_eq]
    refine A.toTPKindAlg.chalLive_congr Ch hc (fun j'' hj'' => hl j'' (lt_of_le_of_lt hj'' hj'))
      (fun j'' _ => by rw [hans]) (by rw [hans])
  · simp only [Set.mem_setOf_eq]
    rw [hl _ hj']

/-- The records up to the challenger's query `i` of slot `j` do not read its answer register. -/
theorem recSet_congr_query (j : Fin A.toTPKindAlg.slots) {i : ℕ} (hi : i < Ch.q) {i' : ℕ}
    (hi' : i' < (j : ℕ) * (Ch.q + A.toTPKindAlg.width) + i + 1) {v v' : A.TW Ch}
    (hc : v'.chal.coins = v.chal.coins) (hl : v'.chal.logs = v.chal.logs)
    (hq : ∀ (j' : Fin A.toTPKindAlg.slots) (i'' : Fin Ch.q), (j' ≠ j ∨ (i'' : ℕ) ≠ i) →
      v'.chal.queries j' i'' = v.chal.queries j' i'') :
    v' ∈ A.recSet Ch i' ↔ v ∈ A.recSet Ch i' := by
  have hL := A.slotLen_pos Ch
  have hlt : i' < A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) := by
    have := A.slot_index_lt Ch j (r := i) (by omega)
    omega
  have hjle : i' / (Ch.q + A.toTPKindAlg.width) ≤ j := by
    have : i' < ((j : ℕ) + 1) * (Ch.q + A.toTPKindAlg.width) := by
      rw [add_mul, one_mul]
      omega
    have := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at this)
    omega
  have hans : ∀ j' : Fin A.toTPKindAlg.slots, j' ≠ j →
      A.toTPKindAlg.ansOf Ch v'.chal j' = A.toTPKindAlg.ansOf Ch v.chal j' := fun j' hj' => by
    unfold KindAlg.ansOf
    congr 1
    funext i''
    rw [hq j' i'' (Or.inl hj')]
  unfold recSet
  rw [dif_pos hlt]
  set jj : Fin A.toTPKindAlg.slots := ⟨i' / (Ch.q + A.toTPKindAlg.width), A.div_lt_slots Ch hlt⟩
  split_ifs with hr
  · simp only [Set.mem_setOf_eq]
    refine A.toTPKindAlg.chalLive_congr Ch hc (fun j'' _ => by rw [hl])
      (fun j'' hj'' => hans j'' (fun h => by
        rw [h] at hj''
        exact absurd hjle (not_le.2 (Fin.lt_def.1 hj'')))) ?_
    by_cases hjj : jj = j
    · unfold KindAlg.ansOf
      refine take_ofFn_congr fun i'' hi'' => ?_
      rw [hq jj i'' (Or.inr ?_)]
      intro h
      have h1 : i' = (j : ℕ) * (Ch.q + A.toTPKindAlg.width) + i' % (Ch.q + A.toTPKindAlg.width) := by
        have := Nat.div_add_mod i' (Ch.q + A.toTPKindAlg.width)
        have hjv : i' / (Ch.q + A.toTPKindAlg.width) = j := congrArg Fin.val hjj
        rw [hjv] at this
        linarith [mul_comm (j : ℕ) (Ch.q + A.toTPKindAlg.width)]
      have h2 : i' % (Ch.q + A.toTPKindAlg.width) ≤ i := by
        have h3 := hi'
        rw [h1] at h3
        omega
      have h4 : (i'' : ℕ) < i' % (Ch.q + A.toTPKindAlg.width) := hi''
      omega
    · rw [hans jj hjj]
  · simp only [Set.mem_setOf_eq]
    rw [hl]

end Nodes

/-! #### The certificate -/

section Certificate

variable [Nonempty X] [AddCommGroup Y]

open ReprogrammedCircuit

/-- The adversary's queries, padded outside the records, keep a set of supports. -/
theorem valid_advQueries (ass : A.TW Ch → List (Assignment X Y)) (k₀ : ℕ) (P : Set (A.TW Ch))
    (hG : ∀ r < A.toTPKindAlg.width, A.supSet Ch (k₀ + r) = P)
    (hpad : ∀ r < A.toTPKindAlg.width, ∀ v ∈ P, v ∉ A.recSet Ch (k₀ + r) →
      ∀ x, (lastAssign (ass v) x).isSome)
    (hP : ∀ v v' : A.TW Ch, v'.chal = v.chal → v'.adv.workspace = v.adv.workspace → v ∈ P →
      v' ∈ P) :
    Valid (A.recSet Ch) (A.supSet Ch) (A.toTPKindAlg.advQueries Ch ass) k₀ P P := by
  have hsw : ∀ (k : Fin A.toTPKindAlg.width) r (p' p : QueryReg (A.TW Ch) 1 X Y),
      (KrausMap.ofPerm (A.toTPKindAlg.advSwap Ch k)).op r p' p ≠ 0 →
        p'.1.chal = p.1.chal ∧ p'.1.adv.workspace = p.1.adv.workspace := by
    intro k r p' p h
    rw [A.ofPerm_ne_zero Ch h]
    exact ⟨rfl, rfl⟩
  refine Valid.concat_finRange (L := 1) (P := fun _ => P) (fun _ => rfl) fun k => ?_
  simp only [mul_one]
  have hG' := hG k k.isLt
  refine ⟨KrausMap.tp_ofPerm _, A.keeps_of_chal Ch _ (fun r p' p h => (hsw k r p' p h).1) _, P,
    fun r p' p hp h => hP _ _ (hsw k r p' p h).1 (hsw k r p' p h).2 hp, ?_⟩
  refine ⟨fun v hv => by rw [hG']; exact hv, fun v hv hc x => hpad k k.isLt v (hG' ▸ hv) hc x, ?_⟩
  rw [hG']
  exact ⟨KrausMap.tp_ofPerm _, A.keeps_of_chal Ch _ (fun r p' p h => (hsw k r p' p h).1) _, P,
    fun r p' p hp h => hP _ _ (hsw k r p' p h).1 (hsw k r p' p h).2 hp, subset_rfl⟩

theorem garSwap_queries (j : Fin A.toTPKindAlg.slots) (i : Fin Ch.q)
    (p : QueryReg (A.TW Ch) 1 X Y) (j' : Fin A.toTPKindAlg.slots) (i'' : Fin Ch.q)
    (h : j' ≠ j ∨ (i'' : ℕ) ≠ i) :
    (A.toTPKindAlg.garSwap Ch j i p).1.chal.queries j' i'' = p.1.chal.queries j' i'' := by
  change Function.update p.1.chal.queries j (Function.update (p.1.chal.queries j) i (p.2 0)) j' i''
    = _
  by_cases hj : j' = j
  · subst hj
    have hi : i'' ≠ i := fun h' => h.elim (fun h'' => h'' rfl) fun h'' => h'' (by rw [h'])
    simp [Function.update_of_ne hi]
  · simp [Function.update_of_ne hj]

/-- The challenger's queries of slot `j`, padded where they are not live, keep `Good (j + 1)`. -/
theorem valid_chalQueries (j : Fin A.toTPKindAlg.slots) :
    Valid (A.recSet Ch) (A.supSet Ch) (A.toTPKindAlg.chalQueries Ch j)
      ((j : ℕ) * (Ch.q + A.toTPKindAlg.width)) (A.Good Ch (j + 1)) (A.Good Ch (j + 1)) := by
  refine Valid.concat_finRange (L := 1) (P := fun _ => A.Good Ch (j + 1)) (fun _ => rfl)
    fun i => ?_
  simp only [mul_one]
  have hr : (i : ℕ) < Ch.q + A.toTPKindAlg.width := by omega
  have hG := A.supSet_slot Ch j hr
  refine ⟨KrausMap.tp_ofPerm _, A.keeps_of_chal Ch _ (fun r p' p h => by
    rw [A.ofPerm_ne_zero Ch h]; rfl) _, A.Good Ch (j + 1), fun r p' p hp h => by
    rw [A.ofPerm_ne_zero Ch h]; exact hp, ?_⟩
  refine ⟨fun v hv => by rw [hG]; exact hv, fun v _ hv x => ?_, ?_⟩
  · rw [A.recSet_chal Ch j i.isLt] at hv
    show (lastAssign (A.toTPKindAlg.chalAss Ch j i v.chal) x).isSome = true
    rw [A.toTPKindAlg.chalAss_of_not_live Ch j i v.chal hv, lastAssign_paddingAssignments]
    rfl
  · rw [hG]
    refine ⟨KrausMap.tp_ofPerm _, fun i' hi' r p' p h => ?_, A.Good Ch (j + 1),
      fun r p' p hp h => ?_, subset_rfl⟩
    · rw [A.ofPerm_ne_zero Ch h]
      exact A.recSet_congr_query Ch j i.isLt hi' rfl rfl
        (fun j' i'' hne => A.garSwap_queries Ch j i p j' i'' hne)
    · rw [A.ofPerm_ne_zero Ch h]
      exact A.good_congr Ch rfl rfl hp

theorem writeReply_fst (j : Fin A.toTPKindAlg.slots) (p : QueryReg (A.TW Ch) 1 X Y) :
    (A.toTPKindAlg.writeReply Ch j p).1.chal = p.1.chal ∧
      (A.toTPKindAlg.writeReply Ch j p).1.adv.workspace = p.1.adv.workspace := by
  change (if (p.1.chal.logs j).isSome = true then _ else p).1.chal = _ ∧
    (if (p.1.chal.logs j).isSome = true then _ else p).1.adv.workspace = _
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- **Slot `j` carries `Good j` to `Good (j + 1)`.** -/
theorem valid_slotCircBoth (j : Fin A.toTPKindAlg.slots) :
    Valid (A.recSet Ch) (A.supSet Ch) (A.toTPKindAlg.slotCircBoth Ch j)
      ((j : ℕ) * (Ch.q + A.toTPKindAlg.width)) (A.Good Ch j) (A.Good Ch (j + 1)) := by
  refine ⟨A.tp_advKraus Ch _, A.keeps_of_chal Ch _ (fun r p' p h =>
    (A.advKraus_ne_zero Ch h).2.1) _, A.Mid Ch j, A.advKraus_slot_supp Ch j, ?_⟩
  refine ⟨A.tp_measReq Ch j, fun i hi o p' p h => ?_, A.Good Ch (j + 1), A.measReq_supp Ch j, ?_⟩
  · rw [measReq_op_apply Ch (B := A.toTPKindAlg) j o p' p] at h
    have hy : p' = A.toTPKindAlg.copyReq Ch j p := by
      by_contra h'
      exact h (mul_eq_zero_of_left (if_neg h') _)
    subst hy
    change (if A.toTPKindAlg.kind p.1.adv.workspace then
      (⟨p.1.adv, p.1.chal.swapLog j p.1.adv.request⟩, p.2) else p).1 ∈ _ ↔ _
    split_ifs
    · exact A.recSet_congr_below Ch j hi rfl rfl fun j' hj' => by
        simp [ChallengerRegs.swapLog, Function.update_of_ne (ne_of_lt hj')]
    · exact Iff.rfl
  refine Valid.append (A.valid_chalQueries Ch j) ?_
  rw [KindAlg.queries_chalQueries]
  refine ⟨KrausMap.tp_ofPerm _, A.keeps_of_chal Ch _ (fun r p' p h => by
    rw [A.ofPerm_ne_zero Ch h]; exact (A.writeReply_fst Ch j p).1) _, A.Good Ch (j + 1),
    fun r p' p hp h => ?_, ?_⟩
  · rw [A.ofPerm_ne_zero Ch h]
    exact A.good_congr Ch (by rw [(A.writeReply_fst Ch j p).1]) (A.writeReply_fst Ch j p).2 hp
  refine A.valid_advQueries Ch _ _ _ (fun r hr => ?_) (fun r hr v _ hv x => ?_)
    (fun v v' hc hw hv => A.good_congr Ch (by rw [hc]) hw hv)
  · rw [add_assoc]
    exact A.supSet_slot Ch j (by omega)
  · rw [add_assoc, A.recSet_adv Ch j hr] at hv
    simp only [KindAlg.advAss]
    rcases hl : v.chal.logs j with _ | r'
    · exact absurd hl hv
    · simp only
      rw [lastAssign_paddingAssignments]
      rfl

/-- **Post batch `b` keeps `Good slots`.** -/
theorem valid_postCirc (b : Fin A.toTPKindAlg.post) :
    Valid (A.recSet Ch) (A.supSet Ch) (A.toTPKindAlg.postCirc Ch b)
      (A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) + b * A.toTPKindAlg.width)
      (A.Good Ch A.toTPKindAlg.slots) (A.Good Ch A.toTPKindAlg.slots) := by
  refine ⟨A.tp_advKraus Ch _, A.keeps_of_chal Ch _ (fun r p' p h =>
    (A.advKraus_ne_zero Ch h).2.1) _, A.Good Ch A.toTPKindAlg.slots, A.advKraus_post_supp Ch b, ?_⟩
  exact A.valid_advQueries Ch _ _ _ (fun r _ => A.supSet_post Ch (by omega))
    (fun r _ v _ hv => absurd (by rw [A.recSet_post Ch (by omega)]; trivial) hv)
    (fun v v' hc hw hv => A.good_congr Ch (by rw [hc]) hw hv)

theorem queries_tp_fullCircBoth :
    (A.toTPKindAlg.fullCircBoth Ch).queries =
      A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) +
        A.toTPKindAlg.width * A.toTPKindAlg.post :=
  A.toTPKindAlg.queries_fullCircBoth Ch

/-- **The certificate of the trace-preserving composition.** -/
theorem valid_fullCircBoth :
    Valid (A.recSet Ch) (A.supSet Ch) (A.toTPKindAlg.fullCircBoth Ch) 0 (A.Good Ch 0)
      (A.supSet Ch (A.toTPKindAlg.fullCircBoth Ch).queries) := by
  have h1 : Valid (A.recSet Ch) (A.supSet Ch)
      (concat ((List.finRange A.toTPKindAlg.slots).map fun j => A.toTPKindAlg.slotCircBoth Ch j))
      0 (A.Good Ch 0) (A.Good Ch A.toTPKindAlg.slots) :=
    Valid.concat_finRange (L := Ch.q + A.toTPKindAlg.width) (P := A.Good Ch)
      (fun j => A.toTPKindAlg.queries_slotCircBoth Ch j)
      fun j => by simpa using A.valid_slotCircBoth Ch j
  have h2 : Valid (A.recSet Ch) (A.supSet Ch)
      (concat ((List.finRange A.toTPKindAlg.post).map (A.toTPKindAlg.postCirc Ch)))
      (0 + A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width)) (A.Good Ch A.toTPKindAlg.slots)
      (A.Good Ch A.toTPKindAlg.slots) :=
    Valid.concat_finRange (L := A.toTPKindAlg.width) (P := fun _ => A.Good Ch A.toTPKindAlg.slots)
      (fun b => A.toTPKindAlg.queries_postCirc Ch b)
      fun b => by simpa using A.valid_postCirc Ch b
  rw [A.queries_tp_fullCircBoth Ch, A.supSet_post Ch (by omega)]
  unfold KindAlg.fullCircBoth
  refine Valid.append (Q := A.Good Ch A.toTPKindAlg.slots)
    (Valid.append (Q := A.Good Ch A.toTPKindAlg.slots) h1 ?_) ?_
  · rw [queries_concat_finRange (fun j => A.toTPKindAlg.queries_slotCircBoth Ch j)]
    exact h2
  · rw [queries_append, queries_concat_finRange (fun j => A.toTPKindAlg.queries_slotCircBoth Ch j),
      queries_concat_finRange (fun b => A.toTPKindAlg.queries_postCirc Ch b)]
    exact ⟨A.tp_advKraus Ch _, A.keeps_of_chal Ch _ (fun r p' p h =>
      (A.advKraus_ne_zero Ch h).2.1) _, A.Good Ch A.toTPKindAlg.slots, A.advKraus_last_supp Ch,
      subset_rfl⟩

end Certificate

/-! #### The initial state and the count -/

section Count

variable [Nonempty X] [AddCommGroup Y] [Nonempty Y]

/-- The initial state of the composition lies in `Good 0`: blank logs and counter `0`. -/
theorem initSys_good (p : QueryReg (A.TW Ch) 1 X Y)
    (hp : (A.toTPKindAlg.initSys Ch).mat p p ≠ 0) : p.1 ∈ A.Good Ch 0 := by
  classical
  simp only [KindAlg.initSys, MState.mix, MState.reindex, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, MState.tensorKet_mat, Matrix.kroneckerMap_apply] at hp
  obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  have hω' := right_ne_zero_of_mul (right_ne_zero_of_smul hω)
  have hi := left_ne_zero_of_mul (right_ne_zero_of_smul hω)
  rw [Matrix.single_apply] at hω'
  have hrest : ((A.toTPKindAlg.advSplit Ch).symm p).2 =
      (⟨fun _ => none, fun _ _ => (KindAlg.x₀, 0), ω⟩, fun _ => (KindAlg.x₀, 0)) := by
    by_contra hne
    exact hω' (if_neg fun h => hne h.1.symm)
  have hlogs : p.1.chal.logs = fun _ => none := by
    have := congrArg (fun r => r.1.logs) hrest
    exact this
  have hc : p.1.adv.workspace.2 = 0 := by
    by_contra hne
    exact hi (A.init_mat_eq_zero p.1.adv p.1.adv (Or.inl hne))
  have hn : A.noneCnt Ch 0 p.1 = 0 := by
    unfold noneCnt
    simp
  refine ⟨by rw [hn]; exact Nat.zero_le _, fun j _ => by rw [hlogs], fun _ => ?_⟩
  rw [hn, hc]
  rfl

/-- **The per-branch count of the composition**: before any query, at most
`width * budget + Q * q + width * post` of the queries so far are records. -/
theorem count_le (k : ℕ) (hk : k ≤ (A.toTPKindAlg.fullCircBoth Ch).queries) (w : A.TW Ch)
    (hw : w ∈ A.supSet Ch k) :
    GordieHowe.QROM.countBelow (A.recSet Ch) (min (k + 1) (A.toTPKindAlg.fullCircBoth Ch).queries) w ≤
      A.width * A.budget + Ch.Q * Ch.q + A.width * A.post := by
  have hL := A.slotLen_pos Ch
  rw [A.queries_tp_fullCircBoth Ch] at hk ⊢
  by_cases hS : k < A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width)
  · unfold supSet at hw
    rw [if_pos hS] at hw
    set n := k / (Ch.q + A.toTPKindAlg.width) + 1
    have hn : n ≤ A.toTPKindAlg.slots := A.div_lt_slots Ch hS
    have hkn : min (k + 1) (A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) +
        A.toTPKindAlg.width * A.toTPKindAlg.post) ≤ n * (Ch.q + A.toTPKindAlg.width) := by
      have h1 := Nat.div_add_mod k (Ch.q + A.toTPKindAlg.width)
      have h2 := Nat.mod_lt k hL
      have h3 : n * (Ch.q + A.toTPKindAlg.width) =
          (Ch.q + A.toTPKindAlg.width) * (k / (Ch.q + A.toTPKindAlg.width)) +
            (Ch.q + A.toTPKindAlg.width) := by
        simp only [n]
        ring
      rw [h3]
      omega
    obtain ⟨g1, -, -⟩ := hw
    have := (GordieHowe.QROM.countBelow_mono _ hkn w).trans (A.countBelow_slots_le Ch w n hn)
    have hans := A.ansCnt_le Ch n hn w
    calc _ ≤ Ch.q * A.ansCnt Ch n w + A.toTPKindAlg.width * A.noneCnt Ch n w := this
      _ ≤ Ch.q * Ch.Q + A.toTPKindAlg.width * A.budget := by
          gcongr
      _ ≤ _ := by
          change Ch.q * Ch.Q + A.width * A.budget ≤ _
          rw [mul_comm Ch.q Ch.Q]
          omega
  · unfold supSet at hw
    rw [if_neg hS] at hw
    obtain ⟨g1, -, -⟩ := hw
    have h1 := GordieHowe.QROM.countBelow_mono (A.recSet Ch) (min_le_right (k + 1)
      (A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) +
        A.toTPKindAlg.width * A.toTPKindAlg.post)) w
    rw [countBelow_add] at h1
    have h2 := A.countBelow_slots_le Ch w A.toTPKindAlg.slots le_rfl
    have h3 := countBelow_le_of_forall (fun r => A.recSet Ch
      (A.toTPKindAlg.slots * (Ch.q + A.toTPKindAlg.width) + r))
      (A.toTPKindAlg.width * A.toTPKindAlg.post) w
    have hans := A.ansCnt_le Ch A.toTPKindAlg.slots le_rfl w
    have h4 : Ch.q * A.ansCnt Ch A.toTPKindAlg.slots w ≤ Ch.Q * Ch.q := by
      rw [mul_comm]
      exact Nat.mul_le_mul_right _ hans
    have h5 : A.toTPKindAlg.width * A.noneCnt Ch A.toTPKindAlg.slots w ≤
        A.toTPKindAlg.width * A.budget := Nat.mul_le_mul_left _ g1
    change _ ≤ A.toTPKindAlg.width * A.budget + Ch.Q * Ch.q +
      A.toTPKindAlg.width * A.toTPKindAlg.post
    omega

end Count

/-- **The per-branch query count of the trace-preserving composition** (CMS19 Lemma 5.9 with a
per-branch count, `QueryCount`): the coherent pure algorithm (`Alg.toQueryAlgCoh`) of the
composition of the trace-preserving form with a challenger, with any output, has at most `width * budget + Q * q + width * post` unpadded
queries on each branch, whatever the number of slots. -/
noncomputable def tpQueryCount {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] {B : Type} (e : GordieHowe.QROM.BitStr I J ≃ B)
    (A : AdaptiveIAlg (GordieHowe.QROM.Bits m) (GordieHowe.QROM.BitStr I J) Req Resp O)
    (Ch : Challenger (GordieHowe.QROM.Bits m) (GordieHowe.QROM.BitStr I J) Req Resp) {O' O'' : Type}
    (f : A.toKindAlg.CW Ch → O') (g : Option O' → O'') :
    GordieHowe.QROM.QueryCount e ((A.toTPKindAlg.composeBothOut Ch f).toQueryAlgCoh.mapOut g)
      (A.width * A.budget + Ch.Q * Ch.q + A.width * A.post) :=
  GordieHowe.QROM.compiledQueryCount e (A.toTPKindAlg.fullCircBoth Ch) KindAlg.x₀
    (A.toTPKindAlg.initSys Ch) (fun v => f v.1) g (A.valid_fullCircBoth Ch)
    (fun p hp => A.initSys_good Ch p hp) (fun k hk w hw => A.count_le Ch k hk w hw)

end AdaptiveIAlg

end GordieHowe.Quantum
