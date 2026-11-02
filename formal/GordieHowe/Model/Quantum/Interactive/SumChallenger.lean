-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.MultiRelay

@[expose] public section

/-!
# The sum of two challengers

`Challenger.sum C₁ C₂`: a challenger answering requests of `Req₁ ⊕ Req₂`, a left request by `C₁`
and a right request by `C₂`, each on its own coins and on the entries of the history with its own
requests (`leftHist`, `rightHist`), with its reply tagged by the side. It answers `C₁.Q + C₂.Q`
requests; each part caps its own requests through its history. Our construction, for an
adversary whose requests go to two challengers (the multi-user challenger and a challenger of proof
queries).

- `leftHist`, `rightHist`: the entries of a history with left (right) requests, the replies read
  back on that side.
- `Challenger.sum`.
- `length_filterMap_getLeft_add`: a request list is as long as its left and right parts together.
- `Challenger.NoAssign.sum`: the sum of two challengers that never reprogram never reprograms.
  `Challenger.NoAssign.hist_oracleIn_sum`: after the requests `L` (each part within its
  challenger's count), the history's left (right) entries are the history of `C₁` (`C₂`) after
  the left (right) part of `L`. `Challenger.NoAssign.answerAfter_sum_inl`,
  `Challenger.NoAssign.answerAfter_sum_inr`: the sum's reply to a left (right) request after `L`
  is `C₁`'s (`C₂`'s) reply after the left (right) part of `L`, tagged.
-/

namespace GordieHowe.Quantum

variable {X Y Req₁ Resp₁ Req₂ Resp₂ : Type}

/-- **The entries of a history with left requests**, the replies read on the left. -/
def leftHist :
    List (HistoryEntry (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂)) → List (HistoryEntry Req₁ Resp₁) :=
  List.filterMap fun e => match e.request with
    | .inl r => some ⟨r, e.response.bind Sum.getLeft?⟩
    | .inr _ => none

/-- **The entries of a history with right requests**, the replies read on the right. -/
def rightHist :
    List (HistoryEntry (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂)) → List (HistoryEntry Req₂ Resp₂) :=
  List.filterMap fun e => match e.request with
    | .inl _ => none
    | .inr r => some ⟨r, e.response.bind Sum.getRight?⟩

/-- **The sum of two challengers**: a left request answered by `C₁` on its coins and the history's
left entries, a right request by `C₂` on its coins and the right entries; the replies tagged by
the side, the assignments kept. -/
noncomputable def Challenger.sum (C₁ : Challenger X Y Req₁ Resp₁) (C₂ : Challenger X Y Req₂ Resp₂) :
    Challenger X Y (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂) where
  Coins := C₁.Coins × C₂.Coins
  coins := C₁.coins.bind fun c₁ => C₂.coins.map fun c₂ => (c₁, c₂)
  Q := C₁.Q + C₂.Q
  q := max C₁.q C₂.q
  respond ω hist
    | .inl r => (C₁.respond ω.1 (leftHist hist) r).mapOutput fun p =>
        ⟨p.response.map Sum.inl, p.assignments⟩
    | .inr r => (C₂.respond ω.2 (rightHist hist) r).mapOutput fun p =>
        ⟨p.response.map Sum.inr, p.assignments⟩
  respond_queries ω hist r H := by
    rcases r with r | r
    · rw [OracleProg.trace_mapOutput]
      exact (C₁.respond_queries _ _ _ H).trans (le_max_left _ _)
    · rw [OracleProg.trace_mapOutput]
      exact (C₂.respond_queries _ _ _ H).trans (le_max_right _ _)

/-- **A request list is as long as its left and right parts together.** -/
theorem length_filterMap_getLeft_add (L : List (Req₁ ⊕ Req₂)) :
    (L.filterMap Sum.getLeft?).length + (L.filterMap Sum.getRight?).length = L.length := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    rcases r with r | r
    · simp only [List.filterMap_cons, Sum.getLeft?_inl, Sum.getRight?_inl, List.length_cons]
      omega
    · simp only [List.filterMap_cons, Sum.getLeft?_inr, Sum.getRight?_inr, List.length_cons]
      omega

/-- A left reply read back on the left. -/
theorem bind_getLeft?_map_inl {α β : Type} (o : Option α) :
    (o.map (Sum.inl : α → α ⊕ β)).bind Sum.getLeft? = o := by
  cases o <;> rfl

/-- A right reply read back on the right. -/
theorem bind_getRight?_map_inr {α β : Type} (o : Option β) :
    (o.map (Sum.inr : β → α ⊕ β)).bind Sum.getRight? = o := by
  cases o <;> rfl

/-- The left entries of a history extended by a left request. -/
theorem leftHist_append_inl (hist : List (HistoryEntry (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂))) (r : Req₁)
    (o : Option (Resp₁ ⊕ Resp₂)) :
    leftHist (hist ++ [⟨.inl r, o⟩]) = leftHist hist ++ [⟨r, o.bind Sum.getLeft?⟩] := by
  simp [leftHist, List.filterMap_append]

/-- The left entries of a history extended by a right request. -/
theorem leftHist_append_inr (hist : List (HistoryEntry (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂))) (r : Req₂)
    (o : Option (Resp₁ ⊕ Resp₂)) : leftHist (hist ++ [⟨.inr r, o⟩]) = leftHist hist := by
  simp [leftHist, List.filterMap_append]

/-- The right entries of a history extended by a left request. -/
theorem rightHist_append_inl (hist : List (HistoryEntry (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂)))
    (r : Req₁) (o : Option (Resp₁ ⊕ Resp₂)) :
    rightHist (hist ++ [⟨.inl r, o⟩]) = rightHist hist := by
  simp [rightHist, List.filterMap_append]

/-- The right entries of a history extended by a right request. -/
theorem rightHist_append_inr (hist : List (HistoryEntry (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂)))
    (r : Req₂) (o : Option (Resp₁ ⊕ Resp₂)) :
    rightHist (hist ++ [⟨.inr r, o⟩]) = rightHist hist ++ [⟨r, o.bind Sum.getRight?⟩] := by
  simp [rightHist, List.filterMap_append]

section NoAssign

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] {C₁ : Challenger X Y Req₁ Resp₁}
  {C₂ : Challenger X Y Req₂ Resp₂}

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] in
/-- **The sum of two challengers that never reprogram never reprograms.** -/
theorem Challenger.NoAssign.sum (h₁ : C₁.NoAssign) (h₂ : C₂.NoAssign) :
    (Challenger.sum C₁ C₂).NoAssign := by
  rintro c hist (r | r) G
  · simp only [Challenger.sum, OracleProg.run_mapOutput]
    exact h₁ _ _ _ _
  · simp only [Challenger.sum, OracleProg.run_mapOutput]
    exact h₂ _ _ _ _

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] in
/-- The sum's reply to a left request is `C₁`'s on the left entries, tagged. -/
theorem Challenger.response_sum_inl (c : C₁.Coins × C₂.Coins)
    (hist : List (HistoryEntry (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂))) (r : Req₁) (G : X → Y) :
    (((Challenger.sum C₁ C₂).respond c hist (.inl r)).run G).response =
      ((C₁.respond c.1 (leftHist hist) r).run G).response.map Sum.inl := by
  simp only [Challenger.sum, OracleProg.run_mapOutput]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] in
/-- The sum's reply to a right request is `C₂`'s on the right entries, tagged. -/
theorem Challenger.response_sum_inr (c : C₁.Coins × C₂.Coins)
    (hist : List (HistoryEntry (Req₁ ⊕ Req₂) (Resp₁ ⊕ Resp₂))) (r : Req₂) (G : X → Y) :
    (((Challenger.sum C₁ C₂).respond c hist (.inr r)).run G).response =
      ((C₂.respond c.2 (rightHist hist) r).run G).response.map Sum.inr := by
  simp only [Challenger.sum, OracleProg.run_mapOutput]

/-- **The histories of the parts of a sum** of challengers that never reprogram: after the
requests `L`, whose left (right) part has at most `C₁.Q` (`C₂.Q`) requests, the history's left
(right) entries are the history of `C₁` (`C₂`) after the left (right) part, on its coins. -/
theorem Challenger.NoAssign.hist_oracleIn_sum (h₁ : C₁.NoAssign) (h₂ : C₂.NoAssign) (H : X → Y)
    (c : C₁.Coins × C₂.Coins) (L : List (Req₁ ⊕ Req₂))
    (hl : (L.filterMap Sum.getLeft?).length ≤ C₁.Q)
    (hr : (L.filterMap Sum.getRight?).length ≤ C₂.Q) :
    leftHist ((Challenger.sum C₁ C₂).toPureEnv.oracleIn (H, c) L).hist =
        (C₁.toPureEnv.oracleIn (H, c.1) (L.filterMap Sum.getLeft?)).hist ∧
      rightHist ((Challenger.sum C₁ C₂).toPureEnv.oracleIn (H, c) L).hist =
        (C₂.toPureEnv.oracleIn (H, c.2) (L.filterMap Sum.getRight?)).hist := by
  induction L using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton L r ih =>
    have hlen := length_filterMap_getLeft_add L
    obtain ⟨hb, ha, -⟩ := (h₁.sum h₂).oracleIn H c L
    rcases r with r | r
    · simp only [List.filterMap_append, List.filterMap_cons, Sum.getLeft?_inl,
        Sum.getRight?_inl, List.filterMap_nil, List.append_nil, List.length_append,
        List.length_singleton] at hl hr ⊢
      obtain ⟨ih1, ih2⟩ := ih (by omega) hr
      obtain ⟨hb₁, ha₁, -⟩ := h₁.oracleIn H c.1 (L.filterMap Sum.getLeft?)
      have hLQ : L.length < (Challenger.sum C₁ C₂).Q := by
        change _ < C₁.Q + C₂.Q
        omega
      rw [Env.oracleIn_append_singleton, Env.oracleIn_append_singleton,
        Challenger.update_toPureEnv_of_lt _ _ _ _ hLQ,
        Challenger.update_toPureEnv_of_lt _ _ _ _
          (by omega : (L.filterMap Sum.getLeft?).length < C₁.Q)]
      dsimp only
      rw [leftHist_append_inl, rightHist_append_inl, ih2, Challenger.response_sum_inl, hb, ha, ih1,
        hb₁, ha₁, bind_getLeft?_map_inl]
      exact ⟨rfl, rfl⟩
    · simp only [List.filterMap_append, List.filterMap_cons, Sum.getLeft?_inr,
        Sum.getRight?_inr, List.filterMap_nil, List.append_nil, List.length_append,
        List.length_singleton] at hl hr ⊢
      obtain ⟨ih1, ih2⟩ := ih hl (by omega)
      obtain ⟨hb₂, ha₂, -⟩ := h₂.oracleIn H c.2 (L.filterMap Sum.getRight?)
      have hLQ : L.length < (Challenger.sum C₁ C₂).Q := by
        change _ < C₁.Q + C₂.Q
        omega
      rw [Env.oracleIn_append_singleton, Env.oracleIn_append_singleton,
        Challenger.update_toPureEnv_of_lt _ _ _ _ hLQ,
        Challenger.update_toPureEnv_of_lt _ _ _ _
          (by omega : (L.filterMap Sum.getRight?).length < C₂.Q)]
      dsimp only
      rw [leftHist_append_inr, rightHist_append_inr, ih1, Challenger.response_sum_inr, hb, ha, ih2,
        hb₂, ha₂, bind_getRight?_map_inr]
      exact ⟨rfl, rfl⟩

/-- **The sum's reply to a left request** after the requests `L`, whose left part has fewer than
`C₁.Q` requests and right part at most `C₂.Q`: `C₁`'s reply after the left part, tagged. -/
theorem Challenger.NoAssign.answerAfter_sum_inl (h₁ : C₁.NoAssign) (h₂ : C₂.NoAssign) (H : X → Y)
    (c : C₁.Coins × C₂.Coins) (L : List (Req₁ ⊕ Req₂)) (r : Req₁)
    (hl : (L.filterMap Sum.getLeft?).length < C₁.Q)
    (hr : (L.filterMap Sum.getRight?).length ≤ C₂.Q) :
    (Challenger.sum C₁ C₂).toPureEnv.answerAfter (H, c) L (.inl r) =
      (C₁.toPureEnv.answerAfter (H, c.1) (L.filterMap Sum.getLeft?) r).map Sum.inl := by
  have hlen := length_filterMap_getLeft_add L
  have hLQ : L.length < (Challenger.sum C₁ C₂).Q := by
    change _ < C₁.Q + C₂.Q
    omega
  rw [(h₁.sum h₂).answerAfter_eq H c L _ hLQ, h₁.answerAfter_eq H c.1 _ r hl,
    ← (h₁.hist_oracleIn_sum h₂ H c L hl.le hr).1]
  simp only [Challenger.sum, OracleProg.run_mapOutput]

/-- **The sum's reply to a right request** after the requests `L`, whose left part has at most
`C₁.Q` requests and right part fewer than `C₂.Q`: `C₂`'s reply after the right part, tagged. -/
theorem Challenger.NoAssign.answerAfter_sum_inr (h₁ : C₁.NoAssign) (h₂ : C₂.NoAssign) (H : X → Y)
    (c : C₁.Coins × C₂.Coins) (L : List (Req₁ ⊕ Req₂)) (r : Req₂)
    (hl : (L.filterMap Sum.getLeft?).length ≤ C₁.Q)
    (hr : (L.filterMap Sum.getRight?).length < C₂.Q) :
    (Challenger.sum C₁ C₂).toPureEnv.answerAfter (H, c) L (.inr r) =
      (C₂.toPureEnv.answerAfter (H, c.2) (L.filterMap Sum.getRight?) r).map Sum.inr := by
  have hlen := length_filterMap_getLeft_add L
  have hLQ : L.length < (Challenger.sum C₁ C₂).Q := by
    change _ < C₁.Q + C₂.Q
    omega
  rw [(h₁.sum h₂).answerAfter_eq H c L _ hLQ, h₂.answerAfter_eq H c.2 _ r hr,
    ← (h₁.hist_oracleIn_sum h₂ H c L hl hr.le).2]
  simp only [Challenger.sum, OracleProg.run_mapOutput]

end NoAssign

end GordieHowe.Quantum
