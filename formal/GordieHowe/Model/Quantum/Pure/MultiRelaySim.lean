-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelay

@[expose] public section

/-!
# The reply of a relayed request whose program keeps its budgets

The reply `MultiRelay.runReply` of a relayed request, computed sub-slot by sub-slot with the
budgets of `K` main requests and `qR` queries, is the result of its program run against the main
replies whenever that run keeps the budgets.

- `MultiRelay.ProgRun ansM H rs p res`: a run of the program `p` against the oracle `H` and the
  main replies `ansM` after the main requests `rs`: its actions, the answers fed to it (each the
  answer of its action after the earlier main requests, `answerOf`), and its result `res`.
  Constructions: `ProgRun.pure`, `ProgRun.query`, `ProgRun.bind`, `ProgRun.liftQ` (a program that
  only queries the oracle, `MultiRelay.liftQ`).
- `MultiRelay.runAux_progRun`, `MultiRelay.runReply_eq_of_progRun`: the relay follows such a run
  with at most `K` main requests (`asksOf`) and `qR` queries (`qryOf`), and replies with its result.
- `MultiRelay.RunsWith ansM H rs p res asks q`: a run with the main requests `asks` and at most `q`
  queries; `RunsWith.pure`, `query_inl`, `query_inr`, `bind`, `mapOutput`, `liftQ`, `mono`;
  `MultiRelay.runReply_eq_of_runsWith`.
- `MultiRelay.AsksIn Resp' p P`: every main request `p` can make satisfies `P`; `AsksIn.pure`,
  `query`, `bind`, `mapOutput`, `liftQ`, `bind_allOut` (the continuation only on the outputs on
  every path, `OracleProg.AllOut`), `translate_inl` (a program of oracle reads).
-/

namespace GordieHowe.Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)

/-- The main requests among actions. -/
def asksOf (acts : List (X ⊕ Req')) : List Req' := acts.filterMap Sum.getRight?

/-- The queries among actions. -/
def qryOf (acts : List (X ⊕ Req')) : List X := acts.filterMap Sum.getLeft?

theorem length_asksOf_add_qryOf (acts : List (X ⊕ Req')) :
    (asksOf acts).length + (qryOf acts).length = acts.length := by
  induction acts with
  | nil => rfl
  | cons a acts ih =>
    rcases a with x | r'
    · simp only [asksOf, qryOf, List.filterMap_cons, Sum.getRight?_inl, Sum.getLeft?_inl,
        List.length_cons] at ih ⊢
      omega
    · simp only [asksOf, qryOf, List.filterMap_cons, Sum.getRight?_inr, Sum.getLeft?_inr,
        List.length_cons] at ih ⊢
      omega

/-- The answer to an action after the main requests `rs ++ asks`: the oracle's value for a query,
the main reply for a main request. -/
def answerOf (ansM : List Req' → Req' → Option Resp') (H : X → Y) (rs asks : List Req') :
    X ⊕ Req' → Y ⊕ Option Resp'
  | .inl x => .inl (H x)
  | .inr r' => .inr (ansM (rs ++ asks) r')

/-- **A run of a program against the main replies** after the main requests `rs`: its actions
`acts`, the answers `fed` it receives (each the answer of its action after the earlier main
requests), and its result `res` after all of them. -/
structure ProgRun {R : Type} (ansM : List Req' → Req' → Option Resp') (H : X → Y) (rs : List Req')
    (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) (res : R) where
  /-- The actions. -/
  acts : List (X ⊕ Req')
  /-- The answers. -/
  fed : List (Y ⊕ Option Resp')
  length_fed : fed.length = acts.length
  /-- Each action is the program's after the earlier answers. -/
  after_lt : ∀ i (h : i < acts.length), p.after (fed.take i) = .inr acts[i]
  /-- Each answer is the answer of its action after the earlier main requests. -/
  fed_eq : ∀ i (h : i < acts.length),
    fed[i]'(length_fed ▸ h) = answerOf ansM H rs (asksOf (acts.take i)) acts[i]
  /-- The program returns `res` after all the answers. -/
  after_fed : p.after fed = .inl res

theorem asksOf_append (l l' : List (X ⊕ Req')) : asksOf (l ++ l') = asksOf l ++ asksOf l' :=
  List.filterMap_append

theorem qryOf_append (l l' : List (X ⊕ Req')) : qryOf (l ++ l') = qryOf l ++ qryOf l' :=
  List.filterMap_append

theorem length_qryOf_take_lt {acts : List (X ⊕ Req')} {i : ℕ} (h : i < acts.length) {x : X}
    (hx : acts[i] = .inl x) : (qryOf (acts.take i)).length < (qryOf acts).length := by
  have h1 : (qryOf (acts.take (i + 1))).length = (qryOf (acts.take i)).length + 1 := by
    rw [List.take_succ, List.getElem?_eq_getElem h, hx, qryOf_append]
    simp [qryOf]
  have h2 : (qryOf (acts.take (i + 1))).length ≤ (qryOf acts).length :=
    ((List.take_sublist _ _).filterMap _).length_le
  omega

theorem length_asksOf_take_lt {acts : List (X ⊕ Req')} {i : ℕ} (h : i < acts.length) {r' : Req'}
    (hr : acts[i] = .inr r') : (asksOf (acts.take i)).length < (asksOf acts).length := by
  have h1 : (asksOf (acts.take (i + 1))).length = (asksOf (acts.take i)).length + 1 := by
    rw [List.take_succ, List.getElem?_eq_getElem h, hr, asksOf_append]
    simp [asksOf]
  have h2 : (asksOf (acts.take (i + 1))).length ≤ (asksOf acts).length :=
    ((List.take_sublist _ _).filterMap _).length_le
  omega

/-! ### Runs of composed programs -/

/-- `after` of a bind before the first program returns. -/
theorem after_bind_inr {R S : Type} {f : R → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') S} :
    ∀ (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) (ans : List (Y ⊕ Option Resp'))
      {a : X ⊕ Req'}, p.after ans = .inr a → (p.bind f).after ans = .inr a
  | .pure _, _, _, h => by simp at h
  | .query _ _, [], _, h => by
    simp only [OracleProg.bind, OracleProg.after_query_nil, Sum.inr.injEq] at h ⊢
    exact h
  | .query _ k, b :: bs, _, h => by
    simp only [OracleProg.bind, OracleProg.after_query_cons] at h ⊢
    exact after_bind_inr (k b) bs h

/-- `after` of a bind once the first program returned exactly at the end of `ans`. -/
theorem after_bind_inl {R S : Type} {f : R → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') S} :
    ∀ (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) (ans : List (Y ⊕ Option Resp')) {x : R},
      p.after ans = .inl x → (∀ i < ans.length, (p.after (ans.take i)).isRight) →
        ∀ l, (p.bind f).after (ans ++ l) = (f x).after l
  | .pure _, [], _, h, _, l => by
    simp only [OracleProg.after_pure, Sum.inl.injEq] at h
    subst h
    rfl
  | .pure _, _ :: _, _, _, hex, _ => by
    have := hex 0 (by simp)
    simp at this
  | .query _ _, [], _, h, _, _ => by simp at h
  | .query _ k, b :: bs, _, h, hex, l => by
    simp only [OracleProg.after_query_cons] at h
    simp only [OracleProg.bind, List.cons_append, OracleProg.after_query_cons]
    refine after_bind_inl (k b) bs h (fun i hi => ?_) l
    have := hex (i + 1) (by simp; omega)
    simpa using this

/-- A run has not returned before its last answer. -/
theorem ProgRun.isRight_after {R : Type} {ansM : List Req' → Req' → Option Resp'} {H : X → Y}
    {rs : List Req'} {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {res : R}
    (S : ProgRun ansM H rs p res) : ∀ i < S.fed.length, (p.after (S.fed.take i)).isRight :=
  fun i hi => by rw [S.after_lt i (S.length_fed ▸ hi)]; rfl

variable {ansM : List Req' → Req' → Option Resp'} {H : X → Y}

/-- **The run of a program that returns at once.** -/
def ProgRun.pure {R : Type} (rs : List Req') (res : R) :
    ProgRun ansM H rs (OracleProg.pure res) res where
  acts := []
  fed := []
  length_fed := rfl
  after_lt _ h := absurd h (Nat.not_lt_zero _)
  fed_eq _ h := absurd h (Nat.not_lt_zero _)
  after_fed := rfl

/-- **The run of a program that first acts `a`**, from a run of its continuation on the answer. -/
def ProgRun.query {R : Type} {rs : List Req'} (a : X ⊕ Req')
    (k : Y ⊕ Option Resp' → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) {res : R}
    (S : ProgRun ansM H (rs ++ asksOf [a]) (k (answerOf ansM H rs [] a)) res) :
    ProgRun ansM H rs (OracleProg.query a k) res where
  acts := a :: S.acts
  fed := answerOf ansM H rs [] a :: S.fed
  length_fed := by simp [S.length_fed]
  after_lt i h := by
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.take_succ_cons, OracleProg.after_query_cons, List.getElem_cons_succ]
      exact S.after_lt i (by simpa using h)
  fed_eq i h := by
    cases i with
    | zero => simp [asksOf]
    | succ i =>
      have hi : i < S.acts.length := by simpa using h
      simp only [List.getElem_cons_succ, List.take_succ_cons]
      rw [S.fed_eq i hi]
      have : asksOf (a :: S.acts.take i) = asksOf [a] ++ asksOf (S.acts.take i) := by
        rw [← asksOf_append]
        rfl
      rw [this]
      cases S.acts[i]'hi <;> simp [answerOf]
  after_fed := S.after_fed

/-- **The run of a bind**: a run of the first program, then a run of the continuation on its
result after its main requests. -/
def ProgRun.bind {R R' : Type} {rs : List Req'} {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
    {f : R → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R'} {x : R} {res : R'}
    (S₁ : ProgRun ansM H rs p x) (S₂ : ProgRun ansM H (rs ++ asksOf S₁.acts) (f x) res) :
    ProgRun ansM H rs (p.bind f) res where
  acts := S₁.acts ++ S₂.acts
  fed := S₁.fed ++ S₂.fed
  length_fed := by simp [S₁.length_fed, S₂.length_fed]
  after_lt i h := by
    have hl := S₁.length_fed
    by_cases hi : i < S₁.acts.length
    · rw [List.take_append_of_le_length (by omega), List.getElem_append_left hi]
      exact after_bind_inr p _ (S₁.after_lt i hi)
    · have hj : i - S₁.acts.length < S₂.acts.length := by simp at h; omega
      have ht : (S₁.fed ++ S₂.fed).take i = S₁.fed ++ S₂.fed.take (i - S₁.acts.length) := by
        rw [List.take_append, List.take_of_length_le (by omega), hl]
      rw [ht, after_bind_inl p _ S₁.after_fed S₁.isRight_after, List.getElem_append_right (by omega)]
      exact S₂.after_lt _ hj
  fed_eq i h := by
    have hl := S₁.length_fed
    by_cases hi : i < S₁.acts.length
    · rw [List.getElem_append_left (by omega), S₁.fed_eq i hi,
        List.getElem_append_left hi, List.take_append_of_le_length hi.le]
    · have hj : i - S₁.acts.length < S₂.acts.length := by simp at h; omega
      have ht : (S₁.acts ++ S₂.acts).take i = S₁.acts ++ S₂.acts.take (i - S₁.acts.length) := by
        rw [List.take_append, List.take_of_length_le (by omega)]
      have hg : (S₁.fed ++ S₂.fed)[i]'(by simp [hl, S₂.length_fed] at h ⊢; omega) =
          S₂.fed[i - S₁.acts.length]'(by rw [S₂.length_fed]; exact hj) := by
        rw [List.getElem_append_right (by omega)]
        simp only [hl]
      have ha : (S₁.acts ++ S₂.acts)[i] = S₂.acts[i - S₁.acts.length] :=
        List.getElem_append_right (by omega)
      rw [hg, S₂.fed_eq _ hj, ht, ha, asksOf_append]
      cases S₂.acts[i - S₁.acts.length] <;> simp [answerOf, List.append_assoc]
  after_fed := by
    rw [after_bind_inl p _ S₁.after_fed S₁.isRight_after]
    exact S₂.after_fed

/-- **A program that only queries the oracle, as a relay program**: its queries as relay queries,
answered by the oracle. -/
def liftQ {R : Type} [Zero Y] (q : OracleProg X Y R) : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R :=
  q.translate Sum.inl fun _ b => b.elim id fun _ => 0

/-- **The run of a lifted program**: its queries against the oracle, no main request. -/
def ProgRun.liftQ {R : Type} [Zero Y] : ∀ (rs : List Req') (q : OracleProg X Y R),
    {S : ProgRun ansM H rs (MultiRelay.liftQ (Resp' := Resp') q) (q.run H) //
      S.acts = (q.trace H).map Sum.inl}
  | rs, .pure r => ⟨ProgRun.pure rs r, rfl⟩
  | rs, .query x k =>
    let S := ProgRun.liftQ (rs ++ asksOf [.inl x]) (k (H x))
    ⟨ProgRun.query (.inl x) _ S.1, congrArg _ S.2⟩

/-- The oracle queries among the reads of a relay with side reads. -/
theorem length_filter_isLeft_take_lt {Xs' : Type} {acts : List ((X ⊕ Xs') ⊕ Req')} {i : ℕ}
    (h : i < acts.length) {a : X ⊕ Xs'} (hx : acts[i] = .inl a) {p : X ⊕ Xs' → Bool}
    (hp : p a = true) :
    ((qryOf (acts.take i)).filter p).length < ((qryOf acts).filter p).length := by
  have h1 : ((qryOf (acts.take (i + 1))).filter p).length =
      ((qryOf (acts.take i)).filter p).length + 1 := by
    rw [List.take_succ, List.getElem?_eq_getElem h, hx, qryOf_append]
    simp [qryOf, hp]
  have h2 : ((qryOf (acts.take (i + 1))).filter p).length ≤ ((qryOf acts).filter p).length :=
    (((List.take_sublist _ _).filterMap _).filter _).length_le
  omega

theorem length_filter_isLeft_add_isRight {Xs' : Type} (l : List (X ⊕ Xs')) :
    (l.filter Sum.isLeft).length + (l.filter Sum.isRight).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rcases a with x | x <;> simp [List.filter_cons] <;> omega

/-- **The answers of the oracle and the side function** to the reads of a relay program: an oracle
query `inl x` by `H x`, a side read `inr x` by `s x`. -/
def sideOracle {Xs Ys : Type} (H : X → Y) (s : Xs → Ys) : X ⊕ Xs → Y ⊕ Ys := Sum.map H s

/-! ### The relayed request along a run -/

section RunShape

variable {Xs' : Type}

/-- Whether an action is a side read. -/
def isSideAct : (X ⊕ Xs') ⊕ Req' → Bool
  | .inl (.inr _) => true
  | _ => false

/-- **The pad sub-slots of a run**: one if its first action is a side read. -/
def padOf : List ((X ⊕ Xs') ⊕ Req') → ℕ
  | .inl (.inr _) :: _ => 1
  | _ => 0

/-- **The sub-slot actions of a run**: its oracle queries and main requests. -/
def nsOf (acts : List ((X ⊕ Xs') ⊕ Req')) : ℕ := (acts.filter fun a => !isSideAct a).length

/-- The side reads at the head of a list of actions. -/
def sideRun : List ((X ⊕ Xs') ⊕ Req') → ℕ
  | .inl (.inr _) :: l => sideRun l + 1
  | _ => 0

theorem sideRun_le : ∀ l : List ((X ⊕ Xs') ⊕ Req'), sideRun l ≤ l.length
  | [] => le_rfl
  | .inl (.inl _) :: _ => Nat.zero_le _
  | .inl (.inr _) :: l => by simp only [sideRun, List.length_cons]; have := sideRun_le l; omega
  | .inr _ :: _ => Nat.zero_le _

theorem isSideAct_of_lt_sideRun : ∀ (l : List ((X ⊕ Xs') ⊕ Req')) (k : ℕ) (hk : k < sideRun l),
    isSideAct (l[k]'(lt_of_lt_of_le hk (sideRun_le l))) = true
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | .inl (.inl _) :: _, _, hk => absurd hk (Nat.not_lt_zero _)
  | .inl (.inr _) :: _, 0, _ => rfl
  | .inl (.inr _) :: l, k + 1, hk => isSideAct_of_lt_sideRun l k (by simp [sideRun] at hk; omega)
  | .inr _ :: _, _, hk => absurd hk (Nat.not_lt_zero _)

theorem not_isSideAct_sideRun : ∀ (l : List ((X ⊕ Xs') ⊕ Req')) (h : sideRun l < l.length),
    isSideAct l[sideRun l] = false
  | [], h => absurd h (Nat.not_lt_zero _)
  | .inl (.inl _) :: _, _ => rfl
  | .inl (.inr _) :: l, h => not_isSideAct_sideRun l (by simp [sideRun] at h; omega)
  | .inr _ :: _, _ => rfl

theorem sideRun_eq_zero : ∀ {l : List ((X ⊕ Xs') ⊕ Req')} (h : 0 < l.length),
    isSideAct l[0] = false → sideRun l = 0
  | .inl (.inl _) :: _, _, _ => rfl
  | .inl (.inr _) :: _, _, h => by simp [isSideAct] at h
  | .inr _ :: _, _, _ => rfl

/-- **The end of the side reads from `j`**: the first action at or after `j` that is not a side
read, or the end. -/
def skipSide (acts : List ((X ⊕ Xs') ⊕ Req')) (j : ℕ) : ℕ := j + sideRun (acts.drop j)

theorem le_skipSide (acts : List ((X ⊕ Xs') ⊕ Req')) (j : ℕ) : j ≤ skipSide acts j :=
  Nat.le_add_right _ _

theorem skipSide_le {acts : List ((X ⊕ Xs') ⊕ Req')} {j : ℕ} (hj : j ≤ acts.length) :
    skipSide acts j ≤ acts.length := by
  have := sideRun_le (acts.drop j)
  simp only [List.length_drop] at this
  unfold skipSide
  omega

theorem isSideAct_of_lt_skipSide {acts : List ((X ⊕ Xs') ⊕ Req')} {j l : ℕ} (hjl : j ≤ l)
    (hl : l < skipSide acts j) (hl' : l < acts.length) : isSideAct acts[l] = true := by
  have h1 := isSideAct_of_lt_sideRun (acts.drop j) (l - j) (by unfold skipSide at hl; omega)
  rw [List.getElem_drop] at h1
  simpa [show j + (l - j) = l by omega] using h1

theorem not_isSideAct_skipSide {acts : List ((X ⊕ Xs') ⊕ Req')} {j : ℕ}
    (h : skipSide acts j < acts.length) : isSideAct (acts[skipSide acts j]'h) = false := by
  have hlt : sideRun (acts.drop j) < (acts.drop j).length := by
    simp only [List.length_drop]
    unfold skipSide at h
    omega
  have h1 := not_isSideAct_sideRun (acts.drop j) hlt
  rw [List.getElem_drop] at h1
  simpa [skipSide] using h1

theorem skipSide_of_not {acts : List ((X ⊕ Xs') ⊕ Req')} {j : ℕ} (h : j < acts.length)
    (hns : isSideAct acts[j] = false) : skipSide acts j = j := by
  unfold skipSide
  rw [sideRun_eq_zero (l := acts.drop j) (by simp; omega) (by rw [List.getElem_drop]; simpa using
      hns)]
  rfl

theorem skipSide_of_le {acts : List ((X ⊕ Xs') ⊕ Req')} {j : ℕ} (h : acts.length ≤ j) :
    skipSide acts j = j := by
  unfold skipSide
  rw [List.drop_eq_nil_of_le h]
  rfl

theorem skipSide_skipSide (acts : List ((X ⊕ Xs') ⊕ Req')) (j : ℕ) :
    skipSide acts (skipSide acts j) = skipSide acts j := by
  by_cases h : skipSide acts j < acts.length
  · exact skipSide_of_not h (not_isSideAct_skipSide h)
  · exact skipSide_of_le (by omega)

/-- The sub-slot actions are the main requests and the oracle queries. -/
theorem nsOf_eq (acts : List ((X ⊕ Xs') ⊕ Req')) :
    nsOf acts = (asksOf acts).length + ((qryOf acts).filter Sum.isLeft).length := by
  induction acts with
  | nil => rfl
  | cons a l ih =>
    rcases a with (x | x) | r' <;>
      simp only [nsOf, asksOf, qryOf, isSideAct, List.filter_cons, List.filterMap_cons,
        Sum.getRight?_inl, Sum.getRight?_inr, Sum.getLeft?_inl, Sum.getLeft?_inr, Sum.isLeft_inl,
        Sum.isLeft_inr, Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true,
        List.length_cons] at ih ⊢ <;> omega

theorem nsOf_take_succ {acts : List ((X ⊕ Xs') ⊕ Req')} {l : ℕ} (h : l < acts.length) :
    nsOf (acts.take (l + 1)) = nsOf (acts.take l) + if isSideAct acts[l] then 0 else 1 := by
  rw [List.take_succ, List.getElem?_eq_getElem h]
  simp only [nsOf, Option.toList_some, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  cases isSideAct acts[l] <;> simp

theorem nsOf_take_le (acts : List ((X ⊕ Xs') ⊕ Req')) (l : ℕ) :
    nsOf (acts.take l) ≤ nsOf acts :=
  ((List.take_sublist _ _).filter _).length_le

/-- The side reads keep the sub-slot actions. -/
theorem nsOf_take_skipSide {acts : List ((X ⊕ Xs') ⊕ Req')} {j : ℕ} (hj : j ≤ acts.length) :
    ∀ l, j ≤ l → l ≤ skipSide acts j → nsOf (acts.take l) = nsOf (acts.take j) := by
    intro l
    induction l with
    | zero => intro hjl _; rw [Nat.le_zero.1 hjl]
    | succ l ih =>
      intro hjl hl
      by_cases hjl' : j = l + 1
      · rw [hjl']
      · have hlt : l < acts.length := lt_of_lt_of_le hl (skipSide_le hj)
        rw [nsOf_take_succ hlt, isSideAct_of_lt_skipSide (j := j) (l := l) (by omega) (by omega)
            hlt, if_pos rfl,
          Nat.add_zero, ih (by omega) (by omega)]

/-- The side reads keep the main requests. -/
theorem asksOf_take_skipSide {acts : List ((X ⊕ Xs') ⊕ Req')} {j : ℕ} (hj : j ≤ acts.length) :
    ∀ l, j ≤ l → l ≤ skipSide acts j → asksOf (acts.take l) = asksOf (acts.take j) := by
    intro l
    induction l with
    | zero => intro hjl _; rw [Nat.le_zero.1 hjl]
    | succ l ih =>
      intro hjl hl
      by_cases hjl' : j = l + 1
      · rw [hjl']
      · have hlt : l < acts.length := lt_of_lt_of_le hl (skipSide_le hj)
        have hside := isSideAct_of_lt_skipSide (j := j) (l := l) (by omega) (by omega) hlt
        rw [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some, asksOf_append,
          ih (by omega) (by omega)]
        rcases ha : acts[l] with (x | x) | r' <;> simp [ha, isSideAct, asksOf] at hside ⊢

/-- The first action of a run is a side read exactly when it has a pad sub-slot. -/
theorem padOf_eq_one {acts : List ((X ⊕ Xs') ⊕ Req')} (h : 0 < acts.length) :
    padOf acts = if isSideAct acts[0] then 1 else 0 := by
  rcases acts with _ | ⟨(x | x) | r', l⟩
  · simp at h
  all_goals rfl

end RunShape

variable [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

variable {ansM : List Req' → Req' → Option Resp'} {H : X → Y} {r : Req} {rs : List Req'}
  {res : Option Resp}

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The relay's state after the first `j` actions of a run** and `np` pad sub-slots. -/
def runSt (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) (j np : ℕ) :
    RelaySt Y Resp' Ys :=
  ⟨S.fed.take j, (asksOf (S.acts.take j)).length,
    ((qryOf (S.acts.take j)).filter Sum.isLeft).length,
    ((qryOf (S.acts.take j)).filter Sum.isRight).length, np, true⟩

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **The program's action after the first `j` actions of a run**: the run's next action, within
the budgets. -/
theorem progAct_runSt (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) {j : ℕ}
    (hj : j < S.acts.length) (np : ℕ) :
    F.progAct r (F.runSt S j np) = match S.acts[j] with
      | .inl (.inl x) =>
        if ((qryOf (S.acts.take j)).filter Sum.isLeft).length < F.qR then some (.inl (.inl x))
        else none
      | .inl (.inr x) =>
        if ((qryOf (S.acts.take j)).filter Sum.isRight).length < F.qS then some (.inl (.inr x))
        else none
      | .inr r' => if (asksOf (S.acts.take j)).length < F.K then some (.inr r') else none := by
  simp only [progAct, runSt, ↓reduceIte]
  rw [S.after_lt j hj]
  rcases S.acts[j] with (x | x) | r' <;> rfl

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- After all the actions of a run the program has returned. -/
theorem progAct_runSt_end (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) (np : ℕ) :
    F.progAct r (F.runSt S S.acts.length np) = none := by
  simp only [progAct, runSt, ↓reduceIte, List.take_of_length_le S.length_fed.le, S.after_fed]

omit [Inhabited X] [Inhabited Req'] in
theorem fed_take_succ (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) {j : ℕ}
    (hj : j < S.acts.length) :
    S.fed.take (j + 1) =
      S.fed.take j ++ [answerOf ansM (sideOracle H F.side) rs (asksOf (S.acts.take j)) S.acts[j]] :=
          by
  have hfl : j < S.fed.length := S.length_fed ▸ hj
  rw [List.take_succ, List.getElem?_eq_getElem hfl, ← S.fed_eq j hj]
  rfl

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem acts_take_succ (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) {j : ℕ}
    (hj : j < S.acts.length) : S.acts.take (j + 1) = S.acts.take j ++ [S.acts[j]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hj]
  rfl

omit [Inhabited X] [Inhabited Req'] in
/-- **A side read of a run, answered by the side function.** -/
theorem sideStep_runSt (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) {j : ℕ}
    (hj : j < S.acts.length) {x : Xs} (hx : S.acts[j] = .inl (.inr x))
    (hs : ((qryOf (S.acts.take j)).filter Sum.isRight).length < F.qS) (np : ℕ) :
    F.sideStep F.sideSa r (F.runSt S j np) = F.runSt S (j + 1) np := by
  have hpa : F.progAct r (F.runSt S j np) = some (.inl (.inr x)) := by
    rw [F.progAct_runSt S hj, hx]
    simp only
    rw [if_pos hs]
  simp only [sideStep, hpa]
  simp only [runSt, fed_take_succ F S hj, acts_take_succ F S hj, asksOf_append, qryOf_append, hx]
  simp [answerOf, asksOf, qryOf, sideOracle, sideSa, List.filter]

omit [Inhabited X] [Inhabited Req'] in
/-- **The side reads of a run from `j`** up to its next query or main request, answered by the
side function, within the side-read budget. -/
theorem close_runSt (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) {j : ℕ}
    (hj : j ≤ S.acts.length)
    (hs : ((qryOf (S.acts.take (skipSide S.acts j))).filter Sum.isRight).length ≤ F.qS)
    (np : ℕ) :
    F.close F.sideSa r (F.runSt S j np) = F.runSt S (skipSide S.acts j) np := by
  have hsk := skipSide_le hj
  -- the side reads after `j` count one each
  have hcnt : ∀ l, j ≤ l → l ≤ skipSide S.acts j →
      ((qryOf (S.acts.take l)).filter Sum.isRight).length =
        ((qryOf (S.acts.take j)).filter Sum.isRight).length + (l - j) := by
    intro l
    induction l with
    | zero => intro hjl _; rw [Nat.le_zero.1 hjl]; simp
    | succ l ih =>
      intro hjl hl
      by_cases hjl' : j = l + 1
      · subst hjl'; simp
      · have hlt : l < S.acts.length := by omega
        have hside := isSideAct_of_lt_skipSide (acts := S.acts) (j := j) (l := l) (by omega)
          (by omega) hlt
        rw [acts_take_succ F S hlt, qryOf_append]
        rcases ha : S.acts[l] with (x | x) | r'
        · simp [ha, isSideAct] at hside
        · rw [show qryOf [(.inl (.inr x) : (X ⊕ Xs) ⊕ Req')] = [.inr x] from rfl,
            List.filter_append, List.length_append, ih (by omega) (by omega)]
          simp only [List.filter_cons, Sum.isRight_inr, ite_true, List.filter_nil,
            List.length_singleton]
          omega
        · simp [ha, isSideAct] at hside
  have hk : ∀ k, (F.sideStep F.sideSa r)^[k] (F.runSt S j np) =
      F.runSt S (min (j + k) (skipSide S.acts j)) np := by
    intro k
    induction k with
    | zero => rw [Nat.add_zero, min_eq_left (le_skipSide _ _)]; rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases hlt : j + k < skipSide S.acts j
      · rw [min_eq_left hlt.le, min_eq_left (by omega : j + (k + 1) ≤ skipSide S.acts j)]
        have hl : j + k < S.acts.length := by omega
        have hside := isSideAct_of_lt_skipSide (acts := S.acts) (le_add_right le_rfl) hlt hl
        rcases ha : S.acts[j + k] with (x | x) | r'
        · simp [ha, isSideAct] at hside
        · have hc := hcnt (j + k) (by omega) hlt.le
          have hc' := hcnt (skipSide S.acts j) (le_skipSide _ _) le_rfl
          rw [F.sideStep_runSt S hl ha (by omega), Nat.add_assoc]
        · simp [ha, isSideAct] at hside
      · rw [min_eq_right (by omega), min_eq_right (by omega)]
        refine F.sideStep_of_not F.sideSa r _ fun x hx => ?_
        by_cases hend : skipSide S.acts j < S.acts.length
        · rw [F.progAct_runSt S hend] at hx
          have hns := not_isSideAct_skipSide hend
          rcases ha : S.acts[skipSide S.acts j] with (x' | x') | r'
          · simp only [ha] at hx
            split_ifs at hx <;> simp at hx
          · simp [ha, isSideAct] at hns
          · simp only [ha] at hx
            split_ifs at hx <;> simp at hx
        · rw [show skipSide S.acts j = S.acts.length by omega, F.progAct_runSt_end] at hx
          cases hx
  unfold close
  rw [hk, min_eq_right]
  have hc := hcnt _ (le_skipSide _ _) le_rfl
  omega

/-- **The relayed request follows a run of its program within the budgets**: after the pad
sub-slot (if the run begins with a side read) and `i` more sub-slots, the relay's state is that
after a prefix of the run with `i` queries and main requests, followed by all its side reads, and
its entries hold that prefix's main requests. -/
theorem runAux_progRun (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res)
    (hK : (asksOf S.acts).length ≤ F.K) (hq : ((qryOf S.acts).filter Sum.isLeft).length ≤ F.qR)
    (hs : ((qryOf S.acts).filter Sum.isRight).length ≤ F.qS) (hp : padOf S.acts ≤ F.qP) :
    ∀ i ≤ nsOf S.acts, ∃ j ≤ S.acts.length,
      (F.runAux ansM H r rs (padOf S.acts + i)).1 = F.runSt S j (padOf S.acts) ∧
      (F.runAux ansM H r rs (padOf S.acts + i)).2.filterMap Prod.fst = asksOf (S.acts.take j) ∧
      nsOf (S.acts.take j) = i ∧ skipSide S.acts j = j := by
  have hsk : ∀ l, ((qryOf (S.acts.take l)).filter Sum.isRight).length ≤ F.qS := fun l =>
    ((((List.take_sublist _ _).filterMap _).filter _).length_le).trans hs
  intro i
  induction i with
  | zero =>
    intro _
    rcases hpad : padOf S.acts with _ | _ | k
    · refine ⟨0, Nat.zero_le _, rfl, rfl, rfl, ?_⟩
      by_cases h0 : 0 < S.acts.length
      · refine skipSide_of_not h0 ?_
        rw [padOf_eq_one h0] at hpad
        split_ifs at hpad with h
        simpa using h
      · exact skipSide_of_le (by omega)
    · -- the pad sub-slot
      have h0 : 0 < S.acts.length := by
        rcases ha : S.acts with _ | a
        · rw [ha] at hpad; cases hpad
        · simp
      obtain ⟨x, hx⟩ : ∃ x, S.acts[0] = .inl (.inr x) := by
        have := padOf_eq_one h0
        rw [hpad] at this
        rcases ha : S.acts[0] with (x | x) | r'
        · simp [ha, isSideAct] at this
        · exact ⟨x, rfl⟩
        · simp [ha, isSideAct] at this
      have hs0 : 0 < F.qS := by
        have := hsk 1
        rw [acts_take_succ F S h0, List.take_zero, List.nil_append, hx] at this
        have h1 : ((qryOf [(.inl (.inr x) : (X ⊕ Xs) ⊕ Req')]).filter Sum.isRight).length = 1 :=
          rfl
        omega
      have hpa : F.progAct r RelaySt.init = some (.inl (.inr x)) := by
        have := F.progAct_runSt S h0 0
        rw [hx] at this
        simpa [runSt, asksOf, qryOf, hs0, RelaySt.init] using this
      have hq1 : 0 < F.qP := by omega
      have hact : F.act r RelaySt.init = .inl (.inr x) := by
        simp only [act, hpa]
        simp [RelaySt.init, hq1]
      have hnext : F.next r RelaySt.init (none, (default, H default)) = F.runSt S 0 1 := by
        simp only [next, hpa]
        simp [runSt, RelaySt.init, asksOf, qryOf, hq1]
      refine ⟨skipSide S.acts 0, skipSide_le (Nat.zero_le _), ?_, ?_, ?_, skipSide_skipSide _ _⟩
      · simp only [runAux, hact, Nat.zero_add]
        rw [hnext, F.close_runSt S (Nat.zero_le _) (hsk _)]
      · simp only [runAux, hact, Nat.zero_add, List.nil_append, List.filterMap_cons,
          List.filterMap_nil]
        rw [asksOf_take_skipSide (Nat.zero_le _) _ (Nat.zero_le _) le_rfl]
        rfl
      · rw [nsOf_take_skipSide (Nat.zero_le _) _ (Nat.zero_le _) le_rfl]
        rfl
    · exfalso
      have := F.qP_le_one
      omega
  | succ i ih =>
    intro hi
    obtain ⟨j, hj, h1, h2, h3, h4⟩ := ih (by omega)
    have hjl : j < S.acts.length := by
      by_contra hc
      have : j = S.acts.length := by omega
      rw [this, List.take_of_length_le le_rfl] at h3
      omega
    have hns : isSideAct S.acts[j] = false := by
      have := not_isSideAct_skipSide (acts := S.acts) (j := j) (by rw [h4]; exact hjl)
      simpa [h4] using this
    have hsk1 := skipSide_le (acts := S.acts) (j := j + 1) hjl
    have hns1 : nsOf (S.acts.take (j + 1)) = i + 1 := by
      rw [nsOf_take_succ hjl, hns, h3]
      rfl
    have hfin : nsOf (S.acts.take (skipSide S.acts (j + 1))) = i + 1 := by
      rw [nsOf_take_skipSide (j := j + 1) hjl _ (le_skipSide _ _) le_rfl, hns1]
    refine ⟨skipSide S.acts (j + 1), hsk1, ?_, ?_, hfin, skipSide_skipSide _ _⟩ <;>
      rw [← Nat.add_assoc] <;> simp only [runAux, h1] <;>
      rcases ha : S.acts[j] with (x | x) | r'
    · -- a query
      have hqlt := length_filter_isLeft_take_lt hjl ha (p := Sum.isLeft) rfl
      have hpa : F.progAct r (F.runSt S j (padOf S.acts)) = some (.inl (.inl x)) := by
        rw [F.progAct_runSt S hjl, ha]
        simp only
        rw [if_pos (by omega)]
      have hact : F.act r (F.runSt S j (padOf S.acts)) = .inl (.inl x) := by simp [act, hpa]
      simp only [hact]
      have hnx : F.next r (F.runSt S j (padOf S.acts)) (none, (x, H x)) =
          F.runSt S (j + 1) (padOf S.acts) := by
        simp only [next, hpa]
        simp only [runSt, fed_take_succ F S hjl, acts_take_succ F S hjl, asksOf_append,
          qryOf_append, ha]
        simp [answerOf, asksOf, qryOf, sideOracle, List.filter]
      rw [hnx, F.close_runSt (j := j + 1) S hjl (hsk _)]
    · simp [ha, isSideAct] at hns
    · -- a main request
      have halt := length_asksOf_take_lt hjl ha
      have hpa : F.progAct r (F.runSt S j (padOf S.acts)) = some (.inr r') := by
        rw [F.progAct_runSt S hjl, ha]
        simp only
        rw [if_pos (by omega)]
      have hact : F.act r (F.runSt S j (padOf S.acts)) = .inr r' := by simp [act, hpa]
      simp only [hact, h2]
      have hnx : F.next r (F.runSt S j (padOf S.acts))
          (ansM (rs ++ asksOf (S.acts.take j)) r', (default, 0)) =
          F.runSt S (j + 1) (padOf S.acts) := by
        simp only [next, hpa]
        simp only [runSt, fed_take_succ F S hjl, acts_take_succ F S hjl, asksOf_append,
          qryOf_append, ha]
        simp [answerOf, asksOf, qryOf]
      rw [hnx, F.close_runSt (j := j + 1) S hjl (hsk _)]
    · -- a query: the entries
      have hpa : F.progAct r (F.runSt S j (padOf S.acts)) = some (.inl (.inl x)) := by
        rw [F.progAct_runSt S hjl, ha]
        simp only
        rw [if_pos (by have := length_filter_isLeft_take_lt hjl ha (p := Sum.isLeft) rfl; omega)]
      have hact : F.act r (F.runSt S j (padOf S.acts)) = .inl (.inl x) := by simp [act, hpa]
      simp only [hact, List.filterMap_append, h2, List.filterMap_cons, List.filterMap_nil,
        List.append_nil]
      rw [asksOf_take_skipSide (acts := S.acts) (j := j + 1) hjl _ (le_skipSide _ _) le_rfl,
        acts_take_succ F S hjl, asksOf_append, ha]
      simp [asksOf]
    · simp [ha, isSideAct] at hns
    · -- a main request: the entries
      have hpa : F.progAct r (F.runSt S j (padOf S.acts)) = some (.inr r') := by
        rw [F.progAct_runSt S hjl, ha]
        simp only
        rw [if_pos (by have := length_asksOf_take_lt hjl ha; omega)]
      have hact : F.act r (F.runSt S j (padOf S.acts)) = .inr r' := by simp [act, hpa]
      simp only [hact, List.filterMap_append, h2, List.filterMap_cons, List.filterMap_nil]
      rw [asksOf_take_skipSide (acts := S.acts) (j := j + 1) hjl _ (le_skipSide _ _) le_rfl,
        acts_take_succ F S hjl, asksOf_append, ha]
      simp [asksOf]

/-- **After the run's sub-slots** the relay's state is that after all its actions, its entries
holding the run's main requests. -/
theorem runAux_end_progRun (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res)
    (hK : (asksOf S.acts).length ≤ F.K) (hq : ((qryOf S.acts).filter Sum.isLeft).length ≤ F.qR)
    (hs : ((qryOf S.acts).filter Sum.isRight).length ≤ F.qS) (hp : padOf S.acts ≤ F.qP) :
    (F.runAux ansM H r rs (padOf S.acts + nsOf S.acts)).1 = F.runSt S S.acts.length (padOf S.acts) ∧
      (F.runAux ansM H r rs (padOf S.acts + nsOf S.acts)).2.filterMap Prod.fst = asksOf S.acts := by
  obtain ⟨j, hj, h1, h2, h3, h4⟩ := F.runAux_progRun S hK hq hs hp _ le_rfl
  have hjl : j = S.acts.length := by
    by_contra hc
    have hlt : j < S.acts.length := by omega
    have hns : isSideAct S.acts[j] = false := by
      have := not_isSideAct_skipSide (acts := S.acts) (j := j) (by rw [h4]; exact hlt)
      simpa [h4] using this
    have h5 := nsOf_take_succ hlt
    rw [hns, h3] at h5
    have := nsOf_take_le S.acts (j + 1)
    simp at h5
    omega
  subst hjl
  rw [List.take_of_length_le le_rfl] at h2
  exact ⟨h1, h2⟩

omit [Inhabited Req'] in
/-- **No side read is made once the run is fed**: at a state fed all the run's answers, the side
reads change nothing. -/
theorem close_of_ans_fed (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res)
    (sa : ℕ → Xs → Ys) (st : RelaySt Y Resp' Ys) (ha : st.ans = S.fed) : F.close sa r st = st := by
  unfold close
  refine Function.iterate_fixed (F.sideStep_of_not sa r st fun x => ?_) _
  by_cases hl : st.live = true
  · simp only [progAct, hl, ↓reduceIte, ha, S.after_fed]
    simp
  · simp [progAct, hl]

/-- **After the run's actions the relay pads**: the program's answers and its liveness stay. -/
theorem runAux_add_progRun (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res)
    (hK : (asksOf S.acts).length ≤ F.K) (hq : ((qryOf S.acts).filter Sum.isLeft).length ≤ F.qR)
    (hs : ((qryOf S.acts).filter Sum.isRight).length ≤ F.qS) (hp : padOf S.acts ≤ F.qP) :
    ∀ k, (F.runAux ansM H r rs (padOf S.acts + nsOf S.acts + k)).1.ans = S.fed ∧
      (F.runAux ansM H r rs (padOf S.acts + nsOf S.acts + k)).1.live = true
  | 0 => by
    obtain ⟨j, hj, h1, -, h3, h4⟩ := F.runAux_progRun S hK hq hs hp _ le_rfl
    have hjl : j = S.acts.length := by
      by_contra hc
      have hlt : j < S.acts.length := by omega
      have hns : isSideAct S.acts[j] = false := by
        have := not_isSideAct_skipSide (acts := S.acts) (j := j) (by rw [h4]; exact hlt)
        simpa [h4] using this
      have h5 := nsOf_take_succ hlt
      rw [hns, h3] at h5
      have := nsOf_take_le S.acts (j + 1)
      simp at h5
      omega
    rw [Nat.add_zero, h1, hjl]
    exact ⟨List.take_of_length_le S.length_fed.le, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := runAux_add_progRun S hK hq hs hp k
    have hpa : ∀ st : RelaySt Y Resp' Ys, st.live = true → st.ans = S.fed → F.progAct r st = none :=
      fun st hl ha => by simp only [progAct, hl, ↓reduceIte, ha, S.after_fed]
    rw [← Nat.add_assoc]
    simp only [runAux, next, hpa _ h2 h1]
    have hcl : ∀ st : RelaySt Y Resp' Ys, st.ans = S.fed → F.close F.sideSa r st = st :=
      fun st ha => by
        unfold close
        refine Function.iterate_fixed (F.sideStep_of_not F.sideSa r st fun x => ?_) _
        by_cases hl : st.live = true
        · rw [hpa st hl ha]; simp
        · simp [progAct, hl]
    split_ifs
    · rw [hcl]
      · exact ⟨h1, by simp [h2, h1, S.after_fed]⟩
      · exact h1
    · rw [hcl]
      · exact ⟨h1, by simp [h2, h1, S.after_fed]⟩
      · exact h1

/-- **The reply of a relayed request whose program keeps its budgets** (module docstring): if the
program of `r` has a run against the main replies after `rs` (oracle queries answered by `H`,
side reads by the side function) with at most `K` main requests, `qR` oracle queries, `qS` side
reads and `qP` pad sub-slots, the relay's reply is the run's result. -/
theorem runReply_eq_of_progRun (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res)
    (hK : (asksOf S.acts).length ≤ F.K) (hq : ((qryOf S.acts).filter Sum.isLeft).length ≤ F.qR)
    (hs : ((qryOf S.acts).filter Sum.isRight).length ≤ F.qS) (hp : padOf S.acts ≤ F.qP) :
    F.runReply ansM H r rs = res := by
  have hT : padOf S.acts + nsOf S.acts ≤ F.len := by
    rw [nsOf_eq, len]
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hT
  obtain ⟨h1, h2⟩ := F.runAux_add_progRun S hK hq hs hp k
  rw [runReply, hk, reply, if_pos h2, h1, S.after_fed]
  rfl

/-! ### Runs with their main requests and a query bound -/

omit [Inhabited X] [Inhabited Req'] in
variable (ansM H) in
/-- **The program `p` has a run against the main replies after `rs`** with the result `res`, the
main requests `asks`, in order, and at most `q` queries. -/
def RunsWith {R : Type} (rs : List Req') (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) (res : R)
    (asks : List Req') (q : ℕ) : Prop :=
  ∃ S : ProgRun ansM H rs p res, asksOf S.acts = asks ∧ (qryOf S.acts).length ≤ q

omit [Inhabited X] [Inhabited Req'] in
theorem RunsWith.pure {R : Type} (rs : List Req') (res : R) :
    RunsWith ansM H rs (OracleProg.pure res) res [] 0 :=
  ⟨ProgRun.pure rs res, rfl, le_rfl⟩

omit [Inhabited X] [Inhabited Req'] in
theorem RunsWith.mono {R : Type} {rs : List Req'} {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
    {res : R} {asks : List Req'} {q q' : ℕ} (h : RunsWith ansM H rs p res asks q) (hq : q ≤ q') :
    RunsWith ansM H rs p res asks q' :=
  let ⟨S, h1, h2⟩ := h
  ⟨S, h1, h2.trans hq⟩

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- A run after equal main requests. -/
def ProgRun.cast {R : Type} {rs rs' : List Req'}
    {p p' : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {res : R} (h : rs = rs') (hp : p = p')
    (S : ProgRun ansM H rs p res) : ProgRun ansM H rs' p' res :=
  h ▸ hp ▸ S

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem ProgRun.acts_cast {R : Type} {rs rs' : List Req'}
    {p p' : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {res : R} (h : rs = rs') (hp : p = p')
    (S : ProgRun ansM H rs p res) : (S.cast h hp).acts = S.acts := by
  subst h hp
  rfl

omit [Inhabited X] [Inhabited Req'] in
/-- A query, then the continuation on the oracle's value. -/
theorem RunsWith.query_inl {R : Type} {rs : List Req'} (x : X)
    {k : Y ⊕ Option Resp' → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {res : R}
    {asks : List Req'} {q : ℕ} (h : RunsWith ansM H rs (k (.inl (H x))) res asks q) :
    RunsWith ansM H rs (OracleProg.query (.inl x) k) res asks (q + 1) := by
  obtain ⟨S, h1, h2⟩ := h
  have hrs : rs = rs ++ asksOf [(.inl x : X ⊕ Req')] := by simp [asksOf]
  refine ⟨ProgRun.query (.inl x) k (S.cast hrs rfl), ?_, ?_⟩
  · change asksOf (.inl x :: (S.cast hrs rfl).acts) = asks
    rw [ProgRun.acts_cast, ← h1]
    simp only [asksOf, List.filterMap_cons, Sum.getRight?_inl]
  · change (qryOf (.inl x :: (S.cast hrs rfl).acts)).length ≤ q + 1
    rw [ProgRun.acts_cast]
    simp only [qryOf, List.filterMap_cons, Sum.getLeft?_inl, List.length_cons] at h2 ⊢
    omega

omit [Inhabited X] [Inhabited Req'] in
/-- A main request, then the continuation on the main reply. -/
theorem RunsWith.query_inr {R : Type} {rs : List Req'} (r' : Req')
    {k : Y ⊕ Option Resp' → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {res : R}
    {asks : List Req'} {q : ℕ} (h : RunsWith ansM H (rs ++ [r']) (k (.inr (ansM rs r'))) res asks q) :
    RunsWith ansM H rs (OracleProg.query (.inr r') k) res (r' :: asks) q := by
  obtain ⟨S, h1, h2⟩ := h
  have hrs : rs ++ [r'] = rs ++ asksOf [(.inr r' : X ⊕ Req')] := by simp [asksOf]
  have hk : k (.inr (ansM rs r')) = k (answerOf ansM H rs [] (.inr r')) := by
    simp [answerOf]
  refine ⟨ProgRun.query (.inr r') k (S.cast hrs hk), ?_, ?_⟩
  · change asksOf (.inr r' :: (S.cast hrs hk).acts) = r' :: asks
    rw [ProgRun.acts_cast, ← h1]
    simp only [asksOf, List.filterMap_cons, Sum.getRight?_inr]
  · change (qryOf (.inr r' :: (S.cast hrs hk).acts)).length ≤ q
    rw [ProgRun.acts_cast]
    simpa only [qryOf, List.filterMap_cons, Sum.getLeft?_inr] using h2

omit [Inhabited X] [Inhabited Req'] in
/-- A bind: a run of the first program, then of the continuation on its result. -/
theorem RunsWith.bind {R R' : Type} {rs : List Req'}
    {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
    {f : R → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R'} {x : R} {res : R'}
    {asks₁ asks₂ : List Req'} {q₁ q₂ : ℕ} (h₁ : RunsWith ansM H rs p x asks₁ q₁)
    (h₂ : RunsWith ansM H (rs ++ asks₁) (f x) res asks₂ q₂) :
    RunsWith ansM H rs (p.bind f) res (asks₁ ++ asks₂) (q₁ + q₂) := by
  obtain ⟨S₁, h11, h12⟩ := h₁
  obtain ⟨S₂, h21, h22⟩ := h₂
  refine ⟨ProgRun.bind S₁ (S₂.cast (by rw [h11]) rfl), ?_, ?_⟩
  · change asksOf (S₁.acts ++ (S₂.cast _ rfl).acts) = _
    rw [ProgRun.acts_cast, asksOf_append, h11, h21]
  · change (qryOf (S₁.acts ++ (S₂.cast _ rfl).acts)).length ≤ _
    rw [ProgRun.acts_cast, qryOf_append, List.length_append]
    omega

omit [Inhabited X] [Inhabited Req'] in
/-- The output of a run mapped. -/
theorem RunsWith.mapOutput {R R' : Type} {rs : List Req'}
    {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} (g : R → R') {x : R} {asks : List Req'}
    {q : ℕ} (h : RunsWith ansM H rs p x asks q) :
    RunsWith ansM H rs (p.mapOutput g) (g x) asks q := by
  have := h.bind (f := fun r => OracleProg.pure (g r)) (RunsWith.pure _ (g x))
  simp only [List.append_nil, Nat.add_zero] at this
  exact this

omit [Inhabited X] [Inhabited Req'] in
/-- **A lifted program** runs with its oracle queries and no main request. -/
theorem RunsWith.liftQ {R : Type} (rs : List Req') (q : OracleProg X Y R) :
    RunsWith ansM H rs (MultiRelay.liftQ (Resp' := Resp') q) (q.run H) [] (q.trace H).length := by
  obtain ⟨S, hS⟩ := ProgRun.liftQ (ansM := ansM) (H := H) rs q
  refine ⟨S, ?_, ?_⟩
  · rw [hS]
    simp only [asksOf, List.filterMap_map]
    exact List.filterMap_eq_nil_iff.2 fun _ _ => rfl
  · rw [hS]
    simp only [qryOf, List.filterMap_map]
    exact (List.length_filterMap_le _ _).trans (by simp)

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem asksOf_map_inl {Xs' : Type} (acts : List (X ⊕ Req')) :
    asksOf (acts.map (Sum.map (Sum.inl : X → X ⊕ Xs') id)) = asksOf acts := by
  induction acts with
  | nil => rfl
  | cons a l ih =>
    rcases a with x | r' <;>
      simp only [asksOf, List.map_cons, List.filterMap_cons, Sum.map_inl, Sum.map_inr,
        Sum.getRight?_inl, Sum.getRight?_inr, id] at ih ⊢ <;> rw [ih]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem qryOf_map_inl {Xs' : Type} (acts : List (X ⊕ Req')) :
    qryOf (acts.map (Sum.map (Sum.inl : X → X ⊕ Xs') id)) = (qryOf acts).map Sum.inl := by
  induction acts with
  | nil => rfl
  | cons a l ih =>
    rcases a with x | r' <;>
      simp only [qryOf, List.map_cons, List.filterMap_cons, Sum.map_inl, Sum.map_inr,
        Sum.getLeft?_inl, Sum.getLeft?_inr, id, List.map_cons] at ih ⊢ <;> rw [ih]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **A run of a side-read-free program** (`plainProg`), from a run of the program: the same
actions as oracle queries and main requests. -/
def ProgRun.plain {ansM : List Req' → Req' → Option Resp'} {H : X → Y} (s : Xs → Ys)
    {rs : List Req'} {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option Resp)}
    {res : Option Resp} (S : ProgRun ansM H rs p res) :
    ProgRun ansM (sideOracle H s) rs (p.translate (Sum.map Sum.inl id) fun _ b => plainAns b) res
    where
  acts := S.acts.map (Sum.map Sum.inl id)
  fed := S.fed.map (Sum.map Sum.inl id)
  length_fed := by simp [S.length_fed]
  after_lt i h := by
    rw [← List.map_take, OracleProg.after_translate _ _ _ (fun _ b => by rcases b with _ | _ <;>
        rfl),
      S.after_lt i (by simpa using h)]
    simp
  fed_eq i h := by
    have hi : i < S.acts.length := by simpa using h
    simp only [List.getElem_map, ← List.map_take, asksOf_map_inl]
    rw [S.fed_eq i hi]
    rcases S.acts[i] with x | r' <;> rfl
  after_fed := by
    rw [OracleProg.after_translate _ _ _ (fun _ b => by rcases b with _ | _ <;> rfl), S.after_fed]
    rfl

/-- **The reply of a relayed request whose side-read-free program runs within the budgets**
(module docstring): for a relay whose programs are the side-read-free programs of `p`
(`plainProg`), at most `K` main requests and `qR` queries. -/
theorem runReply_eq_of_runsWith {ansM : List Req' → Req' → Option Resp'} {H : X → Y} {r : Req}
    {p : Req → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option Resp)} (hp : F.prog = plainProg p)
    {rs : List Req'} {res : Option Resp} {asks : List Req'} {q : ℕ}
    (h : RunsWith ansM H rs (p r) res asks q) (hK : asks.length ≤ F.K) (hq : q ≤ F.qR) :
    F.runReply ansM H r rs = res := by
  obtain ⟨S, h1, h2⟩ := h
  refine F.runReply_eq_of_progRun ((S.plain F.side).cast (p' := F.prog r) rfl (by rw [hp]; rfl))
    ?_ ?_ ?_ ?_
  · rw [ProgRun.acts_cast]
    exact (asksOf_map_inl _).trans h1 ▸ hK
  · rw [ProgRun.acts_cast]
    change ((qryOf (S.acts.map _)).filter Sum.isLeft).length ≤ _
    rw [qryOf_map_inl, List.filter_map, List.length_map]
    refine le_trans (List.length_filter_le _ _) (h2.trans hq)
  · rw [ProgRun.acts_cast]
    change ((qryOf (S.acts.map _)).filter Sum.isRight).length ≤ _
    rw [qryOf_map_inl, List.filter_map]
    simp [Function.comp_def]
  · rw [ProgRun.acts_cast]
    change padOf (S.acts.map _) ≤ _
    rcases S.acts with _ | ⟨x | r', l⟩ <;> simp [padOf]

/-! ### The main requests a program can make -/

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
variable (Resp') in
/-- **Every main request the program `p` can make satisfies `P`**: after any answers. -/
def AsksIn {R : Type} (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) (P : Req' → Prop) : Prop :=
  ∀ ans r', p.after ans = .inr (.inr r') → P r'

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **A program asking in `P` asks in any weaker `P'`.** -/
theorem AsksIn.mono {R : Type} {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
    {P P' : Req' → Prop} (hp : AsksIn Resp' p P) (h : ∀ r', P r' → P' r') : AsksIn Resp' p P' :=
  fun ans r' ha => h r' (hp ans r' ha)

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem AsksIn.pure {R : Type} (x : R) (P : Req' → Prop) :
    AsksIn Resp' (OracleProg.pure x : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) P :=
  fun _ _ h => by simp at h

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem AsksIn.query {R : Type} {a : X ⊕ Req'}
    {k : Y ⊕ Option Resp' → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {P : Req' → Prop}
    (ha : ∀ r', a = .inr r' → P r') (hk : ∀ b, AsksIn Resp' (k b) P) :
    AsksIn Resp' (OracleProg.query a k) P
  | [], r', h => ha r' (by simpa using h)
  | b :: bs, r', h => hk b bs r' (by simpa using h)

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem AsksIn.bind {R R' : Type} {P : Req' → Prop} :
    ∀ {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
      {f : R → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R'},
      AsksIn Resp' p P → (∀ x, AsksIn Resp' (f x) P) → AsksIn Resp' (p.bind f) P
  | .pure x, _, _, hf => hf x
  | .query a k, f, hp, hf => by
    refine AsksIn.query (fun r' ha => hp [] r' (by simp [ha])) fun b => ?_
    exact AsksIn.bind (fun ans r' h => hp (b :: ans) r' (by simpa using h)) hf

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem AsksIn.mapOutput {R R' : Type} {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
    (g : R → R') {P : Req' → Prop} (hp : AsksIn Resp' p P) : AsksIn Resp' (p.mapOutput g) P :=
  hp.bind fun _ => AsksIn.pure _ P

omit [Inhabited X] [Inhabited Req'] in
/-- A lifted program makes no main request. -/
theorem AsksIn.liftQ {R : Type} (q : OracleProg X Y R) (P : Req' → Prop) :
    AsksIn Resp' (MultiRelay.liftQ (Req' := Req') (Resp' := Resp') q) P := by
  induction q with
  | pure x => exact AsksIn.pure x P
  | query x k ih => exact AsksIn.query (fun r' h => by cases h) fun b => ih _

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **A bind whose continuation asks in `P` on the outputs of `p`**: it suffices for the outputs
on every path (`OracleProg.AllOut`). -/
theorem AsksIn.bind_allOut {R R' : Type} {P : Req' → Prop} {Q : R → Prop} :
    ∀ {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
      {f : R → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R'},
      AsksIn Resp' p P → p.AllOut Q → (∀ x, Q x → AsksIn Resp' (f x) P) →
        AsksIn Resp' (p.bind f) P
  | .pure x, _, _, hq, hf => hf x hq
  | .query a k, f, hp, hq, hf => by
    refine AsksIn.query (fun r' ha => hp [] r' (by simp [ha])) fun b => ?_
    exact AsksIn.bind_allOut (fun ans r' h => hp (b :: ans) r' (by simpa using h)) (hq b) hf

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **A program reading the oracle only** (translated to oracle reads) makes no main request. -/
theorem AsksIn.translate_inl {R : Type} (g : X → (Y ⊕ Option Resp') → Y) (p : OracleProg X Y R)
    (P : Req' → Prop) :
    AsksIn Resp' (p.translate (Sum.inl : X → X ⊕ Req') g) P := by
  induction p with
  | pure x => exact AsksIn.pure x P
  | query x k ih => exact AsksIn.query (fun r' h => by cases h) fun b => ih _

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **A program translated to queries that are no main requests makes no main request.** -/
theorem AsksIn.translate_noMain {A B R : Type} (ι : A → X ⊕ Req') (hι : ∀ a r', ι a ≠ .inr r')
    (g : A → (Y ⊕ Option Resp') → B) (p : OracleProg A B R) (P : Req' → Prop) :
    AsksIn Resp' (p.translate ι g) P := by
  induction p with
  | pure x => exact AsksIn.pure x P
  | query a k ih => exact AsksIn.query (fun r' h => absurd h (hι a r')) fun b => ih _

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **A program translated along a map keeping the main requests** asks the main requests of the
program. -/
theorem AsksIn.translate {X' Y' R : Type} {ι : X ⊕ Req' → X' ⊕ Req'}
    (hι : ∀ a r', ι a = .inr r' → a = .inr r') (g : X ⊕ Req' → Y' ⊕ Option Resp' → Y ⊕ Option Resp')
    {P : Req' → Prop} : ∀ {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R},
      AsksIn Resp' p P → AsksIn Resp' (p.translate ι g) P
  | .pure x, _ => AsksIn.pure x P
  | .query a k, hp => by
    refine AsksIn.query (fun r' h => hp [] r' (by rw [hι a r' h]; rfl)) fun b => ?_
    exact AsksIn.translate hι g fun ans r' h => hp (g a b :: ans) r' (by simpa using h)

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **A side-read-free program** (`plainProg`) asks the main requests of the program. -/
theorem AsksIn.plainProg {R : Type} {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R}
    {P : Req' → Prop} (h : AsksIn Resp' p P) :
    AsksIn Resp' (p.translate (Sum.map (Sum.inl : X → X ⊕ Xs) id) fun _ b => plainAns (Ys := Ys) b)
      P :=
  AsksIn.translate (fun a r' h => by rcases a with x | r'' <;> simp_all) _ h

end MultiRelay

end GordieHowe.Quantum
