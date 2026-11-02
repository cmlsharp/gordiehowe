-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignRelayChal
public import GordieHowe.Model.Quantum.Interactive.MultiRelayPos

@[expose] public section

/-!
# The environments of an assigning relay

- `MultiRelay.filterMap_runEntries_of_runsWith_of_eq`: a relayed request whose program runs with
  exactly `K` main requests sends those.
- `AssignRelay.mainOf_congr`: the main request of a run does not depend on the main replies.
- `AssignRelay.histTab_oracleIn_chalD`: the table recorded in `chalD`'s history is the table of its
  assignments in force.
- `AssignRelay.relaysChallenger_relayOf`: `chalT` is the multi-request relay (`relayOf`) of a main
  challenger that reprograms nothing (`MultiRelay.RelaysChallenger`), when it answers at most as
  many requests as the main challenger.
-/

open Finset

namespace GordieHowe.Quantum

open GordieHowe.OracleProg

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

/-- **A relayed request whose side-read-free program runs with exactly `K` main requests sends
those**: its entries' main requests are the run's. -/
theorem filterMap_runEntries_of_runsWith_of_eq {ansM : List Req' → Req' → Option Resp'}
    {H : X → Y} {r : Req} {p : Req → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option Resp)}
    (hp : F.prog = plainProg p) {rs : List Req'} {res : Option Resp} {asks : List Req'} {q : ℕ}
    (h : RunsWith ansM H rs (p r) res asks q) (hK : asks.length = F.K) (hq : q ≤ F.qR) :
    (F.runEntries ansM H r rs).filterMap Prod.fst = asks := by
  rw [F.filterMap_runEntries_of_runsWith ansM H hp h (le_of_eq hK) hq, hK, Nat.sub_self,
    List.replicate_zero, List.append_nil]

end MultiRelay

namespace OracleProg

variable {X Xs Y Ys Req' Resp' R : Type}

/-- The oracle reads among the reads of a relay program's actions. -/
theorem length_filter_isLeft_qryOf (l : List ((X ⊕ Xs) ⊕ Req')) :
    ((Quantum.MultiRelay.qryOf l).filter Sum.isLeft).length = (l.filter isRead).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases a with (x | x) | r' <;>
      simp [Quantum.MultiRelay.qryOf, isRead, List.filter_cons, List.filterMap_cons] at ih ⊢ <;>
      omega

/-- The side reads among the reads of a relay program's actions. -/
theorem length_filter_isRight_qryOf (l : List ((X ⊕ Xs) ⊕ Req')) :
    ((Quantum.MultiRelay.qryOf l).filter Sum.isRight).length = (l.filter isSideRead).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases a with (x | x) | r' <;>
      simp [Quantum.MultiRelay.qryOf, isSideRead, List.filter_cons, List.filterMap_cons] at ih ⊢ <;>
      omega

/-- **The pad sub-slots of a program's trace**: one if it begins with a side read. -/
theorem padOf_trace (o : (X ⊕ Xs) ⊕ Req' → (Y ⊕ Ys) ⊕ Option Resp') :
    ∀ p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R,
      Quantum.MultiRelay.padOf (p.trace o) = if p.startsSide then 1 else 0
  | .pure _ => rfl
  | .query a k => by rcases a with (x | x) | r' <;> rfl

/-- Recording the main request keeps the first query. -/
theorem startsSide_recMain (T : X ⊕ Xs → Option (Y ⊕ Ys)) :
    ∀ p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R,
      (recMain T p).startsSide = p.startsSide
  | .pure _ => rfl
  | .query a k => by rcases a with (x | x) | r' <;> rfl

/-- Mapping the output keeps the first query. -/
theorem startsSide_mapOutput {R' : Type} (f : R → R') :
    ∀ p : OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R,
      (p.mapOutput f).startsSide = p.startsSide
  | .pure _ => rfl
  | .query a k => by rcases a with (x | x) | r' <;> rfl

end OracleProg

namespace AssignRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y]
  [Inhabited Req'] [AddGroup Ys] (C' : Challenger X Y Req' Resp')
  (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)

/-- **The relay's program runs along its trace**, its reads answered by the oracle and the side
function, within the relay's budgets. -/
theorem progRun_relayOf (ansM : List Req' → Req' → Option Resp') (H : X → Y) (rs : List Req')
    (req : (Req × Fin (Q + 1)) × (X → Option Y)) :
    ∃ S : MultiRelay.ProgRun ansM (MultiRelay.sideOracle H G.side) rs (relayOfProg G Q req)
        ((relayOfProg G Q req).run (combineAns (MultiRelay.sideOracle H G.side) (ansM rs))),
      S.acts = (relayOfProg G Q req).trace (combineAns (MultiRelay.sideOracle H G.side) (ansM rs)) ∧
      (MultiRelay.asksOf S.acts).length ≤ (relayOf G Q).K ∧
      ((MultiRelay.qryOf S.acts).filter Sum.isLeft).length ≤ (relayOf G Q).qR ∧
      ((MultiRelay.qryOf S.acts).filter Sum.isRight).length ≤ (relayOf G Q).qS ∧
      MultiRelay.padOf S.acts ≤ (relayOf G Q).qP := by
  have htr : (relayOfProg G Q req).trace (combineAns (MultiRelay.sideOracle H G.side) (ansM rs)) =
      (G.prog req.2 req.1.2 req.1.1).trace
        (combineAns (MultiRelay.sideOracle (reprogT req.2 H) G.side) (ansM rs)) := by
    rw [relayOfProg, trace_mapOutput, trace_recMain, reprogT_tabS]
  have hasks : ((relayOfProg G Q req).trace (combineAns (MultiRelay.sideOracle H G.side)
      (ansM rs))).filterMap Sum.getRight? = ((G.prog req.2 req.1.2 req.1.1).trace
        (combineAns (MultiRelay.sideOracle (reprogT req.2 H) G.side) (ansM rs))).filterMap
          Sum.getRight? := by rw [htr]
  obtain ⟨S, hS⟩ := MultiRelay.progRun_of_asks_le_one ansM (MultiRelay.sideOracle H G.side) rs
    (relayOfProg G Q req) (by rw [hasks, G.asks_eq_one])
  refine ⟨S, hS, ?_, ?_, ?_, ?_⟩
  · rw [hS]
    change (((relayOfProg G Q req).trace _).filterMap Sum.getRight?).length ≤ 1
    rw [hasks, G.asks_eq_one]
  · rw [hS, OracleProg.length_filter_isLeft_qryOf, htr]
    exact G.reads_le _ _ _ _ _
  · rw [hS, OracleProg.length_filter_isRight_qryOf, htr]
    exact G.sides_le _ _ _ _ _
  · rw [hS, OracleProg.padOf_trace, relayOfProg, OracleProg.startsSide_mapOutput,
      OracleProg.startsSide_recMain]
    split_ifs with h
    · exact G.pad_le _ _ _ h
    · exact Nat.zero_le _

/-- **The relay's main requests come from its programs'**: when every program of request number
`c` and request `r` asks in `P c r`, the relay program of a tagged request asks in `P` of its
number and its request. -/
theorem asksIn_relayOf {P : ℕ → Req → Req' → Prop}
    (h : ∀ T c r, MultiRelay.AsksIn Resp' (G.prog T c r) (P c r))
    (p : TaggedReq X Y Req Q) :
    MultiRelay.AsksIn Resp' ((relayOf G Q).prog p) (P p.num p.req) :=
  ((h _ _ _).recMain _).mapOutput _

/-- **The relay's main requests come from its programs' with their side reads answered**: when
every program of table `T`, request number `c` and request `r`, its side reads answered by the side
function, asks in `P T c r`, so does the relay program of a tagged request, in `P` of its table,
its number and its request. -/
theorem asksIn_relayOf_elimSide {P : (X → Option Y) → ℕ → Req → Req' → Prop}
    (h : ∀ T c r, MultiRelay.AsksIn Resp' (elimSide G.side (G.prog T c r)) (P T c r))
    (p : TaggedReq X Y Req Q) :
    MultiRelay.AsksIn Resp' (elimSide (relayOf G Q).side ((relayOf G Q).prog p))
      (P p.tab p.num p.req) := by
  change MultiRelay.AsksIn Resp' (elimSide G.side (OracleProg.mapOutput _
    (OracleProg.recMain (OracleProg.tabS p.tab) (G.prog p.tab p.num p.req)))) _
  rw [OracleProg.mapOutput, elimSide_bind]
  exact (MultiRelay.AsksIn.elimSide_recMain_tabS _ _ (h _ _ _)).bind fun _ =>
    MultiRelay.AsksIn.pure _ _

/-- **The reply of the relay** to a request is the record of its program, its side reads answered
by the side function. -/
theorem runReply_relayOf (ansM : List Req' → Req' → Option Resp') (H : X → Y) (rs : List Req')
    (req : (Req × Fin (Q + 1)) × (X → Option Y)) :
    (relayOf G Q).runReply ansM H req rs =
      some (recordOf G.idle
          ((recMain req.2 (G.elimProg req.2 req.1.2 req.1.1)).run (combineAns H (ansM rs)))) := by
  obtain ⟨S, -, hK, hq, hs, hp⟩ := G.progRun_relayOf Q ansM H rs req
  rw [(relayOf G Q).runReply_eq_of_progRun S hK hq hs hp]
  rw [relayOfProg, run_mapOutput, run_recMain_tabS]
  rfl

/-- **The relay sends its program's main request.** -/
theorem filterMap_runEntries_relayOf (ansM : List Req' → Req' → Option Resp') (H : X → Y)
    (rs : List Req') (req : (Req × Fin (Q + 1)) × (X → Option Y)) :
    ((relayOf G Q).runEntries ansM H req rs).filterMap Prod.fst =
      ((G.elimProg req.2 req.1.2 req.1.1).trace (combineAns (reprogT req.2 H) (ansM rs))).filterMap
        Sum.getRight? := by
  obtain ⟨S, hS, hK, hq, hs, hp⟩ := G.progRun_relayOf Q ansM H rs req
  rw [MultiRelay.filterMap_runEntries_of_progRun (relayOf G Q) ansM H S hK hq hs hp]
  have ha : MultiRelay.asksOf S.acts = ((G.elimProg req.2 req.1.2 req.1.1).trace
      (combineAns (reprogT req.2 H) (ansM rs))).filterMap Sum.getRight? := by
    rw [hS, MultiRelay.asksOf, relayOfProg, trace_mapOutput, trace_recMain, reprogT_tabS,
      elimProg, trace_elimSide, filterMap_getRight_filterMap_dropSide]
  have hl : (MultiRelay.asksOf S.acts).length = 1 := by
    rw [ha, G.elim_asks_eq_one]
  rw [ha] at hl ⊢
  rw [show (relayOf G Q).K = 1 from rfl, hl, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- The record of a run whose program makes the main request `r'` holds `r'` and its main reply. -/
theorem recordOf_main {Tp T : X → Option Y} {h : X → Y} {m : Req' → Option Resp'} {c : ℕ}
    {r : Req} {r' : Req'} {rest : List Req'}
    (hr : ((G.elimProg Tp c r).trace (combineAns (reprogT T h) m)).filterMap Sum.getRight? =
      r' :: rest) :
    (recordOf G.idle ((recMain T (G.elimProg Tp c r)).run (combineAns h m))).2.2 = (r', m r') := by
  simp only [recordOf, run_recMain_snd T h m _ r' rest hr, Option.getD_some]

/-- The one main request of a run of the program given the table `Tp`, reading through `T`. -/
noncomputable def mainOfT (Tp T : X → Option Y) (h : X → Y) (m : Req' → Option Resp') (c : ℕ)
    (r : Req) : Req' :=
  (((G.elimProg Tp c r).trace (combineAns (reprogT T h) m)).filterMap Sum.getRight?).headD G.idle

/-- The one main request of a program run, given and reading through the table `T`. -/
noncomputable abbrev mainOf (T : X → Option Y) (h : X → Y) (m : Req' → Option Resp') (c : ℕ)
    (r : Req) : Req' :=
  G.mainOfT T T h m c r

theorem filterMap_eq_mainOfT (Tp T : X → Option Y) (h : X → Y) (m : Req' → Option Resp')
    (c : ℕ) (r : Req) :
    ((G.elimProg Tp c r).trace (combineAns (reprogT T h) m)).filterMap Sum.getRight? =
      [G.mainOfT Tp T h m c r] := by
  have hl := G.elim_asks_eq_one Tp c r (reprogT T h) m
  rcases hq : ((G.elimProg Tp c r).trace (combineAns (reprogT T h) m)).filterMap Sum.getRight? with
    _ | ⟨a, _ | ⟨b, l⟩⟩
  · rw [hq] at hl; simp at hl
  · simp [mainOfT, hq]
  · rw [hq] at hl; simp at hl

theorem filterMap_eq_mainOf (T : X → Option Y) (h : X → Y) (m : Req' → Option Resp') (c : ℕ)
    (r : Req) : ((G.elimProg T c r).trace (combineAns (reprogT T h) m)).filterMap Sum.getRight? =
      [G.mainOf T h m c r] :=
  G.filterMap_eq_mainOfT T T h m c r

/-- **The main request of a run does not depend on the main replies.** -/
theorem mainOf_congr (T : X → Option Y) (h : X → Y) (m m' : Req' → Option Resp') (c : ℕ)
    (r : Req) : G.mainOf T h m c r = G.mainOf T h m' c r := by
  have e := head?_filterMap_trace_combineAns (reprogT T h) m m' (G.elimProg T c r)
  rw [G.filterMap_eq_mainOf, G.filterMap_eq_mainOf] at e
  simpa using e

/-- **The origin of a table entry** `x ↦ y` among the tagged requests `hP` with the main history
`hist'`: the run of the relay program of a request `p` of `hP`, reading the oracle `H` through
`p`'s table, at some main replies `m`, assigns `y` at `x`, and its main request is a request of
`hist'`. -/
def TableFrom {Q : ℕ} (H : X → Y) (hP : List (TaggedReq X Y Req Q))
    (hist' : List (HistoryEntry Req' Resp')) (x : X) (y : Y) : Prop :=
  ∃ p ∈ hP, ∃ m, lastAssign ((G.elimProg p.tab p.num p.req).run
      (combineAns (reprogT p.tab H) m)).assignments x = some y ∧
    ∃ e' ∈ hist', e'.request = G.mainOf p.tab H m p.num p.req

/-- **A main history and a table explained by tagged requests**: every main request of `hist'` is
the padding request or one the relay program of a request of `hP` can make, and every entry of the
final table `T` and of the table of each request of `hP` has its origin in `hP` and `hist'`
(`TableFrom`). -/
def Explains (Q : ℕ) (H : X → Y) (T : X → Option Y) (hP : List (TaggedReq X Y Req Q))
    (hist' : List (HistoryEntry Req' Resp')) : Prop :=
  (∀ e' ∈ hist', e'.request = G.idle ∨ ∃ p ∈ hP, (G.relayOf Q).CanAsk p e'.request) ∧
    (∀ x y, T x = some y → G.TableFrom H hP hist' x y) ∧
    ∀ q ∈ hP, ∀ x y, q.tab x = some y → G.TableFrom H hP hist' x y

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
theorem chalT_respond (c' : C'.Coins)
    (hist : List (HistoryEntry ((Req × Fin (Q + 1)) × (X → Option Y)) (RespD X Y Resp Req' Resp')))
    (req : (Req × Fin (Q + 1)) × (X → Option Y)) :
    (chalT C' G Q).respond c' hist req =
      (relayProg C' G c' hist req.2 req.2 req.1.2 req.1.1).mapOutput
      fun res => ⟨some (recordOf G.idle res), []⟩ :=
  rfl

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
theorem chalD_respond (c' : C'.Coins)
    (hist : List (HistoryEntry (Req × Fin (Q + 1)) (RespD X Y Resp Req' Resp')))
    (req : Req × Fin (Q + 1)) :
    (chalD C' G Q).respond c' hist req =
        (relayProg C' G c' hist (fun _ => none) (histTab hist) req.2 req.1).mapOutput
      fun res => ⟨some (recordOf G.idle res), res.1.assignments⟩ :=
  rfl

/-- **The state of `chalT` after the requests `rs`**: the base oracle, no assignments, and the main
history recorded in its history is the main challenger's history after the relay's main
requests. -/
theorem oracleIn_chalT (hNA : C'.NoAssign) (hQ : Q ≤ C'.Q) (H : X → Y) (c' : C'.Coins) :
    ∀ rs : List ((Req × Fin (Q + 1)) × (X → Option Y)), rs.length ≤ Q →
      mainHist ((chalT C' G Q).toPureEnv.oracleIn (H, c') rs).hist =
        (C'.toPureEnv.oracleIn (H, c')
          ((relayOf G Q).mainReqs Q (C'.toPureEnv.answerAfter (H, c')) H rs)).hist := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton rs req ih =>
    intro hlen
    simp only [List.length_append, List.length_singleton] at hlen
    have hlt : rs.length < Q := by omega
    set ansM := C'.toPureEnv.answerAfter (H, c')
    have ih' := ih (by omega)
    obtain ⟨hb, ha, -⟩ := (noAssign_chalT C' G Q).oracleIn H c' rs
    have hmlen : ((relayOf G Q).mainReqs Q ansM H rs).length = rs.length := by
      rw [(relayOf G Q).length_mainReqs Q ansM H rs hlt.le]
      exact Nat.one_mul _
    -- the main replies seen by the program are the main challenger's
    have hm : (fun r' =>
        ((C'.respond c' (mainHist ((chalT C' G Q).toPureEnv.oracleIn (H, c') rs).hist)
        r').mapOutput Reply.response).run H) = ansM ((relayOf G Q).mainReqs Q ansM H rs) := by
      funext r'
      rw [run_mapOutput, ih']
      exact (hNA.answerAfter_eq H c' _ r' (by rw [hmlen]; omega)).symm
    rw [Env.oracleIn_append_singleton, Challenger.update_toPureEnv_of_lt _ _ _ _ hlt,
      (relayOf G Q).mainReqs_append, if_pos hlt, filterMap_runEntries_relayOf,
      filterMap_eq_mainOf, Env.oracleIn_append_singleton,
      Challenger.update_toPureEnv_of_lt _ _ _ _ (by rw [hmlen]; omega), hb, ha,
      chalT_respond, run_mapOutput, relayProg, run_lower,
      show H.reprogram ([] : List (Assignment X Y)) = H from rfl, hm]
    simp only [mainHist, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      Option.map_some]
    rw [← mainHist, ih']
    have hrec := G.recordOf_main (T := req.2) (h := H)
        (m := ansM ((relayOf G Q).mainReqs Q ansM H rs))
      (G.filterMap_eq_mainOf req.2 H _ req.1.2 req.1.1)
    obtain ⟨hb', ha', -⟩ := hNA.oracleIn H c' ((relayOf G Q).mainReqs Q ansM H rs)
    rw [hrec, hb', ha', show H.reprogram ([] : List (Assignment X Y)) = H from rfl,
      ← hNA.answerAfter_eq H c' _ _ (by rw [hmlen]; omega)]

/-- **`chalT` is the multi-request relay of the main challenger** (`MultiRelay.RelaysChallenger`),
for a main challenger that reprograms nothing and answers at least `Q` requests. -/
theorem relaysChallenger_relayOf (hNA : C'.NoAssign) (hQ : Q ≤ C'.Q) :
    (relayOf G Q).RelaysChallenger (chalT C' G Q) C' id where
  coins_eq := (PMF.map_id _).symm
  oracle_eq H c _ lg := (noAssign_chalT C' G Q).oracle_eq H c lg
  oracle_eq' H c' _ lg := hNA.oracle_eq H c' lg
  answer_eq H c' rs req hlt := by
    dsimp only [id]
    obtain ⟨hb, ha, -⟩ := (noAssign_chalT C' G Q).oracleIn H c' rs
    rw [Challenger.answerAfter_toPureEnv_of_lt _ _ _ _ hlt, hb, ha,
      show H.reprogram ([] : List (Assignment X Y)) = H from rfl, runReply_relayOf]
    change (((relayProg C' G c' _ req.2 req.2 req.1.2 req.1.1).mapOutput
      fun res => (⟨some (recordOf G.idle res), []⟩ : Reply X Y _)).run H).response = _
    rw [run_mapOutput, relayProg, run_lower]
    have hf : (fun r' =>
        ((C'.respond c' (mainHist ((chalT C' G Q).toPureEnv.oracleIn (H, c') rs).hist)
        r').mapOutput Reply.response).run H) = C'.toPureEnv.answerAfter (H, c')
          ((relayOf G Q).mainReqs (chalT C' G Q).Q (C'.toPureEnv.answerAfter (H, c')) H rs) := by
      funext r'
      rw [run_mapOutput, G.oracleIn_chalT C' Q hNA hQ H c' rs hlt.le]
      refine (hNA.answerAfter_eq H c' _ r' ?_).symm
      rw [(relayOf G Q).length_mainReqs Q _ H rs hlt.le]
      change 1 * rs.length < C'.Q
      rw [Nat.one_mul]
      exact lt_of_lt_of_le hlt hQ
    rw [hf]

/-! ### `chalD` and `chalT` -/

/-- **Assignments the main challenger does not see** (the hypothesis of the absorption of an
assigning challenger): a class `Safe H` of assignment lists at each oracle `H`, containing the
empty list, closed under concatenation (the second list safe at the oracle reprogrammed by the
first), containing every list a program of the relay returns at the oracle it reads, on which
reprogramming `H` does not change the main challenger's replies. The main challenger's reply
programs read the oracle only off the points the relay assigns; a main challenger that makes no
queries satisfies this for every list (`SafeAssign.ofNoQuery`). -/
structure SafeAssign (C' : Challenger X Y Req' Resp')
    (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) where
  /-- The safe assignment lists at the oracle `H`. -/
  Safe : (X → Y) → List (Assignment X Y) → Prop
  safe_nil : ∀ H, Safe H []
  safe_append : ∀ (H : X → Y) a b, Safe H a → Safe (H.reprogram a) b → Safe H (a ++ b)
  /-- Every list a relay program returns is safe at the oracle it reads. -/
  safe_prog : ∀ T c r (h : X → Y) (m : Req' → Option Resp'),
    Safe h ((G.elimProg T c r).run (combineAns h m)).assignments
  /-- The main challenger's replies do not see safe reprogramming. -/
  respond_reprogram : ∀ c' hist r' (H : X → Y) (L : List (Assignment X Y)), Safe H L →
    (C'.respond c' hist r').run (H.reprogram L) = (C'.respond c' hist r').run H

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
/-- A program without queries runs alike against every oracle. -/
theorem run_eq_of_queriesLE_zero {R : Type} {p : OracleProg X Y R} (hp : p.QueriesLE 0)
    (H H' : X → Y) : p.run H = p.run H' := by
  cases p with
  | pure r => rfl
  | query x k => have := hp H; simp [OracleProg.trace] at this

/-- **A main challenger that makes no queries sees no reprogramming**: every list is safe. -/
def SafeAssign.ofNoQuery (hq : C'.q = 0) : SafeAssign C' G where
  Safe _ _ := True
  safe_nil _ := trivial
  safe_append _ _ _ _ _ := trivial
  safe_prog _ _ _ _ _ := trivial
  respond_reprogram c' hist r' H L _ := run_eq_of_queriesLE_zero
    (fun H => hq ▸ C'.respond_queries c' hist r' H) _ _

variable {C' G} (hS : SafeAssign C' G)

variable (G) in
/-- **The table of the assignments in force of `chalD`** after the requests `rs`. -/
noncomputable def tabAfter (H : X → Y) (c' : C'.Coins)
    (rs : List (Req × Fin (Q + 1))) : X → Option Y :=
  lastAssign ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).ass

/-- **The requests tagged by the tables before them.** -/
def augList {R T : Type} (T₁ : List R → T) (rs : List R) : List (R × T) :=
  (rs.foldl (fun (p : List (R × T) × List R) r => (p.1 ++ [(r, T₁ p.2)], p.2 ++ [r])) ([], [])).1

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
theorem foldl_augList_snd {R T : Type} (T₁ : List R → T) (rs : List R) :
    (rs.foldl (fun (p : List (R × T) × List R) r => (p.1 ++ [(r, T₁ p.2)], p.2 ++ [r]))
      ([], [])).2 =
      rs := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih => simp [List.foldl_append, ih]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
theorem augList_append_singleton {R T : Type} (T₁ : List R → T) (rs : List R) (r : R) :
    augList T₁ (rs ++ [r]) = augList T₁ rs ++ [(r, T₁ rs)] := by
  simp only [augList, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_augList_snd]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
@[simp]
theorem length_augList {R T : Type} (T₁ : List R → T) (rs : List R) :
    (augList T₁ rs).length = rs.length := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih => simp [augList_append_singleton, ih]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
/-- **The requests of the tagged logs** are the tagged requests. -/
theorem requestsBefore_augLogs_eq {R T : Type} {m : ℕ} (T₁ : List R → T) (lg : LogReg R m) :
    ∀ k, requestsBefore (augLogs T₁ lg) k = augList T₁ (requestsBefore lg k)
  | 0 => rfl
  | k + 1 => by
    rw [requestsBefore, requestsBefore, requestsBefore_augLogs_eq T₁ lg k]
    split_ifs with hk
    · rcases h : lg ⟨k, hk⟩ with _ | r
      · simp [augLogs, h]
      · simp [augLogs, h, augList_append_singleton]
    · simp

/-- **The table recorded in `chalD`'s history is the table of its assignments in force.** -/
theorem histTab_oracleIn_chalD (H : X → Y) (c' : C'.Coins) : ∀ rs : List (Req × Fin (Q + 1)),
    histTab ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).hist =
      lastAssign ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).ass := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => funext x; rfl
  | append_singleton rs req ih =>
    rw [Env.oracleIn_append_singleton]
    by_cases hlt : rs.length < Q
    · rw [Challenger.update_toPureEnv_of_lt _ _ _ _ hlt]
      simp only [histTab, List.map_append, List.map_cons, List.map_nil, foldT_append_singleton,
        lastAssign_append]
      rw [← histTab, ih, chalD_respond, run_mapOutput]
      rfl
    · rw [Challenger.update_toPureEnv_of_le _ _ _ _ (not_lt.1 hlt)]
      exact ih

/-- **One request to `chalD` and to `chalT`**: from states with the base oracle `H`, safe
assignments in force for `chalD`, none for `chalT`, and the same recorded main history, the reply
of `chalT` to the request tagged with the table of `chalD`'s assignments is `chalD`'s, and `chalD`'s
new assignments are safe. -/
theorem respond_chalT_chalD (H : X → Y) (c' : C'.Coins)
    (sD : ChallengerState X Y (Req × Fin (Q + 1)) (RespD X Y Resp Req' Resp'))
    (sT : ChallengerState X Y ((Req × Fin (Q + 1)) × (X → Option Y)) (RespD X Y Resp Req' Resp'))
    (hbD : sD.base = H) (hsD : hS.Safe H sD.ass) (hbT : sT.base = H) (haT : sT.ass = [])
    (hm : mainHist sT.hist = mainHist sD.hist) (hT : histTab sD.hist = lastAssign sD.ass)
    (req : Req × Fin (Q + 1)) :
    (((chalT C' G Q).respond c' sT.hist (req, lastAssign sD.ass)).run
        (sT.base.reprogram sT.ass)).response =
      (((chalD C' G Q).respond c' sD.hist req).run (sD.base.reprogram sD.ass)).response ∧
    hS.Safe (H.reprogram sD.ass) (((chalD C' G Q).respond c' sD.hist req).run
      (sD.base.reprogram sD.ass)).assignments := by
  rw [chalT_respond, chalD_respond, run_mapOutput, run_mapOutput, relayProg, relayProg, run_lower,
    run_lower, hbD, hbT, haT, show H.reprogram ([] : List (Assignment X Y)) = H from rfl, hT]
  have hmD : (fun r' => ((C'.respond c' (mainHist sD.hist) r').mapOutput Reply.response).run
      (H.reprogram sD.ass)) = fun r' => ((C'.respond c' (mainHist sD.hist) r').mapOutput
        Reply.response).run H := by
    funext r'
    rw [run_mapOutput, run_mapOutput, hS.respond_reprogram _ _ _ _ _ hsD]
  rw [hmD, hm]
  set m := fun r' => ((C'.respond c' (mainHist sD.hist) r').mapOutput Reply.response).run H
  have horc : reprogT (lastAssign sD.ass) H = H.reprogram sD.ass := (reprogram_eq_reprogT H _).symm
  refine ⟨?_, ?_⟩
  · simp only
    congr 1
    have h1 := run_recMain_fst (fun _ => none) (H.reprogram sD.ass) m
      (G.elimProg (lastAssign sD.ass) req.2 req.1)
    have h2 := run_recMain_fst (lastAssign sD.ass) H m (G.elimProg (lastAssign sD.ass) req.2 req.1)
    rw [reprogT_none] at h1
    rw [horc] at h2
    have h3 := G.recordOf_main (T := fun _ => none) (h := H.reprogram sD.ass) (m := m)
      (G.filterMap_eq_mainOfT (lastAssign sD.ass) (fun _ => none) (H.reprogram sD.ass) m req.2
        req.1)
    have h4 := G.recordOf_main (T := lastAssign sD.ass) (h := H) (m := m)
      (G.filterMap_eq_mainOfT (lastAssign sD.ass) (lastAssign sD.ass) H m req.2 req.1)
    have h5 : G.mainOfT (lastAssign sD.ass) (lastAssign sD.ass) H m req.2 req.1 =
        G.mainOfT (lastAssign sD.ass) (fun _ => none) (H.reprogram sD.ass) m req.2 req.1 := by
      simp only [mainOfT, horc, reprogT_none]
    simp only [recordOf] at h3 h4 ⊢
    rw [h1, h2, h3, h4, h5]
  · simp only
    have h1 := run_recMain_fst (fun _ => none) (H.reprogram sD.ass) m
      (G.elimProg (lastAssign sD.ass) req.2 req.1)
    rw [reprogT_none] at h1
    rw [h1]
    exact hS.safe_prog _ _ _ _ _

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
theorem mainHist_append {ReqT : Type}
    (h h' : List (HistoryEntry ReqT (RespD X Y Resp Req' Resp'))) :
    mainHist (h ++ h') = mainHist h ++ mainHist h' :=
  List.filterMap_append

/-- **The states of `chalD` and of `chalT` on the tagged requests**: the base oracle, safe
assignments in force for `chalD`, and the same recorded main history. -/
theorem oracleIn_chalD_chalT (H : X → Y) (c' : C'.Coins) : ∀ rs : List (Req × Fin (Q + 1)),
    ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).base = H ∧
      hS.Safe H ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).ass ∧
      mainHist ((chalT C' G Q).toPureEnv.oracleIn (H, c') (augList (G.tabAfter Q H c') rs)).hist =
        mainHist ((chalD C' G Q).toPureEnv.oracleIn (H, c') rs).hist := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, hS.safe_nil H, rfl⟩
  | append_singleton rs req ih =>
    obtain ⟨hb, hs, hm⟩ := ih
    obtain ⟨hbT, haT, -⟩ := (noAssign_chalT C' G Q).oracleIn H c' (augList (G.tabAfter Q H c') rs)
    rw [augList_append_singleton, Env.oracleIn_append_singleton, Env.oracleIn_append_singleton,
      length_augList]
    by_cases hlt : rs.length < Q
    · rw [Challenger.update_toPureEnv_of_lt _ _ _ _ hlt,
        Challenger.update_toPureEnv_of_lt _ _ _ _ hlt]
      obtain ⟨h1, h2⟩ := G.respond_chalT_chalD Q hS H c' _ _ hb hs hbT haT hm
        (histTab_oracleIn_chalD (C' := C') (G := G) Q H c' rs) req
      refine ⟨hb, hS.safe_append H _ _ hs h2, ?_⟩
      simp only [mainHist_append]
      rw [hm]
      congr 1
      simp only [mainHist, List.filterMap_cons, List.filterMap_nil]
      rw [tabAfter, h1]
    · rw [Challenger.update_toPureEnv_of_le _ _ _ _ (not_lt.1 hlt),
        Challenger.update_toPureEnv_of_le _ _ _ _ (not_lt.1 hlt)]
      exact ⟨hb, hs, hm⟩

include hS in
/-- **`chalT` answers the tagged request as `chalD` answers the request.** -/
theorem answerAfter_chalT_chalD (H : X → Y) (c' : C'.Coins) (rs : List (Req × Fin (Q + 1)))
    (req : Req × Fin (Q + 1)) :
    (chalT C' G Q).toPureEnv.answerAfter (H, c') (augList (G.tabAfter Q H c') rs)
        (req, G.tabAfter Q H c' rs) =
      (chalD C' G Q).toPureEnv.answerAfter (H, c') rs req := by
  by_cases hlt : rs.length < Q
  · rw [Challenger.answerAfter_toPureEnv_of_lt _ _ _ _ (by rw [length_augList]; exact hlt),
      Challenger.answerAfter_toPureEnv_of_lt _ _ _ _ hlt]
    obtain ⟨hb, hs, hm⟩ := G.oracleIn_chalD_chalT Q hS H c' rs
    obtain ⟨hbT, haT, -⟩ := (noAssign_chalT C' G Q).oracleIn H c' (augList (G.tabAfter Q H c') rs)
    exact (G.respond_chalT_chalD Q hS H c' _ _ hb hs hbT haT hm
      (histTab_oracleIn_chalD (C' := C') (G := G) Q H c' rs) req).1
  · rw [Challenger.answerAfter_toPureEnv_of_le _ _ _ _ (by rw [length_augList]; exact not_lt.1 hlt),
      Challenger.answerAfter_toPureEnv_of_le _ _ _ _ (not_lt.1 hlt)]

include hS in
/-- **The replies of `chalT` at the tagged logs are those of `chalD`** (the hypothesis `hans` of the
law of `AdaptiveIAlg.patchTag`). -/
theorem answer_chalT_augLogs (H : X → Y) (c' : C'.Coins) {m : ℕ} (lg : LogReg (Req × Fin (Q + 1)) m)
    (k : Fin m) :
    (chalT C' G Q).toPureEnv.answer (H, c') (augLogs (G.tabAfter Q H c') lg) k =
      (chalD C' G Q).toPureEnv.answer (H, c') lg k := by
  simp only [Env.answer, augLogs, requestsBefore_augLogs_eq]
  rcases lg k with _ | req
  · rfl
  · exact G.answerAfter_chalT_chalD Q hS H c' _ req

include hS in
/-- **The oracle in force of `chalD` is the base oracle read through its table** (the hypothesis
`horc` of the law of `AdaptiveIAlg.patchTag`). -/
theorem oracle_chalD (H : X → Y) (c' : C'.Coins) {m : ℕ} (lg : LogReg (Req × Fin (Q + 1)) m) :
    (chalD C' G Q).toPureEnv.oracle (H, c') lg =
      reprogT (G.tabAfter Q H c' (requests lg))
        ((chalT C' G Q).toPureEnv.oracle (H, c') (augLogs (G.tabAfter Q H c') lg)) := by
  rw [(noAssign_chalT C' G Q).oracle_eq H c']
  obtain ⟨hb, -, -⟩ := G.oracleIn_chalD_chalT Q hS H c' (requests lg)
  change ((chalD C' G Q).toPureEnv.oracleIn (H, c') (requests lg)).base.reprogram
    ((chalD C' G Q).toPureEnv.oracleIn (H, c') (requests lg)).ass = _
  rw [hb, reprogram_eq_reprogT]
  rfl

end AssignRelay

end GordieHowe.Quantum
