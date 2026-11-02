-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignRelay

@[expose] public section

/-!
# The challengers of an assigning relay

For a main challenger `C'` and a relay `G` (`AssignRelay`), two challengers answering at most `Q`
requests on `C'`'s coins, each of whose replies reveals the outer response, the table of the
request's assignments (`lastAssign`), the main request and the main reply (`RespD`):

- `AssignRelay.histTab`: the table recorded in a history, the replies' tables in order.
- `AssignRelay.chalD C' G Q`: request `(r, c)` (the request and its number) is answered by `G`'s
  program of number `c`, given the table recorded in the history (`histTab`), reading the oracle
  in force, its main request answered by `C'`'s reply program after the main history recorded in
  the replies (`mainHist`); it appends the program's assignments.
- `AssignRelay.chalT C' G Q`: request `((r, c), T)` is answered alike, the program given and
  reading the oracle through the table `T`; it assigns nothing.
- `AssignRelay.relayOf G Q`: the multi-request relay (`MultiRelay`, one main request, `qG` reads)
  of `chalT` to `C'`; `AssignRelay.noTrailingSides_relayOf`: it has no trailing side reads when
  `G`'s programs make no side read after their main request.
- `AssignRelay.sideRelay X Y Req Resp Req' Resp' Q`: the side relay of the outer requests to
  `chalD`: request number `c` with request `r` is sent as `(r, min c Q)`, the reply relayed is the
  outer response.
-/

open Finset

namespace GordieHowe.Quantum

open GordieHowe.OracleProg

namespace AssignRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} [DecidableEq X]

/-- The replies of the challengers of a relay: the outer response, the table of the request's
assignments, the main request and the main reply. -/
abbrev RespD (X Y Resp Req' Resp' : Type) : Type := Option Resp × (X → Option Y) ×
    (Req' × Option Resp')

instance [Fintype X] [DecidableEq Y] [DecidableEq Resp] [DecidableEq Req'] [DecidableEq Resp'] :
    DecidableEq (RespD X Y Resp Req' Resp') :=
  @instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ Fintype.decidablePiFintype
    inferInstance)

/-- **A tagged request** of a relay with request cap `Q`: the outer request `req`, its number
`num` (capped at `Q`) and the table `tab` of the assignments in force before it. -/
abbrev TaggedReq (X Y Req : Type) (Q : ℕ) : Type := (Req × Fin (Q + 1)) × (X → Option Y)

/-- The outer request of a tagged request. -/
abbrev TaggedReq.req {Q : ℕ} (p : TaggedReq X Y Req Q) : Req := p.1.1

/-- The number of a tagged request. -/
abbrev TaggedReq.num {Q : ℕ} (p : TaggedReq X Y Req Q) : Fin (Q + 1) := p.1.2

/-- The table in force of a tagged request. -/
abbrev TaggedReq.tab {Q : ℕ} (p : TaggedReq X Y Req Q) : X → Option Y := p.2

/-- **The record of a run of a relay program**: its response, the table of its assignments, its
main request and the main reply (`idle` and no reply if it made none). -/
def recordOf (idle : Req') (res : Reply X Y Resp × Option (Req' × Option Resp')) :
    RespD X Y Resp Req' Resp' :=
  (res.1.response, lastAssign res.1.assignments, res.2.getD (idle, none))

/-- **The main history recorded in a history**: the main request and the main reply of each
answered entry. -/
def mainHist {ReqT : Type} (hist : List (HistoryEntry ReqT (RespD X Y Resp Req' Resp'))) :
    List (HistoryEntry Req' Resp') :=
  hist.filterMap fun e => e.response.map fun x => ⟨x.2.2.1, x.2.2.2⟩

variable (C' : Challenger X Y Req' Resp')
  (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys)

/-- **The table recorded in a history**: the tables of its replies, overridden in order. -/
def histTab {ReqT : Type} (hist : List (HistoryEntry ReqT (RespD X Y Resp Req' Resp'))) :
    X → Option Y :=
  foldT (hist.map fun e => e.response.elim (fun _ => none) fun d => d.2.1)

/-- **The program answering a request** after the history `hist`: `G`'s program of number `c` with
request `r` given the table `Tp`, its side reads answered by the side function (`elimProg`),
reading through the table `T`, recording its main request, its main request answered by `C'`'s
reply program after the recorded main history. -/
def relayProg {ReqT : Type} (c' : C'.Coins)
    (hist : List (HistoryEntry ReqT (RespD X Y Resp Req' Resp')))
    (T Tp : X → Option Y) (c : ℕ) (r : Req) :
    OracleProg X Y (Reply X Y Resp × Option (Req' × Option Resp')) :=
  lower (fun r' => (C'.respond c' (mainHist hist) r').mapOutput Reply.response)
    (recMain T (G.elimProg Tp c r))

theorem length_filter_isRight {α β : Type*} (l : List (α ⊕ β)) :
    (l.filter Sum.isRight).length = (l.filterMap Sum.getRight?).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases a with a | b
    · simp only [List.filter_cons, Sum.isRight_inl, Bool.false_eq_true, ite_false, ih,
        List.filterMap_cons, Sum.getRight?_inl]
    · simp only [List.filter_cons, Sum.isRight_inr, ite_true, List.length_cons, ih,
        List.filterMap_cons, Sum.getRight?_inr]

omit [DecidableEq X] in
/-- **A relay program makes at most `qG + q'` queries**, `q'` the queries of a main reply. -/
theorem length_trace_relayProg_le {ReqT : Type} (c' : C'.Coins)
    (hist : List (HistoryEntry ReqT (RespD X Y Resp Req' Resp'))) (T Tp : X → Option Y) (c : ℕ)
    (r : Req) (H : X → Y) : ((relayProg C' G c' hist T Tp c r).trace H).length ≤ G.qG + C'.q := by
  refine (length_trace_lower_le _ H (q' := C'.q) (fun r' => by
    rw [trace_mapOutput]; exact C'.respond_queries c' (mainHist hist) r' H) _).trans ?_
  rw [trace_recMain, length_filter_isRight, G.elim_asks_eq_one]
  have := G.elim_reads_le Tp c r (reprogT T H) fun r' =>
    ((C'.respond c' (mainHist hist) r').mapOutput Reply.response).run H
  omega

/-- **The assigning challenger of the relay** (module docstring). -/
def chalD (Q : ℕ) : Challenger X Y (Req × Fin (Q + 1)) (RespD X Y Resp Req' Resp') where
  Coins := C'.Coins
  coins := C'.coins
  Q := Q
  q := G.qG + C'.q
  respond c' hist req := (relayProg C' G c' hist (fun _ => none) (histTab hist) req.2
    req.1).mapOutput fun res => ⟨some (recordOf G.idle res), res.1.assignments⟩
  respond_queries c' hist req H := by
    rw [trace_mapOutput]
    exact length_trace_relayProg_le C' G c' hist _ _ _ _ H

/-- **The challenger of the relay reading through the tables of its requests** (module
docstring); it assigns nothing. -/
def chalT (Q : ℕ) : Challenger X Y ((Req × Fin (Q + 1)) × (X → Option Y))
    (RespD X Y Resp Req' Resp') where
  Coins := C'.Coins
  coins := C'.coins
  Q := Q
  q := G.qG + C'.q
  respond c' hist req := (relayProg C' G c' hist req.2 req.2 req.1.2 req.1.1).mapOutput
    fun res => ⟨some (recordOf G.idle res), []⟩
  respond_queries c' hist req H := by
    rw [trace_mapOutput]
    exact length_trace_relayProg_le C' G c' hist _ _ _ _ H

/-- **`chalT` assigns nothing.** -/
theorem noAssign_chalT (Q : ℕ) : (chalT C' G Q).NoAssign := fun _ _ _ _ => by
  simp [chalT, run_mapOutput]

variable (Q : ℕ)

/-- **The program of the multi-request relay of `chalT` to `C'`**: request `((r, c), T)` runs
`G`'s program of number `c` with request `r` reading the oracle through `T` (`tabS`), keeping its
side reads, and recording its main request. -/
def relayOfProg (req : (Req × Fin (Q + 1)) × (X → Option Y)) :
    OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option (RespD X Y Resp Req' Resp')) :=
  (recMain (tabS req.2) (G.prog req.2 req.1.2 req.1.1)).mapOutput fun res =>
    some (recordOf G.idle res)

/-- **The multi-request relay of `chalT` to `C'`**: `relayOfProg`, its side reads answered by
`G`'s side function, one main request, `qG` oracle reads, `qS` side reads and `qP` pad
sub-slots. -/
def relayOf : MultiRelay X Y ((Req × Fin (Q + 1)) × (X → Option Y)) (RespD X Y Resp Req' Resp')
    Req' Resp' Xs Ys where
  prog := relayOfProg G Q
  K := 1
  K_pos := Nat.one_pos
  qR := G.qG
  idle := G.idle
  side := G.side
  qS := G.qS
  qP := G.qP
  qP_le_one := G.qP_le_one
  qP_spec := G.qP_spec

/-- **The multi-request relay of programs without side reads after their main request** has no
trailing side reads. -/
theorem noTrailingSides_relayOf (h : ∀ T c r, (G.prog T c r).NoSideAfterAsk) :
    (G.relayOf Q).NoTrailingSides := fun req =>
  (((h _ _ _).recMain (tabS req.2)).mapOutput _).noTrailingSides

variable (X Y Req Resp Req' Resp') in
/-- **The side relay of the outer requests to `chalD`**: request number `c` with request `r` is sent
as `(r, min c Q)`, and the outer response is relayed. -/
def sideRelay (Q : ℕ) :
    SideRelay Req Resp (Req × Fin (Q + 1)) (RespD X Y Resp Req' Resp') where
  route c r := (r, ⟨min c Q, Nat.lt_succ_of_le (min_le_right _ _)⟩)
  answer _ _ a := a.bind fun x => x.1

omit [DecidableEq X] in
theorem sideRelay_route_injective (c : ℕ) :
    Function.Injective ((sideRelay X Y Req Resp Req' Resp' Q).route c) :=
  fun r r' h => by
  simpa [sideRelay] using congrArg Prod.fst h

end AssignRelay

end GordieHowe.Quantum
