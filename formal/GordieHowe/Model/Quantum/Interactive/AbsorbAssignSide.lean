-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AbsorbAssign
public import GordieHowe.Model.Quantum.Interactive.SumDummy

@[expose] public section

/-!
# A side relay as an assigning relay

A side relay `F` (`SideRelay`, `GordieHowe/Model/Quantum/Interactive/Absorb.lean`) read as an
assigning relay (`AssignRelay`), and the law of `absorb` as the law of `absorbAssign` at it.

- `SideRelay.assignProg F c r`: ask `F.route c r`, return `F.answer c r` of the main reply with no
  assignments. `trace_assignProg`, `reads_assignProg`, `asks_assignProg`: no reads, one main
  request.
- `SideRelay.route_ne_inr`, `SideRelay.dummyRelay_route_ne_inr`: a relay into the left summand
  never sends a right request (satisfiability of `hidle` below).
- `AssignRelay.ofSide F idle` (`ofPlain` of `assignProg`, no reads, no side reads, padding
  request `idle`); `qG_ofSide`, `idle_ofSide`, `elimProg_ofSide`, `run_relayProg_ofSide`.
- `AssignRelay.oracleIn_chalD_ofSide`: the histories `chalD` reaches have their main requests
  relayed by `F`. `AssignRelay.relaysChallenger_ofSide`: `F.RelaysChallenger` and `C'.NoAssign`
  give `(ofSide F idle).RelaysChallenger`. `AssignRelay.safeAssign_ofSide`: its assignments (none)
  are safe.
- `AssignRelay.tagMain`, `AssignRelay.map_relayList_sideRelay`,
  `AssignRelay.mainReqs_relayOf_ofSide`: the main requests of the tagged requests.
- `filter_histAlong_append`: dropping trailing idle requests from a history.
- `AdaptiveIAlg.trace_mgRun_absorbAssignP`: the patched game against `chalT` has trace 1 for `A`
  within its budget. `AdaptiveIAlg.map_tagMain_history_placedP`: its tagged main requests at the
  placed states.
- **`AdaptiveIAlg.toOuterMeasure_absorbAssign_ofSide`**: averaged over the side coins, the output
  and the history without idle requests of `A.absorbAssign (ofSide (F' s) idle) C.Q` against
  `C'` have the law of the output and history of `A.absorb (F' s)` against `C'`.
-/

open Finset
open scoped ComplexOrder


namespace GordieHowe.Quantum

open GordieHowe.OracleProg

namespace SideRelay

variable {X Y Req Resp Req' Resp' : Type} (F : SideRelay Req Resp Req' Resp')

/-- **The program of a side relay**: request number `c` with request `r` asks the main request
`route c r` and returns `answer c r` of the main reply, with no assignments. -/
def assignProg (c : ℕ) (r : Req) : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Reply X Y Resp) :=
  .query (.inr (F.route c r)) fun b => .pure ⟨F.answer c r (b.elim (fun _ => none) id), []⟩

theorem trace_assignProg (c : ℕ) (r : Req) (o : X ⊕ Req' → Y ⊕ Option Resp') :
    ((F.assignProg c r).trace o) = [.inr (F.route c r)] :=
  rfl

/-- The program of a side relay reads the oracle nowhere. -/
theorem reads_assignProg (c : ℕ) (r : Req) (o : X ⊕ Req' → Y ⊕ Option Resp') :
    (((F.assignProg c r).trace o).filter Sum.isLeft).length ≤ 0 := by
  simp [trace_assignProg]

/-- The program of a side relay makes one main request. -/
theorem asks_assignProg (c : ℕ) (r : Req) (o : X ⊕ Req' → Y ⊕ Option Resp') :
    (((F.assignProg c r).trace o).filterMap Sum.getRight?).length = 1 := by
  simp [trace_assignProg]

/-- **A dedicated idle request is never relayed** (satisfiability of the hypothesis `hidle` of
`AdaptiveIAlg.toOuterMeasure_absorbAssign_ofSide`): a relay whose main requests all lie in the left
summand never sends a right request `inr d`. -/
theorem route_ne_inr {R D : Type} (F : SideRelay Req Resp (R ⊕ D) Resp')
    (hF : ∀ c r, (F.route c r).isLeft) (d : D) (c : ℕ) (r : Req) : F.route c r ≠ .inr d :=
  fun h => by simpa [h] using hF c r

/-- **The dummy relay into the left summand never sends an idle right request**: `dummyRelay`
(`GordieHowe/Model/Quantum/Interactive/SumDummy.lean`) with the encoding `inl ∘ enc`. -/
theorem dummyRelay_route_ne_inr {Req₁ Resp₁ R R₀ D : Type} (f : Req₁ → Option Resp₁)
    (enc : Req₁ ⊕ R → R₀) (Q : ℕ) (d : D) (c : ℕ) (x : Req₁ ⊕ R) :
    (dummyRelay (Resp₂ := Resp') f (Sum.inl ∘ enc) Q).route c x ≠ .inr d :=
  route_ne_inr _ (fun _ _ => rfl) d c x

end SideRelay

namespace AssignRelay

variable {X Y Req Resp Req' Resp' : Type}

/-- **A side relay as an assigning relay** (`AssignRelay.ofPlain`): request number `c` with
request `r` asks the main request `F.route c r` and returns `F.answer c r` of the main reply, with
no oracle reads and no assignments; the padding main request `idle`. -/
def ofSide (F : SideRelay Req Resp Req' Resp') (idle : Req') : AssignRelay X Y Req Resp Req' Resp' :=
  ofPlain F.assignProg 0 idle (fun c r _ _ => F.reads_assignProg c r _)
    fun c r _ _ => F.asks_assignProg c r _

variable (F : SideRelay Req Resp Req' Resp') (idle : Req')

@[simp] theorem qG_ofSide : (ofSide (X := X) (Y := Y) F idle).qG = 0 := rfl

@[simp] theorem idle_ofSide : (ofSide (X := X) (Y := Y) F idle).idle = idle := rfl

/-- The program of `ofSide` with its side reads answered is the side relay's program. -/
@[simp] theorem elimProg_ofSide :
    (ofSide (X := X) (Y := Y) F idle).elimProg = fun _ => F.assignProg :=
  elimProg_ofProg (fun _ => F.assignProg) 0 idle (fun _ c r _ _ => F.reads_assignProg c r _)
    fun _ c r _ _ => F.asks_assignProg c r _

variable [DecidableEq X] (C' : Challenger X Y Req' Resp')

omit [DecidableEq X] in
/-- **The relay program of `ofSide` runs as the main reply relayed**: the response `answer c r` of
the main reply to `route c r`, no assignments, and the recorded main request and reply. -/
theorem run_relayProg_ofSide {ReqT : Type} (c' : C'.Coins)
    (hist : List (HistoryEntry ReqT (RespD X Y Resp Req' Resp'))) (T Tp : X → Option Y) (c : ℕ)
    (r : Req) (H : X → Y) :
    (relayProg C' (ofSide F idle) c' hist T Tp c r).run H =
      (⟨F.answer c r ((C'.respond c' (mainHist hist) (F.route c r)).run H).response, []⟩,
        some (F.route c r, ((C'.respond c' (mainHist hist) (F.route c r)).run H).response)) := by
  simp only [relayProg, elimProg_ofSide, run_lower]
  simp [SideRelay.assignProg, recMain, OracleProg.run, combineAns]

variable [Fintype X] [Fintype Y] [Nonempty Y]

/-- **The histories `chalD` reaches at `ofSide`**: after the relay of the outer requests `rs`,
the history has `min |rs| Q` entries, each with a response, and its main history's requests are
the relayed requests (`F.relayList`) of its outer requests. -/
theorem oracleIn_chalD_ofSide (Q : ℕ) (H : X → Y) (c' : C'.Coins) (rs : List Req) :
    ((chalD C' (ofSide F idle) Q).toPureEnv.oracleIn (H, c')
        ((sideRelay X Y Req Resp Req' Resp' Q).relayList rs)).hist.length = min rs.length Q ∧
      (∀ e ∈ ((chalD C' (ofSide F idle) Q).toPureEnv.oracleIn (H, c')
        ((sideRelay X Y Req Resp Req' Resp' Q).relayList rs)).hist, e.response.isSome) ∧
      (mainHist ((chalD C' (ofSide F idle) Q).toPureEnv.oracleIn (H, c')
        ((sideRelay X Y Req Resp Req' Resp' Q).relayList rs)).hist).map HistoryEntry.request =
        F.relayList ((((chalD C' (ofSide F idle) Q).toPureEnv.oracleIn (H, c')
          ((sideRelay X Y Req Resp Req' Resp' Q).relayList rs)).hist.map stripEntry).map
            HistoryEntry.request) := by
  induction rs using List.reverseRecOn with
  | nil => simp [Env.oracleIn_nil, Challenger.toPureEnv, mainHist]
  | append_singleton rs r ih =>
    rw [SideRelay.relayList_append_singleton (sideRelay X Y Req Resp Req' Resp' Q),
      Env.oracleIn_append_singleton, SideRelay.length_relayList]
    generalize (chalD C' (ofSide F idle) Q).toPureEnv.oracleIn (H, c')
      ((sideRelay X Y Req Resp Req' Resp' Q).relayList rs) = s' at ih ⊢
    obtain ⟨hl, hsome, hm⟩ := ih
    by_cases hq : rs.length < Q
    · have hlen : s'.hist.length = rs.length := by rw [hl]; exact min_eq_left hq.le
      rw [(chalD C' (ofSide F idle) Q).update_toPureEnv_of_lt _ _ _
        (show rs.length < (chalD C' (ofSide F idle) Q).Q from hq)]
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton, hlen]
        omega
      · intro e he
        rcases List.mem_append.1 he with he | he
        · exact hsome e he
        · rw [List.mem_singleton.1 he, chalD_respond, run_mapOutput]
          rfl
      · simp only [chalD_respond, run_mapOutput, run_relayProg_ofSide, mainHist,
          List.filterMap_append, List.map_append, List.filterMap_cons, List.filterMap_nil,
          Option.map_some, List.map_cons, List.map_nil, recordOf, Option.getD_some]
        rw [← mainHist, hm, SideRelay.relayList_append_singleton]
        simp [stripEntry, sideRelay, min_eq_left hq.le, hlen]
    · rw [(chalD C' (ofSide F idle) Q).update_toPureEnv_of_le _ _ _
        (show (chalD C' (ofSide F idle) Q).Q ≤ rs.length from not_lt.1 hq)]
      refine ⟨?_, hsome, hm⟩
      rw [hl, List.length_append, List.length_singleton]
      omega

/-- **`ofSide` relays as the side relay** (`AssignRelay.RelaysChallenger`): when the outer
challenger relays the main challenger through `F` (`SideRelay.RelaysChallenger`) and the main
challenger assigns nothing (`hNA`). -/
theorem relaysChallenger_ofSide {C : Challenger X Y Req Resp} {c : C.Coins} {c' : C'.Coins}
    (hF : F.RelaysChallenger C c C' c') (hNA : C'.NoAssign) :
    (ofSide F idle).RelaysChallenger C c C' c' where
  run_eq histD r H' hlen _ {reach} := by
    obtain ⟨H, rs, rfl⟩ := reach
    obtain ⟨-, -, hm⟩ := oracleIn_chalD_ofSide F idle C' C.Q H c' rs
    rw [hF.run_eq _ _ r H' (by rw [hm, List.map_map]) (by simpa using hlen),
      run_relayProg_ofSide, hNA]
    simp

/-- **No assignment of `ofSide` is seen**: the safe lists are the empty one. -/
def safeAssign_ofSide [DecidableEq Y] [Fintype Req] [DecidableEq Req]
    [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
    [DecidableEq Resp'] [Inhabited X] [AddGroup Y] [Inhabited Req'] :
    SafeAssign C' (ofSide F idle) where
  Safe _ L := L = []
  safe_nil _ := rfl
  safe_append _ a b ha hb := by rw [ha, hb]; rfl
  safe_prog T c r h m := by
    simp [SideRelay.assignProg, OracleProg.run]
  respond_reprogram c' hist r' H L hL := by
    subst hL
    rfl

/-- **The main request of a tagged request at a side relay**: `route` at the request's number. -/
def tagMain (F : SideRelay Req Resp Req' Resp') {Q : ℕ} (p : TaggedReq X Y Req Q) : Req' :=
  F.route p.num p.req

omit [DecidableEq X] [Fintype X] [Fintype Y] [Nonempty Y] in
/-- **The numbered requests within the cap carry their positions**: relaying the requests through
`sideRelay` and reading the main request at each number is relaying them through `F`. -/
theorem map_relayList_sideRelay {Q : ℕ} (l : List Req) (hl : l.length ≤ Q) :
    ((sideRelay X Y Req Resp Req' Resp' Q).relayList l).map (fun q => F.route q.2 q.1) =
      F.relayList l := by
  refine List.ext_getElem (by simp [SideRelay.length_relayList]) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, SideRelay.relayList, List.getElem_mapIdx, sideRelay]
  rw [min_eq_left (by simp at h₁; omega)]

/-- **The main requests of `ofSide`'s multi-request relay**: within the cap, those of the tagged
requests (`tagMain`). -/
theorem mainReqs_relayOf_ofSide [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
    [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
    [Inhabited X] [AddGroup Y] [Inhabited Req'] (Q : ℕ)
    (ansM : List Req' → Req' → Option Resp') (H : X → Y) (ts : List (TaggedReq X Y Req Q))
    (hl : ts.length ≤ Q) :
    (relayOf (ofSide F idle) Q).mainReqs Q ansM H ts = ts.map (tagMain F) := by
  induction ts using List.reverseRecOn with
  | nil => rfl
  | append_singleton ts t ih =>
    simp only [List.length_append, List.length_singleton] at hl
    rw [(relayOf (ofSide F idle) Q).mainReqs_append]
    simp only [show ts.length < Q by omega, ↓reduceIte]
    rw [filterMap_runEntries_relayOf, elimProg_ofSide, ih (by omega), List.map_append]
    simp [SideRelay.trace_assignProg, tagMain]

end AssignRelay

/-- **Dropping trailing idle requests from a history**: the history along `l ++ m`, every request
of `m` the idle request `idle` and none of `l`, without its idle entries is the history along
`l`. -/
theorem filter_histAlong_append {Req Resp : Type} [DecidableEq Req]
    (ans : List Req → Req → Option Resp) (idle : Req) (l : List Req) (hl : ∀ x ∈ l, x ≠ idle) :
    ∀ m : List Req, (∀ x ∈ m, x = idle) →
      (histAlong ans (l ++ m)).filter (fun e => e.request ≠ idle) = histAlong ans l := by
  intro m
  induction m using List.reverseRecOn with
  | nil =>
    intro _
    rw [List.append_nil, List.filter_eq_self]
    intro e he
    have hm : e.request ∈ l := by
      rw [← map_request_histAlong ans l]
      exact List.mem_map_of_mem he
    simpa using hl _ hm
  | append_singleton m x ih =>
    intro hm
    rw [← List.append_assoc, histAlong_append_singleton, List.filter_append,
      ih fun y hy => hm y (List.mem_append_left _ hy)]
    simp [hm x (by simp)]

namespace AdaptiveIAlg

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) {C : Challenger X Y Req Resp} {C' : Challenger X Y Req' Resp'}

/-- **The mixed game of the patched absorbed adversary against `chalT` has trace 1**, for `A`
within its budget, when the outer challenger relays the main challenger through `G`
(`mgRun_absorbAssignP`). -/
theorem trace_mgRun_absorbAssignP {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) {c : C.Coins} {c' : C'.Coins}
    (hA : A.WithinBudget) (hrel : G.RelaysChallenger C c C' c') (hS : AssignRelay.SafeAssign C' G)
    (H : X → Y) :
    ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.mgRun (AssignRelay.chalT C' G C.Q).toPureEnv (H, c')
      true).trace = 1 := by
  have hpsd := Circuit.posSemidef_run (Equiv.refl _)
    ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.mgCirc (AssignRelay.chalT C' G C.Q).toPureEnv (H,
        c') true)
    (A.absorbAssignP Req' Resp' C.Q).toKindAlg.mgInitM.posSemidef
  refine Complex.ext ?_ (by
    rw [Complex.one_im]; exact ((Complex.nonneg_iff.1 hpsd.trace_nonneg).2).symm)
  change ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.mgRun _ _ true).trace.re = 1
  rw [A.mgRun_absorbAssignP G hrel hS H, re_trace_embed (fun p q h => by
      have h' := ((A.absorbAssignB Req' Resp' C.Q).patchPlace_injective _ _ _ _) h
      simp only [Prod.map, Prod.mk.injEq] at h'
      exact Prod.ext (A.placeClean_injective _ _ _ _ h'.1) h'.2),
    Matrix.trace_kronecker, trace_ancMat, mul_one]
  exact congrArg Complex.re (hA.trace_mgRun_eq_one _ _)

omit [Inhabited X] [Inhabited Req'] in
/-- **The main requests of the answered history at a placed state** (`placedP`), read at the
requests' numbers through a side relay `F`, are the relay through `F` of `A`'s answered requests. -/
theorem map_tagMain_history_placedP {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
    (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (F : SideRelay Req Resp Req' Resp')
    (c : C.Coins) (H : X → Y) (c' : C'.Coins) (r : A.toKindAlg.G) (a : AncReg X Y A.width) :
    ((A.absorbAssignP Req' Resp' C.Q).history (AssignRelay.chalT C' G C.Q)
        (A.placedP (C := C) G C' H c' r a)).map (fun e => AssignRelay.tagMain F e.request) =
      F.relayList ((requests (A.toKindAlg.emb C H c A.slots r).1.chal.logs).take C.Q) := by
  obtain ⟨⟨⟨w, k⟩, rq, rs, lg⟩, qs⟩ := r
  change LogReg Req A.slots at lg
  rw [show (fun e : HistoryEntry (AssignRelay.TaggedReq X Y Req C.Q)
      (AssignRelay.RespD X Y Resp Req' Resp') => AssignRelay.tagMain F e.request) =
      AssignRelay.tagMain F ∘ HistoryEntry.request from rfl, ← List.map_map, map_request_history]
  change ((requests (augLogs (G.tabAfter C.Q H c') ((AssignRelay.sideRelay X Y Req Resp Req' Resp'
      C.Q).logs lg))).take C.Q).map
    (AssignRelay.tagMain F) = F.relayList ((requests lg).take C.Q)
  rw [requests, AssignRelay.requestsBefore_augLogs_eq, ← requests, SideRelay.requests_logs,
    show AssignRelay.tagMain F = (fun q : Req × Fin (C.Q + 1) => F.route q.2 q.1) ∘ Prod.fst from
      rfl, ← List.map_map, List.map_take, map_fst_augList, SideRelay.take_relayList,
    AssignRelay.map_relayList_sideRelay F _ (List.length_take_le _ _)]


-- TODO(unbundle-M4): bridge lemma at a free relay, so that `exact` does not compare the two
-- adversary forms through `composeBothOut`; move next to `absorbAssign` as its form of
-- `toOuterMeasure_eq_relayAdv_budget`, or drop it once the shapes agree syntactically
/-- **The law of the patched absorbed adversary against `chalT` is the law of the absorbed
adversary against `C'`** (`toOuterMeasure_eq_relayAdv_budget` at `absorbAssign`), for events `P`
and `P'` that agree on the placed states within budget. Stated at a free relay `G`, so that the
shape of `absorbAssign` is compared with that of its `relayAdv` without unfolding `G`. -/
theorem toOuterMeasure_chalT_eq_absorbAssign {Xs Ys : Type} [AddGroup Ys] [Fintype Ys]
    [DecidableEq Ys] (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
    (hF : (G.relayOf Q).RelaysChallenger (AssignRelay.chalT C' G Q) C' id) (H : X → Y)
    (htr : ∀ c', ((A.absorbAssignP Req' Resp' Q).toKindAlg.mgRun
      (AssignRelay.chalT C' G Q).toPureEnv (H, c') true).trace = 1)
    (P : (A.absorbAssignP Req' Resp' Q).toKindAlg.CW (AssignRelay.chalT C' G Q) → Prop)
    (P' : (A.absorbAssign G Q).toKindAlg.CW C' → Prop)
    (himp : ∀ c' y,
      y ∈ ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.dilSet
        {r | P ((A.absorbAssignP Req' Resp' Q).toKindAlg.emb (AssignRelay.chalT C' G Q) H c'
          (A.absorbAssignP Req' Resp' Q).slots r).1} →
      queriesBefore (embR (A.absorbAssignP Req' Resp' Q).post true y).1.2.2.2
        (((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.slots +
          (A.absorbAssignP Req' Resp' Q).post) ≤
        (A.absorbAssignP Req' Resp' Q).budget + (A.absorbAssignP Req' Resp' Q).post →
      P' ((A.absorbAssignP Req' Resp' Q).relayPlace (G.relayOf Q) Q
        ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) C' H c' y))
    (hrev : ∀ c' y, (((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.relG y).1.2 = false →
      queriesBefore (embR (A.absorbAssignP Req' Resp' Q).post true y).1.2.2.2
        (((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.slots +
          (A.absorbAssignP Req' Resp' Q).post) ≤
        (A.absorbAssignP Req' Resp' Q).budget + (A.absorbAssignP Req' Resp' Q).post →
      P' ((A.absorbAssignP Req' Resp' Q).relayPlace (G.relayOf Q) Q
        ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) C' H c' y) →
        P ((A.absorbAssignP Req' Resp' Q).toKindAlg.emb (AssignRelay.chalT C' G Q) H c'
          (A.absorbAssignP Req' Resp' Q).slots
          (((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.relG y).1.1).1) :
    (((A.absorbAssignP Req' Resp' Q).toKindAlg.composeBothOut (AssignRelay.chalT C' G Q)
        id).outLaw H).toOuterMeasure {x | ∃ v ∈ x, P v} =
      (((A.absorbAssign G Q).toKindAlg.composeBothOut C' id).outLaw H).toOuterMeasure
        {x | ∃ v ∈ x, P' v} := by
  classical
  have h := (A.absorbAssignP Req' Resp' Q).toOuterMeasure_eq_relayAdv_budget (G.relayOf Q)
    ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) (AssignRelay.chalT C' G Q) C' id hF H
    htr P P' himp hrev
  rw [h, KindAlg.toOuterMeasure_outLaw_composeBothOut_id,
    @KindAlg.toOuterMeasure_outLaw_composeBothOut_id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ((A.absorbAssignP Req' Resp' Q).relayAdv (G.relayOf Q) (AssignRelay.chalT C' G Q).Q
        ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))).toKindAlg C' H P'
      fun _ => Classical.propDecidable _]
  refine congrArg ENNReal.ofReal (Finset.sum_congr rfl fun c _ => ?_)
  refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
  rfl

/-- **The law of absorbing a side relay is the law of absorbing it as an assigning relay**: up to
the removal of the idle main requests from the history, the output (without the table) and history
of the absorbed adversary `A.absorbAssign (AssignRelay.ofSide (F' s) idle) C.Q` against the main
challenger `C'` have, averaged over the side coins `s ← σ`, the law of the output and history of
`A.absorb (F' s)` against `C'`. Both equal the law of `A` against the outer challenger `C`
(`outLaw_absorb`, `toOuterMeasure_eq_sum_absorbAssignP_of_placed`,
`toOuterMeasure_eq_relayAdv_budget`). Hypotheses: the outer coins are the side coins and the main
coins (`hcoins`); at the side coins `s` the outer challenger relays `C'` through `F' s` (`hrel`);
the two answer the same number of requests (`hQ`); each relay of requests is injective (`hinj`);
`C'` assigns nothing (`hNA`); `A` stays within its budget (`hA`); no relayed request is the idle
request (`hidle`). -/
theorem toOuterMeasure_absorbAssign_ofSide {S : Type} [Fintype S] (σ : PMF S)
    (F' : S → SideRelay Req Resp Req' Resp') (idle : Req') (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (F' s).RelaysChallenger C (e.symm (s, c')) C' c') (hQ : C.Q = C'.Q)
    (hinj : ∀ s c, Function.Injective ((F' s).route c)) (hNA : C'.NoAssign)
    (hA : A.WithinBudget) (hidle : ∀ s c r, (F' s).route c r ≠ idle) (H : X → Y)
    (E : O × List (HistoryEntry Req' Resp') → Prop) :
    ∑ s, σ s * (((A.absorbAssign (AssignRelay.ofSide (F' s) idle) C.Q).toKindAlg.composeBothOut C'
      fun v => ((A.absorbAssign (AssignRelay.ofSide (F' s) idle) C.Q).output C' v,
        (A.absorbAssign (AssignRelay.ofSide (F' s) idle) C.Q).history C' v)).outLaw
          H).toOuterMeasure {x | ∃ p ∈ x, E (p.1.1, p.2.filter fun en => en.request ≠ idle)} =
      ∑ s, σ s * (((A.absorb (F' s)).toKindAlg.composeBothOut C' fun v =>
        ((A.absorb (F' s)).output C' v, (A.absorb (F' s)).history C' v)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E p} := by
  set G : S → AssignRelay X Y Req Resp Req' Resp' := fun s => AssignRelay.ofSide (F' s) idle
  have hrelG : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c' := fun s c' =>
    AssignRelay.relaysChallenger_ofSide (F' s) idle C' (hrel s c') hNA
  have hS : ∀ s, AssignRelay.SafeAssign C' (G s) := fun s =>
    AssignRelay.safeAssign_ofSide (F' s) idle C'
  -- the event of `A` against the outer challenger
  let Mid : A.toKindAlg.CW C → Prop := fun v => E (A.output C v,
    histAlong (C'.toPureEnv.answerAfter (H, (e v.chal.coins).2))
      ((F' (e v.chal.coins).1).relayList ((requests v.chal.logs).take C.Q)))
  -- the event of the patched absorbed adversary against `chalT`
  let Etag : ∀ s, (A.absorbAssignP Req' Resp' C.Q).toKindAlg.CW (AssignRelay.chalT C' (G s) C.Q) →
      Prop := fun s v =>
    E (((A.absorbAssignP Req' Resp' C.Q).output (AssignRelay.chalT C' (G s) C.Q) v).1,
      histAlong (C'.toPureEnv.answerAfter (H, v.chal.coins))
        (((A.absorbAssignP Req' Resp' C.Q).history (AssignRelay.chalT C' (G s) C.Q) v).map
          fun en => AssignRelay.tagMain (F' s) en.request))
  -- the event of the absorbed adversary against `C'`
  let P' : ∀ s, (A.absorbAssign (G s) C.Q).toKindAlg.CW C' → Prop := fun s v =>
    E (((A.absorbAssign (G s) C.Q).output C' v).1,
      ((A.absorbAssign (G s) C.Q).history C' v).filter fun en => en.request ≠ idle)
  have hB := A.toOuterMeasure_eq_sum_absorbAssignP_of_placed σ G e hcoins hrelG hS H Mid Etag
    fun s c' r a => by
      have ho := congrArg Prod.fst (A.readout_absorbAssignP (G s) (hrelG s c') (hS s) H r a)
      refine Iff.of_eq (congrArg₂ (fun o h => E (o, h)) ho ?_)
      rw [A.map_tagMain_history_placedP (G s) (F' s) (e.symm (s, c')) H c' r a]
      change _ = histAlong (C'.toPureEnv.answerAfter (H, (e (e.symm (s, c'))).2))
        ((F' (e (e.symm (s, c'))).1).relayList _)
      rw [Equiv.apply_symm_apply]
      rfl
  have hC : ∀ s, (((A.absorbAssignP Req' Resp' C.Q).toKindAlg.composeBothOut
      (AssignRelay.chalT C' (G s) C.Q) id).outLaw H).toOuterMeasure {x | ∃ v ∈ x, Etag s v} =
      (((A.absorbAssign (G s) C.Q).toKindAlg.composeBothOut C' id).outLaw H).toOuterMeasure
        {x | ∃ v ∈ x, P' s v} := by
    intro s
    have hkey : ∀ c' y, queriesBefore (embR (A.absorbAssignP Req' Resp' C.Q).post true y).1.2.2.2
        (((A.absorbAssignP Req' Resp' C.Q).toTPKindAlg true).unitOut.slots + (A.absorbAssignP Req'
            Resp' C.Q).post) ≤
        (A.absorbAssignP Req' Resp' C.Q).budget + (A.absorbAssignP Req' Resp' C.Q).post →
        (P' s ((A.absorbAssignP Req' Resp' C.Q).relayPlace ((G s).relayOf C.Q) C.Q
          ((A.absorbAssignP Req' Resp' C.Q).relayOut ((G s).relayOf C.Q)) C' H c' y) ↔
        Etag s ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' (G s) C.Q) H c'
          (A.absorbAssignP Req' Resp' C.Q).slots
          (((A.absorbAssignP Req' Resp' C.Q).toTPKindAlg true).unitOut.relG y).1.1).1) := by
      intro c' y hb
      have ho := (A.absorbAssignP Req' Resp' C.Q).output_relayPlace ((G s).relayOf C.Q)
        (AssignRelay.chalT C' (G s) C.Q).Q C' H c' y (AssignRelay.chalT C' (G s) C.Q) c'
      obtain ⟨k, hk⟩ := (A.absorbAssignP Req' Resp' C.Q).history_relayPlace_eq ((G s).relayOf C.Q)
        ((A.absorbAssignP Req' Resp' C.Q).relayOut ((G s).relayOf C.Q))
        (AssignRelay.chalT C' (G s) C.Q) C' H c' y hb
      have hh := (A.absorbAssignP Req' Resp' C.Q).history_emb_relG (AssignRelay.chalT C' (G s) C.Q)
        H c' y
      set ts := (requests (splitLogs y).2).take (AssignRelay.chalT C' (G s) C.Q).Q
      have hts : ts.length ≤ C.Q := List.length_take_le _ _
      have hm := AssignRelay.mainReqs_relayOf_ofSide (F' s) idle C.Q
        (C'.toPureEnv.answerAfter (H, c')) H ts hts
      refine Iff.of_eq (congrArg₂ (fun o h => E (o, h)) (congrArg Prod.fst ho) ?_)
      erw [hk, hh, show (fun en : HistoryEntry (AssignRelay.TaggedReq X Y Req C.Q)
          (AssignRelay.RespD X Y Resp Req' Resp') => AssignRelay.tagMain (F' s) en.request) =
          AssignRelay.tagMain (F' s) ∘ HistoryEntry.request from rfl, ← List.map_map,
        map_request_histAlong]
      change List.filter _ (histAlong _ ((((G s).relayOf C.Q).mainReqs C.Q _ H ts ++
        List.replicate k ((G s).relayOf C.Q).idle).take C'.Q)) = _
      rw [hm, List.take_append, List.take_of_length_le (by simp; omega)]
      refine filter_histAlong_append _ idle _ (fun x hx => ?_) _ fun x hx => ?_
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
        exact hidle s _ _
      · exact List.eq_of_mem_replicate (List.mem_of_mem_take hx)
    exact A.toOuterMeasure_chalT_eq_absorbAssign (G s) C.Q
      ((G s).relaysChallenger_relayOf C' C.Q hNA hQ.le) H
      (fun c' => A.trace_mgRun_absorbAssignP (G s) hA (hrelG s c') (hS s) H) (Etag s) (P' s)
      (fun c' y hy hb => (hkey c' y hb).2 hy.2) fun c' y _ hb h => (hkey c' y hb).1 h
  -- the absorbed side: `outLaw_absorb`
  have hD := A.outLaw_absorb σ F' e hcoins (fun H s c' => (hrel s c').relays H _) hinj H
    (fun d _ rlg c _ => E (A.out d.1.1.1,
      histAlong (C'.toPureEnv.answerAfter (H, (e c).2)) ((requests rlg).take C'.Q)))
  calc _ = ∑ s, σ s * (((A.absorbAssignP Req' Resp' C.Q).toKindAlg.composeBothOut
          (AssignRelay.chalT C' (G s) C.Q) id).outLaw H).toOuterMeasure
            {x | ∃ v ∈ x, Etag s v} := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [KindAlg.toOuterMeasure_outLaw_composeBothOut, hC s]
    _ = ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure {x | ∃ v ∈ x, Mid v} := hB.symm
    _ = _ := by
        refine Eq.trans ?_ (hD.trans (Finset.sum_congr rfl fun s _ => ?_))
        · refine congrArg _ (Set.ext fun o => ?_)
          refine exists_congr fun v => and_congr_right fun _ => ?_
          change E (_, _) ↔ E (_, _)
          rw [SideRelay.requests_logs, SideRelay.take_relayList, hQ]
          rfl
        · rw [KindAlg.outLaw_composeBothOut_congr_emb _ C' H
            (f₂ := fun v => ((A.absorb (F' s)).output C' v,
              histAlong (C'.toPureEnv.answerAfter (H, v.chal.coins))
                ((requests v.chal.logs).take C'.Q)))
            fun c r => Prod.ext rfl (KindAlg.history_stateAt_emb _ C' H c r),
            KindAlg.toOuterMeasure_outLaw_composeBothOut _ _ (fun v => ((A.absorb (F' s)).output C' v,
              histAlong (C'.toPureEnv.answerAfter (H, v.chal.coins))
                ((requests v.chal.logs).take C'.Q)))]
          simp only [Equiv.apply_symm_apply]
          rfl

end AdaptiveIAlg

end GordieHowe.Quantum
