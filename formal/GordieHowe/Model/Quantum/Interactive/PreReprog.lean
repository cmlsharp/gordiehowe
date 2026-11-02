-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RevealedPair

@[expose] public section

/-!
# A challenger that reprograms the base component at its points before answering

For a challenger `C₀` that assigns nothing and a classical program computing, at each request, a
finite set of points, `Challenger.preReprog C₀ pts` is the challenger that, at request `j`,
computes the points `S`, reads the oracle there, assigns to each `x ∈ S` the value with base
component a fresh `Z j x` and second component that of the oracle at `x` (`reprogBase`,
`GordieHowe/Model/Quantum/Interactive/RevealedPair.lean`), and answers as `C₀` at the reprogrammed
oracle. This is the challenger `C₁` of a `RevealedPair` (GHHM21's reprogramming challenger).

- `OracleProg.withAssign ass p`: `p` with its queries at the points of `ass` answered from the list;
  `OracleProg.run_withAssign`: it runs as `p` at `H.reprogram ass` (later assignments take
  precedence in both); `OracleProg.length_trace_withAssign_le`: it makes at most the queries of `p`.
- `reprogAssigns sp S z ys`: the assignment list of `reprogBase`; `reprogram_reprogAssigns`: it
  reprograms the oracle to `reprogBase sp S z H` when `ys` lists the oracle's values on `S`.
- `Challenger.preReprog`, `Challenger.run_respond_preReprog`: the challenger and its reply.
- `Challenger.prodLaw_map_right`: a product law with its second factor mapped.
- `Challenger.RevealedPair.ofPreReprog`: **the reprogramming challenger is the counterpart of a
  revealed pair** for a plain, causal challenger reading the history through its requests and a
  point program meeting the point conditions of `RevealedPair`.
- `Challenger.preReprogKeep keep`: the same replies, but of the assignments of `reprogBase` only
  those at the kept points stay in force; `run_respond_preReprogKeep`, `response_preReprogKeep`.
- `Challenger.hiddenKeep`, `Challenger.oracleByReq_preReprogKeep_eq`: **the oracles in force of the
  kept-only and the full reprogramming challenger agree outside the points not kept**;
  `response_preReprogKeep_eq_of_reads`: their responses agree when the reads avoid those points;
  `respondsByRequests_preReprogKeep`.
- `reprogram_reprogAssigns_list`, `filter_reprogAssigns`, `reprogram_filter_reprogAssigns`: the
  assignment list of `reprogBase` on a list of points, and kept at the points of a set.
-/

namespace GordieHowe

namespace OracleProg

variable {A B R : Type*} [DecidableEq A]

/-- **A program with its queries at the assigned points answered from the assignment list**: a
query at `a` with a last assignment `a := b` in `ass` continues with `b`, the others are queries. -/
def withAssign (ass : List (Quantum.Assignment A B)) : OracleProg A B R → OracleProg A B R
  | pure r => pure r
  | query a k =>
    match Quantum.lastAssign ass a with
    | some b => withAssign ass (k b)
    | none => query a fun b => withAssign ass (k b)

/-- **The program with its assigned queries answered runs as the program at the reprogrammed
oracle.** -/
theorem run_withAssign (ass : List (Quantum.Assignment A B)) (H : A → B) :
    ∀ p : OracleProg A B R, (p.withAssign ass).run H = p.run (H.reprogram ass)
  | pure _ => rfl
  | query a k => by
    rw [run_query]
    rcases h : Quantum.lastAssign ass a with _ | b
    · simp only [withAssign, h, run_query]
      rw [run_withAssign ass H (k (H a)), Quantum.reprogram_apply_eq_lastAssign, h]
      rfl
    · simp only [withAssign, h]
      rw [run_withAssign ass H (k b), Quantum.reprogram_apply_eq_lastAssign, h]
      rfl

/-- **The program with its assigned queries answered makes at most the program's queries.** -/
theorem length_trace_withAssign_le (ass : List (Quantum.Assignment A B)) (H : A → B) :
    ∀ p : OracleProg A B R,
      ((p.withAssign ass).trace H).length ≤ (p.trace (H.reprogram ass)).length
  | pure _ => le_rfl
  | query a k => by
    rw [trace_query, List.length_cons]
    rcases h : Quantum.lastAssign ass a with _ | b
    · simp only [withAssign, h, trace_query, List.length_cons]
      have := length_trace_withAssign_le ass H (k (H a))
      rw [Quantum.reprogram_apply_eq_lastAssign, h]
      exact Nat.succ_le_succ this
    · simp only [withAssign, h]
      have := length_trace_withAssign_le ass H (k b)
      rw [Quantum.reprogram_apply_eq_lastAssign, h]
      exact this.trans (Nat.le_succ _)

end OracleProg

namespace Quantum

variable {X Y Y₁ Y₂ : Type} [DecidableEq X] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

/-- **The assignment list of `reprogBase`**: for the points `l` (listed without repetition) and the
oracle's values `ys` on them, the assignments `x := sp.symm (z x, (sp y).2)`. -/
def reprogAssigns (sp : Y ≃+ Y₁ × Y₂) (z : X → Y₁) (l : List X) (ys : List Y) :
    List (Assignment X Y) :=
  (l.zip ys).map fun p => ⟨p.1, sp.symm (z p.1, (sp p.2).2)⟩

/-- **The assignment list of `reprogBase` reprograms the oracle to `reprogBase`** when the points
are those of `S` without repetition and `ys` lists the oracle's values on them. -/
theorem reprogram_reprogAssigns (sp : Y ≃+ Y₁ × Y₂) (S : Finset X) (z : X → Y₁) (H : X → Y) :
    H.reprogram (reprogAssigns sp z S.toList (S.toList.map H)) = reprogBase sp S z H := by
  funext x
  rw [reprogram_apply_eq_lastAssign]
  have key : ∀ (l : List X), l.Nodup →
      (lastAssign (reprogAssigns sp z l (l.map H)) x).getD (H x) =
        if x ∈ l then sp.symm (z x, (sp (H x)).2) else H x := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil => simp [reprogAssigns, lastAssign]
    | append_singleton l a ih =>
      have hl' : l.Nodup := (List.nodup_append.1 hl).1
      have ha : a ∉ l := fun h => by
        have := (List.nodup_append.1 hl).2.2 a h a (List.mem_singleton_self a)
        exact this rfl
      have hz : reprogAssigns sp z (l ++ [a]) ((l ++ [a]).map H) =
          reprogAssigns sp z l (l.map H) ++ [⟨a, sp.symm (z a, (sp (H a)).2)⟩] := by
        simp only [reprogAssigns, List.map_append, List.map_cons, List.map_nil]
        rw [List.zip_append (by simp)]
        simp
      rw [hz, lastAssign_append_singleton]
      by_cases hx : a = x
      · subst hx
        simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
        rw [ih hl']
        simp [List.mem_append, Ne.symm hx]
  rw [key S.toList (Finset.nodup_toList S)]
  simp [reprogBase, Finset.mem_toList]

/-- **The assignment list of `reprogBase` on a list of points without repetition** reprograms the
oracle at the listed points. -/
theorem reprogram_reprogAssigns_list (sp : Y ≃+ Y₁ × Y₂) (z : X → Y₁) (H : X → Y) {l : List X}
    (hl : l.Nodup) (x : X) :
    H.reprogram (reprogAssigns sp z l (l.map H)) x =
      if x ∈ l then sp.symm (z x, (sp (H x)).2) else H x := by
  rw [reprogram_apply_eq_lastAssign]
  induction l using List.reverseRecOn with
  | nil => simp [reprogAssigns, lastAssign]
  | append_singleton l a ih =>
    have hl' : l.Nodup := (List.nodup_append.1 hl).1
    have hz : reprogAssigns sp z (l ++ [a]) ((l ++ [a]).map H) =
        reprogAssigns sp z l (l.map H) ++ [⟨a, sp.symm (z a, (sp (H a)).2)⟩] := by
      simp only [reprogAssigns, List.map_append, List.map_cons, List.map_nil]
      rw [List.zip_append (by simp)]
      simp
    rw [hz, lastAssign_append_singleton]
    by_cases hx : a = x
    · subst hx
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx), ih hl']
      simp [List.mem_append, Ne.symm hx]

/-- **The assignments of `reprogBase` at the points of a set** are those of `reprogBase` on the
listed points in the set. -/
theorem filter_reprogAssigns (sp : Y ≃+ Y₁ × Y₂) (z : X → Y₁) (H : X → Y) (T : Finset X)
    (l : List X) :
    (reprogAssigns sp z l (l.map H)).filter (fun a => decide (a.input ∈ T)) =
      reprogAssigns sp z (l.filter fun x => decide (x ∈ T))
        ((l.filter fun x => decide (x ∈ T)).map H) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [reprogAssigns] at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons]
    by_cases ha : a ∈ T
    · simp only [ha, decide_true, ↓reduceIte, List.map_cons, List.zip_cons_cons]
      rw [ih]
    · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- **The assignments of `reprogBase` kept at the points of `T`** reprogram the oracle at the
points of `S` in `T`. -/
theorem reprogram_filter_reprogAssigns (sp : Y ≃+ Y₁ × Y₂) (S T : Finset X) (z : X → Y₁)
    (H : X → Y) (x : X) :
    H.reprogram ((reprogAssigns sp z S.toList (S.toList.map H)).filter
        (fun a => decide (a.input ∈ T))) x =
      if x ∈ S ∧ x ∈ T then sp.symm (z x, (sp (H x)).2) else H x := by
  rw [filter_reprogAssigns, reprogram_reprogAssigns_list sp z H
    ((Finset.nodup_toList S).filter _)]
  simp [List.mem_filter, Finset.mem_toList]

end Quantum

namespace Quantum

namespace Challenger

variable {X Y Y₁ Y₂ Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]

/-- **The challenger that reprograms the base component at its points before answering**
(module docstring): coins the fresh base values `Z : Fin Q → X → Y₁` (uniform) and the coins of
`C₀`; at request `j < Q`, the points `S` of `pts` (at most `qp` queries, at most `K` points), the
oracle read on `S`, the assignments of `reprogBase sp S (Z j)`, and the reply of `C₀` at the
reprogrammed oracle (its queries at `S` answered from the assignments), with `C₀`'s assignments
appended. From request `Q` on it answers as `C₀`. -/
noncomputable def preReprog (C₀ : Challenger X Y Req Resp) (sp : Y ≃+ Y₁ × Y₂)
    (pts : C₀.Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Finset X))
    (qp K : ℕ) (hqp : ∀ c hist req, (pts c hist req).QueriesLE qp)
    (hK : ∀ c hist req H, ((pts c hist req).run H).card ≤ K) : Challenger X Y Req Resp where
  Coins := (Fin C₀.Q → X → Y₁) × C₀.Coins
  coins := prodLaw (PMF.uniformOfFintype _) C₀.coins
  Q := C₀.Q
  q := qp + K + C₀.q
  respond ω hist req :=
    if h : hist.length < C₀.Q then
      (pts ω.2 hist req).bind fun S =>
        (OracleProg.queryAll S.toList).bind fun ys =>
          ((C₀.respond ω.2 hist req).withAssign
            (reprogAssigns sp (ω.1 ⟨hist.length, h⟩) S.toList ys)).mapOutput fun r =>
            ⟨r.response, reprogAssigns sp (ω.1 ⟨hist.length, h⟩) S.toList ys ++ r.assignments⟩
    else C₀.respond ω.2 hist req
  respond_queries ω hist req H := by
    split_ifs with h
    · rw [OracleProg.trace_bind, OracleProg.trace_bind, OracleProg.trace_mapOutput,
        List.length_append, List.length_append, OracleProg.trace_queryAll, Finset.length_toList,
        OracleProg.run_queryAll]
      have h1 := hqp ω.2 hist req H
      have h2 := hK ω.2 hist req H
      have h3 := (OracleProg.length_trace_withAssign_le
        (reprogAssigns sp (ω.1 ⟨hist.length, h⟩) ((pts ω.2 hist req).run H).toList
          (((pts ω.2 hist req).run H).toList.map H)) H (C₀.respond ω.2 hist req)).trans
        (C₀.respond_queries ω.2 hist req _)
      omega
    · exact (C₀.respond_queries ω.2 hist req H).trans (Nat.le_add_left _ _)

variable {C₀ : Challenger X Y Req Resp} {sp : Y ≃+ Y₁ × Y₂}
  {pts : C₀.Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Finset X)}
  {qp K : ℕ} {hqp : ∀ c hist req, (pts c hist req).QueriesLE qp}
  {hK : ∀ c hist req H, ((pts c hist req).run H).card ≤ K}

omit [Fintype Y] [Nonempty Y] in
/-- **The reply of the reprogramming challenger** at request `j < Q`: the response of `C₀` at the
oracle reprogrammed on the points to the fresh base values, and the assignments of `reprogBase`
followed by those of `C₀` there. -/
theorem run_respond_preReprog (Z : Fin C₀.Q → X → Y₁) (c : C₀.Coins)
    (hist : List (HistoryEntry Req Resp)) (req : Req) (H : X → Y) (h : hist.length < C₀.Q) :
    ((C₀.preReprog sp pts qp K hqp hK).respond (Z, c) hist req).run H =
      ⟨((C₀.respond c hist req).run
          (reprogBase sp ((pts c hist req).run H) (Z ⟨hist.length, h⟩) H)).response,
        reprogAssigns sp (Z ⟨hist.length, h⟩) ((pts c hist req).run H).toList
            (((pts c hist req).run H).toList.map H) ++
          ((C₀.respond c hist req).run
            (reprogBase sp ((pts c hist req).run H) (Z ⟨hist.length, h⟩) H)).assignments⟩ := by
  simp only [preReprog, h, ↓reduceDIte]
  rw [OracleProg.run_bind, OracleProg.run_bind,
    OracleProg.run_queryAll, OracleProg.run_mapOutput, OracleProg.run_withAssign,
    reprogram_reprogAssigns]

/-- **A product law with its second factor mapped** is the product law mapped on the second
component. -/
theorem prodLaw_map_right {α β γ : Type*} (p : PMF α) (q : PMF β) (f : β → γ) :
    prodLaw p (q.map f) = (prodLaw p q).map (Prod.map id f) := by
  simp only [prodLaw, PMF.map_bind, PMF.map_comp]
  rfl

variable (C₀ sp pts qp K hqp hK) in
/-- **The reprogramming challenger is the counterpart of a revealed pair** (GHHM21's challenger
`C₁`): for a plain challenger `C₀` with coins `(ω₀, c) ← ν ⊗ ζ^Q` read through `enc₀`, causal and
reading the history only through its requests, and a point program reading the history only
through its requests whose points, as a function of the requests, satisfy the conditions of
`RevealedPair` (`pts_subset`, `pts_causal`, `pts_reads`, `pts_le`). -/
noncomputable def RevealedPair.ofPreReprog {B : Set X} {ε : ℝ}
    {Ω₀ Cn : Type} [Fintype Ω₀] [DecidableEq Ω₀] [Fintype Cn] [DecidableEq Cn]
    (ν : PMF Ω₀) (ζ : PMF Cn) (enc₀ : Ω₀ × (Fin C₀.Q → Cn) → C₀.Coins)
    (coins₀ : C₀.coins = (prodLaw ν (PMF.pi fun _ => ζ)).map enc₀)
    (plain : ∀ c hist req H, ((C₀.respond c hist req).run H).assignments = [])
    (byRequests₀ : C₀.RespondsByRequests)
    (causal : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req,
      (∀ i : Fin C₀.Q, (i : ℕ) ≤ hist.length → c i = c' i) →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req)
    (hptsReq : ∀ c (hist hist' : List (HistoryEntry Req Resp)) req,
      hist.map HistoryEntry.request = hist'.map HistoryEntry.request →
      pts c hist req = pts c hist' req)
    (pts_subset : ∀ ω₀ c rs req O,
      (((pts (enc₀ (ω₀, c)) (histOf rs) req).run O : Finset X) : Set X) ⊆ B)
    (pts_causal : ∀ ω₀ (c c' : Fin C₀.Q → Cn) rs req O,
      (∀ i : Fin C₀.Q, (i : ℕ) ≤ rs.length → c i = c' i) →
      (pts (enc₀ (ω₀, c)) (histOf rs) req).run O = (pts (enc₀ (ω₀, c')) (histOf rs) req).run O)
    (pts_reads : ∀ ω₀ c rs req (O O' : X → Y), (∀ x ∉ B, O x = O' x) →
      (∀ x, (sp (O x)).2 = (sp (O' x)).2) →
      (pts (enc₀ (ω₀, c)) (histOf rs) req).run O = (pts (enc₀ (ω₀, c)) (histOf rs) req).run O')
    (pts_le : ∀ ω₀ c rs req O x (h : rs.length < C₀.Q),
      (ζ.toOuterMeasure {c' | x ∈ (pts (enc₀ (ω₀, Function.update c ⟨rs.length, h⟩ c'))
        (histOf rs) req).run O}).toReal ≤ ε) :
    RevealedPair sp B ε C₀ (C₀.preReprog sp pts qp K hqp hK) where
  Ω₀ := Ω₀
  Cn := Cn
  ν := ν
  ζ := ζ
  enc₀ := enc₀
  coins₀ := coins₀
  plain := plain
  byRequests₀ := byRequests₀
  causal := causal
  pts ω₀ c rs req O := (pts (enc₀ (ω₀, c)) (histOf rs) req).run O
  pts_subset := pts_subset
  pts_causal := pts_causal
  pts_reads := pts_reads
  pts_le := pts_le
  enc₁ p := (p.1, enc₀ p.2)
  coins₁ := by
    change prodLaw (PMF.uniformOfFintype _) C₀.coins = _
    rw [coins₀, prodLaw_map_right]
    rfl
  byRequests₁ c hist hist' req hh := by
    have hlen : hist.length = hist'.length := by
      simpa using congrArg List.length hh
    simp only [preReprog, hptsReq c.2 hist hist' req hh, byRequests₀ c.2 hist hist' req hh, hlen]
  reprog Z ω hist req H h := by
    have hp : pts (enc₀ ω) (histOf (hist.map HistoryEntry.request)) req = pts (enc₀ ω) hist req :=
      hptsReq _ _ _ req (map_request_histOf _)
    change (((C₀.preReprog sp pts qp K hqp hK).respond (Z, enc₀ ω) hist req).run H).response = _ ∧
      H.reprogram
          (((C₀.preReprog sp pts qp K hqp hK).respond (Z, enc₀ ω) hist req).run H).assignments
        = _
    rw [run_respond_preReprog Z (enc₀ ω) hist req H h, hp]
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [plain, List.append_nil, reprogram_reprogAssigns]
  Q_eq := rfl

variable (C₀ sp pts qp K hqp hK) in
/-- **The reprogramming challenger keeping only some of its assignments**: at request `j < Q` it
answers exactly as `preReprog` (the reply of `C₀` at the oracle reprogrammed on all the points
`S` of the request), but of the assignments of `reprogBase` it keeps in force afterwards only
those at the points of `keep c hist req r`, `r` the response. From request `Q` on it answers as
`C₀`. Against `preReprog`, the oracles in force differ only at the points not kept. -/
noncomputable def preReprogKeep
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X) :
    Challenger X Y Req Resp where
  Coins := (Fin C₀.Q → X → Y₁) × C₀.Coins
  coins := prodLaw (PMF.uniformOfFintype _) C₀.coins
  Q := C₀.Q
  q := qp + K + C₀.q
  respond ω hist req :=
    if h : hist.length < C₀.Q then
      (pts ω.2 hist req).bind fun S =>
        (OracleProg.queryAll S.toList).bind fun ys =>
          ((C₀.respond ω.2 hist req).withAssign
            (reprogAssigns sp (ω.1 ⟨hist.length, h⟩) S.toList ys)).mapOutput fun r =>
            ⟨r.response, (reprogAssigns sp (ω.1 ⟨hist.length, h⟩) S.toList ys).filter
              (fun a => decide (a.input ∈ keep ω.2 hist req r.response)) ++ r.assignments⟩
    else C₀.respond ω.2 hist req
  respond_queries ω hist req H := by
    split_ifs with h
    · rw [OracleProg.trace_bind, OracleProg.trace_bind, OracleProg.trace_mapOutput,
        List.length_append, List.length_append, OracleProg.trace_queryAll, Finset.length_toList,
        OracleProg.run_queryAll]
      have h1 := hqp ω.2 hist req H
      have h2 := hK ω.2 hist req H
      have h3 := (OracleProg.length_trace_withAssign_le
        (reprogAssigns sp (ω.1 ⟨hist.length, h⟩) ((pts ω.2 hist req).run H).toList
          (((pts ω.2 hist req).run H).toList.map H)) H (C₀.respond ω.2 hist req)).trans
        (C₀.respond_queries ω.2 hist req _)
      omega
    · exact (C₀.respond_queries ω.2 hist req H).trans (Nat.le_add_left _ _)

omit [Fintype Y] [Nonempty Y] in
/-- **The reply of the kept-only reprogramming challenger** at request `j < Q`: the response of
`preReprog`, and the assignments of `reprogBase` at the kept points followed by those of `C₀`. -/
theorem run_respond_preReprogKeep
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (Z : Fin C₀.Q → X → Y₁) (c : C₀.Coins)
    (hist : List (HistoryEntry Req Resp)) (req : Req) (H : X → Y) (h : hist.length < C₀.Q) :
    ((C₀.preReprogKeep sp pts qp K hqp hK keep).respond (Z, c) hist req).run H =
      ⟨((C₀.respond c hist req).run
          (reprogBase sp ((pts c hist req).run H) (Z ⟨hist.length, h⟩) H)).response,
        (reprogAssigns sp (Z ⟨hist.length, h⟩) ((pts c hist req).run H).toList
            (((pts c hist req).run H).toList.map H)).filter
          (fun a => decide (a.input ∈ keep c hist req ((C₀.respond c hist req).run
            (reprogBase sp ((pts c hist req).run H) (Z ⟨hist.length, h⟩) H)).response)) ++
          ((C₀.respond c hist req).run
            (reprogBase sp ((pts c hist req).run H) (Z ⟨hist.length, h⟩) H)).assignments⟩ := by
  simp only [preReprogKeep, h, ↓reduceDIte]
  rw [OracleProg.run_bind, OracleProg.run_bind,
    OracleProg.run_queryAll, OracleProg.run_mapOutput, OracleProg.run_withAssign,
    reprogram_reprogAssigns]

omit [Fintype Y] [Nonempty Y] in
/-- **The kept-only and the full reprogramming challenger give the same response** to every
request at every oracle. -/
theorem response_preReprogKeep
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (ω : (Fin C₀.Q → X → Y₁) × C₀.Coins) (hist : List (HistoryEntry Req Resp)) (req : Req)
    (H : X → Y) :
    (((C₀.preReprogKeep sp pts qp K hqp hK keep).respond ω hist req).run H).response =
      (((C₀.preReprog sp pts qp K hqp hK).respond ω hist req).run H).response := by
  by_cases h : hist.length < C₀.Q
  · rw [run_respond_preReprogKeep keep ω.1 ω.2 hist req H h,
      run_respond_preReprog ω.1 ω.2 hist req H h]
  · simp only [preReprogKeep, preReprog, h, ↓reduceDIte]

variable (C₀ sp pts qp K hqp hK) in
/-- **The points of a request that the kept-only challenger leaves hidden**: the points of the
request after the requests `rs`, at the oracle in force of `preReprogKeep`, outside the kept
points of its response. -/
noncomputable def hiddenKeep
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (ω : (Fin C₀.Q → X → Y₁) × C₀.Coins) (H : X → Y) (rs : List Req) (req : Req) : Finset X :=
  (pts ω.2 (histOf rs) req).run ((C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq ω H rs) \
    keep ω.2 (histOf rs) req
      (((C₀.preReprogKeep sp pts qp K hqp hK keep).respond ω (histOf rs) req).run
        ((C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq ω H rs)).response

omit [Fintype Y] [Nonempty Y] in
/-- **The oracles in force of the kept-only and the full reprogramming challenger agree outside
the hidden points**: for a plain `C₀` and points in `B` read only through the oracle outside `B`
and its second components, after the requests `rs` the two oracles in force agree at every point
outside the hidden points (`hiddenKeep`) of the requests of `rs` numbered below `Q`. -/
theorem oracleByReq_preReprogKeep_eq {B : Set X}
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (plain : ∀ c hist req H, ((C₀.respond c hist req).run H).assignments = [])
    (hsub : ∀ c hist req O, (((pts c hist req).run O : Finset X) : Set X) ⊆ B)
    (hreads : ∀ c hist req (O O' : X → Y), (∀ x ∉ B, O x = O' x) →
      (∀ x, (sp (O x)).2 = (sp (O' x)).2) → (pts c hist req).run O = (pts c hist req).run O')
    (ω : (Fin C₀.Q → X → Y₁) × C₀.Coins) (H : X → Y) (rs : List Req) (x : X)
    (hx : ∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length < C₀.Q →
      x ∉ C₀.hiddenKeep sp pts qp K hqp hK keep ω H rs₀ req) :
    (C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq ω H rs x =
      (C₀.preReprog sp pts qp K hqp hK).oracleByReq ω H rs x := by
  obtain ⟨Z, c⟩ := ω
  set Ok := (C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq (Z, c) H with hOk
  set Of := (C₀.preReprog sp pts qp K hqp hK).oracleByReq (Z, c) H with hOf
  -- both oracles agree with `H` outside `B` and in the second components, and with each other
  -- outside the hidden points
  have key : ∀ rs : List Req, (∀ y ∉ B, Ok rs y = H y) ∧ (∀ y, (sp (Ok rs y)).2 = (sp (H y)).2) ∧
      (∀ y ∉ B, Of rs y = H y) ∧ (∀ y, (sp (Of rs y)).2 = (sp (H y)).2) ∧
      ∀ y, (∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length < C₀.Q →
        y ∉ C₀.hiddenKeep sp pts qp K hqp hK keep (Z, c) H rs₀ req) → Ok rs y = Of rs y := by
    intro rs
    induction rs using List.reverseRecOn with
    | nil => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
    | append_singleton rs req ih =>
      obtain ⟨hk1, hk2, hf1, hf2, hkf⟩ := ih
      have hpre : ∀ y, (∀ rs₀ req', rs₀ ++ [req'] <+: rs ++ [req] → rs₀.length < C₀.Q →
          y ∉ C₀.hiddenKeep sp pts qp K hqp hK keep (Z, c) H rs₀ req') →
          ∀ rs₀ req', rs₀ ++ [req'] <+: rs → rs₀.length < C₀.Q →
            y ∉ C₀.hiddenKeep sp pts qp K hqp hK keep (Z, c) H rs₀ req' :=
        fun y hy rs₀ req' h hl => hy rs₀ req' (h.trans (List.prefix_append _ _)) hl
      have ek := oracleByReq_append_singleton (C := C₀.preReprogKeep sp pts qp K hqp hK keep)
        (Z, c) H rs req
      have ef := oracleByReq_append_singleton (C := C₀.preReprog sp pts qp K hqp hK)
        (Z, c) H rs req
      rw [← hOk] at ek
      rw [← hOf] at ef
      rw [ek, ef]
      have hQk : (C₀.preReprogKeep sp pts qp K hqp hK keep).Q = C₀.Q := rfl
      have hQf : (C₀.preReprog sp pts qp K hqp hK).Q = C₀.Q := rfl
      rw [hQk, hQf]
      by_cases hq : rs.length < C₀.Q
      · have hlen : (histOf (Resp := Resp) rs).length < C₀.Q := by simpa [histOf] using hq
        simp only [hq, ↓reduceIte]
        rw [run_respond_preReprogKeep keep Z c (histOf rs) req (Ok rs) hlen,
          run_respond_preReprog Z c (histOf rs) req (Of rs) hlen]
        dsimp only
        rw [plain, plain, List.append_nil, List.append_nil]
        -- the points of the request are the same at both oracles
        have hS : (pts c (histOf rs) req).run (Of rs) = (pts c (histOf rs) req).run (Ok rs) :=
          hreads c (histOf rs) req (Of rs) (Ok rs) (fun y hy => (hf1 y hy).trans (hk1 y hy).symm)
            (fun y => (hf2 y).trans (hk2 y).symm)
        rw [hS, reprogram_reprogAssigns]
        set S := (pts c (histOf rs) req).run (Ok rs) with hSdef
        set T := keep c (histOf rs) req ((C₀.respond c (histOf rs) req).run
          (reprogBase sp S (Z ⟨(histOf (Resp := Resp) rs).length, hlen⟩) (Ok rs))).response
          with hTdef
        have hSB : ∀ y ∈ S, y ∈ B := fun y hy => hsub c (histOf rs) req (Ok rs) hy
        -- the hidden points of this request
        have hhid : C₀.hiddenKeep sp pts qp K hqp hK keep (Z, c) H rs req = S \ T := by
          unfold hiddenKeep
          rw [← hOk]
          dsimp only
          rw [run_respond_preReprogKeep keep Z c (histOf rs) req (Ok rs) hlen]
        refine ⟨fun y hy => ?_, fun y => ?_, fun y hy => ?_, fun y => ?_, fun y hy => ?_⟩
        · rw [reprogram_filter_reprogAssigns]
          have : ¬ (y ∈ S ∧ y ∈ T) := fun h => hy (hSB y h.1)
          rw [ite_eq_right_of_eq_false _ _ (eq_false this), hk1 y hy]
        · rw [reprogram_filter_reprogAssigns]
          split_ifs
          · rw [AddEquiv.apply_symm_apply, hk2 y]
          · exact hk2 y
        · have : y ∉ S := fun h => hy (hSB y h)
          simp only [reprogBase, this, ↓reduceIte, hf1 y hy]
        · simp only [reprogBase]
          split_ifs
          · rw [AddEquiv.apply_symm_apply, hf2 y]
          · exact hf2 y
        · rw [reprogram_filter_reprogAssigns]
          have hyh : y ∉ S \ T := by
            rw [← hhid]
            exact hy rs req (List.prefix_refl _) hq
          have hold := hkf y (hpre y hy)
          simp only [reprogBase]
          by_cases hyS : y ∈ S
          · have hyT : y ∈ T := by
              by_contra hT
              exact hyh (Finset.mem_sdiff.2 ⟨hyS, hT⟩)
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hyS, hyT⟩),
              ite_eq_left_of_eq_true _ _ (eq_true hyS), hk2 y, hf2 y]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hyS h.1)),
              ite_eq_right_of_eq_false _ _ (eq_false hyS), hold]
      · simp only [hq, ↓reduceIte]
        exact ⟨hk1, hk2, hf1, hf2, fun y hy => hkf y (hpre y hy)⟩
  exact (key rs).2.2.2.2 x hx

omit [Fintype Y] [Nonempty Y] in
/-- **The kept-only and the full reprogramming challenger give the same response after the
requests `rs`** when the reads of the request at the oracle in force of `preReprogKeep` avoid the
hidden points of the earlier requests numbered below `Q`. -/
theorem response_preReprogKeep_eq_of_reads {B : Set X}
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (plain : ∀ c hist req H, ((C₀.respond c hist req).run H).assignments = [])
    (hsub : ∀ c hist req O, (((pts c hist req).run O : Finset X) : Set X) ⊆ B)
    (hreads : ∀ c hist req (O O' : X → Y), (∀ x ∉ B, O x = O' x) →
      (∀ x, (sp (O x)).2 = (sp (O' x)).2) → (pts c hist req).run O = (pts c hist req).run O')
    (ω : (Fin C₀.Q → X → Y₁) × C₀.Coins) (H : X → Y) (rs : List Req) (req : Req)
    (hx : ∀ y ∈ ((C₀.preReprog sp pts qp K hqp hK).respond ω (histOf rs) req).trace
        ((C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq ω H rs),
      ∀ rs₀ req', rs₀ ++ [req'] <+: rs → rs₀.length < C₀.Q →
        y ∉ C₀.hiddenKeep sp pts qp K hqp hK keep ω H rs₀ req') :
    (((C₀.preReprogKeep sp pts qp K hqp hK keep).respond ω (histOf rs) req).run
        ((C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq ω H rs)).response =
      (((C₀.preReprog sp pts qp K hqp hK).respond ω (histOf rs) req).run
        ((C₀.preReprog sp pts qp K hqp hK).oracleByReq ω H rs)).response := by
  rw [response_preReprogKeep, OracleProg.run_congr _ fun y hy =>
    oracleByReq_preReprogKeep_eq keep plain hsub hreads ω H rs y (hx y hy)]

omit [Fintype Y] [Nonempty Y] in
/-- **The kept-only reprogramming challenger reads the history only through its requests** when
`C₀`, the point program and the kept points do. -/
theorem respondsByRequests_preReprogKeep
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (byRequests₀ : C₀.RespondsByRequests)
    (hptsReq : ∀ c (hist hist' : List (HistoryEntry Req Resp)) req,
      hist.map HistoryEntry.request = hist'.map HistoryEntry.request →
      pts c hist req = pts c hist' req)
    (hkeepReq : ∀ c (hist hist' : List (HistoryEntry Req Resp)) req,
      hist.map HistoryEntry.request = hist'.map HistoryEntry.request →
      keep c hist req = keep c hist' req) :
    (C₀.preReprogKeep sp pts qp K hqp hK keep).RespondsByRequests := by
  intro c hist hist' req hh
  have hlen : hist.length = hist'.length := by
    simpa using congrArg List.length hh
  simp only [preReprogKeep, hptsReq c.2 hist hist' req hh, byRequests₀ c.2 hist hist' req hh,
    hkeepReq c.2 hist hist' req hh, hlen]

end Challenger

end Quantum

end GordieHowe
