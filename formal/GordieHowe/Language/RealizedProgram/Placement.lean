-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.CellsLowering
public import GordieHowe.Language.RealizedProgram.StructureCheck
public import GordieHoweNative.Language.RealizedProgram.Placement

@[expose] public section

/-!
# GordieHowe: the cells checks at the structure records' pointers

The cells checks (`GordieHowe.RealizedProgram.CellsValid`) decided at the placement pointers the
compiler emits (`GordieHowe.RealizedProgram.Structure`: `routes`, `logupHosts`, `macHosts`,
`chalValues`), each checker a failure-reporting twin (`…E`, its `Bool` the `okB` of it):

* **the challenge values** (`chalValuesE`): every listed value holds its challenge, and every value
  holding a challenge is at or after the listed one, so the list reads the first value holding each
  challenge (`chalNode_eq_chalOf`);
* **the batches** (`batchesE`): every batch passes the batch check, once per batch;
* **the routes** (`routesE`, a merge with the predicates): every predicate that needs a route
  (`PredBody.needsRoute`) has one, at the pointer it names (an affine row on cells or on views, the
  quadratic test, a part of batch `b`, entry `k` of circuit `c`, or the realized field equation
  with its conversions in mismatch order), and no other predicate has one;
* **the batch routes** (`batchRoutesE`): the routes into each batch, in order, are its parts with
  their indices, so a batch route's predicate is its part (one walk of the routes per batch,
  in place of reading each part by its index);
* **the hosts** (`logupHostsE`, `macHostsE`): the LogUp hosts' keys are exactly the tables' groups,
  in order, each at its circuit entry; every predicate whose H half needs a host
  (`PredBody.needsH`) has one at its circuit entry, and no other predicate has one;
* **the tables' challenges, the entries and the types** (`alphasE`, `entriesE`, `typesE`): sweeps.

**Soundness**: `cellsValid_of_placementB`. The meaning of `CellsValid` is the existentials the
pointers witness; no check here recognizes an object by its shape or searches for it.
-/

namespace GordieHowe.RealizedProgram

open Twin

/-! ## A merge of the predicates with a keyed list -/

/-- **The merge gives every predicate that needs an entry a passing entry**, an entry of the
list keyed by it. -/
theorem mergeE_sound {β : Type} {need : Predicate → Bool}
    {check : ℕ → Predicate → β → Except StructFailure Unit} {missing extra : StructReason} :
    ∀ {pid : ℕ} {ps : List Predicate} {rs : List (ℕ × β)},
      okB (mergeE need check missing extra pid ps rs) = true →
        ∀ k (hk : k < ps.length), need ps[k] = true →
          ∃ x, (pid + k, x) ∈ rs ∧ okB (check (pid + k) ps[k] x) = true
  | _, [], _, _ => fun k hk => absurd hk (Nat.not_lt_zero k)
  | pid, pr :: ps, rs, h => by
    intro k hk hn
    unfold mergeE at h
    split at h
    · rename_i hneed
      split at h
      · rename_i kr rs'
        split at h
        · rename_i hkr
          rw [okB_seqE, Bool.and_eq_true] at h
          cases k with
          | zero =>
            refine ⟨kr.2, ?_, by simpa using h.1⟩
            rw [Nat.add_zero, ← hkr]
            exact List.mem_cons_self
          | succ k =>
            obtain ⟨x, hm, hx⟩ := mergeE_sound h.2 k (by simpa using hk) (by simpa using hn)
            rw [show pid + 1 + k = pid + (k + 1) by omega] at hm
            exact ⟨x, List.mem_cons_of_mem _ hm,
              by rw [show pid + (k + 1) = pid + 1 + k by omega]; simpa using hx⟩
        · cases h
      · cases h
    · rename_i hneed
      cases k with
      | zero => exact absurd (by simpa using hn) hneed
      | succ k =>
        have h' : okB (mergeE need check missing extra (pid + 1) ps rs) = true := by
          split at h
          · split at h
            · cases h
            · exact h
          · exact h
        obtain ⟨x, hm, hx⟩ := mergeE_sound h' k (by simpa using hk) (by simpa using hn)
        rw [show pid + 1 + k = pid + (k + 1) by omega] at hm
        exact ⟨x, hm, by rw [show pid + (k + 1) = pid + 1 + k by omega]; simpa using hx⟩

/-- **The merge over the program's predicates**: every predicate `p` that needs an entry has a
passing one, keyed by `p`. -/
theorem mergeE_predicates {ir : RealizedProgram} {β : Type} {need : Predicate → Bool}
    {check : ℕ → Predicate → β → Except StructFailure Unit} {missing extra : StructReason}
    {rs : List (ℕ × β)} (h : okB (mergeE need check missing extra 0 ir.predicates rs) = true)
    {p : ℕ} (hp : p < ir.predicates.length) (hn : need (ir.predicate p) = true) :
    ∃ x, (p, x) ∈ rs ∧ okB (check p (ir.predicate p) x) = true := by
  have he : ir.predicate p = ir.predicates[p] := by
    rw [predicate_eq_getD,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  rw [he] at hn ⊢
  simpa using mergeE_sound h p hp hn

/-! ## The challenge values -/

section

variable (ir : RealizedProgram)

/-- **The challenge values, checked**: every listed value is a value of the program holding its
challenge (failure `chalValue`), and every value holding a challenge is at or after the challenge's
listed value (failure `chalSweep`, also when the challenge has none). -/
def chalValuesE (S : Structure) : Except StructFailure Unit :=
  seqE
    (allE (fun _ jv => guardE (decide (jv.2 < ir.values.length) &&
        match (ir.value jv.2).kind with
        | .challenge j => j == jv.1
        | _ => false) ⟨jv.1, jv.2, .chalValue⟩) 0 S.chalValues)
    (allE (fun v x => match x.kind with
        | .challenge j => guardE (match S.chalOf j with
            | some w => decide (w ≤ v)
            | none => false) ⟨v, j, .chalSweep⟩
        | _ => .ok ()) 0 ir.values)

/-- **`chalValuesE` as a `Bool`.** -/
def chalValuesB (S : Structure) : Bool := okB (ir.chalValuesE S)

/-- **The batches, checked once each** (failure `batch`). -/
def batchesE : Except StructFailure Unit :=
  allE (fun b B => guardE (ir.batchOkB B.domain b) ⟨b, 0, .batch⟩) 0 ir.batches

/-- **`batchesE` as a `Bool`.** -/
def batchesB : Bool := okB ir.batchesE

/-! ## The routes -/

/-- **A predicate body is a family of affine rows of domain `d`** (`isRow` at the body). -/
def rowBodyB (d : ℕ) (b : PredBody) : Bool :=
  match b.rowSides d with
  | some (e, e') => ir.rowExprOk e && ir.rowExprOk e'
  | none => false

/-- **A predicate body is a family of affine rows on views of domain `d`** (`isViewRow` at the
body). -/
def viewRowBodyB (d : ℕ) (b : PredBody) : Bool :=
  match b.rowSides d with
  | some (e, e') => !ir.rowBodyB d b && ir.viewExprOk d e && ir.viewExprOk d e'
  | none => false

theorem isRow_eq_rowBodyB (d p : ℕ) : ir.isRow d p = ir.rowBodyB d (ir.predicate p).body := rfl

theorem isViewRow_eq_viewRowBodyB (d p : ℕ) :
    ir.isViewRow d p = ir.viewRowBodyB d (ir.predicate p).body := rfl

/-- **Route `r` of predicate `pid` (`pr`), checked at its pointer**: the predicate has a domain of
the program (failure `routeDomain`); an affine route is a row on cells (`false`) or on views
(`true`) of it, a quadratic route its quadratic test, a batch route into a batch `b` of it (its
predicate is the batch's part by `batchRoutesE`), a circuit route entry `k` (a placed predicate or
a Boolean check) of circuit `c` of it (failure `routePointer`); a realized route admits the
predicate at its conversions (failure `realized`). -/
def routeOkE (pid : ℕ) (pr : Predicate) (r : Route) : Except StructFailure Unit :=
  match pr.body.domain? with
  | none => .error ⟨pid, 0, .routeDomain⟩
  | some d =>
    seqE (guardE (decide (d < ir.domains.length)) ⟨pid, 0, .routeDomain⟩) <|
      match r with
      | .affine false => guardE (ir.rowBodyB d pr.body) ⟨pid, 0, .routePointer⟩
      | .affine true => guardE (ir.viewRowBodyB d pr.body) ⟨pid, 0, .routePointer⟩
      | .quadratic => guardE (ir.isQuad d pid) ⟨pid, 0, .routePointer⟩
      | .batch b _ =>
        guardE (decide (b < ir.batches.length) && decide ((ir.batch b).domain = d))
          ⟨pid, b, .routePointer⟩
      | .gkr c k =>
        guardE (decide (c < ir.circuits.length) && decide ((ir.circuit c).domain = d) &&
          (decide ((ir.circuit c).entries[k]? = some (.pred pid)) ||
            decide ((ir.circuit c).entries[k]? = some (.typeCheck pid)))) ⟨pid, c, .routePointer⟩
      | .realized q js => guardE (ir.realizedRouteB pr.body q js) ⟨pid, q, .realized⟩

/-- **The routes, checked**: one merge of the predicates with the sorted `routes`; a predicate that
needs a route (`PredBody.needsRoute`) has its own, which checks at its pointer (`routeOkE`);
failures `routeMissing`, `routeExtra`. -/
def routesE (S : Structure) : Except StructFailure Unit :=
  mergeE (·.body.needsRoute) ir.routeOkE .routeMissing .routeExtra 0 ir.predicates S.routes

end

theorem Structure.mem_batchRoutes {S : Structure} {b pid j : ℕ}
    (h : (pid, Route.batch b j) ∈ S.routes) : (pid, j) ∈ S.batchRoutes b :=
  List.mem_filterMap.2 ⟨_, h, by simp⟩

section

variable (ir : RealizedProgram)

/-! ## The hosts -/

/-! ## The sweeps -/

/-- **Every node-typed value's type follows from its domain's cells** (`typeOwnB`; failure
`types`). -/
def typesE : Except StructFailure Unit :=
  allE (fun v x => guardE (!decide (x.typeSource = .node) || ir.typeOwnB v) ⟨v, 0, .types⟩) 0
    ir.values

/-! ## The placement check -/

/-- **The cells checks at the structure records' pointers** (see the module docstring). -/
def placementE (S : Structure) : Except StructFailure Unit :=
  seqE (guardE (ir.domains.length != 0) ⟨0, 0, .nonempty⟩) <|
  seqE (ir.chalValuesE S) <| seqE ir.batchesE <| seqE (ir.routesE S) <|
  seqE (ir.batchRoutesE S) <|
  seqE (ir.logupHostsE S) <| seqE (ir.alphasE S) <| seqE (ir.macHostsE S) <|
  seqE (ir.entriesE S) ir.typesE

/-- **`placementE` as a `Bool`.** -/
def placementB (S : Structure) : Bool := okB (ir.placementE S)

end

/-! ## Soundness -/

section

variable {ir : RealizedProgram} {S : Structure}

theorem value_eq_getElem {v : ℕ} (hv : v < ir.values.length) : ir.value v = ir.values[v] := by
  rw [value_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]

/-- **The challenge values read the first value holding each challenge** (`chalNode`). -/
theorem chalNode_eq_chalOf (h : ir.chalValuesB S = true) (j : ℕ) : ir.chalNode j = S.chalOf j := by
  simp only [chalValuesB, chalValuesE, okB_seqE, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [okB_allE_iff] at h1 h2
  cases hj : S.chalOf j with
  | some w =>
    have hm := NatTrie.mem_of_get?_ofList hj
    obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hm
    have := h1 k hk
    simp only [okB_guardE, Bool.and_eq_true, decide_eq_true_eq, hkw] at this
    obtain ⟨hw, hkind⟩ := this
    have hkind' : (ir.value w).kind = .challenge j := by
      revert hkind
      cases (ir.value w).kind <;> simp
    unfold chalNode
    rw [List.find?_range_eq_some]
    refine ⟨by rw [hkind']; simp, List.mem_range.2 hw, fun u hu => ?_⟩
    have hu' : u < ir.values.length := by omega
    have h2u := h2 u hu'
    rw [zero_add, ← value_eq_getElem hu'] at h2u
    cases hk' : (ir.value u).kind with
    | challenge c =>
      rw [hk'] at h2u
      by_cases hc : c = j
      · subst hc
        simp only [hj, okB_guardE, decide_eq_true_eq] at h2u
        omega
      · simp [hc]
    | _ => simp
  | none =>
    unfold chalNode
    rw [List.find?_eq_none]
    intro u hu hp
    have hu' := List.mem_range.1 hu
    have h2u := h2 u hu'
    rw [zero_add, ← value_eq_getElem hu'] at h2u
    revert hp h2u
    cases (ir.value u).kind with
    | challenge c =>
      intro hp h2u
      simp only [beq_iff_eq] at hp
      subst hp
      simp [hj, okB_guardE] at h2u
    | _ => simp

/-- **The batches checked once each pass the batch check.** -/
theorem batchOk_of_batchesB (h : ir.batchesB = true) {b : ℕ} (hb : b < ir.batches.length) :
    ir.batchOkB (ir.batch b).domain b = true := by
  simp only [batchesB, batchesE, okB_allE_iff] at h
  have := h b hb
  rw [zero_add, okB_guardE] at this
  rwa [batch, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]

/-- **A batch route's predicate is its batch's part**, when the batch routes check. -/
theorem mem_parts_of_batchRoutesE (h : okB (ir.batchRoutesE S) = true) {pid b j : ℕ}
    (hb : b < ir.batches.length) (hr : (pid, Route.batch b j) ∈ S.routes) :
    pid ∈ (ir.batch b).parts := by
  simp only [batchRoutesE, okB_allE_iff, zero_add, okB_guardE, beq_iff_eq] at h
  have hm := Structure.mem_batchRoutes hr
  rw [h b hb] at hm
  have hB : ir.batches[b] = ir.batch b := by
    rw [batch, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  rw [hB, List.mem_zipIdx_iff_getElem?] at hm
  exact List.mem_of_getElem? hm

/-- **A route checked at its pointer lowers or realizes its predicate** in its own domain. -/
theorem own_of_routeOkE (hbat : ir.batchesB = true) (hbr : okB (ir.batchRoutesE S) = true)
    {pid : ℕ} {r : Route} (hmem : (pid, r) ∈ S.routes)
    (hn : (ir.predicate pid).body.needsRoute = true) (hp : pid < ir.predicates.length)
    (h : okB (ir.routeOkE pid (ir.predicate pid) r) = true) :
    ir.LoweredOwn pid ∨ ir.RealizedOwn pid := by
  unfold routeOkE at h
  split at h
  · cases h
  · rename_i d hd
    rw [okB_seqE, okB_guardE, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hdD, h⟩ := h
    have own : ir.Lowered d pid → ir.LoweredOwn pid := fun hl => ⟨⟨d, hdD⟩, hd, hl⟩
    split at h
    · rw [okB_guardE, ← isRow_eq_rowBodyB] at h
      exact .inl (own (.row hp h))
    · rw [okB_guardE, ← isViewRow_eq_viewRowBodyB] at h
      exact .inl (own (.viewRow hp h))
    · rw [okB_guardE] at h
      exact .inl (own (.quad hp h))
    · rename_i b j
      simp only [okB_guardE, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hb, hbd⟩ := h
      have hok := batchOk_of_batchesB hbat hb
      rw [hbd] at hok
      have hmem : pid ∈ (ir.batch b).parts := mem_parts_of_batchRoutesE hbr hb hmem
      cases hop : (ir.batch b).operands with
      | columns =>
        have hc : ir.colsBatchOkB d b = true := by simp [colsBatchOkB, hok, hop]
        exact .inl (own (.batch ⟨⟨b, hb⟩, hc⟩ hmem))
      | bits =>
        have hc : ir.bitsBatchOkB d b = true := by simp [bitsBatchOkB, hok, hop]
        exact .inl (own (.bitsBatch ⟨b, hb⟩ hc hmem))
    · rename_i c k
      simp only [okB_guardE, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hc, hcd⟩, hk⟩ := h
      refine .inl (own (.placed ⟨⟨c, hc⟩, hcd⟩ hn ?_))
      rcases hk with hk | hk
      · exact .inl (List.mem_of_getElem? hk)
      · exact .inr (List.mem_of_getElem? hk)
    · rename_i q js
      rw [okB_guardE] at h
      refine .inr ?_
      unfold realizedRouteB at h
      unfold RealizedOwn
      split at h
      · rename_i d' e e' q' hb
        rw [hb]
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        obtain ⟨⟨rfl, hd'⟩, ha⟩ := h
        exact ⟨hd', ir.realizedAdmits_of_atB ha⟩
      · rename_i d' e e' real hb
        rw [hb]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨ht, hd'⟩, ha⟩ := h
        simp only
        split at ht
        · rename_i q' hq
          simp only [beq_iff_eq] at ht
          subst ht
          rw [hq]
          exact ⟨hd', ir.realizedAdmits_of_atB ha⟩
        · cases ht
      · cases h

/-- **The routes give every predicate that needs one its lowering or realization.** -/
theorem own_of_routesE (hbat : ir.batchesB = true) (hbr : okB (ir.batchRoutesE S) = true)
    (h : okB (ir.routesE S) = true) :
    ∀ p < ir.predicates.length, (ir.predicate p).body.needsRoute = true →
      ir.LoweredOwn p ∨ ir.RealizedOwn p := by
  intro p hp hn
  obtain ⟨r, hm, hr⟩ := mergeE_predicates h hp hn
  exact own_of_routeOkE hbat hbr hm hn hp hr

/-- **A host checked at its pointer is an entry of a circuit of a domain.** -/
theorem exists_of_hostAtB {c k : ℕ} {rc : RealCircuit} (h : ir.hostAtB c k rc = true) :
    ∃ c' : Fin ir.circuits.length, (ir.circuit c').domain < ir.domains.length ∧
      CircuitEntry.realization rc ∈ (ir.circuit c').entries := by
  simp only [hostAtB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hd⟩, hk⟩ := h
  exact ⟨⟨c, hc⟩, hd, List.mem_of_getElem? hk⟩

/-- **The LogUp hosts give every group's LogUp identity a circuit of a domain.** -/
theorem logup_of_logupHostsE (h : okB (ir.logupHostsE S) = true) :
    ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ∃ c : Fin ir.circuits.length,
      (ir.circuit c).domain < ir.domains.length ∧
        CircuitEntry.realization (.logup t g) ∈ (ir.circuit c).entries := by
  intro t ht g hg
  simp only [logupHostsE, okB_seqE, okB_guardE, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hkeys, hall⟩ := h
  have hall' : ∀ x ∈ S.logupHosts, ir.hostAtB x.2.1 x.2.2 (.logup x.1.1 x.1.2) = true := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := okB_allE_iff.1 hall k hk
    rwa [okB_guardE] at this
  have hmem : (t, g) ∈ S.logupHosts.map (·.1) := by
    rw [hkeys, groupKeys, List.mem_flatMap]
    exact ⟨t, List.mem_range.2 ht, List.mem_map.2 ⟨g, List.mem_range.2 hg, rfl⟩⟩
  obtain ⟨x, hx, hx1⟩ := List.mem_map.1 hmem
  have := hall' x hx
  rw [hx1] at this
  exact exists_of_hostAtB this

/-- **The H halves' hosts give every H half that needs one a circuit of a domain.** -/
theorem macHCovered_of_macHostsE (h : okB (ir.macHostsE S) = true) :
    ∀ p < ir.predicates.length, ir.MacHCovered p := by
  intro p hp hn
  obtain ⟨x, -, hx⟩ := mergeE_predicates (need := (·.body.needsH)) h hp hn
  rw [okB_guardE] at hx
  exact exists_of_hostAtB hx

/-- **The checked tables' challenges are held by values of their fields.** -/
theorem alpha_of_alphasE (hch : ir.chalValuesB S = true) (h : okB (ir.alphasE S) = true) :
    ∀ t < ir.tables.length, ∃ v, ir.chalNode (ir.alphaOf t) = some v ∧
      ir.valueField v = ir.chalField (ir.alphaOf t) := by
  intro t ht
  simp only [alphasE, okB_allE_iff, zero_add, okB_guardE] at h
  have h1 := h t ht
  have ha : ir.alphaOf t = ir.tables[t].alpha := by
    rw [alphaOf, table, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  rw [ha, chalNode_eq_chalOf hch]
  split at h1
  · rename_i v hv
    exact ⟨v, hv, of_decide_eq_true h1⟩
  · cases h1

/-- **The checked entries are covered** (`EntryOk`). -/
theorem entryOk_of_entriesE (hch : ir.chalValuesB S = true) (h : okB (ir.entriesE S) = true) :
    ∀ c < ir.circuits.length, ∀ e ∈ (ir.circuit c).entries, ir.EntryOk e := by
  intro c hc e he
  simp only [entriesE, okB_allE_iff, zero_add] at h
  have h1 := h c hc
  have hcc : ir.circuit c = ir.circuits[c] := by
    rw [circuit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]
  rw [hcc] at he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  have h2 := h1 k hk
  rw [okB_guardE] at h2
  generalize ir.circuits[c].entries[k] = e at h2
  cases e with
  | typeCheck p =>
    simp only [entryOkWithB, decide_eq_true_eq] at h2
    exact h2
  | alignment _ => trivial
  | pred p =>
    simp only [entryOkWithB, decide_eq_true_eq] at h2
    exact h2
  | realization rc =>
    cases rc with
    | logup t g =>
      simp only [entryOkWithB, Bool.and_eq_true, decide_eq_true_eq] at h2
      exact h2
    | macH p =>
      simp only [entryOkWithB, Bool.and_eq_true, decide_eq_true_eq] at h2
      refine ⟨h2.1, ?_⟩
      have h3 := h2.2
      unfold macHNodeWithB at h3
      split at h3
      · rename_i dx x dy y k real hb
        split at h3
        · rename_i v hn hbx hv
          rw [← chalNode_eq_chalOf hch] at hv
          exact ⟨dx, x, dy, y, k, real, v, hb, hn, hbx, hv, of_decide_eq_true h3⟩
        · cases h3
      · cases h3
    | named _ => trivial
    | unmodeled _ => trivial

/-- **The checked types follow from the domains' cells.** -/
theorem types_of_typesE (h : okB ir.typesE = true) :
    ∀ v < ir.values.length, (ir.value v).typeSource = .node → ir.typeOwnB v = true := by
  intro v hv hs
  simp only [typesE, okB_allE_iff, zero_add, okB_guardE, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  rcases h v hv with h1 | h1
  · rw [← value_eq_getElem hv] at h1
    exact absurd hs h1
  · exact h1

/-- **Soundness of the placement check**: the cells checks hold. -/
theorem cellsValid_of_placementB (h : ir.placementB S = true) : ir.CellsValid := by
  simp only [placementB, placementE, okB_seqE, okB_guardE, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨h0, hch, hbat, hr, hbr, hl, ha, hm, he, ht⟩ := h
  exact ⟨h0, own_of_routesE hbat hbr hr, logup_of_logupHostsE hl, alpha_of_alphasE hch ha,
    types_of_typesE ht, entryOk_of_entriesE hch he, macHCovered_of_macHostsE hm⟩

end

end GordieHowe.RealizedProgram
