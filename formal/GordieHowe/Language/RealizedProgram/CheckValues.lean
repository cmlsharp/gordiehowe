-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check

@[expose] public section

/-!
# GordieHowe: the checkers of the program's per-value conditions

Boolean checks of the items of `GordieHowe.RealizedProgram.ValidAtNodes` that range over the values,
written for kernel reduction and run by `decide +kernel`: `MessagesMatch` (`messagesB`),
`ChallengeOrder` (`orderB`), `PadOrderValid` (`padsB`), `PadRealized` (`padRealizedB`) and
`TypeSources` (`typesB`), each with its `_iff` lemma.

Each check visits the values once (`allIdx`), reads the value it visits from the list, and reads any
other value through the table `valueT` (`O(log u)` steps for value `u`) and any predicate through
`predT`. The `Decidable` instances of the conditions in
`GordieHowe/Language/RealizedProgram/Valid.lean` look every value up in the list, `v` steps for value
`v`, so deciding them costs the square of the number of values. The messages' order is checked on
consecutive messages (`chainB`), which for the transitive `MsgBeforeId` is the order on all pairs
that `MessagesMatch` states; a late value's message is looked up in a `NatTrie` of the messages'
values (`msgT`).
-/

namespace GordieHowe.RealizedProgram

/-! ## Chains -/

/-- **Consecutive elements of a list are related by `r`.** -/
def chainB (r : ℕ → ℕ → Bool) : List ℕ → Bool
  | a :: b :: l => r a b && chainB r (b :: l)
  | _ => true

/-- **A chain of a transitive relation is its order on all pairs.** -/
theorem chainB_iff_pairwise {R : ℕ → ℕ → Prop} (r : ℕ → ℕ → Bool)
    (hr : ∀ a b, r a b = true ↔ R a b) (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ l : List ℕ, chainB r l = true ↔ l.Pairwise R
  | [] => by simp [chainB]
  | [_] => by simp [chainB]
  | a :: b :: l => by
    rw [chainB, Bool.and_eq_true, hr, chainB_iff_pairwise r hr htrans (b :: l),
      List.pairwise_cons (l := b :: l)]
    constructor
    · rintro ⟨hab, hbl⟩
      refine ⟨fun x hx => ?_, hbl⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact htrans _ _ _ hab ((List.pairwise_cons.1 hbl).1 x hx)
    · rintro ⟨h, hbl⟩
      exact ⟨h b (by simp), hbl⟩

section

variable (ir : RealizedProgram)

/-! ## Messages -/

/-- **`MsgBeforeId u v`**, through the table. -/
def msgBeforeT (u v : ℕ) : Bool :=
  decide ((ir.valueT u).phase < (ir.valueT v).phase ∨
    ((ir.valueT u).phase = (ir.valueT v).phase ∧ u < v))

theorem msgBeforeT_iff (u v : ℕ) : ir.msgBeforeT u v = true ↔ ir.MsgBeforeId u v := by
  simp only [msgBeforeT, MsgBeforeId, valueT_eq, decide_eq_true_eq]

theorem msgBeforeId_trans (u v w : ℕ) (h1 : ir.MsgBeforeId u v) (h2 : ir.MsgBeforeId v w) :
    ir.MsgBeforeId u w := by
  unfold MsgBeforeId at *
  omega

/-- **`MessageOk m`**, through the table. -/
def messageOkT (m : Message) : Bool :=
  decide (m.value < ir.values.length) && ir.isLateV (ir.valueT m.value) &&
    decide ((ir.valueT m.value).domain = m.domain) &&
    decide ((ir.valueT m.value).field = m.field) &&
    decide ((ir.valueT m.value).phase = m.phase) && decide ((ir.valueT m.value).size = m.size) &&
    decide ((ir.valueT m.value).padSpace = m.space) &&
    decide ((ir.valueT m.value).realization = m.realization)

theorem messageOkT_iff (m : Message) : ir.messageOkT m = true ↔ ir.MessageOk m := by
  simp only [messageOkT, MessageOk, Bool.and_eq_true, decide_eq_true_eq, valueT_eq, isLateV_iff,
    and_assoc]

/-- **The late values with a message**, as a set. -/
def msgT : NatTrie Unit := natSet (ir.messages.map (·.value))

theorem msgT_isSome (v : ℕ) : (ir.msgT.get? v).isSome = true ↔ v ∈ ir.messages.map (·.value) :=
  natSet_isSome _ v

/-- **`MessagesMatch`**: every message matches its value, consecutive messages are in `MsgBefore`
order, and every late value has a message. -/
def messagesB : Bool :=
  ir.messages.all ir.messageOkT && chainB ir.msgBeforeT (ir.messages.map (·.value)) &&
    allIdx (fun v x => !x.kind.isLate || (ir.msgT.get? v).isSome) ir.values 0

/-- **`messagesB` is `MessagesMatch`.** -/
theorem messagesB_iff : ir.messagesB = true ↔ ir.MessagesMatch := by
  rw [messagesMatch_iff]
  simp only [messagesB, Bool.and_eq_true, List.all_eq_true, messageOkT_iff,
    chainB_iff_pairwise _ (ir.msgBeforeT_iff) (ir.msgBeforeId_trans), allIdx_values_iff,
    Bool.or_eq_true, Bool.not_eq_true', msgT_isSome, and_assoc, isLateNode]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun v _ => ?_))
  cases (ir.value v).kind.isLate <;> simp

/-! ## The challenge order -/

/-- **`LateReadOrdered v rd`**, on value `v`. -/
def lateReadOrderedV (x : Value) : Read → Bool
  | .chal c => decide ((ir.challenge c).phase ≤ x.phase)
  | .late _ => false
  | .pad _ => true

theorem lateReadOrderedV_iff (v : ℕ) (rd : Read) :
    ir.lateReadOrderedV (ir.value v) rd = true ↔ ir.LateReadOrdered v rd := by
  cases rd <;> simp [lateReadOrderedV, LateReadOrdered]

/-- **`PredReadOrdered c rd`**, through the table. -/
def predReadOrderedT (c : ℕ) : Read → Bool
  | .chal _ => true
  | .late u => (ir.valueT u).reads.contains (.chal c) ||
      decide ((ir.valueT u).phase < (ir.challenge c).phase)
  | .pad _ => true

theorem predReadOrderedT_iff (c : ℕ) (rd : Read) :
    ir.predReadOrderedT c rd = true ↔ ir.PredReadOrdered c rd := by
  cases rd <;> simp [predReadOrderedT, PredReadOrdered, valueT_eq, List.contains_iff_mem]

/-- **`PredReadsOrdered p c`**, through the table. -/
def predReadsOrderedT (p : Predicate) (c : ℕ) : Bool :=
  !p.role.isSource || !decide (0 < p.deg c) || p.reads.all (ir.predReadOrderedT c)

theorem predReadsOrderedT_iff (p : Predicate) (c : ℕ) :
    ir.predReadsOrderedT p c = true ↔ ir.PredReadsOrdered p c := by
  unfold predReadsOrderedT PredReadsOrdered
  cases hs : p.role.isSource <;> by_cases h : 0 < p.deg c <;>
    simp [h, List.all_eq_true, predReadOrderedT_iff]

/-- **`InRealOrdered rds real`**, through the table. -/
def inRealOrderedT (rds : List Read) : InRealization → Bool
  | .lookup r =>
      (Read.lates rds).all (fun u =>
        decide ((ir.valueT u).phase < (ir.challenge (ir.table r.table).alpha).phase)) &&
      ((ir.table r.table).groups.getD r.group default).lateMult.toList.all (fun m =>
        decide ((ir.valueT m).phase < (ir.challenge (ir.table r.table).alpha).phase)) &&
      (r.digitValues ++ r.second).all (fun u =>
        decide ((ir.valueT u).phase < (ir.challenge (ir.table r.table).alpha).phase))
  | .implied _ _ => true

/-- **`BodyOrdered rds b`**, through the table. -/
def bodyOrderedT (rds : List Read) : PredBody → Bool
  | .equal _ _ _ _ => true
  | .mem _ _ _ real => ir.inRealOrderedT rds real
  | .mod _ _ _ _ _ => true
  | .cross _ _ _ _ _ real =>
      decide ((ir.challenge real.key).phase ≤ (ir.valueT real.tag).phase) &&
        real.accumulators.all fun u => decide ((ir.challenge real.key).phase ≤ (ir.valueT u).phase)

theorem bodyOrderedT_iff (rds : List Read) (b : PredBody) :
    ir.bodyOrderedT rds b = true ↔ ir.BodyOrdered rds b := by
  rcases b with _ | ⟨_, _, _, real⟩ | _ | _
  · simp [bodyOrderedT, BodyOrdered]
  · cases real <;>
      simp [bodyOrderedT, BodyOrdered, inRealOrderedT, InRealOrdered, valueT_eq, and_assoc, or_imp,
        forall_and]
  · simp [bodyOrderedT, BodyOrdered]
  · simp [bodyOrderedT, BodyOrdered, valueT_eq]

/-- **`ChallengeOrder`**: the late values' reads in one pass over the values, the predicates' reads
and realizations in one pass over the predicates. -/
def orderB : Bool :=
  allIdx (fun _ x => !x.kind.isLate || x.reads.all (ir.lateReadOrderedV x)) ir.values 0 &&
    ir.predicates.all (fun p => (List.range ir.challenges.length).all (ir.predReadsOrderedT p)) &&
    ir.predicates.all (fun p => ir.bodyOrderedT p.reads p.body)

/-- **`orderB` is `ChallengeOrder`.** -/
theorem orderB_iff : ir.orderB = true ↔ ir.ChallengeOrder := by
  rw [challengeOrder_iff]
  simp only [orderB, Bool.and_eq_true, List.all_eq_true, allIdx_values_iff, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', predReadsOrderedT_iff, bodyOrderedT_iff, and_assoc,
    lateReadOrderedV_iff, isLateNode, LateReadsOrdered, RealizationOrdered]
  refine and_congr (forall₂_congr fun v _ => ?_) Iff.rfl
  cases (ir.value v).kind.isLate <;> simp

/-! ## The pad order -/

/-- **A pad `u` read by late value `v` comes before it** (`PadsBefore`'s condition), through the
table. -/
def padBeforeT (v u : ℕ) : Bool :=
  decide (u < ir.values.length) && ir.isLateV (ir.valueT u) && (ir.valueT u).isPadRealizedB &&
    ir.msgBeforeT u v

theorem padBeforeT_iff (v u : ℕ) : ir.padBeforeT v u = true ↔
    u < ir.values.length ∧ ir.IsLate u ∧ ir.isPadRealized u = true ∧ ir.MsgBeforeId u v := by
  simp only [padBeforeT, Bool.and_eq_true, decide_eq_true_eq, valueT_eq, isLateV_iff,
    msgBeforeT_iff, isPadRealized_eq, and_assoc]

/-- **`PadOrderValid`**, in one pass over the values. -/
def padsB : Bool :=
  allIdx (fun v x => !x.kind.isLate || (Read.pads x.reads).all (ir.padBeforeT v)) ir.values 0

/-- **`padsB` is `PadOrderValid`.** -/
theorem padsB_iff : ir.padsB = true ↔ ir.PadOrderValid := by
  simp only [padsB, PadOrderValid, PadsBefore, allIdx_values_iff, Bool.or_eq_true,
    Bool.not_eq_true', List.all_eq_true, padBeforeT_iff, isLateNode]
  refine forall₂_congr fun v _ => ?_
  cases (ir.value v).kind.isLate <;> simp

/-- **`PadRealized`**, in one pass over the values. -/
def padRealizedB : Bool :=
  allIdx (fun _ x => !x.kind.isLate || x.isPadRealizedB) ir.values 0

/-- **`padRealizedB` is `PadRealized`.** -/
theorem padRealizedB_iff : ir.padRealizedB = true ↔ ir.PadRealized := by
  simp only [padRealizedB, PadRealized, allIdx_values_iff, Bool.or_eq_true, Bool.not_eq_true',
    isLateNode, isPadRealized_eq]
  refine forall₂_congr fun v _ => ?_
  cases (ir.value v).kind.isLate <;> simp

/-! ## Type sources -/

/-- **`TypeSourced treeNodes v`**, on value `v` (the predicates through `predT`). -/
def typeSourcedV (treeNodes : ℕ → List String) (v : ℕ) (x : Value) : Bool :=
  if x.kind.isBound then true else
  match x.type.nodeName with
  | none => true
  | some s =>
    match x.typeSource with
    | .node =>
        decide (s ∈ treeNodes x.domain) &&
          (if x.kind.isLate then
             decide (x.padSpace = Space.node s) ||
               (decide (x.padSpace = .full) &&
                 decide (s = (ir.field (ir.domainField x.domain)).name))
           else decide (x.node.map (·.name) = some s))
    | .pred p => decide (x.type = .bit) && decide (p < ir.predicates.length) &&
        (ir.predT.getD p default).body.isBoolCheck v &&
        decide ((ir.predT.getD p default).role = .type v)
    | .none => false

theorem typeSourcedV_iff (treeNodes : ℕ → List String) (v : ℕ) :
    ir.typeSourcedV treeNodes v (ir.value v) = true ↔ ir.TypeSourced treeNodes v := by
  have hp : ∀ p, ir.predT.getD p default = ir.predicate p := fun p => toTrie_getD_eq _ p
  unfold typeSourcedV TypeSourced
  simp only [hp, isLateNode]
  cases hb : (ir.value v).kind.isBound
  · simp only [Bool.false_eq_true, if_false]
    cases hn : (ir.value v).type.nodeName
    · simp
    · cases hts : (ir.value v).typeSource
      · simp only
        by_cases hl : (ir.value v).kind.isLate = true <;> simp [hl]
      · simp [and_assoc]
      · simp
  · simp

/-- **`TypeSources treeNodes`**, in one pass over the values. -/
def typesB (treeNodes : ℕ → List String) : Bool :=
  allIdx (fun v x => !(x.isCommittedB || x.kind.isLate) || ir.typeSourcedV treeNodes v x) ir.values 0

/-- **`typesB` is `TypeSources`.** -/
theorem typesB_iff (treeNodes : ℕ → List String) :
    ir.typesB treeNodes = true ↔ ir.TypeSources treeNodes := by
  simp only [typesB, TypeSources, allIdx_values_iff, isCommitted_eq,
    isLateNode, ← typeSourcedV_iff]
  refine forall₂_congr fun v _ => ?_
  cases ((ir.value v).isCommittedB || (ir.value v).kind.isLate) <;> simp

end

end GordieHowe.RealizedProgram
