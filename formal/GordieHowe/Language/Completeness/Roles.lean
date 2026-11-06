-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.RealizedProgram.CellsLowering
public import GordieHowe.Language.RealizedProgram.Reader
public import GordieHoweNative.Language.Completeness.Roles
public import GordieHoweNative.Language.RealizedProgram.Shapes

public section

/-!
# GordieHowe: the honest roles of a realized program

The program facts every application's honest strategy reads, stated once over the realized
program and its structure records and checked once per program (`honestRolesB`, the generated
`Completion.rolesOk`):

* every node-typed value that is not late is a bit view of a committed value with type `Bit`, or a
  committed cell whose type its node states (`typedClassB`);
* no late value is a source value;
* every `kpriv` source value whose type no node states has a checked type (`KprivTyped`);
* every value bound to its digits has the field or a node of `L` as its type (`natTypedInB`);
* every source `mod_q` in the field form has its field row at the records' pointer (`fieldRowsB`);
* no table is γ-packed (`NoGammaTables`).

`HonestRoles` bundles them (`honestRoles_of_B`). From them, the node-typed source values lie in their
types at the source environment of any committed values that put each committed source cell in its
node (`HonestRoles.inType`, `HonestRoles.sourceSatAt`), and the bound values' types contain `1`
(`HonestRoles.boundOneMem`). The MAC sites are the `macSite` records the completeness certificate
reads (`CompletionFacts.macs`). A program's cross-field `equal`s cross the operands it states
(`crossOperandsB`), whose bits give `CrossBitsAt` (`crossBitsAt_of_operands`).
-/

namespace GordieHowe.RealizedProgram

section

variable (ir : RealizedProgram) {I : Interp}

/-- **Whether value `v` is a bit view of a committed value with type `Bit`.** -/
@[expose] def privBitsB (v : ℕ) : Bool :=
  (match (ir.value v).kind with
    | .bits w _ =>
      match (ir.value w).kind with
      | .priv => true
      | _ => false
    | _ => false) && (ir.value v).type == .bit

/-- **Whether a committed cell's type is the one its node states**: a subfield type `E` at node
`E`; `Bit` at a node (whose elements the model makes `0` and `1`, `Interp.BitNodes`); the field
always. -/
@[expose] def cellTypeB (v : ℕ) : Bool :=
  match (ir.value v).type with
  | .sub E => (ir.value v).node.map (·.name) == some E
  | .bit => (ir.value v).node.isSome
  | .field => true

/-- **Every node-typed value that is not late has its type from its node**, as a check at value
`v`: a bit view of a committed value with type `Bit` (`privBitsB`), or a committed cell whose type
its node states (`cellTypeB`). -/
@[expose] def typedClassB (v : ℕ) : Bool :=
  !((ir.value v).typeSource == .node) || decide (ir.IsLate v) || ir.privBitsB v ||
    (ir.privCellB v && ir.cellTypeB v)

/-- **The honest roles' checks at value `v`**: its type class (`typedClassB`), not both late and a
source value, and, bound to its digits, the field or a node of `L` as its type. -/
@[expose] def valueRolesB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  ir.typedClassB v && (!decide (ir.IsLate v) || !decide (ir.IsSourceValue v)) &&
    (!(ir.value v).kind.isBound || ir.natTypedInB L v)

/-- **The honest roles' checks** at the nodes `L` and the structure records `S`: every value's
(`valueRolesB`), the `kpriv` source values' types, the field rows at their pointers and no γ-packed
table. -/
@[expose] def honestRolesB (L : List (ℕ × String)) (S : Structure) : Bool :=
  (List.range ir.values.length).all (ir.valueRolesB L) && decide ir.KprivTyped &&
    ir.fieldRowsB S && decide ir.NoGammaTables

theorem honestRolesB_eq_reader (L : List (ℕ × String)) (S : Structure) :
    ir.honestRolesB L S = @PReader.honestRolesB ir (PReader.ofProgram ir) L S := by
  have h : decide ir.KprivTyped =
      @decide (@PReader.KprivTyped ir (PReader.ofProgram ir)) inferInstance := by
    apply congrArg (@decide ir.KprivTyped)
    exact Subsingleton.elim _ _
  exact congrArg (fun b => (List.range ir.values.length).all (ir.valueRolesB L) && b &&
    ir.fieldRowsB S && decide ir.NoGammaTables) h

/-- **Compiled code runs the honest roles' check at the program's context built once**
(`honestRolesBC`). -/
@[csimp] theorem honestRolesB_csimp : @honestRolesB = @honestRolesBC := by
  funext ir L S
  rw [honestRolesB_eq_reader, honestRolesBC]
  show _ = @PReader.honestRolesB ir (PReader.ofCtx (PCtx.build ir)) L S
  rw [PReader.ofCtx_build]

/-- **The honest roles of a program** at the nodes `L` and the structure records `S` (module
docstring). Properties of the program, checked once per program (`honestRoles_of_B`). -/
structure HonestRoles (L : List (ℕ × String)) (S : Structure) : Prop where
  /-- Every node-typed value that is not late has its type from its node (`typedClassB`). -/
  typed : ∀ v < ir.values.length, ir.typedClassB v = true
  /-- No late value is a source value. -/
  noSourceLate : ∀ v < ir.values.length, ir.IsLate v → ¬ ir.IsSourceValue v
  /-- Every `kpriv` source value whose type no node states has a checked type. -/
  kprivTyped : ir.KprivTyped
  /-- Every value bound to its digits has the field or a node of `L` as its type. -/
  boundNatTyped : ∀ v < ir.values.length, (ir.value v).kind.isBound = true →
    ir.natTypedInB L v = true
  /-- Every source `mod_q` in the field form has its field row at the records' pointer. -/
  fieldRows : ir.fieldRowsB S = true
  /-- No table is γ-packed. -/
  noGamma : ir.NoGammaTables

variable {ir}

/-- **The honest roles from their check.** -/
theorem honestRoles_of_B {L : List (ℕ × String)} {S : Structure}
    (h : ir.honestRolesB L S = true) : ir.HonestRoles L S := by
  unfold honestRolesB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hv, hk⟩, hf⟩, hg⟩ := h
  have hv' : ∀ v < ir.values.length, _ := fun v hlt => by
    have := hv v hlt
    unfold valueRolesB at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      at this
    exact this
  exact {
    typed := fun v hlt => (hv' v hlt).1.1
    noSourceLate := fun v hlt hl hs => by
      rcases (hv' v hlt).1.2 with h | h
      · exact h hl
      · exact h hs
    kprivTyped := hk
    boundNatTyped := fun v hlt hb => by
      rcases (hv' v hlt).2 with h | h
      · rw [hb] at h
        cases h
      · exact h
    fieldRows := hf
    noGamma := hg }

variable {L : List (ℕ × String)} {S : Structure}

/-- **The bound values' subfield types contain `1`** where the nodes `L` do
(`boundOneMem_of_natTypedIn`). -/
theorem HonestRoles.boundOneMem (hR : ir.HonestRoles L S) (hO : OneNodes I L) :
    ir.BoundOneMem I :=
  boundOneMem_of_natTypedIn hO hR.boundNatTyped

/-- **A node-typed source value that is not late lies in its type** at the source environment of
the committed values `V`, where `V` puts each committed source cell in its node (`hmem`) and the
model's nodes of `Bit` values are `{0, 1}` (`hbit`): a bit view of a committed value reads a bit; a
committed cell reads its committed value. -/
theorem HonestRoles.inType (hR : ir.HonestRoles L S)
    (hbit : I.BitNodes ir) {V : ir.Valuation I}
    (hmem : ∀ v < ir.values.length, ir.privCellB v = true → ir.IsSourceValue v → ∀ j E,
      (ir.value v).node.map (·.name) = some E → V v j ∈ (I (ir.valueField v)).node E)
    (x : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) {v : ℕ}
    (hv : v < ir.values.length) (hts : (ir.value v).typeSource = .node) (hl : ¬ ir.IsLate v)
    (hsrc : ir.IsSourceValue v) {j : ℕ} (hj : j < (ir.value v).size) :
    (I (ir.valueField v)).InType (ir.value v).type (ir.reader (ir.srcEnv I x V c π) v j) := by
  have hcl := hR.typed v hv
  unfold typedClassB at hcl
  simp only [hts, beq_self_eq_true, Bool.not_true, Bool.false_or, hl, decide_false,
    Bool.or_eq_true, Bool.and_eq_true] at hcl
  rcases hcl with hb | ⟨hp, hty⟩
  · unfold privBitsB at hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨hk, hty⟩ := hb
    rw [hty]
    revert hk
    rcases hkv : (ir.value v).kind with _ | _ | _ | _ | _ | ⟨w, sel⟩ | _ | _ | _ <;>
      simp only [Bool.false_eq_true, IsEmpty.forall_iff]
    rcases hkw : (ir.value w).kind <;> simp only [Bool.false_eq_true, IsEmpty.forall_iff]
    intro _
    rw [reader_of_bits_of_priv _ hkv hkw]
    unfold FieldInterp.ofBool
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [reader_srcEnv_of_privCellB x _ c π hp hj]
    unfold cellTypeB at hty
    revert hty
    cases hbty : (ir.value v).type with
    | sub E =>
      intro hty
      exact hmem v hv hp hsrc j E (by simpa using hty)
    | bit =>
      intro hty
      obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.1 hty
      exact hbit v hv hbty hts nr hnr _ (hmem v hv hp hsrc j nr.name (by rw [hnr]; rfl))
    | field => intro _; trivial

/-- **The source program holds at the source environment of the committed values `V`** where every
source predicate holds there (`hpreds`) and `V` puts each committed source cell in its node
(`hmem`, `HonestRoles.inType`). -/
theorem HonestRoles.sourceSatAt (hR : ir.HonestRoles L S)
    (hbit : I.BitNodes ir) {V : ir.Valuation I}
    (hmem : ∀ v < ir.values.length, ir.privCellB v = true → ir.IsSourceValue v → ∀ j E,
      (ir.value v).node.map (·.name) = some E → V v j ∈ (I (ir.valueField v)).node E)
    {x : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k} {π : (ir.layout I).Pads}
    (hpreds : ∀ p ∈ ir.predicates, ir.inSource p = true → ir.HoldsAt (ir.srcEnv I x V c π) p.body) :
    ir.SourceSatAt (ir.srcEnv I x V c π) where
  preds := hpreds
  types v hv hs hts _ hj :=
    hR.inType hbit hmem x c π hv hts (fun hl => hR.noSourceLate v hv hl hs) hs hj

/-! ## The operands of the cross-field `equal`s -/

variable (ir) in
/-- **Every cross-field `equal` crosses `x` of domain `dx` and `y` of domain `dy`**, as a check. -/
@[expose] def crossOperandsB (dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .cross dx' x' dy' y' _ _ => dx' == dx && x'.beq x && dy' == dy && y'.beq y
    | _ => true

/-- **The operands of every cross-field `equal`**, from the complete list of cross predicates. -/
theorem crossOperandsB_of_crossPredicateIds {dx dy : ℕ} {x y : Expr} {ids : List ℕ}
    (hids : ir.crossPredicateIds = ids)
    (h : ∀ q ∈ ids, (match (ir.predicate q).body with
      | .cross dx' x' dy' y' _ _ => dx' == dx && x'.beq x && dy' == dy && y'.beq y
      | _ => true) = true) :
    ir.crossOperandsB dx x dy y = true := by
  unfold crossOperandsB
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hp
  have hpq : ir.predicates[q] = ir.predicate q := by
    rw [ir.predicate_eq_getD, List.getD_eq_getElem _ _ hq]
  rw [hpq]
  by_cases hc : (ir.predicate q).body.isCross = true
  · refine h q ?_
    rw [← hids, crossPredicateIds, List.mem_filter, predicateT_eq]
    exact ⟨List.mem_range.2 hq, hc⟩
  · cases hb : (ir.predicate q).body with
    | cross => rw [hb] at hc; exact absurd rfl hc
    | _ => rfl

/-- **The operands of every cross-field `equal`**, from their check. -/
theorem cross_operands_of_B {dx dy : ℕ} {x y : Expr} (h : ir.crossOperandsB dx x dy y = true)
    {p : Predicate} (hp : p ∈ ir.predicates) {dx' dy' : ℕ} {x' y' : Expr} {k : CrossKind}
    {real : MacRealization} (hb : p.body = .cross dx' x' dy' y' k real) :
    dx' = dx ∧ x' = x ∧ dy' = dy ∧ y' = y := by
  have := List.all_eq_true.1 h p hp
  rw [hb] at this
  simp only [Bool.and_eq_true, beq_iff_eq, Expr.beq_iff] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- **The cross-field operand check follows from its pointwise specification.** -/
theorem crossOperandsB_of_operands {dx dy : ℕ} {x y : Expr}
    (h : ∀ p ∈ ir.predicates, ∀ dx' x' dy' y' k real,
      p.body = .cross dx' x' dy' y' k real →
      dx' = dx ∧ x' = x ∧ dy' = dy ∧ y' = y) :
    ir.crossOperandsB dx x dy y = true := by
  apply List.all_eq_true.mpr
  intro p hp
  cases hb : p.body <;> try rfl
  rename_i dx' x' dy' y' k real
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h p hp dx' x' dy' y' k real hb
  simp only [beq_self_eq_true, Expr.beq_iff, Bool.and_eq_true, and_self]

/-- **The source cross-field `equal`s read bits in the environment `e`** where every cross-field
`equal` crosses `x` of domain `dx` and `y` of domain `dy` (`crossOperandsB`) and both read bits
there. -/
theorem crossBitsAt_of_operands {dx dy : ℕ} {x y : Expr} (h : ir.crossOperandsB dx x dy y = true)
    {e : ir.Env I}
    (hx : ∀ i < ir.exprLen x, ir.evalWith (ir.reader e) dx x i = 0 ∨ ir.evalWith (ir.reader e) dx x i = 1)
    (hy : ∀ i < ir.exprLen y, ir.evalWith (ir.reader e) dy y i = 0 ∨ ir.evalWith (ir.reader e) dy y i = 1) :
    ir.CrossBitsAt I e := by
  intro p hp _ dx' x' dy' y' k real hb
  obtain ⟨rfl, rfl, rfl, rfl⟩ := cross_operands_of_B h hp hb
  exact ⟨hx, hy⟩

end

end GordieHowe.RealizedProgram
