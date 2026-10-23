-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Locality
public import GordieHowe.Language.RealizedProgram.SpectralSound

@[expose] public section

/-!
# GordieHowe: the cells lowering of a program

The last step of the proof system's lowering: from the realized program (`GordieHowe.RealizedProgram.Realized`, on the
program's committed assignment) to the predicates of its committing domains (`GordieHowe.RealizedProgram.domainOf`, on
each domain's cells). The committed assignment is read from every domain's cells
(`GordieHowe.RealizedProgram.ofAllCells`), each value from its own domain's; each domain's predicate reads the values
through its own cells (`GordieHowe.RealizedProgram.cellValuation`), which agree with the assignment of all domains at
every value the domain's constraints read (`GordieHowe.RealizedProgram.Local`, `GordieHowe/Language/RealizedProgram/Locality.lean`).

**The checks** (`GordieHowe.RealizedProgram.CellsValid`, decidable, checked by `decide +kernel` on each program):

* the program has a domain;
* every field `equal` and every `mod_0` of the program is lowered into its own domain
  (`GordieHowe.RealizedProgram.loweredOwnB`: an affine row or a family of rows on views of the domain, placed in a GKR
  circuit of the domain, or a part of a batch of the domain that passes the batch check,
  `GordieHowe.RealizedProgram.BatchOk`, on columns or on bits);
* every group of every lookup table has its LogUp identity as a realization circuit of a GKR
  circuit of a domain (`GordieHowe.RealizedProgram.logupAnyB`), and a value of `α`'s field holds every table's
  challenge (`GordieHowe.RealizedProgram.alphaNodeB`);
* every value whose type its packing-tree node enforces is a committed value of its domain whose
  node is its type's subfield (or, for a `Bit` value, a node the model reads as `{0, 1}`,
  `Interp.BitNodes`), a bit view of type `Bit`, or a late value of its domain whose pad space is its
  type's node (`GordieHowe.RealizedProgram.typeOwnB`);
* every entry of every GKR circuit is a predicate of the program, a LogUp identity of a group of a
  table, an alignment check or a realization circuit given no meaning (`GordieHowe.RealizedProgram.entryOkB`; no H
  half of a cross-field `equal`).

**Soundness** (`GordieHowe.RealizedProgram.realizedAt_of_holds`, `GordieHowe.RealizedProgram.cellsLowering`): where every domain's
predicate holds on its cells `a d`, the realized program holds at the committed assignment of all
domains (`RealizedProgram.ofAllCells a`, read through `GordieHowe.RealizedProgram.bindAsg`): every lowered predicate holds
placed at its domain's cells' valuation, which is the reader of all domains at everything it reads
(`GordieHowe.RealizedProgram.Local.preds`, `GordieHowe.RealizedProgram.Local.logup`). The projection is `ofAllCells`; there is no event.
Two properties of the model enter: the fields of the domains with batches on bits have additive
bit coordinates (`GordieHowe.RealizedProgram.BitsBatchAdditive`) and the nodes of node-typed `Bit` values are `{0, 1}`
(`Interp.BitNodes`).

**The honest prover**: where the program and the realized program hold at the
realized assignment of the assignment of all domains and every cell lies in its base, every domain's
predicate holds on its cells (a placed `mod_0` by its field equation),
each constraint transported from the reader of all domains to the domain's cells by locality. The
proof system's honest prover uses it at the cells of the honest values
(`GordieHowe/Language/Honest/Basic.lean`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout

/-! ## Casts into a node -/

/-- **A cast between equal field identifiers keeps membership in a node.** -/
theorem castElt_mem_node {I : Interp} {a b : ℕ} (h : a = b) {x : (I a).K} {E : String}
    (hx : x ∈ (I a).node E) : (castElt x : (I b).K) ∈ (I b).node E := by
  subst h
  simpa using hx

/-- **A cast between equal field identifiers keeps membership in a space.** -/
theorem castElt_mem_space {I : Interp} {a b : ℕ} (h : a = b) {x : (I a).K} {s : Space}
    (hx : x ∈ (I a).space s) : (castElt x : (I b).K) ∈ (I b).space s := by
  subst h
  simpa using hx

section

variable (ir : RealizedProgram)

/-! ## The checks -/

/-- **Predicate `p` is a part of a batch on columns of domain `d` the proof system covers**
(`RealizedProgram.BatchOk`). -/
def batchPartB (d p : ℕ) : Bool :=
  (List.finRange ir.batches.length).any fun b =>
    ir.colsBatchOkB d b && decide (p ∈ (ir.batch b).parts)

/-- **Predicate `p` is a part of a batch on bits of domain `d` the proof system covers**
(`RealizedProgram.BatchOk`). -/
def bitsBatchPartB (d p : ℕ) : Bool :=
  (List.finRange ir.batches.length).any fun b =>
    ir.bitsBatchOkB d b && decide (p ∈ (ir.batch b).parts)

/-- **Predicate `p` is lowered into domain `d`**, decided (`RealizedProgram.Lowered`): a predicate of the
program that is an affine row of `d`, a family of rows on views of `d`, a part of a batch of `d` the
proof system covers, on columns or on bits, a quadratic triple of `d`, or a field `equal` or a `mod_0`
placed in a GKR circuit of `d`. -/
def loweredB (d p : ℕ) : Bool :=
  decide (p < ir.predicates.length) &&
    (ir.isRow d p || ir.isViewRow d p || ir.batchPartB d p || ir.bitsBatchPartB d p ||
      ir.isQuad d p ||
      (((ir.predicate p).body.isEqual || (ir.predicate p).body.isIntEq) &&
        (List.finRange ir.circuits.length).any fun c =>
          decide ((ir.circuit c).domain = d) &&
            (decide (CircuitEntry.pred p ∈ (ir.circuit c).entries) ||
              decide (CircuitEntry.typeCheck p ∈ (ir.circuit c).entries))))

/-- **Predicate `p` is lowered into its own domain** (`PredBody.domain?`), a domain of the
program. -/
def loweredOwnB (p : ℕ) : Bool :=
  match (ir.predicate p).body.domain? with
  | some d => decide (d < ir.domains.length) && ir.loweredB d p
  | none => false

/-- **The LogUp identity of group `g` of table `t` is a realization circuit of a domain**: an
entry of a GKR circuit whose domain is a domain of the program. -/
def logupAnyB (t g : ℕ) : Bool :=
  (List.finRange ir.circuits.length).any fun c =>
    decide ((ir.circuit c).domain < ir.domains.length) &&
      decide (CircuitEntry.realization (.logup t g) ∈ (ir.circuit c).entries)

/-- **The H half of cross-field `equal` `p` is stated by the compiler's own circuit, with a value
holding its key**: `p` is a hosted cross-field `equal` (no `x`-side blind) with no `<mac>.H`
predicate whose key is held by a value of the key's field (`RealizedProgram.chalNode`). -/
def macHNodeB (p : ℕ) : Bool :=
  match (ir.predicate p).body with
  | .cross _ _ _ _ _ real =>
    match real.hPredicate, real.blindX, ir.chalNode real.key with
    | none, none, some v => decide (ir.valueField v = ir.chalField real.key)
    | _, _, _ => false
  | _ => false

/-- **The H half of cross-field `equal` `p` is a realization circuit of a domain**: an entry of a
GKR circuit whose domain is a domain of the program. -/
def macHAnyB (p : ℕ) : Bool :=
  (List.finRange ir.circuits.length).any fun c =>
    decide ((ir.circuit c).domain < ir.domains.length) &&
      decide (CircuitEntry.realization (.macH p) ∈ (ir.circuit c).entries)

/-- **The H half of predicate `p` is covered**: a hosted cross-field `equal` (no `x`-side blind)
with no `<mac>.H` predicate has its H half as a realization circuit of a domain (`macHAnyB`); any
other predicate needs nothing. -/
def macHCoveredB (p : ℕ) : Bool :=
  match (ir.predicate p).body with
  | .cross _ _ _ _ _ real =>
    match real.hPredicate, real.blindX with
    | none, none => ir.macHAnyB p
    | _, _ => true
  | _ => true

/-- **A value of `α`'s field holds table `t`'s challenge** (`RealizedProgram.chalNode`). -/
def alphaNodeB (t : ℕ) : Bool :=
  match ir.chalNode (ir.alphaOf t) with
  | some v => decide (ir.valueField v = ir.chalField (ir.alphaOf t))
  | none => false

/-- **Value `v`'s type is its cells' base in domain `d`**: a committed value of `d` (kind `priv`)
typed `Field`, or typed `Sub(E)` at the node `E`. -/
def typeAtCellB (d v : ℕ) : Bool :=
  ir.isCellValue d v &&
    (match (ir.value v).kind with
      | .priv => true
      | _ => false) &&
    match (ir.value v).type with
    | .field => true
    | .sub E => (ir.value v).node.map (·.name) == some E
    | .bit => (ir.value v).node.isSome

/-- **Value `v` is a bit view of type `Bit`**: its readings are bits (`FieldInterp.ofBool`). -/
def bitViewTypeB (v : ℕ) : Bool :=
  (match (ir.value v).kind with
    | .bits _ _ => true
    | _ => false) && decide ((ir.value v).type = .bit)

/-- **Value `v` is a late value of domain `d` masked over its type's node**: a late value of `d`
that is no committed value, of type `Sub(E)` with pad space the node `E`. Its message and its pad lie
in `E`, so it does. -/
def lateTypeB (d v : ℕ) : Bool :=
  ir.isLateOf d v && !ir.isCellValue d v &&
    match (ir.value v).type, (ir.value v).padSpace with
    | .sub E, .node E' => E == E'
    | _, _ => false

/-- **Value `v`'s type follows from its domain's cells**, a domain of the program: its type is its
cells' base (`typeAtCellB`), it is a bit view of type `Bit` (`bitViewTypeB`), or a late value masked
over its type's node (`lateTypeB`). -/
def typeOwnB (v : ℕ) : Bool :=
  decide ((ir.value v).domain < ir.domains.length) &&
    (ir.typeAtCellB (ir.value v).domain v || ir.bitViewTypeB v ||
      ir.lateTypeB (ir.value v).domain v)

/-- **An entry of a GKR circuit the honest prover covers**: a Boolean check or a placed predicate of
the program, the LogUp identity of a group of a table, an alignment check, or a realization circuit
given no meaning (`named`, `unmodeled`), or the H half of a cross-field `equal` with a value holding
its key (`macHNodeB`). -/
def entryOkB : CircuitEntry → Bool
  | .typeCheck p => decide (p < ir.predicates.length)
  | .alignment _ => true
  | .pred p => decide (p < ir.predicates.length)
  | .realization (.logup t g) => decide (t < ir.tables.length) && decide (g < ir.groupCountOf t)
  | .realization (.macH p) => decide (p < ir.predicates.length) && ir.macHNodeB p
  | .realization (.named _) => true
  | .realization (.unmodeled _) => true

/-- **Predicate `p` is realized through its convolutions' realizations** (`Target.realized q`):
a field `equal` or a `mod_0` of a domain of the program whose target is `realized q`, admitted by
`RealizedAdmits` (its field equation is `q`'s, the convolutions read through their spectral
realizations, `fieldEq_of_realized`). -/
def realizedOwnB (p : ℕ) : Bool :=
  match (ir.predicate p).body with
  | .equal d e e' (.realized q) => decide (d < ir.domains.length ∧ ir.RealizedAdmits d e e' q)
  | .mod d 0 e e' real =>
    match real.target with
    | some (.realized q) => decide (d < ir.domains.length ∧ ir.RealizedAdmits d e e' q)
    | _ => false
  | _ => false

/-- **The program's GKR circuits and affine rows enforce its realized program in its domains** (see
the module docstring): a domain, every field `equal` and `mod_0` lowered into its domain, every
group's LogUp identity a realization circuit of a domain with `α` held by a value of its field,
every node-typed value a committed value at its type's node, and every circuit entry covered by the
honest prover. -/
structure CellsValid : Prop where
  /-- The program has a domain. -/
  nonempty : ir.domains.length ≠ 0
  /-- Every field `equal` and every `mod_0` is lowered into its domain, or realized through its
  convolutions' realizations. -/
  equal : ∀ p < ir.predicates.length,
    ((ir.predicate p).body.isEqual || (ir.predicate p).body.isIntEq) = true →
      (ir.loweredOwnB p || ir.realizedOwnB p) = true
  /-- Every group's LogUp identity is a realization circuit of a domain. -/
  logup : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ir.logupAnyB t g = true
  /-- A value of `α`'s field holds every table's challenge. -/
  alpha : ∀ t < ir.tables.length, ir.alphaNodeB t = true
  /-- Every node-typed value is a committed value of its domain at its type's node. -/
  types : ∀ v < ir.values.length, (ir.value v).typeSource = .node → ir.typeOwnB v = true
  /-- Every entry of every GKR circuit is covered by the honest prover. -/
  entries : ∀ c < ir.circuits.length, ∀ e ∈ (ir.circuit c).entries, ir.entryOkB e = true
  /-- Every H half stated by the compiler's own circuit is a realization circuit of a domain. -/
  macH : ∀ p < ir.predicates.length, ir.macHCoveredB p = true

theorem cellsValid_iff : ir.CellsValid ↔
    ir.domains.length ≠ 0 ∧
      (∀ p < ir.predicates.length,
        ((ir.predicate p).body.isEqual || (ir.predicate p).body.isIntEq) = true →
          (ir.loweredOwnB p || ir.realizedOwnB p) = true) ∧
      (∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ir.logupAnyB t g = true) ∧
      (∀ t < ir.tables.length, ir.alphaNodeB t = true) ∧
      (∀ v < ir.values.length, (ir.value v).typeSource = .node → ir.typeOwnB v = true) ∧
      (∀ c < ir.circuits.length, ∀ e ∈ (ir.circuit c).entries, ir.entryOkB e = true) ∧
      ∀ p < ir.predicates.length, ir.macHCoveredB p = true :=
  ⟨fun h => ⟨h.nonempty, h.equal, h.logup, h.alpha, h.types, h.entries, h.macH⟩,
    fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩⟩

instance : Decidable ir.CellsValid := decidable_of_iff _ ir.cellsValid_iff.symm

variable {ir}

/-! ## The checks' meaning -/

/-- **A predicate decided lowered is lowered** (`RealizedProgram.Lowered`). -/
theorem lowered_of_loweredB {d p : ℕ} (h : ir.loweredB d p = true) : ir.Lowered d p := by
  simp only [loweredB, batchPartB, bitsBatchPartB, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨hp, ((((hrow | hvrow) | ⟨b, hb, hmem⟩) | ⟨b, hb, hmem⟩) | hq) | ⟨heq, c, hc, hmem⟩⟩ := h
  · exact .row hp hrow
  · exact .viewRow hp hvrow
  · exact .batch ⟨b, hb⟩ hmem
  · exact .bitsBatch b hb hmem
  · exact .quad hp hq
  · exact .placed ⟨c, hc⟩ (Bool.or_eq_true_iff.2 heq) hmem

/-- **A predicate decided lowered into its own domain** is lowered into a domain `d` of the
program, its domain. -/
theorem exists_lowered_of_loweredOwnB {p : ℕ} (h : ir.loweredOwnB p = true) :
    ∃ d : Fin ir.domains.length, (ir.predicate p).body.domain? = some (d : ℕ) ∧ ir.Lowered d p := by
  unfold loweredOwnB at h
  split at h
  · rename_i d hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨⟨d, h.1⟩, hd, lowered_of_loweredB h.2⟩
  · cases h

/-- **A field `equal` whose target is no realization's is not realized.** -/
theorem realizedOwnB_equal {p d : ℕ} {e e' : Expr} {t : Target}
    (hb : (ir.predicate p).body = .equal d e e' t) (ht : t.isRealized = false) :
    ir.realizedOwnB p = false := by
  unfold realizedOwnB
  rw [hb]
  cases t <;> simp_all [Target.isRealized]

/-- **A realized field `equal`**: its target is `realized q`, admitted. -/
theorem realizedAdmits_of_equal {p d : ℕ} {e e' : Expr} {t : Target}
    (hb : (ir.predicate p).body = .equal d e e' t) (h : ir.realizedOwnB p = true) :
    d < ir.domains.length ∧ ∃ q, ir.RealizedAdmits d e e' q := by
  unfold realizedOwnB at h
  rw [hb] at h
  cases t <;> simp_all
  exact ⟨_, h.2⟩

/-- **A realized `mod_0`**: its target is `realized q`, admitted. -/
theorem realizedAdmits_of_mod {p d : ℕ} {e e' : Expr} {real : ModRealization}
    (hb : (ir.predicate p).body = .mod d 0 e e' real) (h : ir.realizedOwnB p = true) :
    d < ir.domains.length ∧ ∃ q, ir.RealizedAdmits d e e' q := by
  unfold realizedOwnB at h
  rw [hb] at h
  simp only at h
  split at h
  · simp only [decide_eq_true_eq] at h
    exact ⟨h.1, _, h.2⟩
  · cases h

/-- **A LogUp identity decided in a domain** is an entry of a GKR circuit of a domain of the
program. -/
theorem exists_logup_of_logupAnyB {t g : ℕ} (h : ir.logupAnyB t g = true) :
    ∃ c : Fin ir.circuits.length, (ir.circuit c).domain < ir.domains.length ∧
      CircuitEntry.realization (.logup t g) ∈ (ir.circuit c).entries := by
  simp only [logupAnyB, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h

/-- **An H half decided in a domain** is an entry of a GKR circuit of a domain of the program. -/
theorem exists_macH_of_macHAnyB {p : ℕ} (h : ir.macHAnyB p = true) :
    ∃ c : Fin ir.circuits.length, (ir.circuit c).domain < ir.domains.length ∧
      CircuitEntry.realization (.macH p) ∈ (ir.circuit c).entries := by
  simp only [macHAnyB, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h

/-- **An H half with its key decided held**: `p` is a cross-field `equal` with no `<mac>.H`
predicate whose key is held by a value of the key's field. -/
theorem exists_of_macHNodeB {p : ℕ} (h : ir.macHNodeB p = true) :
    ∃ dx x dy y k real v, (ir.predicate p).body = .cross dx x dy y k real ∧
      real.hPredicate = none ∧ real.blindX = none ∧ ir.chalNode real.key = some v ∧
        ir.valueField v = ir.chalField real.key := by
  unfold macHNodeB at h
  split at h
  · rename_i dx x dy y k real hb
    split at h
    · rename_i v hn hbx hv
      exact ⟨dx, x, dy, y, k, real, v, hb, hn, hbx, hv, of_decide_eq_true h⟩
    · cases h
  · cases h

/-- **The H half at an environment's reader is `MacHHoldsAt` at the key**, when a value of the key's
field holds the key. -/
theorem macHHolds_reader_iff {I : Interp} (e : ir.Env I) {p dx : ℕ} {x : Expr} {dy : ℕ} {y : Expr}
    {k : CrossKind} {real : MacRealization} {v : ℕ}
    (hb : (ir.predicate p).body = .cross dx x dy y k real) (hn : real.hPredicate = none)
    (hv : ir.chalNode real.key = some v) (hf : ir.valueField v = ir.chalField real.key) :
    ir.MacHHolds (ir.reader e) p ↔
      ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0)) := by
  simp only [MacHHolds, hb, hn, hv]
  rw [← ir.reader_chalNode e hv hf, castElt_castElt_eq, if_pos hf]

/-- **A table's challenge decided held** is held by a value of `α`'s field. -/
theorem exists_chalNode_of_alphaNodeB {t : ℕ} (h : ir.alphaNodeB t = true) :
    ∃ v, ir.chalNode (ir.alphaOf t) = some v ∧ ir.valueField v = ir.chalField (ir.alphaOf t) := by
  unfold alphaNodeB at h
  split at h
  · exact ⟨_, by assumption, of_decide_eq_true h⟩
  · cases h

/-- **A node-typed value decided at its cells** is a committed value of the domain, of kind
`priv`, whose type is `Field` or its node's subfield. -/
theorem typeAtCellB_spec {d v : ℕ} (h : ir.typeAtCellB d v = true) :
    ir.isCellValue d v = true ∧ (ir.value v).kind = .priv ∧
      ((ir.value v).type = .field ∨
        (∃ nr : NodeRef, (ir.value v).node = some nr ∧ (ir.value v).type = .sub nr.name) ∨
        ∃ nr : NodeRef, (ir.value v).node = some nr ∧ (ir.value v).type = .bit) := by
  unfold typeAtCellB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hc, hk⟩, ht⟩ := h
  refine ⟨hc, ?_, ?_⟩
  · revert hk
    cases (ir.value v).kind <;> simp
  · revert ht
    cases hty : (ir.value v).type with
    | field => exact fun _ => .inl rfl
    | bit =>
      cases hn : (ir.value v).node with
      | none => simp
      | some nr => exact fun _ => .inr (.inr ⟨nr, rfl, rfl⟩)
    | sub E =>
      cases hn : (ir.value v).node with
      | none => simp
      | some nr =>
        simp only [Option.map_some, beq_iff_eq, Option.some.injEq]
        rintro rfl
        exact .inr (.inl ⟨nr, rfl, rfl⟩)

/-! ## Locality -/

variable {I : Interp} {treeNodes : ℕ → List String}

/-- **A predicate of domain `d` holds placed at `d`'s cells exactly when at all domains'**: the
cells' valuation of `d` and the reader of all domains agree at everything it reads
(`Local.preds`). -/
theorem placedHolds_cellValuation_iff (hl : ir.Local treeNodes)
    (a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K)
    (d : Fin ir.domains.length) {x : ir.Valuation I} {r : (ir.layout I).Run} {pid : ℕ}
    (hpid : pid < ir.predicates.length) (hd : (ir.predicate pid).body.domain? = some (d : ℕ)) :
    ir.PlacedHolds (ir.cellValuation I d x r (a d)) (ir.predicate pid).body ↔
      ir.PlacedHolds (ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r))
        (ir.predicate pid).body :=
  placedHolds_congr fun v hv =>
    cellValuation_eq_reader a d (hl.preds _ (predicate_mem hpid) d hd v hv)

/-- **A LogUp identity of a circuit of domain `d` holds at `d`'s cells exactly when at all
domains'** (`Local.logup`). -/
theorem logupHoldsAt_cellValuation_iff (hl : ir.Local treeNodes)
    (a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K)
    {c : Fin ir.circuits.length} (d : Fin ir.domains.length) (hcd : (ir.circuit c).domain = d)
    {x : ir.Valuation I} {r : (ir.layout I).Run} {t g : ℕ}
    (hmem : CircuitEntry.realization (.logup t g) ∈ (ir.circuit c).entries) :
    ir.LogupHoldsAt (ir.cellValuation I d x r (a d)) t g ↔
      ir.LogupHoldsAt (ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r)) t g :=
  logupHoldsAt_congr fun v hv =>
    cellValuation_eq_reader a d (hcd ▸ hl.logup c c.2 t g hmem v hv)

/-- **The H half of a circuit of domain `d` holds at `d`'s cells exactly when at all domains'**
(`Local.macH`). -/
theorem macHHolds_cellValuation_iff (hl : ir.Local treeNodes)
    (a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K)
    {c : Fin ir.circuits.length} (d : Fin ir.domains.length) (hcd : (ir.circuit c).domain = d)
    {x : ir.Valuation I} {r : (ir.layout I).Run} {p : ℕ}
    (hmem : CircuitEntry.realization (.macH p) ∈ (ir.circuit c).entries) :
    ir.MacHHolds (ir.cellValuation I d x r (a d)) p ↔
      ir.MacHHolds (ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r)) p :=
  macHHolds_congr fun v hv =>
    cellValuation_eq_reader a d (hcd ▸ hl.macH c c.2 p hmem v hv)

/-! ## Soundness -/

/-- **The nodes of the program's node-typed `Bit` values are `{0, 1}`** (a property of the
model): every value of type `Bit` whose type its packing-tree node enforces reads, at that node,
only `0` and `1` (the binary domain's node `bit`, the fixed field of `x ↦ x²`). -/
def _root_.GordieHowe.RealizedProgram.Interp.BitNodes (I : Interp) (ir : RealizedProgram) : Prop :=
  ∀ v < ir.values.length, (ir.value v).type = .bit → (ir.value v).typeSource = .node →
    ∀ nr, (ir.value v).node = some nr → ∀ x ∈ (I (ir.valueField v)).node nr.name, x = 0 ∨ x = 1

/-- **Where the domains' predicates hold, every field `equal` whose target is no realization's
holds** at the committed assignment of all domains: it is lowered into its domain. -/
theorem holdsWith_of_holds_nonrealized (hv : ir.CellsValid) (hl : ir.Local treeNodes)
    (hadd : ir.BitsBatchAdditive I) (hz : ir.ZeroDecodes I) {x : ir.Valuation I}
    {a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K}
    {r : (ir.layout I).Run} (h : ∀ d : Fin ir.domains.length, (ir.domainOf I d).Holds x (a d) r) :
    ∀ p < ir.predicates.length, ∀ d e e' t, (ir.predicate p).body = .equal d e e' t →
      t.isRealized = false →
        ir.HoldsWith (ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r))
          (ir.predicate p).body := by
  intro pid hpid d e e' t hb ht
  have heq : (ir.predicate pid).body.isEqual = true := by rw [hb]; rfl
  have hown := hv.equal pid hpid (by rw [heq]; rfl)
  rw [realizedOwnB_equal hb ht, Bool.or_false] at hown
  obtain ⟨dd, hd, hlow⟩ := exists_lowered_of_loweredOwnB hown
  exact placedHolds_of_isEqual heq
    ((placedHolds_cellValuation_iff hl a dd hpid hd).1 (placedHolds_of_holds hadd hz (h dd) hlow))

/-- **A realized field equation holds where the domains' predicates do**
(`fieldEq_of_realized`): every field `equal` with no realization target holds
(`holdsWith_of_holds_nonrealized`), the zero constants read `0` (`evalE_leaf_zeroConst`), and the
interpretation follows the registry with lawful integer readings (the root decodes to its cast). -/
theorem fieldEq_of_holds_realized (hv : ir.CellsValid) (hl : ir.Local treeNodes)
    (hadd : ir.BitsBatchAdditive I) (hz : ir.ZeroDecodes I) (hwf : ir.WellFormed)
    (hI : I.Registered ir) {primeNodes : ℕ → List String} (hL : I.Lawful ir primeNodes)
    {x : ir.Valuation I} {a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K}
    {r : (ir.layout I).Run} (h : ∀ d : Fin ir.domains.length, (ir.domainOf I d).Holds x (a d) r)
    {p d : ℕ} {e e' : Expr} (hp : p < ir.predicates.length)
    (hpo : ir.PredOk (ir.predicate p).body)
    (hes : (d, e) ∈ (ir.predicate p).body.exprs) (hes' : (d, e') ∈ (ir.predicate p).body.exprs)
    (hlen : ir.exprLen e' = ir.exprLen e) (hd : d < ir.domains.length) {q : ℕ}
    (hR : ir.RealizedAdmits d e e' q) :
    ∀ i < ir.exprLen e,
      ir.evalWith (ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r)) d e i =
        ir.evalWith (ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r)) d e' i := by
  have hf := domainField_lt hwf hd
  exact fieldEq_of_realized hwf.refsOrdered
    (fun v hv' hfv i => evalE_leaf_zeroConst _ hv' hfv (hz _ hf) i)
    (fun c hc => hL.decode_natCast _ hf c hc) (charP_field hI hf)
    (holdsWith_of_holds_nonrealized hv hl hadd hz h) hR (hpo.1 _ hes).2.shape
    (hpo.1 _ hes').2.shape hlen

/-- **The domains' predicates give the realized program**, at the committed assignment of all
domains: every field `equal` and every `mod_0` is lowered into its domain (`placedHolds_of_holds`:
the equality, the field equation, at the domain's cells, then at all domains' by locality) or
realized through its convolutions' realizations (`fieldEq_of_holds_realized`); every
group's LogUp identity is a realization circuit of a domain (`logupHoldsAt_reader_iff`); every
node-typed value is a cell of its domain, which lies in its base, its type's node (a `Bit` cell's
node is `{0, 1}`, `Interp.BitNodes`), a bit view, whose readings are bits, or a late value whose
message and pad lie in its type's node. `hadd`, `hz`, `hbit`, `hI` and `hL` are properties of the
model; `hwf` is a decided item. -/
theorem realizedAt_of_holds (hv : ir.CellsValid) (hl : ir.Local treeNodes)
    (hadd : ir.BitsBatchAdditive I) (hz : ir.ZeroDecodes I) (hbit : I.BitNodes ir)
    (hwf : ir.WellFormed) (hI : I.Registered ir) {primeNodes : ℕ → List String}
    (hL : I.Lawful ir primeNodes) {x : ir.Valuation I}
    {a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K}
    {r : (ir.layout I).Run} (h : ∀ d : Fin ir.domains.length, (ir.domainOf I d).Holds x (a d) r) :
    ir.Realized I x (ir.ofAllCells I a) r where
  equal p hp heq := by
    obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hp
    have hown := hv.equal pid hpid (by rw [heq]; rfl)
    by_cases hre : ir.realizedOwnB pid = true
    · obtain ⟨d, e, e', t, hb⟩ : ∃ d e e' t, (ir.predicate pid).body = .equal d e e' t := by
        revert heq
        cases (ir.predicate pid).body <;> simp [PredBody.isEqual]
      obtain ⟨hd, q, hR⟩ := realizedAdmits_of_equal hb hre
      have hpo := hwf.predicates _ hp
      rw [hb]
      exact fieldEq_of_holds_realized hv hl hadd hz hwf hI hL h hpid hpo
        (by rw [hb]; simp [PredBody.exprs]) (by rw [hb]; simp [PredBody.exprs])
        (by have := hpo.2; rw [hb] at this; exact this.symm) hd hR
    · rw [Bool.not_eq_true] at hre
      rw [hre, Bool.or_false] at hown
      obtain ⟨d, hd, hlow⟩ := exists_lowered_of_loweredOwnB hown
      exact placedHolds_of_isEqual heq
        ((placedHolds_cellValuation_iff hl a d hpid hd).1 (placedHolds_of_holds hadd hz (h d) hlow))
  integer p hp dd lhs rhs real hb := by
    obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hp
    have hown := hv.equal pid hpid (by rw [hb]; simp [PredBody.isIntEq])
    by_cases hre : ir.realizedOwnB pid = true
    · obtain ⟨hd, q, hR⟩ := realizedAdmits_of_mod hb hre
      have hpo := hwf.predicates _ hp
      exact fieldEq_of_holds_realized hv hl hadd hz hwf hI hL h hpid hpo
        (by rw [hb]; simp [PredBody.exprs]) (by rw [hb]; simp [PredBody.exprs])
        (by have := hpo.2; rw [hb] at this; exact this.symm) hd hR
    · rw [Bool.not_eq_true] at hre
      rw [hre, Bool.or_false] at hown
      obtain ⟨d, hd, hlow⟩ := exists_lowered_of_loweredOwnB hown
      have hl' := (placedHolds_cellValuation_iff hl a d hpid hd).1
        (placedHolds_of_holds hadd hz (h d) hlow)
      rw [hb, placedHolds_mod_zero_iff] at hl'
      exact hl'
  logup t ht g hg := by
    obtain ⟨c, hcd, hc⟩ := exists_logup_of_logupAnyB (hv.logup t ht g hg)
    obtain ⟨v, hnode, hf⟩ := exists_chalNode_of_alphaNodeB (hv.alpha t ht)
    have hcirc : ir.CircuitHolds I c
        (ir.cellValuation I (ir.circuit c).domain x r (a ⟨_, hcd⟩)) :=
      (h ⟨_, hcd⟩).circuit ⟨c, rfl⟩
    exact (ir.logupHoldsAt_reader_iff _ hnode hf).1
      ((logupHoldsAt_cellValuation_iff hl a ⟨_, hcd⟩ rfl hc).1 (hcirc _ hc))
  macH p hp dx x' dy y k real hb hn hbx := by
    obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hp
    have hcov := hv.macH pid hpid
    simp only [macHCoveredB, hb, hn, hbx] at hcov
    obtain ⟨c, hcd, hc⟩ := exists_macH_of_macHAnyB hcov
    have hok := hv.entries c c.2 _ hc
    simp only [entryOkB, Bool.and_eq_true] at hok
    obtain ⟨dx', x'', dy', y', k', real', v, hb', hn', -, hv', hf⟩ := exists_of_macHNodeB hok.2
    rw [hb] at hb'
    cases hb'
    have hcirc : ir.CircuitHolds I c
        (ir.cellValuation I (ir.circuit c).domain x r (a ⟨_, hcd⟩)) :=
      (h ⟨_, hcd⟩).circuit ⟨c, rfl⟩
    exact (macHHolds_reader_iff _ hb hn hv' hf).1
      ((macHHolds_cellValuation_iff hl a ⟨_, hcd⟩ rfl hc).1 (hcirc _ hc))
  types v hv' hsrc i hi := by
    have ho := hv.types v hv' hsrc
    simp only [typeOwnB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ho
    obtain ⟨hdl, (hcellB | hbv) | hlt⟩ := ho
    · set d : Fin ir.domains.length := ⟨(ir.value v).domain, hdl⟩ with hdef
      obtain ⟨hcell, hk, hty⟩ := typeAtCellB_spec hcellB
      have hkey : CellKey.val v i ∈ ir.cellKeys d := (ir.mem_cellKeys_val).2 ⟨hv', hcell, hi⟩
      have hdom : ir.domainField d = ir.valueField v := (ir.isCellValue_valueField hcell).symm
      have hread : ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r) v i =
          castElt (a d ⟨_, hkey⟩) := by
        rw [reader_of_priv _ hk]
        simp only [layoutEnv, ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl),
          (asgAgree_ofAllCells a d).val v rfl, ofCells, hkey, ↓reduceDIte]
      rw [hread]
      have hb := (h d).base ⟨_, hkey⟩
      change a d ⟨_, hkey⟩ ∈ ir.cellBase I d ⟨_, hkey⟩ at hb
      rcases hty with hty | ⟨nr, hnode, hty⟩ | ⟨nr, hnode, hty⟩
      · rw [hty]
        trivial
      · rw [hty]
        simp only [cellBase, hnode] at hb
        exact castElt_mem_node hdom hb
      · rw [hty]
        simp only [cellBase, hnode] at hb
        exact hbit v hv' hty hsrc nr hnode _ (castElt_mem_node hdom hb)
    · -- a bit view
      simp only [bitViewTypeB, Bool.and_eq_true, decide_eq_true_eq] at hbv
      obtain ⟨hk, hty⟩ := hbv
      obtain ⟨w, sel, hkv⟩ : ∃ w sel, (ir.value v).kind = .bits w sel := by
        revert hk
        cases (ir.value v).kind <;> simp
      rw [hty]
      have hread : ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r) v i =
          ir.bitView (ir.read (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r)
            ir.values.length) v w sel i := by
        simp only [reader, fuel, read, hkv]
      rw [hread]
      simp only [bitView, FieldInterp.ofBool]
      split <;> simp [FieldInterp.InType]
    · -- a late value masked over its type's node
      simp only [lateTypeB, Bool.and_eq_true, Bool.not_eq_true'] at hlt
      obtain ⟨⟨hlo, hnc⟩, hmatch⟩ := hlt
      set d : Fin ir.domains.length := ⟨(ir.value v).domain, hdl⟩ with hdef
      obtain ⟨E, hty, hps⟩ : ∃ E, (ir.value v).type = .sub E ∧ (ir.value v).padSpace = .node E := by
        revert hmatch
        split
        · rename_i E E' hty hps
          intro h
          simp only [beq_iff_eq] at h
          subst h
          exact ⟨E, hty, hps⟩
        · simp
      have hlate := ir.isLateOf_isLate hlo
      have hk : (ir.value v).kind = .late := by
        have h1 := hlate.1
        revert h1
        cases (ir.value v).kind <;> simp [Kind.isLate]
      have hkey : CellKey.pad v i ∈ ir.cellKeys d := (ir.mem_cellKeys_pad).2 ⟨hv', hnc, hlo, hi⟩
      have hdom : ir.domainField d = ir.valueField v := (ir.isLateOf_valueField hlo).symm
      rw [reader_of_late _ hk, hty]
      simp only [layoutEnv, if_pos (show v < ir.values.length ∧ ir.IsLate v ∧ i < (ir.value v).size
        from ⟨hv', hlate, hi⟩)]
      have hsp : (I (ir.valueField v)).space (ir.value v).padSpace = (I (ir.valueField v)).node E := by
        rw [hps]
        rfl
      change _ ∈ (I (ir.valueField v)).node E
      rw [← hsp]
      refine AddSubgroup.sub_mem _ ?_ ?_
      · unfold msgRead
        rw [dif_pos ⟨hv', hlate, hi⟩]
        exact ((show ir.Mask I v from r.msg ⟨⟨v, hv'⟩, hlate⟩) ⟨i, hi⟩).2
      · have hpad : (ir.bindAsg (ir.ofAllCells I a)).pad v i = castElt (a d ⟨_, hkey⟩) := by
          simp only [bindAsg, (asgAgree_ofAllCells a d).pad v rfl, ofCells, hkey, ↓reduceDIte]
        rw [hpad]
        have hb := (h d).base ⟨_, hkey⟩
        change a d ⟨_, hkey⟩ ∈ ir.cellBase I d ⟨_, hkey⟩ at hb
        simp only [cellBase] at hb
        exact castElt_mem_space hdom hb

variable (I) in
/-- **The cells lowering**: from the realized program to the predicates of the program's domains
(`RealizedProgram.domainOf`), on their cells, for local domains (`RealizedProgram.Local`). The projection reads
the committed assignment from every domain's cells (`RealizedProgram.ofAllCells`); no event
(`realizedAt_of_holds`). -/
def cellsLowering (hv : ir.CellsValid) (hl : ir.Local treeNodes) (hadd : ir.BitsBatchAdditive I)
    (hz : ir.ZeroDecodes I) (hbit : I.BitNodes ir) (hwf : ir.WellFormed) (hI : I.Registered ir)
    {primeNodes : ℕ → List String} (hL : I.Lawful ir primeNodes) :
    Lowering (ir.layout I) (ir.Realized I)
      (GordieHowe.Domain.lowered fun d : Fin ir.domains.length => ir.domainOf I d) where
  proj a := ir.ofAllCells I a
  event _ _ _ _ := False
  challengeUse _ _ _ _ _ _ := Iff.rfl
  sound _ _ _ h := .inl (realizedAt_of_holds hv hl hadd hz hbit hwf hI hL h)

/-! ## The honest prover -/

variable {primeNodes : ℕ → List String}

/-- **The program's fields decode `0` to `0`** when the interpretation follows the registry and its
integer readings are lawful: a field's characteristic is its Lean field's (`Interp.Registered`),
positive as the field is finite, and a constant below it decodes to its cast
(`Interp.Lawful.decode_natCast` at `0`). -/
theorem _root_.GordieHowe.RealizedProgram.Interp.zeroDecodes_of_lawful {primeNodes : ℕ → List String}
    (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) : ir.ZeroDecodes I := by
  intro f hf
  have hpos : 0 < (ir.field f).characteristic := by
    rw [← hI.characteristic f hf, ← hI.ringChar f hf]
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite (I f).K _)
  rw [hL.decode_natCast f hf 0 hpos, Nat.cast_zero]

end

end GordieHowe.RealizedProgram
