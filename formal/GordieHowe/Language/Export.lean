-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Export

@[expose] public section

/-!
# GordieHowe: the plan data schema

The schema of the generated plan files `GordieHoweCerts/Generated/<Scheme>/<Arm>/<Params>/Plan.lean`. The
C++ writes one such file per configuration from a bench binary: a single `def` of type
`GordieHowe.RealizedProgram.Export.Plan` holding the compiled plan and its parameters. The files hold data only (no proofs,
no tactics). `Plan.Valid` (`GordieHowe/Language/Export/Valid.lean`) states the planner's conditions
on it (admissibility, certificates, needle counts); no theorem reads it and no check certifies it
(`GordieHowe/Applications/Program/Conditions.lean`).

Lists are in the C++ order (declaration order for requests, node-id order for challenges, message
order for messages). Names are the C++ node or constraint names. Sizes are counts and structured
ranges; nothing here is per cell or per needle.

Changing a field's meaning, renaming or removing a field or constructor increments `schemaVersion`;
adding a field with a default does not. From version 2 on, the packing modes are `squaringChain`
and `subfieldMasks` and the Ligero data has no field `A`. From version 3 on, the Ligero data has
the field `ldtReps`, the number of repetitions of the low-degree test (absent means one).

The definitions are in `GordieHoweNative/Language/Export.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram.Export

/-! ## The extended Fiat–Shamir points -/

/-- **The row slots before a domain's first packing stage**: one per GKR layer of its circuits, the
input row (absent for a domain with no circuit, which runs no GKR), its affine rows and two
reduction rows per batch (`TreePlan::stream_rows`, `CompiledDomain::extra_rows`). -/
def Domain.firstSlots (d : Domain) : Nat :=
  (d.circuits.map (·.layers)).sum + (if d.circuits = [] then 0 else 1) +
    (d.affineRows.map (·.2)).sum + 2 * d.batches.length

/-- The inner packing stages: the edges whose parent is not the domain's field, in plan order
(`PackingTree::inner`). -/
def Domain.innerEdges (d : Domain) : List PackingEdge := d.packing.filter (·.parent ≠ d.field.name)

/-- The root's measurements: those of the edges into the domain's field (`TreePlan::root_m`). -/
def Domain.rootMeasurements (d : Domain) : Nat :=
  ((d.packing.filter (·.parent = d.field.name)).map (·.measurements)).sum

/-- **The inner stages with their row slots** from `slots` on: each stage paired with the slots so
far, the bound its combination is extended by; each stage adds its measurements to the slots,
whether or not it combines (`TreePlan::stream_rows`). -/
def stageSlots : List PackingEdge → Nat → List (PackingEdge × Nat)
  | [], _ => []
  | e :: es, slots => (e, slots) :: stageSlots es (slots + e.measurements)

/-- **The rows of the points after the stages**: when the root has children, the root combination
at the slots after every stage and Ligero's linear test at the root's measurements and its combined
row; otherwise Ligero's linear test at every slot (`TreePlan::stream_rows`). -/
def Domain.finalRows (d : Domain) : List Nat :=
  let slots := d.firstSlots + (d.innerEdges.map (·.measurements)).sum
  if d.packing.any (·.parent = d.field.name) then [slots, d.rootMeasurements + 1] else [slots]

/-- **The row slots of the inner stages that open a point**: the slots (`stageSlots`, from
`firstSlots`) of the stages two or more rows are routed to (`routedRows`), in stage order. A stage
that one row reaches runs that row without a weight (`TreePlan::stream_rows`). -/
def Domain.stageRows (d : Domain) : List Nat :=
  ((stageSlots d.innerEdges d.firstSlots).filter (2 ≤ ·.1.routedRows)).map (·.2)

/-- **The rows and length of a point of `n` rows** at the default budget `base` and `kBytes`-byte
field elements: `(n, base + 4 · n · kBytes)` (`extend_point_budget_for(n, F)`). -/
def pointOf (base kBytes n : Nat) : Nat × Nat := (n, base + 4 * n * kBytes)

/-- A domain's extended points as rows and lengths, in transcript order. -/
def Domain.pointRows (d : Domain) : List (Nat × Nat) :=
  d.streamPoints.map fun p => (p.rows, p.streamBytes)

/-- The stage points: the extended points before the last `finalRows.length`. -/
def Domain.stagePoints (d : Domain) : List (Nat × Nat) :=
  d.pointRows.take (d.streamPoints.length - d.finalRows.length)

/-- The final points: the last `finalRows.length` extended points. -/
def Domain.finalPoints (d : Domain) : List (Nat × Nat) :=
  d.pointRows.drop (d.streamPoints.length - d.finalRows.length)

/-- **A domain's extended points follow the C++ rule** (`TreePlan::stream_rows`) at the default
budget `base` and `kBytes`-byte field elements (`pointOf`). The points are, in transcript order, one
point for each inner stage that two or more rows are routed to, at its row slots (`stageRows`), then
the final points at `finalRows`. Every inner stage has a routed row: `TreePlan::route` adds no
measurement rows for a stage with none, and the verifier's measurement count then fails. -/
structure Domain.FollowsStreamRule (d : Domain) (base kBytes : Nat) : Prop where
  /-- Every inner stage has a routed row. -/
  routed : ∀ e ∈ d.innerEdges, 1 ≤ e.routedRows
  /-- The stage points are at `stageRows`. -/
  stages : d.stagePoints = d.stageRows.map (pointOf base kBytes)
  /-- The final points are at `finalRows`. -/
  final : d.finalPoints = d.finalRows.map (pointOf base kBytes)

theorem Domain.followsStreamRule_iff (d : Domain) (base kBytes : Nat) :
    d.FollowsStreamRule base kBytes ↔
      (∀ e ∈ d.innerEdges, 1 ≤ e.routedRows) ∧
      d.stagePoints = d.stageRows.map (pointOf base kBytes) ∧
      d.finalPoints = d.finalRows.map (pointOf base kBytes) :=
  ⟨fun h => ⟨h.routed, h.stages, h.final⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

instance (d : Domain) (base kBytes : Nat) : Decidable (d.FollowsStreamRule base kBytes) :=
  decidable_of_iff _ (d.followsStreamRule_iff base kBytes).symm

/-! ## The packing tree's shape and its edges' realizability -/

/-- **The degree of the domain's masking subfield** `S0` over the prime field: the declared
subfield named `maskingSubfield`, or the field itself (an unpacked domain). -/
def Domain.maskingDegree (d : Domain) : Nat :=
  ((d.subfields.find? (·.name = d.maskingSubfield)).map (·.degree)).getD d.field.degree

/-- **An edge's mode and counts follow the planner's rule** (`tree.h`) for a field of degree `n`
with masking subfield of degree `s0`, in characteristic 2 when `char2`, for a child of degree
`b = childDegree` and relative degree `d = degree`: squaring-chain masks exactly when `char2` and
(`b = 1` or `s0 ∤ b`), with `d` masks and `b · d(d − 1)/2` chain cells; subfield masks otherwise,
which need `s0 ∣ b` (`S0 ⊆ B`), with `d · (n / s0)` masks in the prefix and no chain cell. -/
def PackingEdge.EdgeCounts (n s0 : Nat) (char2 : Bool) (e : PackingEdge) : Prop :=
  match e.mode with
  | .squaringChain => char2 = true ∧ (e.childDegree = 1 ∨ ¬ s0 ∣ e.childDegree) ∧
      e.masks = e.degree ∧ e.chainCells = e.childDegree * (e.degree * (e.degree - 1) / 2)
  | .subfieldMasks => s0 ∣ e.childDegree ∧ ¬ (char2 = true ∧ e.childDegree = 1) ∧
      e.masks = e.degree * (n / s0) ∧ e.chainCells = 0

instance (n s0 : Nat) (char2 : Bool) (e : PackingEdge) : Decidable (e.EdgeCounts n s0 char2) := by
  unfold PackingEdge.EdgeCounts
  split <;> infer_instance

/-- **An edge is realizable** (`tree.h`, the planner's final check): the parent's degree is the
child's times the relative degree and divides the field's, the relative degree is at least 2, the
stage measures once per coordinate of its group, and the mode and counts follow the planner's rule
(`EdgeCounts`). -/
def PackingEdge.Realizable (n s0 : Nat) (char2 : Bool) (e : PackingEdge) : Prop :=
  e.parentDegree = e.childDegree * e.degree ∧ e.parentDegree ∣ n ∧ 2 ≤ e.degree ∧
    e.measurements = e.degree ∧ e.EdgeCounts n s0 char2

instance (n s0 : Nat) (char2 : Bool) (e : PackingEdge) : Decidable (e.Realizable n s0 char2) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- **The domain's edges are realizable** where the exporter writes the degrees
(`childDegree ≠ 0`; the defaults `0` mean not exported). -/
def Domain.EdgesRealizable (d : Domain) : Prop :=
  ∀ e ∈ d.packing, e.childDegree ≠ 0 →
    e.Realizable d.field.degree d.maskingDegree (d.field.characteristic == 2)

instance (d : Domain) : Decidable d.EdgesRealizable :=
  inferInstanceAs (Decidable (∀ e ∈ d.packing, _))

/-- **The packing edges form a tree in processing order** (`tree.h`, `bottom_up`): no edge's child
is the field, each child has one edge, and every parent is the field or the child of a later edge
(children are processed before their parents, deepest first). -/
def Domain.IsTree (d : Domain) : Prop :=
  (∀ e ∈ d.packing, e.child ≠ d.field.name) ∧ (d.packing.map (·.child)).Nodup ∧
    ∀ i : Fin d.packing.length, d.packing[i].parent = d.field.name ∨
      ∃ j : Fin d.packing.length, i < j ∧ d.packing[j].child = d.packing[i].parent

instance (d : Domain) : Decidable d.IsTree :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **A domain's packing is well formed**: its edges form a tree in processing order (`IsTree`) and
every edge with exported degrees is realizable (`EdgesRealizable`). -/
structure Domain.WellFormed (d : Domain) : Prop where
  /-- The edges form a tree in processing order. -/
  isTree : d.IsTree
  /-- Every edge with exported degrees is realizable. -/
  edgesRealizable : d.EdgesRealizable

theorem Domain.wellFormed_iff (d : Domain) : d.WellFormed ↔ d.IsTree ∧ d.EdgesRealizable :=
  ⟨fun h => ⟨h.isTree, h.edgesRealizable⟩, fun h => ⟨h.1, h.2⟩⟩

instance (d : Domain) : Decidable d.WellFormed :=
  decidable_of_iff _ d.wellFormed_iff.symm

end GordieHowe.RealizedProgram.Export
