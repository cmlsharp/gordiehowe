-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check

@[expose] public section

/-!
# GordieHowe: the source part of a realized program

The realized program marks what the compiler introduced (compiler/lowering.h): `Value.role` is
`.source` or `.realization owner`, `Predicate.role` is `.source`, `.realization owner` or `.type v`.
The source program `P₀` of the paper's `thm:backend` is the part of role `source`, read in place
(same identifiers):

* **its values** are the values of role `source` (`GordieHowe.RealizedProgram.IsSourceValue`); a value bound to its
  digits (`Kind.bound`) is a committed source value;
* **its challenges** are the challenges of role `source` (`GordieHowe.RealizedProgram.chalIsSource`, `Challenge.role`):
  the realization challenges (a table's `α`, a MAC key) have role `realization`;
* **its predicates** are those of role `source`, and the type checks of source values
  (`GordieHowe.RealizedProgram.inSource`);
* **its semantics** (`GordieHowe.RealizedProgram.SourceSatAt`): every source predicate holds, and every node-typed
  source value lies in its type.

**Well-formedness of the source part** (`GordieHowe.RealizedProgram.SourceValid`, decided through
`GordieHowe.RealizedProgram.sourceValid_iff`): no challenge is `unmodeled`, and the owner of a realization challenge is
a predicate of the matching kind (a table's `α`: an `in`; any other, the MAC key: a cross-field
`equal`; `GordieHowe.RealizedProgram.chalRoleOk`); source predicates read only source values; a source value is
computed only from source values (the values its definition reads, `GordieHowe.RealizedProgram.valueDeps`; a bound
value is committed in `P₀`, so its expression over the digits is not a read); and a source value
reads from the run only source challenges and source late values (`GordieHowe.RealizedProgram.nodeReads`; a message
reads its late value). Then the source semantics depends only on the statement, the committed
assignment, the source challenges and the source late values (`GordieHowe.RealizedProgram.sourceSatAt_congr`), and the
realized program's semantics gives it (`GordieHowe.RealizedProgram.SatAt.toSource`).
-/

namespace GordieHowe.RealizedProgram

open Export

/-- Whether a predicate body is an `in`. -/
def PredBody.isMem : PredBody → Bool
  | .mem _ _ _ _ => true
  | _ => false

/-- Whether a predicate body is a cross-field `equal`. -/
def PredBody.isCross : PredBody → Bool
  | .cross _ _ _ _ _ _ => true
  | _ => false

section

variable (ir : RealizedProgram)

/-! ## The source part -/

/-- **A value of the source program**: a value of role `source`. -/
def IsSourceValue (v : ℕ) : Prop := (ir.value v).role = .source

instance (v : ℕ) : Decidable (ir.IsSourceValue v) := inferInstanceAs (Decidable (_ = _))

/-- **A challenge of the source program**: a challenge of role `source`. -/
def chalIsSource (j : ℕ) : Bool :=
  decide (j < ir.challenges.length) && (ir.challenge j).role == .source

/-- **The role of challenge `j` is admissible**: not `unmodeled`; the owner of a realization
challenge is a predicate, an `in` for a table's challenge `α` (`alpha:<D>`), a cross-field
`equal` for any other (the MAC key `<mac>.beta`). -/
def chalRoleOk (j : ℕ) : Bool :=
  match (ir.challenge j).role with
  | .source => true
  | .realization o =>
    decide (o < ir.predicates.length) &&
      if ir.tables.any (·.alpha == j) then PredBody.isMem (ir.predicate o).body
      else PredBody.isCross (ir.predicate o).body
  | .unmodeled => false

/-- **A predicate of the source program**: of role `source`, or the type check of a source
value. -/
def inSource (p : Predicate) : Bool :=
  match p.role with
  | .source => true
  | .type v => decide (ir.IsSourceValue v)
  | .realization _ => false

/-- **A read of the source program**: a source challenge, or a source value (a late value). A pad
is never read by a value (`RealizedProgram.nodeReads`). -/
def SourceRead : Read → Prop
  | .chal c => ir.chalIsSource c = true
  | .late u => ir.IsSourceValue u
  | .pad _ => False

instance (rd : Read) : Decidable (ir.SourceRead rd) := by
  cases rd <;> unfold SourceRead <;> infer_instance

/-- **The source part is well formed**: the challenges' roles are admissible; source predicates
read only source values; source values are computed only from source values; source values read
from the run only source challenges and source late values. -/
structure SourceValid : Prop where
  /-- Every challenge's role is admissible. -/
  roles : ∀ j < ir.challenges.length, ir.chalRoleOk j = true
  /-- Source predicates read only source values. -/
  preds : ∀ p ∈ ir.predicates, ir.inSource p = true → ∀ u ∈ ir.predNodes p.body,
    ir.IsSourceValue u
  /-- Source values are computed only from source values. -/
  values : ∀ v < ir.values.length, ir.IsSourceValue v → ∀ u ∈ ir.valueDeps v, ir.IsSourceValue u
  /-- Source values read only source challenges and source late values. -/
  reads : ∀ v < ir.values.length, ir.IsSourceValue v → ∀ rd ∈ ir.nodeReads ir.fuel v,
    ir.SourceRead rd

theorem sourceValid_iff : ir.SourceValid ↔
    (∀ j < ir.challenges.length, ir.chalRoleOk j = true) ∧
    (∀ p ∈ ir.predicates, ir.inSource p = true → ∀ u ∈ ir.predNodes p.body,
      ir.IsSourceValue u) ∧
    (∀ v < ir.values.length, ir.IsSourceValue v → ∀ u ∈ ir.valueDeps v, ir.IsSourceValue u) ∧
    ∀ v < ir.values.length, ir.IsSourceValue v → ∀ rd ∈ ir.nodeReads ir.fuel v,
      ir.SourceRead rd :=
  ⟨fun h => ⟨h.roles, h.preds, h.values, h.reads⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

instance : Decidable ir.SourceValid := decidable_of_iff _ ir.sourceValid_iff.symm

/-! ## The source semantics -/

variable {I : Interp}

/-- **The source program is satisfied in the environment `e`**: every source predicate holds, and
every node-typed source value lies in its type. Unchecked bits (`bit_from_unchecked`) are the
programmer's obligation, discharged in the source program's round-by-round soundness proof.
`SourceSatAt` checks the type sets of node-typed values only, because the proof system cannot extract an
unchecked value inside its type set. It coincides with the paper's accepting assignment
(`def:o-semantics`) when the program has no unchecked values, as every paper program does; the
completeness proof's obligation, with every source value in its type, is `SourceAcceptingAt`. -/
structure SourceSatAt (e : ir.Env I) : Prop where
  /-- Every source predicate holds. -/
  preds : ∀ p ∈ ir.predicates, ir.inSource p = true → ir.HoldsAt e p.body
  /-- Every node-typed source value lies in its type. -/
  types : ∀ v < ir.values.length, ir.IsSourceValue v → (ir.value v).typeSource = .node →
    ∀ i < (ir.value v).size, (I (ir.valueField v)).InType (ir.value v).type (ir.reader e v i)

theorem sourceSatAt_iff (e : ir.Env I) : ir.SourceSatAt e ↔
    (∀ p ∈ ir.predicates, ir.inSource p = true → ir.HoldsAt e p.body) ∧
      ∀ v < ir.values.length, ir.IsSourceValue v → (ir.value v).typeSource = .node →
        ∀ i < (ir.value v).size, (I (ir.valueField v)).InType (ir.value v).type (ir.reader e v i) :=
  ⟨fun h => ⟨h.preds, h.types⟩, fun h => ⟨h.1, h.2⟩⟩

instance (e : ir.Env I) : Decidable (ir.SourceSatAt e) :=
  decidable_of_iff _ (ir.sourceSatAt_iff e).symm

variable {ir}

/-- **The realized program's semantics gives the source program's.** -/
theorem SatAt.toSource {e : ir.Env I} (h : ir.SatAt e) : ir.SourceSatAt e where
  preds p hp _ := h.preds p hp
  types v hv _ ht i hi := h.types v hv ht i hi

/-- **Two environments agree on the source program's reads**: one statement, one committed
assignment, the same source challenges and the same source late values. -/
structure Env.AgreeOnSource (e e' : ir.Env I) : Prop where
  /-- The statements agree. -/
  stmt : e.stmt = e'.stmt
  /-- The committed assignments agree. -/
  asg : e.asg = e'.asg
  /-- The source challenges agree. -/
  chal : ∀ c, ir.chalIsSource c = true → e.chal c = e'.chal c
  /-- The source late values agree. -/
  late : ∀ u, ir.IsSourceValue u → e.late u = e'.late u

/-- **Environments agreeing on the source reads agree on what a source value reads.** -/
theorem Env.AgreeOnSource.agreeOn (hs : ir.SourceValid) {e e' : ir.Env I}
    (h : Env.AgreeOnSource e e') {v : ℕ} (hv : ir.IsSourceValue v) :
    Env.AgreeOn (ir.nodeReads ir.fuel v) e e' := by
  by_cases hl : v < ir.values.length
  · refine ⟨h.stmt, h.asg, fun c hc => h.chal c (hs.reads v hl hv _ hc),
      fun u hu => h.late u (hs.reads v hl hv _ hu)⟩
  · rw [nodeReads_of_le (Nat.le_of_not_lt hl)]
    exact ⟨h.stmt, h.asg, fun _ hc => (nomatch hc), fun _ hu => (nomatch hu)⟩

/-- **The source semantics depends only on the source reads** (`SourceValid`). -/
theorem sourceSatAt_congr (hs : ir.SourceValid) {e e' : ir.Env I}
    (h : Env.AgreeOnSource e e') : ir.SourceSatAt e ↔ ir.SourceSatAt e' := by
  have hp : ∀ p ∈ ir.predicates, ir.inSource p = true →
      (ir.HoldsAt e p.body ↔ ir.HoldsAt e' p.body) :=
    fun p hp hsrc => holdsAt_congr <| by
      refine ⟨h.stmt, h.asg, fun c hc => ?_, fun u hu => ?_⟩
      · obtain ⟨w, hw, hc⟩ := List.mem_flatMap.1 hc
        exact (h.agreeOn hs (hs.preds p hp hsrc w hw)).chal c hc
      · obtain ⟨w, hw, hu⟩ := List.mem_flatMap.1 hu
        exact (h.agreeOn hs (hs.preds p hp hsrc w hw)).late u hu
  have hr : ∀ v, ir.IsSourceValue v → ir.reader e v = ir.reader e' v :=
    fun v hv => read_congr _ v (h.agreeOn hs hv)
  rw [sourceSatAt_iff, sourceSatAt_iff]
  refine and_congr (forall₂_congr fun p hp' => forall_congr' fun hsrc => hp p hp' hsrc) ?_
  refine forall₂_congr fun v _ => forall_congr' fun hv => ?_
  rw [hr v hv]

end

end GordieHowe.RealizedProgram
