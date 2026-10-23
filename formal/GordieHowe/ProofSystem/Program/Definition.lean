-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldModel
public import GordieHowe.Language.Realizations.Derivation.Lowering
public import GordieHowe.Model.IOP.ExtractorMap

@[expose] public section

/-!
# GordieHowe: the proof system of a program

The plan-level theorem's assembly: the source protocol `Π_P₀` of a program (its part of role
`source`, `GordieHowe/Language/RealizedProgram/Source.lean`, `GordieHowe/Language/RealizedProgram/Protocol.lean`) compiled to a
multi-circuit IOP (`MultiCircuitIOP`) on the realized program's layout, the lowered system of the
GordieHowe core (`GordieHowe/ProofSystem/Program/System.lean`).

**The proof system** (`RealizedProgram.ProofSystem P ir I`): the program's checks (`GordieHowe.RealizedProgram.Checks`, decided: the
plan `P` with its realized program `ir` valid, `GordieHowe.RealizedProgram.Valid`; the realization condition,
`GordieHowe.RealizedProgram.Derivable`; the well-formed source part, `GordieHowe.RealizedProgram.SourceValid`; the cells checks,
`GordieHowe.RealizedProgram.CellsValid`; the locality of the domains, `GordieHowe.RealizedProgram.Local`), the model of the interpretation
(`Interp.Model`, `GordieHowe/ProofSystem/Program/FieldModel.lean`: the registry, lawful integer readings at the
plan's prime-subfield nodes, the MAC fields, linear readings in the fields of the field-form
`mod_q`s, additive bit coordinates, `Bit` nodes read as `{0, 1}`, the opaque ranges; from the models
of the fields and decided checks of the program, `Interp.Model.of_models`), the GKR sources of the
program's circuits (`src`), and every committing domain's circuit proof with its soundness. A
domain's circuit proof is a `DomainProof` of the domain's predicate under the compiler trust
(`Domain.guard`: the predicate holds when `CircuitsEnforce` does), so the protocol, its verifier,
its honest prover and its simulator are defined without the trust bundle; the soundness theorem's
cells lowering unguards the domains with it (`GordieHowe.RealizedProgram.ProofSystem.cellsLowering`). The tree data of a domain is
the domain proof's: the proof system reads the domain proofs through the `DomainProof` interface.

**The multi-circuit IOP at a lowering** (`RealizedProgram.ProofSystem.iopOf Lw`): the system with the layout
`ir.layout I`, the program's domains (`GordieHowe.RealizedProgram.domainOf`) under the compiler trust, the statement
check `GordieHowe.RealizedProgram.stmtOk` (the program's member checks, made by the verifier before anything else), the
domain proofs and the lowering `Lw` of the relation at the statements that pass the check
(`Constraint.guard`), built directly: `Lw` with the check (`Lowering.check`) enforced by the
domain proofs (`GordieHowe.RealizedProgram.ProofSystem.enforcement`) as the application phase.

* **The protocol** (`GordieHowe.RealizedProgram.ProofSystem.protocol`, `GordieHowe.RealizedProgram.ProofSystem.verifier`, `GordieHowe.RealizedProgram.ProofSystem.iop`): `iopOf` at a lowering
  of `Set.univ` with no event (`GordieHowe.RealizedProgram.ProofSystem.baseLowering`), so it reads no soundness data.
* **The soundness IOP** (`GordieHowe.RealizedProgram.ProofSystem.soundIOP` in `GordieHowe/ProofSystem/Program/Errors.lean`): for round-by-round
  knowledge soundness `h` of `Π_P₀` for `rel` at `RealizedProgram.sourceExtractor proj`, `iopOf` at the
  lowering of `{(x, g) | (x, g x) ∈ rel}` (`GordieHowe.RealizedProgram.ProofSystem.relOf`, witnesses read from the statement, since
  a lowering's projection reads the committed assignment only) to the domains: the cells lowering
  under the trust bundle `T` after the realization step from the source program
  (`GordieHowe.RealizedProgram.ProofSystem.realizeSource`: its events are the realization events at the realization challenges)
  after `Π_P₀`'s events (`GordieHowe.RealizedProgram.loweringOfRbr`) (`GordieHowe.RealizedProgram.ProofSystem.lowering`). Its verifier is the
  protocol's (`verifier_eq`, by `rfl`).
* **The extractor** (`GordieHowe.RealizedProgram.ProofSystem.extractor`): the extractor of `iopOf` at `baseLowering proj`, which is
  the soundness IOP's (`extractor_eq`, by `rfl`), followed by `g ↦ g x`: `proj` at the realized
  assignment of every domain's committed cells (`GordieHowe.RealizedProgram.ofAllCells`, `GordieHowe.RealizedProgram.bindAsg`: a value
  bound to its digits read through them), the committed assignment `Π_P₀` reads.

The two lowerings are irreducible: the unifier compares the soundness IOP with the protocol field by
field, and an unfoldable lowering makes every failed comparison of their application phases expand
both composites.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

section

/-- **The checks of a program** `ir` of the plan `P`, with the opaque ranges `orng` (decided per
program): the plan with its program is valid, the realization condition
(`RealizedProgram.Derivable`: the realization step has valid derivations at the value ranges: the
declared statement bounds `declaredRanges`, which the verifier checks, and the opaque ranges), the
source
part is well formed, the cells checks (the committing domains enforce the realized program), and
every domain's constraints read only its domain (`RealizedProgram.Local`). -/
structure Checks (P : Export.Plan) (ir : RealizedProgram) (orng : List (ℕ × ℕ)) : Prop where
  /-- The plan with its realized program is valid. -/
  valid : RealizedProgram.Valid P ir
  /-- `RealizedProgram.Derivable`: the realization step has valid derivations at the value ranges. -/
  realization : ir.Derivable (primeNodesOf P ir) (ir.declaredRanges ++ orng)
  /-- The source part is well formed. -/
  source : ir.SourceValid
  /-- The cells checks: the committing domains enforce the realized program. -/
  cells : ir.CellsValid
  /-- Every domain's constraints read only its domain. -/
  locality : ir.Local (treeNodesOf P ir)

/-! ## The protocol of the domain proofs

The protocol, its verifier and its extractor read the proof system only through the GKR sources and the
domain proofs, so they are defined on those (`RealizedProgram.iopOfProofs`, `RealizedProgram.extractorOfProofs`),
and the proof system's (`ProofSystem.iopOf`, `ProofSystem.extractor`) are these at the proof system's sources and
proofs. A proof system also carries the domain proofs' soundness, whose errors are real numbers; the
extractor at a concrete proof system is computable as `extractorOfProofs` at its proofs. -/

section OfProofs

variable {ir : RealizedProgram} {I : Interp} (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)

/-- **The domains under the compiler trust** at the GKR sources `src`: every domain's predicate
guarded by `CircuitsEnforce`. -/
abbrev guardedDomainOf (d : Fin ir.domains.length) :
    GordieHowe.Domain (ir.layout I) (ir.Valuation I) :=
  (ir.domainOf I d).guard (ir.CircuitsEnforce I src)

/-- **The domain proofs of a program** at the GKR sources `src`: every domain's circuit proof of
its predicate under the compiler trust. -/
abbrev DomainProofs : Type 1 :=
  ∀ d : Fin ir.domains.length, DomainProof (ir.layout I) (ir.Valuation I) (guardedDomainOf src d)

variable {src} (proof : DomainProofs src)

/-- **The domain proofs enforce the statement check and the domains' predicates under the
compiler trust** (as `ProofSystem.enforcement`). -/
def enforcementOf : Enforcement
    (Constraint.and (Constraint.check (ir.stmtOk I))
      (GordieHowe.Domain.lowered (guardedDomainOf src)))
    (fun d => (proof d).Pub) (fun d => (proof d).Wit) fun d => (proof d).holds where
  ok x _ := ir.stmtOk I x
  pub d x r := (proof d).pub x r
  decode w d := (proof d).decode (w d)
  enforce x w r hok hw := ⟨hok, fun d => (proof d).enforce x r (w d) (hw d)⟩

/-- **The multi-circuit IOP of the domain proofs at the lowering `Lw`** (as `ProofSystem.iopOf`). `hm`:
the program has a domain. -/
def iopOfProofs (hm : ir.domains.length ≠ 0) {W : Type} {rel : Set (ir.Valuation I × W)}
    (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
      (GordieHowe.Domain.lowered (guardedDomainOf src))) :
    MultiCircuitIOP (ir.Valuation I) W rel where
  m := ir.domains.length
  neZero := ⟨hm⟩
  Pub d := (proof d).Pub
  Wit d := (proof d).Wit
  holds d := (proof d).holds
  circuit d := (proof d).proof
  app := ((Lw.check (ir.stmtOk I)).toPhased (enforcementOf proof)).toAppPhase

variable (src) in
/-- **The lowering at the projection `proj`** (as `ProofSystem.baseLowering`): the relation `Set.univ`,
no event; the projection reads the committed assignment from every domain's cells and applies
`proj`. -/
@[irreducible] def baseLoweringOf {W : Type} (proj : ir.Valuation I → ir.Assignment I → W) :
    Lowering (ir.layout I)
      (Constraint.guard (ir.stmtOk I)
        (Constraint.ofRel (Set.univ : Set (ir.Valuation I × (ir.Valuation I → W)))))
      (GordieHowe.Domain.lowered (guardedDomainOf src)) where
  proj a x := proj x (ir.bindAsg (ir.ofAllCells I a))
  event _ _ _ _ := False
  challengeUse _ _ _ _ _ _ := Iff.rfl
  sound _ _ _ _ := .inl (Constraint.guard_of fun _ => Set.mem_univ _)

/-- **The extractor of the domain proofs at the projection `proj`** (as `ProofSystem.extractor`): the
extractor of `iopOfProofs` at `baseLoweringOf proj`, applied to the statement.

Running time: the multi-circuit IOP's extractor (`MultiCircuitIOP.extractor`: one call of every
domain proof's `cp.extract` and `readout`), one decoding of the committed assignment from the cells
(`RealizedProgram.ofAllCells`, one copy per cell), one call of `proj` and its application to the statement;
polynomial when `proj` is. This running time is argued here, not proved in Lean. -/
def extractorOfProofs (hm : ir.domains.length ≠ 0) {W : Type} [Inhabited W]
    (proj : ir.Valuation I → ir.Assignment I → W) :
    Extractor (iopOfProofs proof hm (baseLoweringOf src proj)).spec (ir.Valuation I) W :=
  (iopOfProofs proof hm (baseLoweringOf src proj)).extractor.mapWit fun x g => g x

end OfProofs

/-- **The proof system of a program** (see the module docstring): the program's checks, the model of the
interpretation, the GKR sources of the program's circuits, and every domain's circuit proof of the
domain's predicate under the compiler trust `CircuitsEnforce` at those sources. The domain proofs'
soundness is `ProofSystem.Sound`, apart from this data. -/
structure ProofSystem (P : Export.Plan) (ir : RealizedProgram) (I : Interp) where
  /-- **The ranges of the opaque functions** that the values' intervals read
  (`RealizedProgram.OpaqueRanges`: `(value, bound)` for opaque values computed from the statement whose
  functions return naturals below the bound, the C++ operators' entry bounds); empty for a program
  whose realization reads none. -/
  opaqueRanges : List (ℕ × ℕ) := []
  /-- The program's checks. -/
  checks : ir.Checks P opaqueRanges
  /-- The model of the interpretation. -/
  model : I.Model P ir opaqueRanges
  /-- The GKR sources of the program's circuits. -/
  src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c
  /-- Every domain's circuit proof, of the domain's predicate under the compiler trust. -/
  proof : ∀ d : Fin ir.domains.length, DomainProof (ir.layout I) (ir.Valuation I)
    ((ir.domainOf I d).guard (ir.CircuitsEnforce I src))

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp} (B : ir.ProofSystem P I)

/-- **The soundness of a proof system's domain proofs**: every domain proof's soundness (its errors
and their bounds), a structure over the proof system's data. -/
abbrev Sound : Type := ∀ d, (B.proof d).proof.Sound

/-! ## The checks and the model -/

/-- The plan with its realized program is valid. -/
theorem valid (B : ir.ProofSystem P I) : RealizedProgram.Valid P ir := B.checks.valid

/-- `RealizedProgram.Derivable`: the realization step has valid derivations at the value ranges. -/
theorem realization :
    ir.Derivable (primeNodesOf P ir) (ir.declaredRanges ++ B.opaqueRanges) :=
  B.checks.realization

/-- The source part is well formed. -/
theorem source (B : ir.ProofSystem P I) : ir.SourceValid := B.checks.source

/-- The cells checks. -/
theorem cells (B : ir.ProofSystem P I) : ir.CellsValid := B.checks.cells

/-- Every domain's constraints read only its domain. -/
theorem locality (B : ir.ProofSystem P I) : ir.Local (treeNodesOf P ir) := B.checks.locality

/-- The interpretation follows the registry. -/
theorem registered (B : ir.ProofSystem P I) : I.Registered ir := B.model.registered

/-- The integer readings of the fields are lawful at the plan's prime-subfield nodes. -/
theorem lawful (B : ir.ProofSystem P I) : I.Lawful ir (primeNodesOf P ir) := B.model.lawful

/-- The MAC fields have polynomial bases and the MAC targets' bits are their arguments' bits. -/
theorem macModel (B : ir.ProofSystem P I) : I.MacModel ir := B.model.macModel

/-- The fields of the field-form `mod_q`s have linear integer readings. -/
theorem fieldForm (B : ir.ProofSystem P I) : I.FieldFormModel ir := B.model.fieldForm

/-- The fields of the domains with batches on bits have additive bit coordinates. -/
theorem bitsAdditive (B : ir.ProofSystem P I) : ir.BitsBatchAdditive I := B.model.bitsAdditive

/-- The program's fields decode `0` to `0` (from the model, `Interp.Model.zeroDecodes`). -/
theorem zeroDecodes (B : ir.ProofSystem P I) : ir.ZeroDecodes I := B.model.zeroDecodes

/-- The nodes of the node-typed `Bit` values are `{0, 1}`. -/
theorem bitNodes (B : ir.ProofSystem P I) : I.BitNodes ir := B.model.bitNodes

/-- The opaque functions have the ranges `opaqueRanges`. -/
theorem opaqueModel : ir.OpaqueRanges I B.opaqueRanges := B.model.opaqueModel

/-- **Trust base: the program's GKR circuits enforce their entries** at the proof system's sources. -/
abbrev CircuitsEnforce : Prop := ir.CircuitsEnforce I B.src

/-- **Trust base, honest prover: the program's GKR circuits accept honest inputs** at the proof system's
sources. -/
abbrev CircuitsAccept : Prop := ir.CircuitsAccept I B.src

/-- The program has a domain. -/
theorem domains_ne_zero (B : ir.ProofSystem P I) : ir.domains.length ≠ 0 :=
  B.cells.nonempty

/-- **The domains of the protocol**: every domain's predicate under the compiler trust. -/
abbrev guardedDomain (d : Fin ir.domains.length) :
    GordieHowe.Domain (ir.layout I) (ir.Valuation I) :=
  (ir.domainOf I d).guard B.CircuitsEnforce

/-! ## The protocol -/

/-- **The domain proofs enforce the statement check and the domains' predicates under the
compiler trust**: the verifier's check `RealizedProgram.stmtOk` (the program's member checks), every domain
proof's public input, every domain's cells decoded from its proof's witness
(`DomainProof.enforce`); `RealizedProgram.enforcementOf` at the proof system's proofs. -/
abbrev enforcement : Enforcement
    (Constraint.and (Constraint.check (ir.stmtOk I)) (GordieHowe.Domain.lowered B.guardedDomain))
    (fun d => (B.proof d).Pub) (fun d => (B.proof d).Wit) fun d => (B.proof d).holds :=
  enforcementOf B.proof

/-- **The multi-circuit IOP at the lowering `Lw`** of a relation, at the statements that pass the
member checks (`Constraint.guard`), to the domains' predicates under the compiler trust: the domain
proofs, and `Lw` with the statement check (`Lowering.check`) enforced by them as the application
phase (`Lowering.toPhased`, `Phased.toAppPhase`); `RealizedProgram.iopOfProofs` at the proof system's proofs. Its
rounds are the commitment round, every domain's commit rounds, the program's phases (each a
challenge round and a message round), then every domain proof's reductions and opening. -/
abbrev iopOf {W : Type} {rel : Set (ir.Valuation I × W)}
    (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
      (GordieHowe.Domain.lowered B.guardedDomain)) :
    MultiCircuitIOP (ir.Valuation I) W rel :=
  iopOfProofs B.proof B.domains_ne_zero Lw

/-- **The lowering of the protocol at the projection `proj`**: the relation `Set.univ`, so no event
and no soundness data; the projection reads the committed assignment from every domain's cells
(`RealizedProgram.ofAllCells`) and applies `proj` (`RealizedProgram.baseLoweringOf` at the proof system's sources). The
protocol's verifier and honest prover do not read the lowering; its extractor reads the projection
(`extractor`). -/
abbrev baseLowering {W : Type} (proj : ir.Valuation I → ir.Assignment I → W) :
    Lowering (ir.layout I)
      (Constraint.guard (ir.stmtOk I)
        (Constraint.ofRel (Set.univ : Set (ir.Valuation I × (ir.Valuation I → W)))))
      (GordieHowe.Domain.lowered B.guardedDomain) :=
  baseLoweringOf B.src proj

/-- **The multi-circuit IOP of the protocol at the projection `proj`**. -/
abbrev iopAt {W : Type} (proj : ir.Valuation I → ir.Assignment I → W) :
    MultiCircuitIOP (ir.Valuation I) (ir.Valuation I → W) Set.univ :=
  B.iopOf (B.baseLowering proj)

/-- **The protocol**: the commitment round, every domain's commit rounds, the program's phases (each
a challenge round and a message round), every domain proof's reductions and opening. -/
abbrev protocol : MultiCircuitIOP (ir.Valuation I) (ir.Valuation I → Unit) Set.univ :=
  B.iopAt fun _ _ => ()

/-- The protocol's rounds. -/
abbrev spec : ProtocolSpec B.protocol.n := B.protocol.spec

/-- **The protocol's verifier**: the statement check (`RealizedProgram.stmtOk`), then every domain proof's
verdict on its public input, read from the statement and the run. -/
abbrev verifier : Verifier B.spec (ir.Valuation I) := B.protocol.verifier

/-- **The protocol as an IOP**: the verifier reading the round-`0` commitments at the queried
leaves and every other message in full. -/
abbrev iop : IOP.IOP B.spec (ir.Valuation I) := B.protocol.iop

/-- **The extractor of the proof system** at the projection `proj`: the extractor of the multi-circuit
IOP at `proj` (every domain's cells read from its commit phase and decoded, the committed assignment
read from every domain's cells, `proj` applied: a function of the statement), applied to the
statement (`Extractor.mapWit`); `RealizedProgram.extractorOfProofs` at the proof system's proofs.

Running time: that of `RealizedProgram.extractorOfProofs`. This running time is argued here, not proved in
Lean. -/
abbrev extractor {W : Type} [Inhabited W] (proj : ir.Valuation I → ir.Assignment I → W) :
    Extractor B.spec (ir.Valuation I) W :=
  extractorOfProofs B.proof B.domains_ne_zero proj

/-! ## The lowering of the soundness theorem -/

variable {W : Type} {rel : Set (ir.Valuation I × W)} {proj : ir.Valuation I → ir.Assignment I → W}
  {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}

/-- **The relation of the soundness theorem**: `rel` on the witness read from the statement. -/
abbrev relOf (rel : Set (ir.Valuation I × W)) : Set (ir.Valuation I × (ir.Valuation I → W)) :=
  {p | (p.1, p.2 p.1) ∈ rel}

/-- **The cells lowering under the compiler trust `T`**: the cells lowering
(`RealizedProgram.cellsLowering`, at the domains' locality) to the domains under the trust, which `T`
unguards (`Domain.holds_guard_iff`). Same projection; no event. -/
def cellsLowering (T : B.CircuitsEnforce) :
    Lowering (ir.layout I) (ir.Realized I) (GordieHowe.Domain.lowered B.guardedDomain) where
  proj := (ir.cellsLowering I B.cells B.locality B.bitsAdditive B.zeroDecodes B.bitNodes
      B.valid.program.wellFormed B.registered B.lawful).proj
  event _ _ _ _ := False
  challengeUse _ _ _ _ _ _ := Iff.rfl
  sound x a r h :=
    (ir.cellsLowering I B.cells B.locality B.bitsAdditive B.zeroDecodes B.bitNodes
      B.valid.program.wellFormed B.registered B.lawful).sound x a r
      fun d => GordieHowe.Domain.holds_guard_iff.1 (h d) T

/-- **The realization step from the source program**: the realization step
(`RealizedProgram.realizeLowering_of_derivable`), its source constraint weakened from the realized program's predicates
to the source program's (`RealizedProgram.Pred.toSource`). Same projection (`RealizedProgram.bindAsg`) and
events. -/
def realizeSource :
    Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (ir.SourcePred I)) (ir.Realized I) :=
  (ir.realizeLowering_of_derivable I B.valid.program.wellFormed B.realization B.registered B.lawful
    B.macModel B.opaqueModel).weaken
    fun _ _ _ h => Constraint.guard_of fun hok => Pred.toSource (Constraint.guard_of_check hok h)

/-- **The realization step from the source program has the realization step's errors.** -/
theorem eventBound_realizeSource :
    B.realizeSource.EventBound fun k => ∑ jj : ir.ChalAt k, ir.realError I jj.1 :=
  Lowering.eventBound_weaken (eventBound_realizeLowering_of_derivable _ _ _ _ _ _ _)

/-- **The cells lowering under the trust adds no error.** -/
theorem eventBound_cellsLowering (T : B.CircuitsEnforce) : (B.cellsLowering T).EventBound 0 :=
  Lowering.eventBound_of_not_event fun _ _ _ _ h => h

/-- **`Π_P₀`'s events at the admissible statements** (`RealizedProgram.loweringOfRbr`): the same
projection and events, to the source program at the statements that pass the verifier's check. -/
def rbrRanged (hS : ir.SourceRbr I rel proj S) :
    Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel (relOf rel)))
      (Constraint.guard (ir.stmtOk I) (ir.SourcePred I)) where
  proj := (ir.loweringOfRbr I B.source proj S hS).proj
  event := (ir.loweringOfRbr I B.source proj S hS).event
  challengeUse := (ir.loweringOfRbr I B.source proj S hS).challengeUse
  sound x a r ht := by
    by_cases hok : ir.stmtOk I x = true
    · exact (ir.loweringOfRbr I B.source proj S hS).sound x a r
        (Constraint.guard_of_check hok ht)
    · exact Or.inl (Constraint.guard_of fun h' => absurd h' hok)

/-- **`Π_P₀`'s events at the admissible statements have `Π_P₀`'s errors.** -/
theorem eventBound_rbrRanged (hS : ir.SourceRbr I rel proj S) {δ : Fin ir.phases → ℝ≥0}
    (hδ : (ir.loweringOfRbr I B.source proj S hS).EventBound δ) :
    (B.rbrRanged hS).EventBound δ :=
  hδ

/-- **The lowering of the soundness theorem**, from the relation at the admissible statements
(`stmtOk`: the member checks and the declared bounds): the cells lowering under the compiler trust `T` after the realization step from the
source program after `Π_P₀`'s events, at round-by-round knowledge soundness of `Π_P₀` with no error
at `γ_end` (`hS`). -/
@[irreducible] def lowering (T : B.CircuitsEnforce) (hS : ir.SourceRbr I rel proj S) :
    Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel (relOf rel)))
      (GordieHowe.Domain.lowered B.guardedDomain) :=
  (B.cellsLowering T).comp (B.realizeSource.comp (B.rbrRanged hS))

/-- **The lowering of the soundness theorem is the composite.** -/
theorem lowering_eq (T : B.CircuitsEnforce) (hS : ir.SourceRbr I rel proj S) :
    B.lowering T hS = (B.cellsLowering T).comp (B.realizeSource.comp (B.rbrRanged hS)) := by
  unfold lowering
  rfl

/-- **The multi-circuit IOP of the soundness theorem**: `iopOf` at `lowering`. -/
abbrev soundIOP (T : B.CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    MultiCircuitIOP (ir.Valuation I) (ir.Valuation I → W) (relOf rel) :=
  B.iopOf (B.lowering T ⟨ε, h, hend⟩)

/-- **The soundness IOP's verifier is the protocol's.** -/
theorem verifier_eq (T : B.CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    (B.soundIOP T h hend).verifier = B.verifier :=
  rfl

/-- **The soundness IOP's extractor is the protocol's at `proj`.** -/
theorem extractor_eq [Inhabited W] (T : B.CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    (B.soundIOP T h hend).extractor = (B.iopAt proj).extractor := by
  unfold soundIOP iopAt lowering baseLowering baseLoweringOf
  rfl

end ProofSystem

end

end GordieHowe.RealizedProgram
