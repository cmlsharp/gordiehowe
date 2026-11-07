-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Data
public import GordieHoweNative.Language.PackingDesc
public import GordieHoweNative.Language.RealizedProgram.WithPlan
public import GordieHoweNative.Language.RealizedProgram.Structure
public import GordieHoweNative.Language.RealizedProgram.Annotations
public import GordieHoweNative.Language.Realizations.Derivation.Basic
public import GordieHoweNative.Language.Completeness.Deriv
public import GordieHoweNative.Language.Completeness.Basic
public import GordieHoweNative.ProofSystem.Program.Figures
public import GordieHoweNative.Language.RealizedProgram.Shapes
public import GordieHoweNative.Language.RealizedProgram.SourceRoles
public import GordieHoweNative.Language.Realizations.SelectionCheck

/-!
# GordieHowe: a program's data

`ProgramData`: everything the compiler emits about one program: its computational inputs
(`RuntimeInputs`: the realized program, its plan, the field table, the tableaus and the figures;
`CompletionInputs`: the structure records and the completion certificate), and the witnesses only
its check reads (the hints, the GKR certificates, the shapes, and an optional source-role table).
Each
program's value is a constructor literal of named constants
(`GordieHowe.Generated.<App>.<Params>.data`), so each projection is one unfolding and one
projection step.

The field table, the figures and the shapes (the kinds and body parts of the values and predicates
the application frontends name, `RealizedProgram.ShapeClaim`) are small data. Every type the proof system states per domain or
per circuit is computed from the field table (`FieldTable.interp`, `FieldTable.domainField`) and
the field registry (`GordieHowe/Applications/FieldInterps/Registry.lean`), never from `program` or
`plan`.

The program's check, its parts' soundness and the conditions they give are library code in
`GordieHowe`.
-/

@[expose] public section

namespace GordieHowe

open RealizedProgram

/-! ## Descriptors -/

/-- **The fields the library interprets**, one per Lean field of the registry
(`GordieHowe/Applications/FieldInterps/Registry.lean`, `FieldKey.interp`). -/
inductive FieldKey where
  /-- `GF(2^128)` (`RealizedProgram.gf128`). -/
  | gf128
  /-- `GF(2^256)` (`RealizedProgram.gf256`). -/
  | gf256
  /-- `F_q^6`, `q = 8380417` (`RealizedProgram.fq6`). -/
  | fq6
  /-- `F_q^9`, `q = 12289` (`RealizedProgram.fq9`). -/
  | fq9
  /-- `F_q^11`, `q = 8380417` (`RealizedProgram.fq11`). -/
  | fq11
  /-- `F_q^20`, `q = 12289` (`RealizedProgram.fq20`). -/
  | fq20
  /-- Goldilocks² (`RealizedProgram.gold2`). -/
  | gold2
  /-- Goldilocks⁴ (`RealizedProgram.gold4`). -/
  | gold4
  /-- The P-256 base field (`RealizedProgram.p256`). -/
  | p256
  deriving DecidableEq, Repr, Inhabited

/-- **The opaque-function sets**: the meaning of a program's opaque public values, named by the
plan. -/
inductive OpaqueKey where
  /-- Every opaque value takes no argument: the function is `0`. -/
  | none
  /-- `mac.target_bits` (`RealizedProgram.targetBitsFn`). -/
  | targetBits
  /-- Falcon's opaque functions (`RealizedProgram.falconOps`). -/
  | falcon
  /-- mDL's opaque functions (`RealizedProgram.mdocOps`). -/
  | mdoc
  deriving DecidableEq, Repr, Inhabited

/-- **The plan's name of an opaque-function set** (`Export.Plan.opaqueSet`). -/
@[reducible] def OpaqueKey.name : OpaqueKey → String
  | .none => "none"
  | .targetBits => "targetBits"
  | .falcon => "falcon"
  | .mdoc => "mdoc"

/-- **The shape of a program's interpretation**: one field for every field identifier (`one`), or
field `0` and one field for every other identifier (`two`, `Interp.twoField`), with the
opaque-function set. -/
inductive InterpDesc where
  /-- Field `k` for every identifier. -/
  | one (k : FieldKey) (o : OpaqueKey)
  /-- Field `k0` for identifier `0`, `k1` for every other. -/
  | two (k0 k1 : FieldKey) (o : OpaqueKey)
  deriving DecidableEq, Repr, Inhabited

/-- **The descriptor's opaque-function set.** -/
@[reducible] def InterpDesc.opaque : InterpDesc → OpaqueKey
  | .one _ o => o
  | .two _ _ o => o

/-- **The key of field identifier `f`**: `one`'s key, or `two`'s first key at `0` and its second
key elsewhere. -/
@[reducible] def InterpDesc.key : InterpDesc → Nat → FieldKey
  | .one k _, _ => k
  | .two k0 _ _, 0 => k0
  | .two _ k1 _, _ + 1 => k1

/-- **Entry `i` of a short list of naturals**, `0` past its end: structural and reducible, so on a
literal list and a literal index it reduces at reducible transparency. -/
@[reducible] def nthOr : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, n + 1 => nthOr l n

/-- **The keys of the library's Ligero tableaus** (`TableauKey.cert`,
`GordieHowe/Applications/FieldInterps/Registry.lean`). -/
inductive TableauKey where
  | gf128K265R2 | gf128K282R2 | gf128K300R2 | gf256K339R2 | fq20K271 | falconNativeROMA
  | falconRingNativeROMA | gold2K512R2 | gold4K512 | gold4K512R2 | gold4K1024
  deriving DecidableEq, Repr, Inhabited

/-- **A tableau's numbers with a weighted Johnson line certificate**: the Ligero numbers
(`Ligero.Relative.Shape`: rate, opened columns, encoded block length, low-degree-test repetitions,
privacy positions), the agreement threshold, the exceptional count, and the Johnson certificate
`(m, B, H)` (`IsJohnsonWeightedCertificate`). The masking is the mask test. -/
structure JohnsonDesc where
  rate : Nat
  nreq : Nat
  blockEnc : Nat
  nrep : Nat
  r : Nat
  agree : Nat
  exceptions : Nat
  m : Nat
  B : Nat
  H : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **A domain's Ligero tableau**: one of the library's, or numbers with a Johnson certificate
(`TableauDesc.Ok` checks it, `TableauDesc.cert` builds it). -/
inductive TableauDesc where
  /-- The library's tableau `k`. -/
  | library (k : TableauKey)
  /-- A tableau with a Johnson line certificate. -/
  | johnson (j : JohnsonDesc)
  deriving DecidableEq, Repr, Inhabited

/-! ## Small data -/

/-- **The field table of a program**: the interpretation's shape, each domain's field identifier,
each circuit's domain, each field identifier's packing descriptor, and a claim the compiler may
state and a check confirms: the program has no field-form `mod_q` (`noFieldForm`). The flag at
`false` claims nothing. -/
structure FieldTable where
  /-- The interpretation's shape and opaque-function set. -/
  interp : InterpDesc
  /-- Domain `i`'s field identifier. -/
  domainFields : List Nat
  /-- Circuit `c`'s domain. -/
  circuitDomains : List Nat
  /-- Field identifier `f`'s packing descriptor. -/
  packing : List PackingDesc
  /-- When `true`, the program has no field-form `mod_q`; `false` makes no claim. -/
  noFieldForm : Bool
  deriving Repr, Inhabited

/-- Domain `i`'s field identifier. -/
@[reducible] def FieldTable.domainField (t : FieldTable) (i : Nat) : Nat := nthOr t.domainFields i

/-- Circuit `c`'s domain. -/
@[reducible] def FieldTable.circuitDomain (t : FieldTable) (c : Nat) : Nat :=
  nthOr t.circuitDomains c

/-- Circuit `c`'s field identifier: its domain's. -/
@[reducible] def FieldTable.circuitField (t : FieldTable) (c : Nat) : Nat :=
  t.domainField (t.circuitDomain c)

/-- **The figures of a program**, as numerals: the figures (`ProgramFigures`), each domain's
largest array, largest challenge read and reads besides its first combination, each domain's
stream grants, the transcript's largest grant, the source challenges'
error fractions, and whether the transcript grants no extended stream (`defaultLoads`). -/
structure FiguresData where
  /-- Whether the program states figures. The program's check (`ProgramData.programOkB`) requires
  them present at a program with figures and absent at a program certified only for its proof
  system. -/
  present : Bool := true
  /-- The figures. -/
  figures : ProgramFigures
  /-- Each domain's largest array. -/
  maxArray : List Nat
  /-- Each domain's largest challenge read. -/
  maxRead : List Nat
  /-- Each domain's reads besides its first combination. -/
  restRead : List Nat
  /-- Each domain's stream grants (past the list's end, none). -/
  grants : List ForkGrants
  /-- The transcript's largest grant. -/
  grantMax : Nat
  /-- The error fraction of each source challenge. -/
  sourceErrors : Nat → Nat × Nat
  /-- The transcript grants no extended stream. -/
  defaultLoads : Bool

/-- **No figures**: the figures' data of a program certified for its proof system only
which no configuration reads. -/
def FiguresData.none : FiguresData where
  present := false
  figures := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  maxArray := []
  maxRead := []
  restRead := []
  grants := []
  grantMax := 0
  sourceErrors := fun _ => (0, 1)
  defaultLoads := false

/-- **The computational inputs of a program**: everything its proof system and certified data
read. The realized program, its plan, the field table, each domain's Ligero tableau descriptor
and the figures. Every definition the proof system reads is a function of these inputs
(`GordieHowe/Applications/Program/Conditions.lean`, `Runtime.lean`). -/
structure RuntimeInputs where
  /-- The realized program. -/
  program : RealizedProgram
  /-- The plan. -/
  plan : Export.Plan
  /-- The field table. -/
  fieldTable : FieldTable
  /-- Each domain's Ligero tableau. -/
  tableaus : List TableauDesc
  /-- The figures. -/
  figures : FiguresData

/-- **The computational inputs of the honest strategy**: the structure records, the completion
certificate's generators and derivations, and the honest nodes (the packing nodes known to
contain `1`). -/
structure CompletionInputs where
  /-- The structure records. -/
  records : Structure
  /-- The completion certificate's generators. -/
  gens : Gens
  /-- The completion certificate's derivations. -/
  cderivs : CDerivations
  /-- The honest nodes. -/
  nodes : List (Nat × String)

/-- **The hints**: the certificates that make the checks local and that only the program's check
reads. The expression annotations, the derivations, and checked assignment-read rows. -/
structure Hints where
  /-- The expression annotations. -/
  exprAnn : ExprAnn
  /-- The derivations of the realization. -/
  derivs : Derivations
  /-- Exact assignment-read rows, checked against the prefix recurrence. Rows are required:
  the empty default passes only for a program with no values; nonempty programs reject
  omitted rows. Every exporter emits them. -/
  assignmentReads : List (List Nat) := []

/-- **Everything the compiler emits about one program** (module docstring): the computational
inputs of the proof system (`inputs`) and of the honest strategy (`completion`), and the
witnesses only the program's check reads. `d.program` is `d.inputs.program`, and a definition
of `RuntimeInputs` applies to `d` as `d.inputs`. -/
structure ProgramData extends inputs : RuntimeInputs, completion : CompletionInputs where
  /-- The hints. -/
  hints : Hints
  /-- The GKR certificate of each circuit. -/
  circuits : List CircuitData
  /-- The shapes the application frontends read. -/
  shapes : List ShapeClaim
  /-- Optional source-role assignments. Runtime consumers use their separate computable constant. -/
  sourceRoles : Option (List SourceRoleEntry) := none
  /-- The table selections' certificates (`RealizedProgram.SelCert`, one per `select_row`). -/
  selections : List RealizedProgram.SelCert := []

/-- Domain `i`'s tableau descriptor. -/
def RuntimeInputs.tableauDesc (r : RuntimeInputs) (i : Nat) : TableauDesc :=
  r.tableaus.getD i default

namespace ProgramData

variable (d : ProgramData)

/-- **The shapes part**: every shape claim holds of the program (`RealizedProgram.shapesB`; its
soundness `ProgramData.shapes_sound`). -/
def shapesB : Bool := d.program.shapesB d.shapes

/-- **The source-role part**, requiring complete source assignments when a table is present. -/
def sourceRolesB : Bool := sourceRolesPartB d.program d.sourceRoles

end ProgramData

end GordieHowe
