-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ProgramFigures
public import GordieHowe.ProofSystem.Program.HonestReady

public section

/-!
# The certified data of a compiled program

`GordieHowe.RealizedProgram.CertifiedProgram P ir I`: everything the compiler emits and Lean
checks for a realized program `ir` at its plan `P` and interpretation `I` that a configuration
under spBCS is built from (`GordieHowe/Applications/Configuration/Certified.lean`), apart from the
proof system of its certificates, which a configuration's statements are instantiated at:

* the ready data of its domains;
* the figures with their generated check (`ProgramFigures.Check`): the domains' numbers, the source
  challenges' error fractions, the challenge readers and their largest load, the domains' rest
  reads, the transcript's largest grant, the fields' sizes, the bytes of the fields' elements, the
  phases' message bound and the branch names;
* the ready data of the honest strategy (`CompletionReady.ofGenerated`'s inputs): validity, the
  interpretation's model, the derivable realizations, the source part, the structure records, the
  completeness certificate with its check and the honest roles' check.

Each program's instance is generated (`GordieHowe.Generated.<App>.<Params>.certified`); its fields
are the generated declarations by name. Types are parameters: the program, the plan and the
interpretation are the structure's parameters and no field is a type.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem SPBCS QROM

variable (P : Export.Plan) (ir : RealizedProgram) (I : Interp)

/-- **The certified data of a compiled program** (module docstring). -/
structure CertifiedProgram where
  /-- The ready data of the domains. -/
  ready : ∀ d : Fin ir.domains.length, ir.FieldReady I d P
  /-- The figures. -/
  figures : ProgramFigures
  /-- The numbers of the domains. -/
  numbers : ForkNumbers ready
  /-- The error fractions of the source challenges. -/
  sourceErrors : ℕ → ℕ × ℕ
  /-- The readers of the challenges' values. -/
  samplerReaders : SamplerReaders I ir
  /-- The largest load of a challenge. -/
  chalLoadMax : Load
  /-- Every challenge's draws are within `chalLoadMax`. -/
  chalLoad_le : ∀ k (j : ir.ChalAt k), ir.chalLoad samplerReaders j.1 ≤ chalLoadMax
  /-- The domains' reads besides their first combinations. -/
  restRead : Fin ir.domains.length → ℕ
  /-- The transcript's largest grant. -/
  grantMax : ℕ
  /-- The figures pass their check. -/
  figuresOk : figures.Check numbers sourceErrors samplerReaders chalLoadMax chalLoad_le restRead
    grantMax
  /-- The fields' sizes are their specifications'. -/
  fieldCard : ∀ f, Fintype.card (I f).K = I.specCard f
  /-- The bytes of the fields' elements. -/
  fieldBytes : FieldBytesOf I
  /-- The phases' messages fit in `2^20` bytes. -/
  msgB_le : ∀ k, ir.msgB fieldBytes k ≤ 2 ^ 20
  /-- The branch names. -/
  branchName : Fin ir.domains.length → List Byte
  /-- The branch names have at most `2^10` bytes. -/
  branchName_le : ∀ d, (branchName d).length ≤ 2 ^ 10
  /-- The opaque functions' ranges of the interpretation's model. -/
  opaqueRanges : List (ℕ × ℕ)
  /-- The model of the interpretation. -/
  model : I.Model P ir opaqueRanges
  /-- The program is well formed. -/
  wellFormed : ir.WellFormed
  /-- The value ranges of the realizations. -/
  ranges : List (ℕ × ℕ)
  /-- The realizations are derivable. -/
  derivable : ir.Derivable (primeNodesOf P ir) ranges
  /-- The source part is well formed. -/
  sourceValid : ir.SourceValid
  /-- The structure records. -/
  records : Structure
  /-- The completeness certificate's generators. -/
  gens : Gens
  /-- The completeness certificate's derivations. -/
  cderivs : CDerivations
  /-- The honest nodes. -/
  nodes : List (ℕ × String)
  /-- The completeness certificate passes its check. -/
  completionOk : ir.completionB (primeNodesOf P ir) nodes records gens cderivs = true
  /-- The honest roles pass their check. -/
  rolesOk : ir.honestRolesB nodes records = true

namespace CertifiedProgram

variable {P ir I} (c : CertifiedProgram P ir I)

/-- **The ready data of an honest strategy of the program**: the completeness certificate's at the
plan's prime-subfield nodes and the structure records. -/
abbrev Ready : Type :=
  ir.CompletionReady I (primeNodesOf P ir) c.records c.gens c.cderivs

/-- **The ready data of the honest strategy** (`CompletionReady.ofGenerated`) at nodes known to
contain `1`. -/
@[expose] def completionReady (oneNodes : OneNodes I c.nodes) : c.Ready :=
  .ofGenerated oneNodes c.wellFormed c.model c.derivable c.sourceValid c.completionOk c.rolesOk

end CertifiedProgram

end GordieHowe.RealizedProgram
