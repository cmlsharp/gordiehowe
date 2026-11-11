-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public meta import Lean.Attributes
public meta import Lean.EnvExtension
public meta import Lean.Exception
public meta import Lean.OriginalConstKind

public meta section

/-!
# The `@[headline]` attribute

`@[headline]` marks the theorems the paper claims: the BCS compilation with merges, the program
backend and their components, most of them generic; the literature results the paper presents as
machine-checked (the compressed-oracle lemmas of Zhandry and CMS19, one-way to hiding); the
configuration templates (`@[config_template headline]`,
`GordieHowe/Applications/Configuration/Instantiate.lean`), generic over a configuration; and the
templates' instances that the paper prints, at the configurations `MLDSA44.Emulated.ROMParams` and
`.QROMParams`, stated at concrete settings. A template's restatements at other configurations are
not tagged. Other supporting results (transfer and existence lemmas) are not tagged.

The tagged theorems are the roots of the statement closure (`scripts/StatementClosure.lean`) and
of the statement and hypothesis audit: everything a reader must trust is
reached from their statements.

The tag may be added in a module other than the declaration's (`attribute [headline] n`), so a
theorem can be tagged without editing its file.
-/

open Lean

namespace GordieHowe

/-- The declarations tagged `@[headline]`, across all imported modules. -/
initialize headlineExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := NameSet.insert
    addImportedFn := fun es => es.foldl (fun s a => a.foldl NameSet.insert s) {}
  }

/-- `@[headline]`: the theorem is one the paper claims (a main theorem, a configuration template or
a printed instance), and a root of the statement closure and the audit. -/
initialize registerBuiltinAttribute {
    name := `headline
    descr := "a theorem the paper claims; a root of the statement closure and the audit"
    add := fun decl _ kind => do
      unless kind == AttributeKind.global do
        throwError "@[headline] must be global"
      unless wasOriginallyTheorem (← getEnv) decl do
        throwError "@[headline] applies only to theorems: {decl}"
      modifyEnv (headlineExt.addEntry · decl)
  }

/-- The declarations tagged `@[headline]` in the environment. -/
def headlines (env : Environment) : NameSet :=
  headlineExt.getState env

end GordieHowe
