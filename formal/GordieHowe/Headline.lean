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
backend, their components and their instance corollaries (the bounds per configuration).
Supporting results (O2H, the compressed oracle, transfer and existence lemmas) are not tagged.

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

/-- `@[headline]`: the theorem is one the paper claims (a main theorem or an instance
corollary), and a root of the statement closure and the audit. -/
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
