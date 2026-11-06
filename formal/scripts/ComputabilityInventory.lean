-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe
import Lean.Compiler.IR.CompilerM

/-!
# Definition computability inventory

This audit script intentionally uses the traditional import header: `module` restricts private
visibility in transitive dependencies, even with `import all` on the root. Complete imported
environment inspection, including those private definitions, is the script's interface.

Write every imported definition and opaque declaration, including private declarations,
projections and auxiliaries,
to the TSV path `COST_LINT_INVENTORY_OUTPUT`. There is no namespace or result-type filter.
`noncomputable` includes the compiler's unsafe-recursion companion flag. `has_ir` records
compiled IR independently; type formers and erased definitions can have no IR without being
marked noncomputable. The gate compares these flags with the pinned baseline separately.
-/

open Lean Elab Command

run_cmd do
  let some path ← IO.getEnv "COST_LINT_INVENTORY_OUTPUT" |
    throwError "COST_LINT_INVENTORY_OUTPUT is required"
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .defnInfo _ | .opaqueInfo _ => pure ()
    | _ => continue
    let noncomp := isNoncomputable env n ||
      isNoncomputable env (Compiler.mkUnsafeRecName n)
    let hasIR := (IR.findEnvDecl env n).isSome
    rows := rows.push s!"{n}\t{noncomp}\t{hasIR}"
  rows := rows.qsort (· < ·)
  IO.FS.writeFile path ("name\tnoncomputable\thas_ir\n" ++
    String.intercalate "\n" rows.toList ++ "\n")
  logInfo m!"computability inventory: {rows.size} definitions written"
