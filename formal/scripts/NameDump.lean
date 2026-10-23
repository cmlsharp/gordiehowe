-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-! Every constant name of the environment outside the `GordieHowe` modules, one per line, with
`protected` marked: `<name>\t<p or empty>`. Input of the rename rewriter's name resolution. -/

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    if m.getRoot == `GordieHowe then continue
    if n.isInternal then continue
    IO.println s!"{n}\t{if isProtected env n then "p" else ""}"
