-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-!
# Every constant of the `GordieHowe` modules

One line per constant: `<name>\t<module>\t<kind>\t<flags>`, flags a comma-separated subset of
`instance`, `protected`, `private`, `internal`, `aux` (recursor, `noConfusion`, matcher),
`proj` (a structure projection). Input of the rename-map generator.

Run as `lake env lean scripts/ConstantDump.lean`.
-/

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless m.getRoot == `GordieHowe do continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
    let mut flags : Array String := #[]
    if isInstanceCore env n then flags := flags.push "instance"
    if isProtected env n then flags := flags.push "protected"
    if isPrivateName n then flags := flags.push "private"
    let un := (privateToUserName? n).getD n
    if un.isInternal then flags := flags.push "internal"
    if isAuxRecursor env n || isNoConfusion env n || isMatcherCore env n then flags := flags.push "aux"
    if (env.getProjectionFnInfo? n).isSome then flags := flags.push "proj"
    IO.println s!"{n}\t{m}\t{kind}\t{",".intercalate flags.toList}"
