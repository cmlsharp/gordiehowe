-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweTest.NodesLoadData
meta import GordieHoweTest.NodesLoadData
meta import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

namespace GordieHoweTest.NodesLoad

/-- Registering the reader preserves the original kernel value. -/
theorem reader_eq : nodes.ghNative () = literal := rfl

/-- The kernel checks the literal without a native proof dependency. -/
theorem kernelCheck : nodes.length = 3 := by decide +kernel

/-- Compiled checking reads and compares every field and node name. -/
theorem nativeCheck : nodes = literal := by gh_native_check

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``reader_eq, ``kernelCheck] do
    let axioms ← Lean.collectAxioms n
    unless axioms.all (fun a => [``propext, ``Quot.sound, ``Classical.choice].contains a) do
      throwError "kernel node check trusts additional axioms: {axioms}"
  let axioms ← Lean.collectAxioms ``nativeCheck
  unless axioms.any (fun n => (n.toString.splitOn "native_decide").length > 1) do
    throwError "explicit node check did not record compiled-check trust"

end GordieHoweTest.NodesLoad
