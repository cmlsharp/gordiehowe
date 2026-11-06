-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweTest.StructureLoadData
meta import GordieHoweTest.StructureLoadData
meta import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

namespace GordieHoweTest.StructureLoad

/-- Reader registration preserves the complete structure record's kernel value. -/
theorem reader_eq : records.ghNative () = Literal.records := rfl

/-- The kernel reads long lists and every record category without native-check proof dependencies. -/
theorem kernelCheck : records.gadgets.length = 13 ∧ records.messages.length = 140 ∧
    records.routes.length = 7 ∧ records.ivlSources.length = 9 := by decide +kernel

/-- Explicit compiled checking reads and compares every structure field. -/
theorem nativeCheck : reprStr records = reprStr Literal.records := by gh_native_check

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``reader_eq, ``kernelCheck] do
    let axioms ← Lean.collectAxioms n
    unless axioms.all (fun a => [``propext, ``Quot.sound, ``Classical.choice].contains a) do
      throwError "kernel structure check trusts additional axioms: {axioms}"
  let axioms ← Lean.collectAxioms ``nativeCheck
  unless axioms.any (fun n => (n.toString.splitOn "native_decide").length > 1) do
    throwError "explicit structure check did not record compiled-check trust"

end GordieHoweTest.StructureLoad
