-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweTest.ExprAnnLoadData
meta import GordieHoweTest.ExprAnnLoadData
meta import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

namespace GordieHoweTest.ExprAnnLoad

/-- Registering the runtime reader preserves the loaded value in the kernel. -/
theorem reader_eq : exprAnn.ghNative () = literal := rfl

/-- The loaded literal can be checked entirely by the kernel. -/
theorem kernelCheck : exprAnn.maxId = 28 := by decide +kernel

/-- An explicit native check uses the registered reader. -/
theorem nativeCheck : exprAnn.maxId = 28 := by gh_native_check

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``reader_eq, ``kernelCheck] do
    let axioms ← Lean.collectAxioms n
    unless axioms.all (fun a => [``propext, ``Quot.sound, ``Classical.choice].contains a) do
      throwError "kernel check unexpectedly trusts additional axioms: {axioms}"
  let axioms ← Lean.collectAxioms ``nativeCheck
  unless axioms.any (fun n => (n.toString.splitOn "native_decide").length > 1) do
    throwError "explicit native check did not record its compiled-check axiom"

end GordieHoweTest.ExprAnnLoad
