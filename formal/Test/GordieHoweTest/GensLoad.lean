-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweTest.GensLoadData
meta import GordieHoweTest.GensLoadData
meta import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

namespace GordieHoweTest.GensLoad

/-- Reader registration leaves the literal available to kernel reduction. -/
theorem reader_eq : gens.ghNative () = literal := rfl

/-- The full generator list can be checked in the kernel. -/
theorem kernelCheck : gens.length = 142 := by decide +kernel

/-- Explicit compiled checking reads and compares every generator and constructor field. -/
theorem nativeCheck : gens = literal := by gh_native_check

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``reader_eq, ``kernelCheck] do
    let axioms ← Lean.collectAxioms n
    unless axioms.all (fun a => [``propext, ``Quot.sound, ``Classical.choice].contains a) do
      throwError "kernel generator check unexpectedly uses additional axioms: {axioms}"
  let axioms ← Lean.collectAxioms ``nativeCheck
  unless axioms.any (fun n => (n.toString.splitOn "native_decide").length > 1) do
    throwError "explicit generator check did not record its compiled-check axiom"

end GordieHoweTest.GensLoad
