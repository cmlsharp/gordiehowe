-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweTest.NativeCheckModesData
meta import GordieHoweTest.NativeCheckModesData
meta import GordieHowe.Language.Realizations.Circuit.RelEntry

@[expose] public section

namespace GordieHoweTest.NativeCheckModes

open GordieHowe.GKR.Certificate

/-- The small certificate checks using only kernel reduction. -/
theorem kernelCheck : check cert.dag cert.layered cert.sched = true := by decide +kernel

/-- The loaded certificate has positive width, checked by explicit compiled evaluation. -/
theorem nativeCheck : positive cert.width = true := by gh_native_check

/-- error: gh_native_check: the check evaluates to false; its parts that fail: [GordieHoweTest.NativeCheckModes.zero] -/
#guard_msgs in
example : parts 1 = true := by gh_native_check

/-- error: gh_native_check: the check evaluates to false; its parts that fail: [GordieHoweTest.NativeCheckModes.atZero] -/
#guard_msgs in
example : nestedParts 2 = true := by gh_native_check

open Lean Elab Command in
run_cmd liftTermElabM do
  let kernelAxioms ← Lean.collectAxioms ``kernelCheck
  unless kernelAxioms.all (fun n => [``propext, ``Quot.sound, ``Classical.choice].contains n) do
    throwError "kernel check unexpectedly trusts additional axioms: {kernelAxioms}"
  let nativeAxioms ← Lean.collectAxioms ``nativeCheck
  unless nativeAxioms.any (fun n => (n.toString.splitOn "native_decide").length > 1) do
    throwError "explicit native check did not record its compiled-check axiom"

end GordieHoweTest.NativeCheckModes
