-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweTest.DerivationsLoadData
meta import GordieHoweTest.DerivationsLoadData
meta import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

namespace GordieHoweTest.DerivationsLoad

/-- Reader registration preserves every loaded field's kernel value. -/
theorem reader_eq : derivs.ghNative () = Literal.derivs ∧
    ranks.ghNative () = Literal.ranks ∧ shared.ghNative () = Literal.shared ∧
    circuitDerivs.ghNative () = Literal.circuitDerivs := ⟨rfl, rfl, rfl, rfl⟩

/-- The kernel reads the literal payload without native-check proof dependencies. -/
theorem kernelCheck : derivs.length = 1 ∧ ranks.length = 140 ∧ shared.length = 1 ∧
    circuitDerivs.length = 1 := by decide +kernel

/-- Explicit compiled checking reads and compares all derivation fields. -/
theorem nativeCheck : reprStr (derivs, ranks, shared, circuitDerivs) =
    reprStr (Literal.derivs, Literal.ranks, Literal.shared, Literal.circuitDerivs) := by
  gh_native_check

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``reader_eq, ``kernelCheck] do
    let axioms ← Lean.collectAxioms n
    unless axioms.all (fun a => [``propext, ``Quot.sound, ``Classical.choice].contains a) do
      throwError "kernel derivations check trusts additional axioms: {axioms}"
  let axioms ← Lean.collectAxioms ``nativeCheck
  unless axioms.any (fun n => (n.toString.splitOn "native_decide").length > 1) do
    throwError "explicit derivations check did not record compiled-check trust"

end GordieHoweTest.DerivationsLoad
