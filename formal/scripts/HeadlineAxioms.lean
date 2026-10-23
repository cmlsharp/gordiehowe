-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe

/-! The axioms of every headline theorem: `<headline>\t<axioms, comma-separated>`. -/

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  let heads := (GordieHowe.headlines env).toList.toArray.qsort (·.toString < ·.toString)
  for n in heads do
    let axs ← Lean.collectAxioms n
    let s := axs.qsort (·.toString < ·.toString)
    IO.println s!"{n}\t{",".intercalate (s.toList.map toString)}"
