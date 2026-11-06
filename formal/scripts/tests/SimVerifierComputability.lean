-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.SPBCS.SimExtractJoint
import Lean

/-! The simulation verifiers have ordinary compiled code.
Run with: scripts/lake.sh env lean scripts/tests/SimVerifierComputability.lean -/

open Lean Elab Command in
run_cmd do
  for n in [`GordieHowe.SPBCS.simVerifier, `GordieHowe.SPBCS.simExtControl,
      `GordieHowe.SPBCS.simExtVerifier] do
    unless (IR.findEnvDecl (← getEnv) n).isSome do
      throwError "{n}: missing compiled code"
  logInfo "simulation verifiers: compiled code verified"
