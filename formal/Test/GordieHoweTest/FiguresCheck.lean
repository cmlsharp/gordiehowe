-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.Program.FiguresCheck

/-! # Rejection tests for the figures' queried mask keys and stream grants -/

namespace GordieHowe.Test.FiguresCheck

open RealizedProgram Export FigCheck

private def edge : PackingEdge where
  child := "prime"
  parent := "extension"
  mode := .subfieldMasks
  degree := 4
  measurements := 4
  masks := 80
  childDegree := 1

private def masks : PackingDesc where
  masks := [(1, 4, .subfieldMasks, 80, 0)]

-- A missing query cannot be discharged by the descriptor's default answer.
example : ({} : PackingDesc).masksCoverB [edge] = false := by decide +kernel
example : masks.masksCoverB [edge] = true := by decide +kernel
example : masks.masksCoverB [{ edge with mode := .squaringChain }] = false := by decide +kernel
example : masks.masksCoverB [{ edge with childDegree := 4 }] = false := by decide +kernel

private def domain : DomainFig where
  N := {
    batches := [], degrees := [4, 5], np := 180, nOwn := 0, nw := 0, root := 0,
    rows := 20, rowsOff := 0, quads := 0, circuits := [] }
  t := {
    rate := 12, nreq := 127, blockEnc := 3799, nrep := 1, r := 254,
    split := true, agree := 700, exceptions := 1 }
  fb := 35
  load := (20, 2)
  grant := 0
  grants := { stage := fun i => if i = 0 then 500 else 0, linear := 20 }
  q := 12289 ^ 20
  Mx := 1000
  Lmax := 1000
  Lr := 1000

-- First-stage and linear grants are supported; a later visited stage is rejected.
example : domain.grantsB = true := by decide +kernel
example : domain.joinGrant = 500 := by decide +kernel
example : ({ domain with grants := { stage := fun _ => 500 } }).grantsB = false := by
  decide +kernel
-- Insufficient evidence of two touching claims rejects a nonzero first-stage grant.
example : ({ domain with N := { domain.N with rows := 12 } }).grantsB = false := by
  decide +kernel
-- Stage indices beyond the plan's edges are not visited.
example : ({ domain with grants := {
    stage := fun i => if i = 0 then 500 else if i = 1 then 0 else 999 } }).grantsB = true := by
  decide +kernel

-- The numeric field-error check accepts split masking only.
example : domain.fieldRoundsB 100000 0 = true := by decide +kernel
example : ({ domain with t := { domain.t with split := false } }).fieldRoundsB 100000 0 = false := by
  decide +kernel

end GordieHowe.Test.FiguresCheck
