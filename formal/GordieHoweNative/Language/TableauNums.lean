-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Export

/-!
# GordieHowe: the numbers of a Ligero tableau

A domain's Ligero certificate (`GordieHowe.RealizedProgram.LigeroCert`, Mathlib-side: its line
certificate and masking are facts about codes over every field) is checked against its field and
the plan by two tests, `LigeroCert.validB` (the layout facts at the field's point domain) and
`LigeroCert.matchesB` (the plan's Ligero numbers and masking). Both read only the certificate's
Ligero numbers and whether its masking is the mask test, the tableau's numbers (`TableauNums`).
Here both tests are written on the numbers; `LigeroCert.validB_eq_nums` and
`LigeroCert.matchesB_eq_nums` equate them with the certificate's.
-/

@[expose] public section

namespace GordieHowe

open RealizedProgram

/-- **A tableau's numbers**: its Ligero numbers (`Ligero.Relative.Shape`: rate, opened columns,
encoded block length, low-degree-test repetitions, privacy positions), whether its masking is the
mask test (`split`; otherwise untested masks), and its line certificate's agreement threshold and
exceptional count. -/
structure TableauNums where
  rate : Nat
  nreq : Nat
  blockEnc : Nat
  nrep : Nat
  r : Nat
  split : Bool
  agree : Nat
  exceptions : Nat
  deriving DecidableEq, Repr, Inhabited

namespace TableauNums

variable (t : TableauNums)

/-- The message block: `(block_enc + 1)/(2 + rate)` (`Ligero.Relative.Shape.block`). -/
def block : Nat := (t.blockEnc + 1) / (2 + t.rate)

/-- The code length: the opened columns `[2·block − 1, block_enc)`
(`Ligero.Relative.Shape.N`). -/
def N : Nat := t.blockEnc - (2 * t.block - 1)

/-- **The layout facts** at the point domain of size `q`, and, for the mask test, the opened
columns covered (`2·nreq ≤ block`): `LigeroCert.validB` on the numbers. -/
def validB (q : Nat) : Bool :=
  decide (t.blockEnc ≤ q) && decide (0 < t.nreq) && decide (t.nreq ≤ t.r) &&
    decide (t.r < t.block) && decide (2 * t.block < t.N) && decide (t.nreq ≤ t.N) &&
    decide (0 < t.nrep) && (!t.split || decide (2 * t.nreq ≤ t.block))

/-- **The plan's Ligero numbers and masking are the tableau's**: `LigeroCert.matchesB` on the
numbers. -/
def matchesB (lg : Export.Ligero) : Bool :=
  lg.masking == (if t.split then .split else .listRadius) && lg.rate == t.rate &&
    lg.blockEnc == t.blockEnc && lg.t == t.nreq && lg.r == t.r && lg.N == t.N &&
    lg.k == t.block && lg.ldtReps == t.nrep

end TableauNums

end GordieHowe
