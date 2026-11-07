-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Std

/-!
# GordieHowe: the numeric figures of a program

The numeric data of a program's figures that its generated small data states
(`GordieHowe.FiguresData`): the figures (`RealizedProgram.ProgramFigures`) and the stream grants of
a forked domain (`RealizedProgram.ForkGrants`), in the Mathlib-free library `GordieHoweNative`. The
declarations keep their names; their lemmas are in
`GordieHowe/ProofSystem/Program/ProgramFigures.lean` and
`GordieHowe/ProofSystem/Program/FieldForkCodecs.lean`.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

/-- **The figures of a configuration's program**, as numerals: at most `rounds` rounds, trees of at
most `N` leaves, `nq` queried leaves, `kq` verifier queries, `D` digests per chain input, `pos`
positions, `k`-byte digests, every round error at most `errorMax / 2^errorExp` and every round's
load passing the Chernoff test `2^-chernoff` at the point `zNum / zDen`. The program's generated module `Figures` states
them; the part `figuresPartB` of the program's check checks them (`ProgramFigures.Check`). -/
structure ProgramFigures where
  /-- The rounds of the composite. -/
  rounds : Nat
  /-- The leaves of the largest tree. -/
  N : Nat
  /-- The queried leaves. -/
  nq : Nat
  /-- The verifier's queries. -/
  kq : Nat
  /-- The digests of one chain input. -/
  D : Nat
  /-- The positions. -/
  pos : Nat
  /-- The digest length in bytes. -/
  k : Nat
  /-- The numerator of the largest round error's bound. -/
  errorMax : Nat
  /-- The exponent of its denominator. -/
  errorExp : Nat
  /-- The Chernoff exponent of the loads. -/
  chernoff : Nat
  /-- The numerator of the point at which the loads' Chernoff test is evaluated. -/
  zNum : Nat
  /-- The denominator of that point. -/
  zDen : Nat

/-- **The stream grants of a forked domain's join**: the extra stream bytes of every stage's
combination challenge, by the stage's position, and of Ligero's constraint challenge. -/
structure ForkGrants where
  /-- The grant of the stage at each position. -/
  stage : Nat → Nat := fun _ => 0
  /-- The grant of Ligero's constraint challenge. -/
  linear : Nat := 0

end GordieHowe.RealizedProgram
