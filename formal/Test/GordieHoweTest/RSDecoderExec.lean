-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Foundations.ReedSolomon.Decoder
import Mathlib.Algebra.Field.ZMod

/-!
# Sanity checks for the executable Reed–Solomon decoder

Decoding over `ZMod 13` at the points `1, …, 12` (`N = 12`, `k = 4`, `e = 4`, so `2e + k = N`).
Not imported by `GordieHowe.lean` or `GordieHoweTest.lean`; check with
`lake env lean Test/GordieHoweTest/RSDecoderExec.lean`.
-/

namespace GordieHoweTest.RSDecoderExec

open GordieHowe RSCode BerlekampWelch

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

abbrev K := ZMod 13

def D : Fin 12 → K := fun j => (j.val + 1 : ℕ)

def code : GordieHowe.RSCode K 12 where
  D := D
  D_injective := by decide
  k := 4
  e := 4
  k_pos := by decide
  radius := by decide

/-- The message `3 + X + 4X² + X³`. -/
def msg : Fin 4 → K := ![3, 1, 4, 1]

def codeword : Fin 12 → K := fun j => evalCoeffs msg (D j)

/-- Four corrupted positions: 0, 2, 7, 11. -/
def received : Fin 12 → K := fun j =>
  if j.val = 0 then codeword j + 1
  else if j.val = 2 then codeword j + 5
  else if j.val = 7 then codeword j + 1
  else if j.val = 11 then codeword j + 2
  else codeword j

/-- Five corrupted positions. -/
def tooFar : Fin 12 → K := fun j => if j.val = 5 then received j + 3 else received j

#eval (BerlekampWelch.decode D 4 4 received).map List.ofFn
#guard (BerlekampWelch.decode D 4 4 codeword).map List.ofFn == some [3, 1, 4, 1]
#guard (BerlekampWelch.decode D 4 4 received).map List.ofFn == some [3, 1, 4, 1]
#guard (BerlekampWelch.decode D 4 3 received).isNone

/-- Two rows: the second is `2 + 5X` with errors in columns 2 and 9; together with the first
row's errors in columns 0, 2, 7, 11 that is five error columns, more than `e = 4`. -/
def row2 : Fin 12 → K := fun j =>
  if j.val = 2 then evalCoeffs ![2, 5, 0, 0] (D j) + 7
  else if j.val = 9 then evalCoeffs ![2, 5, 0, 0] (D j) + 1
  else evalCoeffs ![2, 5, 0, 0] (D j)

/-- Second row with an error only in column 7, which the first row already has wrong. -/
def row2' : Fin 12 → K := fun j =>
  if j.val = 7 then evalCoeffs ![2, 5, 0, 0] (D j) + 4 else evalCoeffs ![2, 5, 0, 0] (D j)

def U : RSCode.Matrix K 2 12 := ![received, row2]
def U' : RSCode.Matrix K 2 12 := ![received, row2']

#eval (RSCode.decode code U').map fun cs => List.ofFn fun r => List.ofFn (cs r)
#guard ((RSCode.decode code U').map fun cs => List.ofFn fun r => List.ofFn (cs r)) ==
  some [[3, 1, 4, 1], [2, 5, 0, 0]]
#guard (RSCode.decode code U).isNone
#guard RSCode.read code U' 1 (0 : K) == 2

-- An inconsistent linear system has no solution; a consistent one is solved.
#guard (GaussianElimination.solve (fun (i : Fin 3) (j : Fin 2) => (![![1, 1], ![1, 2], ![2, 3]] i j : K))
  ![1, 2, 4]).isNone
#guard ((GaussianElimination.solve (fun (i : Fin 3) (j : Fin 2) => (![![1, 1], ![1, 2], ![2, 3]] i j : K))
  ![1, 2, 3]).map List.ofFn) == some [0, 1]

end GordieHoweTest.RSDecoderExec
