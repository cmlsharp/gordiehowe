-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

/-!
# Generator literals retain their original expressions

The C++ GHC test writes this fixture. Every generator constructor occurs, followed by enough
source generators to cross the legacy list-splitting boundary.
-/

namespace GordieHoweTest.GensLoad

-- These exposed loaded bodies are the literal interface whose exact expressions are tested.
@[expose] public section
load_ghc "ProgramCertData/Gens.ghc" "be827e51a18ffa53"
end

/-- The original literal, including the named type alias and a list longer than 128 entries. -/
@[expose] def literal : GordieHowe.RealizedProgram.Gens :=
  [.none, .source, .lookupDigit 1 true 2, .commDigit 3 4 5 6, .spec 7,
   .staticHist 8 9, .tag 10, .acc 11, .quotDigit 12, .digitsAcc 13,
   .lowDigit 14 15, .lateHist 16 17,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source,
   .source, .source, .source, .source, .source, .source, .source, .source, .source, .source]

open Lean Elab Command in
run_cmd liftTermElabM do
  let .defnInfo actual ← getConstInfo ``gens | throwError "missing decoded generators"
  let .defnInfo expected ← getConstInfo ``literal | throwError "missing generator literal"
  unless actual.type == expected.type && actual.value == expected.value do
    throwError "loading generators changed the original raw type or value expression"
  if (← getEnv).contains `GordieHoweTest.GensLoad.gens_l0 then
    throwError "program generators were split into auxiliary list declarations"
  let flat := GordieHowe.Ghc.listE (mkConst ``GordieHowe.RealizedProgram.Gen)
    (Array.replicate 142 (mkConst ``GordieHowe.RealizedProgram.Gen.source))
  unless (GordieHowe.Ghc.chainedDefs `legacy expected.type flat true).size > 1 do
    throwError "the fixture does not exercise the legacy list-splitting boundary"

-- Literal declarations test the notation at its branch and recursive split boundaries.
private def list0 : List Nat :=
  []

private def list1 : List Nat :=
  [0]

private def list7 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6]

private def list8 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7]

private def list31 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]

private def list32 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

private def list33 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

private def list63 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62]

private def list64 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63]

private def list65 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 64]

private def list128 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
   100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
   120, 121, 122, 123, 124, 125, 126, 127]

private def list142 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
   100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
   120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
   140, 141]

open Lean Elab Command in
run_cmd liftTermElabM do
  let nat := mkConst ``Nat
  for (n, name) in [(0, ``list0), (1, ``list1), (7, ``list7), (8, ``list8),
      (31, ``list31), (32, ``list32), (33, ``list33), (63, ``list63), (64, ``list64),
      (65, ``list65), (128, ``list128), (142, ``list142)] do
    let .defnInfo literal ← getConstInfo name | throwError "missing list literal"
    let decoded := GordieHowe.Ghc.printedListE nat
      ((List.range n).toArray.map GordieHowe.Ghc.printedNatE)
    unless literal.value == decoded && literal.value.hash == decoded.hash do
      throwError "printed list expression differs at length {n}"

end GordieHoweTest.GensLoad
