-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

/-! # Realization derivation payload regression

The compiler fixture covers emitted steps, interval sources, expressions and named operators,
a long ranks list, negative and large integers, and named index-map references.
-/

namespace GordieHoweTest.DerivationsLoad
open GordieHowe.RealizedProgram

/-- The named index-map reference shared by the binary and literal fixtures. -/
@[expose] def idx0 : IndexMap := []

-- Loaded literal bodies are the interface under test.
@[expose] public section
load_program_ghc "ProgramCertData/Derivations.ghc" "ab65efe01db22e7a"
end

namespace Literal
local notation "ℕ" => Nat
/-- The derivations other than [.realized pid, .conclude 0], by predicate. -/
@[expose] def derivs : List (ℕ × List Step) :=
  [(0, [.inDom 1 (.realized 7), .inDom 1 (.subst (.leaf 1) (.add (.leaf 1) (.leaf 1))), .inDom 1 (.linear [(0, (Int.negSucc 3)), (1, 0), (2, 7)] (.leaf 1) (.add (.leaf 1) (.leaf 1))), .inDom 1 (.lookup [(1, 2, 3)]), .inDom 1 (.rangeNat 0), .inDom 1 (.holdsIn 0), .inDom 1 (.src 7 .const), .inDom 1 (.ivlNat 0), .inDom 1 (.ivlExpr [0, 1, 2] (.leaf 1) 5 12), .inDom 1 (.ivlMeet 0 1), .inDom 1 (.natIvl 0), .inDom 1 (.natComp 0 1), .inDom 1 (.natBool 7), .inDom 1 (.natLin 0 [1, 2]), .inDom 1 (.liftConst 0 1), .inDom 1 (.fieldDvd 0 1 2), .inDom 1 (.groupedMod [1, 2] [0, 1, 2]), .inDom 1 (.ivlApply 0 (some 1) (.leaf 1) 5 12), .inDom 1 (.ivlLogic [0, 1, 2] (.leaf 1)), .inDom 1 (.fact 7), .inDom 1 (.transport 0 1), .inDom 1 (.lift 0 1 2), .inDom 1 (.digits 0 [1, 2] 5), .inDom 1 (.congr 0), .inDom 1 (.mac [1, 2] (some 3) [0, 1, 2]), .inDom 1 (.linop (.spectral 2 0)), .inDom 1 (.conclude 0), .inDom 1 (.hyp 7), .inDom 1 (.ivlDisjoint 0 1), .inDom 1 (.circuitAssert 7), .inDom 1 (.inputPremise 7), .src 3 .const, .src 3 (.declared 2), .src 3 (.nat 0), .src 3 .prime, .src 3 .opaqueBit, .src 3 (.quadRoot 1 0), .src 3 (.rootSet [1, 2]), .src 3 (.shift 0), .src 3 (.tableHull [1, 2] (Int.negSucc 18446744073709551616) 9), .ivlExpr [] (.leaf 1) (Int.negSucc 0) 65537, .ivlExpr [] (.add (.leaf 1) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.sub (.leaf 1) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.scale (.const 18446744073709551617) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.mul (.leaf 1) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.reindex idx0 (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.concat (.leaf 1) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.linear [[(0, .const 18446744073709551617), (1, .node 2 3)]] (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.prod 0 (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.mux (.leaf 1) (.leaf 1) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.negacyclicConv 7 (.nttNatural 65537)) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.ref 0) (Int.negSucc 0) 65537, .ivlExpr [] (.logic .eq 0 [.leaf 1, .leaf 1]) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.negacyclicConv 7 (.nttNatural 65537)) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.polyMatVec 7 2 3 (.nttNatural 65537)) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.polyBroadcast 7 2 (.nttNatural 65537)) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.ntt 2 65537 .natural) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.inverseNtt 2 65537) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.nttTranspose 2 65537) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.rowDot 7 2 3) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.macConv 7 2 3 [0, 2, 5]) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.acyclicConv 7 2) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.diagonal 7) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.scale 7) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.constDiagonal 7) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.sum 2) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.fromDigits 2 65537) (.leaf 1)) (Int.negSucc 0) 65537, .ivlExpr [] (.apply (.batched 2 (.negacyclicConv 7 (.nttNatural 65537))) (.leaf 1)) (Int.negSucc 0) 65537])]

/-- Each predicate's rank: above every predicate its derivation cites. -/
@[expose] def ranks : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
   100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
   120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]

/-- The shared facts: each with its rank and the steps that state it. -/
@[expose] def shared : List SharedEntry :=
  [{ fact := .ivl 0 (.leaf 1) (Int.negSucc 4) 9, rank := 2, steps := [.inDom 1 (.realized 7)] }]

/-- The GKR circuits' derivations other than their instances' facts, by circuit and entry. -/
@[expose] def circuitDerivs : List (ℕ × List (ℕ × List Step)) :=
  [(2, [(3, [.ivlExpr [] (.apply (.batched 2 (.negacyclicConv 7 (.nttNatural 65537))) (.leaf 1)) (Int.negSucc 0) 65537])])]

/-- The derivations, as the checker reads them. -/
@[expose] def derivations : Derivations := { derivs := derivs, ranks := ranks, shared := shared, circuitDerivs := circuitDerivs }

end Literal

open Lean Elab Command in
run_cmd liftTermElabM do
  for (actualName, expectedName) in [(``derivs, ``Literal.derivs), (``ranks, ``Literal.ranks),
      (``shared, ``Literal.shared), (``circuitDerivs, ``Literal.circuitDerivs)] do
    let .defnInfo actual ← getConstInfo actualName | throwError "missing loaded payload"
    let .defnInfo expected ← getConstInfo expectedName | throwError "missing literal"
    unless actual.type == expected.type && actual.value == expected.value do
      throwError "loaded derivations changed the literal type or value: {actualName}"

end GordieHoweTest.DerivationsLoad
