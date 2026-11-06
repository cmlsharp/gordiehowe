-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

/-!
# A compiler-produced expression annotation certificate

`gordiehowe_ghc_test` writes `ProgramCertData/ExprAnn.ghc` when
`GH_PROGRAM_CERT_TEST_DIR` names that directory. The literal is the hand-calculated packing of
the test's inputs; the loader must construct exactly its type and value expressions.
-/

namespace GordieHoweTest.ExprAnnLoad

-- The loader emits several definitions in one command; their literal bodies and reader
-- equations are the interface tested below, as in the compiler's generated Cert modules.
@[expose] public section
load_ghc "ProgramCertData/ExprAnn.ghc" "1805bf8ec360fda1"
end

/-- The expected ten packed naturals, with their original constructor spelling. -/
@[expose] def literal : GordieHowe.RealizedProgram.ExprAnn := ⟨28, 57, 5, 12, 33, 2, 2, 2, 3, 2⟩

open Lean Elab Command in
run_cmd liftTermElabM do
  let .defnInfo actual ← getConstInfo ``exprAnn | throwError "missing decoded definition"
  let .defnInfo expected ← getConstInfo ``literal | throwError "missing expected definition"
  unless actual.type == expected.type && actual.value == expected.value do
    throwError "loading ExprAnn changed its raw type or value expression"
  unless GordieHowe.Ghc.Decode.toE (α := Nat) 28 == Lean.mkRawNatLit 28 do
    throwError "the program certificate decoder changed the existing Nat decoder"

end GordieHoweTest.ExprAnnLoad
