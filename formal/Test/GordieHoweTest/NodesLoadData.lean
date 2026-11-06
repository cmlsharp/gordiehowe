-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.LoadNative

public section

/-! # Honest node metadata retains its original expression

The C++ GHC regression writes this fixture, including quotes, a backslash, a newline and Unicode.
-/

namespace GordieHoweTest.NodesLoad

-- The loaded literal bodies are the interface tested below.
@[expose] public section
load_ghc "ProgramCertData/Nodes.ghc" "46469b1692d86f51"
end

/-- The literal represented by the compiler fixture. -/
@[expose] def literal : List (Nat × String) :=
  [(0, "GF(p^1)"), (1, "bit"), (12, "quote\"slash\\line\nλ")]

open Lean Elab Command in
run_cmd liftTermElabM do
  let .defnInfo actual ← getConstInfo ``nodes | throwError "missing nodes"
  let .defnInfo expected ← getConstInfo ``literal | throwError "missing node literal"
  unless actual.type == expected.type && actual.value == expected.value do
    throwError "loaded nodes changed the original type or value expression"

end GordieHoweTest.NodesLoad
