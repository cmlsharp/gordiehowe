-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelEntry

@[expose] public section

/-!
# Explicit certificate-check modes and failure diagnostics

Importing the reader loader leaves kernel proofs free of compiled-check axioms. Only the explicit
native tactic adds one. Both proofs read the same small exported certificate. A false conjunction
reports the failing named part without introducing a proof.
-/

namespace GordieHoweTest.NativeCheckModes

open GordieHowe.GKR.Certificate

load_ghc "GKRRelData/cert_add.ghc" "566deec2de2eca5d"

/-- A passing part of the diagnostic's conjunction. -/
def positive (n : Nat) : Bool := 0 < n

/-- A failing part at the nonzero test input. -/
def zero (n : Nat) : Bool := n == 0

/-- The checker whose rejection names `zero`. -/
def parts (n : Nat) : Bool := positive n && zero n

/-- A check taking a function argument, to keep a nested binder in its input expression. -/
def atZero (predicate : Nat → Bool) : Bool := predicate 0

/-- The second part closes over the outer argument under a lambda. -/
def nestedParts (n : Nat) : Bool := positive n && atZero (fun k => k == n)

end GordieHoweTest.NativeCheckModes
