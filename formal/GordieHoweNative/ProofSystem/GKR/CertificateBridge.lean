-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.GKR.Certificate

/-! # Compiled checks connecting layered certificates to source circuits

The Boolean checks keep their original names and bodies. Their semantic proofs remain in
`GordieHowe.ProofSystem.GKR.CertificateBridge`.
-/

public section
local notation "ℕ" => Nat

namespace GordieHowe.GKR.CertificateBridge
open Certificate RealizedProgram

/-- A gate's terms have at most one assertion term (constant index `0`). -/
@[expose] def atMostOneAssert : List Term → Bool
  | [] => true
  | t :: ts => cond (Nat.beq t.k 0) (!hasAssert ts) (atMostOneAssert ts)

/-- The assertion check on an empty list. -/
theorem atMostOneAssert_nil : atMostOneAssert [] = true := rfl

/-- The assertion check on a term followed by the rest. -/
theorem atMostOneAssert_cons (t : Term) (ts : List Term) :
    atMostOneAssert (t :: ts) = cond (Nat.beq t.k 0) (!hasAssert ts) (atMostOneAssert ts) := rfl

/-- Every gate of the layer `l` has at most one assertion term. -/
@[expose] def layerUniqueB (w : ℕ) (l : List ℕ) : Bool := l.all fun c => atMostOneAssert (gateTerms w c)

/-- Defining equation for the per-layer assertion check. -/
theorem layerUniqueB_eq (w : ℕ) (l : List ℕ) :
    layerUniqueB w l = l.all (fun c => atMostOneAssert (gateTerms w c)) := rfl

/-- **Every gate of `C` has at most one assertion term.** -/
@[expose] def uniqueAssertsB (w : ℕ) (C : Layered) : Bool := C.layers.all (layerUniqueB w)

/-- Defining equation for the circuit assertion check. -/
theorem uniqueAssertsB_eq (w : ℕ) (C : Layered) :
    uniqueAssertsB w C = C.layers.all (layerUniqueB w) := rfl

/-- **The shape of `C`**: at least one and at most `depth` layers, each of at most `2 ^ width`
gates. -/
@[expose] def shapeB (C : Layered) (width depth : ℕ) : Bool :=
  Nat.blt 0 C.layers.length && Nat.ble C.layers.length depth &&
    C.layers.all fun l => Nat.ble l.length (2 ^ width)

/-- Defining equation for the circuit shape check. -/
theorem shapeB_eq (C : Layered) (width depth : ℕ) :
    shapeB C width depth = (Nat.blt 0 C.layers.length && Nat.ble C.layers.length depth &&
      C.layers.all (fun l => Nat.ble l.length (2 ^ width))) := rfl

end GordieHowe.GKR.CertificateBridge
