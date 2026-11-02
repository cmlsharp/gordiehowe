-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.GKR.Rel

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.GKR.Twin`

The definitions of `GordieHowe.ProofSystem.GKR.Twin` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/ProofSystem/GKR/Twin.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.Twin

/-- **Success of a run**, forgetting the failure. -/
def okB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- **A test**: success when `b`, else the failure `e`. -/
def guardE {ε : Type} (b : Bool) (e : ε) : Except ε Unit := cond b (.ok ()) (.error e)

/-- **A conjunction**: `x`, then `y`; the first failure. -/
def seqE {ε : Type} (x y : Except ε Unit) : Except ε Unit :=
  match x with
  | .ok _ => y
  | .error e => .error e

/-- **A list check with indices**: `f i x` on every element `x` at index `i`, from `i₀`; the first
failure. -/
def allE {ε α : Type} (f : ℕ → α → Except ε Unit) : ℕ → List α → Except ε Unit
  | _, [] => .ok ()
  | i, x :: xs => seqE (f i x) (allE f (i + 1) xs)

/-- **A test on a fold's result**: `q` on the fold's state, or the fold's failure. -/
def thenE {ε β : Type} (x : Except ε β) (q : β → Except ε Unit) : Except ε Unit :=
  match x with
  | .ok b => q b
  | .error e => .error e

/-- **Relabel the failure** (for example, prefix the entry the check belongs to). -/
def mapE {ε ε' α : Type} (g : ε → ε') (x : Except ε α) : Except ε' α :=
  match x with
  | .ok a => .ok a
  | .error e => .error (g e)

end GordieHowe.Twin

namespace GordieHowe.GKR.Rel

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin

/-- **Where the relational check rejects**: the cuts, the assertions, or the asserted nodes. -/
inductive Part where
  /-- A cut. -/
  | cut
  /-- An assertion. -/
  | assert
  /-- The asserted nodes. -/
  | asserted
  deriving Repr, DecidableEq, Inhabited

/-- **A failure**: the part, the item's index within it, and the reason. -/
structure Failure where
  /-- The part. -/
  part : Part
  /-- The item. -/
  item : ℕ
  /-- The reason. -/
  reason : Reason
  deriving Repr, DecidableEq, Inhabited

/-- **A verdict as a twin's result**: `none` succeeds, a reason fails as item `i` of part `pt`. -/
def verdictE (pt : Part) (i : ℕ) : Option Reason → Except Failure Unit
  | none => .ok ()
  | some r => .error ⟨pt, i, r⟩

section

variable (w : ℕ) (D : Dag) (Kc : Consts) (ar : CodeArith)

/-- **The twin of a cut**, at index `i` of the cuts. -/
def cutE (i : ℕ) (W : Wire) (e : TE) : Except Failure Unit :=
  verdictE .cut i (cutR w D Kc ar W e)

/-- **The twin of an assertion**, at index `i` of the assertions. -/
def zeroE (i Z U : ℕ) (e : TE) : Except Failure Unit :=
  verdictE .assert i (zeroR w D Kc ar Z U e)

/-- **The twin of the relational check.** -/
def relOkE (cuts : List (Wire × TE)) (zs : List (ℕ × ℕ × TE)) : Except Failure Unit :=
  seqE (allE (fun i c => cutE w D Kc ar i c.1 c.2) 0 cuts)
    (seqE (allE (fun i z => zeroE w D Kc ar i z.1 z.2.1 z.2.2) 0 zs)
      (guardE (subsetSorted (assertedNodes zs) D.asserts) ⟨.asserted, 0, .asserted⟩))

end

end GordieHowe.GKR.Rel
