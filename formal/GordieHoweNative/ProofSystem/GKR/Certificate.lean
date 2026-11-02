-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Data

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.GKR.Certificate`

The definitions of `GordieHowe.ProofSystem.GKR.Certificate` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/ProofSystem/GKR/Certificate.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.GKR.Certificate

/-- A quadratic term `κ k · v a · v b`. -/
structure Term where
  /-- The constant's index. -/
  k : ℕ
  /-- The left operand. -/
  a : ℕ
  /-- The right operand. -/
  b : ℕ

/-- The `i`-th `w`-bit field of `T`. -/
def field (w T i : ℕ) : ℕ := (T >>> (i * w)) % 2 ^ w

/-- `n` terms read from `c`, three fields each, least significant first. -/
def decodeTerms (w : ℕ) : ℕ → ℕ → List Term
  | 0, _ => []
  | n + 1, c =>
    ⟨c % 2 ^ w, (c >>> w) % 2 ^ w, (c >>> (2 * w)) % 2 ^ w⟩ :: decodeTerms w n (c >>> (3 * w))

/-- A chunk's terms. -/
def terms (w c : ℕ) : List Term := decodeTerms w (c % 2 ^ w / 2) (c >>> w)

/-- The chunk at key `k` (`0`, the zero node, where there is none). -/
def NTree.get : NTree → ℕ → ℕ
  | .nil, _ => 0
  | .leaf c, _ => c
  | .node l r, k => cond (Nat.beq (k % 2) 0) (l.get (k / 2)) (r.get (k / 2))

/-- The `i`-th entry of a table. -/
def cell (w : ℕ) : Table → ℕ → ℕ
  | .ident, i => i
  | .packed e t, i => field w (t.get (i >>> e)) (i % 2 ^ e)

end GordieHowe.GKR.Certificate
