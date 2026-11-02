-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Std

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Foundations.Algebra.ConvMatrix`

The definitions of `GordieHowe.Foundations.Algebra.ConvMatrix` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Foundations/Algebra/ConvMatrix.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.Conv

section Lanes

/-- The lane of width `B` at position `j` of a natural number read as a vector of `B`-bit
digits: `⌊P / 2^(B·j)⌋ mod 2^B`. -/
def lane (B P j : ℕ) : ℕ := P / 2 ^ (B * j) % 2 ^ B

end Lanes

section Reduce

/-- Multiply a packed polynomial by `X` and reduce once by `φ` (packed as `Φ`) when the
coefficient of `X^w` is set. -/
def mulXPacked (B w Φ s : ℕ) : ℕ :=
  if lane B (s * 2 ^ B) w = 0 then s * 2 ^ B else (s * 2 ^ B) ^^^ Φ

end Reduce

variable {w : ℕ}

section Packed

/-- The reduction polynomial packed from a list of taps: `Σ_{t ∈ w :: Tl} 2^(B·t)`. -/
def phiList (B w : ℕ) (Tl : List ℕ) : ℕ := ((w :: Tl).map fun t => 2 ^ (B * t)).sum

/-- The product coefficient of `X^k` on the all-one inputs, `min (k + 1) (2w − 1 − k)`. -/
def onesCoeff (w k : ℕ) : ℕ := min (k + 1) (2 * w - 1 - k)

/-- The packed row sums of `Conv(1…1)`: the pair `(X^n mod φ, Σ_{k<n} c_k · (X^k mod φ))` after
`n = 2w − 1` steps, packed with lanes of width `B`, for `φ` packed as `Φ`. -/
def accPacked (B w Φ : ℕ) : ℕ × ℕ :=
  (List.range (2 * w - 1)).foldl
    (fun p k => (mulXPacked B w Φ p.1, p.2 + onesCoeff w k * p.1)) (1, 0)

end Packed

end GordieHowe.Conv
