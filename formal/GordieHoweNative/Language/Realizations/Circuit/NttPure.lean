-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Circuit.OpRows

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Circuit.NttPure`

The definitions of `GordieHowe.Language.Realizations.Circuit.NttPure` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Circuit/NttPure.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open OpList

section Pure

variable {F : Type _}

/-- **The half-size of stage `s`** of a staged transform on `L` bits: `2^s` in natural order
(`ntt_gadget::transform`), `2^(L−1−s)` in scheme order (`StagedNtt::forward`). -/
def nttHalf (L : ℕ) : NttOrder → ℕ → ℕ
  | .natural, s => 2 ^ s
  | .scheme, s => 2 ^ (L - s - 1)

/-- **The twiddle exponent of stage `s` at the upper position `q`** of a staged transform of
length `n = 2^L`, the twiddle being `ψ^e`: in natural order `(n / 2^s) · (q mod 2^(s+1))`, the
offset's power of `(ψ²)^(2^(L−1−s))`; in scheme order `br_L(2^s + g)`, `g` the block of `q`
(the C++'s `zetas[z]`, `z = 2^s + g`). -/
def nttTwIdx (n L : ℕ) : NttOrder → ℕ → ℕ → ℕ
  | .natural, s, q => n / 2 ^ s * (q % (2 * 2 ^ s))
  | .scheme, s, q => bitRevNat L (2 ^ s + q / (2 * 2 ^ (L - s - 1)))

end Pure

end GordieHowe.RealizedProgram
