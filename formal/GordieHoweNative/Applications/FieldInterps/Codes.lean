-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.GKR.FieldCodes

/-!
# GordieHowe: the fields' code arithmetic

The code arithmetic of each field the registry has (`fq6Code`, `fq9Code`, `fq11Code`,
`fq20Code`, `gold2Code`, `gold4Code`, `gf2_128Code`, `gf2_256Code`) and the Goldilocks prime
(`pGold`), in the Mathlib-free library `GordieHoweNative`, so the circuit checks run compiled. The
declarations keep their names; their homomorphism lemmas are in
`GordieHowe/Applications/FieldInterps/{Basic,Odd,GF256,Fq20}.lean` and `pGold_eq` in
`GordieHowe/Applications/Params.lean`.
-/

@[expose] public section

namespace GordieHowe

/-- The Goldilocks prime `2^64 − 2^32 + 1`, the characteristic of the emulated arms' field
`F_{p²}` (`GordieHowe/Foundations/Fields/Goldilocks.lean`). -/
def pGold : Nat := 2 ^ 64 - 2 ^ 32 + 1

theorem pGold_eq : pGold = 18446744069414584321 := rfl

end GordieHowe

namespace GordieHowe.RealizedProgram

open BinarySpread

/-- **The code arithmetic of `F_q^6`** (`GKR.Fold.ExtCode.overPrime`): `Fp24_6`
(`lib/algebra/fp24_6.h:225`) writes coefficient `i` as `Fp24`'s three bytes
(`lib/algebra/fp24.h:273`) at byte `3 i`, so a code is `Σ_i c_i 2^(24 i)` with `c_i` the coefficient
of `X^i`; the arithmetic modulo `8380417` on each of the `6` coefficients, `X^6 = 7`. -/
def fq6Code : GKR.Fold.ExtCode :=
  GKR.Fold.ExtCode.overPrime 8380417 24 6 7

/-- **The code arithmetic of `F_q^11`** (`GKR.Fold.ExtCode.overPrime`): `MlDsaField11 =
NativeWide<Fp24, 11, 2, …>` (`lib/algebra/fp_native_wide.h:631`) packs coefficient `i` in
`kCoefficientBits = 23` bits at bit `23 i` (`lib/algebra/fp_native_wide.h:64`, `:388`), so a code is
`Σ_i c_i 2^(23 i)` with `c_i` the coefficient of `X^i`; the arithmetic modulo `8380417` on each of
the `11` coefficients, `X^11 = 2`. -/
def fq11Code : GKR.Fold.ExtCode :=
  GKR.Fold.ExtCode.overPrime 8380417 23 11 2

/-- **The code arithmetic of Goldilocks²** (`GKR.Fold.ExtCode.overPrime`): `Fp64G2`
(`lib/algebra/fp_goldilocks.h:402`) writes the coefficients of `1` and `X` as eight bytes each
(`lib/algebra/fp_goldilocks.h:188`), so a code is `Σ_i c_i 2^(64 i)` with `c_i` the coefficient of
`X^i`; the arithmetic modulo `18446744069414584321` on each of the `2` coefficients, `X^2 = 7`. -/
def gold2Code : GKR.Fold.ExtCode :=
  GKR.Fold.ExtCode.overPrime pGold 64 2 7

/-- **The code arithmetic of Goldilocks⁴** (`GKR.Fold.ExtCode.overPrime`): `Fp64G4`
(`lib/algebra/fp_goldilocks4.h:196`) writes coefficient `i` as eight bytes at byte `8 i`, so a code
is `Σ_i c_i 2^(64 i)` with `c_i` the coefficient of `X^i`; the arithmetic modulo
`18446744069414584321` on each of the `4` coefficients, `X^4 = 7`. -/
def gold4Code : GKR.Fold.ExtCode :=
  GKR.Fold.ExtCode.overPrime pGold 64 4 7

/-- **The code arithmetic of `F_q^9`** (`GKR.Fold.ExtCode.overPrime`): `Fp14_9 = Fp14_N<9, 2>`
(`lib/algebra/fp14_n.h:286`, `:397`) writes coefficient `i` as `Fp14`'s two bytes
(`lib/algebra/fp14.h:280`) at byte `2 i`, so a code is `Σ_i c_i 2^(16 i)` with `c_i` the
coefficient of `X^i`; the arithmetic modulo `12289` on each of the `9` coefficients, `X^9 = 2`. -/
def fq9Code : GKR.Fold.ExtCode := GKR.Fold.ExtCode.overPrime 12289 16 9 2

open BinarySpread in
set_option exponentiation.threshold 20000 in
/-- The spread representation of `GF(2^128)`'s code arithmetic: `gf2_128Exec`'s reduction with
digits of `130` bits (`GKR.Fold.BinCode`: `k ≥ n + 2`). -/
def gf2_128CodeExec : Exec where
  k := 130
  n := 128
  tapN := 1 + 2 ^ 130 + 2 ^ 260 + 2 ^ 910
  mask := (2 ^ (130 * 128) - 1) / (2 ^ 130 - 1)

set_option exponentiation.threshold 20000 in
/-- **The code arithmetic of `GF(2^128)`** (`GKR.Fold.BinCode.arith`): exclusive or, and one spread
product per multiplication. -/
def gf2_128Code : GKR.Fold.BinCode := ⟨gf2_128CodeExec, (2 ^ (129 * 128) - 1) / (2 ^ 129 - 1)⟩

open BinarySpread in
set_option exponentiation.threshold 70000 in
/-- The spread representation of `GF(2^256)`'s code arithmetic: `gf2_256Exec`'s reduction with
digits of `258` bits (`GKR.Fold.BinCode`: `k ≥ n + 2`). -/
def gf2_256CodeExec : Exec where
  k := 258
  n := 256
  tapN := 1 + 2 ^ (2 * 258) + 2 ^ (5 * 258) + 2 ^ (10 * 258)
  mask := (2 ^ (258 * 256) - 1) / (2 ^ 258 - 1)

set_option exponentiation.threshold 70000 in
/-- **The code arithmetic of `GF(2^256)`** (`GKR.Fold.BinCode.arith`): exclusive or, and one spread
product per multiplication. -/
def gf2_256Code : GKR.Fold.BinCode := ⟨gf2_256CodeExec, (2 ^ (257 * 256) - 1) / (2 ^ 257 - 1)⟩

/-- **The code arithmetic of the quartic step `F_q[u]/(u^4 - 11)` of `F_q^20`**
(`GKR.Fold.ExtCode.overPrime`): four coefficients of `14` bits, the arithmetic modulo `12289` on
each, `u^4 = 11`. -/
def fq20QuarticCode : GKR.Fold.ExtCode := GKR.Fold.ExtCode.overPrime 12289 14 4 11

/-- **The code arithmetic of `F_q^20`** (`GKR.Fold.ExtCode`): five coefficients of `56` bits, in
`v^0, …, v^4`, over the quartic step's code arithmetic (`fq20QuarticCode`), `v^5 = u + 2` (code
`2 + 2^14`). Its codes are the C++ encoding: `FalconField20 = NativeWide<Fp14, 20, 11, 2, …, true>`
(`lib/algebra/fp_native_wide.h:628`) packs coordinate `e[4 j + i]`, the coefficient of `u^i v^j`
(`lib/algebra/fp_native_wide.h:45`), in `kCoefficientBits = 14` bits at bit `14 (4 j + i)`
(`lib/algebra/fp_native_wide.h:64`, `:388`), so bits `56 j` to `56 j + 55` are the quartic code of
the coefficient of `v^j`. -/
def fq20Code : GKR.Fold.ExtCode := ⟨fq20QuarticCode.arith, 56, 5, 16386⟩

end GordieHowe.RealizedProgram
