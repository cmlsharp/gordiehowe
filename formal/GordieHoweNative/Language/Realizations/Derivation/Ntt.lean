-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Basic
public import GordieHoweNative.Language.RealizedProgram.Locality

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Ntt`

The definitions of `GordieHowe.Language.Realizations.Derivation.Ntt` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Ntt.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The broadcast of a block of `m` coordinates to `K` blocks**: entry `u` is `u mod m`. -/
def bcastMap (K m : ℕ) : IndexMap := List.replicate K (0, 1, m)

/-- **The terms of a polynomial matrix-vector product, grouped by output coordinate**: the
products of block `(i, l)` (`(i L + l) n + s`) reordered so that the `L` terms of output
coordinate `i n + s` are consecutive, entry `(i n + s) L + l` the term `(i L + l) n + s`. -/
def matPerm (K L n : ℕ) : IndexMap :=
  (List.range (K * n)).flatMap fun q => [(q / n * (L * n) + q % n, (n : ℤ), L)]

/-- **The root `ψ` and the size `n` of a transform check** at the characteristic `p`: `n = 2^k`
below `p > 2`, `0 < n`, `ψ < p` and `ψ^n ≡ −1 (mod p)`. -/
def rootOkB (p n psi : ℕ) : Bool :=
  decide (2 < p ∧ psi < p ∧ 0 < n ∧ n < p ∧ n = 2 ^ Nat.log2 n ∧ psi ^ n % p = p - 1)

section

variable (ir : RealizedProgram)

/-- **The transform instances of `linop`** in domain `d` of characteristic `p`. -/
def nttFact (d : ℕ) : LinOpStep → Option Fact
  | .nttInv n psi x =>
    if d < ir.domains.length ∧ rootOkB (ir.charOf (ir.domainField d)) n psi = true then
      some (.eq d (.apply (.inverseNtt n psi) (.apply (.ntt n psi .scheme) x)) x)
    else none
  | .inttInv n psi y =>
    if d < ir.domains.length ∧ rootOkB (ir.charOf (ir.domainField d)) n psi = true then
      some (.eq d (.apply (.ntt n psi .scheme) (.apply (.inverseNtt n psi) y)) y)
    else none
  | .convNtt h psi x =>
    if d < ir.domains.length ∧
        rootOkB (ir.charOf (ir.domainField d)) (ir.value h).size psi = true ∧
        ir.exprLen x = (ir.value h).size then
      some (.eq d (.apply (.negacyclicConv h (.ntt psi)) x)
        (.apply (.inverseNtt (ir.value h).size psi)
          (.mul (.leaf h) (.apply (.ntt (ir.value h).size psi .scheme) x))))
    else none
  | .convCoef h psi x =>
    if d < ir.domains.length ∧
        rootOkB (ir.charOf (ir.domainField d)) (ir.value h).size psi = true ∧
        ir.exprLen x = (ir.value h).size then
      some (.eq d (.apply (.ntt (ir.value h).size psi .scheme)
          (.apply (.negacyclicConv h .coefficients) x))
        (.mul (.apply (.ntt (ir.value h).size psi .scheme) (.leaf h))
          (.apply (.ntt (ir.value h).size psi .scheme) x)))
    else none
  | .transposeInv n psi psi' x =>
    if d < ir.domains.length ∧ rootOkB (ir.charOf (ir.domainField d)) n psi = true ∧
        psi' < ir.charOf (ir.domainField d) ∧ psi * psi' % ir.charOf (ir.domainField d) = 1 then
      some (.eq d (.apply (.nttTranspose n psi') (.apply (.ntt n psi .natural) x))
        (.scale (.const n) x))
    else none
  | .convBcastNtt t K psi x =>
    if d < ir.domains.length ∧
        rootOkB (ir.charOf (ir.domainField d)) ((ir.value t).size / K) psi = true ∧
        (ir.value t).size = K * ((ir.value t).size / K) ∧
        ir.exprLen x = (ir.value t).size / K then
      some (.eq d (.apply (.polyBroadcast t K (.ntt psi)) x)
        (.apply (.inverseNtt ((ir.value t).size / K) psi)
          (.mul (.leaf t) (.reindex (bcastMap K ((ir.value t).size / K))
            (.apply (.ntt ((ir.value t).size / K) psi .scheme) x)))))
    else none
  | .convMatNtt a K L psi x =>
    if d < ir.domains.length ∧
        rootOkB (ir.charOf (ir.domainField d)) ((ir.value a).size / (K * L)) psi = true ∧
        (ir.value a).size = K * L * ((ir.value a).size / (K * L)) ∧ 0 < L ∧
        ir.exprLen x = L * ((ir.value a).size / (K * L)) then
      some (.eq d (.apply (.polyMatVec a K L (.ntt psi)) x)
        (.apply (.inverseNtt ((ir.value a).size / (K * L)) psi)
          (.apply (.sum L) (.reindex (matPerm K L ((ir.value a).size / (K * L)))
            (.mul (.leaf a) (.reindex (bcastMap K (L * ((ir.value a).size / (K * L))))
              (.apply (.ntt ((ir.value a).size / (K * L)) psi .scheme) x)))))))
    else none
  | .adjoint n psi y x =>
    if 0 < n ∧ ir.exprLen y = n ∧ ir.exprLen x = n then
      some (.eq d (.apply (.sum n) (.mul (.apply (.nttTranspose n psi) y) x))
        (.apply (.sum n) (.mul y (.apply (.ntt n psi .natural) x))))
    else none
  | _ => none

end

end GordieHowe.RealizedProgram
