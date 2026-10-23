-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.System.Params
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.Language.Realizations.ModEquality
public import GordieHowe.Foundations.Fields.GoldilocksQuartic

@[expose] public section

/-!
# ML-DSA emulated: the parameters

The parameters of the ML-DSA-44 emulated proof of possession as the C++ compiles it
(`lib/gordiehowe/examples/mldsa/mldsa_emulated.h`, with the shared gadgets in `examples/mldsa/mldsa_gadgets.h`
and the hashes of domain H in `examples/mldsa/mldsa_hash.h`; `msgLen = 32`, an empty context), in one
place: the range table, the signature relation's modular equality in its committed-digit form (its
interval, quotient span, digit count and base), and comments recording the range requests, the MAC
equality at the characteristic of Goldilocks, the domains and domain A's Ligero tableaus.

Domain H, the MAC's field, the layout and the phases are ML-DSA native's: the hash constraints
(`mldsa_hash_side`) and the crossing are the same gadgets, and the plans' domain H agrees with the
native plans' (equal circuit ids). So the field profile is native's `GordieHowe.MLDSA44.Native.Params.Profile`
(the MAC field: width, taps, `convMax`), and the MAC's chunk count is native's `Profile.nch`. The
field of domain A is Goldilocks⁴ at the QROM parameters and Goldilocks² at the ROM parameters (characteristic `pGold`, masking
subfield `F_p`).

Names are the C++'s scoped node names (`signature.w`, `signature.relation.d0`, `alpha:A`, …),
as in the generated plan data (`GordieHowe/Generated/MLDSA44/Emulated/{QROMParams,ROMParams}/Plan.lean`). Citations are
`file:line` at `28705d8e`, relative to `lib/gordiehowe/` unless they name another directory.
-/

namespace GordieHowe.MLDSA44.Emulated.Params

open scoped NNReal
open Native.Params (q N nRows nCols τ dBits γ₂ r1Bits normBound crossBits wDim normOffset normHonest nSamples)

/-! ## The range table and requests

One table `[0, 4096)` (`examples/mldsa/mldsa_emulated.h`, `kT`; `:166-176`, `compile_profile`). The
requests of domain A in declaration order (`examples/mldsa/mldsa_emulated.h`): `signature.w`
(`:200`, `w'` below `T^2`), `norm.z` (`mldsa_gadgets.h:353-354`), `hint.offset`, `hint.slack` and
`hint.nowrap` (`mldsa_gadgets.h:430-434`), `hint_weight.weight` (`mldsa_gadgets.h:442-443`), the
MAC's `mac.low`, `mac.high` and `mac.nowrap` (`mod.h`, `digits`), and the signature relation's
three quotient digits `signature.relation.d0`, `d1`, `d2` (`mod.h:541-650`, `committed_digits`).
The planner realizes `signature.w`, `hint.offset` and `hint.slack` as two digits each, bound to
them, `norm.z` two-sided with two digits and binds `z` to them, `hint.nowrap` and `mac.nowrap`
implied, `hint_weight.weight` as one complement needle, the MAC's limbs direct late, and the
relation's digits direct. -/

/-- The range table size `T = 4096` (`examples/mldsa/mldsa_emulated.h`, `kT`). -/
abbrev T : ℕ := 4096

/-- `signature.w`'s, `hint.offset`'s and `hint.slack`'s honest bound and maximum `T^2 = 16777216`
(`examples/mldsa/mldsa_emulated.h`, `mldsa_gadgets.h:430-431`). -/
abbrev wBound : ℕ := T * T

/-! ## The signature relation

`signature_relation` (`examples/mldsa/mldsa_emulated.h`): `w'` committed below `T^2` and
`assert_mod(w' + 2^d PolyBroadcast(t1)(support - 2 sign), PolyMatVec(a)(z), q)` over the integers,
`t1`'s coefficients below `2^10` and `a`'s below `q` (`EntryBound`), `z` read through its two-sided
norm digits (`z ∈ [-(γ₁ - β - 1), γ₁ - β - 1]`). Both operators are signed, so each maps its Bit
operand to `±absRowSum` with `absRowSum = L n (b - 1)` (`OpSpec::abs_row_sum`). No circuit reads
either side of the congruence, so `mod.h` lowers it in the committed-digit form (`mod.h:541-650`):
`k` the least with `T^k > Qmax`, `B` the least with `B^k > Qmax`, the digits committed, each
requested below `B` with maximum `Dmax`, and the row `lhs - rhs - q qlo - q Σ_j B^j d_j = 0` per
coordinate. -/

/-- `t1`'s coefficient bound `2^10` (`examples/mldsa/mldsa_emulated.h`, `kT1Bound`). -/
abbrev t1Bound : ℕ := 2 ^ 10

/-- The row sum of `PolyBroadcast(t1)`, `L n (b - 1) = N (2^10 - 1) = 261888` with `L = 1` (the
plan's `absRowSum` of both `poly_broadcast` op bounds). -/
abbrev broadcastRowSum : ℕ := N * (t1Bound - 1)

/-- The row sum of `PolyMatVec(a)`, `L n (q - 1) = 8581545984` (the plan's `absRowSum` of
`poly_mat_vec(z)`). -/
abbrev matVecRowSum : ℕ := nCols * N * (q - 1)

/-- The magnitude bound of the left side's two broadcast terms, `2^d r + 2^(d+1) r` for the row sum
`r = broadcastRowSum`. -/
abbrev sigBroadcastBound : ℕ := 2 ^ dBits * broadcastRowSum + 2 ^ (dBits + 1) * broadcastRowSum

/-- The magnitude bound of the right side `PolyMatVec(a)(z)`, `matVecRowSum · (γ₁ - β - 1)`. -/
abbrev sigRhsBound : ℕ := matVecRowSum * (normBound - 1)

/-- **The lower end of `lhs - rhs`**, `-(2^d r + 2^(d+1) r + matVecRowSum (γ₁ - β - 1))`
(`-1124128889241600`; the plan's `intervalLo`). -/
abbrev sigLo : ℤ := -((sigBroadcastBound : ℤ) + sigRhsBound)

/-- **The upper end of `lhs - rhs`**, `(T^2 - 1) + 2^d r + 2^(d+1) r + matVecRowSum (γ₁ - β - 1)`
(`1124128906018815`; the plan's `intervalHi`). -/
abbrev sigHi : ℤ := ((wBound - 1 : ℕ) : ℤ) + sigBroadcastBound + sigRhsBound

/-- **The quotient's lower end** `qlo = ⌈sigLo / q⌉ = -134137583` (`mod.h:292-304`,
`quotient_shape`; the formula of `ModEquality.qlo`). -/
abbrev sigQlo : ℤ := -((-sigLo) / (q : ℤ))

/-- **The quotient's span** `Qmax = ⌊sigHi / q⌋ - qlo = 268275168` (`mod.h:292-304`; the formula of
`ModEquality.qmax`). -/
abbrev sigQmax : ℕ := (sigHi / (q : ℤ) - sigQlo).toNat

/-- The quotient digits `k = 3`, the least with `T^k > Qmax` (`mod.h:569-571`). -/
abbrev sigDigits : ℕ := 3

/-- The digits' base `B = 645`, the least with `B^3 > Qmax` (`mod.h:569`, `:582-594`). -/
abbrev sigBase : ℕ := 645

theorem sigLo_eq : sigLo = -1124128889241600 := by decide

theorem sigHi_eq : sigHi = 1124128906018815 := by decide

theorem sigQlo_eq : sigQlo = -134137583 := by decide

theorem sigQmax_eq : sigQmax = 268275168 := by decide

/-- **The digits cover the quotient**: `Qmax < B^k`, the capacity condition of the
committed-digit form. -/
theorem sigQmax_lt : sigQmax < sigBase ^ sigDigits := by decide

/-! ## The MAC equality at the characteristic `pGold`

The MAC's group, its digit base `B` and radix `2 B` are native's; what
depends on the characteristic of domain A is the limbs' maximum `Dmax` (`mod.h:469-477`) and the
no-wrap request's maximum `p - 1`; the table size moves the no-wrap interval. -/

/-! ## The range table's capacity

`group_capacity` (`range.h:1486-1497`): the least of `p - 1` and, when `log₂|K| - 100 < 120`, the
screen's `⌊2^(log₂|K| - 100)⌋ - (2T - 1)`, computed in floating point. At the QROM parameters (`|K| = p^4`) the
screen is skipped; at the ROM parameters (`|K| = p^2`, `log₂|K|` just below `128`) it gives
`(2^28 - 1) - (2T - 1) = 268427264`. -/

/-! ## The domains

Domain H is native's. Domain A's circuit sizes are the plan data's. -/

/-! ## The extended Fiat–Shamir points

Domain H's are native's. Domain A has no inner stage: its root combination draws one weight per row
slot (its GKR layers, the input row and its affine rows) and its Ligero test one per linear row (the
root's measurements and its combined row; `TreePlan::stream_rows`). -/

/-! ## The Ligero tableaus of domain A

Ligero with an agreement threshold within the Johnson radius and the mask test, over the relatively
packed commitment of domain A, at these
tableaus. Domain H's tableaus are native's (section comments of `GordieHowe/Applications/MLDSA44/System/Params.lean`).

* **QROM parameters** (Goldilocks⁴): domain A's tableau of the emulated Falcon-512 program at the QROM
  parameters (`(rate, block_enc) = (6, 8191)`,
  `(N, k) = (6144, 1024)`, `t = 214`, `A = 2918`, `B = 1020592`);
* **ROM parameters** (Goldilocks²): `(7, 9215)`, `(N, k) = (7168, 1024)`, `t = 93`, the weighted Johnson
  certificate `(m, B, H) = (2, 5, 17)` at `A = 3226` (`B = 903689`).

The code is `k = (block_enc + 1) / (2 + rate)`, `N = block_enc − (2k − 1)`
(`../ligero/ligero_param.h`, `LigeroParam`). -/

end GordieHowe.MLDSA44.Emulated.Params
