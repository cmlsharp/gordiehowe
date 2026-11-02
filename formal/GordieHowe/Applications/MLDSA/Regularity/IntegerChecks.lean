-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# Integer checks of the small-support bounds

The exact integer inequalities behind the small-support bounds of the HighBits regularity
argument ("A shorter proof of the stated HighBits regularity claim", 10 September 2026,
Section 4, equation (10) and the endpoint checks after table (14a)). Here `q = 8380417` is the
ML-DSA modulus (FIPS 204, Section 4) and `L₀ = 190307 = 2(γ₂ - β) - 1` at ML-DSA-44, the
smallest accepted cell size of the three parameter sets.

Each check `(a · d)^a · q^r < (2 L₀)^a` says `a q^(r/a) / (2 L₀) < 1/d`, the base of the
determinant bound `δ_{a,s} < q^r (a q^(r/a) / (2L₀))^s` (note, (9)) at length `a` and support
size `r`. The endpoint checks use the Hadamard form `√a` in place of `a`.
-/

namespace GordieHowe.MLDSA.Regularity

/-- The ML-DSA modulus `q = 8380417` is prime. -/
theorem modulus_prime : Nat.Prime 8380417 := by norm_num

/-- Note (10), `(a, r) = (2, 1)`: `2 q^(1/2) / (2L₀) < 1/64`. -/
theorem check_2_1 : (2 * 64) ^ 2 * 8380417 < (2 * 190307) ^ 2 := by norm_num

/-- Note (10), `(a, r) = (4, 2)`: `4 q^(1/2) / (2L₀) < 1/32`. -/
theorem check_4_2 : (4 * 32) ^ 4 * 8380417 ^ 2 < (2 * 190307) ^ 4 := by norm_num

/-- Note (10), `(a, r) = (8, 3)`: `8 q^(3/8) / (2L₀) < 1/64`. -/
theorem check_8_3 : (8 * 64) ^ 8 * 8380417 ^ 3 < (2 * 190307) ^ 8 := by norm_num

/-- Note (10), `(a, r) = (8, 4)`: `8 q^(1/2) / (2L₀) < 1/16`. -/
theorem check_8_4 : (8 * 16) ^ 8 * 8380417 ^ 4 < (2 * 190307) ^ 8 := by norm_num

/-- Note, first (14a) endpoint (`r = 1`, budget `16`, length `2`): `√(2q) / (2L₀) < 1/64`. -/
theorem endpoint_1 : 2 * 8380417 * 64 ^ 2 < (2 * 190307) ^ 2 := by norm_num

/-- Note, (14a) endpoint `r = 2` (budget `32`, length `4`): `4^4 q^6 / (2L₀)^8 < 1/4`. -/
theorem endpoint_2 : 4 * (4 ^ 4 * 8380417 ^ 6) < (2 * 190307) ^ 8 := by norm_num

/-- Note, (14a) endpoint `r = 3` (budget `64`, length `8`): `8^4 q^6 / (2L₀)^8 < 13/4`. -/
theorem endpoint_3 : 4 * (8 ^ 4 * 8380417 ^ 6) < 13 * (2 * 190307) ^ 8 := by norm_num

/-- Note, (14a) endpoint `r = 4` (budget `128`, length `8`): `8^8 q^12 / (2L₀)^16 < 11`. -/
theorem endpoint_4 : 8 ^ 8 * 8380417 ^ 12 < 11 * (2 * 190307) ^ 16 := by norm_num

/-- Note, (14a) endpoint `r = 5` (budget `256`, length `16`): `16^8 q^10 / (2L₀)^16 < 1`. -/
theorem endpoint_5 : 16 ^ 8 * 8380417 ^ 10 < (2 * 190307) ^ 16 := by norm_num

end GordieHowe.MLDSA.Regularity
