-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.MLDSA.ConcretePrimitives
public import LatticeCrypto.MLDSA.Concrete.LawBounds
public import LatticeCrypto.MLDSA.Scheme

@[expose] public section

/-!
# The FIPS 204 `ExpandS`

The vendored concrete primitives (`concretePrimitives`) give `expandS` an all-zero placeholder
body. This file defines `ExpandS` (FIPS 204 Algorithm 33) with `RejBoundedPoly` (Algorithm 31)
and `CoeffFromHalfByte` (Algorithm 15), on the vendored SHAKE256 (`shake256List`), with a
bounded XOF stream of `rejBoundedPolyByteBudget = 481` bytes per polynomial, the minimum
allowable limit of FIPS 204 Appendix C, Table 3.

* `coeffFromHalfByte`, `rejBoundedPoly?`, `rejBoundedPoly`, `expandS`: the algorithms.
* `rejBoundedPoly_bounded`, `expandS_bounded`: every output coefficient has centered
  representative in `[-η, η]`, for every seed.
* `concretePrimitivesKeyGen`: `concretePrimitives p` with this `expandS`;
  `keyGenFromSeed_s1_bounded`, `keyGenFromSeed_s2_bounded`: its keys have `‖s₁‖∞, ‖s₂‖∞ ≤ η`.
-/

namespace GordieHowe.MLDSA.Spec

open _root_.MLDSA _root_.MLDSA.Concrete

/-- `CoeffFromHalfByte(b)` (FIPS 204 Algorithm 15): for `η = 2`, `2 - (b mod 5)` when `b < 15`;
for `η = 4`, `4 - b` when `b < 9`; `none` (⊥) otherwise, and for every other `η`. -/
def coeffFromHalfByte (eta b : ℕ) : Option ℤ :=
  if eta = 2 ∧ b < 15 then some (2 - ((b % 5 : ℕ) : ℤ))
  else if eta = 4 ∧ b < 9 then some (4 - (b : ℤ))
  else none

/-- `CoeffFromHalfByte` returns integers in `[-η, η]`. -/
theorem natAbs_le_of_coeffFromHalfByte {eta b : ℕ} {z : ℤ}
    (h : coeffFromHalfByte eta b = some z) : z.natAbs ≤ eta := by
  unfold coeffFromHalfByte at h
  split_ifs at h with h1 h2
  · obtain ⟨rfl, -⟩ := h1
    cases h
    have : b % 5 < 5 := Nat.mod_lt _ (by norm_num)
    omega
  · obtain ⟨rfl, hb⟩ := h2
    cases h
    omega

/-- The accepted coefficients of `RejBoundedPoly` (FIPS 204 Algorithm 31, lines 4–16) in the
order the algorithm writes them: for each squeezed byte `z`, `CoeffFromHalfByte(z mod 16)` then
`CoeffFromHalfByte(⌊z / 16⌋)`, the rejected (⊥) ones dropped. Algorithm 31 writes the first 256
of these. -/
def rejBoundedCoeffs (eta : ℕ) (stream : List Byte) : List ℤ :=
  stream.flatMap fun z =>
    (coeffFromHalfByte eta (z.toNat % 16)).toList ++ (coeffFromHalfByte eta (z.toNat / 16)).toList

/-- Every accepted coefficient of `rejBoundedCoeffs` lies in `[-η, η]`. -/
theorem natAbs_le_of_mem_rejBoundedCoeffs {eta : ℕ} {stream : List Byte} {z : ℤ}
    (h : z ∈ rejBoundedCoeffs eta stream) : z.natAbs ≤ eta := by
  simp only [rejBoundedCoeffs, List.mem_flatMap, List.mem_append, Option.mem_toList] at h
  obtain ⟨_, _, h | h⟩ := h <;> exact natAbs_le_of_coeffFromHalfByte h

/-- The number of SHAKE256 bytes `rejBoundedPoly?` squeezes: 481, the minimum allowable limit
for `RejBoundedPoly` in FIPS 204 Appendix C, Table 3 (a failure probability of at most `2^-256`
under the standard XOF assumptions). -/
def rejBoundedPolyByteBudget : ℕ := 481

/-- `RejBoundedPoly(ρ)` (FIPS 204 Algorithm 31) with a bounded XOF stream: absorb the seed into
SHAKE256, squeeze `rejBoundedPolyByteBudget` bytes, and take the first 256 accepted coefficients
(`rejBoundedCoeffs`), or `none` if the stream holds fewer. Algorithm 31 squeezes until 256 are
accepted; Appendix C allows this bound, with the same failure value on every exhausted stream. -/
def rejBoundedPoly? (eta : ℕ) (seed : List Byte) : Option Rq :=
  let coeffs := rejBoundedCoeffs eta (byteArrayToList (shake256List seed rejBoundedPolyByteBudget))
  if h : ringDegree ≤ coeffs.length then
    some (Vector.ofFn fun i : Fin ringDegree => ((coeffs[i.val]'(by omega) : ℤ) : Coeff))
  else none

/-- The total `RejBoundedPoly`: `rejBoundedPoly?`, and `0` where the stream is exhausted. -/
def rejBoundedPoly (eta : ℕ) (seed : List Byte) : Rq :=
  (rejBoundedPoly? eta seed).getD 0

/-- An integer in `[-η, η]` with `η ≤ q / 2` is its own centered representative mod `q`. -/
theorem natAbs_centeredRepr_intCast_le {z : ℤ} {b : ℕ} (hz : z.natAbs ≤ b)
    (hb : b ≤ modulus / 2) : (LatticeCrypto.centeredRepr (z : Coeff)).natAbs ≤ b := by
  rw [LatticeCrypto.centeredRepr_eq_valMinAbs]
  have hq : (modulus : ℤ) = 8380417 := by norm_num [modulus]
  have hb' : (b : ℤ) ≤ 4190208 := by
    have : modulus / 2 = 4190208 := by norm_num [modulus]
    omega
  rw [(ZMod.valMinAbs_spec (z : Coeff) z).2 ⟨rfl, by omega, by omega⟩]
  exact hz

/-- **`RejBoundedPoly` is `η`-bounded**: every coefficient of `rejBoundedPoly η seed`, including
the failure value `0`, has centered representative in `[-η, η]`, for `η ≤ q / 2`. -/
theorem rejBoundedPoly_bounded {eta : ℕ} (heta : eta ≤ modulus / 2) (seed : List Byte) :
    polyBounded (rejBoundedPoly eta seed) eta := by
  unfold polyBounded
  rw [polyNorm_eq_cInfNorm, LatticeCrypto.cInfNorm_le_iff]
  intro i
  unfold rejBoundedPoly rejBoundedPoly?
  dsimp only
  split_ifs with h
  · show (LatticeCrypto.centeredRepr ((Vector.ofFn _ : Vector Coeff ringDegree).get i)).natAbs ≤
      eta
    rw [Vector.get_ofFn]
    exact natAbs_centeredRepr_intCast_le
      (natAbs_le_of_mem_rejBoundedCoeffs (List.getElem_mem _)) heta
  · simp [LatticeCrypto.centeredRepr]

/-- The `ExpandS` seed of polynomial index `r`: `ρ′ ‖ IntegerToBytes(r, 2)`, little-endian. -/
def expandSSeed (rhoPrime : Bytes 64) (r : ℕ) : List Byte :=
  byteArrayToList (vectorToByteArray rhoPrime) ++ [r.toUInt8, (r / 256).toUInt8]

/-- `ExpandS(ρ′)` (FIPS 204 Algorithm 33): `s₁[r] = RejBoundedPoly(ρ′ ‖ IntegerToBytes(r, 2))`
for `r < ℓ` and `s₂[r] = RejBoundedPoly(ρ′ ‖ IntegerToBytes(r + ℓ, 2))` for `r < k`, with the
bounded `rejBoundedPoly`. -/
def expandS (p : Params) (rhoPrime : Bytes 64) : RqVec p.l × RqVec p.k :=
  (Vector.ofFn fun r : Fin p.l => rejBoundedPoly p.eta (expandSSeed rhoPrime r.val),
    Vector.ofFn fun r : Fin p.k => rejBoundedPoly p.eta (expandSSeed rhoPrime (r.val + p.l)))

/-- A vector of `η`-bounded polynomials is `η`-bounded. -/
theorem polyVecBounded_ofFn {k b : ℕ} {f : Fin k → Rq} (hf : ∀ i, polyBounded (f i) b) :
    polyVecBounded (Vector.ofFn f : RqVec k) b := by
  unfold polyVecBounded polyVecNorm
  rw [LatticeCrypto.PolyVec.cInfNorm_le_iff]
  intro j
  simpa [Vector.get_ofFn, polyBounded] using hf j

/-- **`ExpandS` is `η`-bounded**: `‖s₁‖∞ ≤ η` and `‖s₂‖∞ ≤ η` for every `ρ′`, at every parameter
set with `η ≤ q / 2` (all approved ones). -/
theorem expandS_bounded {p : Params} (heta : p.eta ≤ modulus / 2) (rhoPrime : Bytes 64) :
    polyVecBounded (expandS p rhoPrime).1 p.eta ∧ polyVecBounded (expandS p rhoPrime).2 p.eta :=
  ⟨polyVecBounded_ofFn fun _ => rejBoundedPoly_bounded heta _,
    polyVecBounded_ofFn fun _ => rejBoundedPoly_bounded heta _⟩

/-- Every approved parameter set has `η ≤ q / 2`. -/
theorem eta_le_half_of_isApproved {p : Params} (hp : p.isApproved) : p.eta ≤ modulus / 2 := by
  rcases hp with rfl | rfl | rfl <;> decide

/-- **The concrete primitives with the FIPS 204 `ExpandS`**: `concretePrimitives p` with its
placeholder `expandS` replaced by `expandS` (Algorithm 33). Its `expandMask` is still the
vendored all-zero placeholder; nothing that reads this bundle's keys reads `expandMask`. -/
def concretePrimitivesKeyGen (p : Params) : Primitives p :=
  { concretePrimitives p with expandS := expandS p }

/-- Keys of `concretePrimitivesKeyGen` have `‖s₁‖∞ ≤ η`, for every seed. -/
theorem keyGenFromSeed_s1_bounded {p : Params} [NTTRingOps] (hp : p.isApproved)
    (seed : Bytes 32) :
    polyVecBounded (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2.s1 p.eta :=
  (expandS_bounded (eta_le_half_of_isApproved hp) _).1

/-- Keys of `concretePrimitivesKeyGen` have `‖s₂‖∞ ≤ η`, for every seed. -/
theorem keyGenFromSeed_s2_bounded {p : Params} [NTTRingOps] (hp : p.isApproved)
    (seed : Bytes 32) :
    polyVecBounded (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2.s2 p.eta :=
  (expandS_bounded (eta_le_half_of_isApproved hp) _).2

end GordieHowe.MLDSA.Spec
