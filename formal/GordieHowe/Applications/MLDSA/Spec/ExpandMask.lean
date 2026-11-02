-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Spec.ExpandS
public import GordieHowe.Applications.MLDSA.Signing.Ideal

@[expose] public section

/-!
# The FIPS 204 `ExpandMask`

The vendored concrete primitives (`concretePrimitives`) give `expandMask` an all-zero placeholder
body. This file defines `ExpandMask` (FIPS 204 Algorithm 34) on the vendored SHAKE256
(`shake256List`) and the vendored `BitUnpack` (Algorithm 19, `bitUnpackPoly`), and the concrete
primitives with both the FIPS 204 `ExpandS` and the FIPS 204 `ExpandMask`.

* `expandMaskWidth`, `expandMaskSeed`, `expandMaskPoly`, `expandMask`: the algorithm.
* `expandMaskPoly_mem`, `expandMask_inMaskBox`, `expandMaskBox`: at every approved parameter set
  every output coefficient has centered representative in `(-γ₁, γ₁]`, so the output lies in the
  mask box `MaskBox p` of `Signing/Ideal.lean`, for every seed and counter.
* `concretePrimitivesFIPS`: `concretePrimitivesKeyGen p` with this `expandMask`.
* `withExpandMask`, `SigningLaws.withExpandMask`, `highBitsVec_withExpandMask`,
  `keyGenFromSeed_withExpandMask_snd`: replacing `expandMask` in an abstract bundle keeps the
  signing laws, `HighBits` and the generated secret key.
* `keyGenFromSeed_s1_bounded_fips`, `keyGenFromSeed_s2_bounded_fips`: keys of
  `concretePrimitivesFIPS` have `‖s₁‖∞, ‖s₂‖∞ ≤ η`.
-/

namespace GordieHowe.MLDSA.Spec

open _root_.MLDSA _root_.MLDSA.Concrete LatticeCrypto

/-! ### The algorithm -/

/-- The bit width `c = 1 + bitlen(γ₁ - 1)` of FIPS 204 Algorithm 34, line 1 (`simpleWidth b` is
`bitlen b` for `b ≥ 1`). -/
def expandMaskWidth (p : Params) : ℕ := 1 + simpleWidth (p.gamma1 - 1)

/-- The `ExpandMask` seed of polynomial index `n = κ + r`: `ρ'' ‖ IntegerToBytes(n, 2)`,
little-endian (FIPS 204 Algorithm 34, line 4). -/
def expandMaskSeed (rhoDoublePrime : Bytes 64) (n : ℕ) : List Byte :=
  byteArrayToList (vectorToByteArray rhoDoublePrime) ++ [n.toUInt8, (n / 256).toUInt8]

/-- One polynomial of `ExpandMask` (FIPS 204 Algorithm 34, lines 3–6): squeeze `32c` bytes of
SHAKE256 on `expandMaskSeed ρ'' n` and decode them with `BitUnpack(·, γ₁ - 1, γ₁)`
(Algorithm 19, the vendored `bitUnpackPoly` with range `[-γ₁ + 1, γ₁]`, as in `polyZUnpack p`:
coefficients `γ₁ - v` for values `v` of `bitlen(2γ₁ - 1)` bits). -/
def expandMaskPoly (p : Params) (rhoDoublePrime : Bytes 64) (n : ℕ) : Rq :=
  bitUnpackPoly (shake256List (expandMaskSeed rhoDoublePrime n) (32 * expandMaskWidth p))
    (-(p.gamma1 : ℤ) + 1) p.gamma1

/-- `ExpandMask(ρ'', κ)` (FIPS 204 Algorithm 34):
`y[r] = BitUnpack(H(ρ'' ‖ IntegerToBytes(κ + r, 2), 32c), γ₁ - 1, γ₁)` for `r < ℓ`
(`expandMaskPoly`). -/
def expandMask (p : Params) (rhoDoublePrime : Bytes 64) (kappa : ℕ) : RqVec p.l :=
  Vector.ofFn fun r : Fin p.l => expandMaskPoly p rhoDoublePrime (kappa + r.val)

/-! ### The range -/

/-- **`ExpandMask` coefficients lie in `(-γ₁, γ₁]`**: at every approved parameter set every
coefficient of `expandMaskPoly p ρ'' n` has centered representative in `(-γ₁, γ₁]`, for every seed
and index. -/
theorem expandMaskPoly_mem {p : Params} (hp : p.isApproved) (rhoDoublePrime : Bytes 64) (n : ℕ)
    (i : Fin ringDegree) :
    -(p.gamma1 : ℤ) < centeredRepr ((expandMaskPoly p rhoDoublePrime n).get i) ∧
      centeredRepr ((expandMaskPoly p rhoDoublePrime n).get i) ≤ p.gamma1 := by
  obtain ⟨hwidth, hq⟩ := approved_gamma1_width p hp
  obtain ⟨v, hv, hget⟩ := bitUnpackPoly_get
    (shake256List (expandMaskSeed rhoDoublePrime n) (32 * expandMaskWidth p))
    (-(p.gamma1 : ℤ) + 1) (p.gamma1 : ℤ) i
  rw [hwidth] at hv
  have hbound : ((p.gamma1 : ℤ) - (v : ℤ)).natAbs ≤ p.gamma1 := by omega
  rw [expandMaskPoly, hget, centeredRepr_intCast_eq_of_natAbs_le _ hbound hq]
  omega

/-- **`ExpandMask` lands in the mask box**: at every approved parameter set
`ExpandMask(ρ'', κ)` lies in `InMaskBox γ₁`, the range of `MaskBox p`, for every `ρ''` and `κ`. -/
theorem expandMask_inMaskBox {p : Params} (hp : p.isApproved) (rhoDoublePrime : Bytes 64)
    (kappa : ℕ) : InMaskBox p.gamma1 (expandMask p rhoDoublePrime kappa) := by
  intro j i
  simp only [expandMask, Vector.get_ofFn]
  exact expandMaskPoly_mem hp _ _ i

/-- `ExpandMask(ρ'', κ)` as an element of `MaskBox p` (`expandMask_inMaskBox`). -/
def expandMaskBox {p : Params} (hp : p.isApproved) (rhoDoublePrime : Bytes 64) (kappa : ℕ) :
    MaskBox p :=
  ⟨expandMask p rhoDoublePrime kappa, expandMask_inMaskBox hp rhoDoublePrime kappa⟩

/-! ### Replacing `ExpandMask` in an abstract bundle

Stated over an abstract `P : Primitives p`, so that instantiating at the concrete bundles never
unfolds a concrete primitive during a definitional check. -/

/-- The primitives `P` with `ExpandMask` (FIPS 204 Algorithm 34) replaced by `eM`. -/
abbrev withExpandMask {p : Params} (P : Primitives p) (eM : Bytes 64 → ℕ → RqVec p.l) :
    Primitives p :=
  { P with expandMask := eM }

/-- **Replacing `ExpandMask` keeps the signing laws**: none of the three fields reads
`expandMask`. -/
theorem _root_.GordieHowe.MLDSA.SigningLaws.withExpandMask {p : Params} [NTTRingOps]
    {P : Primitives p} (h : SigningLaws P) (eM : Bytes 64 → ℕ → RqVec p.l) :
    SigningLaws (withExpandMask P eM) :=
  ⟨h.transform, h.hide_low, h.sampleInBall_smul_bound⟩

/-- Replacing `ExpandMask` keeps `HighBits`. -/
theorem highBitsVec_withExpandMask {p : Params} (P : Primitives p)
    (eM : Bytes 64 → ℕ → RqVec p.l) (w : RqVec p.k) :
    (withExpandMask P eM).highBitsVec w = P.highBitsVec w :=
  rfl

/-- Replacing `ExpandMask` keeps the secret key of key generation (FIPS 204 Algorithm 6 reads no
`ExpandMask`). -/
theorem keyGenFromSeed_withExpandMask_snd {p : Params} [NTTRingOps] (P : Primitives p)
    (eM : Bytes 64 → ℕ → RqVec p.l) (seed : Bytes 32) :
    (keyGenFromSeed p (withExpandMask P eM) seed).2 = (keyGenFromSeed p P seed).2 :=
  rfl

/-! ### The FIPS 204 bundle -/

/-- **The concrete primitives with the FIPS 204 `ExpandS` and `ExpandMask`**: `concretePrimitives p`
with its placeholder `expandS` replaced by `expandS` (Algorithm 33) and its placeholder
`expandMask` by `expandMask` (Algorithm 34). -/
def concretePrimitivesFIPS (p : Params) : Primitives p :=
  withExpandMask (concretePrimitivesKeyGen p) (expandMask p)

/-- `concretePrimitivesFIPS` reads its `expandMask` from `expandMask`. -/
theorem concretePrimitivesFIPS_expandMask (p : Params) :
    (concretePrimitivesFIPS p).expandMask = expandMask p :=
  rfl

/-- `concretePrimitivesFIPS` reads its `expandS` from `expandS`. -/
theorem concretePrimitivesFIPS_expandS (p : Params) :
    (concretePrimitivesFIPS p).expandS = expandS p :=
  rfl

/-- Keys of `concretePrimitivesFIPS` have `‖s₁‖∞ ≤ η`, for every seed. -/
theorem keyGenFromSeed_s1_bounded_fips {p : Params} [NTTRingOps] (hp : p.isApproved)
    (seed : Bytes 32) :
    polyVecBounded (keyGenFromSeed p (concretePrimitivesFIPS p) seed).2.s1 p.eta := by
  rw [concretePrimitivesFIPS, keyGenFromSeed_withExpandMask_snd]
  exact keyGenFromSeed_s1_bounded hp seed

/-- Keys of `concretePrimitivesFIPS` have `‖s₂‖∞ ≤ η`, for every seed. -/
theorem keyGenFromSeed_s2_bounded_fips {p : Params} [NTTRingOps] (hp : p.isApproved)
    (seed : Bytes 32) :
    polyVecBounded (keyGenFromSeed p (concretePrimitivesFIPS p) seed).2.s2 p.eta := by
  rw [concretePrimitivesFIPS, keyGenFromSeed_withExpandMask_snd]
  exact keyGenFromSeed_s2_bounded hp seed

end GordieHowe.MLDSA.Spec
