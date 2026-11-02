-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Applications.MLDSA.Regularity.T0Law

@[expose] public section

/-!
# `ExpandS` as a random oracle onto the `η`-box

`withExpandS prims G` replaces `ExpandS` (FIPS 204 Algorithm 33) by a random oracle
`G : {0,1}^512 → [-η, η]^{256 (ℓ + k)}` onto the coefficient arrays of the secrets
(`SecretCoeffs`), read as `(s₁, s₂)` by `secretOfCoeffs`, as `withExpandA` does for `ExpandA`.

* `withExpandS_bounded`: the secrets of `withExpandS` are `η`-bounded.
* `expect_withExpandS`: averaged over a uniform `G`, the secret of every `ρ'` is a uniform box
  secret.
* `ringRegGap_withExpandS`, `regGapAvg_withExpandS`: the regularity gap does not read `ExpandS`,
  so with both `ExpandA` and `ExpandS` random oracles the averaged gap is the gap averaged over a
  uniform seed, a uniform box secret and a uniform matrix.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity

variable {p : Params} (prims : Primitives p)

/-- **The primitives with `ExpandS` replaced by `G`**: the primitives of the game in which
`ExpandS` (FIPS 204 Algorithm 33) is a random oracle `G` onto the coefficient arrays of `η`-bounded
secrets. -/
noncomputable abbrev withExpandS (G : Bytes 64 → SecretCoeffs p) : Primitives p :=
  { prims with expandS := fun rhoPrime => secretOfCoeffs (G rhoPrime) }

/-- The secrets of `withExpandS` are `η`-bounded, for every `ρ'`. -/
theorem withExpandS_bounded (G : Bytes 64 → SecretCoeffs p) (rhoPrime : Bytes 64) :
    polyVecBounded ((withExpandS prims G).expandS rhoPrime).1 p.eta ∧
      polyVecBounded ((withExpandS prims G).expandS rhoPrime).2 p.eta :=
  secretOfCoeffs_bounded (G rhoPrime)

/-- **With `ExpandS` a random oracle, the secret of every `ρ'` is uniform on the box**:
`𝔼_G φ(G ρ') = 𝔼_e φ(e)` (`PMF.expect_apply_eval`). -/
theorem expect_withExpandS (rhoPrime : Bytes 64) (φ : SecretCoeffs p → ℝ) :
    𝔼 G : Bytes 64 → SecretCoeffs p, φ (G rhoPrime) = 𝔼 e, φ e :=
  PMF.expect_apply_eval rhoPrime φ

/-- **The regularity gap does not read `ExpandS`.** -/
theorem ringRegGap_withExpandS [NeZero (bucketCount p)] [NTTRingOps] [Nonempty (MaskBox p)]
    (G : Bytes 64 → SecretCoeffs p) (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (βmin : ℚ≥0) :
    ringRegGap (withExpandS prims G) sk aHat βmin = ringRegGap prims sk aHat βmin :=
  rfl

/-- **The averaged regularity gap with `ExpandS` a random oracle**: averaged over `G`,
`regGapAvg` of `withExpandS prims G` is the gap averaged over a uniform seed, a uniform box
secret `e` and a uniform matrix, at the key `idealSecretKey ρ K Â (secretOfCoeffs e)`. -/
theorem expect_regGapAvg_withExpandS [NeZero (bucketCount p)] [NTTRingOps] [Nonempty (MaskBox p)]
    (βmin : ℚ≥0) :
    𝔼 G : Bytes 64 → SecretCoeffs p, regGapAvg (withExpandS prims G) βmin =
      𝔼 seed : Bytes 32, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
        ringRegGap prims (idealSecretKey prims (prims.expandSeed seed).1
          (prims.expandSeed seed).2.2 aHat (secretOfCoeffs e)) aHat βmin := by
  unfold regGapAvg
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl fun seed _ => ?_
  exact expect_withExpandS (prims.expandSeed seed).2.1 fun e => 𝔼 aHat : TqMatrix p.k p.l,
    ringRegGap prims (idealSecretKey prims (prims.expandSeed seed).1
      (prims.expandSeed seed).2.2 aHat (secretOfCoeffs e)) aHat βmin

end GordieHowe.Ring.MLDSAW1
