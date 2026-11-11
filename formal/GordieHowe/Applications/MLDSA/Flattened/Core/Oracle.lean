-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Core.Weights
public import GordieHowe.Foundations.ToMathlib.PMFOracleSingle

public section

/-!
# The flattened signer against one commitment-hash oracle

The flattened signer whose commitment hashes are read from one function `H : BucketVec p →
CommitHashBytes p` drawn once (`H(µ ‖ ·)` for one message representative `µ`), instead of a fresh
uniform hash per attempt.

* `flatSliceLoop`: the loop against a fixed `H`: attempts until one keeps (`oracleAttempt`).
* `flatOracleConcError`: the oracle concentration term of the loop against a uniform `H`
  (`oracleConc`), at most `√(w1MaxProb / flatKeepProb) / 2` (`flatOracleConcError_le`).
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF
open scoped ENNReal BigOperators

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (cut : Cutoff p)

/-- **The flattened signer's attempt against the commitment hashes `H`**: `y` uniform on the mask
box, `c̃ = H(w₁)`, the four checks, the keep coin `min(1, val(c̃) / aw)`. -/
@[expose] noncomputable def flatSliceAttempt (H : BucketVec p → CommitHashBytes p) :
    PMF (Option (BucketVec p)) :=
  oracleAttempt (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut) H

/-- **The flattened signer's loop against the commitment hashes `H`**: attempts until one keeps;
the kept commitment. -/
@[expose] noncomputable def flatSliceLoop (H : BucketVec p → CommitHashBytes p) :
    PMF (Option (BucketVec p)) :=
  untilSome (flatSliceAttempt prims sk aHat cut H)

/-- **The oracle concentration term** of the flattened signer against a uniform commitment-hash
function: `E_H[(q H / q̄ - 1)⁺]` (`oracleConc`). -/
@[expose] noncomputable def flatOracleConcError : ℝ :=
  oracleConc (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut)

/-- The oracle concentration term is nonnegative. -/
theorem flatOracleConcError_nonneg : 0 ≤ flatOracleConcError prims sk aHat cut :=
  oracleConc_nonneg _ _ _ _ _

/-- **The keep probability** of one attempt against a uniform commitment-hash function. -/
@[expose] noncomputable def flatKeepProb : ℝ :=
  (1 - jointAttempt (uniformOfFintype (BucketVec p → CommitHashBytes p))
    (flatSliceAttempt prims sk aHat cut) none).toReal

/-- **The oracle concentration term is at most `√(δ / q̄) / 2`**, with `δ = w1MaxProb` the largest
probability of one commitment and `q̄ = flatKeepProb` (`oracleConc_le`), when the signer's fresh
attempt keeps with positive probability. -/
theorem flatOracleConcError_le (hkeep : SignerKeeps prims sk aHat cut) :
    flatOracleConcError prims sk aHat cut ≤
      √(w1MaxProb aHat / flatKeepProb prims sk aHat cut) / 2 := by
  rw [SignerKeeps] at hkeep
  exact oracleConc_le _ _ _ _ _ (fun v => le_sup' (fun v => ((maskUniform p).map
    (realBuckets aHat) v).toReal) (mem_univ v)) (jointAttempt_oracleAttempt_ne_one _ _ _ _ _ hkeep)

end GordieHowe.MLDSA
