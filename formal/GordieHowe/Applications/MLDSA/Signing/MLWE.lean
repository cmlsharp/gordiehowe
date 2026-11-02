-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.MLDSA.Scheme
public import GordieHowe.Foundations.ToMathlib.PMFSumToReal
public import Mathlib.Probability.Distributions.Uniform
public import GordieHowe.Foundations.ToMathlib.FintypeBytes
public import GordieHowe.Model.Lattice.MLWE

@[expose] public section

/-!
# The decision MLWE advantage at ML-DSA

The library's decision Module-LWE (`GordieHowe/Model/Lattice/MLWE.lean`: Kiltz, Lyubashevsky and
Schaffner, EUROCRYPT 2018, §4.1.1; Barbosa et al., CRYPTO 2023, ePrint 2023/246, §6.2,
Definition 3) at the ML-DSA ring `R_q = Z_q[X]/(X^256 + 1)`, `q = 8380417`: the matrix `Â`
uniform on `T_q^{k×l}`, as FIPS 204 `ExpandA` (Algorithm 32) outputs it, acting by the vendored
`Â ∘ NTT(s₁)` product of key generation (`keyGenFromSeed`), and the law `S` of the secret
`(s₁, s₂)` a parameter (the ML-DSA instance is the law of `ExpandS` on the key-generation seed).

* `mlweRealMean`, `mlweUniformMean`, `mlweAdvantage`: the library's `Lattice.mlweRealMean`,
  `Lattice.mlweUniformMean`, `Lattice.mlweAdvantage` at the ML-DSA carriers.
* `abs_mlweRealMean_sub_mlweUniformMean_le`: for every test, the means differ by at most its
  advantage (the reduction step of a hybrid argument).
* `mlweUniformMean_of_vector`: a test that reads only `t` has its uniform mean over the uniform
  `t` alone.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA LatticeCrypto TransformOps

variable {k l : ℕ}

/-- **The uniform MLWE mean** of a test `f` at ML-DSA (`Lattice.mlweUniformMean`): `𝔼[f(Â, t)]` for
`Â` uniform on `T_q^{k×l}` and `t` uniform on `R_q^k`, independent. -/
noncomputable abbrev mlweUniformMean (f : TqMatrix k l → RqVec k → ℝ) : ℝ :=
  Lattice.mlweUniformMean f

/-- A test that reads only `t` has uniform mean `𝔼_{t uniform} g(t)`. -/
theorem mlweUniformMean_of_vector (g : RqVec k → ℝ) :
    mlweUniformMean (l := l) (fun _ t => g t) =
      ∑ t : RqVec k, (PMF.uniformOfFintype (RqVec k) t).toReal * g t := by
  simp only [mlweUniformMean, Lattice.mlweUniformMean, mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul, PMF.sum_toReal_eq_one, one_mul]

variable [nttOps : NTTRingOps]

/-- **The real MLWE mean** of a test `f` at ML-DSA (`Lattice.mlweRealMean`): `𝔼[f(Â, Â·s₁ + s₂)]`
for `Â` uniform on `T_q^{k×l}` and `(s₁, s₂) ← S`, independent. -/
noncomputable abbrev mlweRealMean (S : PMF (RqVec l × RqVec k))
    (f : TqMatrix k l → RqVec k → ℝ) : ℝ :=
  Lattice.mlweRealMean S f

/-- **The decision MLWE advantage** of a test `f` against secrets with law `S` at ML-DSA
(`Lattice.mlweAdvantage`): `|𝔼_uniform f − 𝔼_real f|`. -/
noncomputable abbrev mlweAdvantage (S : PMF (RqVec l × RqVec k))
    (f : TqMatrix k l → RqVec k → ℝ) : ℝ :=
  Lattice.mlweAdvantage S f

/-- **The MLWE hop**: for every test `f`, its real and uniform means differ by at most its MLWE
advantage. -/
theorem abs_mlweRealMean_sub_mlweUniformMean_le (S : PMF (RqVec l × RqVec k))
    (f : TqMatrix k l → RqVec k → ℝ) :
    |mlweRealMean S f - mlweUniformMean f| ≤ mlweAdvantage S f :=
  Lattice.abs_mlweRealMean_sub_mlweUniformMean_le S f

end GordieHowe.MLDSA
