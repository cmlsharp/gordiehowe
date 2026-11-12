# An ML-DSA ring signature that publishes `w1`

This directory holds the public ring check and the numerical facts of a ring signature over
ordinary FIPS 204 ML-DSA keys in which the signer publishes its commitment `w1`. The ring signature
is `w1Concrete` and its instances `w1Scheme44`, `w1Scheme65`, `w1Scheme87`
(`Applications/Ring/MLDSAW1Ring.lean`), with completeness and anonymity headlines in the
library's ring-signature model, FIPS 204 hedged signing included ([the result](#the-result)). The
lemmas about ML-DSA itself that the proof uses (the signer, regularity, weights) are under
`Applications/MLDSA/`. Paths below are relative to `formal/GordieHowe/`.

Publishing `w1` lets the verifier compute every member's challenge
`c_j = SampleInBall(H(µ_j ‖ w1Encode(w1)))` itself, so the statement proved in zero knowledge
needs no hash evaluation. Published naively, `w1` reveals the signer. The construction below
removes the leak by rejection sampling, and the proof bounds what remains.

## The construction

**Keys.** Ordinary ML-DSA key pairs. Each member publishes `t0` next to its public key `(ρ, t1)`.
FIPS 204 §6.1 notes that `t0` need not be secret.

**Signing** by the member at position `i` of ring `R` on message `m`, with `µ_j = H(tr_j ‖ m)`,
at check parameters `(tol, s)` chosen for the ring size (see [the check
parameters](#the-check-parameters)):

1. **Ring check.** For each member `j` and `r < 355`, derive `c̃ = G(R, j, r)` from a separate
   random oracle `G`, and compute the *check weight* of `t0_j` at `c̃`: zero if
   `‖SampleInBall(c̃)·t0_j‖∞ ≥ γ2`, and otherwise `Pr[Σ_i Bernoulli(p_i) ≤ ω]` with
   `p_i = max(0, |b_i| − β)/(2(γ2 − β) − 1)`, `b = SampleInBall(c̃)·t0_j`. If more than `tol` of
   the `355·|R|` check weights are below `β_min = 1/2`, or two members share `µ_j`, output `⊥`. The
   proof models `µ_j = H_µ(tr_j ‖ m)` as a value of a random oracle `H_µ` and compares the
   `µ_j` themselves (`MuDistinct`), so the refusal holds against an adversary that publishes a key
   whose `µ` equals an honest member's.
2. **Attempt.** Call `ML-DSA.Sign(sk_i, m)`, and recompute its commitment `w1` from the signature
   as the verifier does. The proof models the attempt with a uniform mask `y`
   (`Applications/MLDSA/Signing/Ideal.lean`); with FIPS 204's hedged mask derivation the theorem
   does not apply.
3. **Flattening.** For every member `j`, let `c̃_j = H(µ_j ‖ w1Encode(w1))` and
   `aw_j = aw(t0_j, w1, c̃_j)`, the probability that the ct₀ and hint-count checks of FIPS 204
   Algorithm 7 pass at challenge `SampleInBall(c̃_j)` when the low bits of `w` are uniform in
   `w1`'s buckets (a Poisson-binomial CDF, computed by dynamic programming). Keep the signature with
   probability

   ```
   min(1, β_min / aw_i) · ∏_{j ≠ i} min(1, aw_j / β_min).
   ```

   Otherwise go back to step 2.
4. **Output** `w1` and a zero-knowledge proof (spBCS, the GordieHowe proof system) of "for some
   position `i`, the signature verifies under `pk_i` with commitment `w1`", with witness
   `(i, signature)`.

**Verification** checks the proof against `(R, m, w1)`.

The signer uses `ML-DSA.Sign` as a black box. Its cost per signature is about `1/β_min = 2` calls to
`ML-DSA.Sign` (for honest rings every `aw_j` is above `β_min`, so only the first factor of the coin
is below one), one Poisson-binomial evaluation per member per call, and the ring check, which is
`355` evaluations per member, done once per ring. We estimate the ring check at about 20 s of one
core for a 1024-member ring at ML-DSA-65, from a measured 0.06 ms per evaluation; no
implementation exists.

### The check parameters

Honest rings are almost never refused when the tolerance `tol` and the defect budget `s` grow with
the ring. Two theorems reduce the refusal probability to the law of one honest key's check defect
`δ`, the probability over a uniform `c̃` that its check weight is below `β_min`:
- a ring of distinct keys whose members' defects sum to at most `d` is refused with probability at
  most `|R|²/2^512 + x^−(tol+1) · exp((x − 1) · 355 · d)` for every `x ≥ 1`
  (`expect_not_ringAdmissible_le`; the first term is a collision of the `µ_j`, the second a
  Chernoff upper tail of the failed samples);
- a ring of `N'` honestly generated keys fails the check with probability at most
  `x^−(tol+1) · (𝔼_seed (1 + (x − 1) δ(seed))^355)^N'` (`expect_not_ringCheck_honestRing_le`).

The law of `δ` is not formalized, and we estimate it. At ML-DSA-65 and ML-DSA-87 the ct₀ check
cannot fail for an honest `t0` (`τ·4096 < γ2`). Every honest check weight measured at ML-DSA-65
was at least 0.938, and we estimate a sample below `β_min` at about 10^−23 by extrapolating the
measured tail. At ML-DSA-44 a sample fails for an honest `t0` with probability about 7·10^−9 (the
exact 39-fold convolution of the ct₀ tail). With these per-sample estimates as the members'
defects, the first bound gives the following supported ring sizes, for a refusal probability
below 2^−64:

| Parameter set | `tol` | `s` | `x` | Factor `1/(1 − s)` | Largest ring (estimate) |
|---|---|---|---|---|---|
| ML-DSA-44 | 8 | 3/5 | 26 | 2.5 | 2^13 |
| ML-DSA-44 | 16 | 2/3 | 15 | 3 | 2^17 |
| ML-DSA-44 | 40 | 5/6 | 7 | 6 | 2^21 |
| ML-DSA-65 | 2 | 1/2 | 89 | 2 | 2^46 |
| ML-DSA-87 | 2 | 1/2 | 89 | 2 | 2^46 |

Every row has 355 samples per member and check error at most 2^−240 (`CheckParams`;
`checkParams_tol2`, `checkParams_tol8`, `checkParams_tol16`, `checkParams_tol40`), so the check
term at check parameters is `2 (√Q + 2 t)² / 2^240` at every row. The larger defect budget costs
only the factor
`1/(1 − s)`: at ML-DSA-44 the regularity term at `n = 1024`, `θ = β_min = 1/2` is 2^−80.27 at
`s = 1/2` and 2^−78.69 at `s = 5/6`. Tolerance 2 does not suffice at ML-DSA-44: by the same
bound we estimate the refusal probability of a 1024-member ring at 2^−26. Honest rings stay below
the defect budget at every supported size, since the honest defect is about `7·10^−9` per member
at ML-DSA-44.

## Why it works

### Flattening makes the kept law symmetric

Fix the ring and the oracle. Write `(v, c̃)` for a bucket vector `w1` and a commitment hash. If the
signer's accepted mass were exactly `K · aw_i(v, c̃_i)` for a constant `K`, the kept mass would be

```
K · aw_i · min(1, β_min/aw_i) · ∏_{j≠i} min(1, aw_j/β_min) = K · β_min · ∏_j min(1, aw_j/β_min)
```

(`mul_flattenCoin_eq`), the same for every signer `i`. So the law of the published `w1` would not
depend on `i`. The real accepted mass differs from `K·aw_i` in two ways, and the proof bounds both:

- **`y` is uniform on the mask box, not `w` uniform in the bucket.** `w = A·y` with `y` uniform on a
  box. The accepted mass of `(v, c̃)` is `Pr_y[HighBits(A·y) = v, all four checks pass]`. Its
  stand-in replaces `A·y` by a uniform `w`, scaled by the z-check's acceptance fraction `ρ_z`. The
  *regularity gap* `signerRegGap` is the column-wise ℓ1 distance between the two, relative to the
  signer's mean member weight.
- **The loop is random.** Each attempt reads fresh oracle values. The two signers' loops are
  compared attempt by attempt: the distance between the loops' outputs is at most the normalized
  deviation of one attempt's kept mass from the symmetric mass, plus the chance that the ring's
  total weight falls below a fraction `θ` of its mean (`RingPair.tvDist_untilSome_le`). Both
  quantities concentrate over the oracle `H` by McDiarmid's inequality, because each oracle point
  changes one column. Their variance proxies are of order `1/|V|`, where `|V| = 16^1536` at
  ML-DSA-65. The bound uses the collision probability of `HighBits(A·y)` under a uniform matrix
  (`expect_commitCollision_le`, at most 2^−4352), which gives `McD`.

### Regularity: `A·y` looks uniform to the checks

`ExpandA` is a random oracle, so `A` is uniform. For a fixed challenge, the accept indicator of
bucket vector `v` is a product over the coefficients of `w = A·y` of cell functions: the bucket,
the r0 check, and the hint probability. A finite combination of such products expresses it. The
deviation between masks `y` and uniform `w` is then a Fourier sum over the nonzero modes of
`Z_q^{256k}`, and its square summed over `v` is a sum of pair kernels. Averaging over `A` kills
every pair of modes except those the masks `y, y′` can align, leaving a second moment of the cell
kernels over the box (`ZMod.sum_sum_norm_le` and its ℓ² form,
`Foundations/ToMathlib/CharacterSecondMoment.lean`; `Regularity/RqRegularity.lean`). That second
moment is bounded per NTT slot by:
- exact box counts;
- bounds for modes supported on up to seven slots;
- a hybrid term for larger supports.

The bounds are at most `2^−202`, `2^−398` and `2^−588` at ML-DSA-44, 65 and 87
(`Regularity/InstancesSeven.lean`). Their square roots, with the expansion's constants, give `R`: a
bound on `√(𝔼_A (Σ_v 𝔼_c̃ |real − stand-in|)²)` relative to the stand-in scale, for every key.

### The weight: dividing by a mean that can be small

The regularity gap is relative to the signer's mean member weight `𝔼_c̃ min(1, aw/β_min)`, and for
rare keys that mean is small. The proof does not assume a lower bound on it. Cauchy–Schwarz over the
matrix gives

```
𝔼_A signerRegGap ≤ R/β_min · √(𝔼_A w⁻²)
```

for any lower bound `w` on the mean member weight (`expect_signerRegGap_le_sqrt`). It remains to
show
that `𝔼 w⁻²` is a small constant, averaged over keys, matrices and the `SampleInBall` oracle. The
weight factor is `C = √(𝔼 w⁻²)`.

- **The law of `t0` under a uniform matrix.** `t = A·s1 + s2`. Off the NTT slots where every
  component of `s1` vanishes, `t` is uniform. A Vandermonde argument shows that the top
  `256 − d` coefficients of every component of `t` are uniform and independent, where `d` is the
  number of such slots (`expect_topCoeffs`, `Regularity/T0Law.lean`). With `ExpandS` a random
  oracle,
  `Pr[d ≥ d0] ≤ C(256, d0)·9^{−ℓ d0}` (`expect_le_card_secretZeroSlots_le`). This gives
  moment-generating-function bounds on `‖t0‖₂²`, and with them layered Chernoff tails.
- **ML-DSA-65 and ML-DSA-87.** Two floors bound the weight:
  - the Markov bound `aw ≥ 1 − Σ p_i/(ω + 1)`;
  - the product bound `aw ≥ ∏(1 − p_i) ≥ exp(−Σ p_i − κ Σ p_i²)`.

  `Σ p_i` is bounded by `𝔼|b|`. For `b`, a sum of `τ` signed coefficients of `t0`, the bound uses
  the majorant `|x| ≤ A + B x² − C cos(t x)` (`sum_expect_challengeBall_abs_centeredCoeffs_le`),
  which is 25% sharper than `√𝔼 b²`. The ct₀ check never fails there.
- **ML-DSA-44.** The floors above lose about 80 bits, for two reasons:
  - the expected hint count, about 63, is close to `ω = 80`;
  - the ct₀ check can fail, since `τ·4096 > γ2`.

  The proof replaces them with:
  - **Four lines under the Poisson-binomial CDF.** The CDF is affine in each `p_i`, so a line
    `α − σ Σ p_i` lies below it on the box `[0, 21/25]^ι` once it lies below the binomial CDF at
    every vertex count `N` (`sub_sum_le_poissonBinomialCdf`). Each line is certified by finitely
    many exact rational checks (`Regularity/WeightLines44.lean`).
  - **Bounds on ct₀ failure.**
    - Given the support of the challenge, the signs are independent. A cosh chord and Maclaurin's
      inequality then bound the failure probability by 3/4000 for typical keys.
    - For every `t0` with `‖t0‖∞ ≤ 4096`, a convex-comparison argument bounds it by 217/625
      (`Regularity/Ct0Tail44.lean`).
  - **A layered average over keys,** by the largest component norm (`Regularity/WeightTail44.lean`).

  The result is `𝔼 w⁻² ≤ 22.87`, so `C = 24/5`.

### Other members' keys are adversarial

The keys of the other ring members are arbitrary, including their published `t0`. They enter only
through the product `∏_j min(1, aw_j/β_min)`. A ring whose members' weights often fall below
`β_min` would make the symmetric mass small and the normalized errors large. The ring check rules
this out:
- If every member's probability of a check weight below `β_min` sums to at most `s`, then every
  column mass is in `[1 − s, 1]` (`RingWeights.massRatio_le_inv_one_sub`), which costs the factor
  `1/(1 − s)` in the bound.
- A ring above that passes the 355-sample check with at most `tol` failures with probability at
  most `x^tol · exp(−(1 − 1/x) · 355 · s) ≤ 2^−240` over the check oracle, at each row of check
  parameters (a Chernoff lower tail, `expect_ringCheck_le`).
- The scheme and the scheme on the rings of defect at most `s` (`admLow`) are identical until an
  answered challenge's ring has defect above `s` and passes the check
  (`gameAdvantage_anon_restr_le_bad`). The check of a ring `l` reads `G` only at the points
  `(l, j, r)`, so for an adversary with `t` superposition queries that event has probability at most
  `(√Q + 2 t)² · checkError` (`toReal_runLaw_badReq_le`, the QROM search lemma
  `RingSignature.toReal_runLaw_hit_le`).

The refusal depends only on the ring, the message and the oracles, so it is the same for both
challenge users.

## The result

`Applications/Ring/MLDSAW1Ring.lean` defines the ring signature as one value of the library's
ring-signature model (`Model/RingSignature/`): `w1Scheme44`, `w1Scheme65` and `w1Scheme87` are
`w1Concrete` at ML-DSA-44, ML-DSA-65 and ML-DSA-87, the ring signature `ofBase` of the base signer
`w1ConcreteBase` (the ring check, then the flattened hedged FIPS 204 loop, at the FIPS 204 key
generation and functions) and a proof system `PS` for its ring relation. Its headlines:

- Completeness (BKM06 Definition 1 with errors): `w1Scheme{44,65,87}.completeWithin` and
  `w1Concrete.completeWithin` (`Applications/Ring/MLDSAW1Completeness.lean`). For a refusal rate
  `ρ` of the base signer on honest supported rings and a proof system adaptively complete for the
  ring relation at error `εp`, the ring signature refuses with probability at most `ρ` and is
  rejected with probability at most `εp (q + qPub)`.
- Anonymity (BKM06 Definition 4 with `Q` adaptive challenges, the honest users' key coins given at
  the start): `w1Scheme{44,65,87}.anonAdvantage_le`, `w1Concrete.anonAdvantage_le_coupling` and
  `w1Concrete.anonAdvantage_le_coupling_checkParams` (`Applications/Ring/MLDSAW1AnonQuery.lean`).
  The oracle's values split as `Y ≃+ Y₁ × Y₂` (`OracleSplit`,
  `Applications/Ring/MLDSAW1Split.lean`):
  the base signer and the mask derivation read `Y₁`, and the honest prover reads `Y₁` only off the
  mask and check points. The adversary has `t` superposition queries to the whole oracle, and its
  table reads `Y₁` only off the mask and check points, so it reaches the check oracle `G` by queries
  only. For every such adversary and every `Q`, the advantage is at most
  `Q · w1CouplingError + Q · wi (Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) +
  2 (√Q + 2 t)² · checkError` (`w1NonceTerm k Q t` and `w1SampledCheckTerm reps tol s x Q t`), with
  `wi` the witness-indistinguishability error of `PS` (a
  hypothesis) and `C` a bound on the valid challenges.
  - The third term reprograms the mask derivation at the `Q · k` hidden nonces.
  - The last term is the check term. In each experiment the scheme and the scheme on the rings of
    defect at most `s` (`admLow`) are identical until an answered challenge's ring has defect above
    `s` and passes the check (`gameAdvantage_anon_restr_le_bad`). That event has probability at most
    `(√Q + 2 t)² · checkError` (`toReal_runLaw_badReq_le`). This is the QROM search lemma
    `RingSignature.toReal_runLaw_hit_le` (`Model/RingSignature/Search.lean`), proved by one-way to
    hiding in square-root form with a fresh secret over the whole run (`Model/Quantum/O2H/Search.lean`).
  - `w1CouplingError` holds the regularity and McDiarmid terms as the averages `regGapAt` and
    `collAt` of one honest key at the FIPS 204 functions, and the terms `2 k / D` and `2 (1 - Lk)^k`
    of the bounded loop. `C` enters only through `log C` and `wi (Q · C)`.

  At check parameters (`CheckParams`, check error at most `2^-240`, every row of [the check
  parameters](#the-check-parameters)) the check term is `2 (√Q + 2 t)² / 2^240`. We floor the
  security bits of that term, the same at ML-DSA-44, -65 and -87:

  | `t` | `Q` | bits |
  |---|---|---|
  | `2^64` | `≤ 2^64` | 108 |
  | `2^80` | `2^64` | 76 |
  | `2^96` | `2^64` | 44 |

  The rows at check error `2^-300` need 439, 407, 405 and 401 samples per member for tolerances
  2, 8, 16 and 40 (`checkError_tol{2,8,16,40}_le_300`). The defaults stay at 355 samples.
- Anonymity with `SampleInBall`, `ExpandS` and `ExpandA` random oracles, every term numeric:
  `w1Scheme.expect_anonAdvantage_le` and its instances
  `w1Scheme.expect_anonAdvantage_le_mldsa{44,65,87}`,
  with ring-binding (`…_bind_mldsa{44,65,87}`) and converted (`…_conv_mldsa{44,65,87}`) base
  messages
  (`Applications/Ring/MLDSAW1AnonOracle.lean`).
  The scheme is `w1Scheme` at the concrete primitives with the three oracles `G_B`, `G_S`, `G_A`
  in place of `SampleInBall`, `ExpandS` and `ExpandA` (`randomOraclePrimitives`), the concrete
  encoding and the oracle placement `O` (`W1Oracles.atRandomOracles`). The
  adversary is a family indexed by the three oracles, so it holds them whole, with the access to
  the joint oracle above. For every such family and every `Q`, the advantage averaged over the
  three oracles is at most

  ```
  Q · (2 (2/((1 − s)θ) · n ρ / β_min + √(N n log(C + 1)) / (2^2000 θ(1 − θ)(1 − s) β_min))
       + 2 k / D + 2 (1 − β_min θ (1 − s) / 32)^k)
    + Q · wi(Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240
  ```

  with `ρ` the regularity bound times the weight factor (`11·2^−101 ·
  24/5`, `11·2^−199 · 9/2` and `12·2^−294 · 33/5` at ML-DSA-44, -65 and -87,
  `expect_regGapAvg_le_mldsa{44,65,87}`) and `C` a bound on
  the valid challenges per key vector, for `β_min ∈ (0, 1]`, `n ≥ 1`, `θ ∈ (0, 1)` and
  any row of check parameters with `0 ≤ s`. The proof applies
  `hedgedScheme.anonAdvantage_le_coupling` (the bound above at any primitives with the signing and
  verification laws) at each triple of oracles, with keep level `β_min θ (1 − s) / 32`, and
  averages `w1CouplingError` over the oracles (`expect_w1CouplingError_randomOracle_le`): the
  regularity gap enters linearly (`expect_regGapAt_withExpandA`, `expect_regGapAvg_le_mldsa*`),
  the collision probability under a square root (Jensen's inequality,
  `expect_w1CouplingError_le`; `expect_collAt_withExpandA_le`).

  We floor the security bits of the whole bound except `Q · wi (Q · C)`, at `n = N = 1024`,
  `C = 2^64`, `θ = β_min = 1/2`, tolerance 2 (`s = 1/2`), `t = 2^64`, `k = 2^16` and `D = 2^128`:

  | `Q` | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
  |---|---|---|---|
  | `1` | 53 | 53 | 53 |
  | `2^32` | 37 | 37 | 37 |
  | `2^64` | 16 | 21 | 21 |

  The reprogramming term `4 t √(Q k / 2^256)` dominates, except at ML-DSA-44 with `Q = 2^64`, where
  the regularity term `Q · 2^−80.27` does. At `Q = 1` the other terms are `2^−80.27` (regularity,
  ML-DSA-44), `2^−111` (`2 k / D`), `2^−369` (`2 (1 − 1/256)^k`), `2^−1982` (McDiarmid) and
  `2^−109` (check).

## Lean statements

| Claim | Theorem | File |
|---|---|---|
| Rounds with public outputs, witness indistinguishability | `pubRun`, `tvDist_pubRun_le`, `gameAdvantage_pubRun_le`, `PubWI` | `Applications/Ring/Anonymity.lean`, `Applications/Ring/AnonCoupling.lean` |
| The signer and the flattening identity | `ringLoopSigner`, `memberWeight`, `mul_flattenCoin_eq` | `Applications/MLDSA/Signing/RingSigner.lean` |
| Distinct message representatives | `MuDistinct`, `RingAdmissible`, `schemeOrc` | `Applications/Ring/PublicW1/MLDSAPublicW1.lean`, `Applications/MLDSA/Signing/Oracles.lean` |
| The ring check and its error | `sampledRingCheck`, `RingCheck.sampled`, `checkWeight`, `expect_ringCheck_le`, `checkError_checkParams_le` | `Applications/Ring/PublicW1/MLDSAPublicW1.lean`, `MLDSAPublicW1Regularity.lean` |
| Check parameters | `CheckParams`, `checkParams_tol2`, `checkParams_tol8`, `checkParams_tol16`, `checkParams_tol40` | `Applications/Ring/PublicW1/MLDSAPublicW1Regularity.lean` |
| Refusal of rings of low defect | `refuseError`, `expect_not_ringCheck_le`, `expect_not_ringCheck_honestRing_le`, `expect_not_muDistinct_le`, `expect_not_ringAdmissible_le` | `Applications/Ring/PublicW1/MLDSAPublicW1Refusal.lean` |
| Two loops, adversarial members | `RingPair.tvDist_untilSome_le`, `familyBound`, `RingWeights.massRatio_le_inv_one_sub` | `Foundations/ToMathlib/PMFOracleQuenched.lean` |
| McDiarmid numbers | `sqrt_add_sqrt_le_of_le`, `four_mul_div_add_four_div_le`, `expect_commitCollision_le` | `Applications/Ring/PublicW1/MLDSAPublicW1Concentration.lean`, `Applications/MLDSA/Regularity/CommitCollision.lean` |
| Regularity | `expect_regGapAvg_le_mldsa{44,65,87}`, `expect_signerRegGap_le_sqrt_mldsa{65,87}_seven`, `expect_signerRegGap_le_sqrt_mldsa44_box_seven_of_nonneg` | `Applications/Ring/PublicW1/MLDSAPublicW1Regularity.lean`, `Applications/MLDSA/Regularity/InstancesSeven.lean` |
| Cauchy–Schwarz over the matrix | `expect_signerRegGap_le_sqrt`, `expect_signerRegGap_le_sqrt_of_nonneg` | `Applications/MLDSA/Regularity/SignerRegularity.lean` |
| Law of `t0` under a uniform matrix | `expect_topCoeffs`, `expect_exp_t0SqNorm_le`, `expect_le_card_secretZeroSlots_le` | `Applications/MLDSA/Regularity/T0Law.lean` |
| Weight factor at ML-DSA-65/87 | `expect_expect_floorInvSqBound_le_mldsa65`, `…_mldsa87` | `Applications/MLDSA/Regularity/WeightTail.lean` |
| Weight factor at ML-DSA-44 | `sub_sum_le_poissonBinomialCdf`, `one_sub_le_expect_challengeBall_ct0_mldsa44`, `expect_expect_expect_inv_sq_mldsa44OracleWeight_le` | `Applications/MLDSA/Signing/Flatten.lean`, `Regularity/Ct0Tail44.lean`, `Regularity/WeightTail44.lean` |
| Hedged masks and the keep level | `keepLevel`, `W1CouplingParams`, `PMF.weightedAttemptMasks`, `PMF.keep_ge_of_familyBound_lt` | `Applications/Ring/PublicW1/MLDSAPublicW1Hedged.lean`, `MaskOracle.lean` |
| QROM search over a whole interactive run | `Distinguisher.eventProb_searchLogs_le`, `RingSignature.toReal_runLaw_hit_le` | `Model/Quantum/O2H/Search.lean`, `Model/RingSignature/Search.lean` |
| Identical until a bad request | `RingSignature.gameAdvantage_runLaw_le_untilBad` | `Model/RingSignature/UntilBad.lean` |
| Completeness | `w1Concrete.completeWithin`, `w1Concrete.completeWithin_refusal` | `Applications/Ring/MLDSAW1Completeness.lean`, `MLDSAW1Refusal.lean` |
| Anonymity (check oracle by superposition queries) | `hedgedScheme.anonAdvantage_le_coupling`, `w1Concrete.anonAdvantage_le_coupling`, `w1Scheme{44,65,87}.anonAdvantage_le` | `Applications/Ring/MLDSAW1AnonQuery.lean` |
| The same with `SampleInBall`, `ExpandS` and `ExpandA` random oracles, numeric | `randomOraclePrimitives`, `W1Oracles.atRandomOracles`, `expect_w1CouplingError_randomOracle_le`, `w1Scheme.expect_anonAdvantage_le`, `w1Scheme.expect_anonAdvantage_le_mldsa{44,65,87}` | `Applications/Ring/MLDSAW1AnonOracle.lean`, `Applications/Ring/MLDSAW1IdealDist.lean` |

## What is not shown

- **Anonymity in three settings.** The library does not prove:
  - the anonymity bound for an adversary that sees the check oracle `G` whole (a check term of the
    form `C·checkError`);
  - the bound for classical queries with check and hedge terms linear in the query count,
    `2(q + 1)·checkError`, where the proved quantum-query form gives `2(1 + 2q)²·checkError`;
  - a coupling whose good event and error depend on the base oracle and are averaged over it.
- **`wiError` is a parameter.** Instantiating it needs the public-`w1` ring circuit and its
  zero-knowledge proof, which do not exist. In the headlines it is the hypothesis `hwi` on the
  proof system `PS`.
- **`t0` is not bound to the key.** An adversary may publish a false `t0` under an honest member's
  `(ρ, t1)`. Members could self-certify `(ρ, t1, t0)`; this is not formalized.
- **The model:**
  - The headlines are in the quantum random-oracle model. In `w1Concrete.anonAdvantage_le_coupling`
    and `w1Scheme{44,65,87}.anonAdvantage_le`, `ExpandA`, `ExpandS` and `SampleInBall` are the FIPS
    204 functions, and `regGapAt` and `collAt` stay defined averages. In
    `w1Scheme.expect_anonAdvantage_le` they are random oracles held whole by the adversary, and
    every term is numeric.
  - `µ_j = H_µ(tr_j ‖ m)` and `c̃ = H(µ ‖ w1Encode(w1))` are values of two random oracles, `H_µ`
    and `H` keyed on `(µ, w1)`, as FIPS 204 computes them.
  - The random oracles (`H_µ`, `H`, the check oracle `G`, the proof system's hash) are independent
    in the model. An implementation must domain-separate them from each other and from FIPS 204's
    other uses of SHAKE.
  - The law of an honest key's check defect is not formalized, so the refusal probabilities of
    honest rings in [the check parameters](#the-check-parameters) are estimates; their reduction
    to that law is formalized (`MLDSAPublicW1Refusal.lean`).
  - Deterministic signing (`rnd = 0`) is not covered.
  - Efficiency is not formalized.
- **No implementation or measurements.** The signing cost above is an estimate.
