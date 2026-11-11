-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Lattice.Search
public import GordieHowe.Model.Lattice.MSIS
public import GordieHowe.Model.Lattice.MLWE
public import GordieHowe.Model.Lattice.SelfTargetMSIS
public import GordieHowe.Model.Lattice.MLDSA
public import GordieHowe.Model.Lattice.MLDSAPigeonhole
public import GordieHowe.Model.Signature.SingleUser
public import GordieHowe.Model.Signature.NMA
public import GordieHowe.Model.Signature.Relations
public import GordieHowe.Model.Signature.Assumptions
public import GordieHowe.Applications.MLDSA.Assumptions
public import GordieHowe.Applications.Falcon512.Assumptions

@[expose] public section

/-!
# The assumptions of the library

Every computational assumption the library states, with its definition, its source and its uses,
and the idealizations its proofs use. The library declares no axioms: an assumption is a defined
game and a predicate on a class of adversaries, and a theorem that uses it takes the predicate
(or a bound on an explicit adversary) as a hypothesis.

## Adversaries and hardness

The adversaries of the library need not be efficient, so a hardness statement for every adversary
is false for a problem whose instance determines its solution (`Lattice.not_hard_univ`; at
ML-DSA, Module-SIS by pigeonhole, `Lattice.exists_kernel`, `Lattice.not_msisHard_univ`,
`Lattice.not_keyGenMSISHard_univ`; Module-LWE, `Lattice.not_mlweHard_univ`,
`Lattice.not_mlweHard_univ_of_seed`; the signature games, `Signature.not_muEufCmaHard_univ_whole`).
Each assumption is therefore a predicate `…Hard … 𝒜 ε` on a class `𝒜` of adversaries, a
parameter: every adversary of `𝒜` has advantage at most `ε`. A theorem that uses it either takes
the predicate and the membership of its explicit reductions in `𝒜`, or states its bound at the
explicit reduction. Every predicate holds at `ε = 1` for every class (`Lattice.hard_one`,
`Lattice.mlweHard_one`, `Lattice.selfTargetMSISHard_one`, `Signature.muEufCmaHard_one`).

## Lattice assumptions (`GordieHowe/Model/Lattice/`)

The ring is `R_q = Z_q[X]/(X^n + 1)` (the vendored `NegacyclicRing`), the matrix lives in the
transform domain and acts by `TransformOps.coeffMatVecMul`, and the `∞`-norm is
`PolyVec.cInfNorm`. Langlois and Stehlé (Des. Codes Cryptogr. 75(3), 2015; ePrint 2012/090) are
cited as the origin of Module-LWE and Module-SIS; the definitions are checked against the three
documents named per entry, not against their text.

- **Decision Module-LWE.** `Lattice.mlweAdvantage S f` (`MLWE.lean`), hardness
  `Lattice.MLWEHard S 𝒜 ε`. Sources: KLS18 (ePrint 2017/916) §4.1.1; Dilithium specification 3.1
  §6.1; Barbosa et al. (ePrint 2023/246) Definition 3. The secret law `S` is a parameter.
  At ML-DSA: `GordieHowe.MLDSA.mlweAdvantage` (an abbreviation). Uses: the advantage of the
  test `B_typ` is a term of the bounds of `sum_expect_tvDist_standin_le_mldsa{65,87}`
  (`Regularity/StandinError.lean`).
- **Search Module-LWE.** `Lattice.mlweSearchProb S B` (`MLWE.lean`). No use.
- **Module-SIS, `[A | I]` form, two bounds.** `Lattice.KernelAI norm βz βu`,
  `Lattice.msisWinProb`, `Lattice.MSISHard` (`MSIS.lean`); one bound: `MSISHard.of_max`. Sources:
  KLS18 §4.5.1 and Dilithium specification 3.1 §6.1 (one bound), §6.2.2 (two bounds). At ML-DSA
  (`MLDSA.lean`): `Lattice.Kernel p`, the bounds `msisBoundZ p = 2(γ₁ − β)`,
  `msisStrictBoundZ p = 2(γ₁ − β − 1)`, `msisBoundU p = 4γ₂ + 2` with their values at
  ML-DSA-44/65/87 (`msisBounds_mldsa44` …).
- **Module-SIS, key-generation form with a public seed.** `Lattice.keyGenMsisWinProb p prims`,
  `Lattice.KeyGenMSISHard` (`MLDSA.lean`): the seed `ξ` is uniform and given to the adversary, the
  matrix is `ExpandA` of the `ρ` of `keyGenFromSeed`; it differs from the uniform-matrix form only
  in the law of the matrix. Multi-instance: `keyGenMsisMultiWinProb`, at most `n` times the
  single-seed game (`keyGenMsisMultiWinProb_le`). Intended use: the strong-unforgeability step of
  the converted ML-DSA ring publishing `w₁`.
- **Multiple instances.** `Lattice.multiValid`, `Lattice.guess`,
  `Lattice.multiWinProb_le_card_mul` (`Search.lean`): `n` independent instances are won at most `n`
  times as often, by the guessing adversary.
- **SelfTargetMSIS.** `Lattice.selfTargetWinProb`, `Lattice.SelfTargetMSISHard`
  (`SelfTargetMSIS.lean`), in the QROM against the library's query-bounded quantum adversaries.
  Sources: KLS18 §4.5.1; Dilithium specification 3.1 §6.1, eq. (12); Barbosa et al. Definition 4.
  The game takes a view `V` of the oracle (`queriesOnly`: the sources' game). With the oracle as a
  table the unrestricted class is not hard below `1 − (1 − Pr[chal y = c₀])^|M|`
  (`not_selfTargetMSISHard_univ_whole`). No use.
- **Parameters.** `Lattice.mlweDims_mldsa44` (and 65, 87): `(k, l, η)` of FIPS 204 Table 1.
- No NTRU or Ring-SIS assumption is stated: no result of the library uses one.

## Signature assumptions (`GordieHowe/Model/Signature/`)

The games are those of a `RingSignature.BaseSigner` against `MUAdversary`s, the library's
query-bounded quantum adversaries in the QROM with classical requests to a challenger.

- **MU-EUF-CMA^corr, MU-SUF-CMA^corr.** `Signature.muEufProb`, `Signature.muSufProb`
  (`MultiUser.lean`; Bader et al., TCC 2015, Definition 2; Diemert et al., PKC 2021, Definition 2),
  hardness `MUEufCmaHard`, `MUSufCmaHard` (`Assumptions.lean`).
- **EUF-CMA, SUF-CMA (one user).** `suEufProb`, `suSufProb` (`SingleUser.lean`, the games at one
  user; KLS18 §2.4, Figure 7), hardness `SUEufCmaHard`, `SUSufCmaHard`.
- **EUF-NMA.** `SignOracle.none` (no messages: the requests are the public keys and corruption),
  `muEufNmaProb`, `suEufNmaProb` (`NMA.lean`), hardness `MUEufNmaHard`, `SUEufNmaHard`.
- **Relations.** EUF ≤ SUF (`muEufProb_le_muSufProb`, `suEufProb_le_suSufProb`,
  `MUSufCmaHard.muEufCmaHard`); NMA ≤ CMA at every signing oracle, with the same query and request
  bounds (`muEufNmaProb_le_muEufProb_nmaEmbed`, `Relations.lean`; `MUEufCmaHard.muEufNmaHard`).
  Non-vacuity: every class at `ε = 1` (`muEufCmaHard_one` and its siblings); the adversaries that
  output a draw independent of the public keys, at `keyHitProb B n ≤ n · max_pk Pr[pk(kc) = pk]`
  (`muEufCmaHard_constDrawAdversaries`, `keyHitProb_le`). The unrestricted class fails below `1`
  when every key has a verifying signature: with the oracle as a table
  (`not_muEufCmaHard_univ_whole`), and at every view of the oracle when verification does not read
  it (`not_muEufCmaHard_univ_of_bverify_eq`, by a draw that reads the public keys:
  `not_muEufCmaHard_drawAdversaries`).
- **Named base-scheme assumptions** (`Applications/MLDSA/Assumptions.lean`,
  `Applications/Falcon512/Assumptions.lean`):
  `MLDSA44SufCma`, `MLDSA65SufCma`, `MLDSA87SufCma` and their multi-user forms
  `MLDSA44MUSufCma` … (FIPS 204 §3.1); `Falcon512EufCma`, `Falcon512MUEufCma` (Falcon
  specification v1.2, §2.2.1). The base signers never read the game's oracle, so these are
  standard-model assumptions on the schemes with their hash functions; the random-oracle proofs
  (KLS18 Theorem 3.1 and eq. (21), corrected by Barbosa et al. and by Devevey, Fallahpour,
  Passelègue and Stehlé) do not bound them as defined. Uses: the unforgeability results bound the
  ring adversary's success by the success of explicit base-scheme forgers
  (`muEufProb (ringMUForger …)` in `Applications/Ring/RingForger*.lean` and
  `Applications/Falcon512/Ring/*/*/RingForger.lean`, to which `MUEufCmaHard.le` applies; the
  relay and extraction forgers of `Applications/Ring/Unforgeability.lean`,
  `RingUnforgeability.lean` and `StrongForger.lean`, which are not `MUAdversary`s); no result
  takes these predicates as hypotheses.
- **Named assumptions with `t₀` published** (`Applications/MLDSA/Assumptions.lean`, section "`t₀`
  published"): `MLDSAT0EufCma`, `MLDSAT0MUEufCma`, `MLDSAT0MUEufCmaWithin` (EUF-CMA) and
  `MLDSAT0EufNma`, `MLDSAT0MUEufNma` (EUF-NMA), with `MLDSA44T0EufCma` … `MLDSA87T0MUEufNma` at the
  three parameter sets: the games at the ML-DSA signer whose public key is `(ρ, t₁, t₀)`
  (`MLDSA.mldsaT0BaseScheme`, the core of `MLDSAW1.w1BaseSigner`). This signer reads the game's
  random oracle, so they are random-oracle assumptions. The justification (uncited, and FIPS 204
  §6.1, p. 22): analyses take `t₀` to be public, and its bits "can be reconstructed from a small
  number of signatures"; neither is proved. Uses: the flattened signer's unforgeability
  (`Applications/MLDSA/Flattened/Unforgeability.lean`) and the corollaries of the ring-binding and
  converted unforgeability theorems under them (`Applications/Ring/MLDSAW1NamedAssumptions.lean`).

## Idealizations used inside proofs

These are models of the game, not assumptions: a result proved in an idealized game says nothing
about the concrete function it replaces.

- **`ExpandA`, `ExpandS` and `SampleInBall` as random oracles in the ring signature's anonymity
  headlines.** `w1Scheme.expect_anonAdvantage_le_mldsa{44,65,87}` and their `_bind` and `_conv`
  forms (`Applications/Ring/MLDSAW1AnonOracle.lean`) average the advantage over the three
  oracles (`randomOraclePrimitives`), with the adversary indexed by them.
- **`ExpandA` as a random oracle (`Â` uniform).** `withExpandA`, `expect_regGap_withExpandA`,
  `idealAnonError`, `advantage_le_ideal` (`Applications/Ring/PublicW1/MLDSAPublicW1.lean`); the
  three-oracle anonymity headlines `advantage_le_bkm06` and `advantage_le_bkm06_mldsa{44,65,87}`
  and their `_of`, `_query`, `_checkParams` forms (`PublicW1/MLDSAPublicW1Regularity.lean`) and the
  hedged forms (`PublicW1/MLDSAPublicW1Hedged*.lean`); the regularity and collision lemmas at a
  uniform matrix (`Applications/MLDSA/Regularity/`: `T0Law`, `CommitCollision`
  (`expect_commitCollision_le`), `SignerRegularity`, `Instances*`).
- **`ExpandS` as a random oracle (a uniform `η`-box secret).** `withExpandS`
  (`PublicW1/MLDSAPublicW1ExpandS.lean`), `oracleSecretLaw`
  (`Applications/MLDSA/Regularity/StandinError44.lean`).
- **`SampleInBall` as a random oracle onto `B_τ`.** `withSampleInBall`, `oraclePrims`;
  `Applications/MLDSA/Signing/Floor.lean` states it as the standard idealization of
  its XOF stream, not proved.
- **`ExpandMask` and `H` uniform.** `Applications/MLDSA/Signing/Ideal.lean` (`maskUniform`).
- **The uniform-`t` key model.** `floorProb_mldsa44_uniformT_le`
  (`Applications/MLDSA/Signing/Floor.lean`, section `UniformT`), `Regularity/T0Mgf.lean`
  (section `UniformT`), `hybridKeyLaw` (`Applications/MLDSA/Signing/HybridKeyLaw.lean`).
- **Terms left unevaluated at the concrete FIPS 204 functions.** `regGapAt` and `collAt`
  (`Applications/Ring/MLDSAW1IdealDist.lean`) enter `w1Concrete.anonAdvantage_le_coupling` and its
  instances as defined averages: the numeric regularity and collision bounds hold for the
  random-oracle `ExpandA`, `ExpandS` and `SampleInBall`, where the headlines
  `w1Scheme.expect_anonAdvantage_le_mldsa{44,65,87}` apply them.

## Gaps

- MU ≤ n · SU (a guessing reduction from the multi-user to the single-user signature game) is not
  proved: the single-user adversary must sign for the other users with fresh coins per request.
- For a verification that reads the oracle, the unrestricted-class failure of the signature games
  is proved with the oracle as a table only, not with query access only.
- No Falcon-1024 base signer, so no Falcon-1024 assumption.
- No non-vacuity witness below `1` is proved for Module-SIS or SelfTargetMSIS (a class shown hard
  at some `ε < 1`); for Module-LWE the input-ignoring tests are hard at `0` (`mlweHard_const`).
- Barbosa et al. (ePrint 2023/246) is checked against its local copy; Devevey et al. (ePrint
  2023/245) and FIPS 206 are cited without a local copy checked.
- The text of Langlois–Stehlé has not been checked against the Module-LWE and Module-SIS forms.
- `regGapAt` and `collAt` at the concrete `ExpandA` would need an assumption on `ExpandA` (a PRF)
  that the library does not state; the numeric anonymity headlines take `ExpandA`, `ExpandS` and
  `SampleInBall` as random oracles instead.
-/
