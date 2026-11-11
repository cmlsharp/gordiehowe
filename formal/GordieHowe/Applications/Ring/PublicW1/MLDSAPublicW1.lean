-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.PublicValue
public import GordieHowe.Applications.MLDSA.Signing.PublishedKey
public import GordieHowe.Applications.MLDSA.Signing.Oracles
public import GordieHowe.Applications.MLDSA.Signing.RingSigner
public import GordieHowe.Applications.MLDSA.Signing.SampleInBallShape
public import GordieHowe.Applications.MLDSA.Signing.ChallengeMoments
public import GordieHowe.Applications.MLDSA.Spec.ExpandS
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# The ML-DSA ring signature publishing `w₁`

Every ring member publishes `(ρ, t₁, t₀)` (`PubKey`, with the key generation `keyGen`, in
`Applications/MLDSA/Signing/PublishedKey.lean`). The game has three random oracles: the
message-representative oracle `H_µ` (`µ = H(tr ‖ M′)`, FIPS 204 Algorithm 7 line 6), the
commitment-hash oracle `H` on `(µ, w₁)` (`c̃ = H(µ ‖ w1Encode(w₁))`, line 15), and the check
oracle `G`. The signer of position `i` runs the weighted ring loop of `RingSigner.lean` against
`H(µ ‖ w1Encode(w₁))` (`schemeOrc`, `ringAttemptOut`, `signLaw`), and refuses rings that are not
admissible at the game's oracles (`RingAdmissible`: the members' `µ_j` pairwise distinct, and the
public ring check against `G`; the refusal is a function of the published keys, the message and
the oracles, the same output for every signer). The ring relation is `ringVerify` at the signer's
position.
`pubSigner` is the resulting `PubSigner`, with `RingAdmissible` its refusal rule
(`PubSigner.Admit`): in the anonymity game the adversary chooses any ring holding the two users'
keys and sees `⊥` for a ring the signer refuses.

* `checkWeight`, `checkWeight_le_t0Weight`, `flatWeight_eq_one_of_le_checkWeight`: the
  bucket-free acceptance weight `acceptWeightLower` of `b = SampleInBall(c̃)·t₀`, rational
  (`coe_checkWeight`), at most the acceptance weight in every bucket vector; where it reaches
  `β_min` the member weight is one. The check compares rationals and has compiled code.
* `checkDefect`, `ringDefect`, `one_sub_le_colMass_of_ringDefect_le`,
  `massRatio_le_of_ringDefect_le`: the probability `δ_j` over a uniform `c̃` that member `j`'s
  check weight is below `β_min`, and their sum. A ring of defect `∑_j δ_j ≤ s < 1` has every column
  mass in `[1 - s, 1]` and mass ratio at most `1 / (1 - s)`.
* `CheckOrc`, `checkFails`, `RingCheck`, `RingAdmissible`, `LowDefect`: the check oracle from the
  points `(ring, member, sample)` to commitment hashes, independent of `H`; the check with
  tolerance `tol` that at most `tol` of the members' check weights at their `reps` hashes
  `G(l, j, r)` are below `β_min`: `n · reps` values of `G`, each read through one product
  `SampleInBall(c̃)·t₀,j` and one Poisson-binomial CDF.
* `checkError`, `expect_ringCheck_le`, `expect_exists_ringCheck_le`: over a uniform check oracle,
  a ring of defect at least `s` passes with probability at most
  `checkError reps tol s x = x^tol · exp(-(1 - 1/x) · reps · s)` for every `x ≥ 1` (the Chernoff
  lower tail); some ring of defect above `s` among a finite set of `C` rings passes with
  probability at most `C · checkError reps tol s x`.
* `valid_of_mem_support_signLaw`: every output of an honest signer whose attempt keeps with
  positive probability is valid.
* `ringPair`, `map_fst_signLaw`, `tvDist_le_oracleError`: the two signers of a challenge of
  defect at most `s` whose ring passes the check as a `PMF.RingPair`; their public-value laws are
  within `oracleError`, the `familyBound` of the rings of defect at most `s`;
  `ite_keeps_le_oracleError`, `signsValidly_of_keeps`: when some signer never keeps the error is
  at least one; otherwise, without the bad event `BadPass` (a ring of defect above `s` passing the
  check), every output is valid.
* `expect_oracleError_le`, `expect_ite_good_le`, `advantage_le`: anonymity against full key
  exposure (BKM06 Definition 4, as in `PubAnonAdversary.advantage_le_of_signsValidly`) with error
  `(Q + 1) · anonError + Q · wiError δ (Q · C) + C · checkError reps tol s x`, `C` the number of
  challenges of the adversary's set valid for any key vector (`PubAnonAdversary.ValidCountLe`),
  `anonError` the
  average over the users' coins of `2 / ((1 - s) θ)` times the largest regularity gap of an honest
  key (`signerRegGap`) plus the McDiarmid terms, for every defect budget `s < 1` and `x ≥ 1`.
* `advantage_le_concrete`: the same at the concrete primitives with the FIPS 204 `ExpandS`
  (`concretePrimitivesKeyGen`) of every approved parameter set (ML-DSA-44, 65, 87), with no
  hypothesis on the primitives (the laws and the encoding:
  `Applications/MLDSA/Signing/PublishedKey.lean`).
* `regGapAvg`, `expect_regGap_withExpandA`, `idealAnonError`, `advantage_le_ideal`:
  the game with `ExpandA` a random oracle (the primitives `withExpandA` with
  `ExpandA := G`, averaged over a uniform `G`), with the regularity term
  `2 / ((1 - s) θ) · n · regGapAvg`, `regGapAvg` the regularity gap averaged over the seed and a
  uniform
  matrix; the factor `n` bounds the largest of the `n` honest users' gaps by their sum. At the
  concrete primitives, with `SampleInBall` and `ExpandS` random oracles as well:
  `advantage_le_ideal_concrete` in `MLDSAPublicW1Regularity.lean`.
* `withSampleInBall`, `expect_withSampleInBall`, `expect_flatWeight_withSampleInBall`: the
  primitives with `SampleInBall := G` for a random oracle `G` onto the challenge set `B_τ`
  (`ChallengeBall`); averaged over a uniform `G`, the challenge of every commitment hash is uniform
  on `B_τ`.

## Scope of the model

- **The signer is the ideal-mask signer** (`Applications/MLDSA/Signing/Ideal.lean`: the mask `y`
  uniform on the mask box at every attempt). FIPS 204's hedged mask
  `y = ExpandMask(H(K ‖ rnd ‖ µ), κ)` takes at most about `2^256` values per signer, so an
  adversary with unbounded queries to the mask derivation can locate `w₁`; the step to hedged
  signing against query-bounded adversaries is `MLDSAPublicW1Hedged.lean`.
- **The message representatives are computed and compared.** `µ_j = H_µ(tr_j ‖ m)` is a value of
  the oracle `H_µ`, and `H` is keyed on `(µ, w₁)` as FIPS 204 keys `c̃`. The signer refuses rings
  with two equal `µ_j` (`MuDistinct`), so the members' points of `H` are distinct for every ring
  it signs on, whatever keys the adversary publishes. `H_µ`, `H` and `G` are independent random
  oracles; an implementation domain-separates them.
- **The check term `C · checkError` of `advantage_le` counts the adversary's candidate rings per
  key vector** (`BadPass` ranges over the challenges valid for the actual keys), since the
  adversary sees all of `G`. For an adversary whose choice reads `G` through `q` queries the term
  is `2 (q + 1) · checkError` (`advantage_le_query`, `MLDSAPublicW1Query.lean`, one challenge).
- **Refusals of rings of low defect** are bounded in `MLDSAPublicW1Refusal.lean`; the tolerance
  `tol` and the defect budget `s` are chosen per ring size (`CheckParams` in
  `MLDSAPublicW1Regularity.lean`, and the README).
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA PMF Finset
open scoped ENNReal BigOperators

variable {p : Params} (prims : Primitives p)

/-- The published `t₀`s of a ring. -/
def ringT0s (l : List (PubKey p prims)) : Fin l.length → RqVec p.k := fun j => (l.get j).2.2

/-- The members' oracle points `(tr_j, m)` of a ring and a message. -/
def ringPts {Msg : Type} (l : List (PubKey p prims)) (m : Msg) : Fin l.length → Bytes 64 × Msg :=
  fun j => (pubTr prims (l.get j), m)

variable [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]
  {Msg : Type} [Fintype Msg] [DecidableEq Msg]

/-- **The members' message representatives** `µ_j = H(tr_j ‖ m)` of a ring and a message. -/
def ringMus (Hmu : MuOrc Msg) (l : List (PubKey p prims)) (m : Msg) : Fin l.length → Bytes 64 :=
  fun j => Hmu (ringPts prims l m j)

/-! ### The public ring check -/

/-- **The ring defect** at the cut-off `β_min`: the sum of the members' check defects. -/
noncomputable def ringDefect (βmin : ℚ≥0) (l : List (PubKey p prims)) : ℝ :=
  ∑ j, checkDefect prims (Cutoff.const βmin) (ringT0s prims l j)

omit [Nonempty (MaskBox p)] in
/-- **Every mean member weight is at least one minus the member's check defect**, in every
bucket vector (`one_sub_checkDefect_le_expect_flatWeight`). -/
theorem one_sub_checkDefect_le_meanWeight (hp : SigningParams p) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (l : List (PubKey p prims)) (j : Fin l.length) (v : BucketVec p) :
    1 - checkDefect prims (Cutoff.const βmin) (ringT0s prims l j) ≤
      (ringWeights prims βmin (ringT0s prims l)).meanWeight j v :=
  one_sub_checkDefect_le_expect_flatWeight prims hp hβ0 (ringT0s prims l j) v

omit [Nonempty (MaskBox p)] in
/-- **The column masses of a ring of defect at most `s`** are at least `1 - s`
(`RingWeights.one_sub_le_colMass`). -/
theorem one_sub_le_colMass_of_ringDefect_le (hp : SigningParams p) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {l : List (PubKey p prims)} {s : ℝ}
    (hs : ringDefect prims βmin l ≤ s) (v : BucketVec p) :
    1 - s ≤ (ringWeights prims βmin (ringT0s prims l)).colMass v :=
  RingWeights.one_sub_le_colMass _ (one_sub_checkDefect_le_meanWeight prims hp hβ0 hβt l) hs v

omit [Nonempty (MaskBox p)] in
/-- **The mass ratio of a ring of defect at most `s < 1`** is at most `1 / (1 - s)`
(`RingWeights.massRatio_le_inv_one_sub`). -/
theorem massRatio_le_of_ringDefect_le (hp : SigningParams p) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {l : List (PubKey p prims)} {s : ℝ} (hs : ringDefect prims βmin l ≤ s)
    (hs1 : s < 1) : (ringWeights prims βmin (ringT0s prims l)).massRatio ≤ (1 - s)⁻¹ :=
  RingWeights.massRatio_le_inv_one_sub _ (one_sub_checkDefect_le_meanWeight prims hp hβ0 hβt l)
    hs hs1

/-- Rings of published keys have decidable equality. -/
instance [DecidableEq prims.Power2High] (N : ℕ) : DecidableEq (RingOf (PubKey p prims) N) :=
  fun a b => decidable_of_iff (a.1 = b.1) Subtype.ext_iff.symm

/-- **The check oracle** for rings of at most `N` published keys and `reps` samples per member: a
random oracle, independent of the scheme's oracle, from the points `(ring, member, sample)` to
commitment hashes. -/
abbrev CheckOrc (p : Params) (prims : Primitives p) (N reps : ℕ) : Type :=
  RingOf (PubKey p prims) N × Fin N × Fin reps → CommitHashBytes p

/-- **The failed check samples of a ring** at the cut-off `β_min` against the check oracle `G`:
the number of pairs of a member `j` and a sample `r < reps` at which the check weight of `t₀,j`
at the commitment hash `G(l, j, r)` is below `β_min`. -/
def checkFails (βmin : ℚ≥0) {N reps : ℕ} (G : CheckOrc p prims N reps)
    (l : RingOf (PubKey p prims) N) : ℕ :=
  (univ.filter fun jr : Fin l.1.length × Fin reps =>
    checkWeight prims (ringT0s prims l.1 jr.1) (G (l, Fin.castLE l.2 jr.1, jr.2)) < βmin).card

/-- **The public ring check** at the cut-off `β_min` with tolerance `tol` against the check oracle
`G`: at most `tol` of the pairs of a member `j` and a sample `r < reps` have the check weight of
`t₀,j` at the commitment hash `G(l, j, r)` below `β_min` (`checkFails`). A function of the
published keys and `G` only. -/
def RingCheck (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (G : CheckOrc p prims N reps)
    (l : RingOf (PubKey p prims) N) : Prop :=
  checkFails prims βmin G l ≤ tol

/-- The public ring check is decided by comparing the count of failed samples with `tol`. -/
instance (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (G : CheckOrc p prims N reps)
    (l : RingOf (PubKey p prims) N) : Decidable (RingCheck prims βmin tol G l) :=
  inferInstanceAs (Decidable (checkFails prims βmin G l ≤ tol))

/-- The oracles of the game: the scheme's oracles (the message-representative oracle `H_µ` and
the commitment-hash oracle `H`) and the check oracle `G`. -/
abbrev GameOrc {p : Params} (prims : Primitives p) (Msg : Type) (N reps : ℕ) : Type :=
  SchOrc p Msg × CheckOrc p prims N reps

/-- **Distinct message representatives**: the members' `µ_j = H_µ(tr_j ‖ m)` of a ring and a
message are pairwise distinct. The signer computes them. -/
def MuDistinct (Hmu : MuOrc Msg) {N : ℕ} (l : RingOf (PubKey p prims) N) (m : Msg) : Prop :=
  (l.1.map fun x => Hmu (pubTr prims x, m)).Nodup

/-- **An admissible ring and message at the game's oracles** `((H_µ, H), G)`: distinct message
representatives `µ_j` and the public ring check with tolerance `tol` against `G`. A function of
the published keys, the message and the oracles only. -/
def RingAdmissible (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (HG : GameOrc prims Msg N reps)
    (l : RingOf (PubKey p prims) N) (m : Msg) : Prop :=
  MuDistinct prims HG.1.1 l m ∧ RingCheck prims βmin tol HG.2 l

/-- **Admissibility is decided classically**: `RingCheck` compares real defects. -/
noncomputable instance (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (HG : GameOrc prims Msg N reps)
    (l : RingOf (PubKey p prims) N) (m : Msg) : Decidable (RingAdmissible prims βmin tol HG l m) :=
  Classical.dec _

/-- **A ring of defect at most `s`** at the cut-off `β_min`. -/
def LowDefect (βmin : ℚ≥0) (s : ℝ) {N : ℕ} (l : RingOf (PubKey p prims) N) : Prop :=
  ringDefect prims βmin l.1 ≤ s

/-- **One attempt of the ring signer with its output**: `weightedAttemptWith` of the member
weights of the ring, the signer's idealized attempt with `Â = ExpandA(ρ)`, its flattening coin,
and the signature output, against the members' points of the oracle `H`. -/
noncomputable def ringAttemptOut (βmin : ℚ≥0) (sk : SecretKey p) (l : List (PubKey p prims))
    (i : Fin l.length) (m : Msg) (H : Orc p Msg) :
    PMF (Option (BucketVec p × FIPSSignature p prims)) :=
  weightedAttemptWith (ringWeights prims βmin (ringT0s prims l)) i (maskUniform p)
    (realBuckets (prims.expandA sk.rho)) (attemptAccept prims sk (prims.expandA sk.rho))
    (fun a => (flattenCoin prims sk (Cutoff.const βmin) a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk
        (Cutoff.const βmin))
    (fun y c => attemptOutput prims sk (prims.expandA sk.rho) (y, c)) (ringOf (ringPts prims l m) H)

variable [Inhabited prims.Hint] [Fintype prims.Hint]

open Classical in
/-- **The ring signing law** at the game's oracles `((H_µ, H), G)`: on a ring and message
admissible at the oracles with tolerance `tol` (`RingAdmissible`) with the position in range, the
unbounded ring loop against `H(µ ‖ w1Encode(w₁))` (`schemeOrc`), outputting the kept `w₁` with its
signature (a fixed default if it never keeps); on other rings the refusal, the same default for
every signer. -/
noncomputable def signLaw (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (HG : GameOrc prims Msg N reps)
    (sk : SecretKey p) (R : RingOf (PubKey p prims) N) (i : ℕ) (m : Msg) :
    PMF (BucketVec p × FIPSSignature p prims) :=
  if h : i < R.1.length ∧ RingAdmissible prims βmin tol HG R m then
    (untilSome (ringAttemptOut prims βmin sk R.1 ⟨i, h.1⟩ m (schemeOrc HG.1))).map
      fun o => o.getD default
  else PMF.pure default

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [DecidableEq prims.Hint]

/-- **The check error** at `reps` samples per member, tolerance `tol`, defect budget `s` and
Chernoff parameter `x`: `x^tol · exp(-(1 - 1/x) · reps · s)`, the bound of
`expect_ringCheck_le` for `x ≥ 1`. -/
noncomputable def checkError (reps tol : ℕ) (s x : ℝ) : ℝ :=
  x ^ tol * Real.exp (-((1 - x⁻¹) * (reps * s)))

omit nttOps in
/-- The check error is nonnegative for `x ≥ 0`. -/
theorem checkError_nonneg (reps tol : ℕ) (s : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ checkError reps tol s x := by
  unfold checkError
  positivity

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
open Classical in
/-- **A ring of defect at least `s` passes the check with tolerance `tol` with probability at most
`checkError reps tol s x`** over a uniform check oracle, for every `x ≥ 1` (the Chernoff lower
tail): the `n · reps` check points `(l, j, r)` are distinct, so the failures are independent with
probabilities the check defects `δ_j`; `1[F ≤ tol] ≤ x^tol · x^(-F)` for the number `F` of
failures, whose expectation is `x^tol · ∏_j (1 - (1 - 1/x) δ_j)^reps ≤
x^tol · exp(-(1 - 1/x) · reps ∑_j δ_j)` (`PMF.expect_comp_embedding`, `PMF.expect_prod_apply`). -/
theorem expect_ringCheck_le (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (l : RingOf (PubKey p prims) N)
    {s x : ℝ} (hs : s ≤ ringDefect prims βmin l.1) (hx : 1 ≤ x) :
    𝔼 G : CheckOrc p prims N reps, (if RingCheck prims βmin tol G l then 1 else 0 : ℝ) ≤
      checkError reps tol s x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h1x : 0 ≤ 1 - x⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hx)
  set ψ : Fin l.1.length × Fin reps → CommitHashBytes p → ℝ := fun jr c =>
    if checkWeight prims (ringT0s prims l.1 jr.1) c < βmin then x⁻¹ else 1
  have hψ0 : ∀ jr c, 0 ≤ ψ jr c := fun jr c => by
    simp only [ψ]
    split_ifs <;> positivity
  let e : Fin l.1.length × Fin reps ↪ RingOf (PubKey p prims) N × Fin N × Fin reps :=
    ⟨fun jr => (l, Fin.castLE l.2 jr.1, jr.2), fun a b h => by
      simp only [Prod.mk.injEq, Fin.castLE_inj] at h
      exact Prod.ext h.2.1 h.2.2⟩
  have h1 : ∀ G : CheckOrc p prims N reps,
      (if RingCheck prims βmin tol G l then 1 else 0 : ℝ) ≤ x ^ tol * ∏ jr, ψ jr (G (e jr)) :=
    fun G => by
    have hprod : ∏ jr, ψ jr (G (e jr)) = x⁻¹ ^ checkFails prims βmin G l := by
      simp only [ψ]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      rfl
    rw [hprod, inv_pow, ← div_eq_mul_inv]
    split_ifs with h
    · rw [le_div_iff₀ (pow_pos hx0 _), one_mul]
      exact pow_le_pow_right₀ hx h
    · positivity
  have hψ : ∀ jr, 𝔼 c, ψ jr c =
      1 - (1 - x⁻¹) * checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 jr.1) := fun jr => by
    have h : ∀ c, ψ jr c = 1 - (1 - x⁻¹) *
        (if checkWeight prims (ringT0s prims l.1 jr.1) c < βmin then 1 else 0) := fun c => by
      simp only [ψ]
      split_ifs <;> ring
    rw [Finset.expect_congr rfl fun c _ => h c, Finset.expect_sub_distrib,
      Finset.expect_const univ_nonempty, ← Finset.mul_expect, checkDefect]
  have hsum : ∑ jr : Fin l.1.length × Fin reps, checkDefect prims (Cutoff.const βmin) (ringT0s
      prims l.1 jr.1) =
      reps * ringDefect prims βmin l.1 := by
    rw [Fintype.sum_prod_type, ringDefect, Finset.mul_sum]
    simp
  calc 𝔼 G : CheckOrc p prims N reps, (if RingCheck prims βmin tol G l then 1 else 0 : ℝ)
      ≤ 𝔼 G : CheckOrc p prims N reps, x ^ tol * ∏ jr, ψ jr (G (e jr)) :=
        Finset.expect_le_expect fun G _ => h1 G
    _ = x ^ tol * ∏ jr, 𝔼 c, ψ jr c := by
        rw [← Finset.mul_expect, PMF.expect_comp_embedding e (fun g => ∏ jr, ψ jr (g jr)),
          PMF.expect_prod_apply]
    _ ≤ x ^ tol * ∏ jr : Fin l.1.length × Fin reps,
          Real.exp (-((1 - x⁻¹) * checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1
              jr.1))) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun jr _ => Finset.expect_nonneg fun c _ => hψ0 jr c) fun jr _ => ?_) (by positivity)
        rw [hψ jr]
        linarith [Real.add_one_le_exp (-((1 - x⁻¹) *
          checkDefect prims (Cutoff.const βmin) (ringT0s prims l.1 jr.1)))]
    _ = x ^ tol * Real.exp (-((1 - x⁻¹) * (reps * ringDefect prims βmin l.1))) := by
        rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, hsum]
    _ ≤ checkError reps tol s x :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)) h1x))) (by positivity)

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
open Classical in
/-- **The union bound over a finite set of rings**: over a uniform check oracle, some ring of
`F` (through `ring`) of defect above `s` passes the check with tolerance `tol` with probability at
most `|F| · checkError reps tol s x`, for every `x ≥ 1` (`expect_ringCheck_le`). -/
theorem expect_exists_ringCheck_le (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} {α : Type*}
    (F : Finset α) (ring : α → RingOf (PubKey p prims) N) (s : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    𝔼 G : CheckOrc p prims N reps, (if ∃ a ∈ F, s < ringDefect prims βmin (ring a).1 ∧
        RingCheck prims βmin tol G (ring a) then 1 else 0 : ℝ) ≤
      F.card * checkError reps tol s x := by
  set f : α → CheckOrc p prims N reps → ℝ := fun a G =>
    if s < ringDefect prims βmin (ring a).1 ∧ RingCheck prims βmin tol G (ring a) then 1 else 0
  have hf0 : ∀ a G, 0 ≤ f a G := fun a G => by simp only [f]; split_ifs <;> norm_num
  calc 𝔼 G : CheckOrc p prims N reps, (if ∃ a ∈ F, s < ringDefect prims βmin (ring a).1 ∧
        RingCheck prims βmin tol G (ring a) then 1 else 0 : ℝ)
      ≤ 𝔼 G : CheckOrc p prims N reps, ∑ a ∈ F, f a G := Finset.expect_le_expect fun G _ => by
        split_ifs with h
        · obtain ⟨a, ha, h⟩ := h
          have : f a G = 1 := if_pos h
          exact this ▸ Finset.single_le_sum (fun a _ => hf0 a G) ha
        · exact Finset.sum_nonneg fun a _ => hf0 a G
    _ = ∑ a ∈ F, 𝔼 G : CheckOrc p prims N reps, f a G := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _a ∈ F, checkError reps tol s x := Finset.sum_le_sum fun a _ => by
        by_cases hd : s < ringDefect prims βmin (ring a).1
        · simp only [f, hd, true_and]
          exact expect_ringCheck_le prims βmin tol (ring a) hd.le hx
        · simp only [f, hd, false_and, if_false, Finset.expect_const_zero]
          exact checkError_nonneg reps tol s (zero_le_one.trans hx)
    _ = F.card * checkError reps tol s x := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The ML-DSA ring signer publishing `w₁`**, with rings of at most `N` published keys and
messages `Msg`, at the cut-off `β_min`, with `reps` check samples per member and at most `tol`
failed samples per ring, and the encoding
`enc` of recomputed commitments as bucket vectors: published keys `(ρ, t₁, t₀)`, the game's
oracles `((H_µ, H), G)` (`H_µ` on `(tr, m)`, `H` on `(µ, w₁)`, `G` the check oracle), public value
`w₁`, base signature `(c̃, z, h)`, the ring relation `ringVerify` against `H(µ ‖ w1Encode(w₁))`
at the signer's position, and the refusal rule `RingAdmissible` at the game's oracles. Reducible, so
instance search reaches the named types of its fields. -/
@[reducible] noncomputable def pubSigner (N : ℕ) (βmin : ℚ≥0) (reps tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) : PubSigner N Msg where
  PK := PubKey p prims
  SK := SecretKey p
  KeyCoins := Bytes 32
  Pub := BucketVec p
  Sig := FIPSSignature p prims
  Orc := GameOrc prims Msg N reps
  Stmt := PubStmt (PubKey p prims) Msg (BucketVec p) N
  Wit := PubWit (FIPSSignature p prims)
  keyGen := keyGen prims
  signLaw HG sk R i m := signLaw prims βmin tol HG sk R i m
  stmt R m w1 := ⟨R, m, w1⟩
  wit i sig := ⟨i, sig⟩
  stmtPub := PubStmt.pub
  stmtPub_stmt _ _ _ := rfl
  rel HG := {x | ∃ h : x.2.idx < x.1.ring.1.length,
    ringVerify prims (schemeOrc HG.1) enc (pubPk prims (x.1.ring.1.get ⟨x.2.idx, h⟩)) x.1.msg
      x.1.pub x.2.sig = true}
  Admit HG R m := RingAdmissible prims βmin tol HG R m

/-- **Every output of an honest signer that keeps with positive probability is valid**: for the
key of `seed` with `‖s₂‖∞ ≤ η`, at its position of a ring admissible at the game's oracles, if one
ring attempt keeps with positive probability then every output of the signing law verifies, given
the signing and verification laws and a coherent encoding `enc`. -/
theorem valid_of_mem_support_signLaw (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {βmin : ℚ≥0} {tol N reps : ℕ} {seed : Bytes 32}
    (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta) {R : RingOf (PubKey p prims) N} {i : ℕ}
    (hi : i < R.1.length) (HG : GameOrc prims Msg N reps)
    (m : Msg) (hadm : RingAdmissible prims βmin tol HG R m)
    (hkey : R.1.get ⟨i, hi⟩ = (keyGen prims seed).1)
    (hkeep : ringAttemptOut prims βmin (keyGen prims seed).2 R.1 ⟨i, hi⟩ m (schemeOrc HG.1) none ≠ 1)
    {x : BucketVec p × FIPSSignature p prims}
    (hx : x ∈ (signLaw prims βmin tol HG (keyGen prims seed).2 R i m).support) :
    ∃ h : i < R.1.length,
      ringVerify prims (schemeOrc HG.1) enc (pubPk prims (R.1.get ⟨i, h⟩)) m x.1 x.2 = true := by
  rw [signLaw, dif_pos ⟨hi, hadm⟩, mem_support_map_iff] at hx
  obtain ⟨o, ho, rfl⟩ := hx
  cases o with
  | none =>
    exact absurd ((mem_support_iff _ _).1 ho) (by rw [untilSome_apply_none hkeep]; simp)
  | some vσ =>
    obtain ⟨w, σ⟩ := vσ
    obtain ⟨y, rfl, hacc, rfl⟩ := exists_of_mem_support_weightedAttemptWith _ _ _ _ _ _ _ _ _
      (mem_support_of_mem_support_untilSome ho)
    refine ⟨hi, ?_⟩
    have key := ringVerify_attemptOutput prims h_laws hv henc (seed := seed)
      (pk := (keyGenFromSeed p prims seed).1) (sk := (keyGenFromSeed p prims seed).2) rfl hs2
      (schemeOrc HG.1) m y
    simp only [ringOf, ringPts, hkey, keyGen, pubTr, keyGenFromSeed_rho] at hacc
    simp only [Option.getD_some, pubPk, hkey, keyGen, ringOf, ringPts, pubTr]
    exact key hacc

/-- Distinct message representatives make the members' points `µ_j` of the commitment-hash oracle
distinct. -/
theorem ringMus_injective {Hmu : MuOrc Msg} {N : ℕ} {l : RingOf (PubKey p prims) N} {m : Msg}
    (hnd : MuDistinct prims Hmu l m) : Function.Injective (ringMus prims Hmu l.1 m) := by
  intro j k h
  have hx := List.inj_on_of_nodup_map hnd (List.get_mem l.1 j) (List.get_mem l.1 k) h
  exact (List.Nodup.get_inj_iff (List.Nodup.of_map _ hnd)).1 hx

/-- The `none` mass of an attempt is that of its relabelling. -/
theorem _root_.PMF.map_optionMap_apply_none {α β : Type*} (A : PMF (Option α)) (f : α → β) :
    A.map (Option.map f) none = A none := by
  rw [map_apply, tsum_eq_single none fun o ho => by cases o <;> simp_all]
  simp

section Assembly

variable (N : ℕ) (βmin : ℚ≥0) (reps tol : ℕ) (enc : Vector prims.High p.k → BucketVec p) {n : ℕ}

/-- **The two signers of a challenge as a ring pair at the members' points `pt`**: the member
weights of the published `t₀`s and the two users' ring signers at their positions. -/
@[reducible]
noncomputable def ringPairAt (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {K : Type}
    (keys : Fin n → Bytes 32) (c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n)
    (hc : c.Valid _ keys) (pt : Fin c.ring.1.length ↪ K) :
    PMF.RingPair K (BucketVec p) (CommitHashBytes p) where
  Mem := Fin c.ring.1.length
  pt := pt
  wts := ringWeights prims βmin (ringT0s prims c.ring.1)
  pos b := ⟨c.idx b, by cases b <;> simp [RingChoice.idx, hc.idx₀_lt, hc.idx₁_lt]⟩
  signer b := flatLoopSigner prims (keyGen prims (keys (c.user b))).2
    (prims.expandA (keyGen prims (keys (c.user b))).2.rho) hp (cut := Cutoff.const βmin) hβ0 hβt

/-- **The two signers of a challenge with distinct message representatives as a ring pair**:
`ringPairAt` at the members' points `µ_j = H_µ(tr_j ‖ m)` of the commitment-hash oracle. -/
@[reducible]
noncomputable def ringPair (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg)
    (c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n) (hc : c.Valid _ keys)
    (hmu : MuDistinct prims Hmu c.ring c.msg) :
    PMF.RingPair (Bytes 64) (BucketVec p) (CommitHashBytes p) :=
  ringPairAt prims N βmin reps tol enc hp hβ0 hβt keys c hc
    ⟨ringMus prims Hmu c.ring.1 c.msg, ringMus_injective prims hmu⟩

/-- **The public-value law of a signer of a challenge admissible at the game's oracles** is the
loop of its ring-pair attempt against the commitment-hash oracle `H`, with the default for a loop
that never keeps. -/
theorem map_fst_signLaw (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (keys : Fin n → Bytes 32) (c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n)
    (hc : c.Valid _ keys) (HG : GameOrc prims Msg N reps)
    (hA : RingAdmissible prims βmin tol HG c.ring c.msg) (b : Bool) :
    (c.signLaw HG keys b).map Prod.fst =
      (untilSome ((ringPair prims N βmin reps tol enc hp hβ0 hβt keys HG.1.1 c hc hA.1).attempt b
        HG.1.2)).map fun o => o.getD default := by
  have hlt : c.idx b < c.ring.1.length := by
    cases b <;> simp [RingChoice.idx, hc.idx₀_lt, hc.idx₁_lt]
  show (MLDSAW1.signLaw prims βmin tol HG (keyGen prims (keys (c.user b))).2 c.ring (c.idx b)
    c.msg).map Prod.fst = _
  unfold MLDSAW1.signLaw
  rw [dif_pos ⟨hlt, hA⟩, map_comp]
  have hf : (Prod.fst ∘ fun o : Option (BucketVec p × FIPSSignature p prims) => o.getD default) =
      (fun o => o.getD default) ∘ Option.map Prod.fst := by
    funext o; cases o <;> rfl
  rw [hf, ← map_comp, untilSome_map_optionMap]
  unfold ringAttemptOut
  rw [map_weightedAttemptWith]
  rfl

/-- The attempt with its output keeps exactly when the ring-pair attempt does. -/
theorem ringAttemptOut_apply_none (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (keys : Fin n → Bytes 32) (Hmu : MuOrc Msg)
    (c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n)
    (hc : c.Valid _ keys) (hmu : MuDistinct prims Hmu c.ring c.msg) (H : ChOrc p) (b : Bool) :
    ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1
        ((ringPair prims N βmin reps tol enc hp hβ0 hβt keys Hmu c hc hmu).pos b) c.msg
        (schemeOrc (Hmu, H)) none =
      (ringPair prims N βmin reps tol enc hp hβ0 hβt keys Hmu c hc hmu).attempt b H none := by
  rw [← map_optionMap_apply_none _ Prod.fst]
  exact congrArg (fun q => q none) (map_weightedAttemptWith
    (ringWeights prims βmin (ringT0s prims c.ring.1)) _ (maskUniform p) _ _ _ _ _ _)


/-! ### The regularity gap at uniform key material -/

section UniformKeys

open LatticeCrypto TransformOps

/-- **The average regularity gap with a uniform matrix**: `signerRegGap` (whose challenge `c̃` is
uniform, `c = SampleInBall(c̃)`) at the key of a uniform seed's `ρ`, `K` and
`(s₁, s₂) = ExpandS(ρ')` (FIPS 204 Algorithm 33, the concrete `ExpandS` of the primitives) with
the matrix `Â` uniform and independent of the seed. -/
noncomputable def regGapAvg (βmin : ℚ≥0) : ℝ :=
  𝔼 seed : Bytes 32, 𝔼 aHat : TqMatrix p.k p.l,
    signerRegGap prims (idealSecretKey prims (prims.expandSeed seed).1 (prims.expandSeed seed).2.2
      aHat (prims.expandS (prims.expandSeed seed).2.1)) aHat (Cutoff.const βmin)

/-- **With `ExpandA` a random oracle, the average over the oracle and honest key generation of
the regularity gap is `regGapAvg`**: the oracle's value at `ρ` is uniform
(`PMF.expect_apply_eval`). -/
theorem expect_regGap_withExpandA (βmin : ℚ≥0) :
    𝔼 G : Bytes 32 → TqMatrix p.k p.l, 𝔼 seed : Bytes 32,
        signerRegGap (withExpandA prims G) (keyGen (withExpandA prims G) seed).2
          ((withExpandA prims G).expandA (keyGen (withExpandA prims G) seed).2.rho)
              (Cutoff.const βmin) =
      regGapAvg prims βmin := by
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl fun seed _ => ?_
  exact PMF.expect_apply_eval (prims.expandSeed seed).1 (fun aHat => signerRegGap prims
    (idealSecretKey prims (prims.expandSeed seed).1 (prims.expandSeed seed).2.2 aHat
      (prims.expandS (prims.expandSeed seed).2.1)) aHat (Cutoff.const βmin))

end UniformKeys

end Assembly

/-! ### `SampleInBall` as a random oracle -/

section RandomChallenge

open LatticeCrypto TransformOps

/-- **The primitives with `SampleInBall` replaced by `G`**: the primitives of the game in which
`SampleInBall` (FIPS 204 Algorithm 29) is a random oracle `G`. -/
abbrev withSampleInBall (G : CommitHashBytes p → ChallengePoly) : Primitives p :=
  { prims with sampleInBall := G }

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] [Inhabited prims.Hint]
  [Fintype prims.Hint] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [DecidableEq prims.Hint] in
/-- **With `SampleInBall` a random oracle onto `B_τ`, every challenge is uniform on `B_τ`**: for
`G` uniform among the functions from commitment hashes to the challenge set `B_τ` (FIPS 204 §2.3,
`τ ≤ 256`), `𝔼_G 𝔼_c̃ f(c̃, G(c̃)) = 𝔼_c̃ 𝔼_{c ∈ B_τ} f(c̃, c)`. -/
theorem expect_withSampleInBall (hτ : p.tau ≤ ringDegree)
    (f : CommitHashBytes p → ChallengePoly → ℝ) :
    𝔼 G : CommitHashBytes p → ChallengeBall p.tau, 𝔼 cTilde : CommitHashBytes p,
        f cTilde ((withSampleInBall prims fun c => (G c).1).sampleInBall cTilde) =
      𝔼 cTilde : CommitHashBytes p, 𝔼 c : ChallengeBall p.tau, f cTilde c.1 := by
  have := challengeBall_nonempty hτ
  rw [Finset.expect_comm]
  exact Finset.expect_congr rfl fun cTilde _ =>
    PMF.expect_apply_eval cTilde (fun c : ChallengeBall p.tau => f cTilde c.1)

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Inhabited prims.Hint] [Fintype prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [DecidableEq prims.Hint] in
/-- **The mean member weight with `SampleInBall` a random oracle onto `B_τ`**: averaged over the
oracle and the commitment hash, the member weight `min(1, aw / β_min)` of `t₀` in bucket vector
`v` is its average over a uniform challenge `c ∈ B_τ` with the shift `b = c·t₀`. -/
theorem expect_flatWeight_withSampleInBall (hτ : p.tau ≤ ringDegree) (βmin : ℚ≥0)
    (t0 : RqVec p.k) (v : BucketVec p) :
    𝔼 G : CommitHashBytes p → ChallengeBall p.tau, 𝔼 cTilde : CommitHashBytes p,
        (flatWeight (withSampleInBall prims fun c => (G c).1) (Cutoff.const βmin) t0 (v, cTilde) :
            ℝ≥0∞).toReal =
      𝔼 c : ChallengeBall p.tau, (min 1 (ENNReal.ofReal (acceptWeight p.gamma2 p.beta p.omega
        (centeredCoeffs (c.1 • t0)) fun x => (v x).val) / βmin)).toReal := by
  have h := expect_withSampleInBall prims hτ fun _ c => (min 1 (ENNReal.ofReal
    (acceptWeight p.gamma2 p.beta p.omega (centeredCoeffs (c • t0)) fun x => (v x).val) /
      βmin)).toReal
  rw [Finset.expect_const univ_nonempty] at h
  simp only [coe_flatWeight, coe_t0Weight]
  exact h

end RandomChallenge

/-! ### Anonymity -/

section Main

open IOP GordieHowe.SPBCS GordieHowe.QROM

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e} {n Q : ℕ}
  (A : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n Q)

/-- The valid challenges of the adversary's set of ring defect at most `s` (`LowDefect`) at the
users' coins `keys`. -/
abbrev ValidChoice (s : ℝ) (keys : Fin n → _root_.MLDSA.Bytes 32) : Type :=
  {c : A.choices // c.1.Valid _ keys ∧ LowDefect prims βmin s c.1.ring}

open Classical in
noncomputable instance (s : ℝ) (keys : Fin n → _root_.MLDSA.Bytes 32) :
    Fintype (ValidChoice prims A s keys) :=
  Subtype.fintype _

/-- **The rings of the challenges of defect at most `s`** at the users' coins `keys`, as ring
pairs at the positions (`ringPairAt` at `Fin N`); their variance proxies and errors do not read the
points. -/
@[reducible]
noncomputable def family (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (s : ℝ)
    (keys : Fin n → _root_.MLDSA.Bytes 32) (c : ValidChoice prims A s keys) :
    PMF.RingPair (Fin N) (BucketVec p) (CommitHashBytes p) :=
  ringPairAt prims N βmin reps tol enc hp hβ0 hβt keys c.1.1 c.2.1 (Fin.castLEEmb c.1.1.ring.2)

/-- The valid challenges of the adversary's set of ring defect at most `s` whose message
representatives at `H_µ` are distinct. -/
abbrev ValidChoiceMu (s : ℝ) (keys : Fin n → _root_.MLDSA.Bytes 32) (Hmu : MuOrc Msg) : Type :=
  {c : A.choices // c.1.Valid _ keys ∧ MuDistinct prims Hmu c.1.ring c.1.msg ∧
    LowDefect prims βmin s c.1.ring}

open Classical in
noncomputable instance (s : ℝ) (keys : Fin n → _root_.MLDSA.Bytes 32) (Hmu : MuOrc Msg) :
    Fintype (ValidChoiceMu prims A s keys Hmu) :=
  Subtype.fintype _

/-- **The rings of the challenges of defect at most `s` with distinct message representatives**
at the users' coins and `H_µ`, as ring pairs at the members' points `µ_j` (`ringPair`). -/
@[reducible]
noncomputable def familyMu (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (s : ℝ)
    (keys : Fin n → _root_.MLDSA.Bytes 32) (Hmu : MuOrc Msg) (c : ValidChoiceMu prims A s keys Hmu) :
    PMF.RingPair (_root_.MLDSA.Bytes 64) (BucketVec p) (CommitHashBytes p) :=
  ringPair prims N βmin reps tol enc hp hβ0 hβt keys Hmu c.1.1 c.2.1 c.2.2.1

/-- The challenge of `ValidChoice` under one of `ValidChoiceMu`. -/
def ValidChoiceMu.toValidChoice {s : ℝ} {keys : Fin n → _root_.MLDSA.Bytes 32} {Hmu : MuOrc Msg}
    (c : ValidChoiceMu prims A s keys Hmu) : ValidChoice prims A s keys :=
  ⟨c.1, c.2.1, c.2.2.2⟩

open Classical in
/-- **The anonymity error at the users' coins and the scheme's oracles `(H_µ, H)`**: the bound
`familyBound` over the commitment-hash oracle `H` of the rings of the challenges of defect at
most `s` with distinct message representatives, at the threshold fraction `θ`, or zero without
such challenges. -/
noncomputable def oracleError (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (s θ : ℝ) (keys : Fin n → _root_.MLDSA.Bytes 32) (H : SchOrc p Msg) : ℝ :=
  if h : Nonempty (ValidChoiceMu prims A s keys H.1) then
    haveI := h; familyBound (familyMu prims A hp hβ0 hβt s keys H.1) θ H.2
  else 0

/-- **The largest regularity gap** of the honest users' keys (`signerRegGap`). -/
noncomputable def maxRegGap (βmin : ℚ≥0) [NeZero n] (keys : Fin n → _root_.MLDSA.Bytes 32) : ℝ :=
  univ.sup' univ_nonempty fun u => signerRegGap prims (keyGen prims (keys u)).2
    (prims.expandA (keyGen prims (keys u)).2.rho) (Cutoff.const βmin)

open Classical in
/-- The largest deviation variance proxy of the rings of defect at most `s`. -/
noncomputable def maxDevVar (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (s θ : ℝ)
    (keys : Fin n → _root_.MLDSA.Bytes 32) : ℝ :=
  if h : Nonempty (ValidChoice prims A s keys) then
    haveI := h; univ.sup' univ_nonempty fun c => (family prims A hp hβ0 hβt s keys c).devVar θ
  else 0

open Classical in
/-- The largest weight variance proxy of the rings of defect at most `s`. -/
noncomputable def maxCountVar (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (s θ : ℝ)
    (keys : Fin n → _root_.MLDSA.Bytes 32) : ℝ :=
  if h : Nonempty (ValidChoice prims A s keys) then
    haveI := h; univ.sup' univ_nonempty fun c => (family prims A hp hβ0 hβt s keys c).countVar θ
  else 0

/-- **The good event of the scheme's oracles**: the two signers of every challenge of defect at
most `s` with distinct message representatives keep with positive probability. -/
def Keeps (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (s : ℝ)
    (keys : Fin n → _root_.MLDSA.Bytes 32) (H : SchOrc p Msg) : Prop :=
  ∀ (c : ValidChoiceMu prims A s keys H.1) (b : Bool),
    (familyMu prims A hp hβ0 hβt s keys H.1 c).attempt b H.2 none ≠ 1

/-- **The bad event of the check oracle** at the users' coins `keys`: the ring of some challenge of
the adversary's set valid for `keys` has defect above `s` and passes the check against `G`. Only
the challenges valid for the actual keys count: the set, fixed before the keys, may hold candidate
rings for every key vector. -/
def BadPass (s : ℝ) (keys : Fin n → _root_.MLDSA.Bytes 32) (G : CheckOrc p prims N reps) : Prop :=
  ∃ c ∈ A.validChoices keys, s < ringDefect prims βmin c.ring.1 ∧ RingCheck prims βmin tol G c.ring

variable {prims A}

/-- A valid challenge's position of user `b` holds user `b`'s published key. -/
theorem get_idx_eq {keys : Fin n → _root_.MLDSA.Bytes 32}
    {c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n}
    (hc : c.Valid _ keys) (b : Bool) (hlt : c.idx b < c.ring.1.length) :
    c.ring.1.get ⟨c.idx b, hlt⟩ = (keyGen prims (keys (c.user b))).1 := by
  cases b
  · simp only [RingChoice.idx, RingChoice.user, List.get_eq_getElem]
    exact hc.key₀
  · simp only [RingChoice.idx, RingChoice.user, List.get_eq_getElem]
    exact hc.key₁

/-- **Without the bad event, the rings of the challenges admissible at the game's oracles have
defect at most `s`.** -/
theorem lowDefect_of_not_badPass {s : ℝ} {keys : Fin n → _root_.MLDSA.Bytes 32}
    {HG : GameOrc prims Msg N reps} (hB : ¬ BadPass prims A s keys HG.2)
    {c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n} (hcm : c ∈ A.choices)
    (hc : c.Valid _ keys) (hA : RingAdmissible prims βmin tol HG c.ring c.msg) :
    LowDefect prims βmin s c.ring :=
  not_lt.1 fun hlt => hB ⟨c, (A.mem_validChoices).2 ⟨hcm, hc⟩, hlt, hA.2⟩

/-- The rings of defect at most `s < 1` have positive mass
(`one_sub_le_colMass_of_ringDefect_le`). -/
theorem family_mass_pos (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s : ℝ}
    (hs1 : s < 1) (keys : Fin n → _root_.MLDSA.Bytes 32) (c : ValidChoice prims A s keys) :
    0 < (family prims A hp hβ0 hβt s keys c).wts.mass :=
  RingWeights.mass_pos _ fun v => (sub_pos.2 hs1).trans_le
    (one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt c.2.2 v)

/-- The rings of defect at most `s < 1` with distinct message representatives have positive
mass. -/
theorem familyMu_mass_pos (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s : ℝ}
    (hs1 : s < 1) (keys : Fin n → _root_.MLDSA.Bytes 32) (Hmu : MuOrc Msg)
    (c : ValidChoiceMu prims A s keys Hmu) :
    0 < (familyMu prims A hp hβ0 hβt s keys Hmu c).wts.mass :=
  family_mass_pos hp hβ0 hβt hs1 keys c.toValidChoice

/-- The anonymity error is nonnegative. -/
theorem oracleError_nonneg (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hs1 : s < 1) (hθ0 : 0 < θ) (keys : Fin n → _root_.MLDSA.Bytes 32) (H : SchOrc p Msg) :
    0 ≤ oracleError prims A hp hβ0 hβt s θ keys H := by
  unfold oracleError
  split_ifs with h
  · exact familyBound_nonneg hθ0 (familyMu_mass_pos hp hβ0 hβt hs1 keys H.1) H.2
  · exact le_rfl

/-- **The two users' public-value laws of every challenge of defect at most `s` admissible at the
game's oracles are within the anonymity error.** -/
theorem tvDist_le_oracleError (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s θ : ℝ} (hs1 : s < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (keys : Fin n → _root_.MLDSA.Bytes 32)
    (HG : GameOrc prims Msg N reps)
    (c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n) (hcm : c ∈ A.choices)
    (hc : c.Valid _ keys) (hd : LowDefect prims βmin s c.ring)
    (hA : RingAdmissible prims βmin tol HG c.ring c.msg) :
    PMF.tvDist ((c.signLaw HG keys false).map Prod.fst) ((c.signLaw HG keys true).map Prod.fst) ≤
      oracleError prims A hp hβ0 hβt s θ keys HG.1 := by
  have hne : Nonempty (ValidChoiceMu prims A s keys HG.1.1) := ⟨⟨⟨c, hcm⟩, hc, hA.1, hd⟩⟩
  unfold oracleError
  rw [dif_pos hne]
  rw [map_fst_signLaw prims N βmin reps tol enc hp hβ0 hβt keys c hc HG hA,
    map_fst_signLaw prims N βmin reps tol enc hp hβ0 hβt keys c hc HG hA]
  exact (tvDist_map_le _ _ _).trans (tvDist_le_familyBound
    (R := familyMu prims A hp hβ0 hβt s keys HG.1.1) hθ0 hθ1
    (familyMu_mass_pos hp hβ0 hβt hs1 keys HG.1.1) ⟨⟨c, hcm⟩, hc, hA.1, hd⟩ HG.1.2)

open Classical in
/-- **The bad event of the scheme's oracles is within the anonymity error**: if some signer of a
challenge of defect at most `s` with distinct message representatives never keeps, the error is
at least one. -/
theorem ite_keeps_le_oracleError (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s θ : ℝ} (hs1 : s < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (keys : Fin n → _root_.MLDSA.Bytes 32)
    (H : SchOrc p Msg) :
    (if Keeps prims A hp hβ0 hβt s keys H then 0 else 1 : ℝ) ≤
      oracleError prims A hp hβ0 hβt s θ keys H := by
  split_ifs with hK
  · exact oracleError_nonneg hp hβ0 hβt hs1 hθ0 keys H
  · simp only [Keeps, not_forall, not_not] at hK
    obtain ⟨c, b, hb⟩ := hK
    have hne : Nonempty (ValidChoiceMu prims A s keys H.1) := ⟨c⟩
    unfold oracleError
    rw [dif_pos hne]
    exact one_le_familyBound_of_never hθ0 hθ1 (familyMu_mass_pos hp hβ0 hβt hs1 keys H.1) c b
      H.2 hb

/-- **When every signer of a challenge of defect at most `s` keeps, the signers of an admissible
challenge of defect at most `s` sign validly**, given the signing and verification laws, a
coherent encoding, and `‖s₂‖∞ ≤ η` for every honest key (`hs2`). -/
theorem validAt_of_keeps (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s : ℝ}
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    (keys : Fin n → _root_.MLDSA.Bytes 32) (HG : GameOrc prims Msg N reps)
    (hK : Keeps prims A hp hβ0 hβt s keys HG.1)
    {c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n} (hcm : c ∈ A.choices)
    (hc : c.Valid _ keys) (hA : RingAdmissible prims βmin tol HG c.ring c.msg)
    (hd : LowDefect prims βmin s c.ring) (b : Bool) {x : BucketVec p × FIPSSignature p prims}
    (hx : x ∈ (c.signLaw HG keys b).support) : c.ValidAt HG b x := by
  have hlt : c.idx b < c.ring.1.length := by
    cases b <;> simp [RingChoice.idx, hc.idx₀_lt, hc.idx₁_lt]
  have hkeep : (ringPair prims N βmin reps tol enc hp hβ0 hβt keys HG.1.1 c hc hA.1).attempt b
      HG.1.2 none ≠ 1 :=
    hK ⟨⟨c, hcm⟩, hc, hA.1, hd⟩ b
  rw [← ringAttemptOut_apply_none prims N βmin reps tol enc hp hβ0 hβt keys HG.1.1 c hc hA.1 HG.1.2
    b] at hkeep
  exact valid_of_mem_support_signLaw prims h_laws hv henc (hs2 _) hlt HG c.msg hA
    (get_idx_eq hc b hlt) hkeep hx

/-- **When every signer of a challenge of defect at most `s` keeps and no ring of defect above
`s` passes the check, the signers of the admissible challenges sign validly**
(`validAt_of_keeps`, `lowDefect_of_not_badPass`). -/
theorem signsValidly_of_keeps (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s : ℝ}
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    (keys : Fin n → _root_.MLDSA.Bytes 32) (HG : GameOrc prims Msg N reps)
    (hK : Keeps prims A hp hβ0 hβt s keys HG.1) (hB : ¬ BadPass prims A s keys HG.2) :
    A.SignsValidly HG keys := fun c hcm hc hA b x hx =>
  validAt_of_keeps hp hβ0 hβt h_laws hv henc hs2 keys HG hK hcm hc hA
    (lowDefect_of_not_badPass hB hcm hc hA) b hx

/-- The largest regularity gap is nonnegative. -/
theorem maxRegGap_nonneg [NeZero n] (keys : Fin n → _root_.MLDSA.Bytes 32) :
    0 ≤ maxRegGap prims βmin keys :=
  (signerRegGap_nonneg prims _ _ (Cutoff.const βmin)).trans (Finset.le_sup' (fun u => signerRegGap
      prims
    (keyGen prims (keys u)).2 (prims.expandA (keyGen prims (keys u)).2.rho) (Cutoff.const βmin))
        (mem_univ 0))

/-- The largest regularity gap is at most the sum of the honest users' gaps. -/
theorem maxRegGap_le_sum [NeZero n] (keys : Fin n → _root_.MLDSA.Bytes 32) :
    maxRegGap prims βmin keys ≤
      ∑ u, signerRegGap prims (keyGen prims (keys u)).2
        (prims.expandA (keyGen prims (keys u)).2.rho) (Cutoff.const βmin) :=
  Finset.sup'_le _ _ fun u _ => Finset.single_le_sum (f := fun u => signerRegGap prims
    (keyGen prims (keys u)).2 (prims.expandA (keyGen prims (keys u)).2.rho) (Cutoff.const βmin))
    (fun _ _ => signerRegGap_nonneg prims _ _ (Cutoff.const βmin)) (mem_univ u)

/-- **The average over the users' coins of the largest regularity gap** is at most `n` times the
average regularity gap of one honest key (`maxRegGap_le_sum`, each user's coins uniform). -/
theorem expect_maxRegGap_le [NeZero n] :
    𝔼 keys : Fin n → _root_.MLDSA.Bytes 32, maxRegGap prims βmin keys ≤
      n * 𝔼 seed : _root_.MLDSA.Bytes 32, signerRegGap prims (keyGen prims seed).2
        (prims.expandA (keyGen prims seed).2.rho) (Cutoff.const βmin) := by
  refine (Finset.expect_le_expect fun keys _ => maxRegGap_le_sum keys).trans_eq ?_
  rw [Finset.expect_sum_comm, Finset.sum_congr rfl fun u _ => PMF.expect_apply_eval u
    (fun x => signerRegGap prims (keyGen prims x).2 (prims.expandA (keyGen prims x).2.rho)
        (Cutoff.const βmin))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The average over the commitment-hash oracle of the anonymity error at the users' coins
`keys` and the message-representative oracle `H_µ`**:
at most `2 / ((1 - s) θ)` times the largest regularity gap of the honest keys, plus the McDiarmid
terms of the largest variance proxies, for an adversary with at most `C` challenges of its set
valid for any key vector (`expect_familyBound_le`; `RingPair.error_le_of_massRatio_le` with the mass ratio at most
`1 / (1 - s)` of a ring of defect at most `s`, `massRatio_le_of_ringDefect_le`;
`relColError_le_signerRegGap`). -/
theorem expect_oracleError_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (h_laws : SigningLaws prims) (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) [NeZero n] {C : ℕ}
    (hC : A.ValidCountLe C) (keys : Fin n → _root_.MLDSA.Bytes 32) (Hmu : MuOrc Msg) :
    𝔼 H : ChOrc p, oracleError prims A hp hβ0 hβt s θ keys (Hmu, H) ≤
      2 * (1 - s)⁻¹ / θ * maxRegGap prims βmin keys +
        √(maxDevVar prims A hp hβ0 hβt s θ keys * Real.log C / 2) +
        √(maxCountVar prims A hp hβ0 hβt s θ keys * Real.log (C + 1) / 2) := by
  have hκ0 : 0 ≤ (1 - s)⁻¹ := (inv_pos.2 (sub_pos.2 hs1)).le
  by_cases h : Nonempty (ValidChoiceMu prims A s keys Hmu)
  · have hne : Nonempty (ValidChoice prims A s keys) := ⟨h.some.toValidChoice⟩
    have hor : ∀ H : ChOrc p, oracleError prims A hp hβ0 hβt s θ keys (Hmu, H) =
        haveI := h; familyBound (familyMu prims A hp hβ0 hβt s keys Hmu) θ H := fun H => by
      unfold oracleError
      exact dif_pos h
    simp only [hor]
    unfold maxDevVar maxCountVar
    simp only [dif_pos hne]
    haveI := h
    set R := familyMu prims A hp hβ0 hβt s keys Hmu
    have hcardC : (Fintype.card (ValidChoiceMu prims A s keys Hmu) : ℝ) ≤ C := by
      have : Fintype.card (ValidChoiceMu prims A s keys Hmu) ≤ (A.validChoices keys).card := by
        refine (Fintype.card_le_of_injective (fun c => (⟨c.1.1, (A.mem_validChoices).2
          ⟨c.1.2, c.2.1⟩⟩ : A.validChoices keys)) fun c c' h => ?_).trans_eq (Fintype.card_coe _)
        have h' : c.1.1 = c'.1.1 := congrArg (fun x : A.validChoices keys => x.1) h
        exact Subtype.ext (Subtype.ext h')
      exact_mod_cast this.trans (hC keys)
    have hcard1 : (0 : ℝ) < Fintype.card (ValidChoiceMu prims A s keys Hmu) := by
      exact_mod_cast Fintype.card_pos
    have hdv0 : ∀ c, 0 ≤ (family prims A hp hβ0 hβt s keys c).devVar θ := fun c => by
      unfold RingPair.devVar; positivity
    have hcv0 : ∀ c, 0 ≤ (family prims A hp hβ0 hβt s keys c).countVar θ := fun c => by
      unfold RingPair.countVar; positivity
    have he : ∀ c, (R c).error θ ≤ 2 * (1 - s)⁻¹ / θ * maxRegGap prims βmin keys := fun c => by
      refine (RingPair.error_le_of_massRatio_le (R c) hθ0 (fun v => (sub_pos.2 hs1).trans_le
        (one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt c.2.2.2 v))
        (massRatio_le_of_ringDefect_le prims hp hβ0 hβt c.2.2.2 hs1)).trans ?_
      have hb : ∀ b : Bool, relColError (R c).wts ((R c).pos b) ((R c).signer b).P
          ((R c).signer b).w1 ((R c).signer b).acc ((R c).signer b).κ ((R c).signer b).β ≤
          maxRegGap prims βmin keys := fun b => by
        have hlt : c.1.1.idx b < c.1.1.ring.1.length := by
          cases b <;> simp [RingChoice.idx, c.2.1.idx₀_lt, c.2.1.idx₁_lt]
        have hi : ringT0s prims c.1.1.ring.1 ⟨c.1.1.idx b, hlt⟩ =
            (keyGen prims (keys (c.1.1.user b))).2.t0 :=
          congrArg (fun x : PubKey p prims => x.2.2) (get_idx_eq c.2.1 b hlt)
        exact (relColError_le_signerRegGap prims _ _ hp h_laws (hs2 _) _ _ hi hβ0 hβt).trans
          (Finset.le_sup' (fun u => signerRegGap prims (keyGen prims (keys u)).2
            (prims.expandA (keyGen prims (keys u)).2.rho) (Cutoff.const βmin)) (mem_univ
                (c.1.1.user b)))
      calc (1 - s)⁻¹ / θ * ∑ b : Bool, relColError (R c).wts ((R c).pos b) ((R c).signer b).P
            ((R c).signer b).w1 ((R c).signer b).acc ((R c).signer b).κ ((R c).signer b).β
          ≤ (1 - s)⁻¹ / θ * ∑ _b : Bool, maxRegGap prims βmin keys :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hb b)
              (div_nonneg hκ0 hθ0.le)
        _ = 2 * (1 - s)⁻¹ / θ * maxRegGap prims βmin keys := by
            rw [Fintype.sum_bool]; ring
    refine (expect_familyBound_le hθ0 hθ1 (familyMu_mass_pos hp hβ0 hβt hs1 keys Hmu)
      (sd := univ.sup' univ_nonempty fun c => (family prims A hp hβ0 hβt s keys c).devVar θ)
      (sc := univ.sup' univ_nonempty fun c => (family prims A hp hβ0 hβt s keys c).countVar θ) he
      (fun c => Finset.le_sup' (fun c => (family prims A hp hβ0 hβt s keys c).devVar θ)
        (mem_univ c.toValidChoice))
      (fun c => Finset.le_sup' (fun c => (family prims A hp hβ0 hβt s keys c).countVar θ)
        (mem_univ c.toValidChoice))).trans ?_
    have hsd0 : 0 ≤ univ.sup' univ_nonempty fun c => (family prims A hp hβ0 hβt s keys c).devVar θ :=
      (hdv0 _).trans (Finset.le_sup' (fun c => (family prims A hp hβ0 hβt s keys c).devVar θ)
        (mem_univ (Classical.arbitrary _)))
    have hsc0 : 0 ≤ univ.sup' univ_nonempty fun c =>
        (family prims A hp hβ0 hβt s keys c).countVar θ :=
      (hcv0 _).trans (Finset.le_sup' (fun c => (family prims A hp hβ0 hβt s keys c).countVar θ)
        (mem_univ (Classical.arbitrary _)))
    refine add_le_add (add_le_add le_rfl ?_) ?_
    · refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (by norm_num))
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hcard1 hcardC) hsd0
    · refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (by norm_num))
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hsc0
  · have hor : ∀ H : ChOrc p, oracleError prims A hp hβ0 hβt s θ keys (Hmu, H) = 0 := fun H => by
      unfold oracleError
      exact dif_neg h
    simp only [hor, Finset.expect_const_zero]
    exact add_nonneg (add_nonneg (mul_nonneg (div_nonneg (by linarith) hθ0.le)
      (maxRegGap_nonneg keys)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- **The average over the scheme's oracles of the anonymity error at the users' coins `keys`**:
the bound of `expect_oracleError_le`, averaged over the message-representative oracle. -/
theorem expect_schOrc_oracleError_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (h_laws : SigningLaws prims) (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) [NeZero n] {C : ℕ}
    (hC : A.ValidCountLe C) (keys : Fin n → _root_.MLDSA.Bytes 32) :
    𝔼 H : SchOrc p Msg, oracleError prims A hp hβ0 hβt s θ keys H ≤
      2 * (1 - s)⁻¹ / θ * maxRegGap prims βmin keys +
        √(maxDevVar prims A hp hβ0 hβt s θ keys * Real.log C / 2) +
        √(maxCountVar prims A hp hβ0 hβt s θ keys * Real.log (C + 1) / 2) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact (Finset.expect_le_expect fun Hmu _ =>
    expect_oracleError_le hp hβ0 hβt h_laws hs2 hθ0 hθ1 hs1 hC keys Hmu).trans_eq
      (Finset.expect_const univ_nonempty _)

/-- **The anonymity error** of the ML-DSA ring signature publishing `w₁`, for an adversary with
at most `C` challenges of its set valid for any key vector, at the defect budget `s` and the threshold fraction `θ`: the average over
the honest users' coins of `2 / ((1 - s) θ)` times the largest regularity gap of their keys, plus
the McDiarmid terms `√(maxDevVar · log C / 2) + √(maxCountVar · log (C + 1) / 2)`. -/
noncomputable def anonError (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) [NeZero n]
    (s θ : ℝ) (C : ℕ) : ℝ :=
  𝔼 keys : Fin n → (pubSigner prims (Msg := Msg) N βmin reps tol enc).KeyCoins,
    (2 * (1 - s)⁻¹ / θ * maxRegGap prims βmin keys +
      √(maxDevVar prims A hp hβ0 hβt s θ keys * Real.log C / 2) +
      √(maxCountVar prims A hp hβ0 hβt s θ keys * Real.log (C + 1) / 2))

/-- **The anonymity error with the largest gap averaged over the users' coins**: at most
`2 / ((1 - s) θ) · n` times the average regularity gap of one honest key, plus the averaged
McDiarmid terms (`expect_maxRegGap_le`). -/
theorem anonError_le_keyAvg (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hθ0 : 0 < θ) (hs1 : s < 1) [NeZero n] (C : ℕ) :
    anonError (A := A) hp hβ0 hβt s θ C ≤
      2 * (1 - s)⁻¹ / θ * (n * 𝔼 seed : _root_.MLDSA.Bytes 32,
          signerRegGap prims (keyGen prims seed).2 (prims.expandA (keyGen prims seed).2.rho)
              (Cutoff.const βmin)) +
        𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          (√(maxDevVar prims A hp hβ0 hβt s θ keys * Real.log C / 2) +
            √(maxCountVar prims A hp hβ0 hβt s θ keys * Real.log (C + 1) / 2)) := by
  unfold anonError
  simp only [add_assoc]
  rw [Finset.expect_add_distrib]
  refine add_le_add ?_ le_rfl
  have hk : 0 ≤ 2 * (1 - s)⁻¹ / θ :=
    div_nonneg (mul_nonneg zero_le_two (inv_pos.2 (sub_pos.2 hs1)).le) hθ0.le
  calc 𝔼 keys : Fin n → (pubSigner prims (Msg := Msg) N βmin reps tol enc).KeyCoins,
        2 * (1 - s)⁻¹ / θ * maxRegGap prims βmin keys
        = 2 * (1 - s)⁻¹ / θ * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            maxRegGap prims βmin keys :=
          (Finset.mul_expect _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (expect_maxRegGap_le (prims := prims)) hk

open Classical in
/-- **The bad events of the two oracles**: averaged over the game's oracles `(H, G)`, the
probability that some signer of a challenge of defect at most `s` never keeps or that a ring of
defect above `s` passes the check is at most the average anonymity error plus
`C · checkError reps tol s x` for every `x ≥ 1` (`ite_keeps_le_oracleError`,
`expect_exists_ringCheck_le`). -/
theorem expect_ite_good_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hs1 : s < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) {x : ℝ} (hx : 1 ≤ x) {C : ℕ}
    (hC : A.ValidCountLe C) (keys : Fin n → _root_.MLDSA.Bytes 32)
    [∀ HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
      Decidable (Keeps prims A hp hβ0 hβt s keys HG.1 ∧ ¬ BadPass prims A s keys HG.2)] :
    𝔼 HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
        (if Keeps prims A hp hβ0 hβt s keys HG.1 ∧ ¬ BadPass prims A s keys HG.2 then 0 else 1 : ℝ) ≤
      𝔼 HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
        oracleError prims A hp hβ0 hβt s θ keys HG.1 + C * checkError reps tol s x := by
  have hpt : ∀ HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
      (if Keeps prims A hp hβ0 hβt s keys HG.1 ∧ ¬ BadPass prims A s keys HG.2 then 0 else 1 : ℝ) ≤
        oracleError prims A hp hβ0 hβt s θ keys HG.1 +
          (if BadPass prims A s keys HG.2 then 1 else 0) := fun HG => by
    have hk := ite_keeps_le_oracleError (A := A) hp hβ0 hβt hs1 hθ0 hθ1 keys HG.1
    have h0 := oracleError_nonneg (A := A) hp hβ0 hβt hs1 hθ0 keys HG.1
    by_cases hK : Keeps prims A hp hβ0 hβt s keys HG.1 <;>
      by_cases hB : BadPass prims A s keys HG.2 <;> simp only [hK, hB] at hk ⊢ <;> norm_num at hk ⊢ <;>
      linarith
  refine (Finset.expect_le_expect fun HG _ => hpt HG).trans ?_
  rw [Finset.expect_add_distrib]
  refine add_le_add le_rfl ?_
  have hB : ∀ G : CheckOrc p prims N reps, (if BadPass prims A s keys G then 1 else 0 : ℝ) =
      if ∃ c ∈ A.validChoices keys, s < ringDefect prims βmin c.ring.1 ∧
        RingCheck prims βmin tol G c.ring then 1 else 0 := fun G =>
    if_congr Iff.rfl rfl rfl
  refine (Finset.expect_comp_snd
    (fun G => (if BadPass prims A s keys G then 1 else 0 : ℝ))).trans_le ?_
  rw [Finset.expect_congr rfl fun G _ => hB G]
  convert (expect_exists_ringCheck_le prims βmin tol (A.validChoices keys) RingChoice.ring s
    hx).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hC keys)) (checkError_nonneg reps tol s
      (zero_le_one.trans hx))) using 3

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁`** against full key exposure (BKM06
Definition 4, ePrint 2005/304, p. 6, keys given at the start as in CCLM22 Experiment 2, p. 21,
`Q` adaptive challenges, the oracles `H_µ`, `H` and `G` visible), with the signer refusing rings
with two equal message representatives and rings that fail the public check (`RingCheck`, `reps`
samples per member, at most `tol` failed samples per ring): for the spBCS compilation `M` whose
honest prover has honest-verifier
zero knowledge at error `δ` for the ring relation at every oracle (`hz`), every adversary with at
most `C` challenges of its set valid for any key vector (`hC`), and every distinguisher, the
advantage is at most
`(Q + 1) · 𝔼_keys (2 / ((1 - s) θ) · maxRegGap + √(maxDevVar · log C / 2) +
√(maxCountVar · log (C + 1) / 2)) + Q · wiError δ (Q · C) + C · checkError reps tol s x`,
at every defect budget `s < 1`, threshold fraction `θ ∈ (0, 1)` and `x ≥ 1`. The rings of defect
at most `s` have mass ratio at most `1 / (1 - s)` (`massRatio_le_of_ringDefect_le`); a ring of
defect above `s` among the adversary's `C` challenges valid for the keys passes the check with
probability at most `C · checkError reps tol s x` over the check oracle
(`expect_exists_ringCheck_le`), whichever of them the adversary chooses after seeing the oracle;
the term is small only for adversaries with far fewer than `1 / checkError` candidate rings per
key vector. The signer is the ideal-mask signer (`Applications/MLDSA/Signing/Ideal.lean`), not FIPS 204's hedged
mask derivation. The adversary may choose any ring holding the
two users' keys; a ring the signer refuses (`RingAdmissible` fails) is answered by `⊥` in both
experiments. Hypotheses: the signing and verification laws of the primitives, the encoding `enc`
coherent with `bucketsOf`, `‖s₂‖∞ ≤ η` for every honest key
(FIPS 204 Algorithm 33's range), and the cut-off `β_min ∈ (0, ∞)`. -/
theorem advantage_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    {E : (j : ι) → (M.comp j).Encoder}
    {V : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt →
      FullTr P τ → Bool}
    {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
    {honest : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Wit →
      R → CausalProver P τ (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt}
    (Rv : ∀ H, M.Reveal E (Qs H)) {PubZ : Type}
    {pubZ : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt → PubZ}
    {sim : ∀ H, CausalJointSimulator (Rv H).MV PubZ} {δ : NNReal}
    (hz : ∀ H, CausalHVZK (Rv H).MV ((pubSigner prims (Msg := Msg) N βmin reps tol enc).rel H)
      (honest H) pubZ (sim H) δ) {C : ℕ} (hC : A.ValidCountLe C)
    (D : (Fin n → _root_.MLDSA.Bytes 32) → GameOrc prims Msg N reps →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) M.NIProof Q → Prop) :
    A.advantage E Qs honest D ≤
      (Q + 1) * anonError (A := A) hp hβ0 hβt s θ C + Q * M.wiError δ (Q * C) +
        C * checkError reps tol s x := by
  have h := A.advantage_le_of_signsValidly Rv hz hC
    (fun keys HG => Keeps prims A hp hβ0 hβt s keys HG.1 ∧ ¬ BadPass prims A s keys HG.2)
    (fun keys HG hG => signsValidly_of_keeps hp hβ0 hβt h_laws hv henc hs2 keys HG hG.1 hG.2)
    (fun keys HG => oracleError prims A hp hβ0 hβt s θ keys HG.1)
    (fun keys HG => oracleError_nonneg hp hβ0 hβt hs1 hθ0 keys HG.1)
    (fun keys HG hG c hcm hc hA => tvDist_le_oracleError hp hβ0 hβt hs1 hθ0 hθ1 keys HG c hcm
      hc (lowDefect_of_not_badPass hG.2 hcm hc hA) hA) D
  have hind : 𝔼 keys : Fin n → (pubSigner prims (Msg := Msg) N βmin reps tol enc).KeyCoins,
        𝔼 HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
          (if Keeps prims A hp hβ0 hβt s keys HG.1 ∧ ¬ BadPass prims A s keys HG.2 then 0 else 1 : ℝ) ≤
      𝔼 keys : Fin n → (pubSigner prims (Msg := Msg) N βmin reps tol enc).KeyCoins,
        𝔼 HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
          oracleError prims A hp hβ0 hβt s θ keys HG.1 + C * checkError reps tol s x := by
    refine (Finset.expect_le_expect fun keys _ =>
      expect_ite_good_le (A := A) hp hβ0 hβt hs1 hθ0 hθ1 hx hC keys).trans_eq ?_
    exact (Finset.expect_add_distrib _ _ _).trans
      (congrArg (_ + ·) (Finset.expect_const univ_nonempty _))
  have hE : 𝔼 keys : Fin n → (pubSigner prims (Msg := Msg) N βmin reps tol enc).KeyCoins,
        𝔼 HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
          oracleError prims A hp hβ0 hβt s θ keys HG.1 ≤
      anonError (A := A) hp hβ0 hβt s θ C :=
    Finset.expect_le_expect fun keys _ =>
      (Finset.expect_comp_fst
        (fun H => oracleError prims A hp hβ0 hβt s θ keys H)).trans_le
        (expect_schOrc_oracleError_le hp hβ0 hβt h_laws hs2 hθ0 hθ1 hs1 hC keys)
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have key : ∀ {a X I W B G q : ℝ}, a ≤ q * X + W + I → I ≤ X + G → X ≤ B → 0 ≤ q →
      a ≤ (q + 1) * B + W + G := fun h1 h2 h3 h4 => by nlinarith
  exact key h hind hE hQ

end Main

/-! ### Anonymity with `ExpandA` a random oracle -/

section Ideal

open IOP GordieHowe.SPBCS GordieHowe.QROM

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n Q : ℕ}
  {M : ∀ G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
    SPBCS Mg P (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e}
  (A : ∀ G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
    PubAnonAdversary (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc) (M G) n Q)

/-- **The anonymity error with `ExpandA` a random oracle**: `2 / ((1 - s) θ)` times
`n · regGapAvg`, plus the average over the oracle `G` and the users' coins of the McDiarmid terms
`√(maxDevVar · log C / 2) + √(maxCountVar · log (C + 1) / 2)` of the game at `G`. -/
noncomputable def idealAnonError (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (s θ : ℝ) (C : ℕ) : ℝ :=
  2 * (1 - s)⁻¹ / θ * (n * regGapAvg prims βmin) +
    𝔼 G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      (√(maxDevVar (withExpandA prims G) (A G) hp hβ0 hβt s θ keys * Real.log C / 2) +
        √(maxCountVar (withExpandA prims G) (A G) hp hβ0 hβt s θ keys * Real.log (C + 1) / 2))

/-- **Averaging a bound with any check term over `ExpandA` as a random oracle**, for any
quantity: if at every oracle `G` the quantity `f G` is at most
`(Q + 1) · anonError + Q · wiError δ (Q · C) + chk` (with `anonError` of the adversary `A G`), its
average over a uniform `G` is at most `(Q + 1) · idealAnonError + Q · 𝔼_G wiError δ (Q · C) + chk`
(`anonError_le_keyAvg`, `expect_regGap_withExpandA`). `f G` is the advantage of `A G`
(`advantage_le_ideal_of`), or the advantage against a signer that refuses more rings
(`MLDSAPublicW1HedgedQuery.lean`). -/
theorem expect_le_ideal_of (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s θ : ℝ} (hθ0 : 0 < θ) (hs1 : s < 1) [NeZero n] {δ : NNReal} {C : ℕ} {chk : ℝ}
    (f : (_root_.MLDSA.Bytes 32 → TqMatrix p.k p.l) → ℝ)
    (hf : ∀ G, f G ≤ (Q + 1) * anonError (A := A G) hp hβ0 hβt s θ C + Q * (M G).wiError δ (Q * C) + chk) :
    𝔼 G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, f G ≤
      (Q + 1) * idealAnonError prims A hp hβ0 hβt s θ C +
        Q * 𝔼 G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, (M G).wiError δ (Q * C) + chk := by
  have hG : ∀ G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
      f G ≤
        (Q + 1) * (2 * (1 - s)⁻¹ / θ * (n * 𝔼 seed : _root_.MLDSA.Bytes 32,
            signerRegGap (withExpandA prims G) (keyGen (withExpandA prims G) seed).2
            ((withExpandA prims G).expandA (keyGen (withExpandA prims G) seed).2.rho)
                (Cutoff.const βmin)) +
          𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            (√(maxDevVar (withExpandA prims G) (A G) hp hβ0 hβt s θ keys * Real.log C / 2) +
              √(maxCountVar (withExpandA prims G) (A G) hp hβ0 hβt s θ keys *
                Real.log (C + 1) / 2))) + Q * (M G).wiError δ (Q * C) + chk := fun G =>
    (hf G).trans <| by
      gcongr
      exact anonError_le_keyAvg (A := A G) hp hβ0 hβt hθ0 hs1 C
  refine (Finset.expect_le_expect fun G _ => hG G).trans_eq ?_
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    ← Finset.mul_expect, Finset.expect_add_distrib, ← Finset.mul_expect, ← Finset.mul_expect,
    expect_regGap_withExpandA, Finset.expect_const univ_nonempty]
  rfl

/-- **Averaging a bound with any check term over `ExpandA` as a random oracle**: if at every
oracle `G` the advantage is at most `(Q + 1) · anonError + Q · wiError δ (Q · C) + chk` (`hcore`:
`advantage_le`, or `advantage_le_query` for a query-bounded adversary), the advantage averaged
over a uniform `G` is at most `(Q + 1) · idealAnonError + Q · 𝔼_G wiError δ (Q · C) + chk`
(`expect_le_ideal_of`). -/
theorem advantage_le_ideal_of (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s θ : ℝ} (hθ0 : 0 < θ) (hs1 : s < 1) [NeZero n]
    {E : ∀ G, (j : ι) → ((M G).comp j).Encoder}
    {V : ∀ G, GameOrc (withExpandA prims G) Msg N reps →
      (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).Stmt → FullTr P τ → Bool}
    {Qs : ∀ G H x, (M G).IOPQueries (V G H) x} {R : Type} [Fintype R] [Nonempty R]
    {honest : ∀ G, GameOrc (withExpandA prims G) Msg N reps →
      (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).Wit →
      R → CausalProver P τ (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).Stmt}
    {δ : NNReal} {C : ℕ} {chk : ℝ}
    (D : ∀ G, (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (withExpandA prims G) Msg N reps →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) (M G).NIProof Q → Prop)
    (hcore : ∀ G, (A G).advantage (E G) (Qs G) (honest G) (D G) ≤
      (Q + 1) * anonError (A := A G) hp hβ0 hβt s θ C + Q * (M G).wiError δ (Q * C) + chk) :
    𝔼 G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, (A G).advantage (E G) (Qs G) (honest G) (D G) ≤
      (Q + 1) * idealAnonError prims A hp hβ0 hβt s θ C +
        Q * 𝔼 G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, (M G).wiError δ (Q * C) + chk :=
  expect_le_ideal_of prims A hp hβ0 hβt hθ0 hs1 _ hcore

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁` with `ExpandA` a random oracle**
(BKM06 Definition 4 as in `advantage_le`, with the advantage averaged over a uniform oracle
`G : ρ ↦ Â` for `ExpandA`; at each `G` the game, its spBCS compilation `M G`, the adversary `A G`
and the distinguisher see all of `G`). Key generation is FIPS 204 Algorithm 6 with `Â = G(ρ)` and
the primitives' own `ExpandS` (`keyGen_withExpandA`), so the matrix is uniform and independent of
`(ρ', K)`. The advantage is at most
`(Q + 1) · (2 / ((1 - s) θ) · n · regGapAvg + 𝔼_{G, keys} (√(maxDevVar · log C / 2) +
√(maxCountVar · log (C + 1) / 2))) + Q · 𝔼_G wiError δ (Q · C) + C · checkError reps tol s x`
for every `x ≥ 1` (`advantage_le_ideal_of` with `advantage_le`). The factor
`n` bounds the largest gap over the `n` honest users, among which the adversary chooses, by their
sum. -/
theorem advantage_le_ideal (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    {E : ∀ G, (j : ι) → ((M G).comp j).Encoder}
    {V : ∀ G, GameOrc (withExpandA prims G) Msg N reps →
      (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).Stmt → FullTr P τ → Bool}
    {Qs : ∀ G H x, (M G).IOPQueries (V G H) x} {R : Type} [Fintype R] [Nonempty R]
    {honest : ∀ G, GameOrc (withExpandA prims G) Msg N reps →
      (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).Wit →
      R → CausalProver P τ (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).Stmt}
    (Rv : ∀ G H, (M G).Reveal (E G) (Qs G H)) {PubZ : Type}
    {pubZ : ∀ G, (pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).Stmt → PubZ}
    {sim : ∀ G H, CausalJointSimulator (Rv G H).MV PubZ} {δ : NNReal}
    (hz : ∀ G H, CausalHVZK (Rv G H).MV
      ((pubSigner (withExpandA prims G) (Msg := Msg) N βmin reps tol enc).rel H)
      (honest G H) (pubZ G) (sim G H) δ) {C : ℕ} (hC : ∀ G, (A G).ValidCountLe C)
    (D : ∀ G, (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (withExpandA prims G) Msg N reps →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) (M G).NIProof Q → Prop) :
    𝔼 G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, (A G).advantage (E G) (Qs G) (honest G) (D G) ≤
      (Q + 1) * idealAnonError prims A hp hβ0 hβt s θ C +
        Q * 𝔼 G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, (M G).wiError δ (Q * C) +
          C * checkError reps tol s x :=
  advantage_le_ideal_of prims A hp hβ0 hβt hθ0 hs1 D fun G =>
    advantage_le (A := A G) hp hβ0 hβt (SigningLaws.withExpandA prims h_laws G)
      (VerifyLaws.withExpandA prims hv G) henc (fun seed => hs2 seed) hθ0 hθ1 hs1 hx (Rv G) (hz G)
      (hC G) (D G)

/-- **The anonymity error averaged over `ExpandA` as a random oracle** is at most the ideal
anonymity error (`anonError_le_keyAvg`, `expect_regGap_withExpandA`). -/
theorem expect_anonError_le_idealAnonError (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ} (hθ0 : 0 < θ) (hs1 : s < 1) [NeZero n] (C : ℕ) :
    𝔼 G : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, anonError (A := A G) hp hβ0 hβt s θ C ≤
      idealAnonError prims A hp hβ0 hβt s θ C := by
  refine (Finset.expect_le_expect fun G _ =>
    anonError_le_keyAvg (A := A G) hp hβ0 hβt hθ0 hs1 C).trans_eq ?_
  rw [Finset.expect_add_distrib, ← Finset.mul_expect, ← Finset.mul_expect,
    expect_regGap_withExpandA]
  rfl

end Ideal


end GordieHowe.Ring.MLDSAW1

/-! ### Anonymity at the concrete primitives -/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec PMF Finset IOP
  GordieHowe.SPBCS GordieHowe.QROM
open scoped ENNReal BigOperators

attribute [local instance] concreteNTTRingOps

instance (p : Params) : Inhabited (concretePrimitivesKeyGen p).Hint :=
  inferInstanceAs (Inhabited (Vector Bool ringDegree))

instance (p : Params) : Fintype (concretePrimitivesKeyGen p).Hint :=
  inferInstanceAs (Fintype (Vector Bool ringDegree))

instance (p : Params) : DecidableEq (concretePrimitivesKeyGen p).Hint :=
  inferInstanceAs (DecidableEq (Vector Bool ringDegree))

instance (p : Params) : Fintype (concretePrimitivesKeyGen p).Power2High :=
  inferInstanceAs (Fintype Rq)

instance (p : Params) : DecidableEq (concretePrimitivesKeyGen p).Power2High :=
  inferInstanceAs (DecidableEq Rq)

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg]
  [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner (concretePrimitivesKeyGen p) (Msg := Msg) N βmin reps tol
    (concreteEnc p)).Stmt k kN kS L e} {n Q : ℕ}
  (A : PubAnonAdversary (pubSigner (concretePrimitivesKeyGen p) (Msg := Msg) N βmin reps tol
    (concreteEnc p)) M n Q)

/-- **Anonymity of the ML-DSA ring signature publishing `w₁` at the concrete primitives** (the
vendored FIPS 204 primitives with the FIPS 204 `ExpandS`, `concretePrimitivesKeyGen`, and the
concrete NTT, at every approved parameter set: ML-DSA-44, 65 and 87), `advantage_le` with the
signing laws (`signingLaws_concreteKeyGen`), the verification laws (`verifyLaws_concreteKeyGen`),
the encoding (`concreteEnc_highBitsVec_keyGen`) and `‖s₂‖∞ ≤ η` for every honest key
(`keyGenFromSeed_s2_bounded`) discharged. -/
theorem advantage_le_concrete (hp : p.isApproved) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    {E : (j : ι) → (M.comp j).Encoder}
    {V : GameOrc (concretePrimitivesKeyGen p) Msg N reps → (pubSigner (concretePrimitivesKeyGen p)
      (Msg := Msg) N βmin reps tol (concreteEnc p)).Stmt → FullTr P τ → Bool}
    {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
    {honest : GameOrc (concretePrimitivesKeyGen p) Msg N reps → (pubSigner
      (concretePrimitivesKeyGen p) (Msg := Msg) N βmin reps tol (concreteEnc p)).Wit → R →
        CausalProver P τ (pubSigner (concretePrimitivesKeyGen p) (Msg := Msg) N βmin reps tol
          (concreteEnc p)).Stmt}
    (Rv : ∀ H, M.Reveal E (Qs H)) {PubZ : Type}
    {pubZ : (pubSigner (concretePrimitivesKeyGen p) (Msg := Msg) N βmin reps tol
      (concreteEnc p)).Stmt → PubZ}
    {sim : ∀ H, CausalJointSimulator (Rv H).MV PubZ} {δ : NNReal}
    (hz : ∀ H, CausalHVZK (Rv H).MV ((pubSigner (concretePrimitivesKeyGen p) (Msg := Msg) N βmin
      reps tol (concreteEnc p)).rel H) (honest H) pubZ (sim H) δ) {C : ℕ} (hC : A.ValidCountLe C)
    (D : (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (concretePrimitivesKeyGen p) Msg N reps →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) M.NIProof Q → Prop) :
    A.advantage E Qs honest D ≤
      (Q + 1) * anonError (A := A) (SigningParams.of_isApproved hp) hβ0 hβt s θ C +
        Q * M.wiError δ (Q * C) + C * checkError reps tol s x :=
  advantage_le (A := A) (SigningParams.of_isApproved hp) hβ0 hβt (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (concreteEnc_highBitsVec_keyGen hp)
    (fun _ => keyGenFromSeed_s2_bounded hp _) hθ0 hθ1 hs1 hx Rv hz hC D

end GordieHowe.Ring.MLDSAW1
