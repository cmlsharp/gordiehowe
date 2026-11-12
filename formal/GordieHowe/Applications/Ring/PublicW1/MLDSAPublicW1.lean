-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Anonymity
public import GordieHowe.Applications.MLDSA.Signing.PublishedKey
public import GordieHowe.Applications.MLDSA.Signing.Oracles
public import GordieHowe.Applications.MLDSA.Signing.RingSigner
public import GordieHowe.Applications.MLDSA.Signing.SampleInBallShape
public import GordieHowe.Applications.MLDSA.Signing.ChallengeMoments
public import GordieHowe.Applications.MLDSA.Spec.ExpandS
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# The public ring check of the ML-DSA ring signature publishing `w₁`

Every ring member publishes `(ρ, t₁, t₀)` (`PubKey`, with the key generation `keyGen`, in
`Applications/MLDSA/Signing/PublishedKey.lean`). The game has three random oracles: the
message-representative oracle `H_µ` (`µ = H(tr ‖ M′)`, FIPS 204 Algorithm 7 line 6), the
commitment-hash oracle `H` on `(µ, w₁)` (`c̃ = H(µ ‖ w1Encode(w₁))`, line 15), and the check
oracle `G` (`GameOrc`). The signer refuses rings that are not admissible at the game's oracles
(`RingAdmissible`: the members' `µ_j` pairwise distinct, and the public ring check against `G`; the
refusal is a function of the published keys, the message and the oracles). This file states the
check and its error; the signers and their anonymity and completeness bounds are in
`Applications/Ring/MLDSAW1*.lean`.

* `CutoffFamily`, `constCut`, `ringCuts`, `CutoffFamily.SameTop`, `CutoffFamily.LevelAtLeast`: the
  cut-offs of the check, per ring and member, with the constant family at `β_min`.
* `ringDefectOf`, `ringDefect`, `one_sub_le_colMass_of_ringDefect_le`,
  `massRatio_le_of_ringDefect_le`: the sum over the members of the probability `δ_j` over a uniform
  `c̃` that member `j`'s check weight (`checkWeight`) is below its cut-off (`checkDefect`). A ring
  of
  defect `∑_j δ_j ≤ s < 1` has every column mass in `[1 - s, 1]` and mass ratio at most
  `1 / (1 - s)`.
* `CheckOrc`, `checkFails`, `sampledRingCheck`, `sampledAdm`, `RingAdmissible`, `LowDefect`: the
  check oracle from the points `(ring, member, sample)` to commitment hashes, independent of `H`;
  the check with tolerance `tol` that at most `tol` of the members' check weights at their `reps`
  hashes `G(l, j, r)` are below the cut-off.
* `checkError`, `expect_ringCheck_le`, `expect_sampledAdm_le`, `expect_exists_ringCheck_le`: over a
  uniform check oracle, a ring of defect at least `s` passes with probability at most
  `checkError reps tol s x = x^tol · exp(-(1 - 1/x) · reps · s)` for every `x ≥ 1` (the Chernoff
  lower tail); some ring of defect above `s` among a finite set of `C` rings passes with
  probability at most `C · checkError reps tol s x`.
* `RingCheck`, `RingCheck.sampled`: a ring check with its shortfall level and error, and the
  sampled check as one.
* `regGapAvg`, `expect_regGap_withExpandA`: the regularity gap of an honest key averaged over the
  seed and a uniform matrix (the primitives `withExpandA` with `ExpandA := G`).
* `withSampleInBall`, `expect_withSampleInBall`, `expect_flatWeight_withSampleInBall`: the
  primitives with `SampleInBall := G` for a random oracle `G` onto the challenge set `B_τ`
  (`ChallengeBall`); averaged over a uniform `G`, the challenge of every commitment hash is uniform
  on `B_τ`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA PMF Finset
open scoped ENNReal BigOperators

variable {p : Params} (prims : Primitives p)

/-- The published `t₀`s of a ring. -/
def ringT0s (l : List (PubKey p prims)) : Fin l.length → RqVec p.k := fun j => (l.get j).2.2

/-! ### Cut-off families -/

/-- **A cut-off family of the ring**: a cut-off for every key list `l` and every position `j`; the
scheme reads it at the positions of the ring only (`ringCuts`), so its values at positions past
`l.length` do not matter. -/
abbrev CutoffFamily : Type := List (PubKey p prims) → ℕ → Cutoff p

/-- **The constant cut-off family** at the level `β_min`: every member of every ring has the
constant cut-off `Cutoff.const βmin` (the ring of `MLDSAW1Ring.lean` at its parameters). A plain
definition, read through `constCut_apply`. -/
def constCut (βmin : ℚ≥0) : CutoffFamily prims := fun _ _ => Cutoff.const βmin

/-- The constant cut-off family gives every member the constant cut-off. -/
theorem constCut_apply (βmin : ℚ≥0) (l : List (PubKey p prims)) (j : ℕ) :
    constCut prims βmin l j = Cutoff.const βmin :=
  rfl

/-- **One level for the ring**: every two positions of a key list have the same public level `top`
(so that the number of attempts does not depend on the signer). Stated for all positions, a
deliberate strengthening: the scheme reads the family at the members' positions only. -/
def CutoffFamily.SameTop (cutOf : CutoffFamily prims) : Prop :=
  ∀ l i j, (cutOf l i).top = (cutOf l j).top

/-- **The ring's level is at least `β`** at every position of every key list (stated for all
positions, a deliberate strengthening as for `SameTop`; the scheme reads the members' positions
only). -/
def CutoffFamily.LevelAtLeast (cutOf : CutoffFamily prims) (β : ℚ≥0) : Prop :=
  ∀ l j, β ≤ (cutOf l j).top

/-- The constant cut-off family has one level for the ring. -/
theorem constCut_sameTop (βmin : ℚ≥0) : CutoffFamily.SameTop prims (constCut prims βmin) :=
  fun _ _ _ => rfl

/-- The constant cut-off family has level `β_min`. -/
theorem constCut_levelAtLeast (βmin : ℚ≥0) :
    CutoffFamily.LevelAtLeast prims (constCut prims βmin) βmin :=
  fun _ _ => le_rfl

/-- **The members' cut-offs of a ring** as a function of its positions. -/
def ringCuts (cutOf : CutoffFamily prims) (l : List (PubKey p prims)) :
    Fin l.length → Cutoff p :=
  fun j => cutOf l j

/-- At the constant cut-off family every member's cut-off is the constant cut-off. -/
theorem ringCuts_constCut (βmin : ℚ≥0) (l : List (PubKey p prims)) :
    ringCuts prims (constCut prims βmin) l = fun _ => Cutoff.const βmin :=
  rfl

/-- The members' oracle points `(tr_j, m)` of a ring and a message. -/
def ringPts {Msg : Type} (l : List (PubKey p prims)) (m : Msg) : Fin l.length → Bytes 64 × Msg :=
  fun j => (pubTr prims (l.get j), m)

variable [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]
  {Msg : Type} [Fintype Msg] [DecidableEq Msg]

/-- **The members' message representatives** `µ_j = H(tr_j ‖ m)` of a ring and a message. -/
def ringMus (Hmu : MuOrc Msg) (l : List (PubKey p prims)) (m : Msg) : Fin l.length → Bytes 64 :=
  fun j => Hmu (ringPts prims l m j)

/-! ### The public ring check -/

/-- **The ring defect at per-member cut-offs**: the sum of the members' check defects, member `j`
at its cut-off `cutOf l j`. -/
noncomputable def ringDefectOf (cutOf : CutoffFamily prims) (l : List (PubKey p prims)) : ℝ :=
  ∑ j, checkDefect prims (ringCuts prims cutOf l j) (ringT0s prims l j)

/-- **The ring defect** at the cut-off `β_min`: the sum of the members' check defects
(`ringDefectOf` at the constant cut-off family `constCut βmin`). -/
noncomputable abbrev ringDefect (βmin : ℚ≥0) (l : List (PubKey p prims)) : ℝ :=
  ringDefectOf prims (constCut prims βmin) l

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
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

/-- **The failed check samples of a ring at per-member cut-offs** against the check oracle `G`:
the number of pairs of a member `j` and a sample `r < reps` at which the check weight of `t₀,j`
at the commitment hash `c = G(l, j, r)` is below member `j`'s cut-off at `c`
(`(cutOf l j).val c`). -/
def checkFailsOf (cutOf : CutoffFamily prims) {N reps : ℕ} (G : CheckOrc p prims N reps)
    (l : RingOf (PubKey p prims) N) : ℕ :=
  (univ.filter fun jr : Fin l.1.length × Fin reps =>
    checkWeight prims (ringT0s prims l.1 jr.1) (G (l, Fin.castLE l.2 jr.1, jr.2)) <
      (ringCuts prims cutOf l.1 jr.1).val (G (l, Fin.castLE l.2 jr.1, jr.2))).card

/-- **The failed check samples of a ring** at the cut-off `β_min` against the check oracle `G`:
the number of pairs of a member `j` and a sample `r < reps` at which the check weight of `t₀,j`
at the commitment hash `G(l, j, r)` is below `β_min` (`checkFailsOf` at the constant cut-off
family `constCut βmin`). -/
abbrev checkFails (βmin : ℚ≥0) {N reps : ℕ} (G : CheckOrc p prims N reps)
    (l : RingOf (PubKey p prims) N) : ℕ :=
  checkFailsOf prims (constCut prims βmin) G l


/-- **The public ring check** at the cut-off `β_min` with tolerance `tol` against the check oracle
`G`: at most `tol` of the pairs of a member `j` and a sample `r < reps` have the check weight of
`t₀,j` at the commitment hash `G(l, j, r)` below `β_min` (`checkFails`). A function of the
published keys and `G` only. -/
def sampledRingCheck (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (G : CheckOrc p prims N reps)
    (l : RingOf (PubKey p prims) N) : Prop :=
  checkFails prims βmin G l ≤ tol

/-- The public ring check is decided by comparing the count of failed samples with `tol`. -/
instance (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (G : CheckOrc p prims N reps)
    (l : RingOf (PubKey p prims) N) : Decidable (sampledRingCheck prims βmin tol G l) :=
  inferInstanceAs (Decidable (checkFails prims βmin G l ≤ tol))

/-- **The sampled ring check** at the cut-off family `cutOf` with tolerance `tol`, as a Boolean
test of the ring `l` and its check samples `g j r = G(l, j, r)`: at most `tol` failed samples
(`checkFailsOf`). The test the signer runs. -/
def sampledAdm (cutOf : CutoffFamily prims) (tol : ℕ) {N reps : ℕ}
    (l : RingOf (PubKey p prims) N) (g : Fin N → Fin reps → CommitHashBytes p) : Bool :=
  decide (checkFailsOf prims cutOf
    (fun pt : RingOf (PubKey p prims) N × Fin N × Fin reps => g pt.2.1 pt.2.2) l ≤ tol)

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- At the constant cut-off family the sampled test passes exactly when the public ring check
`sampledRingCheck` holds. -/
theorem sampledAdm_constCut_eq_true_iff (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ}
    (G : CheckOrc p prims N reps) (l : RingOf (PubKey p prims) N) :
    sampledAdm prims (constCut prims βmin) tol l (fun j r => G (l, j, r)) = true ↔
      sampledRingCheck prims βmin tol G l :=
  decide_eq_true_iff

/-- The oracles of the game: the scheme's oracles (the message-representative oracle `H_µ` and
the commitment-hash oracle `H`) and the check oracle `G`. -/
abbrev GameOrc {p : Params} (prims : Primitives p) (Msg : Type) (N reps : ℕ) : Type :=
  SchOrc p Msg × CheckOrc p prims N reps

/-- **Distinct message representatives**: the members' `µ_j = H_µ(tr_j ‖ m)` of a ring and a
message are pairwise distinct. The signer computes them. -/
def MuDistinct (Hmu : MuOrc Msg) {N : ℕ} (l : RingOf (PubKey p prims) N) (m : Msg) : Prop :=
  (l.1.map fun x => Hmu (pubTr prims x, m)).Nodup

/-- **Distinctness of the message representatives is decided**: it is `List.Nodup` of a list of
`Bytes 64`. -/
@[instance_reducible, instance]
def instDecidableMuDistinct (Hmu : MuOrc Msg) {N : ℕ} (l : RingOf (PubKey p prims) N) (m : Msg) :
    Decidable (MuDistinct prims Hmu l m) :=
  inferInstanceAs (Decidable (List.Nodup _))

/-- **An admissible ring and message at the game's oracles** `((H_µ, H), G)`: distinct message
representatives `µ_j` and the public ring check with tolerance `tol` against `G`. A function of
the published keys, the message and the oracles only. -/
def RingAdmissible (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (HG : GameOrc prims Msg N reps)
    (l : RingOf (PubKey p prims) N) (m : Msg) : Prop :=
  MuDistinct prims HG.1.1 l m ∧ sampledRingCheck prims βmin tol HG.2 l

/-- **Admissibility is decided**: the distinctness of the message representatives
(`instDecidableMuDistinct`) and the sampled ring check, which counts failed checks
(`sampledRingCheck`, a comparison of natural numbers). -/
instance (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (HG : GameOrc prims Msg N reps)
    (l : RingOf (PubKey p prims) N) (m : Msg) : Decidable (RingAdmissible prims βmin tol HG l m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **A ring of defect at most `s`** at the cut-off `β_min`. -/
def LowDefect (βmin : ℚ≥0) (s : ℝ) {N : ℕ} (l : RingOf (PubKey p prims) N) : Prop :=
  ringDefect prims βmin l.1 ≤ s


variable [Inhabited prims.Hint] [Fintype prims.Hint]


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
/-- **A ring of defect at least `s` passes the check with tolerance `tol` with probability at most
`checkError reps tol s x`** over a uniform check oracle, for every `x ≥ 1` (the Chernoff lower
tail): the `n · reps` check points `(l, j, r)` are distinct, so the failures are independent with
probabilities the check defects `δ_j`; `1[F ≤ tol] ≤ x^tol · x^(-F)` for the number `F` of
failures, whose expectation is `x^tol · ∏_j (1 - (1 - 1/x) δ_j)^reps ≤
x^tol · exp(-(1 - 1/x) · reps ∑_j δ_j)` (`PMF.expect_comp_embedding`, `PMF.expect_prod_apply`). -/
theorem expect_ringCheck_le (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (l : RingOf (PubKey p prims) N)
    {s x : ℝ} (hs : s ≤ ringDefect prims βmin l.1) (hx : 1 ≤ x) :
    𝔼 G : CheckOrc p prims N reps, (if sampledRingCheck prims βmin tol G l then 1 else 0 : ℝ) ≤
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
      (if sampledRingCheck prims βmin tol G l then 1 else 0 : ℝ) ≤ x ^ tol * ∏ jr, ψ jr (G (e
          jr)) :=
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
    rw [Fintype.sum_prod_type, ringDefect, ringDefectOf, Finset.mul_sum]
    simp [ringCuts_constCut]
  calc 𝔼 G : CheckOrc p prims N reps, (if sampledRingCheck prims βmin tol G l then 1 else 0 : ℝ)
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
/-- **A ring of defect at least `s` at per-member cut-offs passes the sampled test with tolerance
`tol` with probability at most `checkError reps tol s x`** over a uniform check oracle, for every
`x ≥ 1`: `expect_ringCheck_le` with the threshold of each sample the cut-off of its member at the
sample's commitment hash, so that the probability that a sample of member `j` fails is the check
defect of `t₀,j` at `cutOf l j` (`checkDefect`). -/
theorem expect_sampledAdm_le (cutOf : CutoffFamily prims) (tol : ℕ) {N reps : ℕ}
    (l : RingOf (PubKey p prims) N) {s x : ℝ} (hs : s ≤ ringDefectOf prims cutOf l.1)
    (hx : 1 ≤ x) :
    𝔼 G : CheckOrc p prims N reps,
        (if sampledAdm prims cutOf tol l (fun j r => G (l, j, r)) = true then 1 else 0 : ℝ) ≤
      checkError reps tol s x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h1x : 0 ≤ 1 - x⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hx)
  set ψ : Fin l.1.length × Fin reps → CommitHashBytes p → ℝ := fun jr c =>
    if checkWeight prims (ringT0s prims l.1 jr.1) c < (ringCuts prims cutOf l.1 jr.1).val c
    then x⁻¹ else 1
  have hψ0 : ∀ jr c, 0 ≤ ψ jr c := fun jr c => by
    simp only [ψ]
    split_ifs <;> positivity
  let e : Fin l.1.length × Fin reps ↪ RingOf (PubKey p prims) N × Fin N × Fin reps :=
    ⟨fun jr => (l, Fin.castLE l.2 jr.1, jr.2), fun a b h => by
      simp only [Prod.mk.injEq, Fin.castLE_inj] at h
      exact Prod.ext h.2.1 h.2.2⟩
  have h1 : ∀ G : CheckOrc p prims N reps,
      (if sampledAdm prims cutOf tol l (fun j r => G (l, j, r)) = true then 1 else 0 : ℝ) ≤
        x ^ tol * ∏ jr, ψ jr (G (e jr)) := fun G => by
    have hprod : ∏ jr, ψ jr (G (e jr)) = x⁻¹ ^ checkFailsOf prims cutOf G l := by
      simp only [ψ]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      rfl
    rw [hprod, inv_pow, ← div_eq_mul_inv]
    split_ifs with h
    · rw [le_div_iff₀ (pow_pos hx0 _), one_mul]
      exact pow_le_pow_right₀ hx (of_decide_eq_true h)
    · positivity
  have hψ : ∀ jr, 𝔼 c, ψ jr c =
      1 - (1 - x⁻¹) * checkDefect prims (ringCuts prims cutOf l.1 jr.1) (ringT0s prims l.1 jr.1) :=
    fun jr => by
    have h : ∀ c, ψ jr c = 1 - (1 - x⁻¹) *
        (if checkWeight prims (ringT0s prims l.1 jr.1) c < (ringCuts prims cutOf l.1 jr.1).val c
          then 1 else 0) := fun c => by
      simp only [ψ]
      split_ifs <;> ring
    rw [Finset.expect_congr rfl fun c _ => h c, Finset.expect_sub_distrib,
      Finset.expect_const univ_nonempty, ← Finset.mul_expect, checkDefect]
  have hsum : ∑ jr : Fin l.1.length × Fin reps,
      checkDefect prims (ringCuts prims cutOf l.1 jr.1) (ringT0s prims l.1 jr.1) =
      reps * ringDefectOf prims cutOf l.1 := by
    rw [Fintype.sum_prod_type, ringDefectOf, Finset.mul_sum]
    simp
  calc 𝔼 G : CheckOrc p prims N reps,
        (if sampledAdm prims cutOf tol l (fun j r => G (l, j, r)) = true then 1 else 0 : ℝ)
      ≤ 𝔼 G : CheckOrc p prims N reps, x ^ tol * ∏ jr, ψ jr (G (e jr)) :=
        Finset.expect_le_expect fun G _ => h1 G
    _ = x ^ tol * ∏ jr, 𝔼 c, ψ jr c := by
        rw [← Finset.mul_expect, PMF.expect_comp_embedding e (fun g => ∏ jr, ψ jr (g jr)),
          PMF.expect_prod_apply]
    _ ≤ x ^ tol * ∏ jr : Fin l.1.length × Fin reps,
          Real.exp (-((1 - x⁻¹) *
            checkDefect prims (ringCuts prims cutOf l.1 jr.1) (ringT0s prims l.1 jr.1))) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun jr _ => Finset.expect_nonneg fun c _ => hψ0 jr c) fun jr _ => ?_) (by positivity)
        rw [hψ jr]
        linarith [Real.add_one_le_exp (-((1 - x⁻¹) *
          checkDefect prims (ringCuts prims cutOf l.1 jr.1) (ringT0s prims l.1 jr.1)))]
    _ = x ^ tol * Real.exp (-((1 - x⁻¹) * (reps * ringDefectOf prims cutOf l.1))) := by
        rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, hsum]
    _ ≤ checkError reps tol s x :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)) h1x))) (by positivity)

omit [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] in
/-- **The ring check** at the cut-off family `cutOf`: an admissibility test of rings against the
check oracle `G`, with the property the anonymity bound reads (`CheckHit`, `w1OracleAnonError`).
Its fields:

- `adm`: the test, a Boolean function of the ring `l` and its check samples `G(l, j, r)` (computable
  data; the signer runs it, and its decision is the Boolean itself);
- `s`: the shortfall level;
- `e`: the test's error, nonnegative (`e_nonneg`);
- `shortfall_le`: a ring whose members' check defects at the cut-off family `cutOf` sum to at
  least `s` (`ringDefectOf`) passes the test with probability at most `e`, an expectation over a
  uniform check oracle.

`RingCheck.sampled` is the sampled test `sampledAdm` the signer runs, with the Chernoff bound
`expect_sampledAdm_le`; at the constant cut-off family it admits exactly the rings passing the
public ring check `sampledRingCheck` (`RingCheck.sampled_admits_constCut_iff`). -/
structure RingCheck (cutOf : CutoffFamily prims) (N reps : ℕ) where
  /-- The test: admits the ring `l` at its check samples `g j r = G(l, j, r)`. -/
  adm : RingOf (PubKey p prims) N → (Fin N → Fin reps → CommitHashBytes p) → Bool
  /-- The shortfall level. -/
  s : ℝ
  /-- The error of the test. -/
  e : ℝ
  /-- The error is nonnegative. -/
  e_nonneg : 0 ≤ e
  /-- A ring of defect at least `s` passes the test with probability at most `e` over a uniform
  check oracle. -/
  shortfall_le : ∀ l : RingOf (PubKey p prims) N, s ≤ ringDefectOf prims cutOf l.1 →
    𝔼 G : CheckOrc p prims N reps, (if adm l (fun j r => G (l, j, r)) = true then 1 else 0 : ℝ) ≤ e

omit [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] in
/-- **The ring `l` passes the ring check `chk`** against the check oracle `G`. -/
abbrev RingCheck.Admits {cutOf : CutoffFamily prims} {N reps : ℕ}
    (chk : RingCheck prims cutOf N reps) (G : CheckOrc p prims N reps)
    (l : RingOf (PubKey p prims) N) : Prop :=
  chk.adm l (fun j r => G (l, j, r)) = true

omit [NeZero (bucketCount p)] [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] in
/-- **Admission reads the check oracle at the ring's points only**: two check oracles agreeing at
the points `(l, j, r)` admit `l` alike. -/
theorem RingCheck.admits_congr {cutOf : CutoffFamily prims} {N reps : ℕ}
    (chk : RingCheck prims cutOf N reps) {G G' : CheckOrc p prims N reps}
    {l : RingOf (PubKey p prims) N} (h : ∀ j r, G (l, j, r) = G' (l, j, r)) :
    chk.Admits prims G l ↔ chk.Admits prims G' l := by
  unfold RingCheck.Admits
  rw [show (fun j r => G (l, j, r)) = fun j r => G' (l, j, r) from funext fun j => funext (h j)]

omit [NeZero (bucketCount p)] [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] in
/-- **A ring of shortfall above `s` passes the ring check with probability at most `e`**
(`shortfall_le`, and `0` below), as the expectation of the indicator of both. -/
theorem RingCheck.expect_high_admits_le {cutOf : CutoffFamily prims} {N reps : ℕ}
    (chk : RingCheck prims cutOf N reps) (l : RingOf (PubKey p prims) N) :
    𝔼 G : CheckOrc p prims N reps,
        (if chk.s < ringDefectOf prims cutOf l.1 ∧ chk.Admits prims G l then 1 else 0 : ℝ) ≤
      chk.e := by
  classical
  by_cases hl : chk.s < ringDefectOf prims cutOf l.1
  · refine (Finset.expect_le_expect fun G _ => ?_).trans (chk.shortfall_le l hl.le)
    by_cases h : chk.adm l (fun j r => G (l, j, r)) = true <;> simp [RingCheck.Admits, hl, h]
  · simp only [hl, false_and, ite_false, Finset.expect_const_zero]
    exact chk.e_nonneg

omit [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] in
/-- **The sampled ring check** at the cut-off family `cutOf` with tolerance `tol`, shortfall level
`s` and Chernoff parameter `x ≥ 1`: the test `sampledAdm cutOf tol` (which reads neither `s` nor
`x`) with error `checkError reps tol s x` (`expect_sampledAdm_le`). -/
noncomputable def RingCheck.sampled (cutOf : CutoffFamily prims) (tol N reps : ℕ) (s x : ℝ)
    (hx : 1 ≤ x) : RingCheck prims cutOf N reps where
  adm := sampledAdm prims cutOf tol
  s := s
  e := checkError reps tol s x
  e_nonneg := by
    have : (0 : ℝ) ≤ x := zero_le_one.trans hx
    unfold checkError
    positivity
  shortfall_le l hs := expect_sampledAdm_le prims cutOf tol l hs hx

omit [NeZero (bucketCount p)] [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] in
/-- At the constant cut-off family the sampled ring check admits exactly the rings passing the
public ring check `sampledRingCheck`. -/
theorem RingCheck.sampled_admits_constCut_iff (βmin : ℚ≥0) (tol N reps : ℕ) (s x : ℝ)
    (hx : 1 ≤ x) (G : CheckOrc p prims N reps) (l : RingOf (PubKey p prims) N) :
    (RingCheck.sampled prims (constCut prims βmin) tol N reps s x hx).Admits prims G l ↔
      sampledRingCheck prims βmin tol G l :=
  sampledAdm_constCut_eq_true_iff prims βmin tol G l

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- **The union bound over a finite set of rings**: over a uniform check oracle, some ring of
`F` (through `ring`) of shortfall above `chk.s` passes the ring check `chk` with probability at
most `|F| · chk.e` (`RingCheck.expect_high_admits_le`). -/
theorem expect_exists_ringCheck_le {cutOf : CutoffFamily prims} {N reps : ℕ}
    (chk : RingCheck prims cutOf N reps) {α : Type*} (F : Finset α)
    (ring : α → RingOf (PubKey p prims) N) :
    𝔼 G : CheckOrc p prims N reps, (if ∃ a ∈ F, chk.s < ringDefectOf prims cutOf (ring a).1 ∧
        chk.Admits prims G (ring a) then 1 else 0 : ℝ) ≤ F.card * chk.e := by
  set f : α → CheckOrc p prims N reps → ℝ := fun a G =>
    if chk.s < ringDefectOf prims cutOf (ring a).1 ∧ chk.Admits prims G (ring a) then 1 else 0
  have hf0 : ∀ a G, 0 ≤ f a G := fun a G => by simp only [f]; split_ifs <;> norm_num
  calc 𝔼 G : CheckOrc p prims N reps, (if ∃ a ∈ F, chk.s < ringDefectOf prims cutOf (ring a).1 ∧
        chk.Admits prims G (ring a) then 1 else 0 : ℝ)
      ≤ 𝔼 G : CheckOrc p prims N reps, ∑ a ∈ F, f a G := Finset.expect_le_expect fun G _ => by
        split_ifs with h
        · obtain ⟨a, ha, h⟩ := h
          have : f a G = 1 := if_pos h
          exact this ▸ Finset.single_le_sum (fun a _ => hf0 a G) ha
        · exact Finset.sum_nonneg fun a _ => hf0 a G
    _ = ∑ a ∈ F, 𝔼 G : CheckOrc p prims N reps, f a G := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _a ∈ F, chk.e := Finset.sum_le_sum fun a _ => chk.expect_high_admits_le prims (ring a)
    _ = F.card * chk.e := by rw [Finset.sum_const, nsmul_eq_mul]


omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] in
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


/-! ### The regularity gap at uniform key material -/

section UniformKeys

open LatticeCrypto TransformOps

/-- **The average regularity gap with a uniform matrix**: `signerRegGap` (whose challenge `c̃` is
uniform, `c = SampleInBall(c̃)`) at the key of a uniform seed's `ρ`, `K` and
`(s₁, s₂) = ExpandS(ρ')` (the `expandS` of the primitives `prims`; FIPS 204 Algorithm 33 at the
concrete primitives), with the matrix `Â` uniform and independent of the seed. -/
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


/-! ### Anonymity with `ExpandA` a random oracle -/


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
  [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι}
  {Mg : Merges τ} {nr : ι → ℕ} {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n Q : ℕ}


end GordieHowe.Ring.MLDSAW1
