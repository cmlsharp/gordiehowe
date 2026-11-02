-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.RingSigner
public import GordieHowe.Applications.MLDSA44.Spec.Encoding
public import GordieHowe.Applications.MLDSA.Regularity.RqRegularity
import all LatticeCrypto.MLDSA.Concrete.Rounding
import all LatticeCrypto.MLDSA.ConcretePrimitives

@[expose] public section

/-!
# The signer's acceptance event coefficientwise

At the concrete primitives, the event "`HighBits(Â·y) = v` and the four checks of FIPS 204
Algorithm 7 pass" is the z-check together with membership of the coefficients of `Â·y` in the
uniform-`w` acceptance set (`realBuckets_attemptAccept_iff`): the r0-check, the ct₀-check and
the hint-count check read the coefficients of `Â·y - c s₂` and `c t₀` only.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

/-- **The concrete primitives with `SampleInBall` replaced by `G`**: every other primitive is the
concrete one. At `G = (concretePrimitives p).sampleInBall` this is `concretePrimitives p`
(`concreteWithSampleInBall_concrete`); for `G` a random oracle onto the challenge set it is the
game in which `SampleInBall` (FIPS 204 Algorithm 29) is a random oracle. -/
def concreteWithSampleInBall (p : Params) (G : CommitHashBytes p → ChallengePoly) : Primitives p :=
  { concretePrimitives p with sampleInBall := G }

/-- At the concrete `SampleInBall` the primitives are the concrete ones. -/
theorem concreteWithSampleInBall_concrete (p : Params) :
    concreteWithSampleInBall p (concretePrimitives p).sampleInBall = concretePrimitives p :=
  rfl

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  {G : CommitHashBytes p → ChallengePoly}

omit [NeZero (bucketCount p)] nttOps in
theorem lowBitsVec_get_get {k : ℕ} (w : RqVec k) (j : Fin k) (i : Fin ringDegree) :
    (((concreteWithSampleInBall p G).lowBitsVec w).get j).get i =
      ((lowBitsCoeff ((w.get j).get i) p.gamma2 : ℤ) : Coeff) := by
  simp only [Primitives.lowBitsVec, Vector.get_map]
  exact LatticeCrypto.Poly.get_vectorOfFn _ i

omit [NeZero (bucketCount p)] nttOps in
theorem abs_lowBitsCoeff_le (hp : SigningParams p) (x : Coeff) :
    |lowBitsCoeff x p.gamma2| ≤ p.gamma2 := by
  have := (GordieHowe.MLDSA44.decomposeCoeff_repr hp.gamma2_pos hp.gamma2_dvd x).low_mem
  unfold lowBitsCoeff
  rw [abs_le]
  rcases this with h | h <;> omega

omit nttOps in
theorem natAbs_lt_iff_abs_lt {z : ℤ} {c : ℕ} : z.natAbs < c ↔ |z| < c := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast Iff.rfl

/-- The r0-check coefficientwise. -/
theorem r0Check_lowBitsVec_iff (hp : SigningParams p) (w : RqVec p.k) :
    r0Check (p := p) ((concreteWithSampleInBall p G).lowBitsVec w) = true ↔
      ∀ x : CoeffIndex p, |lowBitsCoeff (rqVecCoeffs w x) p.gamma2| < (p.gamma2 : ℤ) - p.beta := by
  have hβ := hp.beta_lt_gamma2
  have hq : 2 * p.gamma2 < modulus := by have := hp.two_buckets; omega
  rw [r0Check, decide_eq_true_iff, polyVecNorm_lt_iff _ (by omega)]
  constructor
  · intro h x
    have := h x.1 x.2
    rw [lowBitsVec_get_get, LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le _
      (by have := abs_lowBitsCoeff_le hp ((w.get x.1).get x.2); rw [abs_le] at this; omega) hq,
      natAbs_lt_iff_abs_lt] at this
    rw [rqVecCoeffs_apply]
    push_cast [Nat.cast_sub hβ.le] at this
    exact this
  · intro h j i
    have := h (j, i)
    rw [lowBitsVec_get_get, LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le _
      (by have := abs_lowBitsCoeff_le hp ((w.get j).get i); rw [abs_le] at this; omega) hq,
      natAbs_lt_iff_abs_lt]
    rw [rqVecCoeffs_apply] at this
    push_cast [Nat.cast_sub hβ.le]
    exact this

omit [NeZero (bucketCount p)] in
/-- The ct₀-check coefficientwise. -/
theorem ct0Check_iff (hp : SigningParams p) (sk : SecretKey p) (cTilde : CommitHashBytes p) :
    ct0Check (p := p) ((concreteWithSampleInBall p G).sampleInBall cTilde • sk.t0) = true ↔
      ∀ x, |ct0Shift (concreteWithSampleInBall p G) sk cTilde x| < p.gamma2 := by
  rw [ct0Check, decide_eq_true_iff, polyVecNorm_lt_iff _ hp.gamma2_pos]
  constructor
  · intro h x
    have := h x.1 x.2
    rw [ct0Shift, centeredCoeffs, rqVecCoeffs_apply, ← natAbs_lt_iff_abs_lt]
    exact this
  · intro h j i
    have := h (j, i)
    rw [ct0Shift, centeredCoeffs, rqVecCoeffs_apply, ← natAbs_lt_iff_abs_lt] at this
    exact this

omit nttOps in
theorem rqVec_add_get_get {k : ℕ} (u v : RqVec k) (j : Fin k) (i : Fin ringDegree) :
    ((u + v).get j).get i = (u.get j).get i + (v.get j).get i := by
  have h1 : (u + v).get j = u.get j + v.get j := by
    simp only [Vector.get_eq_getElem, Vector.getElem_add]
  rw [h1, Rq.get_add]

omit nttOps in
theorem rqVec_sub_get_get {k : ℕ} (u v : RqVec k) (j : Fin k) (i : Fin ringDegree) :
    ((u - v).get j).get i = (u.get j).get i - (v.get j).get i := by
  have h1 : (u - v).get j = u.get j - v.get j := by
    simp only [Vector.get_eq_getElem, Vector.getElem_sub]
  rw [h1, Rq.get_sub]

omit nttOps in
theorem rqVec_neg_get_get {k : ℕ} (u : RqVec k) (j : Fin k) (i : Fin ringDegree) :
    ((-u).get j).get i = -(u.get j).get i := by
  have h1 : (-u).get j = -u.get j := by
    simp only [Vector.get_eq_getElem, Vector.getElem_neg]
  rw [h1, Rq.get_neg]

omit [NeZero (bucketCount p)] in
/-- The hint-count check coefficientwise. -/
theorem hintCheck_attemptHint_iff (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) :
    hintCheck (concreteWithSampleInBall p G) (attemptHint (concreteWithSampleInBall p G) sk aHat y cTilde) = true ↔
      #(univ.filter fun x : CoeffIndex p =>
        makeHintCoeff (-(ct0Shift (concreteWithSampleInBall p G) sk cTilde x : Coeff))
          (rqVecCoeffs (aHat * y) x - (cs2Shift (concreteWithSampleInBall p G) sk cTilde x : Coeff) +
            (ct0Shift (concreteWithSampleInBall p G) sk cTilde x : Coeff)) p.gamma2 = true) ≤ p.omega := by
  set z : RqVec p.k := -((concreteWithSampleInBall p G).sampleInBall cTilde • sk.t0)
  set r : RqVec p.k := aHat * y - (concreteWithSampleInBall p G).sampleInBall cTilde • sk.s2 +
    (concreteWithSampleInBall p G).sampleInBall cTilde • sk.t0
  have hz : Vector.zipWith (makeHint p) z r =
      Vector.ofFn fun j => Vector.ofFn fun i => makeHintCoeff ((z.get j).get i) ((r.get j).get i)
        p.gamma2 := by
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_zipWith, Vector.getElem_ofFn]
    rfl
  rw [hintCheck, decide_eq_true_iff]
  change hintWeightVec (Vector.zipWith (makeHint p) z r) ≤ p.omega ↔ _
  rw [hz, GordieHowe.MLDSA44.hintWeightVec_ofFn]
  have hcoef : ∀ x : CoeffIndex p, makeHintCoeff ((z.get x.1).get x.2) ((r.get x.1).get x.2)
      p.gamma2 = makeHintCoeff (-(ct0Shift (concreteWithSampleInBall p G) sk cTilde x : Coeff))
        (rqVecCoeffs (aHat * y) x - (cs2Shift (concreteWithSampleInBall p G) sk cTilde x : Coeff) +
          (ct0Shift (concreteWithSampleInBall p G) sk cTilde x : Coeff)) p.gamma2 := by
    intro x
    simp only [z, r, rqVec_neg_get_get, rqVec_add_get_get, rqVec_sub_get_get, ct0Shift, cs2Shift,
      centeredCoeffs, rqVecCoeffs_apply, ← LatticeCrypto.centeredRepr_intCast]
  simp_rw [hcoef]

theorem realBuckets_eq_iff (hp : SigningParams p) (aHat : TqMatrix p.k p.l) (y : MaskBox p)
    (v : BucketVec p) :
    realBuckets aHat y = v ↔ ∀ x, highBitsCoeff (rqVecCoeffs (aHat * y.1) x) p.gamma2 = (v x).val := by
  constructor
  · rintro rfl x
    rw [realBuckets, val_bucketsOf hp]
  · intro h
    funext x
    exact Fin.ext (by rw [realBuckets, val_bucketsOf hp]; exact h x)

/-- **The signer's acceptance event at the concrete primitives**: `HighBits(Â·y) = v` and the four
checks pass exactly when the z-check passes and the coefficients of `Â·y` lie in the
uniform-`w` acceptance set with `a = c s₂`, `b = c t₀`. -/
theorem realBuckets_attemptAccept_iff (hp : SigningParams p) (sk : SecretKey p)
    (aHat : TqMatrix p.k p.l) (y : MaskBox p) (cTilde : CommitHashBytes p) (v : BucketVec p) :
    (realBuckets aHat y = v ∧ attemptAccept (concreteWithSampleInBall p G) sk aHat y cTilde = true) ↔
      zCheck (p := p) (y.1 + (concreteWithSampleInBall p G).sampleInBall cTilde • sk.s1) = true ∧
        rqVecCoeffs (aHat * y.1) ∈ acceptSet p.gamma2 p.beta p.omega
          (cs2Shift (concreteWithSampleInBall p G) sk cTilde) (ct0Shift (concreteWithSampleInBall p G) sk cTilde)
          fun x => (v x).val := by
  have hsub : ∀ x, rqVecCoeffs (aHat * y.1 - (concreteWithSampleInBall p G).sampleInBall cTilde • sk.s2) x =
      rqVecCoeffs (aHat * y.1) x - (cs2Shift (concreteWithSampleInBall p G) sk cTilde x : Coeff) := by
    intro x
    rw [rqVecCoeffs_apply, rqVec_sub_get_get, cs2Shift, centeredCoeffs, rqVecCoeffs_apply,
      rqVecCoeffs_apply, ← LatticeCrypto.centeredRepr_intCast]
  rw [realBuckets_eq_iff hp, attemptAccept, signAccept]
  simp only [Bool.and_eq_true, r0Check_lowBitsVec_iff hp, ct0Check_iff hp,
    hintCheck_attemptHint_iff, hsub, acceptSet, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-! ### Masses as counts -/

omit nttOps in
theorem toReal_signerMass_uniform {Y V C : Type*} [Fintype Y] [Nonempty Y] [DecidableEq V]
    (w1 : Y → V) (acc : Y → C → Bool) (v : V) (c : C) :
    (PMF.signerMass (PMF.uniformOfFintype Y) w1 acc v c).toReal =
      (Fintype.card Y : ℝ)⁻¹ * #(univ.filter fun y => w1 y = v ∧ acc y c = true) := by
  rw [PMF.signerMass, ENNReal.toReal_sum (fun y _ => by split_ifs <;> simp [PMF.uniformOfFintype_apply])]
  simp_rw [apply_ite ENNReal.toReal, PMF.toReal_uniformOfFintype_apply, ENNReal.toReal_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [NeZero (bucketCount p)] in
/-- The z-check box coefficientwise (as in `zCheck_vec_card`). -/
theorem inMaskBox_zCheck_iff (hp : SigningParams p) (v : RqVec p.l) (y : RqVec p.l) :
    (InMaskBox p.gamma1 y ∧ zCheck (p := p) (y + v) = true) ↔
      ∀ j i, (y.get j).get i ∈
        zCheckCoeffSet p.gamma1 p.beta (LatticeCrypto.centeredRepr ((v.get j).get i)) := by
  have hβ := hp.beta_lt_gamma1
  rw [zCheck, decide_eq_true_iff, polyVecNorm_lt_iff _ (by omega)]
  simp only [zCheckCoeffSet, Finset.mem_filter, Finset.mem_univ, true_and, InMaskBox]
  have hadd : ∀ j i, ((y + v).get j).get i =
      (y.get j).get i + (((LatticeCrypto.centeredRepr ((v.get j).get i) : ℤ)) : Coeff) := by
    intro j i
    rw [← LatticeCrypto.centeredRepr_intCast, rqVec_add_get_get]
  simp only [hadd]
  constructor
  · rintro ⟨h1, h2⟩ j i
    refine ⟨h1 j i, ?_⟩
    have := h2 j i
    rw [← LatticeCrypto.centeredRepr_intCast] at this ⊢
    rw [abs_lt]; omega
  · intro h
    refine ⟨fun j i => (h j i).1, fun j i => ?_⟩
    have := (h j i).2
    rw [← LatticeCrypto.centeredRepr_intCast] at this ⊢
    rw [abs_lt] at this; omega

/-! ### The matrix and the masks in the abstract model -/

/-- The coefficient-domain matrix `A = NTT⁻¹(Â)` entrywise. -/
noncomputable def matOfHat {k l : ℕ} (aHat : TqMatrix k l) : Fin k → Fin l → Rq :=
  fun i b => nttOps.fromHat ((aHat.get i).get b)

theorem rqVecCoeffs_mul_eq_matAct [NTTRingLaws nttOps] {k l : ℕ} (aHat : TqMatrix k l)
    (y : RqVec l) : rqVecCoeffs (aHat * y) = matAct (k := k) (fun b => y.get b) (matOfHat aHat) := by
  funext ic
  rw [rqVecCoeffs_apply]
  change ((nttOps.coeffMatVecMul aHat y).get ic.1).get ic.2 = getHom ic.2 _
  rw [coeffMatVecMul_get]
  rfl

/-- The z-check box of a shift `v` (`v = c s₁`): coordinate `(b, c)` ranges over the masks of
`zCheckCoeffSet γ₁ β v_{b,c}`. -/
def zBox (p : Params) (v : RqVec p.l) : Fin p.l × Fin ringDegree → Finset Coeff :=
  fun bc => zCheckCoeffSet p.gamma1 p.beta (LatticeCrypto.centeredRepr ((v.get bc.1).get bc.2))

omit nttOps in
theorem polyOf_get_self (f : Rq) : polyOf (fun c => f.get c) = f := by
  apply Vector.ext
  intro i hi
  exact polyOf_get (fun c => f.get c) ⟨i, hi⟩

/-- The coefficients of a mask vector. -/
def maskCoeffs {l : ℕ} (y : RqVec l) : Fin l × Fin ringDegree → Coeff :=
  fun bc => (y.get bc.1).get bc.2

theorem maskOf_maskCoeffs {l : ℕ} (y : RqVec l) : maskOf (maskCoeffs y) = fun b => y.get b := by
  funext b
  exact polyOf_get_self (y.get b)

open Classical in
/-- **The real accepted mass as a box average**: at the concrete primitives,
`realMass v c = |MaskBox|⁻¹ · #{z ∈ zBox (c s₁) | A·maskOf z ∈ acceptSet a b v}`. -/
theorem toReal_realMass_eq [NTTRingLaws nttOps] [Nonempty (MaskBox p)] (hp : SigningParams p)
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (cTilde : CommitHashBytes p)
    (hs1 : polyVecNorm ((concreteWithSampleInBall p G).sampleInBall cTilde • sk.s1) ≤ p.beta)
    (v : BucketVec p) :
    (realMass (concreteWithSampleInBall p G) sk aHat v cTilde).toReal =
      (Fintype.card (MaskBox p) : ℝ)⁻¹ *
        #((Fintype.piFinset (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk.s1))).filter
          fun z => matAct (k := p.k) (maskOf z) (matOfHat aHat) ∈ acceptSet p.gamma2 p.beta
            p.omega (cs2Shift (concreteWithSampleInBall p G) sk cTilde)
            (ct0Shift (concreteWithSampleInBall p G) sk cTilde) fun x => (v x).val) := by
  rw [realMass, maskUniform, toReal_signerMass_uniform]
  congr 2
  set cs1 := (concreteWithSampleInBall p G).sampleInBall cTilde • sk.s1
  refine Finset.card_bij (fun y _ => maskCoeffs y.1) ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    obtain ⟨-, hy⟩ := hy
    rw [realBuckets_attemptAccept_iff hp] at hy
    have hbox := (inMaskBox_zCheck_iff hp cs1 y.1).mp ⟨y.2, hy.1⟩
    refine ⟨Fintype.mem_piFinset.mpr fun bc => hbox bc.1 bc.2, ?_⟩
    rw [maskOf_maskCoeffs, ← rqVecCoeffs_mul_eq_matAct]
    exact hy.2
  · intro y _ y' _ h
    apply Subtype.ext
    apply Vector.ext
    intro b hb
    have := congrArg (fun z => polyOf fun c => z (⟨b, hb⟩, c)) h
    simp only [maskCoeffs] at this
    rw [polyOf_get_self, polyOf_get_self] at this
    simpa [Vector.get_eq_getElem] using this
  · intro z hz
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hz
    set y : RqVec p.l := Vector.ofFn (maskOf z)
    have hyc : maskCoeffs y = z := by
      funext bc
      simp only [maskCoeffs, y, Vector.get_ofFn, maskOf, polyOf_get]
    have hbox := (inMaskBox_zCheck_iff hp cs1 y).mpr fun j i => by
      have := hz.1 (j, i)
      rw [← hyc] at this
      exact this
    refine ⟨⟨y, hbox.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hyc⟩
    rw [realBuckets_attemptAccept_iff hp]
    refine ⟨hbox.2, ?_⟩
    rw [rqVecCoeffs_mul_eq_matAct, ← maskOf_maskCoeffs, hyc]
    exact hz.2

end GordieHowe.MLDSA.Regularity
