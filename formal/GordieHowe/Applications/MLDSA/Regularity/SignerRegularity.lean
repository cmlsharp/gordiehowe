-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.SignerAccept
public import GordieHowe.Applications.MLDSA.Regularity.ConcreteCells
public import GordieHowe.Applications.MLDSA.Regularity.SmallSupportBridge
public import GordieHowe.Applications.MLDSA.Regularity.KernelMass
public import GordieHowe.Applications.MLDSA.Regularity.HybridAnnihilator
public import GordieHowe.Foundations.ToMathlib.SqrtAverage

@[expose] public section

/-!
# The regularity of the ML-DSA signer

The real accepted mass of `(w₁, c̃)` minus `ρ_z` times the stand-in mass is `ρ_z` times the
combination `∑_t c_t D_t(v)` of the mask-average-minus-uniform differences of the products of
accepted-cell functions (`realMass_sub_standinMass_eq`), so the regularity bound over `R_q`
(`sum_norm_regularity_le`) bounds its average over the matrix (`sum_abs_realMass_sub_le`), and its
`ℓ²` form (`sum_sq_norm_regularity_le`) the mean square over the matrix of the column error
(`sum_sq_sum_abs_realMass_sub_le`). By Cauchy–Schwarz over the matrix, the mean regularity gap is
then at most `R / β_min · √(𝔼_Â w(Â)⁻²)` for every positive lower bound `w(Â)` on the mean member
weights (`expect_ringRegGap_le_sqrt`). The bound also holds for a lower bound `w(Â) ≥ 0` that
vanishes only where every mean member weight vanishes (`expect_ringRegGap_le_sqrt_of_nonneg`):
such a matrix has `ringRegGap = 0` (`ringRegGap_eq_zero`, each column `x / 0 = 0`) and
`w(Â)⁻² = 0`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] {M : ℕ} [NeZero M]
  {G : CommitHashBytes p → ChallengePoly}

open Classical in
/-- **The stand-in mass as a count**: `standinMass v c = q^{-N} · #(acceptSet a b v)`. -/
theorem toReal_standinMass_eq (hp : SigningParams p) (sk : SecretKey p)
    (cTilde : CommitHashBytes p) (v : BucketVec p) :
    (standinMass (concreteWithSampleInBall p G) sk v cTilde).toReal =
      (Fintype.card (CoeffIndex p → Coeff) : ℝ)⁻¹ *
        #(univ.filter fun w : CoeffIndex p → Coeff => w ∈ acceptSet p.gamma2 p.beta p.omega
          (cs2Shift (concreteWithSampleInBall p G) sk cTilde) (ct0Shift (concreteWithSampleInBall p G) sk cTilde)
          fun x => (v x).val) := by
  rw [standinMass, toReal_signerMass_uniform]
  congr 3
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨rfl, h⟩
    simpa [standinAccept] using h
  · intro h
    have hb : bucketsOf w = v := funext fun x => Fin.ext (by
      rw [val_bucketsOf hp]; exact ((Finset.mem_filter.1 h).2.1) x)
    refine ⟨hb, ?_⟩
    simp [standinAccept, hb, h]

/-! ### The key as a function of `A s₁` -/

/-- The low part `t₀` of `A s₁ + s₂` (FIPS 204 Algorithm 6, `Power2Round`). -/
noncomputable def t0Of (s₂ : RqVec p.k) (τ : Fin p.k → Rq) : RqVec p.k :=
  ((concretePrimitives p).power2RoundVec (Vector.ofFn τ + s₂)).2

/-- The secret key `sk₀` with `t₀` recomputed from `A s₁ = τ`. -/
noncomputable def keyOf (sk₀ : SecretKey p) (τ : Fin p.k → Rq) : SecretKey p :=
  { sk₀ with t0 := t0Of sk₀.s2 τ }

/-- The accepted-cell family of the signer with `SampleInBall = G`: expansion term `t`, key value
`τ = A s₁`, coefficient `ic`, bucket `r`. -/
noncomputable def signerCells (G : CommitHashBytes p → ChallengePoly) (sk₀ : SecretKey p)
    (cTilde : CommitHashBytes p)
    (t : ZMod M) (τ : Fin p.k → Rq) (ic : CoeffIndex p)
    (r : Fin (bucketCount p)) (x : Coeff) : ℂ :=
  acceptCell p.gamma2 p.beta (cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde)
    (ct0Shift (concreteWithSampleInBall p G) (keyOf sk₀ τ) cTilde) t ic r.val x

omit [NeZero (bucketCount p)] in
open Classical in
/-- The indicator expansion summed against the mask average and the uniform average. -/
theorem sum_countCoeff_maskDiff_eq [Nonempty (CoeffIndex p)] (hω : p.omega < M)
    (hN : Fintype.card (CoeffIndex p) < M)
    (sk₀ : SecretKey p) (cTilde : CommitHashBytes p) (s₁ : Fin p.l → Rq)
    (S : Fin p.l × Fin ringDegree → Finset Coeff) (A : Fin p.k → Fin p.l → Rq) (v : BucketVec p) :
    ∑ t, ZMod.countCoeff M p.omega t *
        ZMod.maskDiff (keyMap (k := p.k) s₁) (boxMasks S) matAct 0
          (fun τ (v : CoeffIndex p → Fin (bucketCount p)) ic => signerCells G sk₀ cTilde t τ ic (v ic)) A v =
      (((#(boxMasks S) : ℝ)⁻¹ * #((Fintype.piFinset S).filter fun z =>
          matAct (k := p.k) (maskOf z) A ∈ acceptSet p.gamma2 p.beta p.omega
            (cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde)
            (ct0Shift (concreteWithSampleInBall p G) (keyOf sk₀ (keyMap s₁ A)) cTilde) fun x => (v x).val) -
        (Fintype.card (CoeffIndex p → Coeff) : ℝ)⁻¹ * #(univ.filter fun w : CoeffIndex p → Coeff =>
          w ∈ acceptSet p.gamma2 p.beta p.omega (cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde)
            (ct0Shift (concreteWithSampleInBall p G) (keyOf sk₀ (keyMap s₁ A)) cTilde)
            fun x => (v x).val) : ℝ) : ℂ) := by
  set a := cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde
  set b := ct0Shift (concreteWithSampleInBall p G) (keyOf sk₀ (keyMap s₁ A)) cTilde
  set v' : CoeffIndex p → ℕ := fun x => (v x).val
  have hind := fun w => indicator_acceptSet_eq p.gamma2 p.beta p.omega hω hN a b v' w
  have hcell : ∀ (t : ZMod M) (w : CoeffIndex p → Coeff), ∏ ic, signerCells G sk₀ cTilde t (keyMap s₁ A) ic (v ic) (w ic) =
      ∏ ic, acceptCell p.gamma2 p.beta a b t ic (v' ic) (w ic) := fun t w => rfl
  have hexp : ∀ w : CoeffIndex p → Coeff,
      ∑ t, ZMod.countCoeff M p.omega t *
        ∏ ic, signerCells G sk₀ cTilde t (keyMap s₁ A) ic (v ic) (w ic) =
      if w ∈ acceptSet p.gamma2 p.beta p.omega a b v' then 1 else 0 := fun w => by
    simp_rw [hcell]
    exact (hind w).symm
  have hinj : Set.InjOn maskOf (Fintype.piFinset S : Set (Fin p.l × Fin ringDegree → Coeff)) :=
    fun c _ c' _ h => maskOf_injective h
  have hcardq : ((modulus : ℕ) : ℂ) ^ Fintype.card (CoeffIndex p) =
      (Fintype.card (CoeffIndex p → Coeff) : ℂ) := by
    rw [Fintype.card_fun, ZMod.card]; push_cast; rfl
  simp only [ZMod.maskDiff, mul_sub, Finset.sum_sub_distrib, sub_zero]
  have e1 : ∑ t, ZMod.countCoeff M p.omega t *
      ((#(boxMasks S) : ℂ)⁻¹ * ∑ z ∈ boxMasks S, ∏ ic,
        signerCells G sk₀ cTilde t (keyMap s₁ A) ic (v ic) (matAct z A ic)) =
      (#(boxMasks S) : ℂ)⁻¹ * #((Fintype.piFinset S).filter fun z =>
          matAct (k := p.k) (maskOf z) A ∈ acceptSet p.gamma2 p.beta p.omega a b v') := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ z ∈ boxMasks S, ∑ t, ZMod.countCoeff M p.omega t *
        ((#(boxMasks S) : ℂ)⁻¹ * ∏ ic, signerCells G sk₀ cTilde t (keyMap s₁ A) ic (v ic)
          (matAct z A ic)) = (#(boxMasks S) : ℂ)⁻¹ *
        (if matAct z A ∈ acceptSet p.gamma2 p.beta p.omega a b v' then 1 else 0) := by
      intro z _
      rw [← hexp]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, boxMasks, Finset.sum_image hinj,
      Finset.sum_boole]
  have e2 : ∑ t, ZMod.countCoeff M p.omega t *
      ((((modulus : ℕ) : ℂ) ^ Fintype.card (CoeffIndex p))⁻¹ * ∑ u : CoeffIndex p → Coeff, ∏ ic,
        signerCells G sk₀ cTilde t (keyMap s₁ A) ic (v ic) (u ic)) =
      (Fintype.card (CoeffIndex p → Coeff) : ℂ)⁻¹ * #(univ.filter fun w : CoeffIndex p → Coeff =>
          w ∈ acceptSet p.gamma2 p.beta p.omega a b v') := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ u : CoeffIndex p → Coeff, ∑ t, ZMod.countCoeff M
        p.omega t * ((((modulus : ℕ) : ℂ) ^ Fintype.card (CoeffIndex p))⁻¹ *
          ∏ ic, signerCells G sk₀ cTilde t (keyMap s₁ A) ic (v ic) (u ic)) =
        (((modulus : ℕ) : ℂ) ^ Fintype.card (CoeffIndex p))⁻¹ *
          (if u ∈ acceptSet p.gamma2 p.beta p.omega a b v' then 1 else 0) := by
      intro u
      rw [← hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, Finset.sum_boole, hcardq]
  rw [e1, e2]
  push_cast
  ring

omit [NeZero (bucketCount p)] nttOps in
theorem card_zBox (hp : SigningParams p) {v : RqVec p.l} (hv : polyVecNorm v ≤ p.beta)
    (bc : Fin p.l × Fin ringDegree) : #(zBox p v bc) = 2 * (p.gamma1 - p.beta) - 1 := by
  refine box_shift_card hp.gamma1_beta_lt ?_
  have := GordieHowe.MLDSA44.natAbs_centeredRepr_le_polyVecNorm v bc.1 bc.2
  rw [abs_le]; omega

theorem card_piFinset_zBox (hp : SigningParams p) {v : RqVec p.l} (hv : polyVecNorm v ≤ p.beta) :
    #(Fintype.piFinset (zBox p v)) = (2 * (p.gamma1 - p.beta) - 1) ^ (ringDegree * p.l) := by
  rw [Fintype.card_piFinset, Finset.prod_congr rfl fun bc _ => card_zBox hp hv bc,
    Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    mul_comm p.l]

theorem toReal_zAcceptFraction_eq [Nonempty (MaskBox p)] (hp : SigningParams p) {v : RqVec p.l}
    (hv : polyVecNorm v ≤ p.beta) :
    (zAcceptFraction p).toReal =
      #(Fintype.piFinset (zBox p v)) / (Fintype.card (MaskBox p) : ℝ) := by
  have hβ := hp.beta_lt_gamma1
  rw [zAcceptFraction, ENNReal.toReal_ofReal (by positivity), card_piFinset_zBox hp hv,
    card_maskBox hp.two_gamma1_lt, div_pow]
  push_cast
  rfl

open Classical in
/-- **The real-minus-stand-in column as a combination of mask differences**: for the key
`sk = keyOf sk₀ (A s₁)` with `A = NTT⁻¹(Â)`,
`|realMass v c - ρ_z standinMass v c| = ρ_z · ‖∑_t c_t D_t(A)(v)‖`. -/
theorem abs_realMass_sub_standinMass_eq [NTTRingLaws nttOps] [Nonempty (MaskBox p)]
    [Nonempty (CoeffIndex p)] (hp : SigningParams p)
    (hω : p.omega < M)
    (hN : Fintype.card (CoeffIndex p) < M) (sk₀ : SecretKey p)
    (cTilde : CommitHashBytes p)
    (hs1 : polyVecNorm ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) ≤ p.beta)
    (aHat : TqMatrix p.k p.l) (v : BucketVec p) :
    |(realMass (concreteWithSampleInBall p G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat)))
        aHat v cTilde).toReal -
      (zAcceptFraction p * standinMass (concreteWithSampleInBall p G)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal| =
      (zAcceptFraction p).toReal * ‖∑ t, ZMod.countCoeff M p.omega t *
        ZMod.maskDiff (keyMap (k := p.k) (fun b => sk₀.s1.get b))
          (boxMasks (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1))) matAct 0
          (fun τ (v : CoeffIndex p → Fin (bucketCount p)) ic => signerCells G sk₀ cTilde t τ ic (v ic))
          (matOfHat aHat) v‖ := by
  set A := matOfHat aHat
  set sk := keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) A)
  set B := Fintype.piFinset (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1))
  rw [sum_countCoeff_maskDiff_eq hω hN, Complex.norm_real, Real.norm_eq_abs]
  have hcs2 : cs2Shift (concreteWithSampleInBall p G) sk cTilde = cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde :=
    rfl
  have hreal := toReal_realMass_eq hp sk aHat cTilde hs1 v
  rw [hcs2] at hreal
  have hstand := toReal_standinMass_eq (G := G) hp sk cTilde v
  rw [hcs2] at hstand
  have hcardZ : #(boxMasks (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1))) = #B :=
    Finset.card_image_of_injective _ maskOf_injective
  have hρ := toReal_zAcceptFraction_eq hp hs1
  have hB0 : (0 : ℝ) < #B := by
    rw [card_piFinset_zBox hp hs1]
    have := hp.beta_lt_gamma1
    exact_mod_cast pow_pos (by omega) _
  rw [ENNReal.toReal_mul, hreal, hstand, hcardZ, hρ]
  have hM : (0 : ℝ) < Fintype.card (MaskBox p) := Nat.cast_pos.mpr Fintype.card_pos
  set X : ℝ := ((#(B.filter fun z => matAct (k := p.k) (maskOf z) A ∈ acceptSet p.gamma2 p.beta
    p.omega (cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde) (ct0Shift (concreteWithSampleInBall p G) sk cTilde)
    fun x => (v x).val) : ℕ) : ℝ)
  set Y : ℝ := ((#(univ.filter fun w : CoeffIndex p → Coeff => w ∈ acceptSet p.gamma2 p.beta p.omega
    (cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde) (ct0Shift (concreteWithSampleInBall p G) sk cTilde)
    fun x => (v x).val) : ℕ) : ℝ)
  change |(Fintype.card (MaskBox p) : ℝ)⁻¹ * X - #B / Fintype.card (MaskBox p) *
    ((Fintype.card (CoeffIndex p → Coeff) : ℝ)⁻¹ * Y)| =
    #B / Fintype.card (MaskBox p) * |(#B : ℝ)⁻¹ * X - (Fintype.card (CoeffIndex p → Coeff) : ℝ)⁻¹ * Y|
  rw [show (Fintype.card (MaskBox p) : ℝ)⁻¹ * X - #B / Fintype.card (MaskBox p) *
      ((Fintype.card (CoeffIndex p → Coeff) : ℝ)⁻¹ * Y) =
      #B / Fintype.card (MaskBox p) * ((#B : ℝ)⁻¹ * X -
        (Fintype.card (CoeffIndex p → Coeff) : ℝ)⁻¹ * Y) by field_simp,
    abs_mul, abs_of_nonneg (by positivity)]

theorem matOfHat_bijective [hl : NTTRingLaws nttOps] {k l : ℕ} :
    Function.Bijective (matOfHat (k := k) (l := l)) := by
  refine ⟨fun a a' h => ?_, fun A => ⟨Vector.ofFn fun i => Vector.ofFn fun b => nttOps.toHat (A i b),
    ?_⟩⟩
  · apply Vector.ext
    intro i hi
    apply Vector.ext
    intro b hb
    have := congrFun (congrFun h ⟨i, hi⟩) ⟨b, hb⟩
    simp only [matOfHat] at this
    have h2 := congrArg nttOps.toHat this
    rw [hl.toHat_fromHat, hl.toHat_fromHat] at h2
    simpa [Vector.get_eq_getElem] using h2
  · funext i b
    simp only [matOfHat, Vector.get_ofFn, hl.fromHat_toHat]

open Classical in
/-- **The signer's column error averaged over the matrix.** For every challenge `c̃` with
`‖c s₁‖∞ ≤ β`, and a bound `Env` on the averaged second moments of the signer's cell kernels,
`∑_Â ∑_v |realMass v c̃ - ρ_z standinMass v c̃| ≤ |T_q^{k×ℓ}| · ρ_z · Λ · (m L/q)^(256k) · √Env`,
for the keys `keyOf sk₀ (A s₁)` whose `t₀` is recomputed from the matrix. -/
theorem sum_abs_realMass_sub_le [NTTRingLaws nttOps] [Nonempty (MaskBox p)]
    [Nonempty (CoeffIndex p)] (hp : SigningParams p)
    (hω : p.omega < M)
    (hN : Fintype.card (CoeffIndex p) < M) (sk₀ : SecretKey p)
    (cTilde : CommitHashBytes p)
    (hs1 : polyVecNorm ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) ≤ p.beta)
    {L : ℝ} (hL : 0 < L) {Env : ℝ} (hEnv0 : 0 ≤ Env)
    (hEnv : ∀ (t : ZMod M) τ, averagedSecondMoment maskSlotEquiv
      (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1)) slotRoot
      (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) L)
      (keySlot (fun b => sk₀.s1.get b)) 0 ≤ Env) :
    ∑ aHat : TqMatrix p.k p.l, ∑ v : BucketVec p,
        |(realMass (concreteWithSampleInBall p G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction p * standinMass (concreteWithSampleInBall p G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal| ≤
      Fintype.card (TqMatrix p.k p.l) * ((zAcceptFraction p).toReal *
        (∑ t, ‖ZMod.countCoeff M p.omega t‖) *
        ((bucketCount p * L / modulus) ^ (p.k * ringDegree) * √Env)) := by
  set cs1 := (concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1
  set ρ := (zAcceptFraction p).toReal
  have hρ : 0 ≤ ρ := ENNReal.toReal_nonneg
  set F : (Fin p.k → Fin p.l → Rq) → BucketVec p → ℂ := fun A v =>
    ∑ t, ZMod.countCoeff M p.omega t *
      ZMod.maskDiff (keyMap (k := p.k) (fun b => sk₀.s1.get b)) (boxMasks (zBox p cs1)) matAct 0
        (fun τ (v : CoeffIndex p → Fin (bucketCount p)) ic => signerCells G sk₀ cTilde t τ ic (v ic)) A v
  have hS : (Fintype.piFinset (zBox p cs1)).Nonempty := by
    rw [← Finset.card_pos, card_piFinset_zBox hp hs1]
    have := hp.beta_lt_gamma1
    exact pow_pos (by omega) _
  have hbound := sum_norm_regularity_le (k := p.k) (m := bucketCount p) (fun b => sk₀.s1.get b)
    (zBox p cs1) hS (ZMod.countCoeff M p.omega)
    (fun t τ ic r => signerCells G sk₀ cTilde t τ ic r) hL 0 hEnv0 hEnv
  have hcard : Fintype.card (Fin p.k → Fin p.l → Rq) = Fintype.card (TqMatrix p.k p.l) :=
    (Fintype.card_of_bijective matOfHat_bijective).symm
  calc ∑ aHat : TqMatrix p.k p.l, ∑ v : BucketVec p, |(realMass (concreteWithSampleInBall p G)
          (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat v cTilde).toReal -
        (zAcceptFraction p * standinMass (concreteWithSampleInBall p G)
          (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal|
      = ρ * ∑ aHat : TqMatrix p.k p.l, ∑ v, ‖F (matOfHat aHat) v‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun aHat _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ =>
          abs_realMass_sub_standinMass_eq hp hω hN sk₀ cTilde hs1 aHat v
    _ = ρ * ∑ A, ∑ v, ‖F A v‖ := by
        congr 1
        exact Fintype.sum_bijective _ matOfHat_bijective _ _ fun _ => rfl
    _ ≤ ρ * (Fintype.card (Fin p.k → Fin p.l → Rq) *
          (∑ t, ‖ZMod.countCoeff M p.omega t‖) *
          ((bucketCount p * L / modulus) ^ (p.k * ringDegree) * √Env)) :=
        mul_le_mul_of_nonneg_left hbound hρ
    _ = _ := by rw [hcard]; ring

open Classical in
/-- **The signer's column error averaged over the matrix, `ℓ²` form.** Under the hypotheses of
`sum_abs_realMass_sub_le`,
`∑_Â (∑_v |realMass v c̃ - ρ_z standinMass v c̃|)²
  ≤ |T_q^{k×ℓ}| · (ρ_z · Λ · (m L/q)^(256k) · √Env)²`,
for the keys `keyOf sk₀ (A s₁)` whose `t₀` is recomputed from the matrix. -/
theorem sum_sq_sum_abs_realMass_sub_le [NTTRingLaws nttOps] [Nonempty (MaskBox p)]
    [Nonempty (CoeffIndex p)] (hp : SigningParams p)
    (hω : p.omega < M)
    (hN : Fintype.card (CoeffIndex p) < M) (sk₀ : SecretKey p)
    (cTilde : CommitHashBytes p)
    (hs1 : polyVecNorm ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) ≤ p.beta)
    {L : ℝ} (hL : 0 < L) {Env : ℝ} (hEnv0 : 0 ≤ Env)
    (hEnv : ∀ (t : ZMod M) τ, averagedSecondMoment maskSlotEquiv
      (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1)) slotRoot
      (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) L)
      (keySlot (fun b => sk₀.s1.get b)) 0 ≤ Env) :
    ∑ aHat : TqMatrix p.k p.l, (∑ v : BucketVec p,
        |(realMass (concreteWithSampleInBall p G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction p * standinMass (concreteWithSampleInBall p G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal|) ^ 2 ≤
      Fintype.card (TqMatrix p.k p.l) * ((zAcceptFraction p).toReal *
        (∑ t, ‖ZMod.countCoeff M p.omega t‖) *
        ((bucketCount p * L / modulus) ^ (p.k * ringDegree) * √Env)) ^ 2 := by
  set cs1 := (concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1
  set ρ := (zAcceptFraction p).toReal
  set F : (Fin p.k → Fin p.l → Rq) → BucketVec p → ℂ := fun A v =>
    ∑ t, ZMod.countCoeff M p.omega t *
      ZMod.maskDiff (keyMap (k := p.k) (fun b => sk₀.s1.get b)) (boxMasks (zBox p cs1)) matAct 0
        (fun τ (v : CoeffIndex p → Fin (bucketCount p)) ic => signerCells G sk₀ cTilde t τ ic (v ic)) A v
  have hS : (Fintype.piFinset (zBox p cs1)).Nonempty := by
    rw [← Finset.card_pos, card_piFinset_zBox hp hs1]
    have := hp.beta_lt_gamma1
    exact pow_pos (by omega) _
  have hbound := sum_sq_norm_regularity_le (k := p.k) (m := bucketCount p)
    (fun b => sk₀.s1.get b) (zBox p cs1) hS (ZMod.countCoeff M p.omega)
    (fun t τ ic r => signerCells G sk₀ cTilde t τ ic r) hL 0 hEnv0 hEnv
  have hcard : Fintype.card (Fin p.k → Fin p.l → Rq) = Fintype.card (TqMatrix p.k p.l) :=
    (Fintype.card_of_bijective matOfHat_bijective).symm
  calc ∑ aHat : TqMatrix p.k p.l, (∑ v : BucketVec p, |(realMass (concreteWithSampleInBall p G)
          (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat v cTilde).toReal -
        (zAcceptFraction p * standinMass (concreteWithSampleInBall p G)
          (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal|) ^ 2
      = ρ ^ 2 * ∑ aHat : TqMatrix p.k p.l, (∑ v, ‖F (matOfHat aHat) v‖) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun aHat _ => ?_
        rw [← mul_pow, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun v _ =>
          abs_realMass_sub_standinMass_eq hp hω hN sk₀ cTilde hs1 aHat v
    _ = ρ ^ 2 * ∑ A, (∑ v, ‖F A v‖) ^ 2 := by
        congr 1
        exact Fintype.sum_bijective _ matOfHat_bijective _ _ fun _ => rfl
    _ ≤ ρ ^ 2 * (Fintype.card (Fin p.k → Fin p.l → Rq) *
          ((∑ t, ‖ZMod.countCoeff M p.omega t‖) *
          ((bucketCount p * L / modulus) ^ (p.k * ringDegree) * √Env)) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = _ := by rw [hcard]; ring

/-! ### The averaged second moment of the signer's cells -/

/-- The cell size `L = 2(γ₂ - β) - 1` as a real number. -/
noncomputable def cellSize (p : Params) : ℝ := ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ)

omit [NeZero (bucketCount p)] nttOps in
theorem cellSize_pos (hp : SigningParams p) : 0 < cellSize p := by
  have := hp.beta_lt_gamma2
  unfold cellSize
  exact_mod_cast (show 0 < 2 * (p.gamma2 - p.beta) - 1 by omega)

/-- **The kernel bounds of the signer's cells**, for `|c s₂| ≤ β` coefficientwise, with the
hint-split kernel `f = hintKernel (q/L)` and any `S₁ ≥ ∑ f`, `S₁ ≥ 1`. -/
theorem kernelBounds_signerCells [Nonempty (CoeffIndex p)] (hp : SigningParams p) (sk₀ : SecretKey p)
    (cTilde : CommitHashBytes p)
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde x| ≤ p.beta)
    (t : ZMod M) (τ : Fin p.k → Rq) {S₁ : ℝ} (hS₁ : 1 ≤ S₁)
    (hfS : ∑ a : Coeff, hintKernel ((modulus : ℝ) / cellSize p) a ≤ S₁) :
    KernelBounds (F := Coeff)
      (fun i c => normKernel (fun r => signerCells G sk₀ cTilde t τ (i, c) r) (cellSize p))
      (fun i c => normWeight (fun r => signerCells G sk₀ cTilde t τ (i, c) r) (cellSize p))
      (hintKernel ((modulus : ℝ) / cellSize p)) S₁
      ((modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount p)) * cellSize p ^ 2)) := by
  have hL := cellSize_pos hp
  have hN : (0 : ℝ) < modulus := by norm_num [modulus]
  have hC : (0 : ℝ) ≤ (modulus : ℝ) / cellSize p := by positivity
  refine kernelBounds_of_cells (fun i c => fun r => signerCells G sk₀ cTilde t τ (i, c) r) hL
    (hintKernel_nonneg hC) (hintKernel_le_one _) hS₁ hfS ?_ ?_ ?_
  · intro i c r r' x h
    exact acceptCell_disjoint p.gamma2 p.beta _ _ t (i, c) (fun h' => h (Fin.ext h')) x
  · intro i c r
    refine (sum_norm_acceptCell_sq_le p.gamma2 p.beta _ _ t (i, c) r.val).trans (le_of_eq ?_)
    unfold cellSize
    have hr : r.val < (modulus - 1) / (2 * p.gamma2) := r.isLt
    rw [card_rejectionBucket' hp.gamma2_pos hp.gamma2_dvd hr (ha (i, c))]
  · intro i c r a
    have hr : r.val < (modulus - 1) / (2 * p.gamma2) := r.isLt
    exact norm_fourierCoeff_acceptCell_le hp.gamma2_pos hp.gamma2_dvd hp.two_buckets hr
      hp.beta_lt_gamma2 _ _ t (i, c) (ha (i, c)) a

/-- `hintKernel (q/L)` is a kernel bound in the sense of the spectral recursion. -/
theorem isKernelBound_hintKernel (hp : SigningParams p) :
    IsKernelBound ((modulus : ℝ) / cellSize p) (hintKernel (N := modulus) ((modulus : ℝ) / cellSize p)) where
  nonneg := hintKernel_nonneg (by have := cellSize_pos hp; positivity)
  le_one := hintKernel_le_one _
  mul_abs_valMinAbs_le x hx := hintKernel_mul_abs_le hx

open Classical in
/-- **The averaged second moment of the signer's cells**, closed by the second-moment bound with
the small supports of the spectral recursion: for `L ≥ 190307` it is at most
`∑_t C(256, t) supportTerm t` with `G = 2(γ₁ - β) - 1`, `m = bucketCount`, `T₂ = q² / (m L²)`. -/
theorem averagedSecondMoment_signerCells_le [Nonempty (CoeffIndex p)] (hp : SigningParams p)
    (sk₀ : SecretKey p) (cTilde : CommitHashBytes p)
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde x| ≤ p.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) ≤ p.beta)
    (t : ZMod M) (τ : Fin p.k → Rq) {S₁ : ℝ} (hS₁ : 1 ≤ S₁)
    (hfS : ∑ a : Coeff, hintKernel ((modulus : ℝ) / cellSize p) a ≤ S₁)
    (hL₀ : 190307 ≤ cellSize p) :
    averagedSecondMoment maskSlotEquiv
        (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize p))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤
      ∑ t ∈ range (ringDegree + 1), (ringDegree.choose t : ℝ) *
        (if t = 0 then 0 else supportTerm ringDegree p.k p.l (2 * (p.gamma1 - p.beta) - 1) 4
          smallSupportDelta S₁
          ((modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount p)) * cellSize p ^ 2)) t) := by
  have hβ := hp.beta_lt_gamma1
  have hL := cellSize_pos hp
  have hC : (modulus : ℝ) / cellSize p ≤ 8380417 / 190307 := by
    rw [show (modulus : ℝ) = 8380417 by norm_num [modulus]]
    gcongr
  have hδ : SmallSupportBounds slotRoot (hintKernel ((modulus : ℝ) / cellSize p)) 4
      smallSupportDelta :=
    smallSupportBounds_of_isKernelBound slotRoot_injective slotRoot_pow
      (isKernelBound_hintKernel hp) hC
  exact averagedSecondMoment_le maskSlotEquiv _ (by omega) (card_zBox hp hs1) slotRoot_injective
    slotRoot_ne_zero (kernelBounds_signerCells hp sk₀ cTilde ha t τ hS₁ hfS) hδ _ 0

open Classical in
/-- **Parseval for the signer's cells**: the normalized weights satisfy `∑_a φ(a)² ≤ q / L`. -/
theorem sum_normWeight_signerCells_sq_le [Nonempty (CoeffIndex p)] (hp : SigningParams p) (sk₀ : SecretKey p)
    (cTilde : CommitHashBytes p)
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde x| ≤ p.beta)
    (t : ZMod M) (τ : Fin p.k → Rq) (i : Fin p.k) (c : Fin ringDegree) :
    ∑ a : Coeff, normWeight (fun r => signerCells G sk₀ cTilde t τ (i, c) r) (cellSize p) a ^ 2 ≤
      (modulus : ℝ) / cellSize p := by
  refine sum_normWeight_sq_le (g := fun r => signerCells G sk₀ cTilde t τ (i, c) r)
    (cellSize_pos hp) (fun r => (sum_norm_acceptCell_sq_le p.gamma2 p.beta _ _ t (i, c) r.val).trans
    (le_of_eq (by
      unfold cellSize
      have hr : r.val < (modulus - 1) / (2 * p.gamma2) := r.isLt
      rw [card_rejectionBucket' hp.gamma2_pos hp.gamma2_dvd hr (ha (i, c))])))

open Classical in
/-- **The averaged second moment of the signer's cells, hybrid form**: as
`averagedSecondMoment_signerCells_le`, with every support size `t` taking the minimum of the
small-support term and the hybrid term `hybridFactor S₁ (q/L) k G ℓ ^ t`
(`averagedSecondMoment_le_hybrid`). -/
theorem averagedSecondMoment_signerCells_le_hybrid [Nonempty (CoeffIndex p)]
    (hp : SigningParams p) (sk₀ : SecretKey p) (cTilde : CommitHashBytes p)
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde x| ≤ p.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) ≤ p.beta)
    (t : ZMod M) (τ : Fin p.k → Rq) {S₁ : ℝ} (hS₁ : 1 ≤ S₁)
    (hfS : ∑ a : Coeff, hintKernel ((modulus : ℝ) / cellSize p) a ≤ S₁)
    (hL₀ : 190307 ≤ cellSize p) :
    averagedSecondMoment maskSlotEquiv
        (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize p))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤
      ∑ t ∈ range (ringDegree + 1), (ringDegree.choose t : ℝ) *
        (if t = 0 then 0 else min (supportTerm ringDegree p.k p.l (2 * (p.gamma1 - p.beta) - 1) 4
          smallSupportDelta S₁
          ((modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount p)) * cellSize p ^ 2)) t)
          (hybridFactor S₁ ((modulus : ℝ) / cellSize p) p.k (2 * (p.gamma1 - p.beta) - 1)
            p.l ^ t)) := by
  have hβ := hp.beta_lt_gamma1
  have hL := cellSize_pos hp
  have hC : (modulus : ℝ) / cellSize p ≤ 8380417 / 190307 := by
    rw [show (modulus : ℝ) = 8380417 by norm_num [modulus]]
    gcongr
  have hδ : SmallSupportBounds slotRoot (hintKernel ((modulus : ℝ) / cellSize p)) 4
      smallSupportDelta :=
    smallSupportBounds_of_isKernelBound slotRoot_injective slotRoot_pow
      (isKernelBound_hintKernel hp) hC
  have hq : (0 : ℝ) ≤ (modulus : ℝ) / cellSize p := by
    have : (0 : ℝ) < modulus := by norm_num [modulus]
    positivity
  exact averagedSecondMoment_le_hybrid maskSlotEquiv _ (by omega) (card_zBox hp hs1)
    slotRoot_injective slotRoot_ne_zero (kernelBounds_signerCells hp sk₀ cTilde ha t τ hS₁ hfS)
    hq (fun i c => sum_normWeight_signerCells_sq_le hp sk₀ cTilde ha t τ i c) hδ _ 0

/-- `ringRegGap` with the mean member weights bounded below by `μ > 0`. -/
theorem ringRegGap_le [Nonempty (MaskBox p)] (hp : SigningParams p) (prims : Primitives p)
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {μ : ℝ} (hμ : 0 < μ)
    (hmw : ∀ v, μ ≤ 𝔼 c, (memberWeight prims βmin sk.t0 (v, c) : ℝ≥0∞).toReal) :
    ringRegGap prims sk aHat βmin ≤
      (∑ v, 𝔼 c, |(realMass prims sk aHat v c).toReal -
          (zAcceptFraction p * standinMass prims sk v c).toReal|) /
        (μ * ((standinScale p * βmin).toReal * Fintype.card (BucketVec p))) := by
  have hden : 0 < (standinScale p * βmin).toReal * Fintype.card (BucketVec p) :=
    mul_pos (ringLevel_pos hp hβ0 hβt) (by exact_mod_cast Fintype.card_pos)
  unfold ringRegGap
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun v _ =>
    div_le_div_of_nonneg_left (Finset.expect_nonneg fun _ _ => abs_nonneg _) hμ (hmw v))
      hden.le).trans (le_of_eq ?_)
  rw [← Finset.sum_div, div_div]

/-- **Zero mean member weights give a zero regularity gap**: if the mean member weight of every
bucket vector is `0`, `ringRegGap = 0` (each column is `x / 0 = 0`). -/
theorem ringRegGap_eq_zero (prims : Primitives p) [Nonempty (MaskBox p)] (sk : SecretKey p)
    (aHat : TqMatrix p.k p.l) {βmin : ℚ≥0}
    (h : ∀ v, 𝔼 c, (memberWeight prims βmin sk.t0 (v, c) : ℝ≥0∞).toReal = 0) :
    ringRegGap prims sk aHat βmin = 0 := by
  unfold ringRegGap
  simp [h]

/-- **The mean regularity gap by Cauchy–Schwarz over the matrix, with a weight that may
vanish.** As `expect_ringRegGap_le_sqrt`, for a lower bound `w Â ≥ 0` on the mean member weights
of every bucket vector such that `w Â = 0` only when every mean member weight of `Â` is `0`:
`𝔼_Â ringRegGap ≤ R / β_min · √(𝔼_Â (w Â)⁻²)`, with `0⁻¹ = 0`. -/
theorem expect_ringRegGap_le_sqrt_of_nonneg [Nonempty (MaskBox p)] (hp : SigningParams p)
    (prims : Primitives p) (sk : TqMatrix p.k p.l → SecretKey p) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {w : TqMatrix p.k p.l → ℝ} (hw0 : ∀ aHat, 0 ≤ w aHat)
    (hw : ∀ aHat v, w aHat ≤ 𝔼 c, (memberWeight prims βmin (sk aHat).t0 (v, c) : ℝ≥0∞).toReal)
    (hzero : ∀ aHat, w aHat = 0 → ∀ v,
      𝔼 c, (memberWeight prims βmin (sk aHat).t0 (v, c) : ℝ≥0∞).toReal = 0)
    {R : ℝ} (hR : 0 ≤ R)
    (hnum : 𝔼 aHat, (∑ v, 𝔼 c, |(realMass prims (sk aHat) aHat v c).toReal -
        (zAcceptFraction p * standinMass prims (sk aHat) v c).toReal|) ^ 2 ≤
      ((standinScale p).toReal * Fintype.card (BucketVec p) * R) ^ 2) :
    𝔼 aHat, ringRegGap prims (sk aHat) aHat βmin ≤
      R / (βmin : ℝ≥0∞).toReal * √(𝔼 aHat, (w aHat ^ 2)⁻¹) := by
  set K := (standinScale p).toReal
  set V : ℝ := ((Fintype.card (BucketVec p) : ℕ) : ℝ)
  have hK : 0 < K := standinScale_pos hp
  have hV : 0 < V := Nat.cast_pos.mpr Fintype.card_pos
  have hβ : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  set N : TqMatrix p.k p.l → ℝ := fun aHat => ∑ v, 𝔼 c,
    |(realMass prims (sk aHat) aHat v c).toReal -
      (zAcceptFraction p * standinMass prims (sk aHat) v c).toReal|
  have hstep : ∀ aHat, ringRegGap prims (sk aHat) aHat βmin ≤
      N aHat * (w aHat)⁻¹ / (K * (βmin : ℝ≥0∞).toReal * V) := fun aHat => by
    rcases (hw0 aHat).eq_or_lt with h | h
    · rw [ringRegGap_eq_zero prims (sk aHat) aHat (hzero aHat h.symm), ← h, inv_zero, mul_zero,
        zero_div]
    refine (ringRegGap_le hp prims (sk aHat) aHat hβ0 hβt h (hw aHat)).trans_eq ?_
    have := h.ne'
    have hK' : (standinScale p).toReal ≠ 0 := hK.ne'
    rw [ENNReal.toReal_mul]
    simp only [K, V, N]
    field_simp
  have hNs : √(𝔼 aHat, N aHat ^ 2) ≤ K * V * R := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ K * V * R)]
    exact Real.sqrt_le_sqrt hnum
  have hS : 0 ≤ √(𝔼 aHat, (w aHat ^ 2)⁻¹) := Real.sqrt_nonneg _
  calc 𝔼 aHat, ringRegGap prims (sk aHat) aHat βmin
      ≤ 𝔼 aHat, N aHat * (w aHat)⁻¹ / (K * (βmin : ℝ≥0∞).toReal * V) :=
        Finset.expect_le_expect fun aHat _ => hstep aHat
    _ = (𝔼 aHat, N aHat * (w aHat)⁻¹) / (K * (βmin : ℝ≥0∞).toReal * V) :=
      (Finset.expect_div _ _ _).symm
    _ ≤ (√(𝔼 aHat, N aHat ^ 2) * √(𝔼 aHat, (w aHat)⁻¹ ^ 2)) / (K * (βmin : ℝ≥0∞).toReal * V) :=
        div_le_div_of_nonneg_right (Real.expect_mul_le_sqrt_mul_sqrt _ _ _) (by positivity)
    _ ≤ (K * V * R * √(𝔼 aHat, (w aHat ^ 2)⁻¹)) / (K * (βmin : ℝ≥0∞).toReal * V) := by
        simp_rw [inv_pow]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hNs hS) (by positivity)
    _ = R / (βmin : ℝ≥0∞).toReal * √(𝔼 aHat, (w aHat ^ 2)⁻¹) := by
        field_simp

/-- **The mean regularity gap by Cauchy–Schwarz over the matrix.** For keys `sk Â`, a positive
lower bound `w Â` on the mean member weights of every bucket vector, and the `ℓ²` numerator bound
`𝔼_Â (∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| R)²` with `K = standinScale`,
`𝔼_Â ringRegGap ≤ R / β_min · √(𝔼_Â (w Â)⁻²)` (`expect_ringRegGap_le_sqrt_of_nonneg`). -/
theorem expect_ringRegGap_le_sqrt [Nonempty (MaskBox p)] (hp : SigningParams p)
    (prims : Primitives p) (sk : TqMatrix p.k p.l → SecretKey p) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {w : TqMatrix p.k p.l → ℝ} (hw0 : ∀ aHat, 0 < w aHat)
    (hw : ∀ aHat v, w aHat ≤ 𝔼 c, (memberWeight prims βmin (sk aHat).t0 (v, c) : ℝ≥0∞).toReal)
    {R : ℝ} (hR : 0 ≤ R)
    (hnum : 𝔼 aHat, (∑ v, 𝔼 c, |(realMass prims (sk aHat) aHat v c).toReal -
        (zAcceptFraction p * standinMass prims (sk aHat) v c).toReal|) ^ 2 ≤
      ((standinScale p).toReal * Fintype.card (BucketVec p) * R) ^ 2) :
    𝔼 aHat, ringRegGap prims (sk aHat) aHat βmin ≤
      R / (βmin : ℝ≥0∞).toReal * √(𝔼 aHat, (w aHat ^ 2)⁻¹) :=
  expect_ringRegGap_le_sqrt_of_nonneg hp prims sk hβ0 hβt (fun aHat => (hw0 aHat).le) hw
    (fun aHat h => absurd h (hw0 aHat).ne') hR hnum

end GordieHowe.MLDSA.Regularity
