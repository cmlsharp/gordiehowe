-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.T0Law
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# Collisions of the commitment under a uniform matrix

The signer's commitment is `w₁ = HighBits(Â y)` for a mask `y` uniform on the mask box
(`realBuckets`, `maskUniform`). Its collision probability at the matrix `Â` is
`CP(Â) = ∑_v Pr_y[HighBits(Â y) = v]² = Pr_{y, y'}[HighBits(Â y) = HighBits(Â y')]`
(`commitCollision`, `commitCollision_eq`).

**The bound** (`expect_commitCollision_le`): for a uniform matrix,
`𝔼_Â CP(Â) ≤ (((4γ₂ + 1)/q)^k + (2γ₁)^(-ℓ))^256` (`commitCollisionBound`).

* Two coefficients in one `HighBits` bucket (FIPS 204 Algorithm 37) differ by at most `2γ₂`
  (`natAbs_centeredRepr_sub_le_of_highBitsCoeff_eq`): the low parts lie in `[-γ₂, γ₂]`.
* Fix masks `y, y'` and `d = y - y'`, with `Z(d)` the slots at which every component of `d`
  vanishes (`zeroSlots`). The top `256 - #Z(d)` coefficients of every row of `A d`,
  `A = NTT⁻¹(Â)`, are uniform (`expect_topCoeffs`), and `A d = A y - A y'`; a collision puts each
  of them in the `4γ₂ + 1` residues of centered absolute value at most `2γ₂`. So
  `Pr_Â[collision] ≤ ((4γ₂ + 1)/q)^(k (256 - #Z(d)))` (`expect_bucketsOf_eq_le`).
* For a fixed `y'` and every set `D` of slots, `Pr_y[D ⊆ Z(y - y')] ≤ (2γ₁)^(-ℓ #D)`
  (`expect_subset_zeroSlots_sub_le`): the low `#D` coefficients of each component of `y - y'`
  are determined by the others (`eq_zero_of_low_of_vanishing`,
  `expect_vanishing_le_of_forall_injective`). The key average of `(1 + x)^#Z`
  (`GordieHowe.expect_one_add_pow_card_le`) gives the bound.

`commitCollisionBound_le_mldsa44`, `_mldsa65`, `_mldsa87`: at every approved parameter set the
bound is at most `(2^-17)^256 = 2^-4352`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

/-! ### Left distributivity in `R_q` -/

/-- Multiplication in `R_q` distributes over addition on the right factor. -/
theorem rq_mul_add (f g h : Rq) : f * (g + h) = f * g + f * h := by
  apply quotientOfRq_injective
  have e1 : quotientOfRq (f * (g + h)) = quotientOfRq f * (quotientOfRq g + quotientOfRq h) := by
    rw [← coeffSemantics.add_sound]; exact coeffSemantics.mul_sound _ _
  have e2 : quotientOfRq (f * g + f * h) =
      quotientOfRq f * quotientOfRq g + quotientOfRq f * quotientOfRq h := by
    rw [← coeffSemantics.mul_sound, ← coeffSemantics.mul_sound]; exact coeffSemantics.add_sound _ _
  rw [e1, e2, mul_add]


/-! ### Two coefficients in one bucket -/

/-- **Two coefficients in one `HighBits` bucket differ by at most `2γ₂`**: for `2γ₂ ∣ q - 1`
and `4γ₂ < q`, if `HighBits(r) = HighBits(r')` (FIPS 204 Algorithm 37) then
`|r - r'| ≤ 2γ₂` (centered), since both low parts lie in `[-γ₂, γ₂]` (`decomposeCoeff_repr`). -/
theorem natAbs_centeredRepr_sub_le_of_highBitsCoeff_eq {γ₂ : ℕ} (hγ : 0 < γ₂)
    (hdvd : 2 * γ₂ ∣ modulus - 1) (hq : 2 * (2 * γ₂) < modulus) {r r' : Coeff}
    (h : highBitsCoeff r γ₂ = highBitsCoeff r' γ₂) :
    (centeredRepr (r - r')).natAbs ≤ 2 * γ₂ := by
  have hr := GordieHowe.MLDSA44.decomposeCoeff_repr hγ hdvd r
  have hr' := GordieHowe.MLDSA44.decomposeCoeff_repr hγ hdvd r'
  have h1 : (decomposeCoeff r γ₂).1 = (decomposeCoeff r' γ₂).1 := h
  set r1 := (decomposeCoeff r γ₂).1
  set r0 := (decomposeCoeff r γ₂).2
  set r1' := (decomposeCoeff r' γ₂).1
  set r0' := (decomposeCoeff r' γ₂).2
  have hlow : -(2 * γ₂ : ℤ) ≤ r0 - r0' ∧ r0 - r0' ≤ 2 * γ₂ := by
    rcases hr.low_mem with ⟨h2, h3⟩ | ⟨-, h2⟩ <;> rcases hr'.low_mem with ⟨h4, h5⟩ | ⟨-, h4⟩ <;>
      constructor <;> omega
  have hsub : r - r' = ((r0 - r0' : ℤ) : Coeff) := by
    have hcast : ∀ x : Coeff, ((x.val : ℤ) : Coeff) = x := fun x => by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [← hcast r, ← hcast r', ← Int.cast_sub, ZMod.intCast_eq_intCast_iff_dvd_sub]
    have hq' : ((modulus : ℕ) : ℤ) = (modulus : ℤ) := rfl
    rcases hr.val_eq with e1 | e1 <;> rcases hr'.val_eq with e2 | e2
    · exact ⟨0, by rw [e1, e2, h1]; ring⟩
    · exact ⟨1, by rw [e1, e2, h1]; ring⟩
    · exact ⟨-1, by rw [e1, e2, h1]; ring⟩
    · exact ⟨0, by rw [e1, e2, h1]; ring⟩
  rw [hsub, centeredRepr_intCast_eq_of_natAbs_le (r0 - r0') (b := 2 * γ₂) (by omega) hq]
  omega

/-- Under `SigningParams p`, `4γ₂ < q`: there are at least two buckets of width `2γ₂`. -/
theorem _root_.GordieHowe.MLDSA.SigningParams.four_gamma2_lt {p : Params} (hp : SigningParams p) :
    2 * (2 * p.gamma2) < modulus := by
  obtain ⟨M, hM⟩ := hp.gamma2_dvd
  have h2 := hp.two_buckets
  have hγ := hp.gamma2_pos
  have hq : 1 ≤ modulus := by norm_num [modulus]
  have hM2 : 2 ≤ M := by
    by_contra hlt
    interval_cases M <;> omega
  have : 2 * p.gamma2 * 2 ≤ 2 * p.gamma2 * M := Nat.mul_le_mul_left _ hM2
  omega

/-- **Equal bucket vectors differ coordinatewise by at most `2γ₂`**, under `SigningParams p`. -/
theorem natAbs_centeredRepr_sub_le_of_bucketsOf_eq {p : Params} [NeZero (bucketCount p)]
    (hp : SigningParams p) {w w' : CoeffIndex p → Coeff} (h : bucketsOf w = bucketsOf w')
    (x : CoeffIndex p) : (centeredRepr (w x - w' x)).natAbs ≤ 2 * p.gamma2 := by
  refine natAbs_centeredRepr_sub_le_of_highBitsCoeff_eq hp.gamma2_pos hp.gamma2_dvd
    hp.four_gamma2_lt ?_
  rw [← val_bucketsOf hp w x, ← val_bucketsOf hp w' x, h]

/-- **The residues of centered absolute value at most `b`** number `2b + 1` (`card_etaCoeff`), so
a uniform residue lands among them with probability `(2b + 1)/q`, for `2b < q`. -/
theorem expect_natAbs_centeredRepr_le {b : ℕ} (hb : 2 * b < modulus) :
    𝔼 r : Coeff, (if (centeredRepr r).natAbs ≤ b then 1 else 0 : ℝ) =
      ((2 * b + 1 : ℕ) : ℝ) / modulus := by
  rw [Fintype.expect_eq_sum_div_card, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_one, ZMod.card, ← card_etaCoeff hb, Fintype.card_subtype]

/-! ### The mask box coordinatewise -/

/-- The coefficients of the mask box: residues with centered representative in `(-γ₁, γ₁]`
(the range of ExpandMask, FIPS 204 Algorithm 34). -/
abbrev MaskCoeff (γ₁ : ℕ) := {a : Coeff // -(γ₁ : ℤ) < centeredRepr a ∧ centeredRepr a ≤ γ₁}

/-- `MaskCoeff γ₁` has `2γ₁` elements when `2γ₁ < q` (`card_maskCoeff`). -/
theorem card_maskCoeffSubtype {γ₁ : ℕ} (hq : 2 * γ₁ < modulus) :
    Fintype.card (MaskCoeff γ₁) = 2 * γ₁ := by
  rw [Fintype.card_subtype, card_maskCoeff hq]

/-- **The mask box is the box of its coefficients**: `MaskBox p ≃ (Fin ℓ → Fin 256 → MaskCoeff γ₁)`. -/
noncomputable def maskBoxEquiv (p : Params) :
    MaskBox p ≃ (Fin p.l → Fin ringDegree → MaskCoeff p.gamma1) where
  toFun y b c := ⟨(y.1.get b).get c, y.2 b c⟩
  invFun f := ⟨Vector.ofFn fun b => polyOf fun c => (f b c).1, fun b c => by
    simp only [Vector.get_ofFn, polyOf_get]
    exact (f b c).2⟩
  left_inv y := by
    apply Subtype.ext
    change Vector.ofFn (fun b => polyOf fun c => (y.1.get b).get c) = y.1
    simp only [polyOf_get_self]
    apply Vector.ext
    intro i hi
    simp [Vector.get_eq_getElem]
  right_inv f := by
    funext b c
    apply Subtype.ext
    simp only [Vector.get_ofFn, polyOf_get]

/-- The coefficients of `(maskBoxEquiv p).symm f`. -/
theorem maskBoxEquiv_symm_get_get (p : Params) (f : Fin p.l → Fin ringDegree → MaskCoeff p.gamma1)
    (b : Fin p.l) (c : Fin ringDegree) :
    (((maskBoxEquiv p).symm f).1.get b).get c = (f b c).1 := by
  change ((Vector.ofFn fun b => polyOf fun c => (f b c).1).get b).get c = _
  rw [Vector.get_ofFn, polyOf_get]

/-! ### Zero slots of the difference of two masks -/

/-- **A shifted box polynomial vanishes on `D` with probability at most `#A^-#D`**: as
`expect_vanishing_le_of_injective`, with an injection `ι c : A ↪ Z_q` for each coefficient. -/
theorem expect_vanishing_le_of_forall_injective {A : Type*} [Fintype A] [Nonempty A]
    {ι : Fin ringDegree → A → Coeff} (hι : ∀ c, Function.Injective (ι c))
    (D : Finset (Fin ringDegree)) :
    𝔼 f : Fin ringDegree → A,
        (if ∀ j ∈ D, ∑ c, ι c (f c) * slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) ≤
      ((Fintype.card A : ℝ)⁻¹) ^ #D := by
  classical
  have hD : #D ≤ ringDegree := by simpa using Finset.card_le_univ D
  have hinj : ∀ f g : Fin ringDegree → A,
      (∀ j ∈ D, ∑ c, ι c (f c) * slotRoot j ^ (c : ℕ) = 0) →
      (∀ j ∈ D, ∑ c, ι c (g c) * slotRoot j ^ (c : ℕ) = 0) →
      (fun c : topPositions #D => f c) = (fun c : topPositions #D => g c) → f = g := by
    intro f g hf hg hfg
    have hfg' := eq_zero_of_low_of_vanishing D (fun c => ι c (f c) - ι c (g c)) (fun c hc => by
      have := congrFun hfg ⟨c, mem_filter.2 ⟨mem_univ _, hc⟩⟩
      simp only at this
      rw [this, sub_self]) (fun j hj => by
      simp only [sub_mul, Finset.sum_sub_distrib, hf j hj, hg j hj, sub_self])
    funext c
    exact hι c (sub_eq_zero.1 (congrFun hfg' c))
  have hcard : #(univ.filter fun f : Fin ringDegree → A =>
      ∀ j ∈ D, ∑ c, ι c (f c) * slotRoot j ^ (c : ℕ) = 0) ≤
      Fintype.card A ^ (ringDegree - #D) := by
    refine (Finset.card_le_card_of_injOn (t := univ)
      (fun f : Fin ringDegree → A => fun c : topPositions #D => f c)
      (fun f _ => Finset.mem_univ _) fun f hf g hg h => hinj f g ?_ ?_ h).trans ?_
    · exact (mem_filter.1 (mem_coe.1 hf)).2
    · exact (mem_filter.1 (mem_coe.1 hg)).2
    · rw [card_univ, Fintype.card_fun, Fintype.card_coe, card_topPositions]
  have hE : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  rw [Fintype.expect_eq_sum_div_card, ← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one,
    Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [div_le_iff₀ (by positivity), inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  calc _ ≤ (Fintype.card A : ℝ) ^ (ringDegree - #D) * (Fintype.card A : ℝ) ^ #D := by
        gcongr
        exact_mod_cast hcard
    _ = (Fintype.card A : ℝ) ^ ringDegree := by rw [← pow_add, Nat.sub_add_cancel hD]

/-- **The zero slots of the difference of a uniform mask and a fixed one**: for `y` uniform on
the mask box and any `y'`, `Pr_y[D ⊆ Z(y - y')] ≤ ((2γ₁)^-ℓ)^#D`: each of the `ℓ` independent
components of `y - y'` vanishes on `D` with probability at most `(2γ₁)^-#D`
(`expect_vanishing_le_of_forall_injective`). -/
theorem expect_subset_zeroSlots_sub_le {p : Params} (hp : SigningParams p) (y' : MaskBox p)
    (D : Finset (Fin ringDegree)) :
    𝔼 y : MaskBox p, (if D ⊆ zeroSlots (fun b => y.1.get b - y'.1.get b) then 1 else 0 : ℝ) ≤
      ((((2 * p.gamma1 : ℕ) : ℝ)⁻¹) ^ p.l) ^ #D := by
  classical
  have hq := hp.two_gamma1_lt
  have hγ : 0 < p.gamma1 := by have := hp.beta_lt_gamma1; omega
  have : Nonempty (MaskCoeff p.gamma1) := by
    rw [← Fintype.card_pos_iff, card_maskCoeffSubtype hq]; omega
  have hind : ∀ f : Fin p.l → Fin ringDegree → MaskCoeff p.gamma1,
      (if D ⊆ zeroSlots (fun b => ((maskBoxEquiv p).symm f).1.get b - y'.1.get b) then 1 else 0 : ℝ) =
        ∏ b : Fin p.l, (if ∀ j ∈ D, ∑ c, ((f b c).1 - (y'.1.get b).get c) *
          slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) := by
    intro f
    rw [Finset.prod_boole]
    have hiff : D ⊆ zeroSlots (fun b => ((maskBoxEquiv p).symm f).1.get b - y'.1.get b) ↔
        ∀ b : Fin p.l, ∀ j ∈ D,
          ∑ c, ((f b c).1 - (y'.1.get b).get c) * slotRoot j ^ (c : ℕ) = 0 := by
      simp only [zeroSlots, subset_iff, mem_filter, mem_univ, true_and, slotEval, Rq.get_sub,
        maskBoxEquiv_symm_get_get]
      exact ⟨fun h b j hj => h hj b, fun h j hj b => h b j hj⟩
    simp only [mem_univ, true_implies, hiff]
  calc 𝔼 y : MaskBox p, (if D ⊆ zeroSlots (fun b => y.1.get b - y'.1.get b) then 1 else 0 : ℝ)
      = 𝔼 f : Fin p.l → Fin ringDegree → MaskCoeff p.gamma1, ∏ b : Fin p.l,
          (if ∀ j ∈ D, ∑ c, ((f b c).1 - (y'.1.get b).get c) *
            slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) := by
        refine Fintype.expect_equiv (maskBoxEquiv p) _ _ fun y => ?_
        rw [← hind, Equiv.symm_apply_apply]
    _ = ∏ b : Fin p.l, 𝔼 g : Fin ringDegree → MaskCoeff p.gamma1,
          (if ∀ j ∈ D, ∑ c, ((g c).1 - (y'.1.get b).get c) *
            slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) :=
        PMF.expect_prod_apply (fun b (g : Fin ringDegree → MaskCoeff p.gamma1) =>
          (if ∀ j ∈ D, ∑ c, ((g c).1 - (y'.1.get b).get c) *
            slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ))
    _ ≤ ∏ _b : Fin p.l, ((Fintype.card (MaskCoeff p.gamma1) : ℝ)⁻¹) ^ #D :=
        Finset.prod_le_prod₀ (fun b _ => Finset.expect_nonneg fun g _ => by split_ifs <;> norm_num)
          fun b _ => expect_vanishing_le_of_forall_injective
            (ι := fun c (a : MaskCoeff p.gamma1) => a.1 - (y'.1.get b).get c)
            (fun c a a' h => Subtype.ext (sub_left_injective h)) D
    _ = _ := by
        rw [Finset.prod_const, card_univ, Fintype.card_fin, card_maskCoeffSubtype hq, ← pow_mul,
          ← pow_mul]
        ring

/-! ### The collision probability under a uniform matrix -/

section Collision

variable {p : Params} [nttOps : NTTRingOps] [NTTRingLaws nttOps]

/-- **A collision of `HighBits(Â y)` and `HighBits(Â y')` under a uniform matrix**: with
`Z = Z(y - y')`, `Pr_Â[HighBits(Â y) = HighBits(Â y')] ≤ (((4γ₂ + 1)/q)^k)^(256 - #Z)`. The top
`256 - #Z` coefficients of every row of `A (y - y') = A y - A y'` are uniform
(`expect_topCoeffs`) and lie within `2γ₂` of zero on a collision
(`natAbs_centeredRepr_sub_le_of_bucketsOf_eq`). -/
theorem expect_bucketsOf_eq_le [NeZero (bucketCount p)] (hp : SigningParams p)
    (y y' : RqVec p.l) :
    𝔼 aHat : TqMatrix p.k p.l, (if bucketsOf (rqVecCoeffs (aHat * y)) =
        bucketsOf (rqVecCoeffs (aHat * y')) then 1 else 0 : ℝ) ≤
      ((((4 * p.gamma2 + 1 : ℕ) : ℝ) / modulus) ^ p.k) ^
        (ringDegree - #(zeroSlots fun b => y.get b - y'.get b)) := by
  classical
  set s : Fin p.l → Rq := fun b => y.get b - y'.get b
  set T := topIndex p.k #(zeroSlots s)
  set g : Coeff → ℝ := fun r => if (centeredRepr r).natAbs ≤ 2 * p.gamma2 then 1 else 0 with hg
  have hy : ∀ b, y.get b = s b + y'.get b := fun b => (sub_add_cancel (y.get b) (y'.get b)).symm
  have hpt : ∀ A : Fin p.k → Fin p.l → Rq,
      (if bucketsOf (matAct (k := p.k) (fun b => y.get b) A) =
        bucketsOf (matAct (k := p.k) (fun b => y'.get b) A) then 1 else 0 : ℝ) ≤
        ∏ x : T, g (topCoeffs s #(zeroSlots s) A x) := by
    intro A
    split_ifs with h
    · refine le_of_eq (Finset.prod_eq_one fun x _ => ?_).symm
      have hx := natAbs_centeredRepr_sub_le_of_bucketsOf_eq hp h x.1
      have he : topCoeffs s #(zeroSlots s) A x = matAct (k := p.k) (fun b => y.get b) A x.1 -
          matAct (k := p.k) (fun b => y'.get b) A x.1 := by
        have hsum : ∑ b, A x.1.1 b * y.get b =
            ∑ b, A x.1.1 b * s b + ∑ b, A x.1.1 b * y'.get b := by
          refine (Finset.sum_congr rfl fun b _ => ?_).trans Finset.sum_add_distrib
          rw [hy b]
          exact rq_mul_add _ _ _
        change (∑ b, A x.1.1 b * s b).get x.1.2 = (∑ b, A x.1.1 b * y.get b).get x.1.2 -
          (∑ b, A x.1.1 b * y'.get b).get x.1.2
        rw [hsum]
        exact eq_sub_of_add_eq (Rq.get_add _ _ _).symm
      simp only [g, he, hx, ite_true]
    · exact Finset.prod_nonneg fun x _ => by simp only [g]; split_ifs <;> norm_num
  have h4 : 2 * (2 * p.gamma2) + 1 = 4 * p.gamma2 + 1 := by ring
  calc 𝔼 aHat : TqMatrix p.k p.l, (if bucketsOf (rqVecCoeffs (aHat * y)) =
        bucketsOf (rqVecCoeffs (aHat * y')) then 1 else 0 : ℝ)
      = 𝔼 A : Fin p.k → Fin p.l → Rq, (if bucketsOf (matAct (k := p.k) (fun b => y.get b) A) =
          bucketsOf (matAct (k := p.k) (fun b => y'.get b) A) then 1 else 0 : ℝ) := by
        simp_rw [rqVecCoeffs_mul_eq_matAct]
        exact Fintype.expect_bijective _ matOfHat_bijective _ _ fun _ => rfl
    _ ≤ 𝔼 A : Fin p.k → Fin p.l → Rq, ∏ x : T, g (topCoeffs s #(zeroSlots s) A x) :=
        Finset.expect_le_expect fun A _ => hpt A
    _ = 𝔼 u : T → Coeff, ∏ x : T, g (u x) := expect_topCoeffs s (fun u => ∏ x : T, g (u x))
    _ = ∏ _x : T, 𝔼 r, g r := PMF.expect_prod_apply (fun _ => g)
    _ = _ := by
        rw [Finset.prod_const, card_univ, Fintype.card_coe, card_topIndex, hg,
          expect_natAbs_centeredRepr_le hp.four_gamma2_lt, h4, pow_mul]

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

/-- **The collision probability of the commitment** at the matrix `Â`:
`CP(Â) = ∑_v Pr_y[HighBits(Â y) = v]²` for `y` uniform on the mask box. -/
noncomputable def commitCollision (aHat : TqMatrix p.k p.l) : ℝ :=
  ∑ v, ((maskUniform p).map (realBuckets aHat) v).toReal ^ 2

omit [NTTRingLaws nttOps] in
/-- The collision probability is the probability that two independent masks collide. -/
theorem commitCollision_eq (aHat : TqMatrix p.k p.l) :
    commitCollision aHat = 𝔼 y : MaskBox p, 𝔼 y' : MaskBox p,
      if realBuckets aHat y = realBuckets aHat y' then (1 : ℝ) else 0 :=
  PMF.sum_sq_toReal_map_uniformOfFintype _

omit [NTTRingLaws nttOps] in
/-- The collision probability is nonnegative. -/
theorem commitCollision_nonneg (aHat : TqMatrix p.k p.l) : 0 ≤ commitCollision aHat :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit nttOps [NTTRingLaws nttOps] [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The collision bound** `(((4γ₂ + 1)/q)^k + (2γ₁)^-ℓ)^256`. -/
noncomputable def commitCollisionBound (p : Params) : ℝ :=
  ((((4 * p.gamma2 + 1 : ℕ) : ℝ) / modulus) ^ p.k + (((2 * p.gamma1 : ℕ) : ℝ)⁻¹) ^ p.l) ^
    ringDegree

/-- **The collision probability of the commitment under a uniform matrix**:
`𝔼_Â CP(Â) ≤ (((4γ₂ + 1)/q)^k + (2γ₁)^-ℓ)^256`. For fixed masks `y, y'` a collision has
probability at most `t^(256 - #Z(y - y'))`, `t = ((4γ₂ + 1)/q)^k` (`expect_bucketsOf_eq_le`); over
`y`, `𝔼 t^(256 - #Z) = t^256 𝔼 (1/t)^#Z ≤ (t + (1 - t)(2γ₁)^-ℓ)^256`
(`GordieHowe.expect_one_add_pow_card_le`, `expect_subset_zeroSlots_sub_le`). -/
theorem expect_commitCollision_le (hp : SigningParams p) :
    𝔼 aHat : TqMatrix p.k p.l, commitCollision aHat ≤ commitCollisionBound p := by
  classical
  set t : ℝ := (((4 * p.gamma2 + 1 : ℕ) : ℝ) / modulus) ^ p.k
  set a : ℝ := (((2 * p.gamma1 : ℕ) : ℝ)⁻¹) ^ p.l
  have hq0 : (0 : ℝ) < modulus := by norm_num [modulus]
  have hρ1 : ((4 * p.gamma2 + 1 : ℕ) : ℝ) ≤ modulus := by
    have := hp.four_gamma2_lt
    exact_mod_cast (by omega : 4 * p.gamma2 + 1 ≤ modulus)
  have ht0 : 0 < t := pow_pos (div_pos (by positivity) hq0) _
  have ht1 : t ≤ 1 := pow_le_one₀ (div_nonneg (by positivity) hq0.le) ((div_le_one hq0).2 hρ1)
  have ha0 : 0 ≤ a := by positivity
  have hx : 0 ≤ t⁻¹ - 1 := sub_nonneg.2 ((one_le_inv₀ ht0).2 ht1)
  have hy' : ∀ y' : MaskBox p, 𝔼 y : MaskBox p,
      t ^ (ringDegree - #(zeroSlots fun b => y.1.get b - y'.1.get b)) ≤ (t + a) ^ ringDegree := by
    intro y'
    have hZ := GordieHowe.expect_one_add_pow_card_le
      (Z := fun y : MaskBox p => zeroSlots fun b => y.1.get b - y'.1.get b) hx
      (expect_subset_zeroSlots_sub_le hp y')
    rw [Fintype.card_fin] at hZ
    have hpow : ∀ y : MaskBox p, t ^ (ringDegree - #(zeroSlots fun b => y.1.get b - y'.1.get b)) =
        t ^ ringDegree * (1 + (t⁻¹ - 1)) ^ #(zeroSlots fun b => y.1.get b - y'.1.get b) := by
      intro y
      rw [add_sub_cancel, pow_sub₀ t ht0.ne' ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _)), inv_pow]
    simp_rw [hpow]
    rw [← Finset.mul_expect]
    calc t ^ ringDegree * 𝔼 y : MaskBox p,
          (1 + (t⁻¹ - 1)) ^ #(zeroSlots fun b => y.1.get b - y'.1.get b)
        ≤ t ^ ringDegree * (1 + (t⁻¹ - 1) * a) ^ ringDegree :=
          mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = (t + (1 - t) * a) ^ ringDegree := by
          rw [← mul_pow]
          congr 1
          field_simp
      _ ≤ (t + a) ^ ringDegree :=
          pow_le_pow_left₀ (by nlinarith) (by nlinarith) _
  calc 𝔼 aHat : TqMatrix p.k p.l, commitCollision aHat
      = 𝔼 y' : MaskBox p, 𝔼 y : MaskBox p, 𝔼 aHat : TqMatrix p.k p.l,
          (if realBuckets aHat y = realBuckets aHat y' then 1 else 0 : ℝ) := by
        simp_rw [commitCollision_eq]
        rw [Finset.expect_comm]
        rw [Finset.expect_congr rfl fun y _ => Finset.expect_comm _ _ _]
        exact Finset.expect_comm _ _ _
    _ ≤ 𝔼 y' : MaskBox p, 𝔼 y : MaskBox p,
          t ^ (ringDegree - #(zeroSlots fun b => y.1.get b - y'.1.get b)) :=
        Finset.expect_le_expect fun y' _ => Finset.expect_le_expect fun y _ =>
          (expect_bucketsOf_eq_le hp y.1 y'.1)
    _ ≤ 𝔼 _y' : MaskBox p, (t + a) ^ ringDegree := Finset.expect_le_expect fun y' _ => hy' y'
    _ = commitCollisionBound p := Finset.expect_const univ_nonempty _

end Collision

/-! ### The bound at the approved parameter sets -/

/-- The collision bound at ML-DSA-44 is at most `(2^-17)^256`:
`(380929/q)^4 + 2^-72 ≤ 2^-17`. -/
theorem commitCollisionBound_le_mldsa44 :
    commitCollisionBound _root_.MLDSA.mldsa44 ≤ (1 / 2 ^ 17) ^ ringDegree := by
  obtain ⟨hk, hl, hg1, hg2, -, -⟩ := mldsa44_vals
  rw [commitCollisionBound, hk, hl, hg1, hg2]
  refine pow_le_pow_left₀ (add_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _)) _) (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _)) ?_ _
  norm_num [modulus]

/-- The collision bound at ML-DSA-65 is at most `(2^-17)^256`:
`(1047553/q)^6 + 2^-100 ≤ 2^-17`. -/
theorem commitCollisionBound_le_mldsa65 :
    commitCollisionBound mldsa65 ≤ (1 / 2 ^ 17) ^ ringDegree := by
  obtain ⟨hk, hl, hg1, hg2, -, -⟩ := mldsa65_vals
  rw [commitCollisionBound, hk, hl, hg1, hg2]
  refine pow_le_pow_left₀ (add_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _)) _) (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _)) ?_ _
  norm_num [modulus]

/-- The collision bound at ML-DSA-87 is at most `(2^-17)^256`:
`(1047553/q)^8 + 2^-140 ≤ 2^-17`. -/
theorem commitCollisionBound_le_mldsa87 :
    commitCollisionBound mldsa87 ≤ (1 / 2 ^ 17) ^ ringDegree := by
  obtain ⟨hk, hl, hg1, hg2, -, -⟩ := mldsa87_vals
  rw [commitCollisionBound, hk, hl, hg1, hg2]
  refine pow_le_pow_left₀ (add_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _)) _) (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _)) ?_ _
  norm_num [modulus]

end GordieHowe.MLDSA.Regularity
