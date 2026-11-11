-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.CommitCollision
public import GordieHowe.Model.Lattice.MLDSA
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# The point probability of the commitment

The signer's commitment is `w₁ = HighBits(Â y)` for a mask `y` uniform on the mask box
(`realBuckets`, `maskUniform`; FIPS 204 Algorithm 7 lines 11–14, Algorithm 37). Its point
probability at the matrix `Â` is `δ(Â) = max_v Pr_y[HighBits(Â y) = v]` (`commitPointMax`).

**One matrix.** Fix `l` distinct rows `σ` of `A = NTT⁻¹(Â)` and let `ker(A_σ)` be the kernel of
the minor on them, the `d ∈ R_q^l` with `∑_b A_{σ i, b} d_b = 0` for every `i` (`minorKernel`).
A `HighBits` fibre of `Z_q` has at most `2γ₂ + 1` elements (`card_highBitsCoeff_fibre_le`), so
the rows `σ` of `A y` lie in a set of at most `(2γ₂ + 1)^(256 l)` vectors, and two masks with the
same rows `σ` differ by an element of `ker(A_σ)`. Hence
`δ(Â) ≤ #ker(A_σ) · deltaGood p` with `deltaGood p = ((2γ₂ + 1)/(2γ₁))^(256 l)`
(`card_realBuckets_eq_le`, `commitPointMax_le`).

At the slot `j` (the root `r_j = ζ^(2j+1)` of `X^256 + 1`, `SlotTransform.lean`) the minor is the
`l × l` matrix `M_j` over `Z_q` of the values `A_{σ i, b}(r_j)` (`slotMinor`). The kernel is the
product of the slot kernels, so `#ker(A_σ) = q^(∑_j (l - rank M_j))` (`card_minorKernel`), and
`δ(Â) ≤ q^(∑_j (l - rank M_j)) · deltaGood p` (`commitPointMax_le_slotRank`): a slot whose minor
has rank `l - e` costs a factor `q^e`. If every slot minor has rank `l`, `δ(Â) ≤ deltaGood p`
(`commitPointMax_le_deltaGood`).

**A uniform matrix.** For `A` uniform, `𝔼_A #ker(A_σ) = ∑_d Pr_A[d ∈ ker(A_σ)]`. The top
`256 - #Z(d)` coefficients of every row of `A d` are uniform (`expect_topCoeffs`, `Z(d)` the zero
slots of `d`), so `Pr_A[d ∈ ker(A_σ)] ≤ (q^-l)^(256 - #Z(d))` (`expect_mem_minorKernel_le`); a
uniform `d` has `D ⊆ Z(d)` with probability at most `(q^-l)^#D`
(`expect_subset_zeroSlots_le`). Summing over the zero-slot patterns
(`GordieHowe.expect_one_add_pow_card_le`), `𝔼_A #ker(A_σ) ≤ (2 - q^-l)^256`
(`expect_card_minorKernel_le`), and `𝔼_Â δ(Â) ≤ (2 - q^-l)^256 · deltaGood p`
(`commitPointAvgBound`, `expect_commitPointMax_le`).

**The approved parameter sets** (exact integer comparisons, `decide +kernel`):

| set       | `(k, l)` | `deltaGood p`     | `commitPointAvgBound p` |
|-----------|----------|-------------------|-------------------------|
| ML-DSA-44 | `(4, 4)` | `≤ 2^-471`        | `≤ 2^-215`              |
| ML-DSA-65 | `(6, 5)` | `≤ 2^-1281`       | `≤ 2^-1025`             |
| ML-DSA-87 | `(8, 7)` | `≤ 2^-1794`       | `≤ 2^-1538`             |

(`deltaGood_mldsa44`, `_mldsa65`, `_mldsa87`; `commitPointAvgBound_mldsa44`, `_mldsa65`,
`_mldsa87`, from `(2 - q^-l)^256 ≤ 2^256`, `commitPointAvgBound_le_of_deltaGood_le`).

**Honest keys.** `commitPointAt prims` is `𝔼_seed δ(ExpandA(ρ(seed)))` at the key-generation
matrix (`GordieHowe.Lattice.keyGenMatrix`); it is a definition, not bounded here.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

/-! ### `HighBits` fibres -/

/-- **A `HighBits` fibre of `Z_q` has at most `2γ₂ + 1` elements**, for `2γ₂ ∣ q - 1`: a residue
with `HighBits(r) = r₁` is `2γ₂ r₁ + r₀` for its low part `r₀ ∈ [-γ₂, γ₂]` (FIPS 204
Algorithm 36, `decomposeCoeff_repr`). -/
theorem card_highBitsCoeff_fibre_le {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (h : ℕ) : #(univ.filter fun r : Coeff => highBitsCoeff r γ₂ = h) ≤ 2 * γ₂ + 1 := by
  have hcast : ∀ r : Coeff, highBitsCoeff r γ₂ = h →
      r = ((2 * γ₂ * h + (decomposeCoeff r γ₂).2 : ℤ) : Coeff) := by
    intro r hr
    have hd := GordieHowe.MLDSA44.decomposeCoeff_repr hγ hdvd r
    have h1 : (decomposeCoeff r γ₂).1 = h := hr
    rw [h1] at hd
    have hr' : ((r.val : ℤ) : Coeff) = r := by simp
    rcases hd.val_eq with he | he
    · calc r = ((r.val : ℤ) : Coeff) := hr'.symm
        _ = _ := by rw [he]
    · calc r = ((r.val : ℤ) : Coeff) := hr'.symm
        _ = _ := by rw [he]; push_cast; simp
  have hI : #(Finset.Icc (-(γ₂ : ℤ)) γ₂) = 2 * γ₂ + 1 := by rw [Int.card_Icc]; omega
  rw [← hI]
  refine Finset.card_le_card_of_injOn (fun r => (decomposeCoeff r γ₂).2) (fun r hr => ?_)
    fun r hr r' hr' he => ?_
  · have hr0 := (GordieHowe.MLDSA44.decomposeCoeff_repr hγ hdvd r).low_mem
    dsimp only
    rw [mem_coe, mem_Icc]
    rcases hr0 with ⟨h2, h3⟩ | ⟨-, h2⟩ <;> constructor <;> omega
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr hr'
    have he' : (decomposeCoeff r γ₂).2 = (decomposeCoeff r' γ₂).2 := he
    calc r = ((2 * γ₂ * h + (decomposeCoeff r γ₂).2 : ℤ) : Coeff) := hcast r hr
      _ = ((2 * γ₂ * h + (decomposeCoeff r' γ₂).2 : ℤ) : Coeff) := by rw [he']
      _ = r' := (hcast r' hr').symm

/-- **A coefficientwise `HighBits` fibre of `R_q` has at most `(2γ₂ + 1)^256` elements**: the
polynomials whose coefficients have the prescribed `HighBits` (`card_highBitsCoeff_fibre_le`). -/
theorem card_highBitsPoly_fibre_le {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (u : Fin ringDegree → ℕ) :
    #(univ.filter fun r : Rq => ∀ c, highBitsCoeff (r.get c) γ₂ = u c) ≤
      (2 * γ₂ + 1) ^ ringDegree := by
  have h := natCard_vector_forall (α := Coeff) (n := ringDegree)
    (fun c (x : Coeff) => highBitsCoeff x γ₂ = u c)
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  change #(univ.filter fun r : Vector Coeff ringDegree => ∀ c, highBitsCoeff (r.get c) γ₂ = u c) ≤ _
  rw [h]
  calc ∏ c, #(univ.filter fun x : Coeff => highBitsCoeff x γ₂ = u c)
      ≤ ∏ _c : Fin ringDegree, (2 * γ₂ + 1) :=
        Finset.prod_le_prod fun c _ => card_highBitsCoeff_fibre_le hγ hdvd (u c)
    _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]

/-! ### The kernel of a minor -/

section Kernel

variable {k l : ℕ}

/-- **The kernel of the minor on the rows `σ`** of a coefficient-domain matrix
`A ∈ R_q^(k × l)`: the `d ∈ R_q^l` with `∑_b A_{σ i, b} d_b = 0` for every `i`. -/
noncomputable def minorKernel (σ : Fin l ↪ Fin k) (A : Fin k → Fin l → Rq) :
    Finset (Fin l → Rq) :=
  univ.filter fun d => ∀ i, ∑ b, A (σ i) b * d b = 0

/-- Multiplication in `R_q` distributes over subtraction on the right factor. -/
theorem rq_mul_sub (f g h : Rq) : f * (g - h) = f * g - f * h := by
  have h1 : f * (g - h) + f * h = f * g := by
    rw [← rq_mul_add]
    congr 1
    exact sub_add_cancel g h
  exact eq_sub_of_add_eq h1

/-- The rows `σ` of `A d` are additive in `d`: `∑_b A_{ib} (y_b - y'_b) = ∑_b A_{ib} y_b -
∑_b A_{ib} y'_b`. -/
theorem sum_mul_sub (A : Fin l → Rq) (y y' : Fin l → Rq) :
    ∑ b, A b * (y b - y' b) = ∑ b, A b * y b - ∑ b, A b * y' b := by
  exact (Finset.sum_congr rfl fun b _ => rq_mul_sub _ _ _).trans
    (Finset.sum_sub_distrib (f := fun b => A b * y b) (g := fun b => A b * y' b))

end Kernel

/-! ### The count at one matrix -/

section Count

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] [NTTRingLaws nttOps]

omit [NeZero (bucketCount p)] in
/-- Row `i` of `Â y` is `∑_b A_{ib} y_b` with `A = NTT⁻¹(Â)` entrywise. -/
theorem mul_get_eq_sum (aHat : TqMatrix p.k p.l) (y : RqVec p.l) (i : Fin p.k) :
    (aHat * y).get i = ∑ b, matOfHat aHat i b * y.get b :=
  coeffMatVecMul_get nttOps aHat y i

/-- **The masks with a given commitment number at most `#ker(A_σ) · (2γ₂ + 1)^(256 l)`**, for
any `l` rows `σ` of `A = NTT⁻¹(Â)`: the rows `σ` of `A y` lie in a product of `l` polynomial
`HighBits` fibres (`card_highBitsPoly_fibre_le`), and two masks with the same rows `σ` differ by
an element of the kernel of the minor (`minorKernel`). -/
theorem card_realBuckets_eq_le (hp : SigningParams p) (aHat : TqMatrix p.k p.l)
    (σ : Fin p.l ↪ Fin p.k) (v : BucketVec p) :
    #(univ.filter fun y : MaskBox p => realBuckets aHat y = v) ≤
      #(minorKernel σ (matOfHat aHat)) * ((2 * p.gamma2 + 1) ^ ringDegree) ^ p.l := by
  classical
  set s := univ.filter fun y : MaskBox p => realBuckets aHat y = v
  set f : MaskBox p → Fin p.l → Rq := fun y i => (aHat * y.1).get (σ i)
  set T := Fintype.piFinset fun i : Fin p.l =>
    univ.filter fun r : Rq => ∀ c, highBitsCoeff (r.get c) p.gamma2 = (v (σ i, c)).val
  have hfib : ∀ w ∈ s.image f, #(s.filter fun y => f y = w) ≤ #(minorKernel σ (matOfHat aHat)) := by
    intro w _
    rcases (s.filter fun y => f y = w).eq_empty_or_nonempty with h0 | ⟨y0, hy0⟩
    · rw [h0, card_empty]; exact Nat.zero_le _
    have hy0w : f y0 = w := (mem_filter.1 hy0).2
    refine Finset.card_le_card_of_injOn (fun y b => y.1.get b - y0.1.get b) (fun y hy => ?_)
      fun y _ y' _ he => ?_
    · have hyw : f y = w := (mem_filter.1 hy).2
      simp only [minorKernel, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      intro i
      rw [sum_mul_sub]
      have h1 := congrFun hyw i
      have h2 := congrFun hy0w i
      simp only [f, mul_get_eq_sum] at h1 h2
      rw [h1, h2]
      exact sub_self _
    · apply Subtype.ext
      apply Vector.ext
      intro i hi
      have h3 := congrFun he ⟨i, hi⟩
      simp only [Vector.get_eq_getElem] at h3
      exact sub_left_injective (b := (y0.1)[i]) h3
  have himg : s.image f ⊆ T := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
    have hy' := (realBuckets_eq_iff hp aHat y v).1 (mem_filter.1 hy).2
    simp only [T, Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
    intro i c
    have := hy' (σ i, c)
    rwa [rqVecCoeffs_apply] at this
  have hT : #T ≤ ((2 * p.gamma2 + 1) ^ ringDegree) ^ p.l := by
    rw [Fintype.card_piFinset]
    calc _ ≤ ∏ _i : Fin p.l, (2 * p.gamma2 + 1) ^ ringDegree :=
          Finset.prod_le_prod fun i _ =>
            card_highBitsPoly_fibre_le hp.gamma2_pos hp.gamma2_dvd fun c => (v (σ i, c)).val
      _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]
  calc #s ≤ #(minorKernel σ (matOfHat aHat)) * #(s.image f) :=
        Finset.card_le_mul_card_image s _ hfib
    _ ≤ _ := Nat.mul_le_mul_left _ ((card_le_card himg).trans hT)

end Count

/-! ### The kernel slot by slot -/

section Slots

variable {k l : ℕ}

/-- **The minor at slot `j`**: the `l × l` matrix over `Z_q` of the values at the root
`r_j = ζ^(2j+1)` of the entries of `A` on the rows `σ` (the NTT slot `j` of the minor). -/
noncomputable def slotMinor (σ : Fin l ↪ Fin k) (A : Fin k → Fin l → Rq) (j : Fin ringDegree) :
    Matrix (Fin l) (Fin l) Coeff :=
  Matrix.of fun i b => slotEval (slotRoot j) (A (σ i) b)

/-- A polynomial is zero exactly when it vanishes at every slot (`slotVec_injective`). -/
theorem rq_eq_zero_iff_forall_slotEval (f : Rq) :
    f = 0 ↔ ∀ j, slotEval (slotRoot j) f = 0 := by
  constructor
  · rintro rfl j
    exact slotEval_zero (slotRoot_pow j)
  · intro h
    apply slotVec_injective
    funext j
    rw [slotVec, slotVec, h j, slotEval_zero (slotRoot_pow j)]

/-- **The kernel of the minor, slot by slot**: `d` is in the kernel of the minor on the rows `σ`
exactly when at every slot `j` the values `d̂(j)` are in the kernel of the slot minor. -/
theorem mem_minorKernel_iff (σ : Fin l ↪ Fin k) (A : Fin k → Fin l → Rq) (d : Fin l → Rq) :
    d ∈ minorKernel σ A ↔
      ∀ j, (slotMinor σ A j).mulVec (fun b => slotEval (slotRoot j) (d b)) = 0 := by
  simp only [minorKernel, mem_filter, mem_univ, true_and]
  have hrow : ∀ i j, slotEval (slotRoot j) (∑ b, A (σ i) b * d b) =
      (slotMinor σ A j).mulVec (fun b => slotEval (slotRoot j) (d b)) i := by
    intro i j
    rw [slotEval_sum (slotRoot_pow j)]
    simp only [slotEval_mul (slotRoot_pow j), Matrix.mulVec, dotProduct, slotMinor,
      Matrix.of_apply]
  constructor
  · intro h j
    funext i
    rw [← hrow, h i]
    exact slotEval_zero (slotRoot_pow j)
  · intro h i
    rw [rq_eq_zero_iff_forall_slotEval]
    intro j
    rw [hrow]
    exact congrFun (h j) i

/-- The values at every slot of every component: `R_q^l ≃ (Z_q^l)^256`. -/
noncomputable def slotFunEquiv (l : ℕ) : (Fin l → Rq) ≃ (Fin ringDegree → Fin l → Coeff) where
  toFun d j b := slotEval (slotRoot j) (d b)
  invFun F b := (Equiv.ofBijective slotVec slotVec_bijective).symm fun j => F j b
  left_inv d := funext fun b => (Equiv.ofBijective slotVec slotVec_bijective).symm_apply_apply (d b)
  right_inv F := funext fun j => funext fun b =>
    congrFun ((Equiv.ofBijective slotVec slotVec_bijective).apply_symm_apply fun j => F j b) j

/-- **A kernel over `Z_q` has `q^(l - rank)` elements**: rank–nullity
(`LinearMap.finrank_range_add_finrank_ker`) and `#V = q^(dim V)`
(`Module.natCard_eq_pow_finrank`). -/
theorem card_mulVec_eq_zero (M : Matrix (Fin l) (Fin l) Coeff) :
    Fintype.card {x : Fin l → Coeff // M.mulVec x = 0} = modulus ^ (l - M.rank) := by
  classical
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hk : Module.finrank Coeff (LinearMap.ker M.mulVecLin) = l - M.rank := by
    rw [Matrix.rank]; omega
  rw [← Nat.card_eq_fintype_card]
  calc Nat.card {x : Fin l → Coeff // M.mulVec x = 0}
      = Nat.card (LinearMap.ker M.mulVecLin) := Nat.card_congr (Equiv.subtypeEquivRight fun x => by
          rw [LinearMap.mem_ker, Matrix.mulVecLin_apply])
    _ = Nat.card Coeff ^ Module.finrank Coeff (LinearMap.ker M.mulVecLin) :=
        Module.natCard_eq_pow_finrank
    _ = _ := by rw [Nat.card_zmod, hk]

/-- **The size of the kernel of the minor is `q^(∑_j (l - rank M_j))`**, `M_j` the slot minors
(`slotMinor`): the kernel is the product over the slots of the kernels of the slot minors
(`mem_minorKernel_iff`), and a slot minor of rank `l - e` has a kernel of `q^e` elements
(`card_mulVec_eq_zero`). -/
theorem card_minorKernel (σ : Fin l ↪ Fin k) (A : Fin k → Fin l → Rq) :
    #(minorKernel σ A) = modulus ^ ∑ j, (l - (slotMinor σ A j).rank) := by
  classical
  rw [← Fintype.card_coe]
  calc Fintype.card (minorKernel σ A)
      = Fintype.card {F : Fin ringDegree → Fin l → Coeff //
          ∀ j, (slotMinor σ A j).mulVec (F j) = 0} :=
        Fintype.card_congr ((slotFunEquiv l).subtypeEquiv fun d => by
          rw [mem_minorKernel_iff]
          exact Iff.rfl)
    _ = ∏ j, Fintype.card {x : Fin l → Coeff // (slotMinor σ A j).mulVec x = 0} := by
        rw [Fintype.card_congr
          (Equiv.subtypePiEquivPi (β := fun _ : Fin ringDegree => Fin l → Coeff)
          (p := fun j x => (slotMinor σ A j).mulVec x = 0)), Fintype.card_pi]
    _ = _ := by simp only [card_mulVec_eq_zero, Finset.prod_pow_eq_pow_sum]

end Slots

/-! ### The point probability at one matrix -/

section Point

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]

/-- **The point probability bound for a full-rank minor**: `((2γ₂ + 1)/(2γ₁))^(256 l)`. -/
noncomputable def deltaGood (p : Params) : ℝ :=
  (((2 * p.gamma2 + 1 : ℕ) : ℝ) / ((2 * p.gamma1 : ℕ) : ℝ)) ^ (ringDegree * p.l)

omit nttOps in
/-- `deltaGood p` is nonnegative. -/
theorem deltaGood_nonneg (p : Params) : 0 ≤ deltaGood p := by
  unfold deltaGood; positivity

omit [NeZero (bucketCount p)] nttOps in
/-- The law of `f(y)` for `y` uniform on the mask box: `Pr[f(y) = v]` is the number of masks
with `f(y) = v` over `(2γ₁)^(256 l)`. -/
theorem toReal_map_maskUniform_apply (hq : 2 * p.gamma1 < modulus) {β : Type*} [DecidableEq β]
    (f : MaskBox p → β) (v : β) :
    ((maskUniform p).map f v).toReal =
      #(univ.filter fun y => f y = v) / ((2 * p.gamma1 : ℕ) : ℝ) ^ (ringDegree * p.l) := by
  rw [PMF.map_apply, tsum_fintype]
  trans (∑ y, if f y = v then ((Fintype.card (MaskBox p) : ENNReal))⁻¹ else 0).toReal
  · congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : f y = v
    · simp only [h, ite_true, maskUniform, PMF.uniformOfFintype_apply]
    · simp only [h, Ne.symm h, ite_false]
  have hc : Fintype.card (MaskBox p) = (2 * p.gamma1) ^ (ringDegree * p.l) := by
    rw [← Nat.card_eq_fintype_card]; exact natCard_maskBox hq
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, hc]
  simp [div_eq_mul_inv, ENNReal.toReal_inv]

/-- **The point probability of the commitment** at the matrix `Â`: the largest probability of a
commitment value, `max_v Pr_y[HighBits(Â y) = v]` for `y` uniform on the mask box
(`realBuckets`, `maskUniform`). -/
noncomputable def commitPointMax (aHat : TqMatrix p.k p.l) : ℝ :=
  ⨆ v : BucketVec p, ((maskUniform p).map (realBuckets aHat) v).toReal

/-- Every commitment value has probability at most `commitPointMax`. -/
theorem toReal_map_realBuckets_le_commitPointMax (aHat : TqMatrix p.k p.l) (v : BucketVec p) :
    ((maskUniform p).map (realBuckets aHat) v).toReal ≤ commitPointMax aHat :=
  le_ciSup (f := fun v => ((maskUniform p).map (realBuckets aHat) v).toReal)
    (Finite.bddAbove_range _) v

variable [NTTRingLaws nttOps]

/-- **The point probability at one matrix**: for any `l` rows `σ` of `A = NTT⁻¹(Â)`,
`commitPointMax Â ≤ #ker(A_σ) · deltaGood p` (`card_realBuckets_eq_le`). -/
theorem commitPointMax_le (hp : SigningParams p) (aHat : TqMatrix p.k p.l)
    (σ : Fin p.l ↪ Fin p.k) :
    commitPointMax aHat ≤ #(minorKernel σ (matOfHat aHat)) * deltaGood p := by
  have hq := hp.two_gamma1_lt
  have hγ : 0 < p.gamma1 := by have := hp.beta_lt_gamma1; omega
  have hpos : (0 : ℝ) < ((2 * p.gamma1 : ℕ) : ℝ) ^ (ringDegree * p.l) := by
    have : (0 : ℝ) < ((2 * p.gamma1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * p.gamma1)
    positivity
  refine ciSup_le fun v => ?_
  rw [toReal_map_maskUniform_apply hq, div_le_iff₀ hpos, deltaGood, div_pow, mul_assoc,
    div_mul_cancel₀ _ hpos.ne']
  have h := card_realBuckets_eq_le hp aHat σ v
  rw [← pow_mul] at h
  exact_mod_cast h

/-- **The point probability in terms of the slot ranks**: `commitPointMax Â ≤
q^(∑_j (l - rank M_j)) · deltaGood p`, `M_j` the slot minors of the rows `σ` of `A = NTT⁻¹(Â)`
(`card_minorKernel`). A slot whose minor has rank `l - e` costs a factor `q^e`. -/
theorem commitPointMax_le_slotRank (hp : SigningParams p) (aHat : TqMatrix p.k p.l)
    (σ : Fin p.l ↪ Fin p.k) :
    commitPointMax aHat ≤
      (modulus : ℝ) ^ (∑ j, (p.l - (slotMinor σ (matOfHat aHat) j).rank)) * deltaGood p := by
  have h := commitPointMax_le hp aHat σ
  rw [card_minorKernel] at h
  exact_mod_cast h

/-- **The full-rank case**: if the minor on the rows `σ` has rank `l` at every slot, then
`commitPointMax Â ≤ deltaGood p`. -/
theorem commitPointMax_le_deltaGood (hp : SigningParams p) (aHat : TqMatrix p.k p.l)
    (σ : Fin p.l ↪ Fin p.k) (hrank : ∀ j, (slotMinor σ (matOfHat aHat) j).rank = p.l) :
    commitPointMax aHat ≤ deltaGood p := by
  have h := commitPointMax_le_slotRank hp aHat σ
  simp only [hrank, Nat.sub_self, Finset.sum_const_zero, pow_zero, one_mul] at h
  exact h

end Point

/-! ### A uniform matrix -/

section Uniform

variable {k l : ℕ}

/-- The coefficients of every component: `R_q^l ≃ (Z_q^256)^l`. -/
noncomputable def rqFunEquiv (l : ℕ) : (Fin l → Rq) ≃ (Fin l → Fin ringDegree → Coeff) where
  toFun d b c := (d b).get c
  invFun F b := polyOf (F b)
  left_inv d := funext fun b => polyOf_get_self (d b)
  right_inv F := funext fun b => funext fun c => polyOf_get (F b) c

/-- **A uniform `d ∈ R_q^l` has `D ⊆ Z(d)` with probability at most `(q^-l)^#D`**: each of the
`l` independent components vanishes on `D` with probability at most `q^-#D`
(`expect_vanishing_le_of_injective`). -/
theorem expect_subset_zeroSlots_le (D : Finset (Fin ringDegree)) :
    𝔼 d : Fin l → Rq, (if D ⊆ zeroSlots d then 1 else 0 : ℝ) ≤
      (((modulus : ℝ)⁻¹) ^ l) ^ #D := by
  classical
  have hind : ∀ F : Fin l → Fin ringDegree → Coeff,
      (if D ⊆ zeroSlots ((rqFunEquiv l).symm F) then 1 else 0 : ℝ) =
        ∏ b : Fin l,
          (if ∀ j ∈ D, ∑ c, id (F b c) * slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) := by
    intro F
    rw [Finset.prod_boole]
    have hiff : D ⊆ zeroSlots ((rqFunEquiv l).symm F) ↔
        ∀ b : Fin l, ∀ j ∈ D, ∑ c, id (F b c) * slotRoot j ^ (c : ℕ) = 0 := by
      simp only [zeroSlots, subset_iff, mem_filter, mem_univ, true_and, slotEval, rqFunEquiv,
        Equiv.coe_fn_symm_mk, polyOf_get, id]
      exact ⟨fun h b j hj => h hj b, fun h j hj b => h b j hj⟩
    simp only [mem_univ, true_implies, hiff]
  calc 𝔼 d : Fin l → Rq, (if D ⊆ zeroSlots d then 1 else 0 : ℝ)
      = 𝔼 F : Fin l → Fin ringDegree → Coeff, ∏ b : Fin l,
          (if ∀ j ∈ D, ∑ c, id (F b c) * slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) := by
        refine Fintype.expect_equiv (rqFunEquiv l) _ _ fun d => ?_
        rw [← hind, Equiv.symm_apply_apply]
    _ = ∏ b : Fin l, 𝔼 g : Fin ringDegree → Coeff,
          (if ∀ j ∈ D, ∑ c, id (g c) * slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ) :=
        PMF.expect_prod_apply (fun (_ : Fin l) (g : Fin ringDegree → Coeff) =>
          (if ∀ j ∈ D, ∑ c, id (g c) * slotRoot j ^ (c : ℕ) = 0 then 1 else 0 : ℝ))
    _ ≤ ∏ _b : Fin l, ((Fintype.card Coeff : ℝ)⁻¹) ^ #D :=
        Finset.prod_le_prod₀ (fun b _ => Finset.expect_nonneg fun g _ => by split_ifs <;> norm_num)
          fun b _ => expect_vanishing_le_of_injective Function.injective_id D
    _ = _ := by
        rw [prod_const, card_univ, Fintype.card_fin, ZMod.card, ← pow_mul, ← pow_mul, mul_comm]

/-- **The kernel of the minor under a uniform matrix**: for `l` distinct rows `σ` and any
`d ∈ R_q^l`, `Pr_A[d ∈ ker(A_σ)] ≤ (q^-l)^(256 - #Z(d))`. The top `256 - #Z(d)` coefficients
of every row of `A d` are uniform (`expect_topCoeffs`) and vanish on the rows `σ`. -/
theorem expect_mem_minorKernel_le (σ : Fin l ↪ Fin k) (d : Fin l → Rq) :
    𝔼 A : Fin k → Fin l → Rq, (if d ∈ minorKernel σ A then 1 else 0 : ℝ) ≤
      (((modulus : ℝ)⁻¹) ^ l) ^ (ringDegree - #(zeroSlots d)) := by
  classical
  set Z := #(zeroSlots d)
  set R : Finset (Fin k) := univ.map σ
  set g : topIndex k Z → Coeff → ℝ := fun x u => if x.1.1 ∈ R then (if u = 0 then 1 else 0) else 1
  have hg0 : ∀ x u, 0 ≤ g x u := by intro x u; simp only [g]; split_ifs <;> norm_num
  have hpt : ∀ A : Fin k → Fin l → Rq,
      (if d ∈ minorKernel σ A then 1 else 0 : ℝ) ≤ ∏ x, g x (topCoeffs d Z A x) := by
    intro A
    split_ifs with h
    · simp only [minorKernel, mem_filter, mem_univ, true_and] at h
      refine le_of_eq (Finset.prod_eq_one fun x _ => ?_).symm
      simp only [g]
      split_ifs with hx hu
      · rfl
      · exfalso
        apply hu
        obtain ⟨i, -, hi⟩ := mem_map.1 hx
        change (∑ b, A x.1.1 b * d b).get x.1.2 = 0
        rw [← hi, h i]
        exact LatticeCrypto.vectorRing_zero_get _
      · rfl
    · exact Finset.prod_nonneg fun x _ => hg0 x _
  have hE : ∀ x, 𝔼 u : Coeff, g x u = if x.1.1 ∈ R then (modulus : ℝ)⁻¹ else 1 := by
    intro x
    simp only [g]
    split_ifs
    · rw [Fintype.expect_eq_sum_div_card, Finset.sum_ite_eq' univ (0 : Coeff), ZMod.card]
      simp
    · simp
  have hcard : #(univ.filter fun x : topIndex k Z => x.1.1 ∈ R) = l * (ringDegree - Z) := by
    rw [← card_map (Function.Embedding.subtype _)]
    have hm : (univ.filter fun x : topIndex k Z => x.1.1 ∈ R).map (Function.Embedding.subtype _) =
        R ×ˢ topPositions Z := by
      ext ⟨a, c⟩
      simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
        mem_product]
      constructor
      · rintro ⟨⟨⟨a', c'⟩, hmem⟩, hx, hxe⟩
        simp only [Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl⟩ := hxe
        exact ⟨hx, (mem_product.1 hmem).2⟩
      · rintro ⟨ha, hc⟩
        exact ⟨⟨(a, c), mem_product.2 ⟨mem_univ _, hc⟩⟩, ha, rfl⟩
    rw [hm, card_product, card_map, card_univ, Fintype.card_fin, card_topPositions]
  calc 𝔼 A : Fin k → Fin l → Rq, (if d ∈ minorKernel σ A then 1 else 0 : ℝ)
      ≤ 𝔼 A : Fin k → Fin l → Rq, ∏ x, g x (topCoeffs d Z A x) :=
        Finset.expect_le_expect fun A _ => hpt A
    _ = 𝔼 u : topIndex k Z → Coeff, ∏ x, g x (u x) :=
        expect_topCoeffs d (fun u => ∏ x, g x (u x))
    _ = ∏ x, 𝔼 r, g x r := PMF.expect_prod_apply g
    _ = ∏ x : topIndex k Z, (if x.1.1 ∈ R then (modulus : ℝ)⁻¹ else 1) :=
        Finset.prod_congr rfl fun x _ => hE x
    _ = ((modulus : ℝ)⁻¹) ^ #(univ.filter fun x : topIndex k Z => x.1.1 ∈ R) := by
        rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
    _ = _ := by rw [hcard, pow_mul]

/-- **The expected kernel size of the minor under a uniform matrix**: for `l` distinct rows `σ`,
`𝔼_A #ker(A_σ) ≤ (2 - q^-l)^256`. With `Q = q^l`, `𝔼_A #ker(A_σ) = ∑_d Pr_A[d ∈ ker(A_σ)] ≤
∑_d Q^-(256 - #Z(d)) = 𝔼_d Q^#Z(d)` (`expect_mem_minorKernel_le`), and
`𝔼_d (1 + (Q - 1))^#Z(d) ≤ (1 + (Q - 1)/Q)^256` (`expect_one_add_pow_card_le`,
`expect_subset_zeroSlots_le`): the sum over the zero-slot patterns of `d`. -/
theorem expect_card_minorKernel_le (σ : Fin l ↪ Fin k) :
    𝔼 A : Fin k → Fin l → Rq, (#(minorKernel σ A) : ℝ) ≤
      (2 - ((modulus : ℝ) ^ l)⁻¹) ^ ringDegree := by
  classical
  set Q : ℝ := (modulus : ℝ) ^ l with hQ
  have hq0 : (0 : ℝ) < modulus := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne modulus)
  have hQ0 : 0 < Q := pow_pos hq0 l
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne modulus))
  have hinvQ : ((modulus : ℝ)⁻¹) ^ l = Q⁻¹ := by rw [hQ, inv_pow]
  have h1 : ∀ A : Fin k → Fin l → Rq, (#(minorKernel σ A) : ℝ) =
      ∑ d, (if d ∈ minorKernel σ A then 1 else 0 : ℝ) := by
    intro A
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, univ_inter]
  have hcardF : (Nat.card (Fin l → Rq) : ℝ) = Q ^ ringDegree := by
    have hc : Nat.card (Fin l → Rq) = (modulus ^ ringDegree) ^ l := by
      rw [Nat.card_congr (rqFunEquiv l), Nat.card_fun, Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card (α := Fin ringDegree), Nat.card_eq_fintype_card (α := Fin l),
        Fintype.card_fin, Fintype.card_fin]
    rw [hc, Nat.cast_pow, Nat.cast_pow, hQ, ← pow_mul, ← pow_mul, mul_comm]
  have hpt : ∀ d : Fin l → Rq,
      (((modulus : ℝ)⁻¹) ^ l) ^ (ringDegree - #(zeroSlots d)) =
        (Q ^ ringDegree)⁻¹ * Q ^ #(zeroSlots d) := by
    intro d
    have hZ : #(zeroSlots d) ≤ ringDegree := (card_le_univ _).trans_eq (Fintype.card_fin _)
    rw [hinvQ, pow_sub₀ _ (inv_ne_zero hQ0.ne') hZ, inv_pow, inv_pow, inv_inv]
  have hZ : ∀ D : Finset (Fin ringDegree),
      𝔼 d : Fin l → Rq, (if D ⊆ zeroSlots d then 1 else 0 : ℝ) ≤ Q⁻¹ ^ #D := by
    intro D
    have := expect_subset_zeroSlots_le (l := l) D
    rwa [hinvQ] at this
  have hmain := GordieHowe.expect_one_add_pow_card_le (Z := fun d : Fin l → Rq => zeroSlots d)
    (x := Q - 1) (p := Q⁻¹) (by linarith) hZ
  simp only [add_sub_cancel, Fintype.card_fin] at hmain
  simp_rw [h1]
  rw [Finset.expect_sum_comm]
  calc ∑ d, 𝔼 A : Fin k → Fin l → Rq, (if d ∈ minorKernel σ A then 1 else 0 : ℝ)
      ≤ ∑ d : Fin l → Rq, (Q ^ ringDegree)⁻¹ * Q ^ #(zeroSlots d) :=
        Finset.sum_le_sum fun d _ => (expect_mem_minorKernel_le σ d).trans_eq (hpt d)
    _ = 𝔼 d : Fin l → Rq, Q ^ #(zeroSlots d) := by
        rw [← Finset.mul_sum, Fintype.expect_eq_sum_div_card, Fintype.card_eq_nat_card, hcardF,
          div_eq_inv_mul]
    _ ≤ (1 + (Q - 1) * Q⁻¹) ^ ringDegree := hmain
    _ = _ := by
        congr 1
        field_simp
        ring

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] [NTTRingLaws nttOps]
  [Nonempty (MaskBox p)]

/-- **The average point probability bound** at the parameter set `p`:
`(2 - q^-l)^256 · deltaGood p`. -/
noncomputable def commitPointAvgBound (p : Params) : ℝ :=
  (2 - ((modulus : ℝ) ^ p.l)⁻¹) ^ ringDegree * deltaGood p

/-- **The point probability of the commitment under a uniform matrix**: for `Â` uniform on
`T_q^(k × l)` and any `l` distinct rows `σ`, `𝔼_Â commitPointMax Â ≤ (2 - q^-l)^256 ·
deltaGood p` (`commitPointMax_le`, `expect_card_minorKernel_le`; `A = NTT⁻¹(Â)` is uniform,
`matOfHat_bijective`). -/
theorem expect_commitPointMax_le (hp : SigningParams p) (σ : Fin p.l ↪ Fin p.k) :
    𝔼 aHat : TqMatrix p.k p.l, commitPointMax aHat ≤ commitPointAvgBound p := by
  calc 𝔼 aHat : TqMatrix p.k p.l, commitPointMax aHat
      ≤ 𝔼 aHat : TqMatrix p.k p.l, (#(minorKernel σ (matOfHat aHat)) : ℝ) * deltaGood p :=
        Finset.expect_le_expect fun aHat _ => commitPointMax_le hp aHat σ
    _ = (𝔼 A : Fin p.k → Fin p.l → Rq, (#(minorKernel σ A) : ℝ)) * deltaGood p := by
        rw [Finset.expect_mul]
        exact Fintype.expect_bijective _ matOfHat_bijective _ _ fun _ => rfl
    _ ≤ commitPointAvgBound p :=
        mul_le_mul_of_nonneg_right (expect_card_minorKernel_le σ) (deltaGood_nonneg p)

end Uniform

/-! ### The approved parameter sets -/

/-- `(2 - q^-l)^256 ≤ 2^256` turns a bound `deltaGood p ≤ 2^-(n + 256)` into
`commitPointAvgBound p ≤ 2^-n`. -/
theorem commitPointAvgBound_le_of_deltaGood_le {p : Params} {n : ℕ}
    (h : deltaGood p ≤ (1 / 2) ^ (n + ringDegree)) : commitPointAvgBound p ≤ (1 / 2) ^ n := by
  have hq1 : (1 : ℝ) ≤ (modulus : ℝ) ^ p.l :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne modulus))
  have hinv : ((modulus : ℝ) ^ p.l)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
  have h2 : (2 - ((modulus : ℝ) ^ p.l)⁻¹) ^ ringDegree ≤ 2 ^ ringDegree :=
    pow_le_pow_left₀ (by linarith) (by linarith [inv_nonneg.2 (zero_le_one.trans hq1)]) _
  calc commitPointAvgBound p ≤ 2 ^ ringDegree * (1 / 2) ^ (n + ringDegree) :=
        mul_le_mul h2 h (deltaGood_nonneg p) (by positivity)
    _ = (1 / 2) ^ n := by
        rw [pow_add, mul_comm ((1 / 2 : ℝ) ^ n), ← mul_assoc, ← mul_pow]
        norm_num

/-- **ML-DSA-44**: `deltaGood = (190465/262144)^1024 ≤ 2^-471`. -/
theorem deltaGood_mldsa44 : deltaGood _root_.MLDSA.mldsa44 ≤ (1 / 2) ^ 471 := by
  obtain ⟨-, hl, hg1, hg2, -, -⟩ := mldsa44_vals
  rw [deltaGood, hl, hg1, hg2, div_pow, one_div_pow, div_le_div_iff₀ (by positivity)
    (by positivity), one_mul]
  exact_mod_cast (by decide +kernel : (2 * 95232 + 1) ^ (ringDegree * 4) * 2 ^ 471 ≤
    (2 * 131072) ^ (ringDegree * 4))

/-- **ML-DSA-65**: `deltaGood = (523777/1048576)^1280 ≤ 2^-1281`. -/
theorem deltaGood_mldsa65 : deltaGood mldsa65 ≤ (1 / 2) ^ 1281 := by
  obtain ⟨-, hl, hg1, hg2, -, -⟩ := mldsa65_vals
  rw [deltaGood, hl, hg1, hg2, div_pow, one_div_pow, div_le_div_iff₀ (by positivity)
    (by positivity), one_mul]
  exact_mod_cast (by decide +kernel : (2 * 261888 + 1) ^ (ringDegree * 5) * 2 ^ 1281 ≤
    (2 * 524288) ^ (ringDegree * 5))

/-- **ML-DSA-87**: `deltaGood = (523777/1048576)^1792 ≤ 2^-1794`. -/
theorem deltaGood_mldsa87 : deltaGood mldsa87 ≤ (1 / 2) ^ 1794 := by
  obtain ⟨-, hl, hg1, hg2, -, -⟩ := mldsa87_vals
  rw [deltaGood, hl, hg1, hg2, div_pow, one_div_pow, div_le_div_iff₀ (by positivity)
    (by positivity), one_mul]
  exact_mod_cast (by decide +kernel : (2 * 261888 + 1) ^ (ringDegree * 7) * 2 ^ 1794 ≤
    (2 * 524288) ^ (ringDegree * 7))

/-- **ML-DSA-44**: the average point probability bound is at most `2^-215`. -/
theorem commitPointAvgBound_mldsa44 : commitPointAvgBound _root_.MLDSA.mldsa44 ≤ (1 / 2) ^ 215 :=
  commitPointAvgBound_le_of_deltaGood_le (deltaGood_mldsa44.trans_eq (by norm_num [ringDegree]))

/-- **ML-DSA-65**: the average point probability bound is at most `2^-1025`. -/
theorem commitPointAvgBound_mldsa65 : commitPointAvgBound mldsa65 ≤ (1 / 2) ^ 1025 :=
  commitPointAvgBound_le_of_deltaGood_le (deltaGood_mldsa65.trans_eq (by norm_num [ringDegree]))

/-- **ML-DSA-87**: the average point probability bound is at most `2^-1538`. -/
theorem commitPointAvgBound_mldsa87 : commitPointAvgBound mldsa87 ≤ (1 / 2) ^ 1538 :=
  commitPointAvgBound_le_of_deltaGood_le (deltaGood_mldsa87.trans_eq (by norm_num [ringDegree]))

/-! ### Over the key seed -/

section Seed

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]
  (prims : Primitives p)

/-- **The average point probability of the commitment over honest keys**: `commitPointMax` at
the key-generation matrix `Â = ExpandA(ρ)` of a uniform seed (`GordieHowe.Lattice.keyGenMatrix`,
FIPS 204 Algorithm 6). -/
noncomputable def commitPointAt : ℝ :=
  𝔼 seed : Bytes 32, commitPointMax (GordieHowe.Lattice.keyGenMatrix p prims seed)

end Seed

end GordieHowe.MLDSA.Regularity
