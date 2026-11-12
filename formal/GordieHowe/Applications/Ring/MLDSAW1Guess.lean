-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Anonymity
public import GordieHowe.Applications.MLDSA.Regularity.Instances
public import GordieHowe.Foundations.ToMathlib.PMFFiber

@[expose] public section

/-!
# Guessing a signature of the fresh-mask w₁ signer from its public value

The guessing probability `γ` of `BaseSigner.SigGivenPubAvgLe` (the average conditional min-entropy
of Dodis, Ostrovsky, Reyzin, Smith, "Fuzzy Extractors", SIAM J. Comput. 38(1), 2008, section 2.4)
for the base signer of the ML-DSA ring publishing `w₁` with fresh masks (`freshBase`,
`MLDSAW1Anonymity.lean`), at every oracle. A signature `σ = (c̃, z, h)` with `z = y + c·s₁` fixes
its mask `y` (`mask_eq_of_attemptOutput_eq`); each of the at most `k · T` masks a run draws is
uniform on `MaskBox p` when the mask decoding is (`hMask`); so one signature has probability at
most `k · T / |MaskBox p|`, and the sum over the public values `w₁ ∈ BucketVec p` is at most
`k · T · |BucketVec p| / |MaskBox p|`.

- `mask_eq_of_attemptOutput_eq`: the attempt output determines its mask.
- `PMF.toOuterMeasure_le_card_div_of_exists_eq`: an event on which one of `|ι|` uniform values is a
  fixed point has probability at most `|ι| / |Z|`.
- `pr_eq_some_le_of_masks`, `sum_iSup_pr_le_of_masks`: an output that is the attempt output of one
  of `|ι|` uniform masks is one signature with probability at most `|ι| / |MaskBox p|`; the sum
  over the commitments of the largest such probability is at most
  `|ι| · |BucketVec p| / |MaskBox p|`.
- `map_uniform_freshCoins_eq`: under uniform coins of the fresh loop, each decoded mask is uniform.
- `pr_bsign_freshBase_le`, `sigGivenPubAvgLe_freshBase`: **the fresh-mask base signer** outputs one
  signature with probability at most `k · T / |MaskBox p|` and satisfies
  `SigGivenPubAvgLe (k · T · |BucketVec p| / |MaskBox p|)`.
- `pr_ssign_freshBase_le`, `sum_iSup_pr_ssign_freshBase_le`: **one call (`T` attempts)**, the
  ordinary signer (`stdProg` at `MaskSource.fresh`): one signature with probability at most
  `T / |MaskBox p|`, and the guessing sum from `w₁` at most `T · |BucketVec p| / |MaskBox p|`.
- `card_bucketVec`: `|BucketVec p| = bucketCount p ^ (k · 256)` (with `card_maskBox`,
  `|MaskBox p| = (2γ₁) ^ (256 · l)` when `2γ₁ < q`). `ENNReal.natCast_div_le_inv_two_pow`: a ratio
  `a / c` of natural numbers with `a · 2^b ≤ c` is at most `2^(-b)`.
  `card_bucketVec_div_card_maskBox_mldsa44`, `card_bucketVec_div_card_maskBox_mldsa65`,
  `card_bucketVec_div_card_maskBox_mldsa87`: the ratio `|BucketVec p| / |MaskBox p|` at the three
  parameter sets.

The hypothesis `hMask` (the mask decoding pushes the uniform law on `Y` to the uniform law on the
mask box) is the one of the anonymity headlines; the decoding `satMask` of `SatY p` satisfies it
(`map_satMask`, `MLDSAW1IdealDist.lean`).
-/

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature
open scoped ENNReal

/-! ### Uniform values at a fixed point -/

namespace PMF

/-- **An event on which one of `|ι|` uniform values is a fixed point** has probability at most
`|ι| / |Z|`: the union bound over `ι`, each value being `z₀` with probability `1 / |Z|`. -/
theorem toOuterMeasure_le_card_div_of_exists_eq {C ι Z : Type*} [Fintype ι] [Fintype Z]
    [Nonempty Z] (μ : PMF C) (F : ι → C → Z) (hF : ∀ j, μ.map (F j) = uniformOfFintype Z)
    (z₀ : Z) {E : Set C} (hE : ∀ c ∈ E, ∃ j, F j c = z₀) :
    μ.toOuterMeasure E ≤ Fintype.card ι / Fintype.card Z := by
  calc μ.toOuterMeasure E ≤ μ.toOuterMeasure (⋃ j, F j ⁻¹' {z₀}) :=
        μ.toOuterMeasure_mono fun c hc => Set.mem_iUnion.2 (hE c hc.1)
    _ ≤ ∑ j, μ.toOuterMeasure (F j ⁻¹' {z₀}) := MeasureTheory.measure_iUnion_fintype_le _ _
    _ = ∑ _j : ι, (Fintype.card Z : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← toOuterMeasure_map_apply, hF j, toOuterMeasure_apply_singleton,
          uniformOfFintype_apply]
    _ = Fintype.card ι / Fintype.card Z := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

end PMF

namespace GordieHowe.Ring.MLDSAW1

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The attempt output fixes its mask -/

section Mask

variable (prims : Primitives p) [nttOps : NTTRingOps]

/-- **The attempt output determines its mask**: `(c̃, y + c·s₁, h) = (c̃', y' + c'·s₁, h')` gives
`c̃ = c̃'`, so `c = c'`, and then `y = y'`. -/
theorem mask_eq_of_attemptOutput_eq {sk : SecretKey p} {aHat : TqMatrix p.k p.l}
    {y y' : MaskBox p} {c c' : CommitHashBytes p}
    (h : attemptOutput prims sk aHat (y, c) = attemptOutput prims sk aHat (y', c')) : y = y' := by
  have hc : c = c' := congrArg FIPSSignature.cTilde h
  subst hc
  have hz := congrArg FIPSSignature.z h
  dsimp only [attemptOutput] at hz
  refine Subtype.ext (Vector.ext fun j hj => ?_)
  have hj' := congrArg (fun v : RqVec p.l => v[j]) hz
  simp only [Vector.getElem_add] at hj'
  ext i
  have hi := congrArg (fun r : Rq => coeffRing.backend.coeff r i) hj'
  simp only [LatticeCrypto.NegacyclicRing.coeff_add] at hi
  exact add_right_cancel hi

variable [Nonempty (MaskBox p)]

/-- **An output that is the attempt output of one of `|ι|` uniform masks is one signature with
probability at most `|ι| / |MaskBox p|`**: for coins `c` uniform on `C`, if every signature
`out c` outputs is `attemptOutput (F j c, c̃)` for some `j` and `c̃`, and each `F j` pushes the
uniform law on `C` to the uniform law on the mask box. -/
theorem pr_eq_some_le_of_masks {C ι : Type*} [Fintype C] [Nonempty C] [Fintype ι]
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (out : C → Option (FIPSSignature p prims))
    (F : ι → C → MaskBox p)
    (hF : ∀ j, (PMF.uniformOfFintype C).map (F j) = PMF.uniformOfFintype (MaskBox p))
    (hout : ∀ c σ, out c = some σ → ∃ j cTilde, σ = attemptOutput prims sk aHat (F j c, cTilde))
    (σ : FIPSSignature p prims) :
    Pr[c ~ PMF.uniformOfFintype C : out c = some σ] ≤
      Fintype.card ι / Fintype.card (MaskBox p) := by
  by_cases hne : ∃ c₀, out c₀ = some σ
  · obtain ⟨c₀, h₀⟩ := hne
    obtain ⟨j₀, c₀', hσ₀⟩ := hout c₀ σ h₀
    refine PMF.toOuterMeasure_le_card_div_of_exists_eq _ F hF (F j₀ c₀) fun c hc => ?_
    obtain ⟨j, c', hσ⟩ := hout c σ hc
    exact ⟨j, mask_eq_of_attemptOutput_eq prims (hσ.symm.trans hσ₀)⟩
  · push Not at hne
    have hempty : (Set.ofPred fun c => out c = some σ) = ∅ :=
      Set.eq_empty_of_forall_notMem fun c hc => hne c hc
    rw [hempty, MeasureTheory.measure_empty]
    exact zero_le

/-- **The guessing sum of such an output from a commitment**: the sum over the commitments
`y ∈ BucketVec p` of the largest probability that `out` outputs one signature `σ` with
`pub σ = y` is at most `|ι| · |BucketVec p| / |MaskBox p|` (`pr_eq_some_le_of_masks`). -/
theorem sum_iSup_pr_le_of_masks {C ι : Type*} [Fintype C] [Nonempty C] [Fintype ι]
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (out : C → Option (FIPSSignature p prims))
    (F : ι → C → MaskBox p)
    (hF : ∀ j, (PMF.uniformOfFintype C).map (F j) = PMF.uniformOfFintype (MaskBox p))
    (hout : ∀ c σ, out c = some σ → ∃ j cTilde, σ = attemptOutput prims sk aHat (F j c, cTilde))
    (pub : FIPSSignature p prims → BucketVec p) :
    ∑ y : BucketVec p, ⨆ σ : FIPSSignature p prims,
        Pr[c ~ PMF.uniformOfFintype C : out c = some σ ∧ pub σ = y] ≤
      Fintype.card ι * Fintype.card (BucketVec p) / Fintype.card (MaskBox p) := by
  calc ∑ y : BucketVec p, ⨆ σ : FIPSSignature p prims,
        Pr[c ~ PMF.uniformOfFintype C : out c = some σ ∧ pub σ = y]
      ≤ ∑ _y : BucketVec p, (Fintype.card ι / Fintype.card (MaskBox p) : ℝ≥0∞) :=
        Finset.sum_le_sum fun y _ => iSup_le fun σ =>
          ((PMF.uniformOfFintype C).toOuterMeasure_mono fun c hc => hc.1.1).trans
            (pr_eq_some_le_of_masks prims sk aHat out F hF hout σ)
    _ = Fintype.card ι * Fintype.card (BucketVec p) / Fintype.card (MaskBox p) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [div_eq_mul_inv]
        ring

end Mask

/-! ### The fresh-mask base signer -/

section Fresh

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

omit [NeZero (bucketCount p)] nttOps [DecidableEq Y] in
/-- **The mask of one point of one call is uniform**: under uniform coins of the fresh loop, the
decoding of the mask function of call `c` at the point `u` is uniform on the mask box, for a mask
decoding pushing the uniform law to the uniform law (`hMask`). -/
theorem map_uniform_freshCoins_eq
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p)) (c : Fin k)
    (u : MaskPt T Msg) :
    (PMF.uniformOfFintype ((Fin k → MaskPt T Msg → Y) × (Fin k → Fin D))).map
        (fun cb => M.ans (cb.1 c u)) = PMF.uniformOfFintype (MaskBox p) := by
  classical
  have h : (fun cb : (Fin k → MaskPt T Msg → Y) × (Fin k → Fin D) => M.ans (cb.1 c u)) =
      M.ans ∘ (fun g : MaskPt T Msg → Y => g u) ∘ (fun f : Fin k → MaskPt T Msg → Y => f c) ∘
        Prod.fst := rfl
  rw [h, ← PMF.map_comp, ← PMF.map_comp, ← PMF.map_comp, PMF.map_fst_uniformOfFintype,
    PMF.uniformOfFintype_map_eval, PMF.uniformOfFintype_map_eval, hMask]

/-- **The fresh-mask base signer outputs one signature with probability at most
`k · T / |MaskBox p|`**: at every oracle, for every secret key, ring, position, message and
signature, for a uniform mask decoding (`hMask`). Each signature is the attempt output of one of
the `k · T` masks of the run (`run_bsign_w1BaseSigner`, `exists_index_of_loopOut_eq_some`). -/
theorem pr_bsign_freshBase_le
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p)) (H : X → Y)
    (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : ℕ) (m : RMsg)
    (σ : FIPSSignature p prims) :
    Pr[c ~ PMF.uniformOfFintype (freshBase prims O M βmin tol enc k D bmsg).Coins :
        ((freshBase prims O M βmin tol enc k D bmsg).bsign sk R i m c).run H = some σ] ≤
      (k * T : ℝ≥0∞) / Fintype.card (MaskBox p) := by
  have hcard : ((k * T : ℕ) : ℝ≥0∞) = k * T := by push_cast; rfl
  have h := pr_eq_some_le_of_masks prims (ι := Fin k × Fin T) sk (prims.expandA sk.rho)
    (fun c => ((freshBase prims O M βmin tol enc k D bmsg).bsign sk R i m c).run H)
    (fun j cb => M.ans (cb.1 j.1 (j.2, (sk.key, (sk.tr, bmsg R m)))))
    (fun j => map_uniform_freshCoins_eq M k D hMask j.1 _) (fun cb σ' hσ' => by
      have hrun := (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M) k D bmsg sk R
        i m cb H).symm.trans hσ'
      split_ifs at hrun with hok hi
      obtain ⟨c, t, hσ⟩ := exists_index_of_loopOut_eq_some prims hrun
      exact ⟨(c, t), _, hσ⟩) σ
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hcard] at h
  exact h

/-- **Guessing a signature of the fresh-mask base signer from its public value**: the fresh-mask
base signer satisfies `SigGivenPubAvgLe (k · T · |BucketVec p| / |MaskBox p|)` at every oracle,
for a uniform mask decoding (`hMask`, satisfied by `satMask`, `map_satMask`): the public value
`w₁ ∈ BucketVec p` takes `|BucketVec p|` values, and each signature has probability at most
`k · T / |MaskBox p|` (`pr_bsign_freshBase_le`). -/
theorem sigGivenPubAvgLe_freshBase
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p)) :
    (freshBase prims O M βmin tol enc k D bmsg).SigGivenPubAvgLe
      (k * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p)) := by
  intro H kc R i _ m
  calc ∑ y : BucketVec p, ⨆ σ : FIPSSignature p prims,
        Pr[c ~ PMF.uniformOfFintype (freshBase prims O M βmin tol enc k D bmsg).Coins :
          ((freshBase prims O M βmin tol enc k D bmsg).bsign
            ((freshBase prims O M βmin tol enc k D bmsg).sk kc) R i m c).run H = some σ ∧
          ((freshBase prims O M βmin tol enc k D bmsg).pub
            ((freshBase prims O M βmin tol enc k D bmsg).pk kc) σ).run H = y]
      ≤ ∑ _y : BucketVec p, ((k * T : ℝ≥0∞) / Fintype.card (MaskBox p)) :=
        Finset.sum_le_sum fun y _ => iSup_le fun σ =>
          (PMF.toOuterMeasure_mono _ fun c hc => hc.1.1).trans
            (pr_bsign_freshBase_le prims O M βmin tol enc k D bmsg hMask H _ R i m σ)
    _ = k * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [div_eq_mul_inv]
        ring

/-- **One call (`T` attempts): the ordinary signer with fresh masks outputs one signature with
probability at most `T / |MaskBox p|`**: at every oracle, for every secret key, base message and
signature, the ordinary signer of the fresh-mask base signer (`stdProg` at `MaskSource.fresh`, the
`T` masks of the first call) under uniform coins, for a uniform mask decoding (`hMask`). -/
theorem pr_ssign_freshBase_le
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p)) (H : X → Y)
    (sk : SecretKey p) (bm : Msg) (σ : FIPSSignature p prims) :
    Pr[c ~ PMF.uniformOfFintype (freshBase prims O M βmin tol enc k D bmsg).Coins :
        ((freshBase prims O M βmin tol enc k D bmsg).ssign sk bm c).run H = some σ] ≤
      (T : ℝ≥0∞) / Fintype.card (MaskBox p) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hempty : (Set.ofPred fun c : (freshBase prims O M βmin tol enc 0 D bmsg).Coins =>
        ((freshBase prims O M βmin tol enc 0 D bmsg).ssign sk bm c).run H = some σ) = ∅ :=
      Set.eq_empty_of_forall_notMem fun c hc => by
        obtain ⟨hk, -⟩ := exists_index_of_run_stdProg_eq_some prims (MaskSource.fresh M)
          O.toMLDSAOracles 0 sk bm c.1 H
          (by simpa only [w1BaseSigner, w1BaseSignerOf, mldsaT0BaseScheme, W1Loop.stdSigner,
              ringLoop, ringLoopOf,
            Set.mem_setOf_eq] using hc)
        exact absurd hk (lt_irrefl 0)
    rw [hempty, MeasureTheory.measure_empty]
    exact zero_le
  · have h := pr_eq_some_le_of_masks prims (ι := Fin T) sk (prims.expandA sk.rho)
      (fun c => ((freshBase prims O M βmin tol enc k D bmsg).ssign sk bm c).run H)
      (fun t cb => M.ans (cb.1 ⟨0, hk⟩ (t, (sk.key, (sk.tr, bm)))))
      (fun t => map_uniform_freshCoins_eq M k D hMask _ _) (fun cb σ' hσ' => by
        obtain ⟨hk', t, c', hσ⟩ := exists_index_of_run_stdProg_eq_some prims (MaskSource.fresh M)
          O.toMLDSAOracles k sk bm cb.1 H
          (by simpa only [w1BaseSigner, w1BaseSignerOf, mldsaT0BaseScheme, W1Loop.stdSigner,
              ringLoop, ringLoopOf] using hσ')
        exact ⟨t, c', hσ⟩) σ
    rwa [Fintype.card_fin] at h

/-- **One call (`T` attempts): guessing a signature of the ordinary signer with fresh masks from its
`w₁`**: the sum over `y ∈ BucketVec p` of the largest probability that the ordinary signer of the
fresh-mask base signer outputs one signature with public value `w₁ = y` is at most
`T · |BucketVec p| / |MaskBox p|`, at every oracle, secret key, public key and base message, for a
uniform mask decoding (`hMask`; `pr_ssign_freshBase_le`). -/
theorem sum_iSup_pr_ssign_freshBase_le
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p)) (H : X → Y)
    (sk : SecretKey p) (pk : PubKey p prims) (bm : Msg) :
    ∑ y : BucketVec p, ⨆ σ : FIPSSignature p prims,
        Pr[c ~ PMF.uniformOfFintype (freshBase prims O M βmin tol enc k D bmsg).Coins :
          ((freshBase prims O M βmin tol enc k D bmsg).ssign sk bm c).run H = some σ ∧
          ((freshBase prims O M βmin tol enc k D bmsg).pub pk σ).run H = y] ≤
      T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p) := by
  calc ∑ y : BucketVec p, ⨆ σ : FIPSSignature p prims,
        Pr[c ~ PMF.uniformOfFintype (freshBase prims O M βmin tol enc k D bmsg).Coins :
          ((freshBase prims O M βmin tol enc k D bmsg).ssign sk bm c).run H = some σ ∧
          ((freshBase prims O M βmin tol enc k D bmsg).pub pk σ).run H = y]
      ≤ ∑ _y : BucketVec p, ((T : ℝ≥0∞) / Fintype.card (MaskBox p)) :=
        Finset.sum_le_sum fun y _ => iSup_le fun σ =>
          (PMF.toOuterMeasure_mono _ fun c hc => hc.1.1).trans
            (pr_ssign_freshBase_le prims O M βmin tol enc k D bmsg hMask H sk bm σ)
    _ = T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [div_eq_mul_inv]
        ring

end Fresh

/-! ### The number of commitments and of masks -/

/-- **`|BucketVec p| = bucketCount p ^ (k · 256)`**: one of `bucketCount p` buckets for each of the
`k · 256` coefficients of `w ∈ R_q^k`. -/
theorem card_bucketVec (p : Params) [NeZero (bucketCount p)] :
    Fintype.card (BucketVec p) = bucketCount p ^ (p.k * ringDegree) :=
  GordieHowe.MLDSA.card_bucketVec p

/-- A ratio `a / c` of natural numbers is at most `2^(-b)` when `a · 2^b ≤ c`. -/
theorem _root_.ENNReal.natCast_div_le_inv_two_pow {a c b : ℕ} (h : a * 2 ^ b ≤ c) :
    (a : ℝ≥0∞) / c ≤ (2 ^ b)⁻¹ := by
  have h2 : (2 : ℝ≥0∞) ^ b ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ b ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  refine ENNReal.div_le_of_le_mul ?_
  calc (a : ℝ≥0∞) = a * 2 ^ b * (2 ^ b)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel h2 h2', mul_one]
    _ ≤ c * (2 ^ b)⁻¹ := by
        gcongr
        exact_mod_cast h
    _ = (2 ^ b)⁻¹ * c := mul_comm _ _

/-- **At ML-DSA-44, `|BucketVec p| / |MaskBox p| = 44^1024 / 2^18432 ≤ 2^-12841`**:
`44^1024 · 2^12841 ≤ 2^18432`. -/
theorem card_bucketVec_div_card_maskBox_mldsa44 :
    (Fintype.card (BucketVec _root_.MLDSA.mldsa44) : ℝ≥0∞) /
        Fintype.card (MaskBox _root_.MLDSA.mldsa44) ≤ (2 ^ 12841)⁻¹ := by
  refine ENNReal.natCast_div_le_inv_two_pow ?_
  rw [card_bucketVec, card_maskBox (by rw [mldsa44_vals.2.2.1]; norm_num [modulus]),
    bucketCount_mldsa44, mldsa44_vals.1, mldsa44_vals.2.1, mldsa44_vals.2.2.1, ringDegree]
  set_option exponentiation.threshold 20000 in norm_num

/-- **At ML-DSA-65, `|BucketVec p| / |MaskBox p| = 16^1536 / 2^25600 = 2^-19456`.** -/
theorem card_bucketVec_div_card_maskBox_mldsa65 :
    (Fintype.card (BucketVec mldsa65) : ℝ≥0∞) / Fintype.card (MaskBox mldsa65) ≤
      (2 ^ 19456)⁻¹ := by
  refine ENNReal.natCast_div_le_inv_two_pow (le_of_eq ?_)
  rw [card_bucketVec, card_maskBox (by rw [mldsa65_vals.2.2.1]; norm_num [modulus]),
    bucketCount_mldsa65, mldsa65_vals.1, mldsa65_vals.2.1, mldsa65_vals.2.2.1, ringDegree,
    show (16 : ℕ) = 2 ^ 4 by rfl, show (2 * 524288 : ℕ) = 2 ^ 20 by rfl, ← pow_mul, ← pow_mul,
    ← pow_add]

/-- **At ML-DSA-87, `|BucketVec p| / |MaskBox p| = 16^2048 / 2^35840 = 2^-27648`.** -/
theorem card_bucketVec_div_card_maskBox_mldsa87 :
    (Fintype.card (BucketVec mldsa87) : ℝ≥0∞) / Fintype.card (MaskBox mldsa87) ≤
      (2 ^ 27648)⁻¹ := by
  refine ENNReal.natCast_div_le_inv_two_pow (le_of_eq ?_)
  rw [card_bucketVec, card_maskBox (by rw [mldsa87_vals.2.2.1]; norm_num [modulus]),
    bucketCount_mldsa87, mldsa87_vals.1, mldsa87_vals.2.1, mldsa87_vals.2.2.1, ringDegree,
    show (16 : ℕ) = 2 ^ 4 by rfl, show (2 * 524288 : ℕ) = 2 ^ 20 by rfl, ← pow_mul, ← pow_mul,
    ← pow_add]

end GordieHowe.Ring.MLDSAW1
