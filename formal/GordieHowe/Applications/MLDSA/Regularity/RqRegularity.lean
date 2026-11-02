-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.AdmissibleBridge
public import GordieHowe.Applications.MLDSA.Regularity.CellKernel

@[expose] public section

/-!
# The regularity bound over `R_q`

Instantiates the abstract kernel average (`ZMod.sum_sum_norm_le`) at the uniform matrix
`A ∈ R_q^{k×ℓ}`, the key map `A ↦ A s₁`, masks `y` from a box of coefficient vectors, and
accept indicators that are combinations `∑_t c_t ∏_{(i,c)} g_{t,τ,(i,c), v_{i,c}}(w_{i,c})` of
products of cell functions over the coefficients of `w = A y`, and bounds the admissible kernel
masses by the averaged second moment of `SecondMoment.lean`:

- `maskOf`, `maskSlot`: the mask polynomial vector of a coefficient vector and its slot vector,
  a linear equivalence (`maskSlotEquiv`);
- `pairKernel_prod`: the pair kernel of a product family is the product of the coefficientwise
  cell kernels;
- `admissibleMass_le`: the admissible kernel mass is at most `(m (L/q)²)^N` times the averaged
  second moment of the normalized cell kernels;
- `sum_norm_regularity_le`, `sum_sq_norm_regularity_le`: the regularity bound and its `ℓ²` form.
-/

open Finset ComplexConjugate
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA

variable {k ℓ : ℕ}

/-- The mask polynomial vector of a coefficient vector `z : Fin ℓ × Fin 256 → Coeff`. -/
noncomputable def maskOf (z : Fin ℓ × Fin ringDegree → Coeff) : Fin ℓ → Rq :=
  fun b => polyOf fun c => z (b, c)

/-- The slot vector of the mask of `z`: `j ↦ b ↦ ŷ_b(j)`. -/
noncomputable def maskSlot (z : Fin ℓ × Fin ringDegree → Coeff) : Fin ringDegree → Fin ℓ → Coeff :=
  fun j b => slotVec (maskOf z b) j

theorem maskSlot_apply (z : Fin ℓ × Fin ringDegree → Coeff) (j : Fin ringDegree) (b : Fin ℓ) :
    maskSlot z j b = ∑ c, z (b, c) * slotRoot j ^ (c : ℕ) := by
  simp only [maskSlot, slotVec, slotEval, maskOf, polyOf_get]

/-- The slot transform of masks as a linear equivalence. -/
noncomputable def maskSlotEquiv :
    (Fin ℓ × Fin ringDegree → Coeff) ≃ₗ[Coeff] (Fin ringDegree → Fin ℓ → Coeff) :=
  LinearEquiv.ofBijective
    { toFun := maskSlot
      map_add' := fun z z' => by
        funext j b
        simp only [maskSlot_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a z => by
        funext j b
        simp only [maskSlot_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
    (by
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun z z' h => ?_, ?_⟩
      · funext bc
        have h1 : maskOf z bc.1 = maskOf z' bc.1 := slotVec_injective (funext fun j =>
          congrFun (congrFun h j) bc.1)
        have h2 := congrArg (fun f : Rq => f.get bc.2) h1
        simpa only [maskOf, polyOf_get] using h2
      · simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, pow_mul])

theorem maskOf_injective : Function.Injective (maskOf (ℓ := ℓ)) := by
  intro z z' h
  funext bc
  have h2 := congrArg (fun f : Rq => f.get bc.2) (congrFun h bc.1)
  simpa only [maskOf, polyOf_get] using h2

/-- The pair kernel of a product family over coordinates is the product of the coordinatewise
cell kernels. -/
theorem pairKernel_prod {N : ℕ} [NeZero N] {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (g : I → Fin m → ZMod N → ℂ) (ξ η : I → ZMod N) :
    ZMod.pairKernel (fun v : I → Fin m => fun i => g i (v i)) ξ η =
      ∏ i, ZMod.cellKernel (g i) (ξ i, η i) := by
  simp only [ZMod.pairKernel, ZMod.prodFourier, map_prod, ← Finset.prod_mul_distrib,
    ZMod.cellKernel]
  exact (Fintype.prod_sum fun i r => ZMod.fourierCoeff (g i r) (ξ i) *
    conj (ZMod.fourierCoeff (g i r) (η i))).symm

/-- The modes of `w`'s coefficients as slot modes: `μ ↦ (ξ_μ, η_μ)` is a bijection. -/
theorem modePair_bijective :
    Function.Bijective fun μ : Fin k → Fin ringDegree → Coeff × Coeff => (modeFst μ, modeSnd μ) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun μ μ' h => ?_, ?_⟩
  · funext i
    refine coeffOfSlots_injective slotRoot_injective (funext fun c => Prod.ext ?_ ?_)
    · exact congrFun (congrArg Prod.fst h) (i, c)
    · exact congrFun (congrArg Prod.snd h) (i, c)
  · exact Fintype.card_congr ((Equiv.curry _ _ _).symm.trans
      (Equiv.arrowProdEquivProdArrow _ _ _))

section Mass

variable {m : ℕ} [NeZero m] (s₁ : Fin ℓ → Rq) (S : Fin ℓ × Fin ringDegree → Finset Coeff)
  (g : Fin k × Fin ringDegree → Fin m → Coeff → ℂ) {L : ℝ}

/-- The masks of a coefficient box. -/
noncomputable def boxMasks : Finset (Fin ℓ → Rq) := (Fintype.piFinset S).image maskOf

/-- The normalized cell kernels of a cell family, by row and coefficient. -/
noncomputable def cellKernels (L : ℝ) : Fin k → Fin ringDegree → Coeff × Coeff → ℝ :=
  fun i c => normKernel (g (i, c)) L

/-- The slot vector of `s₁`. -/
noncomputable def keySlot : Fin ringDegree → Fin ℓ → Coeff := fun j b => slotVec (s₁ b) j

theorem norm_pairKernel_eq (hL : 0 < L) (μ : Fin k → Fin ringDegree → Coeff × Coeff) :
    ‖ZMod.pairKernel (fun v : Fin k × Fin ringDegree → Fin m => fun ic => g ic (v ic))
        (modeFst μ) (modeSnd μ)‖ =
      ((m : ℝ) * (L / modulus) ^ 2) ^ (k * ringDegree) * modeWeight slotRoot (cellKernels g L) μ := by
  have hN : (0 : ℝ) < modulus := by norm_num [modulus]
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hC : (0 : ℝ) < m * (L / modulus) ^ 2 := by positivity
  rw [pairKernel_prod, norm_prod, modeWeight, ← Fintype.prod_prod_type']
  rw [show ((m : ℝ) * (L / modulus) ^ 2) ^ (k * ringDegree) =
      ∏ _ic : Fin k × Fin ringDegree, ((m : ℝ) * (L / modulus) ^ 2) by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ic _ => ?_
  have hpair : coeffOfSlots slotRoot (μ ic.1) ic.2 = (modeFst μ ic, modeSnd μ ic) := rfl
  simp only [cellKernels, normKernel, Fintype.card_fin]
  rw [hpair]
  field_simp

theorem modeFst_zero : modeFst (0 : Fin k → Fin ringDegree → Coeff × Coeff) = 0 := by
  funext ic
  simp [modeFst, coeffOfSlots_zero]

open Classical in
/-- **The admissible kernel mass is the averaged second moment**, up to the normalization
`(m (L/q)²)^N`: for masks from a coefficient box and a product cell family. -/
theorem admissibleMass_le (hL : 0 < L) (τ : Fin k → Rq) :
    ZMod.admissibleMass (keyMap (k := k) s₁) (boxMasks S) matAct
        (fun _ (v : Fin k × Fin ringDegree → Fin m) ic => g ic (v ic)) τ ≤
      ((m : ℝ) * (L / modulus) ^ 2) ^ (k * ringDegree) *
        averagedSecondMoment maskSlotEquiv S slotRoot (cellKernels g L) (keySlot s₁) 0 := by
  set C : ℝ := ((m : ℝ) * (L / modulus) ^ 2) ^ (k * ringDegree)
  have hN : (0 : ℝ) < modulus := by norm_num [modulus]
  have hC : 0 ≤ C := by positivity
  set B := Fintype.piFinset S
  set E := (univ : Finset (Fin k × Fin ringDegree → Coeff)).erase 0
  set G : (Fin k × Fin ringDegree → Fin m) → Fin k × Fin ringDegree → Coeff → ℂ :=
    fun v ic => g ic (v ic)
  -- per pair of masks
  have hpair : ∀ y y' : Fin ℓ → Rq,
      ∑ ξ ∈ E, ∑ η ∈ E, (if ZMod.Admissible (keyMap (k := k) s₁) matAct y y' ξ η then
        ‖ZMod.pairKernel G ξ η‖ else 0) ≤
      C * secondMoment slotRoot (cellKernels g L) (keySlot s₁) (fun j b => slotVec (y b) j)
        (fun j b => slotVec (y' b) j) := by
    intro y y'
    set f : (Fin k × Fin ringDegree → Coeff) × (Fin k × Fin ringDegree → Coeff) → ℝ := fun p =>
      if p.1 ≠ 0 ∧ p.2 ≠ 0 then
        (if ZMod.Admissible (keyMap (k := k) s₁) matAct y y' p.1 p.2 then
          ‖ZMod.pairKernel G p.1 p.2‖ else 0) else 0
    have hE : ∀ h : (Fin k × Fin ringDegree → Coeff) → ℝ,
        ∑ x ∈ E, h x = ∑ x, if x ≠ 0 then h x else 0 := by
      intro h
      rw [← Finset.sum_filter, Finset.filter_ne']
    have h1 : ∑ ξ ∈ E, ∑ η ∈ E, (if ZMod.Admissible (keyMap (k := k) s₁) matAct y y' ξ η then
        ‖ZMod.pairKernel G ξ η‖ else 0) = ∑ p, f p := by
      rw [hE, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      by_cases hξ : ξ = 0
      · simp [hξ, f]
      · rw [if_pos hξ, hE]
        refine Finset.sum_congr rfl fun η _ => ?_
        by_cases hη : η = 0
        · simp [hη, f]
        · simp only [f, ne_eq, hξ, hη, not_false_eq_true, and_self, if_true]
    have h2 : ∑ p, f p = ∑ μ : Fin k → Fin ringDegree → Coeff × Coeff,
        f (modeFst μ, modeSnd μ) :=
      (Fintype.sum_bijective _ modePair_bijective _ _ fun _ => rfl).symm
    have h3 : ∀ μ : Fin k → Fin ringDegree → Coeff × Coeff, f (modeFst μ, modeSnd μ) ≤
        C * (if μ ≠ 0 ∧ Admissible (keySlot s₁) (fun j b => slotVec (y b) j)
          (fun j b => slotVec (y' b) j) μ then modeWeight slotRoot (cellKernels g L) μ else 0) := by
      intro μ
      simp only [f]
      by_cases h0 : modeFst μ ≠ 0 ∧ modeSnd μ ≠ 0
      · rw [if_pos h0]
        by_cases hA : ZMod.Admissible (keyMap (k := k) s₁) matAct y y' (modeFst μ) (modeSnd μ)
        · have hμ : μ ≠ 0 := fun h => h0.1 (by rw [h, modeFst_zero])
          rw [if_pos hA, if_pos ⟨hμ, slotAdmissible_of_admissible s₁ y y' μ hA⟩]
          exact le_of_eq (norm_pairKernel_eq g hL μ)
        · rw [if_neg hA]
          split_ifs
          · exact mul_nonneg hC (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun c _ =>
              normKernel_nonneg _ hL _)
          · rw [mul_zero]
      · rw [if_neg h0]
        split_ifs
        · exact mul_nonneg hC (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun c _ =>
            normKernel_nonneg _ hL _)
        · rw [mul_zero]
    rw [h1, h2]
    refine (Finset.sum_le_sum fun μ _ => h3 μ).trans (le_of_eq ?_)
    rw [secondMoment, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp
  have hinj : Set.InjOn maskOf (B : Set (Fin ℓ × Fin ringDegree → Coeff)) :=
    fun c _ c' _ h => maskOf_injective h
  have hcard : #(boxMasks S) = #B := Finset.card_image_of_injective _ maskOf_injective
  have hswap : ∀ (X : (Fin ℓ → Rq) → (Fin ℓ → Rq) → (Fin k × Fin ringDegree → Coeff) →
      (Fin k × Fin ringDegree → Coeff) → ℝ),
      ∑ ξ ∈ E, ∑ η ∈ E, ∑ z ∈ boxMasks S, ∑ z' ∈ boxMasks S, X z z' ξ η =
        ∑ z ∈ boxMasks S, ∑ z' ∈ boxMasks S, ∑ ξ ∈ E, ∑ η ∈ E, X z z' ξ η := by
    intro X
    calc ∑ ξ ∈ E, ∑ η ∈ E, ∑ z ∈ boxMasks S, ∑ z' ∈ boxMasks S, X z z' ξ η
        = ∑ ξ ∈ E, ∑ z ∈ boxMasks S, ∑ η ∈ E, ∑ z' ∈ boxMasks S, X z z' ξ η :=
          Finset.sum_congr rfl fun ξ _ => Finset.sum_comm
      _ = ∑ ξ ∈ E, ∑ z ∈ boxMasks S, ∑ z' ∈ boxMasks S, ∑ η ∈ E, X z z' ξ η :=
          Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = ∑ z ∈ boxMasks S, ∑ ξ ∈ E, ∑ z' ∈ boxMasks S, ∑ η ∈ E, X z z' ξ η := Finset.sum_comm
      _ = ∑ z ∈ boxMasks S, ∑ z' ∈ boxMasks S, ∑ ξ ∈ E, ∑ η ∈ E, X z z' ξ η :=
          Finset.sum_congr rfl fun z _ => Finset.sum_comm
  set κ : ℝ := ((#(boxMasks S) : ℝ) ^ 2)⁻¹
  have hκ : 0 ≤ κ := by positivity
  have hB0 : (#B : ℝ) * #B = (#(boxMasks S) : ℝ) ^ 2 := by rw [hcard, sq]
  unfold ZMod.admissibleMass
  calc ∑ ξ ∈ E, ∑ η ∈ E, κ * ∑ z ∈ boxMasks S, ∑ z' ∈ boxMasks S,
        (if ZMod.Admissible (keyMap (k := k) s₁) matAct z z' ξ η then
          ‖ZMod.pairKernel ((fun _ (v : Fin k × Fin ringDegree → Fin m) ic => g ic (v ic)) τ) ξ η‖
        else 0)
      = κ * ∑ z ∈ boxMasks S, ∑ z' ∈ boxMasks S, ∑ ξ ∈ E, ∑ η ∈ E,
          (if ZMod.Admissible (keyMap (k := k) s₁) matAct z z' ξ η then
            ‖ZMod.pairKernel G ξ η‖ else 0) := by
        rw [← hswap]
        simp only [Finset.mul_sum]
        rfl
    _ ≤ κ * ∑ z ∈ boxMasks S, ∑ z' ∈ boxMasks S, C * secondMoment slotRoot (cellKernels g L)
          (keySlot s₁) (fun j b => slotVec (z b) j) (fun j b => slotVec (z' b) j) := by
        gcongr with z _ z' _
        exact hpair z z'
    _ = C * averagedSecondMoment maskSlotEquiv S slotRoot (cellKernels g L) (keySlot s₁) 0 := by
        have hF : ∀ H : (Fin ℓ → Rq) → ℝ, ∑ z ∈ boxMasks S, H z = ∑ c ∈ B, H (maskOf c) :=
          fun H => Finset.sum_image hinj
        have hE : ∀ c, maskSlotEquiv c - 0 = maskSlot (ℓ := ℓ) c := fun c => by
          rw [sub_zero]; exact LinearEquiv.ofBijective_apply _ _
        rw [hF]
        simp_rw [hF]
        rw [averagedSecondMoment, Finset.sum_product, hB0]
        simp only [hE]
        simp_rw [← Finset.mul_sum]
        simp only [κ]
        rw [div_eq_mul_inv, mul_comm _ (_ ^ 2)⁻¹, ← mul_assoc, mul_comm _ C, mul_assoc]
        rfl

/-- **The regularity bound over `R_q`.** For masks from a nonempty coefficient box, cell families
`gfam t τ (i, c) r` of every expansion term `t` and key value `τ = A s₁`, and a bound `Env` on
the averaged second moment of their normalized cell kernels,
`∑_A ∑_v ‖∑_t c_t D_{t,A}(v)‖ ≤ |𝒜| · Λ · (m L / q)^(256 k) · √Env`. The shift `c₀` (the `c s₂`
term of `w = A y - c s₂`) is arbitrary. -/
theorem sum_norm_regularity_le {R : Type*} [Fintype R] (hS : (Fintype.piFinset S).Nonempty)
    (c : R → ℂ) (gfam : R → (Fin k → Rq) → Fin k × Fin ringDegree → Fin m → Coeff → ℂ)
    (hL : 0 < L) (c₀ : Fin k × Fin ringDegree → Coeff) {Env : ℝ} (hEnv0 : 0 ≤ Env)
    (hEnv : ∀ t τ, averagedSecondMoment maskSlotEquiv S slotRoot (cellKernels (gfam t τ) L)
      (keySlot s₁) 0 ≤ Env) :
    ∑ A, ∑ v, ‖∑ t, c t * ZMod.maskDiff (keyMap (k := k) s₁) (boxMasks S) matAct c₀
        (fun τ (v : Fin k × Fin ringDegree → Fin m) ic => gfam t τ ic (v ic)) A v‖ ≤
      Fintype.card (Fin k → Fin ℓ → Rq) * (∑ t, ‖c t‖) *
        ((m * L / modulus) ^ (k * ringDegree) * √Env) := by
  set C : ℝ := ((m : ℝ) * (L / modulus) ^ 2) ^ (k * ringDegree)
  have hN : (0 : ℝ) < modulus := by norm_num [modulus]
  have hC : 0 ≤ C := by positivity
  have hZ : (boxMasks S).Nonempty := hS.image _
  have h := ZMod.sum_sum_norm_le (keyMap (k := k) s₁) (boxMasks S) hZ matAct c₀ c
    (fun t τ (v : Fin k × Fin ringDegree → Fin m) ic => gfam t τ ic (v ic)) (B := C * Env)
    fun t τ =>
      (admissibleMass_le s₁ S (gfam t τ) hL τ).trans (mul_le_mul_of_nonneg_left (hEnv t τ) hC)
  refine h.trans (le_of_eq ?_)
  congr 1
  have hV : (Fintype.card (Fin k × Fin ringDegree → Fin m) : ℝ) = (m : ℝ) ^ (k * ringDegree) := by
    simp [Fintype.card_prod]
  rw [hV, ← mul_assoc, show (m : ℝ) ^ (k * ringDegree) * C =
      ((m * L / modulus) ^ (k * ringDegree)) ^ 2 by
    simp only [C]
    ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- **The regularity bound over `R_q`, `ℓ²` form.** Under the hypotheses of
`sum_norm_regularity_le`,
`∑_A (∑_v ‖∑_t c_t D_{t,A}(v)‖)² ≤ |𝒜| · (Λ · (m L / q)^(256 k) · √Env)²`. -/
theorem sum_sq_norm_regularity_le {R : Type*} [Fintype R] (hS : (Fintype.piFinset S).Nonempty)
    (c : R → ℂ) (gfam : R → (Fin k → Rq) → Fin k × Fin ringDegree → Fin m → Coeff → ℂ)
    (hL : 0 < L) (c₀ : Fin k × Fin ringDegree → Coeff) {Env : ℝ} (hEnv0 : 0 ≤ Env)
    (hEnv : ∀ t τ, averagedSecondMoment maskSlotEquiv S slotRoot (cellKernels (gfam t τ) L)
      (keySlot s₁) 0 ≤ Env) :
    ∑ A, (∑ v, ‖∑ t, c t * ZMod.maskDiff (keyMap (k := k) s₁) (boxMasks S) matAct c₀
        (fun τ (v : Fin k × Fin ringDegree → Fin m) ic => gfam t τ ic (v ic)) A v‖) ^ 2 ≤
      Fintype.card (Fin k → Fin ℓ → Rq) *
        ((∑ t, ‖c t‖) * ((m * L / modulus) ^ (k * ringDegree) * √Env)) ^ 2 := by
  set C : ℝ := ((m : ℝ) * (L / modulus) ^ 2) ^ (k * ringDegree)
  have hN : (0 : ℝ) < modulus := by norm_num [modulus]
  have hC : 0 ≤ C := by positivity
  have hZ : (boxMasks S).Nonempty := hS.image _
  have h := ZMod.sum_sq_sum_norm_le (keyMap (k := k) s₁) (boxMasks S) hZ matAct c₀ c
    (fun t τ (v : Fin k × Fin ringDegree → Fin m) ic => gfam t τ ic (v ic)) (B := C * Env)
    fun t τ =>
      (admissibleMass_le s₁ S (gfam t τ) hL τ).trans (mul_le_mul_of_nonneg_left (hEnv t τ) hC)
  refine h.trans (le_of_eq ?_)
  congr 1
  have hV : (Fintype.card (Fin k × Fin ringDegree → Fin m) : ℝ) = (m : ℝ) ^ (k * ringDegree) := by
    simp [Fintype.card_prod]
  rw [hV, mul_pow, mul_pow, Real.sq_sqrt hEnv0]
  simp only [C]
  ring

end Mass

end GordieHowe.MLDSA.Regularity
