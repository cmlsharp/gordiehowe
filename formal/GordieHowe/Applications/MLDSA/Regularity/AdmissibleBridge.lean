-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.SlotTransform
public import GordieHowe.Applications.MLDSA.Regularity.SecondMoment
public import GordieHowe.Foundations.ToMathlib.CharacterSecondMoment

@[expose] public section

/-!
# From the kernel average over `A` to the slot annihilators

The matrix `A ∈ R_q^{k×ℓ}` acts on masks `y ∈ R_q^ℓ` by `A ↦ A y` (`matAct`, read as the
coefficient vector of `A y`) and is seen by the accept indicator only through `A s₁`
(`keyMap`). A pair of Fourier modes `(ξ, η)` on the coefficients of `w` survives the average of
`A` on the cosets of `ker (A ↦ A s₁)` (`ZMod.Admissible`) only if, at every slot `j` and row `i`,
the dual coordinates `(α_i(j), β_i(j))` lie in the slot annihilator
`{(a, b) | a x̂(j) - b x̂'(j) ∈ span ŝ₁(j)}` (`slotAdmissible_of_admissible`). Here
`ξ_{i,c} = ∑_j α_i(j) r_j^c` (`modeFst`), so `ξ · w = ∑_{i,j} α_i(j) ŵ_i(j)`.

Proof: if the condition fails at `(i₀, j₀)`, a dot product `u` with `u · ŝ₁(j₀) = 0` separates
`α x̂(j₀) - β x̂'(j₀)` from `span ŝ₁(j₀)` (`Submodule.exists_dotProduct_separating`); the matrix
`K` with slot values `t u` at `(i₀, j₀)` and `0` elsewhere lies in `ker (A ↦ A s₁)` and its
character value is `e(1) ≠ 1`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA

variable {k ℓ : ℕ}

/-- The polynomial with coefficients `c ↦ w c`. -/
noncomputable def polyOf (w : Fin ringDegree → Coeff) : Rq := polyBackend.equivPi.symm w

theorem polyOf_get (w : Fin ringDegree → Coeff) (c : Fin ringDegree) : (polyOf w).get c = w c := by
  simp only [polyOf, LatticeCrypto.PolyBackend.equivPi_symm_apply]
  exact LatticeCrypto.Poly.get_vectorOfFn w c

/-- Reading coefficient `c` is additive. -/
def getHom (c : Fin ringDegree) : Rq →+ Coeff where
  toFun f := f.get c
  map_zero' := LatticeCrypto.vectorRing_zero_get c
  map_add' f g := LatticeCrypto.vectorRing_add_get f g c

section Maps

/-- The additive structure of a function group through its `AddCommGroup` instance, the one the
kernel average (`ZMod.Admissible`) is stated with. -/
abbrev groupZero (X : Type*) [AddCommGroup X] : AddZero X :=
  @AddZeroClass.toAddZero _ (@AddMonoid.toAddZeroClass _ (@SubNegMonoid.toAddMonoid _
    (@AddGroup.toSubNegMonoid _ (@AddCommGroup.toAddGroup _ inferInstance))))

/-- The coefficient vector of `A y`, as an additive map of `A`. -/
noncomputable def matAct (y : Fin ℓ → Rq) :
    @AddMonoidHom (Fin k → Fin ℓ → Rq) (Fin k × Fin ringDegree → Coeff) (groupZero _) (groupZero _) where
  toFun A ic := getHom ic.2 (∑ b, A ic.1 b * y b)
  map_zero' := by
    funext ic
    have h : ∑ b, (0 : Fin k → Fin ℓ → Rq) ic.1 b * y b = 0 :=
      Finset.sum_eq_zero fun b _ => rq_zero_mul (y b)
    change getHom ic.2 (∑ b, (0 : Fin k → Fin ℓ → Rq) ic.1 b * y b) = 0
    rw [h, map_zero]
  map_add' A B := by
    funext ic
    have h : ∑ b, (A + B) ic.1 b * y b = ∑ b, A ic.1 b * y b + ∑ b, B ic.1 b * y b :=
      (Finset.sum_congr rfl fun b _ => rq_add_mul _ _ _).trans Finset.sum_add_distrib
    change getHom ic.2 (∑ b, (A + B) ic.1 b * y b) =
      getHom ic.2 (∑ b, A ic.1 b * y b) + getHom ic.2 (∑ b, B ic.1 b * y b)
    rw [h, map_add]

/-- The key map `A ↦ A s₁`. -/
noncomputable def keyMap (s : Fin ℓ → Rq) :
    @AddMonoidHom (Fin k → Fin ℓ → Rq) (Fin k → Rq) (groupZero _) (groupZero _) where
  toFun A i := ∑ b, A i b * s b
  map_zero' := by
    funext i
    exact Finset.sum_eq_zero fun b _ => rq_zero_mul (s b)
  map_add' A B := by
    funext i
    exact (Finset.sum_congr rfl fun b _ => rq_add_mul _ _ _).trans Finset.sum_add_distrib

end Maps

/-- The row evaluation `∑_c w_{i,c} r_j^c` of a coefficient vector of `R_q^k`. -/
def rowEval (w : Fin k × Fin ringDegree → Coeff) (i : Fin k) (j : Fin ringDegree) : Coeff :=
  ∑ c, w (i, c) * slotRoot j ^ (c : ℕ)

/-- The first coefficient-domain mode of a slot mode: `ξ_{i,c} = ∑_j r_j^c α_i(j)`. -/
noncomputable def modeFst (μ : Fin k → Fin ringDegree → Coeff × Coeff) :
    Fin k × Fin ringDegree → Coeff :=
  fun ic => (coeffOfSlots slotRoot (μ ic.1) ic.2).1

/-- The second coefficient-domain mode of a slot mode. -/
noncomputable def modeSnd (μ : Fin k → Fin ringDegree → Coeff × Coeff) :
    Fin k × Fin ringDegree → Coeff :=
  fun ic => (coeffOfSlots slotRoot (μ ic.1) ic.2).2

/-- `ξ · w = ∑_{i,j} α_i(j) ∑_c w_{i,c} r_j^c`. -/
theorem dot_modeFst (μ : Fin k → Fin ringDegree → Coeff × Coeff)
    (w : Fin k × Fin ringDegree → Coeff) :
    ZMod.dot (modeFst μ) w =
      ∑ i, ∑ j, (μ i j).1 * rowEval w i j := by
  simp only [ZMod.dot, modeFst, rowEval, coeffOfSlots, Prod.fst_sum, Prod.smul_fst, smul_eq_mul,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dot_modeSnd (μ : Fin k → Fin ringDegree → Coeff × Coeff)
    (w : Fin k × Fin ringDegree → Coeff) :
    ZMod.dot (modeSnd μ) w =
      ∑ i, ∑ j, (μ i j).2 * rowEval w i j := by
  simp only [ZMod.dot, modeSnd, rowEval, coeffOfSlots, Prod.snd_sum, Prod.smul_snd, smul_eq_mul,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The slot values of a matrix row times a mask: `ŵ_i(j) = ∑_b Â_{ib}(j) ŷ_b(j)`. -/
theorem slotVec_sum_mul (A : Fin k → Fin ℓ → Rq) (y : Fin ℓ → Rq) (i : Fin k)
    (j : Fin ringDegree) :
    slotVec (∑ b, A i b * y b) j = ∑ b, slotVec (A i b) j * slotVec (y b) j := by
  have h1 : slotVec (∑ b, A i b * y b) j = slotEvalHom (slotRoot_pow j) (∑ b, A i b * y b) :=
    (slotEvalHom_apply _ _).symm
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, slotEvalHom_apply, slotEvalHom_apply]
  rfl

theorem rowEval_matAct (y : Fin ℓ → Rq) (A : Fin k → Fin ℓ → Rq) (i : Fin k)
    (j : Fin ringDegree) :
    rowEval (matAct y A) i j = ∑ b, slotVec (A i b) j * slotVec (y b) j := by
  rw [← slotVec_sum_mul]
  rfl

theorem sum_sum_eq_single {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [AddCommMonoid M] (F : α → β → M) (a₀ : α) (b₀ : β)
    (hF : ∀ a b, ¬ (a = a₀ ∧ b = b₀) → F a b = 0) : ∑ a, ∑ b, F a b = F a₀ b₀ := by
  rw [Finset.sum_eq_single a₀ (fun a _ ha => Finset.sum_eq_zero fun b _ => hF a b fun h => ha h.1)
    (fun h => absurd (Finset.mem_univ a₀) h)]
  exact Finset.sum_eq_single b₀ (fun b _ hb => hF a₀ b fun h => hb h.2)
    (fun h => absurd (Finset.mem_univ b₀) h)

theorem slotVec_zero (j : Fin ringDegree) : slotVec 0 j = 0 := slotEval_zero (slotRoot_pow j)

/-- **The kernel average leaves only slot-admissible modes.** If the pair of coefficient-domain
modes `(modeFst μ, modeSnd μ)` survives the average over `A` on the cosets of `ker (A ↦ A s₁)`
for masks `y, y'`, then `μ` is admissible for the slot vectors `ŝ₁, ŷ, ŷ'`. -/
theorem slotAdmissible_of_admissible (s₁ y y' : Fin ℓ → Rq)
    (μ : Fin k → Fin ringDegree → Coeff × Coeff)
    (h : ZMod.Admissible (keyMap (k := k) s₁) (matAct (k := k)) y y' (modeFst μ) (modeSnd μ)) :
    Admissible (fun j b => slotVec (s₁ b) j) (fun j b => slotVec (y b) j)
      (fun j b => slotVec (y' b) j) μ := by
  intro i₀ j₀
  by_contra hns
  rw [mem_slotAnnihilator] at hns
  set v := (μ i₀ j₀).1 • (fun b => slotVec (y b) j₀) - (μ i₀ j₀).2 • (fun b => slotVec (y' b) j₀)
  obtain ⟨u, hus, huv⟩ := Submodule.exists_dotProduct_separating hns
  set t := (∑ b, u b * v b)⁻¹
  let T : Fin k → Fin ℓ → Fin ringDegree → Coeff := fun i b j =>
    if i = i₀ ∧ j = j₀ then t * u b else 0
  let K : Fin k → Fin ℓ → Rq := fun i b => Function.surjInv slotVec_bijective.2 (T i b)
  have hK : ∀ i b, slotVec (K i b) = T i b := fun i b =>
    Function.surjInv_eq slotVec_bijective.2 (T i b)
  have hker : keyMap s₁ K = 0 := by
    funext i
    apply slotVec_injective
    funext j
    change slotVec (∑ b, K i b * s₁ b) j = slotVec 0 j
    rw [slotVec_sum_mul, slotVec_zero]
    simp only [hK, T]
    by_cases hij : i = i₀ ∧ j = j₀
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [and_self, if_true, mul_assoc, ← Finset.mul_sum]
      rw [hus, mul_zero]
    · simp only [hij, if_false, zero_mul, Finset.sum_const_zero]
  have hval : ZMod.dot (modeFst μ) (matAct y K) - ZMod.dot (modeSnd μ) (matAct y' K) = 1 := by
    rw [dot_modeFst, dot_modeSnd, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, rowEval_matAct, hK]
    rw [sum_sum_eq_single _ i₀ j₀ fun i j hij => by simp only [T, hij, if_false, zero_mul,
      Finset.sum_const_zero, mul_zero, sub_zero]]
    have hT : ∀ b, T i₀ b j₀ = t * u b := fun b => if_pos ⟨rfl, rfl⟩
    have hv : ∀ b, v b = (μ i₀ j₀).1 * slotVec (y b) j₀ - (μ i₀ j₀).2 * slotVec (y' b) j₀ :=
      fun b => rfl
    simp only [hT]
    have : (μ i₀ j₀).1 * ∑ b, t * u b * slotVec (y b) j₀ -
        (μ i₀ j₀).2 * ∑ b, t * u b * slotVec (y' b) j₀ = t * ∑ b, u b * v b := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hv b]
      ring
    rw [this]
    exact inv_mul_cancel₀ huv
  have h1 := h K hker
  have h2 : ZMod.stdAddChar (1 : Coeff) = 1 := by
    rw [← hval]
    exact h1
  have : (1 : Coeff) = 0 := ZMod.injective_stdAddChar (h2.trans (AddChar.map_zero_eq_one _).symm)
  exact one_ne_zero this

end GordieHowe.MLDSA.Regularity
