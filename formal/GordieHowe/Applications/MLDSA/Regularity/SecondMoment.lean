-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.BoxSubspace
public import GordieHowe.Foundations.ToMathlib.InformationSet

@[expose] public section

/-!
# The second moment of the HighBits regularity argument

This file bounds the averaged second moment that the Fourier reduction
(`GordieHowe/Applications/MLDSA/Regularity/FourierReduction.lean`) leaves. It works in the slot
(NTT) domain of `R_q = F[X]/(X^n + 1)` over a finite field `F`: `n` slots with distinct nonzero
roots `r j`, `k` rows and `ℓ` columns.

* A *mode* `μ : Fin k → Fin n → F × F` assigns to every row `i` and slot `j` the pair
  `(ξ^∨_i(j), η^∨_i(j))` of dual coordinates of the two Fourier modes of the squared difference.
  Its coefficient-domain words are `coeffOfSlots r (μ i)`, `c ↦ ∑_j r_j ^ c • μ i j`.
* For masks `x, x'` in the slot domain (`Fin n → Fin ℓ → F`, the transforms of `z - c s₁`) and
  `ŝ₁` (`s`), the mode survives the average over the matrix `A` exactly when every pair lies in
  the slot annihilator, `a • x j - b • x' j ∈ span {s j}` (`Admissible`): averaging a character
  of `A` over the kernel of `A ↦ A s₁` (`AddChar.sum_comp_mul_eq_zero`) leaves this, with
  `ℓ - 1` independent equations per slot in place of `ℓ` when `A` is averaged freely.
* `secondMoment` sums the kernel weights `modeWeight` of the nonzero admissible modes; the
  average over two independent masks drawn from a box is `averagedSecondMoment`.

The bound `averagedSecondMoment_le` groups the modes by their slot support `T` and takes, per
`T`, one of two bounds:

* *fixed modes* (`#T ≤ n / 2`): each mode with support `T` is admissible with probability at
  most `G^{-(ℓ-1)#T}` (`card_admissible_le`), and the kernel weights of all modes supported in
  `T` multiply over rows; per row they are bounded by the two-window bound `T₂ ^ #T`
  (`sum_prod_le_two_windows`) or, for `#T ≤ 5`, by the small-support bound `(1 + δ_{#T})^2`;
* *fixed masks* (`#T > n / 2`): for given masks the admissible modes supported in `T` form a
  subspace of dimension `∑_{j ∈ T} dim D_j`, `D_j` the slot annihilator, so their weight is at
  most `S₁ ^ (k ∑_j dim D_j)` (`sum_prod_le_pow_finrank`); a nonzero `D_j` forces `x̂_j ∈ span ŝ₁`
  or `x̂'_j ∈ span(x̂_j, ŝ₁)`, a full one forces both `x̂_j, x̂'_j ∈ span ŝ₁`, and averaging over
  the masks in two stages gives `X ^ #T` with
  `X = (G^{-(ℓ-1)} + G^{-(ℓ-2)}) S₁ ^ k + G^{-2(ℓ-1)} S₁ ^ (2k)`.

Source: "A shorter proof of the stated HighBits regularity claim" (10 September 2026), Section 3,
equations (4)-(6), with the kernel restricted to `ker (A ↦ A s₁)` and the fixed-mask route in place
of the overlapping-window bound (20).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section Box

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n ℓ : ℕ}

omit [Fintype F] in
open Classical in
/-- A box of masks in the coefficient domain, read in the slot domain through the linear
equivalence `E`, meets the translate `w + ∏_j L j` of a product of slot subspaces in at most
`#B · ∏_j G^(dim L_j) / G^ℓ` points, for sides of size exactly `G`. -/
theorem card_box_pi_le (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F)) (S : ι → Finset F) {G : ℕ}
    (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) (L : Fin n → Submodule F (Fin ℓ → F))
    (w : Fin n → Fin ℓ → F) :
    (#((Fintype.piFinset S).filter (fun z => E z - w ∈ Submodule.pi Set.univ L)) : ℝ) ≤
      #(Fintype.piFinset S) * ∏ j, ((G : ℝ) ^ Module.finrank F (L j) / (G : ℝ) ^ ℓ) := by
  classical
  set U := (Submodule.pi Set.univ L).comap E.toLinearMap
  have hU : Module.finrank F U = ∑ j, Module.finrank F (L j) := by
    rw [← Submodule.finrank_pi_univ L]
    exact (Submodule.equivMapOfInjective _ E.injective _ |>.trans
      (LinearEquiv.ofEq _ _ (Submodule.map_comap_eq_of_surjective E.surjective _))).finrank_eq
  have hcard : #(Fintype.piFinset S) = G ^ (n * ℓ) := by
    rw [Fintype.card_piFinset, Finset.prod_congr rfl fun i _ => hS i, Finset.prod_const,
      Finset.card_univ]
    congr 1
    have := E.finrank_eq
    simp only [Module.finrank_fintype_fun_eq_card] at this
    rw [this, Module.finrank_pi_fintype]
    simp
  have hfilter : (Fintype.piFinset S).filter (fun z => E z - w ∈ Submodule.pi Set.univ L) =
      (Fintype.piFinset S).filter (fun z => z - E.symm w ∈ U) := by
    refine Finset.filter_congr fun z _ => ?_
    simp only [U, Submodule.mem_comap, LinearEquiv.coe_coe, map_sub, LinearEquiv.apply_symm_apply]
  rw [hfilter]
  have h1 := U.card_filter_sub_mem_le_pow_finrank S hG (fun i => (hS i).le) (E.symm w)
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  calc (#((Fintype.piFinset S).filter (fun z => z - E.symm w ∈ U)) : ℝ)
      ≤ (G : ℝ) ^ Module.finrank F U := by exact_mod_cast h1
    _ = #(Fintype.piFinset S) * ∏ j, ((G : ℝ) ^ Module.finrank F (L j) / (G : ℝ) ^ ℓ) := by
        rw [hcard, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum, hU, Nat.cast_pow, ← pow_mul, mul_comm ℓ n,
          mul_div_cancel₀ _ (by positivity)]

/-- Two-stage counting: if at most `c₁` points `z` of `B` satisfy `P`, and for every `z` at most
`c₂ ≥ 0` points `z'` satisfy `Q z`, then at most `c₁ c₂` pairs satisfy `P z ∧ Q z z'`. -/
theorem card_filter_product_le {α : Type*} (B : Finset α) (P : α → Prop) [DecidablePred P]
    (Q : α → α → Prop) [∀ z, DecidablePred (Q z)] {c₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (h₁ : (#(B.filter P) : ℝ) ≤ c₁) (h₂ : ∀ z, (#(B.filter (Q z)) : ℝ) ≤ c₂) :
    (#((B ×ˢ B).filter fun p => P p.1 ∧ Q p.1 p.2) : ℝ) ≤ c₁ * c₂ := by
  have hcard : #((B ×ˢ B).filter fun p => P p.1 ∧ Q p.1 p.2) =
      ∑ z ∈ B.filter P, #(B.filter (Q z)) := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs with hz
    · rw [Finset.card_filter]
      exact Finset.sum_congr rfl fun z' _ => by simp [hz]
    · exact Finset.sum_eq_zero fun z' _ => by simp [hz]
  rw [hcard, Nat.cast_sum]
  calc ∑ z ∈ B.filter P, (#(B.filter (Q z)) : ℝ) ≤ ∑ _z ∈ B.filter P, c₂ :=
        Finset.sum_le_sum fun z _ => h₂ z
    _ = #(B.filter P) * c₂ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ c₁ * c₂ := mul_le_mul_of_nonneg_right h₁ hc₂

end Box

section Modes

variable {n k ℓ : ℕ}

/-- The coefficient-domain word of a slot-domain vector: `c ↦ ∑_j r_j ^ c • μ_j`. For dual
coordinates `μ = ξ^∨` this is the character vector `ξ = Vᵀ ξ^∨` (note, Section 3). -/
def coeffOfSlots {M : Type*} [AddCommMonoid M] [Module F M] (r : Fin n → F) (μ : Fin n → M) :
    Fin n → M :=
  fun c => ∑ j, r j ^ (c : ℕ) • μ j

/-- The slot pairing `(a, b) ↦ a • x - b • x'`. -/
def slotPairing (x x' : Fin ℓ → F) : F × F →ₗ[F] (Fin ℓ → F) :=
  (LinearMap.fst F F F).smulRight x - (LinearMap.snd F F F).smulRight x'

omit [Fintype F] [DecidableEq F] in
@[simp] theorem slotPairing_apply (x x' : Fin ℓ → F) (p : F × F) :
    slotPairing x x' p = p.1 • x - p.2 • x' := rfl

/-- The slot annihilator `D = {(a, b) | a • x - b • x' ∈ span {s}}`. -/
def slotAnnihilator (s x x' : Fin ℓ → F) : Submodule F (F × F) :=
  (Submodule.span F {s}).comap (slotPairing x x')

omit [Fintype F] [DecidableEq F] in
theorem mem_slotAnnihilator {s x x' : Fin ℓ → F} {p : F × F} :
    p ∈ slotAnnihilator s x x' ↔ p.1 • x - p.2 • x' ∈ Submodule.span F {s} := Iff.rfl

/-- A mode `μ` survives the kernel average for masks `x, x'` (note, (4), restricted to
`ker (A ↦ A s₁)`): every pair `μ i j` lies in the slot annihilator at `j`. -/
def Admissible (s x x' : Fin n → Fin ℓ → F) (μ : Fin k → Fin n → F × F) : Prop :=
  ∀ i j, μ i j ∈ slotAnnihilator (s j) (x j) (x' j)

/-- The kernel weight of a mode: `∏_i ∏_c κ i c ((ξ_i)_c, (η_i)_c)` over the coefficient words. -/
def modeWeight (r : Fin n → F) (κ : Fin k → Fin n → F × F → ℝ)
    (μ : Fin k → Fin n → F × F) : ℝ :=
  ∏ i, ∏ c, κ i c (coeffOfSlots r (μ i) c)

/-- The slot support of a mode: the slots where some row is nonzero. -/
def modeSupport (μ : Fin k → Fin n → F × F) : Finset (Fin n) :=
  univ.filter fun j => ∃ i, μ i j ≠ 0

omit [Fintype F] in
theorem modeSupport_eq_empty_iff {μ : Fin k → Fin n → F × F} :
    modeSupport μ = ∅ ↔ μ = 0 := by
  constructor
  · intro h
    funext i j
    by_contra hne
    have : j ∈ modeSupport μ := Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hne⟩
    rw [h] at this
    exact Finset.notMem_empty j this
  · rintro rfl
    exact Finset.filter_false_of_mem fun j _ ⟨i, hi⟩ => hi rfl

open Classical in
/-- The second moment for masks `x, x'`: the total kernel weight of the nonzero admissible
modes. -/
noncomputable def secondMoment (r : Fin n → F) (κ : Fin k → Fin n → F × F → ℝ)
    (s x x' : Fin n → Fin ℓ → F) : ℝ :=
  ∑ μ ∈ univ.filter (fun μ => μ ≠ 0 ∧ Admissible s x x' μ), modeWeight r κ μ

open Classical in
/-- The part of the second moment carried by modes of slot support exactly `T`. -/
noncomputable def supportMoment (r : Fin n → F) (κ : Fin k → Fin n → F × F → ℝ)
    (s x x' : Fin n → Fin ℓ → F) (T : Finset (Fin n)) : ℝ :=
  ∑ μ ∈ univ.filter (fun μ => Admissible s x x' μ ∧ modeSupport μ = T), modeWeight r κ μ

open Classical in
/-- The second moment splits over the nonempty slot supports. -/
theorem secondMoment_eq_sum_supportMoment (r : Fin n → F) (κ : Fin k → Fin n → F × F → ℝ)
    (s x x' : Fin n → Fin ℓ → F) :
    secondMoment r κ s x x' =
      ∑ T ∈ (univ : Finset (Fin n)).powerset.filter (· ≠ ∅), supportMoment r κ s x x' T := by
  unfold secondMoment supportMoment
  rw [← Finset.sum_fiberwise_of_maps_to (g := modeSupport)
    (t := (univ : Finset (Fin n)).powerset.filter (· ≠ ∅))]
  · refine Finset.sum_congr rfl fun T hT => Finset.sum_congr ?_ fun _ _ => rfl
    ext μ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, h⟩, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      refine ⟨⟨fun h0 => ?_, h⟩, rfl⟩
      rw [Finset.mem_filter] at hT
      exact hT.2 (modeSupport_eq_empty_iff.mpr h0)
  · intro μ hμ
    rw [Finset.mem_filter] at hμ ⊢
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      fun h => hμ.2.1 (modeSupport_eq_empty_iff.mp h)⟩

end Modes

section Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n k ℓ : ℕ}

omit [Fintype F] [DecidableEq F] in
theorem finrank_span_singleton_le_one (v : Fin ℓ → F) :
    Module.finrank F (Submodule.span F {v}) ≤ 1 := by
  classical
  refine (finrank_span_le_card ({v} : Set (Fin ℓ → F))).trans ?_
  simp

omit [Fintype F] in
theorem finrank_span_pair_le_two (v w : Fin ℓ → F) :
    Module.finrank F (Submodule.span F {v, w}) ≤ 2 := by
  classical
  refine (finrank_span_le_card ({v, w} : Set (Fin ℓ → F))).trans ?_
  rw [Set.toFinset_insert, Set.toFinset_singleton]
  exact (Finset.card_insert_le _ _).trans (by simp)

/-- The box factor `G ^ dim L / G ^ ℓ` of a slot subspace; it is `1` for `L = ⊤`. -/
noncomputable def boxFactor (G : ℕ) (L : Submodule F (Fin ℓ → F)) : ℝ :=
  (G : ℝ) ^ Module.finrank F L / (G : ℝ) ^ ℓ

omit [Fintype F] [DecidableEq F] in
theorem boxFactor_top (G : ℕ) (hG : 1 ≤ G) : boxFactor G (⊤ : Submodule F (Fin ℓ → F)) = 1 := by
  have : (0 : ℝ) < G := by exact_mod_cast hG
  rw [boxFactor, finrank_top, Module.finrank_fin_fun, div_self (by positivity)]

omit [Fintype F] [DecidableEq F] in
theorem boxFactor_nonneg (G : ℕ) (L : Submodule F (Fin ℓ → F)) : 0 ≤ boxFactor G L := by
  unfold boxFactor
  positivity

omit [Fintype F] [DecidableEq F] in
theorem boxFactor_le {G : ℕ} (hG : 1 ≤ G) {L : Submodule F (Fin ℓ → F)} {d : ℕ}
    (hd : Module.finrank F L ≤ d) : boxFactor G L ≤ (G : ℝ) ^ d / (G : ℝ) ^ ℓ := by
  unfold boxFactor
  gcongr
  · exact_mod_cast hG

/-- A product of per-slot factors bounded by `c` on `T` and by `1` elsewhere is at most `c ^ #T`. -/
theorem prod_le_pow_of_le_ite {T : Finset (Fin n)} {f : Fin n → ℝ} {c : ℝ}
    (hf0 : ∀ j, 0 ≤ f j) (hf : ∀ j, f j ≤ if j ∈ T then c else 1) : ∏ j, f j ≤ c ^ #T := by
  calc ∏ j, f j ≤ ∏ j, (if j ∈ T then c else 1) :=
        Finset.prod_le_prod₀ (fun j _ => hf0 j) fun j _ => hf j
    _ = c ^ #T := by rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

omit [Fintype F] [DecidableEq F] in
theorem mem_span_of_slotPairing {s x x' : Fin ℓ → F} {p : F × F} (hp : p ≠ 0)
    (h : p.1 • x - p.2 • x' ∈ Submodule.span F {s}) :
    (p.2 = 0 → x ∈ Submodule.span F {s}) ∧
      (p.2 ≠ 0 → x' - (p.2⁻¹ * p.1) • x ∈ Submodule.span F {s}) := by
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have ha : p.1 ≠ 0 := fun ha => hp (Prod.ext ha hb)
    rw [hb, zero_smul, sub_zero] at h
    have := Submodule.smul_mem _ p.1⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  · have := Submodule.smul_mem _ (-p.2⁻¹) h
    convert this using 1
    rw [smul_sub, smul_smul, smul_smul, neg_mul, neg_mul, inv_mul_cancel₀ hb]
    module

open Classical in
/-- Fixed modes: a mode with slot support `T` is admissible for two masks drawn from a box with
probability at most `(G / G^ℓ) ^ #T = G^{-(ℓ-1)#T}`. At each slot of `T` one nonzero row gives
one equation `a x̂_j - b x̂'_j ∈ span ŝ₁(j)`: for `b = 0` it confines `x̂_j` to a line, otherwise
it confines `x̂'_j` to a translate of a line chosen after `x̂`. -/
theorem card_admissible_le (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F)) (S : ι → Finset F) {G : ℕ}
    (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) (s w₀ : Fin n → Fin ℓ → F)
    {μ : Fin k → Fin n → F × F} {T : Finset (Fin n)} (hT : modeSupport μ = T) :
    (#((Fintype.piFinset S ×ˢ Fintype.piFinset S).filter fun p =>
        Admissible s (E p.1 - w₀) (E p.2 - w₀) μ) : ℝ) ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) * ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T := by
  set B := Fintype.piFinset S
  -- a nonzero pair `p j = μ i j` at every slot of the support
  let p : Fin n → F × F := fun j => if h : ∃ i, μ i j ≠ 0 then μ h.choose j else 0
  have hp : ∀ j ∈ T, p j ≠ 0 ∧ ∃ i, μ i j = p j := by
    intro j hj
    rw [← hT, modeSupport, Finset.mem_filter] at hj
    have h := hj.2
    simp only [p, dif_pos h]
    exact ⟨h.choose_spec, _, rfl⟩
  let Tx := T.filter fun j => (p j).2 = 0
  let Ty := T.filter fun j => (p j).2 ≠ 0
  let L₁ : Fin n → Submodule F (Fin ℓ → F) := fun j =>
    if j ∈ Tx then Submodule.span F {s j} else ⊤
  let L₂ : Fin n → Submodule F (Fin ℓ → F) := fun j =>
    if j ∈ Ty then Submodule.span F {s j} else ⊤
  let shift : (Fin n → Fin ℓ → F) → Fin n → Fin ℓ → F := fun x j =>
    if j ∈ Ty then ((p j).2⁻¹ * (p j).1) • x j else 0
  have hsub : (B ×ˢ B).filter (fun q => Admissible s (E q.1 - w₀) (E q.2 - w₀) μ) ⊆
      (B ×ˢ B).filter (fun q => E q.1 - w₀ ∈ Submodule.pi Set.univ L₁ ∧
        E q.2 - (w₀ + shift (E q.1 - w₀)) ∈ Submodule.pi Set.univ L₂) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, fun j _ => ?_, fun j _ => ?_⟩
    · simp only [L₁]
      split_ifs with hj
      · obtain ⟨hjT, hb⟩ := Finset.mem_filter.mp hj
        obtain ⟨hp0, i, hi⟩ := hp j hjT
        have h := hq.2 i j
        rw [hi, mem_slotAnnihilator] at h
        exact (mem_span_of_slotPairing hp0 h).1 hb
      · exact Submodule.mem_top
    · simp only [L₂, shift]
      split_ifs with hj
      · obtain ⟨hjT, hb⟩ := Finset.mem_filter.mp hj
        obtain ⟨hp0, i, hi⟩ := hp j hjT
        have h := hq.2 i j
        rw [hi, mem_slotAnnihilator] at h
        have := (mem_span_of_slotPairing hp0 h).2 hb
        simpa only [Pi.sub_apply, Pi.add_apply, if_pos hj, sub_add_eq_sub_sub, SetLike.mem_coe]
          using this
      · exact Submodule.mem_top
  have hfac : ∀ L : Fin n → Submodule F (Fin ℓ → F), 0 ≤ ∏ j, boxFactor G (L j) :=
    fun L => Finset.prod_nonneg fun j _ => boxFactor_nonneg G (L j)
  have hcount := card_filter_product_le B (fun z => E z - w₀ ∈ Submodule.pi Set.univ L₁)
    (fun z z' => E z' - (w₀ + shift (E z - w₀)) ∈ Submodule.pi Set.univ L₂)
    (mul_nonneg (Nat.cast_nonneg _) (hfac L₂))
    (card_box_pi_le E S hG hS L₁ w₀) (fun z => card_box_pi_le E S hG hS L₂ _)
  have hG0 : (0 : ℝ) ≤ (G : ℝ) / (G : ℝ) ^ ℓ := by positivity
  have hprod : (∏ j, boxFactor G (L₁ j)) * ∏ j, boxFactor G (L₂ j) ≤
      ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T := by
    rw [← Finset.prod_mul_distrib]
    refine prod_le_pow_of_le_ite (fun j => mul_nonneg (boxFactor_nonneg _ _)
      (boxFactor_nonneg _ _)) fun j => ?_
    have hline : boxFactor G (Submodule.span F {s j}) ≤ (G : ℝ) / (G : ℝ) ^ ℓ := by
      simpa using boxFactor_le hG (finrank_span_singleton_le_one (s j))
    simp only [L₁, L₂]
    by_cases hjT : j ∈ T
    · rw [if_pos hjT]
      by_cases hb : (p j).2 = 0
      · have hx : j ∈ Tx := Finset.mem_filter.mpr ⟨hjT, hb⟩
        have hy : j ∉ Ty := fun h => (Finset.mem_filter.mp h).2 hb
        rw [if_pos hx, if_neg hy, boxFactor_top G hG, mul_one]
        exact hline
      · have hx : j ∉ Tx := fun h => hb (Finset.mem_filter.mp h).2
        have hy : j ∈ Ty := Finset.mem_filter.mpr ⟨hjT, hb⟩
        rw [if_neg hx, if_pos hy, boxFactor_top G hG, one_mul]
        exact hline
    · have hx : j ∉ Tx := fun h => hjT (Finset.mem_filter.mp h).1
      have hy : j ∉ Ty := fun h => hjT (Finset.mem_filter.mp h).1
      rw [if_neg hjT, if_neg hx, if_neg hy, boxFactor_top G hG, mul_one]
  calc (#((B ×ˢ B).filter fun q => Admissible s (E q.1 - w₀) (E q.2 - w₀) μ) : ℝ)
      ≤ #((B ×ˢ B).filter (fun q => E q.1 - w₀ ∈ Submodule.pi Set.univ L₁ ∧
          E q.2 - (w₀ + shift (E q.1 - w₀)) ∈ Submodule.pi Set.univ L₂)) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (#B * ∏ j, boxFactor G (L₁ j)) * (#B * ∏ j, boxFactor G (L₂ j)) := hcount
    _ = #B * #B * ((∏ j, boxFactor G (L₁ j)) * ∏ j, boxFactor G (L₂ j)) := by ring
    _ ≤ #B * #B * ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T := by gcongr

end Probability

section Rows

variable {n k : ℕ}

/-- Amplitudes on `T` extended by zero to all slots. -/
def extendSlots {M : Type*} [Zero M] (T : Finset (Fin n)) (lam : T → M) : Fin n → M :=
  fun j => if h : j ∈ T then lam ⟨j, h⟩ else 0

omit [Fintype F] [DecidableEq F] in
theorem coeffOfSlots_extendSlots {M : Type*} [AddCommMonoid M] [Module F M] (r : Fin n → F)
    (T : Finset (Fin n)) (lam : T → M) (c : Fin n) :
    coeffOfSlots r (extendSlots T lam) c = ∑ j : T, r j ^ (c : ℕ) • lam j := by
  unfold coeffOfSlots extendSlots
  rw [← Finset.sum_subset (Finset.subset_univ T) fun j _ hj => by rw [dif_neg hj, smul_zero],
    ← Finset.sum_coe_sort T]
  exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.2]

omit [Fintype F] [DecidableEq F] in
theorem coeffOfSlots_zero {M : Type*} [AddCommMonoid M] [Module F M] (r : Fin n → F) :
    coeffOfSlots r (0 : Fin n → M) = 0 := by
  funext c
  simp [coeffOfSlots]

/-- The coefficient-domain pair word of amplitudes `λ : T → F × F`. -/
def pairWord (r : Fin n → F) (T : Finset (Fin n)) (lam : T → F × F) : Fin n → F × F :=
  coeffOfSlots r (extendSlots T lam)

theorem pairWord_fst (r : Fin n → F) (T : Finset (Fin n)) (lam : T → F × F) (c : Fin n) :
    (pairWord r T lam c).1 = powerCodeWord T r n (fun j => (lam j).1) c := by
  rw [pairWord, coeffOfSlots_extendSlots, Prod.fst_sum, powerCodeWord]
  exact Finset.sum_congr rfl fun j _ => by rw [Prod.smul_fst, smul_eq_mul, mul_comm]

theorem pairWord_snd (r : Fin n → F) (T : Finset (Fin n)) (lam : T → F × F) (c : Fin n) :
    (pairWord r T lam c).2 = powerCodeWord T r n (fun j => (lam j).2) c := by
  rw [pairWord, coeffOfSlots_extendSlots, Prod.snd_sum, powerCodeWord]
  exact Finset.sum_congr rfl fun j _ => by rw [Prod.smul_snd, smul_eq_mul, mul_comm]

/-- Pair words inherit the window bijections of the scalar words, coordinate by coordinate. -/
theorem bijective_window_pairWord {r : Fin n → F} {T : Finset (Fin n)} {W : Finset (Fin n)}
    (hW : Function.Bijective fun lam : T → F => fun b : W => powerCodeWord T r n lam b) :
    Function.Bijective fun lam : T → F × F => fun b : W => pairWord r T lam b := by
  refine ⟨fun lam lam' h => ?_, fun z => ?_⟩
  · have h1 : (fun j => (lam j).1) = fun j => (lam' j).1 := hW.1 <| funext fun b => by
      have := congrArg Prod.fst (congrFun h b)
      simp only [pairWord_fst] at this
      exact this
    have h2 : (fun j => (lam j).2) = fun j => (lam' j).2 := hW.1 <| funext fun b => by
      have := congrArg Prod.snd (congrFun h b)
      simp only [pairWord_snd] at this
      exact this
    funext j
    exact Prod.ext (congrFun h1 j) (congrFun h2 j)
  · obtain ⟨l₁, hl₁⟩ := hW.2 fun b => (z b).1
    obtain ⟨l₂, hl₂⟩ := hW.2 fun b => (z b).2
    refine ⟨fun j => (l₁ j, l₂ j), funext fun b => Prod.ext ?_ ?_⟩
    · simp only [pairWord_fst]
      exact congrFun hl₁ b
    · simp only [pairWord_snd]
      exact congrFun hl₂ b

/-- The kernel mass of row `i` over the modes supported in `T`:
`∑_{λ : T → F × F} ∏_c κ i c (pairWord λ c)`. -/
noncomputable def rowMass (r : Fin n → F) (κ : Fin k → Fin n → F × F → ℝ) (i : Fin k)
    (T : Finset (Fin n)) : ℝ :=
  ∑ lam : T → F × F, ∏ c, κ i c (pairWord r T lam c)

/-- Two windows (note, (6), first case): a row's kernel mass over a support of `#T ≤ n / 2` slots
is at most `T₂ ^ #T` when `0 ≤ κ ≤ 1` and `∑ κ² ≤ T₂` at every coefficient. -/
theorem rowMass_le_two_windows {r : Fin n → F} (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0)
    {κ : Fin k → Fin n → F × F → ℝ} (hκ0 : ∀ i c u, 0 ≤ κ i c u) (hκ1 : ∀ i c u, κ i c u ≤ 1)
    {T₂ : ℝ} (hT₂ : ∀ i c, ∑ u, κ i c u ^ 2 ≤ T₂) (i : Fin k) {T : Finset (Fin n)}
    (hT : #T + #T ≤ n) : rowMass r κ i T ≤ T₂ ^ #T := by
  classical
  have h₁ : 0 + #T ≤ n := by omega
  have b₁ := bijective_window_pairWord (bijective_window_powerCodeWord hr.injOn
    (fun j _ => hr0 j) h₁)
  have b₂ := bijective_window_pairWord (bijective_window_powerCodeWord hr.injOn
    (fun j _ => hr0 j) hT)
  obtain ⟨hW₁, hinj⟩ := isInformationSet_image_of_bijective _ b₁
  obtain ⟨hW₂, -⟩ := isInformationSet_image_of_bijective _ b₂
  rw [rowMass, ← Finset.sum_image (f := fun y : Fin n → F × F => ∏ c, κ i c (y c))
    fun lam _ lam' _ h => hinj h]
  exact sum_prod_le_two_windows hW₁ hW₂ (disjoint_consecutiveWindow h₁ hT)
    (card_consecutiveWindow h₁) (card_consecutiveWindow hT) (hκ0 i) (hκ1 i) (hT₂ i)

theorem powerCodeWord_injective {r : Fin n → F} (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0)
    (T : Finset (Fin n)) : Function.Injective (powerCodeWord T r n) := by
  have hT : 0 + #T ≤ n := by
    simpa using (Finset.card_le_univ T).trans (Fintype.card_fin n).le
  intro l l' h
  exact (bijective_window_powerCodeWord hr.injOn (fun j _ => hr0 j) hT).1 (by simp only [h])

omit [Fintype F] [DecidableEq F] in
theorem powerCodeWord_zero (r : Fin n → F) (T : Finset (Fin n)) :
    powerCodeWord T r n 0 = 0 := by
  funext c
  simp [powerCodeWord]

theorem pairWord_zero (r : Fin n → F) (T : Finset (Fin n)) : pairWord r T 0 = 0 := by
  have : extendSlots T (0 : T → F × F) = 0 := by
    funext j
    simp [extendSlots]
  rw [pairWord, this, coeffOfSlots_zero]

/-- Small supports: with `0 ≤ κ (u, v) ≤ φ u · φ v`, `0 ≤ φ ≤ min 1 f`, and the nonzero words of
`T` of total `f`-weight at most `δ`, a row's kernel mass over the nonzero modes supported in `T`
is at most `2δ + δ² = (1 + δ)² - 1`. -/
theorem rowMass_sub_zero_le {r : Fin n → F} (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0)
    {κ : Fin k → Fin n → F × F → ℝ} {φ : Fin k → Fin n → F → ℝ} {f : F → ℝ}
    (hκ0 : ∀ i c u, 0 ≤ κ i c u) (hκφ : ∀ i c u, κ i c u ≤ φ i c u.1 * φ i c u.2)
    (hφ0 : ∀ i c u, 0 ≤ φ i c u) (hφ1 : ∀ i c u, φ i c u ≤ 1) (hφf : ∀ i c u, φ i c u ≤ f u)
    (hf0 : ∀ u, 0 ≤ f u) (i : Fin k) {T : Finset (Fin n)} {δ : ℝ}
    (hδ : ∑ y ∈ (powerCode T r n).filter (· ≠ 0), ∏ c, f (y c) ≤ δ) :
    rowMass r κ i T - ∏ c, κ i c 0 ≤ 2 * δ + δ ^ 2 := by
  classical
  set h : (T → F) → ℝ := fun l => ∏ c, φ i c (powerCodeWord T r n l c) with hh
  have hh0 : ∀ l, 0 ≤ h l := fun l => Finset.prod_nonneg fun c _ => hφ0 i c _
  set H : (T → F × F) → ℝ := fun lam => h (fun j => (lam j).1) * h (fun j => (lam j).2)
  -- the zero mode
  have hzero : ∏ c, κ i c (pairWord r T 0 c) = ∏ c, κ i c 0 := by
    rw [pairWord_zero]
    rfl
  have hsplit : rowMass r κ i T - ∏ c, κ i c 0 =
      ∑ lam ∈ univ.erase 0, ∏ c, κ i c (pairWord r T lam c) := by
    rw [rowMass, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0), hzero, add_sub_cancel_left]
  -- the nonzero modes, pointwise
  have hpt : ∀ lam : T → F × F, ∏ c, κ i c (pairWord r T lam c) ≤ H lam := by
    intro lam
    simp only [H, hh]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun c _ => hκ0 i c _) fun c _ => ?_
    have := hκφ i c (pairWord r T lam c)
    rwa [pairWord_fst, pairWord_snd] at this
  -- the sum over pairs of amplitudes is a square
  have hsq : ∑ lam, H lam = (∑ l, h l) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _) _ _ fun lam => rfl
  have hH0 : H 0 = h 0 ^ 2 := by
    simp only [H, sq]
    rfl
  set D := ∑ l ∈ univ.erase 0, h l
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun l _ => hh0 l
  have hsumh : ∑ l, h l = h 0 + D := (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have hh01 : h 0 ≤ 1 := Finset.prod_le_one₀ (fun c _ => hφ0 i c _) fun c _ => hφ1 i c _
  have hDle : D ≤ δ := by
    have hinj := powerCodeWord_injective hr hr0 T
    calc D ≤ ∑ l ∈ univ.erase 0, ∏ c, f (powerCodeWord T r n l c) :=
          Finset.sum_le_sum fun l _ => Finset.prod_le_prod₀ (fun c _ => hφ0 i c _)
            fun c _ => hφf i c _
      _ = ∑ y ∈ (univ.erase 0).image (powerCodeWord T r n), ∏ c, f (y c) :=
          (Finset.sum_image (f := fun y : Fin n → F => ∏ c, f (y c))
            fun l _ l' _ h => hinj h).symm
      _ ≤ ∑ y ∈ (powerCode T r n).filter (· ≠ 0), ∏ c, f (y c) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ =>
            Finset.prod_nonneg fun c _ => hf0 _
          intro y hy
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
          refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ l), ?_⟩
          intro h0
          rw [← powerCodeWord_zero r T] at h0
          exact (Finset.mem_erase.mp hl).1 (hinj h0)
      _ ≤ δ := hδ
  have hh00 : 0 ≤ h 0 := hh0 0
  calc rowMass r κ i T - ∏ c, κ i c 0
      = ∑ lam ∈ univ.erase 0, ∏ c, κ i c (pairWord r T lam c) := hsplit
    _ ≤ ∑ lam ∈ univ.erase 0, H lam := Finset.sum_le_sum fun lam _ => hpt lam
    _ = (h 0 + D) ^ 2 - h 0 ^ 2 := by
        rw [← hsumh, ← hsq, ← hH0, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0),
          add_sub_cancel_left]
    _ = 2 * h 0 * D + D ^ 2 := by ring
    _ ≤ 2 * 1 * δ + δ ^ 2 := by gcongr
    _ = 2 * δ + δ ^ 2 := by ring

/-- `∏ (a + b) - ∏ a ≤ ∏ (1 + b) - 1` for `0 ≤ a ≤ 1` and `0 ≤ b`: the zero-mode masses `a` are at
most one. -/
theorem prod_add_sub_prod_le {α : Type*} (s : Finset α) {a b : α → ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1) (hb : ∀ i, 0 ≤ b i) :
    ∏ i ∈ s, (a i + b i) - ∏ i ∈ s, a i ≤ ∏ i ∈ s, (1 + b i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj]
    have hX : ∏ i ∈ s, a i ≤ ∏ i ∈ s, (a i + b i) :=
      Finset.prod_le_prod₀ (fun i _ => ha0 i) fun i _ => le_add_of_nonneg_right (hb i)
    have hX' : ∏ i ∈ s, (a i + b i) ≤ ∏ i ∈ s, (1 + b i) :=
      Finset.prod_le_prod₀ (fun i _ => add_nonneg (ha0 i) (hb i)) fun i _ => by linarith [ha1 i]
    have hY0 : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg fun i _ => ha0 i
    have hZ1 : 1 ≤ ∏ i ∈ s, (1 + b i) := Finset.one_le_prod₀ fun i _ => by linarith [hb i]
    nlinarith [ha0 j, ha1 j, hb j]

/-- Fixed modes, summed: the kernel weight of the modes with slot support exactly `T ≠ ∅` is at
most `∏_i rowMass_i - ∏_i ∏_c κ i c 0`, the weight of the nonzero modes supported in `T`. -/
theorem sum_modeWeight_support_le {r : Fin n → F} {κ : Fin k → Fin n → F × F → ℝ}
    (hκ0 : ∀ i c u, 0 ≤ κ i c u) {T : Finset (Fin n)} (hT : T ≠ ∅) :
    ∑ μ ∈ univ.filter (fun μ : Fin k → Fin n → F × F => modeSupport μ = T), modeWeight r κ μ ≤
      ∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0 := by
  classical
  let ext : (Fin k → T → F × F) → Fin k → Fin n → F × F := fun M i => extendSlots T (M i)
  have hext : Function.Injective ext := by
    intro M M' h
    funext i j
    have := congrFun (congrFun h i) j
    simp only [ext, extendSlots, dif_pos j.2] at this
    exact this
  have hext0 : ext 0 = 0 := by
    funext i j
    simp [ext, extendSlots]
  have hw : ∀ M, modeWeight r κ (ext M) = ∏ i, ∏ c, κ i c (pairWord r T (M i) c) := fun M => rfl
  have hsub : univ.filter (fun μ : Fin k → Fin n → F × F => modeSupport μ = T) ⊆
      (univ.erase 0).image ext := by
    intro μ hμ
    have hμT : modeSupport μ = T := (Finset.mem_filter.mp hμ).2
    have hoff : ∀ i j, j ∉ T → μ i j = 0 := by
      intro i j hj
      by_contra hne
      exact hj (hμT ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hne⟩)
    refine Finset.mem_image.mpr ⟨fun i j => μ i j, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · intro h0
      apply hT
      rw [← hμT, modeSupport_eq_empty_iff]
      funext i j
      by_cases hj : j ∈ T
      · exact congrFun (congrFun h0 i) ⟨j, hj⟩
      · exact hoff i j hj
    · funext i j
      simp only [ext, extendSlots]
      split_ifs with hj
      · rfl
      · exact (hoff i j hj).symm
  have hw0 : ∀ μ, 0 ≤ modeWeight r κ μ := fun μ =>
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun c _ => hκ0 i c _
  calc ∑ μ ∈ univ.filter (fun μ : Fin k → Fin n → F × F => modeSupport μ = T), modeWeight r κ μ
      ≤ ∑ μ ∈ (univ.erase 0).image ext, modeWeight r κ μ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun μ _ _ => hw0 μ
    _ = ∑ M ∈ (univ : Finset (Fin k → T → F × F)).erase 0,
          ∏ i, ∏ c, κ i c (pairWord r T (M i) c) := by
        rw [Finset.sum_image fun M _ M' _ h => hext h]
        exact Finset.sum_congr rfl fun M _ => hw M
    _ = ∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0 := by
        have h0 : ∏ i, ∏ c, κ i c (pairWord r T ((0 : Fin k → T → F × F) i) c) =
            ∏ i, ∏ c, κ i c 0 := by
          simp only [Pi.zero_apply, pairWord_zero]
        rw [eq_sub_iff_add_eq, ← h0, Finset.sum_erase_add _ _ (Finset.mem_univ 0)]
        simp only [rowMass]
        exact (Fintype.prod_sum fun i lam => ∏ c, κ i c (pairWord r T lam c)).symm

end Rows

section FixedModes

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n k ℓ : ℕ}

open Classical in
/-- Fixed modes, averaged over two masks from a box: the support-`T` part of the second moment,
summed over the box pairs, is at most `#B² · G^{-(ℓ-1)#T} · (∏_i rowMass_i - ∏_i ∏_c κ i c 0)`. -/
theorem sum_supportMoment_le_fixedModes (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    (S : ι → Finset F) {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) (r : Fin n → F)
    {κ : Fin k → Fin n → F × F → ℝ} (hκ0 : ∀ i c u, 0 ≤ κ i c u) (s w₀ : Fin n → Fin ℓ → F)
    {T : Finset (Fin n)} (hT : T ≠ ∅) :
    ∑ q ∈ Fintype.piFinset S ×ˢ Fintype.piFinset S,
        supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) * ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T *
        (∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0) := by
  set B := Fintype.piFinset S
  set P := univ.filter (fun μ : Fin k → Fin n → F × F => modeSupport μ = T)
  have hw0 : ∀ μ, 0 ≤ modeWeight r κ μ := fun μ =>
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun c _ => hκ0 i c _
  have hrw : ∀ q : (ι → F) × (ι → F), supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T =
      ∑ μ ∈ P, if Admissible s (E q.1 - w₀) (E q.2 - w₀) μ then modeWeight r κ μ else 0 := by
    intro q
    rw [supportMoment, ← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun μ _ => and_comm) fun _ _ => rfl
  simp_rw [hrw]
  rw [Finset.sum_comm]
  have hc : (0 : ℝ) ≤ ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T := by positivity
  calc ∑ μ ∈ P, ∑ q ∈ B ×ˢ B,
        (if Admissible s (E q.1 - w₀) (E q.2 - w₀) μ then modeWeight r κ μ else 0)
      = ∑ μ ∈ P, modeWeight r κ μ *
          #((B ×ˢ B).filter fun q => Admissible s (E q.1 - w₀) (E q.2 - w₀) μ) := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ μ ∈ P, modeWeight r κ μ * (#B * #B * ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T) := by
        refine Finset.sum_le_sum fun μ hμ => mul_le_mul_of_nonneg_left ?_ (hw0 μ)
        exact card_admissible_le E S hG hS s w₀ (Finset.mem_filter.mp hμ).2
    _ = #B * #B * ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T * ∑ μ ∈ P, modeWeight r κ μ := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ #B * #B * ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T *
          (∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0) := by
        gcongr
        exact sum_modeWeight_support_le hκ0 hT

end FixedModes

section FixedMasks

variable {n k ℓ : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- `coeffOfSlots r` is injective on pair-valued slot vectors for distinct roots: each coordinate
is the transposed Vandermonde matrix applied to the slot values. -/
theorem coeffOfSlots_injective {r : Fin n → F} (hr : Function.Injective r) :
    Function.Injective (coeffOfSlots r : (Fin n → F × F) → Fin n → F × F) := by
  have hdet : (Matrix.vandermonde r).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hr
  have key : ∀ (g : Fin n → F), (fun c : Fin n => ∑ j, r j ^ (c : ℕ) * g j) = 0 → g = 0 := by
    intro g hg
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
    funext c
    have := congrFun hg c
    simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply] using this
  intro ν ν' h
  have h1 : (fun j => (ν j).1 - (ν' j).1) = 0 := key _ <| funext fun c => by
    have := congrArg Prod.fst (congrFun h c)
    simp only [coeffOfSlots, Prod.fst_sum, Prod.smul_fst, smul_eq_mul] at this
    simp only [mul_sub, Finset.sum_sub_distrib, this, sub_self, Pi.zero_apply]
  have h2 : (fun j => (ν j).2 - (ν' j).2) = 0 := key _ <| funext fun c => by
    have := congrArg Prod.snd (congrFun h c)
    simp only [coeffOfSlots, Prod.snd_sum, Prod.smul_snd, smul_eq_mul] at this
    simp only [mul_sub, Finset.sum_sub_distrib, this, sub_self, Pi.zero_apply]
  funext j
  exact Prod.ext (sub_eq_zero.mp (congrFun h1 j)) (sub_eq_zero.mp (congrFun h2 j))

/-- The coefficient words of a pair-valued slot vector, as one word on `Fin n ⊕ Fin n`. -/
def coeffPairMap (r : Fin n → F) : (Fin n → F × F) →ₗ[F] (Fin n ⊕ Fin n → F) where
  toFun ν := fun c => Sum.elim (fun c => (coeffOfSlots r ν c).1) (fun c => (coeffOfSlots r ν c).2) c
  map_add' ν ν' := by
    funext c
    cases c <;> simp [coeffOfSlots, Finset.sum_add_distrib, smul_add]
  map_smul' a ν := by
    funext c
    cases c <;> simp [coeffOfSlots, Prod.fst_sum, Prod.snd_sum, Finset.mul_sum, mul_left_comm]

theorem coeffPairMap_injective {r : Fin n → F} (hr : Function.Injective r) :
    Function.Injective (coeffPairMap r) := by
  intro ν ν' h
  refine coeffOfSlots_injective hr (funext fun c => Prod.ext ?_ ?_)
  · exact congrFun h (Sum.inl c)
  · exact congrFun h (Sum.inr c)

/-- The slot annihilators at the masks `x, x'`. -/
def slotAnnihilators (s x x' : Fin n → Fin ℓ → F) (j : Fin n) : Submodule F (F × F) :=
  slotAnnihilator (s j) (x j) (x' j)

/-- The weight of a slot annihilator `D` in the fixed-mask bound: `0` for `D = 0`, else
`(S₁ ^ k) ^ dim D`. -/
noncomputable def annihilatorWeight (S₁ : ℝ) (k : ℕ) (D : Submodule F (F × F)) : ℝ :=
  if D = ⊥ then 0 else (S₁ ^ k) ^ Module.finrank F D

open Classical in
/-- Fixed masks: for given masks the support-`T` part of the second moment is at most
`∏_{j ∈ T} annihilatorWeight D_j`. The admissible modes supported in `T` are `k`-tuples from the
subspace `∏_{j ∈ T} D_j`, of dimension `∑_{j ∈ T} dim D_j`, and each row's kernel weight over it is
at most `S₁ ^ dim` (`sum_prod_le_pow_finrank`); a support slot with `D_j = 0` admits no mode. -/
theorem supportMoment_le_fixedMasks {r : Fin n → F} (hr : Function.Injective r)
    {κ : Fin k → Fin n → F × F → ℝ} {φ : Fin k → Fin n → F → ℝ} (hκ0 : ∀ i c u, 0 ≤ κ i c u)
    (hκφ : ∀ i c u, κ i c u ≤ φ i c u.1 * φ i c u.2) (hφ0 : ∀ i c u, 0 ≤ φ i c u)
    (hφ1 : ∀ i c u, φ i c u ≤ 1) {S₁ : ℝ} (hS₁ : 1 ≤ S₁) (hφS : ∀ i c, ∑ u, φ i c u ≤ S₁)
    (s x x' : Fin n → Fin ℓ → F) (T : Finset (Fin n)) :
    supportMoment r κ s x x' T ≤
      ∏ j ∈ T, annihilatorWeight S₁ k (slotAnnihilators s x x' j) := by
  classical
  set D := slotAnnihilators s x x'
  by_cases hD : ∃ j ∈ T, D j = ⊥
  · -- no mode has support `T`
    obtain ⟨j, hj, hj0⟩ := hD
    have hempty : (univ : Finset (Fin k → Fin n → F × F)).filter
        (fun μ => Admissible s x x' μ ∧ modeSupport μ = T) = ∅ := by
      refine Finset.filter_false_of_mem fun μ _ ⟨hadm, hsupp⟩ => ?_
      rw [← hsupp, modeSupport, Finset.mem_filter] at hj
      obtain ⟨i, hi⟩ := hj.2
      have := hadm i j
      change μ i j ∈ D j at this
      rw [hj0, Submodule.mem_bot] at this
      exact hi this
    rw [supportMoment, hempty, Finset.sum_empty]
    exact Finset.prod_nonneg fun j _ => by
      unfold annihilatorWeight
      split_ifs
      · exact le_refl 0
      · positivity
  push Not at hD
  set R : Submodule F (Fin n → F × F) :=
    Submodule.pi Set.univ fun j => if j ∈ T then D j else ⊥
  have hRdim : Module.finrank F R = ∑ j ∈ T, Module.finrank F (D j) := by
    rw [Submodule.finrank_pi_univ]
    rw [← Finset.sum_subset (Finset.subset_univ T) fun j _ hj => by rw [if_neg hj, finrank_bot]]
    exact Finset.sum_congr rfl fun j hj => by rw [if_pos hj]
  have hsub : univ.filter (fun μ => Admissible s x x' μ ∧ modeSupport μ = T) ⊆
      Fintype.piFinset fun _ : Fin k => univ.filter (· ∈ R) := by
    intro μ hμ
    obtain ⟨hadm, hsupp⟩ := (Finset.mem_filter.mp hμ).2
    rw [Fintype.mem_piFinset]
    intro i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j _ => ?_⟩
    show μ i j ∈ (if j ∈ T then D j else ⊥)
    split_ifs with hj
    · exact hadm i j
    · rw [Submodule.mem_bot]
      by_contra hne
      exact hj (hsupp ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hne⟩)
  have hw0 : ∀ μ, 0 ≤ modeWeight r κ μ := fun μ =>
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun c _ => hκ0 i c _
  -- one row
  have hrow : ∀ i, ∑ ν ∈ univ.filter (· ∈ R), ∏ c, κ i c (coeffOfSlots r ν c) ≤
      S₁ ^ Module.finrank F R := by
    intro i
    let ψ : Fin n ⊕ Fin n → F → ℝ := fun c => Sum.elim (fun c => φ i c) (fun c => φ i c) c
    refine le_trans (Finset.sum_le_sum fun ν _ => ?_) (sum_prod_le_pow_finrank (coeffPairMap r)
      (coeffPairMap_injective hr) R (φ := ψ) (fun c u => by cases c <;> exact hφ0 i _ u)
      (fun c u => by cases c <;> exact hφ1 i _ u) hS₁ (fun c => by cases c <;> exact hφS i _))
    rw [Fintype.prod_sum_type]
    simp only [ψ, coeffPairMap, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun c _ => hκ0 i c _) fun c _ => hκφ i c _
  calc supportMoment r κ s x x' T
      ≤ ∑ μ ∈ Fintype.piFinset (fun _ : Fin k => univ.filter (· ∈ R)), modeWeight r κ μ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun μ _ _ => hw0 μ
    _ = ∏ i, ∑ ν ∈ univ.filter (· ∈ R), ∏ c, κ i c (coeffOfSlots r ν c) := by
        rw [Finset.prod_univ_sum (fun _ : Fin k => univ.filter (· ∈ R))
          (fun i ν => ∏ c, κ i c (coeffOfSlots r ν c))]
        rfl
    _ ≤ ∏ _i : Fin k, S₁ ^ Module.finrank F R :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun ν _ =>
          Finset.prod_nonneg fun c _ => hκ0 i c _) fun i _ => hrow i
    _ = ∏ j ∈ T, annihilatorWeight S₁ k (D j) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, hRdim,
          Finset.sum_mul, ← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [annihilatorWeight, if_neg (hD j hj), ← pow_mul, mul_comm]

/-- The three slot events of the fixed-mask route at one slot: `0`, `x̂ ∈ span ŝ₁`; `1`,
`x̂' ∈ span (x̂, ŝ₁)`; `2`, `x̂, x̂' ∈ span ŝ₁`. -/
def slotEvent (τ : Fin 3) (s x x' : Fin ℓ → F) : Prop :=
  if τ = 0 then x ∈ Submodule.span F {s}
  else if τ = 1 then x' ∈ Submodule.span F {x, s}
  else x ∈ Submodule.span F {s} ∧ x' ∈ Submodule.span F {s}

/-- The weight of each slot event in the fixed-mask expansion. -/
def slotEventWeight (S₁ : ℝ) (k : ℕ) : Fin 3 → ℝ := ![S₁ ^ k, S₁ ^ k, (S₁ ^ k) ^ 2]

open Classical in
/-- A nonzero slot annihilator forces event `0` or `1`; a full one forces event `2`. Hence
`annihilatorWeight D ≤ ∑_τ slotEventWeight τ · 1[slotEvent τ]`. -/
theorem annihilatorWeight_le_sum {S₁ : ℝ} (hS₁ : 0 ≤ S₁) (k : ℕ) (s x x' : Fin ℓ → F) :
    annihilatorWeight S₁ k (slotAnnihilator s x x') ≤
      ∑ τ, slotEventWeight S₁ k τ * if slotEvent τ s x x' then 1 else 0 := by
  set D := slotAnnihilator s x x'
  have hw : ∀ τ, 0 ≤ slotEventWeight S₁ k τ * if slotEvent τ s x x' then 1 else 0 := by
    intro τ
    refine mul_nonneg ?_ (by split_ifs <;> norm_num)
    fin_cases τ <;> simp [slotEventWeight] <;> positivity
  have hsum : ∑ τ, slotEventWeight S₁ k τ * (if slotEvent τ s x x' then 1 else 0) =
      S₁ ^ k * (if slotEvent 0 s x x' then 1 else 0) +
        S₁ ^ k * (if slotEvent 1 s x x' then 1 else 0) +
        (S₁ ^ k) ^ 2 * (if slotEvent 2 s x x' then 1 else 0) := by
    rw [Fin.sum_univ_three]
    rfl
  unfold annihilatorWeight
  split_ifs with hD
  · exact Finset.sum_nonneg fun τ _ => hw τ
  have hle : Module.finrank F D ≤ 2 := by
    have := Submodule.finrank_le D
    simpa [Module.finrank_prod] using this
  have hpos : Module.finrank F D ≠ 0 := fun h => hD (Submodule.finrank_eq_zero.mp h)
  rw [hsum]
  have hi : ∀ (P : Prop) [Decidable P] (c : ℝ), 0 ≤ c → 0 ≤ c * (if P then (1 : ℝ) else 0) :=
    fun P _ c hc => mul_nonneg hc (by split_ifs <;> norm_num)
  have hk : 0 ≤ S₁ ^ k := pow_nonneg hS₁ k
  have h0 := hi (slotEvent 0 s x x') _ hk
  have h1 := hi (slotEvent 1 s x x') _ hk
  have h2 := hi (slotEvent 2 s x x') _ (sq_nonneg (S₁ ^ k))
  rcases (show Module.finrank F D = 1 ∨ Module.finrank F D = 2 by omega) with h | h
  · obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    have hmem := (mem_span_of_slotPairing hp0 hp)
    rw [h, pow_one]
    by_cases hb : p.2 = 0
    · have : slotEvent 0 s x x' := by simpa [slotEvent] using hmem.1 hb
      rw [if_pos this, mul_one]
      linarith
    · have hx' : x' ∈ Submodule.span F {x, s} := by
        have hsub : Submodule.span F {s} ≤ Submodule.span F {x, s} :=
          Submodule.span_mono (by simp)
        have hx : x ∈ Submodule.span F {x, s} := Submodule.subset_span (by simp)
        have := Submodule.add_mem _ (hsub (hmem.2 hb)) (Submodule.smul_mem _ (p.2⁻¹ * p.1) hx)
        simpa using this
      have : slotEvent 1 s x x' := by simpa [slotEvent] using hx'
      rw [if_pos this, mul_one]
      linarith
  · have htop : D = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_prod]; simp)
    have h10 : ((1 : F), (0 : F)) ∈ D := htop ▸ Submodule.mem_top
    have h01 : ((0 : F), (1 : F)) ∈ D := htop ▸ Submodule.mem_top
    rw [mem_slotAnnihilator] at h10 h01
    simp only [one_smul, zero_smul, sub_zero, zero_sub] at h10 h01
    have : slotEvent 2 s x x' := by
      simp only [slotEvent]
      exact ⟨h10, by simpa using Submodule.neg_mem _ h01⟩
    rw [if_pos this, mul_one, h]
    linarith

theorem prod_dite_mem_eq {M : Type*} [CommMonoid M] (T : Finset (Fin n)) (g : T → M) :
    ∏ j, (if h : j ∈ T then g ⟨j, h⟩ else 1) = ∏ j : T, g j := by
  rw [← Finset.prod_subset (Finset.subset_univ T) fun j _ hj => dif_neg hj,
    ← Finset.prod_coe_sort T]
  exact Finset.prod_congr rfl fun j _ => dif_pos j.2

theorem fin_three_cases (τ : Fin 3) : τ = 0 ∨ τ = 1 ∨ τ = 2 := by
  fin_cases τ <;> simp

/-- The first-stage box factor bound of slot event `τ` (on `x̂`). -/
noncomputable def firstFactor (G ℓ : ℕ) (τ : Fin 3) : ℝ :=
  if τ = 1 then 1 else (G : ℝ) / (G : ℝ) ^ ℓ

/-- The second-stage box factor bound of slot event `τ` (on `x̂'` given `x̂`). -/
noncomputable def secondFactor (G ℓ : ℕ) (τ : Fin 3) : ℝ :=
  if τ = 0 then 1 else if τ = 1 then (G : ℝ) ^ 2 / (G : ℝ) ^ ℓ else (G : ℝ) / (G : ℝ) ^ ℓ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- Two-stage averaging of a slot-event pattern `σ` on `T`: at most
`#B² ∏_{j ∈ T} firstFactor (σ j) · secondFactor (σ j)` pairs of box masks realize it. -/
theorem card_slotEvents_le (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F)) (S : ι → Finset F) {G : ℕ}
    (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) (s w₀ : Fin n → Fin ℓ → F) (T : Finset (Fin n))
    (σ : T → Fin 3) :
    (#((Fintype.piFinset S ×ˢ Fintype.piFinset S).filter fun q =>
        ∀ j : T, slotEvent (σ j) (s j) ((E q.1 - w₀) j) ((E q.2 - w₀) j)) : ℝ) ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) *
        ∏ j : T, (firstFactor G ℓ (σ j) * secondFactor G ℓ (σ j)) := by
  set B := Fintype.piFinset S
  let L₁ : Fin n → Submodule F (Fin ℓ → F) := fun j =>
    if h : j ∈ T then (if σ ⟨j, h⟩ = 1 then ⊤ else Submodule.span F {s j}) else ⊤
  let L₂ : (Fin n → Fin ℓ → F) → Fin n → Submodule F (Fin ℓ → F) := fun x j =>
    if h : j ∈ T then
      (if σ ⟨j, h⟩ = 0 then ⊤
        else if σ ⟨j, h⟩ = 1 then Submodule.span F {x j, s j} else Submodule.span F {s j})
    else ⊤
  have hsub : (B ×ˢ B).filter (fun q =>
        ∀ j : T, slotEvent (σ j) (s j) ((E q.1 - w₀) j) ((E q.2 - w₀) j)) ⊆
      (B ×ˢ B).filter (fun q => E q.1 - w₀ ∈ Submodule.pi Set.univ L₁ ∧
        E q.2 - w₀ ∈ Submodule.pi Set.univ (L₂ (E q.1 - w₀))) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, fun j _ => ?_, fun j _ => ?_⟩
    · show (E q.1 - w₀) j ∈ L₁ j
      simp only [L₁]
      split_ifs with hj h1
      · exact Submodule.mem_top
      · have hev := hq.2 ⟨j, hj⟩
        rcases fin_three_cases (σ ⟨j, hj⟩) with h0 | h1' | h2
        · rw [h0] at hev
          simpa [slotEvent] using hev
        · exact absurd h1' h1
        · rw [h2] at hev
          simp only [slotEvent] at hev
          exact (by simpa using hev : _ ∧ _).1
      · exact Submodule.mem_top
    · show (E q.2 - w₀) j ∈ L₂ (E q.1 - w₀) j
      simp only [L₂]
      split_ifs with hj h0 h1
      · exact Submodule.mem_top
      · have hev := hq.2 ⟨j, hj⟩
        rw [h1] at hev
        simpa [slotEvent] using hev
      · have hev := hq.2 ⟨j, hj⟩
        rcases fin_three_cases (σ ⟨j, hj⟩) with h0' | h1' | h2
        · exact absurd h0' h0
        · exact absurd h1' h1
        · rw [h2] at hev
          simp only [slotEvent] at hev
          exact (by simpa using hev : _ ∧ _).2
      · exact Submodule.mem_top
  -- uniform box factor bounds
  let u₁ : Fin n → ℝ := fun j => if h : j ∈ T then firstFactor G ℓ (σ ⟨j, h⟩) else 1
  let u₂ : Fin n → ℝ := fun j => if h : j ∈ T then secondFactor G ℓ (σ ⟨j, h⟩) else 1
  have hb₁ : ∀ j, boxFactor G (L₁ j) ≤ u₁ j := by
    intro j
    simp only [L₁, u₁, firstFactor]
    split_ifs
    · rw [boxFactor_top G hG]
    · simpa using boxFactor_le hG (finrank_span_singleton_le_one (s j))
    · rw [boxFactor_top G hG]
  have hb₂ : ∀ x j, boxFactor G (L₂ x j) ≤ u₂ j := by
    intro x j
    simp only [L₂, u₂, secondFactor]
    split_ifs
    · rw [boxFactor_top G hG]
    · exact boxFactor_le hG (finrank_span_pair_le_two (x j) (s j))
    · simpa using boxFactor_le hG (finrank_span_singleton_le_one (s j))
    · rw [boxFactor_top G hG]
  have hu₁ : 0 ≤ ∏ j, u₁ j := Finset.prod_nonneg fun j _ =>
    (boxFactor_nonneg G (L₁ j)).trans (hb₁ j)
  have hu₂ : 0 ≤ ∏ j, u₂ j := Finset.prod_nonneg fun j _ =>
    (boxFactor_nonneg G (L₂ 0 j)).trans (hb₂ 0 j)
  have hcount := card_filter_product_le B (fun z => E z - w₀ ∈ Submodule.pi Set.univ L₁)
    (fun z z' => E z' - w₀ ∈ Submodule.pi Set.univ (L₂ (E z - w₀)))
    (c₁ := #B * ∏ j, u₁ j) (c₂ := #B * ∏ j, u₂ j)
    (mul_nonneg (Nat.cast_nonneg _) hu₂)
    ((card_box_pi_le E S hG hS L₁ w₀).trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun j _ => boxFactor_nonneg _ _) fun j _ => hb₁ j)
      (Nat.cast_nonneg _)))
    (fun z => (card_box_pi_le E S hG hS _ w₀).trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun j _ => boxFactor_nonneg _ _) fun j _ => hb₂ _ j)
      (Nat.cast_nonneg _)))
  have hprod : (∏ j, u₁ j) * ∏ j, u₂ j =
      ∏ j : T, (firstFactor G ℓ (σ j) * secondFactor G ℓ (σ j)) := by
    rw [← Finset.prod_mul_distrib, ← prod_dite_mem_eq T]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [u₁, u₂]
    split_ifs <;> simp
  calc (#((B ×ˢ B).filter fun q =>
        ∀ j : T, slotEvent (σ j) (s j) ((E q.1 - w₀) j) ((E q.2 - w₀) j)) : ℝ)
      ≤ #((B ×ˢ B).filter (fun q => E q.1 - w₀ ∈ Submodule.pi Set.univ L₁ ∧
          E q.2 - w₀ ∈ Submodule.pi Set.univ (L₂ (E q.1 - w₀)))) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (#B * ∏ j, u₁ j) * (#B * ∏ j, u₂ j) := hcount
    _ = #B * #B * ∏ j : T, (firstFactor G ℓ (σ j) * secondFactor G ℓ (σ j)) := by
        rw [← hprod]
        ring

/-- The per-slot factor `X` of the fixed-mask route:
`S₁^k G/G^ℓ + S₁^k G²/G^ℓ + S₁^{2k} (G/G^ℓ)²`, that is
`(G^{-(ℓ-1)} + G^{-(ℓ-2)}) S₁^k + G^{-2(ℓ-1)} S₁^{2k}`. -/
noncomputable def fixedMaskFactor (S₁ : ℝ) (k G ℓ : ℕ) : ℝ :=
  ∑ τ, slotEventWeight S₁ k τ * (firstFactor G ℓ τ * secondFactor G ℓ τ)

open Classical in
/-- Fixed masks, averaged over two masks from a box: the support-`T` part of the second moment,
summed over the box pairs, is at most `#B² · X ^ #T` with `X = fixedMaskFactor`. -/
theorem sum_supportMoment_le_fixedMasks (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    (S : ι → Finset F) {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) {r : Fin n → F}
    (hr : Function.Injective r) {κ : Fin k → Fin n → F × F → ℝ} {φ : Fin k → Fin n → F → ℝ}
    (hκ0 : ∀ i c u, 0 ≤ κ i c u) (hκφ : ∀ i c u, κ i c u ≤ φ i c u.1 * φ i c u.2)
    (hφ0 : ∀ i c u, 0 ≤ φ i c u) (hφ1 : ∀ i c u, φ i c u ≤ 1) {S₁ : ℝ} (hS₁ : 1 ≤ S₁)
    (hφS : ∀ i c, ∑ u, φ i c u ≤ S₁) (s w₀ : Fin n → Fin ℓ → F) (T : Finset (Fin n)) :
    ∑ q ∈ Fintype.piFinset S ×ˢ Fintype.piFinset S,
        supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) * fixedMaskFactor S₁ k G ℓ ^ #T := by
  set B := Fintype.piFinset S
  set w := slotEventWeight S₁ k
  set ev : T → Fin 3 → (ι → F) × (ι → F) → Prop := fun j τ q =>
    slotEvent τ (s j) ((E q.1 - w₀) j) ((E q.2 - w₀) j)
  have hS₀ : 0 ≤ S₁ := le_trans zero_le_one hS₁
  have hw0 : ∀ τ, 0 ≤ w τ := by
    intro τ
    fin_cases τ <;> simp [w, slotEventWeight] <;> positivity
  have step1 : ∀ q : (ι → F) × (ι → F), supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤
      ∑ σ : T → Fin 3, (∏ j, w (σ j)) * if ∀ j, ev j (σ j) q then 1 else 0 := by
    intro q
    refine (supportMoment_le_fixedMasks hr hκ0 hκφ hφ0 hφ1 hS₁ hφS s _ _ T).trans ?_
    calc ∏ j ∈ T, annihilatorWeight S₁ k (slotAnnihilators s (E q.1 - w₀) (E q.2 - w₀) j)
        = ∏ j : T, annihilatorWeight S₁ k
            (slotAnnihilator (s j) ((E q.1 - w₀) j) ((E q.2 - w₀) j)) :=
          (Finset.prod_coe_sort T _).symm
      _ ≤ ∏ j : T, ∑ τ, w τ * if ev j τ q then 1 else 0 :=
          Finset.prod_le_prod₀ (fun j _ => by
              unfold annihilatorWeight
              split_ifs
              · exact le_refl 0
              · positivity)
            fun j _ => annihilatorWeight_le_sum hS₀ k _ _ _
      _ = ∑ σ : T → Fin 3, ∏ j, (w (σ j) * if ev j (σ j) q then 1 else 0) :=
          Fintype.prod_sum _
      _ = ∑ σ : T → Fin 3, (∏ j, w (σ j)) * if ∀ j, ev j (σ j) q then 1 else 0 := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.prod_mul_distrib, Finset.prod_boole]
          simp
  calc ∑ q ∈ B ×ˢ B, supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T
      ≤ ∑ q ∈ B ×ˢ B, ∑ σ : T → Fin 3, (∏ j, w (σ j)) * if ∀ j, ev j (σ j) q then 1 else 0 :=
        Finset.sum_le_sum fun q _ => step1 q
    _ = ∑ σ : T → Fin 3, (∏ j, w (σ j)) * #((B ×ˢ B).filter fun q => ∀ j, ev j (σ j) q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ ∑ σ : T → Fin 3, (∏ j, w (σ j)) *
          (#B * #B * ∏ j : T, (firstFactor G ℓ (σ j) * secondFactor G ℓ (σ j))) :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
          (card_slotEvents_le E S hG hS s w₀ T σ) (Finset.prod_nonneg fun j _ => hw0 _)
    _ = #B * #B * ∏ _j : T, fixedMaskFactor S₁ k G ℓ := by
        rw [fixedMaskFactor, Finset.prod_univ_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp only [Finset.prod_mul_distrib, w]
        ring
    _ = #B * #B * fixedMaskFactor S₁ k G ℓ ^ #T := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

end FixedMasks

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n k ℓ : ℕ}

/-- The hypotheses on the normalized pair kernel `κ i c` of row `i` and coefficient `c`: it is
dominated by a product `φ i c u · φ i c v` of single-coefficient weights `0 ≤ φ ≤ min 1 f` with
`∑_u φ ≤ S₁` (the `ℓ¹` Fourier mass), and its squares sum to at most `T₂` (Parseval for the
same-cell pair indicator). -/
structure KernelBounds (κ : Fin k → Fin n → F × F → ℝ) (φ : Fin k → Fin n → F → ℝ) (f : F → ℝ)
    (S₁ T₂ : ℝ) : Prop where
  kernel_nonneg : ∀ i c u, 0 ≤ κ i c u
  kernel_le_mul : ∀ i c u, κ i c u ≤ φ i c u.1 * φ i c u.2
  weight_nonneg : ∀ i c u, 0 ≤ φ i c u
  weight_le_one : ∀ i c u, φ i c u ≤ 1
  weight_le : ∀ i c u, φ i c u ≤ f u
  bound_nonneg : ∀ u, 0 ≤ f u
  weight_sum_le : ∀ i c, ∑ u, φ i c u ≤ S₁
  one_le_mass : 1 ≤ S₁
  kernel_sq_sum_le : ∀ i c, ∑ u, κ i c u ^ 2 ≤ T₂

omit [Field F] [DecidableEq F] in
theorem KernelBounds.kernel_le_one {κ : Fin k → Fin n → F × F → ℝ} {φ : Fin k → Fin n → F → ℝ}
    {f : F → ℝ} {S₁ T₂ : ℝ} (h : KernelBounds κ φ f S₁ T₂) (i : Fin k) (c : Fin n)
    (u : F × F) : κ i c u ≤ 1 :=
  (h.kernel_le_mul i c u).trans ((mul_le_mul (h.weight_le_one i c _) (h.weight_le_one i c _)
    (h.weight_nonneg i c _) zero_le_one).trans_eq (one_mul 1))

/-- The small-support bounds (supplied by the spectral recursion,
`GordieHowe/Applications/MLDSA/Regularity/SmallSupport.lean`): for every nonempty support `T` of
at most `m` slots, the nonzero words of `T` have total `f`-weight at most `δ #T`. -/
structure SmallSupportBounds (r : Fin n → F) (f : F → ℝ) (m : ℕ) (δ : ℕ → ℝ) : Prop where
  bound : ∀ T : Finset (Fin n), T ≠ ∅ → #T ≤ m →
    ∑ y ∈ (powerCode T r n).filter (· ≠ 0), ∏ c, f (y c) ≤ δ #T

/-- The bound on the support-`t` part of the averaged second moment: small supports (`t ≤ m`),
`G^{-(ℓ-1)t} ((1 + δ_t)^{2k} - 1)`; medium supports (`2t ≤ n`), `G^{-(ℓ-1)t} T₂^{kt}`; large
supports, `X ^ t` with `X = fixedMaskFactor S₁ k G ℓ`. -/
noncomputable def supportTerm (n k ℓ G m : ℕ) (δ : ℕ → ℝ) (S₁ T₂ : ℝ) (t : ℕ) : ℝ :=
  if t ≤ m then ((G : ℝ) / (G : ℝ) ^ ℓ) ^ t * ((1 + δ t) ^ (2 * k) - 1)
  else if t + t ≤ n then ((G : ℝ) / (G : ℝ) ^ ℓ) ^ t * (T₂ ^ t) ^ k
  else fixedMaskFactor S₁ k G ℓ ^ t

open Classical in
/-- The second moment averaged over two independent masks drawn uniformly from the box
`∏_i S i` (read in the slot domain through `E` and shifted by `w₀`). -/
noncomputable def averagedSecondMoment (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    (S : ι → Finset F) (r : Fin n → F) (κ : Fin k → Fin n → F × F → ℝ)
    (s w₀ : Fin n → Fin ℓ → F) : ℝ :=
  (∑ q ∈ Fintype.piFinset S ×ˢ Fintype.piFinset S,
      secondMoment r κ s (E q.1 - w₀) (E q.2 - w₀)) /
    (#(Fintype.piFinset S) * #(Fintype.piFinset S))

open Classical in
/-- The support-`T` part of the second moment, summed over the box pairs, is at most
`#B² · supportTerm #T` for every nonempty `T`: fixed modes with the small-support bound for
`#T ≤ m`, fixed modes with two windows for `2 #T ≤ n`, fixed masks otherwise. -/
theorem sum_supportMoment_le_supportTerm (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    (S : ι → Finset F) {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) {r : Fin n → F}
    (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0) {κ : Fin k → Fin n → F × F → ℝ}
    {φ : Fin k → Fin n → F → ℝ} {f : F → ℝ} {S₁ T₂ : ℝ} (hκ : KernelBounds κ φ f S₁ T₂) {m : ℕ}
    {δ : ℕ → ℝ} (hδ : SmallSupportBounds r f m δ) (s w₀ : Fin n → Fin ℓ → F)
    {T : Finset (Fin n)} (hT0 : T ≠ ∅) :
    ∑ q ∈ Fintype.piFinset S ×ˢ Fintype.piFinset S,
        supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) * supportTerm n k ℓ G m δ S₁ T₂ #T := by
  set B := Fintype.piFinset S
  simp only [supportTerm]
  have hκ0 := hκ.kernel_nonneg
  have ha0 : ∀ i, 0 ≤ ∏ c, κ i c 0 := fun i => Finset.prod_nonneg fun c _ => hκ0 i c _
  have hrow0 : ∀ i, ∏ c, κ i c 0 ≤ rowMass r κ i T := by
    intro i
    have := Finset.single_le_sum (f := fun lam : T → F × F => ∏ c, κ i c (pairWord r T lam c))
      (fun lam _ => Finset.prod_nonneg fun c _ => hκ0 i c _) (Finset.mem_univ 0)
    simpa [rowMass, pairWord_zero] using this
  have hc0 : (0 : ℝ) ≤ #B * #B * ((G : ℝ) / (G : ℝ) ^ ℓ) ^ #T := by positivity
  split_ifs with hsmall hmed
  · -- small supports
    rw [← mul_assoc]
    refine (sum_supportMoment_le_fixedModes E S hG hS r hκ0 s w₀ hT0).trans
      (mul_le_mul_of_nonneg_left ?_ hc0)
    have hb : ∀ i, rowMass r κ i T - ∏ c, κ i c 0 ≤ 2 * δ #T + δ #T ^ 2 := fun i =>
      rowMass_sub_zero_le hr hr0 hκ0 hκ.kernel_le_mul hκ.weight_nonneg hκ.weight_le_one
        hκ.weight_le hκ.bound_nonneg i (hδ.bound T hT0 hsmall)
    have hmain := prod_add_sub_prod_le univ (a := fun i => ∏ c, κ i c 0)
      (b := fun i => rowMass r κ i T - ∏ c, κ i c 0) ha0
      (fun i => Finset.prod_le_one₀ (fun c _ => hκ0 i c _) fun c _ => hκ.kernel_le_one i c _)
      (fun i => sub_nonneg.mpr (hrow0 i))
    simp only [add_sub_cancel] at hmain
    refine hmain.trans ?_
    have hbb : ∀ i, 0 ≤ rowMass r κ i T - ∏ c, κ i c 0 := fun i => sub_nonneg.mpr (hrow0 i)
    calc ∏ i, (1 + (rowMass r κ i T - ∏ c, κ i c 0)) - 1
        ≤ ∏ _i : Fin k, (1 + (2 * δ #T + δ #T ^ 2)) - 1 := by
          refine sub_le_sub_right (Finset.prod_le_prod₀ (fun i _ =>
            add_nonneg zero_le_one (hbb i)) fun i _ => by linarith [hb i]) _
      _ = (1 + δ #T) ^ (2 * k) - 1 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
          ring
  · -- medium supports
    rw [← mul_assoc]
    refine (sum_supportMoment_le_fixedModes E S hG hS r hκ0 s w₀ hT0).trans
      (mul_le_mul_of_nonneg_left ?_ hc0)
    calc ∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0 ≤ ∏ i, rowMass r κ i T :=
          sub_le_self _ (Finset.prod_nonneg fun i _ => ha0 i)
      _ ≤ ∏ _i : Fin k, T₂ ^ #T := Finset.prod_le_prod₀
          (fun i _ => (ha0 i).trans (hrow0 i)) fun i _ =>
            rowMass_le_two_windows hr hr0 hκ0 hκ.kernel_le_one hκ.kernel_sq_sum_le i hmed
      _ = (T₂ ^ #T) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · -- large supports
    exact sum_supportMoment_le_fixedMasks E S hG hS hr hκ0 hκ.kernel_le_mul hκ.weight_nonneg
      hκ.weight_le_one hκ.one_le_mass hκ.weight_sum_le s w₀ T

open Classical in
/-- From per-support bounds to the averaged second moment: if the support-`T` part, summed over
the box pairs, is at most `#B² · g #T` for every nonempty `T`, then
`averagedSecondMoment ≤ ∑_{t = 1}^n C(n, t) · g t`. -/
theorem averagedSecondMoment_le_of_sum_supportMoment_le (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    (S : ι → Finset F) {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) (r : Fin n → F)
    (κ : Fin k → Fin n → F × F → ℝ) (s w₀ : Fin n → Fin ℓ → F) {g : ℕ → ℝ}
    (hg : ∀ T : Finset (Fin n), T ≠ ∅ →
      ∑ q ∈ Fintype.piFinset S ×ˢ Fintype.piFinset S,
          supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤
        #(Fintype.piFinset S) * #(Fintype.piFinset S) * g #T) :
    averagedSecondMoment E S r κ s w₀ ≤
      ∑ t ∈ range (n + 1), (n.choose t : ℝ) * (if t = 0 then 0 else g t) := by
  set B := Fintype.piFinset S
  have hB : (0 : ℝ) < #B * #B := by
    have : 0 < #B := by
      rw [Fintype.card_piFinset]
      exact Finset.prod_pos fun i _ => by rw [hS i]; exact hG
    positivity
  set g' : ℕ → ℝ := fun t => if t = 0 then 0 else g t
  have hT : ∀ T : Finset (Fin n), T ≠ ∅ →
      ∑ q ∈ B ×ˢ B, supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤ #B * #B * g' #T := by
    intro T hT0
    have hcard0 : #T ≠ 0 := fun h => hT0 (Finset.card_eq_zero.mp h)
    simp only [g', if_neg hcard0]
    exact hg T hT0
  rw [averagedSecondMoment, div_le_iff₀ hB]
  calc ∑ q ∈ B ×ˢ B, secondMoment r κ s (E q.1 - w₀) (E q.2 - w₀)
      = ∑ T ∈ (univ : Finset (Fin n)).powerset.filter (· ≠ ∅),
          ∑ q ∈ B ×ˢ B, supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T := by
        simp_rw [secondMoment_eq_sum_supportMoment]
        exact Finset.sum_comm
    _ ≤ ∑ T ∈ (univ : Finset (Fin n)).powerset.filter (· ≠ ∅), #B * #B * g' #T :=
        Finset.sum_le_sum fun T hT0 => hT T (Finset.mem_filter.mp hT0).2
    _ = #B * #B * ∑ T ∈ (univ : Finset (Fin n)).powerset, g' #T := by
        rw [← Finset.mul_sum, Finset.sum_filter]
        congr 1
        refine Finset.sum_congr rfl fun T _ => ?_
        split_ifs with h
        · rfl
        · push Not at h
          simp [g', h]
    _ = (∑ t ∈ range (n + 1), (n.choose t : ℝ) * g' t) * (#B * #B) := by
        rw [Finset.sum_powerset_apply_card, Finset.card_univ, Fintype.card_fin, mul_comm]
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [nsmul_eq_mul]

open Classical in
/-- **The averaged second moment.** For distinct nonzero slot roots, kernel bounds
`KernelBounds κ φ f S₁ T₂`, small-support bounds up to `m` slots and a box with sides of size
`G ≥ 1`,
`averagedSecondMoment ≤ ∑_{t = 1}^n C(n, t) · supportTerm t`. -/
theorem averagedSecondMoment_le (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F)) (S : ι → Finset F)
    {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) {r : Fin n → F} (hr : Function.Injective r)
    (hr0 : ∀ j, r j ≠ 0) {κ : Fin k → Fin n → F × F → ℝ} {φ : Fin k → Fin n → F → ℝ}
    {f : F → ℝ} {S₁ T₂ : ℝ} (hκ : KernelBounds κ φ f S₁ T₂) {m : ℕ} {δ : ℕ → ℝ}
    (hδ : SmallSupportBounds r f m δ) (s w₀ : Fin n → Fin ℓ → F) :
    averagedSecondMoment E S r κ s w₀ ≤
      ∑ t ∈ range (n + 1), (n.choose t : ℝ) *
        (if t = 0 then 0 else supportTerm n k ℓ G m δ S₁ T₂ t) :=
  averagedSecondMoment_le_of_sum_supportMoment_le E S hG hS r κ s w₀ fun _ hT0 =>
    sum_supportMoment_le_supportTerm E S hG hS hr hr0 hκ hδ s w₀ hT0

end Main

end GordieHowe.MLDSA.Regularity
