-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fintype.Pi
public import GordieHowe.Foundations.ToMathlib.BoxSubspace

@[expose] public section

/-!
# Product weights over a code with information sets

For a set `C ⊆ ι → A` of words and a window `W ⊆ ι`, `W` is an *information set* of `C` when
restricting to `W` maps `C` bijectively onto all of `W → A` (`IsInformationSet`). Sums of product
weights `∑_{y ∈ C} ∏_i h i (y i)` with `0 ≤ h ≤ 1` are then bounded by sums over the alphabet:

- `sum_prod_window_eq`: over an information set the product sum factors,
  `∑_{y ∈ C} ∏_{i ∈ W} g i (y i) = ∏_{i ∈ W} ∑_a g i a`;
- `sum_prod_le_window`: one window, `∑_{y ∈ C} ∏_i h i (y i) ≤ ∏_{i ∈ W} ∑_a h i a`;
- `sum_prod_le_two_windows`: two disjoint windows and Cauchy–Schwarz,
  `∑_{y ∈ C} ∏_i h i (y i) ≤ S ^ r` when both have `r` coordinates and `∑_a h i a ^ 2 ≤ S`.

These are equation (6) of "A shorter proof of the stated HighBits regularity claim" (10 September
2026, Section 3), first case ("keep two disjoint windows, discard the other factors (which are at
most one), and apply Cauchy–Schwarz"), together with its one-window form. Nothing requires `C` to
be a subspace, so every translate of a code with information sets has the same ones.

`vandermonde_isInformationSet`: the words `y b = ∑_{j ∈ T} λ_j r_j ^ b` (`λ` free) with distinct
nonzero `r_j` have every window of `#T` consecutive positions as an information set, since the
restricted map has matrix `(r_j ^ (s + b))_{b, j}`, a Vandermonde matrix times an invertible
diagonal matrix (note, Section 3: "every `r` consecutive coordinates of `C_T` form an information
set").
-/

open Finset
open scoped BigOperators

namespace GordieHowe

section InformationSet

variable {ι A : Type*} [Fintype A]

/-- `W` is an information set of `C`: restriction to `W` maps `C` bijectively onto `W → A`. -/
def IsInformationSet (C : Finset (ι → A)) (W : Finset ι) : Prop :=
  Set.BijOn (fun y : ι → A => fun i : W => y i) C Set.univ

/-- Over an information set the product sum factors:
`∑_{y ∈ C} ∏_{i ∈ W} g i (y i) = ∏_{i ∈ W} ∑_a g i a`. -/
theorem sum_prod_window_eq {C : Finset (ι → A)} {W : Finset ι} (hW : IsInformationSet C W)
    (g : ι → A → ℝ) :
    ∑ y ∈ C, ∏ i ∈ W, g i (y i) = ∏ i ∈ W, ∑ a, g i a := by
  classical
  have h1 : ∑ y ∈ C, ∏ i ∈ W, g i (y i) = ∑ z : W → A, ∏ i : W, g i (z i) := by
    refine Finset.sum_nbij (fun y : ι → A => fun i : W => y i) (fun _ _ => Finset.mem_univ _)
      hW.injOn (fun z _ => ?_) (fun y _ => ?_)
    · obtain ⟨y, hy, rfl⟩ := hW.surjOn (Set.mem_univ z)
      exact ⟨y, hy, rfl⟩
    · exact (Finset.prod_coe_sort W fun i => g i (y i)).symm
  rw [h1, ← Fintype.prod_sum (fun (i : W) (a : A) => g i a)]
  exact Finset.prod_coe_sort W fun i => ∑ a, g i a

omit [Fintype A] in
/-- A parametrized code whose restriction to `W` is a bijection from the parameters: `W` is an
information set of the image, and the parametrization is injective. -/
theorem isInformationSet_image_of_bijective {P : Type*} [Fintype P] [DecidableEq (ι → A)]
    (g : P → ι → A) {W : Finset ι} (hg : Function.Bijective fun p => fun i : W => g p i) :
    IsInformationSet (Finset.univ.image g) W ∧ Function.Injective g := by
  refine ⟨⟨fun y _ => Set.mem_univ _, ?_, fun z _ => ?_⟩, fun p p' h => hg.1 (by simp only [h])⟩
  · rintro y hy y' hy' hyy
    simp only [Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ, true_and] at hy hy'
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨p', rfl⟩ := hy'
    rw [hg.1 hyy]
  · obtain ⟨p, hp⟩ := hg.2 z
    exact ⟨g p, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ p)), hp⟩

variable [Fintype ι] [DecidableEq ι]

omit [Fintype A] in
/-- Discarding the factors off `W`: for `0 ≤ h ≤ 1`,
`∏_i h i (y i) ≤ ∏_{i ∈ W} h i (y i)`. -/
theorem prod_le_prod_window {h : ι → A → ℝ} (h0 : ∀ i a, 0 ≤ h i a) (h1 : ∀ i a, h i a ≤ 1)
    (W : Finset ι) (y : ι → A) : ∏ i, h i (y i) ≤ ∏ i ∈ W, h i (y i) := by
  rw [← Finset.prod_mul_prod_compl W]
  refine mul_le_of_le_one_right (Finset.prod_nonneg fun i _ => h0 i _) ?_
  exact Finset.prod_le_one₀ (fun i _ => h0 i _) fun i _ => h1 i _

/-- One window: `∑_{y ∈ C} ∏_i h i (y i) ≤ ∏_{i ∈ W} ∑_a h i a` for `0 ≤ h ≤ 1`. -/
theorem sum_prod_le_window {C : Finset (ι → A)} {W : Finset ι} (hW : IsInformationSet C W)
    {h : ι → A → ℝ} (h0 : ∀ i a, 0 ≤ h i a) (h1 : ∀ i a, h i a ≤ 1) :
    ∑ y ∈ C, ∏ i, h i (y i) ≤ ∏ i ∈ W, ∑ a, h i a := by
  rw [← sum_prod_window_eq hW h]
  exact Finset.sum_le_sum fun y _ => prod_le_prod_window h0 h1 W y

/-- One window with a uniform bound: `∑_{y ∈ C} ∏_i h i (y i) ≤ S ^ #W` when `∑_a h i a ≤ S`. -/
theorem sum_prod_le_window_pow {C : Finset (ι → A)} {W : Finset ι} (hW : IsInformationSet C W)
    {h : ι → A → ℝ} (h0 : ∀ i a, 0 ≤ h i a) (h1 : ∀ i a, h i a ≤ 1) {S : ℝ}
    (hS : ∀ i, ∑ a, h i a ≤ S) :
    ∑ y ∈ C, ∏ i, h i (y i) ≤ S ^ #W := by
  refine (sum_prod_le_window hW h0 h1).trans ?_
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun a _ => h0 i a) fun i _ => hS i

/-- Two disjoint windows: for `0 ≤ h ≤ 1` with `∑_a h i a ^ 2 ≤ S` at every coordinate and
disjoint information sets `W₁, W₂` of `r` coordinates each, `∑_{y ∈ C} ∏_i h i (y i) ≤ S ^ r`. -/
theorem sum_prod_le_two_windows {C : Finset (ι → A)} {W₁ W₂ : Finset ι}
    (hW₁ : IsInformationSet C W₁) (hW₂ : IsInformationSet C W₂) (hdisj : Disjoint W₁ W₂)
    {r : ℕ} (hr₁ : #W₁ = r) (hr₂ : #W₂ = r)
    {h : ι → A → ℝ} (h0 : ∀ i a, 0 ≤ h i a) (h1 : ∀ i a, h i a ≤ 1) {S : ℝ}
    (hS : ∀ i, ∑ a, h i a ^ 2 ≤ S) :
    ∑ y ∈ C, ∏ i, h i (y i) ≤ S ^ r := by
  set F₁ := fun y : ι → A => ∏ i ∈ W₁, h i (y i)
  set F₂ := fun y : ι → A => ∏ i ∈ W₂, h i (y i)
  have hpt : ∀ y, ∏ i, h i (y i) ≤ F₁ y * F₂ y := by
    intro y
    rw [← Finset.prod_union hdisj]
    exact prod_le_prod_window h0 h1 _ y
  have hsq : ∀ (W : Finset ι), IsInformationSet C W → #W = r →
      ∑ y ∈ C, (∏ i ∈ W, h i (y i)) ^ 2 ≤ S ^ r := by
    intro W hW hr
    have : ∑ y ∈ C, (∏ i ∈ W, h i (y i)) ^ 2 = ∏ i ∈ W, ∑ a, h i a ^ 2 := by
      rw [← sum_prod_window_eq hW (fun i a => h i a ^ 2)]
      exact Finset.sum_congr rfl fun y _ => (Finset.prod_pow _ _ _).symm
    rw [this, ← hr, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _) fun i _ => hS i
  have hS0 : 0 ≤ S ^ r := le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hsq W₁ hW₁ hr₁)
  calc ∑ y ∈ C, ∏ i, h i (y i) ≤ ∑ y ∈ C, F₁ y * F₂ y := Finset.sum_le_sum fun y _ => hpt y
    _ ≤ √(∑ y ∈ C, F₁ y ^ 2) * √(∑ y ∈ C, F₂ y ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √(S ^ r) * √(S ^ r) := by
        gcongr
        · exact hsq W₁ hW₁ hr₁
        · exact hsq W₂ hW₂ hr₂
    _ = S ^ r := Real.mul_self_sqrt hS0

end InformationSet

section Subspace

variable {ι F V : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Product weights over a subspace: for an injective linear map `L : V → (ι → F)`, a subspace
`R ⊆ V` and weights `0 ≤ φ ≤ 1` with `∑_u φ c u ≤ S` (`1 ≤ S`),
`∑_{v ∈ R} ∏_c φ c (L v c) ≤ S ^ dim R`. The image `L R` projects injectively onto at most
`dim R` coordinates (`Submodule.exists_finset_card_le_finrank_injOn`); keep those factors only. -/
theorem sum_prod_le_pow_finrank (L : V →ₗ[F] (ι → F)) (hL : Function.Injective L)
    (R : Submodule F V) [DecidablePred (· ∈ R)] {φ : ι → F → ℝ} (h0 : ∀ c u, 0 ≤ φ c u)
    (h1 : ∀ c u, φ c u ≤ 1) {S : ℝ} (hS1 : 1 ≤ S) (hS : ∀ c, ∑ u, φ c u ≤ S) :
    ∑ v ∈ univ.filter (· ∈ R), ∏ c, φ c (L v c) ≤ S ^ Module.finrank F R := by
  obtain ⟨P, hP, hinj⟩ := (R.map L).exists_finset_card_le_finrank_injOn
  have hrank : Module.finrank F (R.map L) = Module.finrank F R :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hL R).symm
  let π : V → (P → F) := fun v c => L v c
  have hπ : Set.InjOn π (univ.filter (· ∈ R) : Finset V) := by
    intro v hv v' hv' hvv
    have hv : v ∈ R := (Finset.mem_filter.mp hv).2
    have hv' : v' ∈ R := (Finset.mem_filter.mp hv').2
    have hd : L (v - v') ∈ R.map L := Submodule.mem_map_of_mem (R.sub_mem hv hv')
    have h0' := hinj _ hd fun c hc => by
      have := congrFun hvv ⟨c, hc⟩
      simp only [π] at this
      rw [map_sub, Pi.sub_apply, this, sub_self]
    rw [map_sub, sub_eq_zero] at h0'
    exact hL h0'
  have hSnn : 0 ≤ S := le_trans zero_le_one hS1
  calc ∑ v ∈ univ.filter (· ∈ R), ∏ c, φ c (L v c)
      ≤ ∑ v ∈ univ.filter (· ∈ R), ∏ c ∈ P, φ c (L v c) :=
        Finset.sum_le_sum fun v _ => prod_le_prod_window h0 h1 P (L v)
    _ = ∑ u ∈ (univ.filter (· ∈ R)).image π, ∏ c : P, φ c (u c) := by
        rw [Finset.sum_image hπ]
        exact Finset.sum_congr rfl fun v _ => (Finset.prod_coe_sort P fun c => φ c (L v c)).symm
    _ ≤ ∑ u : P → F, ∏ c : P, φ c (u c) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun u _ _ =>
          Finset.prod_nonneg fun c _ => h0 c _
    _ = ∏ c : P, ∑ u, φ c u := (Fintype.prod_sum (fun (c : P) (u : F) => φ c u)).symm
    _ ≤ ∏ _c : P, S := Finset.prod_le_prod₀ (fun c _ => Finset.sum_nonneg fun u _ => h0 c u)
        fun c _ => hS c
    _ = S ^ #P := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    _ ≤ S ^ Module.finrank F R := pow_le_pow_right₀ hS1 (hrank ▸ hP)

end Subspace

section Vandermonde

variable {J F : Type*} [DecidableEq J] [Field F] [Fintype F] [DecidableEq F]

/-- The word `b ↦ ∑_{j ∈ T} λ_j r_j ^ b`, `b < n`, of the amplitudes `λ : T → F`. -/
def powerCodeWord (T : Finset J) (r : J → F) (n : ℕ) (lam : T → F) : Fin n → F :=
  fun b => ∑ j : T, lam j * r j ^ (b : ℕ)

/-- The words `y b = ∑_{j ∈ T} λ_j r_j ^ b`, for `b < n`, as `λ` ranges over `T → F`. -/
noncomputable def powerCode (T : Finset J) (r : J → F) (n : ℕ) : Finset (Fin n → F) :=
  Finset.univ.image (powerCodeWord T r n)

/-- The embedding `i ↦ s + i` of `Fin m` into `Fin n`, for `s + m ≤ n`. -/
def shiftEmbedding {n s m : ℕ} (h : s + m ≤ n) : Fin m ↪ Fin n :=
  ⟨fun i => ⟨s + i, by omega⟩, fun i j hij => by
    simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at hij
    exact Fin.ext hij⟩

@[simp] theorem val_shiftEmbedding {n s m : ℕ} (h : s + m ≤ n) (i : Fin m) :
    ((shiftEmbedding h i : Fin n) : ℕ) = s + i := rfl

/-- The window of positions `s, s + 1, …, s + m - 1` in `Fin n`, for `s + m ≤ n`. -/
def consecutiveWindow {n s m : ℕ} (h : s + m ≤ n) : Finset (Fin n) :=
  Finset.univ.map (shiftEmbedding h)

theorem card_consecutiveWindow {n s m : ℕ} (h : s + m ≤ n) : #(consecutiveWindow h) = m := by
  rw [consecutiveWindow, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem disjoint_consecutiveWindow {n m : ℕ} (h₁ : 0 + m ≤ n) (h₂ : m + m ≤ n) :
    Disjoint (consecutiveWindow h₁) (consecutiveWindow h₂) := by
  rw [Finset.disjoint_left]
  intro b hb hb'
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hb
  obtain ⟨j, -, hj⟩ := Finset.mem_map.mp hb'
  have := congrArg Fin.val hj
  simp only [val_shiftEmbedding] at this
  omega

omit [DecidableEq J] [Fintype F] [DecidableEq F] in
/-- For distinct nonzero `r_j` (`j ∈ T`), the amplitudes `λ` are determined by, and determine
freely, the word of `λ` on any window of `#T` consecutive positions: the restricted map has matrix
`(r_j ^ (s + i))_{i, j}`, a Vandermonde matrix times an invertible diagonal matrix. -/
theorem bijective_window_powerCodeWord {T : Finset J} {r : J → F} (hr : Set.InjOn r T)
    (hr0 : ∀ j ∈ T, r j ≠ 0) {n s : ℕ} (hs : s + #T ≤ n) :
    Function.Bijective fun lam : T → F => fun b : consecutiveWindow hs => powerCodeWord T r n lam b
    := by
  classical
  set W := consecutiveWindow hs
  have hWc : #W = #T := card_consecutiveWindow hs
  -- The restricted linear map `λ ↦ (b ↦ ∑_j λ_j r_j ^ b)` on `W`.
  let Φ : (T → F) →ₗ[F] (W → F) :=
    { toFun := fun lam b => ∑ j : T, lam j * r j ^ ((b : Fin n) : ℕ)
      map_add' := fun x y => by
        funext b
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext b
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  -- The `i`-th window position `s + i`.
  let pos : Fin #T → W := fun i =>
    ⟨shiftEmbedding hs i, Finset.mem_map_of_mem _ (Finset.mem_univ i)⟩
  -- Injectivity of `Φ`: the matrix `r_j ^ (s + i)` is Vandermonde times a diagonal.
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro lam hlam
    let eT := T.equivFin
    let v : Fin #T → F := fun k => r (eT.symm k)
    have hv : Function.Injective v := by
      intro k k' hk
      exact eT.symm.injective (Subtype.ext (hr (eT.symm k).2 (eT.symm k').2 hk))
    let μ : Fin #T → F := fun k => lam (eT.symm k) * v k ^ s
    have hμ : (Matrix.vandermonde v).transpose.mulVec μ = 0 := by
      funext i
      have h := congrFun hlam (pos i)
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, pos, val_shiftEmbedding] at h
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
        Pi.zero_apply, μ]
      rw [← h, ← eT.symm.sum_comp]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [v, pow_add]
      ring
    have hdet : (Matrix.vandermonde v).transpose.det ≠ 0 := by
      rw [Matrix.det_transpose]
      exact Matrix.det_vandermonde_ne_zero_iff.mpr hv
    have hμ0 : μ = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hμ
    funext j
    have h := congrFun hμ0 (eT j)
    simp only [μ, v, Equiv.symm_apply_apply, Pi.zero_apply] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff'.mp h).1 (hr0 j j.2)
  have hsurj : Function.Surjective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    simp [Module.finrank_fintype_fun_eq_card, hWc]
  exact ⟨hinj, hsurj⟩

/-- Every window of `#T` consecutive positions is an information set of `powerCode T r n`, for
distinct nonzero `r_j` (`j ∈ T`). -/
theorem vandermonde_isInformationSet {T : Finset J} {r : J → F} (hr : Set.InjOn r T)
    (hr0 : ∀ j ∈ T, r j ≠ 0) {n s : ℕ} (hs : s + #T ≤ n) :
    IsInformationSet (powerCode T r n) (consecutiveWindow hs) :=
  (isInformationSet_image_of_bijective _ (bijective_window_powerCodeWord hr hr0 hs)).1

end Vandermonde

end GordieHowe
