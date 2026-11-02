-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.DensityRunTransport

@[expose] public section

/-!
# Two circuits of the same shape related by carried permutations

Two circuits of the core (`Quantum.Circuit`) with Kraus maps at the same places and queries at the
same places, related gate by gate by a permutation carried along (`Circuit.Twin`): Kraus map `K'`
of the first, read after the carried permutation `σ`, is Kraus map `K` of the second followed by
the next carried permutation `σ'`, on the matrices supported on the current support, which `K`
carries to the next one (`ChRel`, `Keeps`); at a query the carried permutation commutes with the
query and the support is kept (predicates `QI`, `SI`). Then the segments between the queries are
related in the same way (`Circuit.Twin.segments`), the shape the density-matrix transport of
`GordieHowe/Model/QROM/DensityRunTransport.lean` reads.

- `ChRel`, `Keeps`, `ChRel.comp`, `Keeps.comp`, `chRel_ofPerm`, `keeps_ofPerm_of`.
- `Circuit.Twin`, `Circuit.Twin.append`, `Circuit.Twin.queries_eq`, `Circuit.Twin.segments`.
- `Circuit.withPerms`: a basis permutation inserted after each query; `Circuit.seg_withPerms`.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Kraus maps related by carried permutations -/

/-- **`K'` read after `σ` is `K` followed by `σ'`** on the matrices supported on `S`. -/
def ChRel {R R' : Type} [Fintype R] [Fintype R'] (σ' σ : Equiv.Perm ι) (S : Set ι)
    (K' : KrausMap R' ι ι) (K : KrausMap R ι ι) : Prop :=
  ∀ ρ, Supp S ρ → K' (ρ.submatrix σ.symm σ.symm) = (K ρ).submatrix σ'.symm σ'.symm

/-- **`K` carries the support `S` to `S'`.** -/
def Keeps {R : Type} [Fintype R] (S S' : Set ι) (K : KrausMap R ι ι) : Prop :=
  ∀ ρ, Supp S ρ → Supp S' (K ρ)

section Rel

variable {R₁ R₂ R₁' R₂' : Type} [Fintype R₁] [Fintype R₂] [Fintype R₁'] [Fintype R₂']

theorem ChRel.comp {σ'' σ' σ : Equiv.Perm ι} {S S' : Set ι} {K₂' : KrausMap R₂' ι ι}
    {K₂ : KrausMap R₂ ι ι} {K₁' : KrausMap R₁' ι ι} {K₁ : KrausMap R₁ ι ι}
    (h₂ : ChRel σ'' σ' S' K₂' K₂) (h₁ : ChRel σ' σ S K₁' K₁) (hk : Keeps S S' K₁) :
    ChRel σ'' σ S (K₂'.comp K₁') (K₂.comp K₁) := fun ρ hρ => by
  rw [KrausMap.comp_apply, KrausMap.comp_apply, h₁ ρ hρ, h₂ _ (hk ρ hρ)]

theorem Keeps.comp {S S' S'' : Set ι} {K₂ : KrausMap R₂ ι ι} {K₁ : KrausMap R₁ ι ι}
    (h₂ : Keeps S' S'' K₂) (h₁ : Keeps S S' K₁) : Keeps S S'' (K₂.comp K₁) := fun ρ hρ => by
  rw [KrausMap.comp_apply]
  exact h₂ _ (h₁ ρ hρ)

theorem Keeps.mono {S S' T : Set ι} {K : KrausMap R₁ ι ι} (h : Keeps S S' K) (hT : S' ⊆ T) :
    Keeps S T K := fun ρ hρ a b hab => by
  obtain ⟨ha, hb⟩ := h ρ hρ a b hab
  exact ⟨hT ha, hT hb⟩

theorem chRel_identity (σ : Equiv.Perm ι) (S : Set ι) :
    ChRel σ σ S (KrausMap.identity ι) (KrausMap.identity ι) := fun ρ _ => by
  simp

theorem keeps_identity (S : Set ι) : Keeps S S (KrausMap.identity ι) := fun ρ hρ => by
  simpa using hρ

/-- **A basis permutation `π` relates `σ` to `σ'`** on `S` when `π ∘ σ = σ' ∘ π` on `S`. -/
theorem chRel_ofPerm {π : Equiv.Perm ι} {σ' σ : Equiv.Perm ι} {S : Set ι}
    (h : ∀ a ∈ S, π (σ a) = σ' (π a)) :
    ChRel σ' σ S (KrausMap.ofPerm π) (KrausMap.ofPerm π) := fun ρ hρ => by
  rw [KrausMap.ofPerm_apply, KrausMap.ofPerm_apply]
  ext x y
  simp only [Matrix.submatrix_apply]
  by_cases hxy : ρ (π.symm (σ'.symm x)) (π.symm (σ'.symm y)) = 0
  · rw [hxy]
    by_contra hne
    obtain ⟨ha, hb⟩ := hρ _ _ hne
    have ex : σ.symm (π.symm x) = π.symm (σ'.symm x) := by
      apply (π.trans σ').injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
      rw [← h _ ha, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have ey : σ.symm (π.symm y) = π.symm (σ'.symm y) := by
      apply (π.trans σ').injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
      rw [← h _ hb, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hne (by rw [ex, ey, hxy])
  · obtain ⟨ha, hb⟩ := hρ _ _ hxy
    have ex : σ.symm (π.symm x) = π.symm (σ'.symm x) := by
      have := h _ ha
      apply σ.injective
      apply π.injective
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, this, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    have ey : σ.symm (π.symm y) = π.symm (σ'.symm y) := by
      have := h _ hb
      apply σ.injective
      apply π.injective
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, this, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    rw [ex, ey]

/-- **A basis permutation carries `S` to `S'`** when it maps `S` into `S'`. -/
theorem keeps_ofPerm_of {π : Equiv.Perm ι} {S S' : Set ι} (h : ∀ a ∈ S, π a ∈ S') :
    Keeps S S' (KrausMap.ofPerm π) := fun ρ hρ a b hab => by
  rw [KrausMap.ofPerm_apply, Matrix.submatrix_apply] at hab
  obtain ⟨ha, hb⟩ := hρ _ _ hab
  exact ⟨by simpa using h _ ha, by simpa using h _ hb⟩

end Rel

/-! ### Twin circuits -/

namespace Circuit

/-- **Two circuits related gate by gate by a carried permutation**, from the permutation `σ` and
the support `S` at the start to `σe` and `Se` at the end: Kraus maps related by `ChRel` with the
support carried by `Keeps`, queries at which the carried permutation and the support satisfy `QI`
and `SI`. -/
inductive Twin (QI : Equiv.Perm ι → Prop) (SI : Set ι → Prop) (σe : Equiv.Perm ι) (Se : Set ι) :
    Circuit ι → Circuit ι → Equiv.Perm ι → Set ι → Prop
  | nil {σ : Equiv.Perm ι} {S : Set ι} : σ = σe → S = Se → Twin QI SI σe Se .nil .nil σ S
  | kraus {R R' : Type} [Fintype R] [Fintype R'] {K' : KrausMap R' ι ι} {K : KrausMap R ι ι}
      {c' c : Circuit ι} {σ σ' : Equiv.Perm ι} {S S' : Set ι} :
      ChRel σ' σ S K' K → Keeps S S' K → Twin QI SI σe Se c' c σ' S' →
        Twin QI SI σe Se (.kraus K' c') (.kraus K c) σ S
  | query {c' c : Circuit ι} {σ : Equiv.Perm ι} {S : Set ι} : QI σ → SI S →
      Twin QI SI σe Se c' c σ S → Twin QI SI σe Se (.query c') (.query c) σ S

variable {QI : Equiv.Perm ι → Prop} {SI : Set ι → Prop}

/-- **Twin circuits concatenated.** -/
theorem Twin.append {σm σe : Equiv.Perm ι} {Sm Se : Set ι} {c₁' c₁ c₂' c₂ : Circuit ι}
    {σ : Equiv.Perm ι} {S : Set ι} (h₁ : Twin QI SI σm Sm c₁' c₁ σ S)
    (h₂ : Twin QI SI σe Se c₂' c₂ σm Sm) : Twin QI SI σe Se (c₁' ++ c₂') (c₁ ++ c₂) σ S := by
  induction h₁ with
  | nil hσ hS =>
    subst hσ hS
    exact h₂
  | kraus hK hk _ ih => exact .kraus hK hk ih
  | query hq hs _ ih => exact .query hq hs ih

/-- Twin circuits have the same number of queries. -/
theorem Twin.queries_eq {σe : Equiv.Perm ι} {Se : Set ι} {c' c : Circuit ι} {σ : Equiv.Perm ι}
    {S : Set ι} (h : Twin QI SI σe Se c' c σ S) : c'.queries = c.queries := by
  induction h with
  | nil => rfl
  | kraus _ _ _ ih => exact ih
  | query _ _ _ ih => simp [queries, ih]

/-- **The segments of twin circuits are related**: there are carried permutations `P j` (the one
at the start of segment `j`) and supports `S j` with `P 0 = σ`, `S 0 = S`, segment `j` of the first
read after `P j` being segment `j` of the second followed by `P (j + 1)` on `S j`, the second's
segment carrying `S j` to `S (j + 1)`, `P (queries + 1) = σe`, and `QI (P (j + 1))`,
`SI (S (j + 1))` at each query `j`. -/
theorem Twin.segments {σe : Equiv.Perm ι} {Se : Set ι} {c' c : Circuit ι} {σ : Equiv.Perm ι}
    {S : Set ι} (h : Twin QI SI σe Se c' c σ S) :
    ∃ (P : ℕ → Equiv.Perm ι) (T : ℕ → Set ι), P 0 = σ ∧ T 0 = S ∧
      (∀ j, ChRel (P (j + 1)) (P j) (T j) (c'.seg j).K (c.seg j).K ∧
        Keeps (T j) (T (j + 1)) (c.seg j).K) ∧
      P (c.queries + 1) = σe ∧ ∀ j < c.queries, QI (P (j + 1)) ∧ SI (T (j + 1)) := by
  induction h with
  | @nil σ S hσ hS =>
    subst hσ hS
    refine ⟨fun _ => σ, fun _ => S, rfl, rfl, fun j => ?_, rfl,
      fun j hj => absurd hj (by simp [queries])⟩
    rw [Circuit.seg_nil j]
    exact ⟨chRel_identity σ S, keeps_identity S⟩
  | @kraus R R' _ _ K' K c' c σ σ' S S' hK hk _ ih =>
    obtain ⟨P, T, hP0, hT0, hseg, hend, hq⟩ := ih
    refine ⟨fun j => if j = 0 then σ else P j, fun j => if j = 0 then S else T j, rfl, rfl,
      fun j => ?_, by simpa [queries] using hend, fun j hj => by simpa [queries] using hq j hj⟩
    cases j with
    | zero =>
      have h0 := hseg 0
      rw [hP0, hT0] at h0
      refine ⟨?_, ?_⟩
      · simp only [if_true, show (0 + 1 : ℕ) ≠ 0 from by omega, if_false]
        exact h0.1.comp hK hk
      · simp only [if_true, show (0 + 1 : ℕ) ≠ 0 from by omega, if_false]
        exact h0.2.comp hk
    | succ j =>
      simp only [show j + 1 ≠ 0 from by omega, show j + 1 + 1 ≠ 0 from by omega, if_false]
      exact hseg (j + 1)
  | @query c' c σ S hq hs _ ih =>
    obtain ⟨P, T, hP0, hT0, hseg, hend, hq'⟩ := ih
    refine ⟨fun j => if j = 0 then σ else P (j - 1), fun j => if j = 0 then S else T (j - 1), rfl,
      rfl, fun j => ?_, ?_, fun j hj => ?_⟩
    · cases j with
      | zero =>
        simp only [if_true, show (0 + 1 : ℕ) ≠ 0 from by omega, if_false, Nat.sub_self, hP0, hT0]
        exact ⟨chRel_identity σ S, keeps_identity S⟩
      | succ j =>
        simp only [show j + 1 ≠ 0 from by omega, show j + 1 + 1 ≠ 0 from by omega, if_false,
          Nat.add_sub_cancel]
        exact hseg j
    · simp only [queries, show c.queries + 1 + 1 ≠ 0 from by omega, if_false, Nat.add_sub_cancel]
      exact hend
    · cases j with
      | zero =>
        simp only [show (0 + 1 : ℕ) ≠ 0 from by omega, if_false, Nat.sub_self, hP0, hT0]
        exact ⟨hq, hs⟩
      | succ j =>
        simp only [show j + 1 + 1 ≠ 0 from by omega, if_false, Nat.add_sub_cancel]
        exact hq' j (by simp [queries] at hj; omega)

/-- **A basis permutation inserted after each query**: `π (k + 1)` after the `k`-th query, the
queries counted from `k₀`. -/
def withPerms (π : ℕ → Equiv.Perm ι) : ℕ → Circuit ι → Circuit ι
  | _, nil => nil
  | k, kraus K c => kraus K (withPerms π k c)
  | k, query c => query (kraus (KrausMap.ofPerm (π (k + 1))) (withPerms π (k + 1) c))

theorem queries_withPerms (π : ℕ → Equiv.Perm ι) (k : ℕ) (c : Circuit ι) :
    (c.withPerms π k).queries = c.queries := by
  induction c generalizing k with
  | nil => rfl
  | kraus K c ih => exact ih k
  | query c ih => simp [withPerms, queries, ih]

/-- **The segments of a circuit with permutations inserted after the queries**: segment
`1 ≤ j ≤ queries` is the circuit's segment `j` after `π (k₀ + j)`. -/
theorem seg_withPerms (π : ℕ → Equiv.Perm ι) (k : ℕ) (c : Circuit ι) (j : ℕ) (hj : j ≤ c.queries)
    (ρ : Matrix ι ι ℂ) :
    ((c.withPerms π k).seg j).K ρ =
      (c.seg j).K (if j = 0 then ρ else ρ.submatrix (π (k + j)).symm (π (k + j)).symm) := by
  induction c generalizing k j ρ with
  | nil =>
    obtain rfl : j = 0 := by simpa [queries] using hj
    rfl
  | kraus K c ih =>
    cases j with
    | zero =>
      change ((c.withPerms π k).head.K.comp K) ρ = ((head c).K.comp K) ρ
      rw [KrausMap.comp_apply, KrausMap.comp_apply]
      have := ih k 0 (Nat.zero_le _) (K ρ)
      rw [if_pos rfl] at this
      exact this
    | succ j =>
      change ((c.withPerms π k).seg (j + 1)).K ρ = (c.seg (j + 1)).K _
      exact ih k (j + 1) hj ρ
  | query c ih =>
    cases j with
    | zero =>
      change (KrausMap.identity ι) ρ = (KrausMap.identity ι) ρ
      rfl
    | succ j =>
      have hj' : j ≤ c.queries := by simpa [queries] using hj
      change ((kraus (KrausMap.ofPerm (π (k + 1))) (c.withPerms π (k + 1))).seg j).K ρ =
        (c.seg j).K _
      cases j with
      | zero =>
        change (((c.withPerms π (k + 1)).head).K.comp (KrausMap.ofPerm (π (k + 1)))) ρ = _
        rw [KrausMap.comp_apply, KrausMap.ofPerm_apply]
        have := ih (k + 1) 0 (Nat.zero_le _) (ρ.submatrix (π (k + 1)).symm (π (k + 1)).symm)
        rw [if_pos rfl] at this
        exact this
      | succ j =>
        change ((c.withPerms π (k + 1)).seg (j + 1)).K ρ = (c.seg (j + 1)).K _
        rw [ih (k + 1) (j + 1) hj' ρ]
        simp only [show j + 1 ≠ 0 from by omega, show j + 1 + 1 ≠ 0 from by omega, if_false]
        rw [show k + 1 + (j + 1) = k + (j + 1 + 1) by omega]

end Circuit

end GordieHowe.Quantum
