-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.ExpandCohBlock

@[expose] public section

/-!
# Pairs of Kraus maps on the blocks of a label, under composition

For a label `ℓ : ι → Option L` of the basis states:

- `KeepsNone ℓ K`: on the columns with label `none`, the nonzero rows have label `none`.
- `BlockIso ℓ K`: `K` keeps the blocks and the `none` label, and the overlaps of its rows of
  every block `r` from two columns are those of the identity. Basis permutations that keep the
  label (`BlockIso.ofPerm`), the identity and the projective measurement of a function
  (`BlockIso.measureFn`) are examples; `BlockIso.comp`.
- `SetIso S K`: the nonzero entries of `K` have the row in `S` iff the column is.
- `PairOn ℓ r Sr Sc K K'`: `K` and `K'` agree on the rows in `Sr` and columns in `Sc` with label
  `none` or `some r`; `PairOn.comp`.
- `PairNone ℓ Sc Sr K K'`: both move `Sc` into `Sr` and keep the blocks there, agree on the rows
  in `Sr` with label `none`, and have the same overlaps into every block from two columns in `Sc`
  with label `none`; kept by composing with a block isometry keeping the set before
  (`PairNone.comp_left`) or after (`PairNone.comp_right`).
- `rowGram_comp`: the overlaps of a composition.
- `OnFst`: a Kraus map on the first factor of a split, with the transports of the above.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → Option L)

/-- **A Kraus map keeps the `none` label**: on the columns with label `none`, its nonzero rows have
label `none`. -/
def KeepsNone {R : Type*} [Fintype R] (K : KrausMap R ι ι) : Prop :=
  ∀ i a b, ℓ b = none → K.op i a b ≠ 0 → ℓ a = none

/-- **Two Kraus maps agree on the block `r` along permutations**: on the rows in `Sr` and the
columns in `Sc` with label `none` or `some r`, the operator `ρ i` of `K'` read along `πr` on the
rows and `πc` on the columns is the operator `i` of `K`. -/
def PairOn {R : Type*} [Fintype R] (r : L) (ρ : Equiv.Perm R) (πr πc : Equiv.Perm ι)
    (Sr Sc : Set ι) (K K' : KrausMap R ι ι) : Prop :=
  ∀ i a b, InBlock ℓ r a → a ∈ Sr → InBlock ℓ r b → b ∈ Sc → K'.op (ρ i) (πr a) (πc b) = K.op i a b

/-- **A Kraus map keeps a set in both directions**: its nonzero entries have the row in `S` iff
the column is. -/
def SetIso {R : Type*} [Fintype R] (S : Set ι) (K : KrausMap R ι ι) : Prop :=
  ∀ i a b, K.op i a b ≠ 0 → (a ∈ S ↔ b ∈ S)

variable [DecidableEq L]

/-- **A block isometry**: it keeps the blocks and the `none` label, and its rows of every block
have the overlaps of the identity's. -/
structure BlockIso {R : Type*} [Fintype R] (K : KrausMap R ι ι) : Prop where
  /-- The blocks are kept. -/
  keeps : ∀ i, KeepsBlocks ℓ (K.op i)
  /-- The `none` label is kept. -/
  keepsNone : KeepsNone ℓ K
  /-- The overlaps of the rows of a block are the identity's. -/
  gram : ∀ r m n, rowGram ℓ r K m n = if m = n ∧ ℓ m = some r then 1 else 0

/-- **Two Kraus maps on the `none` block, from the sets `Sc` to `Sr` for the first and `Sc'` to
`Sr'` for the second**: each moves its column set into its row set and keeps the blocks there,
they agree on the rows in `Sr` with label `none` from the columns in `Sc` with label `none`, and
their rows of every block have the same overlaps from two columns in `Sc` with label `none`. -/
structure PairNone {R : Type*} [Fintype R] (Sc Sr Sc' Sr' : Set ι) (K K' : KrausMap R ι ι) :
    Prop where
  /-- The first moves `Sc` into `Sr`. -/
  keepsSet : ∀ i, KeepsSet Sc Sr (K.op i)
  /-- The second moves `Sc'` into `Sr'`. -/
  keepsSet' : ∀ i, KeepsSet Sc' Sr' (K'.op i)
  /-- The first keeps the blocks on `Sc`. -/
  keeps : ∀ i, KeepsBlocksOn Sc ℓ (K.op i)
  /-- The second keeps the blocks on `Sc'`. -/
  keeps' : ∀ i, KeepsBlocksOn Sc' ℓ (K'.op i)
  /-- Agreement on the rows in `Sr` with label `none` from the columns in `Sc` with label
  `none`. -/
  row_none_eq : ∀ i a b, a ∈ Sr → b ∈ Sc → ℓ a = none → ℓ b = none → K'.op i a b = K.op i a b
  /-- The overlaps into every block from two columns in `Sc` with label `none`. -/
  gram_eq : ∀ r c d, c ∈ Sc → d ∈ Sc → ℓ c = none → ℓ d = none →
    rowGram ℓ r K' c d = rowGram ℓ r K c d

variable {ℓ}

omit [DecidableEq L] in
/-- **A product keeps the blocks** when both factors do. -/
theorem KeepsBlocks.mul {A B : Matrix ι ι ℂ} (hA : KeepsBlocks ℓ A) (hB : KeepsBlocks ℓ B) :
    KeepsBlocks ℓ (A * B) := fun r' a b hb hne => by
  rw [Matrix.mul_apply] at hne
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact hA r' a m (hB r' m b hb (right_ne_zero_of_mul hm)) (left_ne_zero_of_mul hm)

omit [DecidableEq L] in
/-- **A nonzero entry from a row with label `none` of a matrix keeping the blocks** has its column
with label `none`. -/
theorem KeepsBlocks.col_none {A : Matrix ι ι ℂ} (hA : KeepsBlocks ℓ A) {a m : ι}
    (ha : ℓ a = none) (hne : A a m ≠ 0) : ℓ m = none := by
  rcases hm : ℓ m with _ | r'
  · rfl
  · have := hA r' a m hm hne
    rw [ha] at this
    exact absurd this (by simp)

omit [DecidableEq L] in
/-- **A nonzero entry from a row of the block `r` of a matrix keeping the blocks** has its column in
the block. -/
theorem KeepsBlocks.col_inBlock {A : Matrix ι ι ℂ} (hA : KeepsBlocks ℓ A) {r : L} {a m : ι}
    (ha : InBlock ℓ r a) (hne : A a m ≠ 0) : InBlock ℓ r m :=
  mem_inBlock_of_ne_zero hA ha hne

section Comp

omit [Fintype ι] [DecidableEq ι] [DecidableEq L] in
/-- Four sums with the two inner ones brought outside. -/
theorem sum_comm4 {α β γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ] (F : Finset β)
    (f : α → β → γ → δ → ℂ) :
    ∑ x, ∑ y ∈ F, ∑ z, ∑ w, f x y z w = ∑ z, ∑ w, ∑ x, ∑ y ∈ F, f x y z w := by
  calc _ = ∑ x, ∑ z, ∑ y ∈ F, ∑ w, f x y z w :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ z, ∑ w, ∑ y ∈ F, f x y z w :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ w, ∑ y ∈ F, f x y z w := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun z _ => Finset.sum_comm

variable {R₁ R₂ : Type*} [Fintype R₁] [Fintype R₂]

omit [DecidableEq L] in
theorem keepsNone_comp {K₂ : KrausMap R₂ ι ι} {K₁ : KrausMap R₁ ι ι} (h₂ : KeepsNone ℓ K₂)
    (h₁ : KeepsNone ℓ K₁) : KeepsNone ℓ (K₂.comp K₁) := fun i a b hb hne => by
  change (K₂.op i.2 * K₁.op i.1) a b ≠ 0 at hne
  rw [Matrix.mul_apply] at hne
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h₂ i.2 a m (h₁ i.1 m b hb (right_ne_zero_of_mul hm)) (left_ne_zero_of_mul hm)

omit [DecidableEq L] in
theorem keepsBlocks_comp {K₂ : KrausMap R₂ ι ι} {K₁ : KrausMap R₁ ι ι}
    (h₂ : ∀ i, KeepsBlocks ℓ (K₂.op i)) (h₁ : ∀ i, KeepsBlocks ℓ (K₁.op i)) :
    ∀ i, KeepsBlocks ℓ ((K₂.comp K₁).op i) := fun i => (h₂ i.2).mul (h₁ i.1)

/-- **The overlaps of a composition**: those of the second map, weighted by the first map's
entries. -/
theorem rowGram_comp (r : L) (K₂ : KrausMap R₂ ι ι) (K₁ : KrausMap R₁ ι ι) (c d : ι) :
    rowGram ℓ r (K₂.comp K₁) c d =
      ∑ i₁, ∑ m, ∑ n, K₁.op i₁ m c * star (K₁.op i₁ n d) * rowGram ℓ r K₂ m n := by
  unfold rowGram
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i₁ _ => ?_
  change ∑ i₂, ∑ a ∈ _, (K₂.op i₂ * K₁.op i₁) a c * star ((K₂.op i₂ * K₁.op i₁) a d) = _
  simp only [Matrix.mul_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm4, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ =>
    Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **The overlaps after a block isometry** are those before it. -/
theorem rowGram_comp_of_blockIso {N : KrausMap R₂ ι ι} (hN : BlockIso ℓ N) (r : L)
    (K : KrausMap R₁ ι ι) (c d : ι) : rowGram ℓ r (N.comp K) c d = rowGram ℓ r K c d := by
  rw [rowGram_comp]
  simp only [hN.gram, mul_ite, mul_one, mul_zero, ite_and]
  unfold rowGram
  refine Finset.sum_congr rfl fun i₁ _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem BlockIso.comp {K₂ : KrausMap R₂ ι ι} {K₁ : KrausMap R₁ ι ι} (h₂ : BlockIso ℓ K₂)
    (h₁ : BlockIso ℓ K₁) : BlockIso ℓ (K₂.comp K₁) where
  keeps := keepsBlocks_comp h₂.keeps h₁.keeps
  keepsNone := keepsNone_comp h₂.keepsNone h₁.keepsNone
  gram r m n := by rw [rowGram_comp_of_blockIso h₂, h₁.gram]

omit [DecidableEq L] in
theorem SetIso.keepsSet {S : Set ι} {K : KrausMap R₁ ι ι} (h : SetIso S K) (i : R₁) :
    KeepsSet S S (K.op i) := fun a b hb hne => (h i a b hne).2 hb

omit [DecidableEq L] in
theorem SetIso.comp {S : Set ι} {K₂ : KrausMap R₂ ι ι} {K₁ : KrausMap R₁ ι ι}
    (h₂ : SetIso S K₂) (h₁ : SetIso S K₁) : SetIso S (K₂.comp K₁) := fun i a b hne => by
  change (K₂.op i.2 * K₁.op i.1) a b ≠ 0 at hne
  rw [Matrix.mul_apply] at hne
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact (h₂ i.2 a m (left_ne_zero_of_mul hm)).trans (h₁ i.1 m b (right_ne_zero_of_mul hm))

omit [DecidableEq L] in
theorem keepsSet_comp {S₀ S₁ S₂ : Set ι} {A B : Matrix ι ι ℂ} (hA : KeepsSet S₁ S₂ A)
    (hB : KeepsSet S₀ S₁ B) : KeepsSet S₀ S₂ (A * B) := fun a b hb hne => by
  rw [Matrix.mul_apply] at hne
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact hA a m (hB m b hb (right_ne_zero_of_mul hm)) (left_ne_zero_of_mul hm)

omit [DecidableEq L] in
theorem keepsBlocksOn_comp {S₀ S₁ : Set ι} {A B : Matrix ι ι ℂ} (hA : KeepsBlocksOn S₁ ℓ A)
    (hB : KeepsBlocksOn S₀ ℓ B) (hBs : KeepsSet S₀ S₁ B) : KeepsBlocksOn S₀ ℓ (A * B) :=
  fun r' a b hb hl hne => by
  rw [Matrix.mul_apply] at hne
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact hA r' a m (hBs m b hb (right_ne_zero_of_mul hm)) (hB r' m b hb hl (right_ne_zero_of_mul hm))
    (left_ne_zero_of_mul hm)

omit [DecidableEq L] in
theorem KeepsBlocks.on {A : Matrix ι ι ℂ} (h : KeepsBlocks ℓ A) (S : Set ι) :
    KeepsBlocksOn S ℓ A := fun r' a b _ hb hne => h r' a b hb hne

theorem PairNone.refl {S S' : Set ι} {K : KrausMap R₁ ι ι} (h : ∀ i, KeepsBlocks ℓ (K.op i))
    (hS : SetIso S K) (hS' : SetIso S' K) : PairNone ℓ S S S' S' K K :=
  ⟨hS.keepsSet, hS'.keepsSet, fun i => (h i).on S, fun i => (h i).on S', fun _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ => rfl⟩

/-- **A pair after a block isometry keeping its starting sets.** -/
theorem PairNone.comp_left {S₁ S₂ S₁' S₂' : Set ι} {K K' : KrausMap R₂ ι ι}
    (h : PairNone ℓ S₁ S₂ S₁' S₂' K K') {M : KrausMap R₁ ι ι} (hM : BlockIso ℓ M)
    (hMS : SetIso S₁ M) (hMS' : SetIso S₁' M) :
    PairNone ℓ S₁ S₂ S₁' S₂' (K.comp M) (K'.comp M) where
  keepsSet i := keepsSet_comp (h.keepsSet i.2) (hMS.keepsSet i.1)
  keepsSet' i := keepsSet_comp (h.keepsSet' i.2) (hMS'.keepsSet i.1)
  keeps i := keepsBlocksOn_comp (h.keeps i.2) ((hM.keeps i.1).on S₁) (hMS.keepsSet i.1)
  keeps' i := keepsBlocksOn_comp (h.keeps' i.2) ((hM.keeps i.1).on S₁') (hMS'.keepsSet i.1)
  row_none_eq i a b ha hb hal hbl := by
    change (K'.op i.2 * M.op i.1) a b = (K.op i.2 * M.op i.1) a b
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : M.op i.1 m b = 0
    · simp [hm]
    rw [h.row_none_eq _ a m ha ((hMS i.1 m b hm).2 hb) hal (hM.keepsNone _ _ _ hbl hm)]
  gram_eq r c d hc hd hcl hdl := by
    rw [rowGram_comp, rowGram_comp]
    refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun m _ =>
      Finset.sum_congr rfl fun n _ => ?_
    by_cases hm : M.op i₁ m c = 0
    · simp [hm]
    by_cases hn : M.op i₁ n d = 0
    · simp [hn]
    rw [h.gram_eq r m n ((hMS i₁ m c hm).2 hc) ((hMS i₁ n d hn).2 hd)
      (hM.keepsNone _ _ _ hcl hm) (hM.keepsNone _ _ _ hdl hn)]

/-- **A block isometry keeping the end sets, after a pair.** -/
theorem PairNone.comp_right {S₁ S₂ S₁' S₂' : Set ι} {K K' : KrausMap R₁ ι ι}
    (h : PairNone ℓ S₁ S₂ S₁' S₂' K K') {N : KrausMap R₂ ι ι} (hN : BlockIso ℓ N)
    (hNS : SetIso S₂ N) (hNS' : SetIso S₂' N) :
    PairNone ℓ S₁ S₂ S₁' S₂' (N.comp K) (N.comp K') where
  keepsSet i := keepsSet_comp (hNS.keepsSet i.2) (h.keepsSet i.1)
  keepsSet' i := keepsSet_comp (hNS'.keepsSet i.2) (h.keepsSet' i.1)
  keeps i := keepsBlocksOn_comp ((hN.keeps i.2).on S₂) (h.keeps i.1) (h.keepsSet i.1)
  keeps' i := keepsBlocksOn_comp ((hN.keeps i.2).on S₂') (h.keeps' i.1) (h.keepsSet' i.1)
  row_none_eq i a b ha hb hal hbl := by
    change (N.op i.2 * K'.op i.1) a b = (N.op i.2 * K.op i.1) a b
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : N.op i.2 a m = 0
    · simp [hm]
    rw [h.row_none_eq _ m _ ((hNS i.2 a m hm).1 ha) hb ((hN.keeps i.2).col_none hal hm) hbl]
  gram_eq r c d hc hd hcl hdl := by
    rw [rowGram_comp_of_blockIso hN, rowGram_comp_of_blockIso hN]
    exact h.gram_eq r c d hc hd hcl hdl

omit [DecidableEq L] in
/-- **Pairs agreeing on a block along permutations, composed**: the first maps move the column
sets into the middle ones, the second keep the blocks there, on the block the column permutation
maps `S₀` into `S₀'` and the middle one maps only `S₁` into `S₁'`, and the row and middle
permutations keep the label. -/
theorem PairOn.comp {r : L} {S₀ S₁ S₂ S₀' S₁' : Set ι} {ρ₁ : Equiv.Perm R₁}
    {ρ₂ : Equiv.Perm R₂} {πr πm πc : Equiv.Perm ι} {K₂ K₂' : KrausMap R₂ ι ι}
    {K₁ K₁' : KrausMap R₁ ι ι} (h₂ : PairOn ℓ r ρ₂ πr πm S₂ S₁ K₂ K₂')
    (h₁ : PairOn ℓ r ρ₁ πm πc S₁ S₀ K₁ K₁')
    (s₁ : ∀ i, KeepsSet S₀ S₁ (K₁.op i)) (s₁' : ∀ i, KeepsSet S₀' S₁' (K₁'.op i))
    (k₂ : ∀ i, KeepsBlocksOn S₁ ℓ (K₂.op i)) (k₂' : ∀ i, KeepsBlocksOn S₁' ℓ (K₂'.op i))
    (hc : ∀ x, InBlock ℓ r x → x ∈ S₀ → πc x ∈ S₀')
    (hm : ∀ x, InBlock ℓ r x → πm x ∈ S₁' → x ∈ S₁) (hlr : ∀ x, ℓ (πr x) = ℓ x)
    (hlm : ∀ x, ℓ (πm x) = ℓ x) :
    PairOn ℓ r (ρ₁.prodCongr ρ₂) πr πc S₂ S₀ (K₂.comp K₁) (K₂'.comp K₁') :=
  fun i a b ha has hb hbs => by
  change (K₂'.op (ρ₂ i.2) * K₁'.op (ρ₁ i.1)) (πr a) (πc b) = (K₂.op i.2 * K₁.op i.1) a b
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp πm]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hcb := hc b hb hbs
  by_cases hmb : InBlock ℓ r m
  · by_cases hz : K₁'.op (ρ₁ i.1) (πm m) (πc b) = 0 ∧ K₁.op i.1 m b = 0
    · rw [hz.1, hz.2, mul_zero, mul_zero]
    have hms : m ∈ S₁ := by
      by_cases h1 : K₁'.op (ρ₁ i.1) (πm m) (πc b) = 0
      · exact s₁ i.1 m b hbs (fun h0 => hz ⟨h1, h0⟩)
      · exact hm m hmb (s₁' _ _ _ hcb h1)
    rw [h₂ _ a m ha has hmb hms, h₁ _ m b hmb hms hb hbs]
  · have e : K₂.op i.2 a m * K₁.op i.1 m b = 0 := by
      by_cases h1 : K₁.op i.1 m b = 0
      · rw [h1, mul_zero]
      · have hms := s₁ i.1 m b hbs h1
        have : K₂.op i.2 a m = 0 := by
          by_contra hne
          exact hmb (mem_inBlock_of_ne_zero_on (k₂ i.2) ha hms hne)
        rw [this, zero_mul]
    rw [e]
    by_cases h1 : K₁'.op (ρ₁ i.1) (πm m) (πc b) = 0
    · rw [h1, mul_zero]
    · have hms' := s₁' _ _ _ hcb h1
      have e' : K₂'.op (ρ₂ i.2) (πr a) (πm m) = 0 := by
        by_contra hne
        have hin := mem_inBlock_of_ne_zero_on (k₂' (ρ₂ i.2))
          (show InBlock ℓ r (πr a) by unfold InBlock; rw [hlr]; exact ha) hms' hne
        apply hmb
        unfold InBlock at hin ⊢
        rwa [hlm] at hin
      rw [e', zero_mul]

end Comp

/-! ### Examples of block isometries -/

omit [DecidableEq L] in
theorem ofPerm_op_eq (π : Equiv.Perm ι) (u : Unit) (a b : ι) :
    (KrausMap.ofPerm π).op u a b = if a = π b then 1 else 0 := by
  simp only [KrausMap.ofPerm, KrausMap.permConj, KrausMap.identity, Matrix.submatrix_apply,
    Equiv.refl_apply, Matrix.one_apply]
  exact if_congr (Equiv.symm_apply_eq π) rfl rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq L] in
theorem star_ite_one_zero (p : Prop) [Decidable p] :
    star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

/-- **A basis permutation keeping the label is a block isometry.** -/
theorem BlockIso.ofPerm {π : Equiv.Perm ι} (hπ : ∀ x, ℓ (π x) = ℓ x) :
    BlockIso ℓ (KrausMap.ofPerm π) where
  keeps u r' a b hb hne := by
    rw [ofPerm_op_eq] at hne
    split_ifs at hne with h
    · rw [h, hπ, hb]
    · exact absurd rfl hne
  keepsNone u a b hb hne := by
    rw [ofPerm_op_eq] at hne
    split_ifs at hne with h
    · rw [h, hπ, hb]
    · exact absurd rfl hne
  gram r m n := by
    unfold rowGram
    simp only [ofPerm_op_eq, Fintype.univ_unit, Finset.sum_singleton, mul_ite, ite_mul, mul_one,
      one_mul, zero_mul, mul_zero, star_ite_one_zero]
    rw [Finset.sum_filter]
    by_cases h : m = n <;> by_cases h' : ℓ m = some r
    · subst h
      rw [Finset.sum_eq_single (π m) (fun a _ ha => by simp [ha]) (by simp)]
      simp [h', hπ]
    · subst h
      rw [Finset.sum_eq_single (π m) (fun a _ ha => by simp [ha]) (by simp)]
      simp [h', hπ]
    · refine (Finset.sum_eq_zero fun a _ => ?_).trans (by simp [h])
      split_ifs with h1 h2 h3 <;>
        first | rfl | exact absurd (π.injective (h2.symm.trans h3)) (fun e => h e.symm)
    · refine (Finset.sum_eq_zero fun a _ => ?_).trans (by simp [h])
      split_ifs with h1 h2 h3 <;>
        first | rfl | exact absurd (π.injective (h2.symm.trans h3)) (fun e => h e.symm)

/-- **The identity is a block isometry.** -/
theorem BlockIso.identity : BlockIso ℓ (KrausMap.identity ι) := by
  have h := BlockIso.ofPerm (ℓ := ℓ) (π := Equiv.refl ι) fun _ => rfl
  refine ⟨fun u => ?_, fun u a b hb hne => h.keepsNone u a b hb ?_, fun r m n => ?_⟩
  · intro r' a b hb hne
    exact h.keeps u r' a b hb (by rwa [ofPerm_op_eq, Equiv.refl_apply, ← Matrix.one_apply])
  · rwa [ofPerm_op_eq, Equiv.refl_apply, ← Matrix.one_apply]
  · rw [← h.gram r m n]
    unfold rowGram
    simp only [ofPerm_op_eq, Equiv.refl_apply, ← Matrix.one_apply]
    rfl

/-- **A projective measurement of a function is a block isometry.** -/
theorem BlockIso.measureFn {M : Type*} [Fintype M] [DecidableEq M] (f : ι → M) :
    BlockIso ℓ (KrausMap.measureFn f) where
  keeps o r' a b hb hne := by
    have h : a = b := by
      by_contra h
      exact hne (Matrix.diagonal_apply_ne _ h)
    rw [h, hb]
  keepsNone o a b hb hne := by
    have h : a = b := by
      by_contra h
      exact hne (Matrix.diagonal_apply_ne _ h)
    rw [h, hb]
  gram r m n := by
    unfold rowGram
    change ∑ o, ∑ a ∈ _, Matrix.diagonal _ a m * star (Matrix.diagonal _ a n) = _
    simp only [Matrix.diagonal_apply, mul_ite, ite_mul, mul_one, one_mul, zero_mul, mul_zero,
      star_ite_one_zero, apply_ite star, star_zero]
    rw [Finset.sum_comm, Finset.sum_filter]
    by_cases h : m = n
    · subst h
      rw [Finset.sum_eq_single m (fun a _ ha => by simp [ha]) (by simp)]
      by_cases h' : ℓ m = some r
      · simp only [h', if_true, true_and]
        rw [Finset.sum_eq_single (f m) (fun o _ ho => by simp [Ne.symm ho]) (by simp)]
        simp
      · simp [h']
    · refine (Finset.sum_eq_zero fun a _ => ?_).trans (by simp [h])
      by_cases ha : a = m
      · subst ha
        simp [h]
      · simp [ha]

omit [DecidableEq L] in
theorem SetIso.ofPerm {S : Set ι} {π : Equiv.Perm ι} (hπ : ∀ x, π x ∈ S ↔ x ∈ S) :
    SetIso S (KrausMap.ofPerm π) := fun u a b hne => by
  rw [ofPerm_op_eq] at hne
  split_ifs at hne with h
  · rw [h, hπ]
  · exact absurd rfl hne

omit [DecidableEq L] in
theorem SetIso.identity (S : Set ι) : SetIso S (KrausMap.identity ι) := fun u a b hne => by
  by_cases h : a = b
  · rw [h]
  · exact absurd (Matrix.one_apply_ne h) hne

omit [DecidableEq L] in
theorem SetIso.measureFn {M : Type*} [Fintype M] [DecidableEq M] (S : Set ι) (f : ι → M) :
    SetIso S (KrausMap.measureFn f) := fun o a b hne => by
  have h : a = b := by
    by_contra h
    exact hne (Matrix.diagonal_apply_ne _ h)
  rw [h]

omit [DecidableEq L] in
/-- **A basis permutation commuting with `π` agrees with itself along `π`.** -/
theorem pairOn_ofPerm {g π : Equiv.Perm ι} (hg : ∀ x, g (π x) = π (g x)) (r : L) (Sr Sc : Set ι) :
    PairOn ℓ r (Equiv.refl Unit) π π Sr Sc (KrausMap.ofPerm g) (KrausMap.ofPerm g) :=
  fun u a b _ _ _ _ => by
  simp only [Equiv.refl_apply, ofPerm_op_eq, hg, π.injective.eq_iff]

omit [DecidableEq L] in
/-- **The identity agrees with itself along every permutation.** -/
theorem pairOn_identity (π : Equiv.Perm ι) (r : L) (Sr Sc : Set ι) :
    PairOn ℓ r (Equiv.refl Unit) π π Sr Sc (KrausMap.identity ι) (KrausMap.identity ι) :=
  fun u a b _ _ _ _ => by
  change (1 : Matrix ι ι ℂ) (π a) (π b) = (1 : Matrix ι ι ℂ) a b
  simp only [Matrix.one_apply, π.injective.eq_iff]

omit [DecidableEq L] in
/-- **A projective measurement of a function carried by `φ` along `π`** agrees with itself along
`π`, its outcomes relabelled by `φ`. -/
theorem pairOn_measureFn {M : Type*} [Fintype M] [DecidableEq M] {f : ι → M} {π : Equiv.Perm ι}
    {φ : Equiv.Perm M} (hf : ∀ x, f (π x) = φ (f x)) (r : L) (Sr Sc : Set ι) :
    PairOn ℓ r φ π π Sr Sc (KrausMap.measureFn f) (KrausMap.measureFn f) :=
  fun o a b _ _ _ _ => by
  change Matrix.diagonal _ (π a) (π b) = Matrix.diagonal _ a b
  simp only [Matrix.diagonal_apply, π.injective.eq_iff, hf, φ.injective.eq_iff]

omit [DecidableEq L] in
/-- **A projective measurement of a function carried by `φ` along `π` on the columns of the
block in `Sc`** agrees with itself along `π` there, its outcomes relabelled by `φ`. -/
theorem pairOn_measureFn_on {M : Type*} [Fintype M] [DecidableEq M] {f : ι → M}
    {π : Equiv.Perm ι} {φ : Equiv.Perm M} (r : L) (Sr Sc : Set ι)
    (hf : ∀ x, InBlock ℓ r x → x ∈ Sc → f (π x) = φ (f x)) :
    PairOn ℓ r φ π π Sr Sc (KrausMap.measureFn f) (KrausMap.measureFn f) :=
  fun o a b _ _ hb hbs => by
  change Matrix.diagonal _ (π a) (π b) = Matrix.diagonal _ a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq, hf a hb hbs, φ.injective.eq_iff]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hab (π.injective h)), Matrix.diagonal_apply_ne _ hab]

/-! ### Kraus maps on one factor of a split -/

section Tensor

variable {κ E : Type*} [Fintype κ] [DecidableEq κ] [Fintype E] [DecidableEq E] (e : ι ≃ κ × E)
  {ℓκ : κ → Option L} {R : Type*} [Fintype R]

/-- **A Kraus map on the first factor of a split** `e`: its entries are those of `K` on the
first factor times the identity on the second. -/
def OnFst (K : KrausMap R κ κ) (Kt : KrausMap R ι ι) : Prop :=
  ∀ i y x, Kt.op i y x = K.op i (e y).1 (e x).1 * (1 : Matrix E E ℂ) (e y).2 (e x).2

variable {e}

omit [DecidableEq L] in
theorem OnFst.keepsBlocks {K : KrausMap R κ κ} {Kt : KrausMap R ι ι} (h : OnFst e K Kt)
    (hK : ∀ i, KeepsBlocks ℓκ (K.op i)) :
    ∀ i, KeepsBlocks (fun y => ℓκ (e y).1) (Kt.op i) := fun i r' a b hb hne => by
  rw [h] at hne
  exact hK i r' _ _ hb (left_ne_zero_of_mul hne)

omit [DecidableEq L] in
theorem OnFst.keepsNone {K : KrausMap R κ κ} {Kt : KrausMap R ι ι} (h : OnFst e K Kt)
    (hK : KeepsNone ℓκ K) : KeepsNone (fun y => ℓκ (e y).1) Kt := fun i a b hb hne => by
  rw [h] at hne
  exact hK i _ _ hb (left_ne_zero_of_mul hne)

omit [DecidableEq L] in
theorem OnFst.keepsSet {K : KrausMap R κ κ} {Kt : KrausMap R ι ι} (h : OnFst e K Kt)
    {Sc Sr : Set κ} (hK : ∀ i, KeepsSet Sc Sr (K.op i)) (i : R) :
    KeepsSet {y | (e y).1 ∈ Sc} {y | (e y).1 ∈ Sr} (Kt.op i) := fun a b hb hne => by
  rw [h] at hne
  exact hK i _ _ hb (left_ne_zero_of_mul hne)

omit [DecidableEq L] in
theorem OnFst.keepsBlocksOn {K : KrausMap R κ κ} {Kt : KrausMap R ι ι} (h : OnFst e K Kt)
    {Sc : Set κ} (hK : ∀ i, KeepsBlocksOn Sc ℓκ (K.op i)) (i : R) :
    KeepsBlocksOn {y | (e y).1 ∈ Sc} (fun y => ℓκ (e y).1) (Kt.op i) := fun r' a b hb hl hne => by
  rw [h] at hne
  exact hK i r' _ _ hb hl (left_ne_zero_of_mul hne)

omit [DecidableEq L] in
theorem OnFst.setIso {K : KrausMap R κ κ} {Kt : KrausMap R ι ι} (h : OnFst e K Kt)
    {S : Set κ} (hK : SetIso S K) : SetIso {y | (e y).1 ∈ S} Kt := fun i a b hne => by
  rw [h] at hne
  exact hK i _ _ (left_ne_zero_of_mul hne)

omit [DecidableEq L] in
/-- **Kraus maps on the first factor agreeing on a block along permutations** of the first
factor that keep the second. -/
theorem OnFst.pairOn {r : L} {ρ : Equiv.Perm R} {πr πc : Equiv.Perm κ} {πr' πc' : Equiv.Perm ι}
    (hr : ∀ y, e (πr' y) = (πr (e y).1, (e y).2)) (hc : ∀ y, e (πc' y) = (πc (e y).1, (e y).2))
    {Sr Sc : Set κ} {K K' : KrausMap R κ κ} {Kt Kt' : KrausMap R ι ι}
    (h : OnFst e K Kt) (h' : OnFst e K' Kt') (hp : PairOn ℓκ r ρ πr πc Sr Sc K K') :
    PairOn (fun y => ℓκ (e y).1) r ρ πr' πc' {y | (e y).1 ∈ Sr} {y | (e y).1 ∈ Sc} Kt Kt' :=
  fun i a b ha has hb hbs => by
  rw [h, h', hr, hc, hp i _ _ ha has hb hbs]

/-- **The overlaps of a Kraus map on the first factor**: those of `K` on the first factors when
the second factors agree, else `0`. -/
theorem OnFst.rowGram {K : KrausMap R κ κ} {Kt : KrausMap R ι ι} (h : OnFst e K Kt) (r : L)
    (c d : ι) : rowGram (fun y => ℓκ (e y).1) r Kt c d =
      (1 : Matrix E E ℂ) (e c).2 (e d).2 * rowGram ℓκ r K (e c).1 (e d).1 := by
  unfold QROM.rowGram
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : ∀ v w : E, star ((1 : Matrix E E ℂ) v w) = (1 : Matrix E E ℂ) v w := fun v w => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_equiv e _
    (fun z => if ℓκ z.1 = some r then (K.op i z.1 (e c).1 * (1 : Matrix E E ℂ) z.2 (e c).2) *
      star (K.op i z.1 (e d).1 * (1 : Matrix E E ℂ) z.2 (e d).2) else 0) (fun a => by
        rw [h, h])]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [star_mul', hs]
  split_ifs
  · simp only [Matrix.one_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
    by_cases hcd : (e c).2 = (e d).2
    · rw [if_pos hcd, Finset.sum_eq_single (e d).2]
      · rw [if_pos rfl, if_pos hcd.symm]
      · intro x _ hx
        rw [if_neg hx]
      · simp
    · rw [if_neg hcd]
      exact Finset.sum_eq_zero fun v _ => by
        split_ifs with e1 e2
        · exact absurd (e2.symm.trans e1) hcd
        · rfl
        · rfl
  · simp

theorem OnFst.blockIso {K : KrausMap R κ κ} {Kt : KrausMap R ι ι} (h : OnFst e K Kt)
    (hK : BlockIso ℓκ K) : BlockIso (fun y => ℓκ (e y).1) Kt where
  keeps := h.keepsBlocks hK.keeps
  keepsNone := h.keepsNone hK.keepsNone
  gram r m n := by
    rw [h.rowGram, hK.gram, Matrix.one_apply]
    by_cases h1 : (e m).2 = (e n).2 <;> by_cases h2 : (e m).1 = (e n).1
    · have : m = n := e.injective (Prod.ext h2 h1)
      subst this
      simp
    · have : m ≠ n := fun hmn => h2 (by rw [hmn])
      simp [h1, h2, this]
    · have : m ≠ n := fun hmn => h1 (by rw [hmn])
      simp [h1, this]
    · have : m ≠ n := fun hmn => h1 (by rw [hmn])
      simp [h1, this]

theorem OnFst.pairNone {Sc Sr Sc' Sr' : Set κ} {K K' : KrausMap R κ κ} {Kt Kt' : KrausMap R ι ι}
    (h : OnFst e K Kt) (h' : OnFst e K' Kt') (hp : PairNone ℓκ Sc Sr Sc' Sr' K K') :
    PairNone (fun y => ℓκ (e y).1) {y | (e y).1 ∈ Sc} {y | (e y).1 ∈ Sr} {y | (e y).1 ∈ Sc'}
      {y | (e y).1 ∈ Sr'} Kt Kt' where
  keepsSet := h.keepsSet hp.keepsSet
  keepsSet' := h'.keepsSet hp.keepsSet'
  keeps := h.keepsBlocksOn hp.keeps
  keeps' := h'.keepsBlocksOn hp.keeps'
  row_none_eq i a b ha hb hal hbl := by
    rw [h, h', hp.row_none_eq i _ _ ha hb hal hbl]
  gram_eq r c d hc hd hcl hdl := by
    rw [h.rowGram, h'.rowGram, hp.gram_eq r _ _ hc hd hcl hdl]

end Tensor

end GordieHowe.QROM
