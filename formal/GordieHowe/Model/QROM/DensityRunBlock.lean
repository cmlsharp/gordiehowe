-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.DensityRunRelabel

@[expose] public section

/-!
# Density-matrix runs on one block of a label

A label `ℓ : V → Option L` of the work register whose value, once set, every Kraus map keeps
(`KeepsBlocks`: on a column with label `some r'`, the nonzero rows have label `some r'`). On the
basis states with label `none` or `some r` (`InBlock ℓ r`), two runs whose Kraus maps agree along a
permutation `τ` of the work register keeping the label, on the rows and columns with label `none` or
`some r`, are related by `τ` there (`densityRun_relabel_block`; the permutation may change with the
step). A run's entries on these basis
states never read the columns of the other blocks. Trace-preserving runs that agree on the
rows with label `none`, with the same overlaps from the columns with label `none` into every
block, give every block the same mass (`densityRun_block_mass`): once set, a label's block evolves
by a trace-preserving map.

- `InBlock`, `KeepsBlocks`, `OpRelOn`, `OpRelOn₂`, `OpRelIdx`, `OpRelOn₂.idx` (two Kraus maps
  agreeing along a permutation on the rows and columns of a set, or along permutations of the rows
  and of the columns on the rows of one set and the columns of another, the operators kept or
  permuted), `prevSeq`, `KeepsSet`, `KeepsBlocksOn`,
  `mem_inBlock_of_ne_zero_on`, `densityRun_supported`.
- `mem_inBlock_of_ne_zero`: a nonzero entry in a row with label `none` or `some r` has its column
  there.
- `mul_mul_conjTranspose_relabel_block`, `KrausMapBlock.apply_relabel_block`: one conjugation and
  one Kraus map, on the block.
- `densityRun_relabel_block`: the runs.
- `labelInd`, `sum_four_comm`, `sum_filter_conj_eq`, `sum_filter_kron_one`, `sum_conj_block_mass`:
  the mass of a block after one family of conjugations, and two families agreeing on the rows with
  label `none` with the same overlaps into the blocks.
- `conjTranspose_mul_of_norm_kernelOp`, `simQueryKernel_unitary`: the simulated query has
  orthonormal columns.
- `densityRun_block_mass`: trace-preserving runs agreeing on the columns with label `none` agree on
  the `none` block and give every block the same mass.
-/

open Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.QROM

open GordieHowe.Quantum

/-! ### Blocks of a label -/

section Block

variable {ι L : Type*} (ℓ : ι → Option L)

/-- **The basis states with label `none` or `some r`.** -/
def InBlock (r : L) (a : ι) : Prop :=
  ℓ a = none ∨ ℓ a = some r

/-- **A matrix keeps the blocks of the label**: on a column with label `some r'`, its nonzero rows
have label `some r'`. -/
def KeepsBlocks (A : Matrix ι ι ℂ) : Prop :=
  ∀ r' a b, ℓ b = some r' → A a b ≠ 0 → ℓ a = some r'

/-- **The value before step `n`**: `x₀` before the first step, the value after step `n - 1`
otherwise. -/
def prevSeq {α : Sort*} (x : ℕ → α) (x₀ : α) (n : ℕ) : α :=
  if n = 0 then x₀ else x (n - 1)

/-- **Two Kraus maps agree on the rows in `Sr` and the columns in `Sc`, read along `π` on the rows
and along `π₀` on the columns.** -/
def OpRelOn₂ {R : Type*} [Fintype R] [Fintype ι] [DecidableEq ι] (π π₀ : Equiv.Perm ι)
    (Sr Sc : Set ι) (K K' : KrausMap R ι ι) : Prop :=
  ∀ k a b, a ∈ Sr → b ∈ Sc → K'.op k (π a) (π₀ b) = K.op k a b

/-- **Two Kraus maps agree on the rows in `Sr` and the columns in `Sc`, read along `π` on the rows,
along `π₀` on the columns and along `ρ` on the operators.** -/
def OpRelIdx {R : Type*} [Fintype R] [Fintype ι] [DecidableEq ι] (ρ : Equiv.Perm R)
    (π π₀ : Equiv.Perm ι) (Sr Sc : Set ι) (K K' : KrausMap R ι ι) : Prop :=
  ∀ k a b, a ∈ Sr → b ∈ Sc → K'.op (ρ k) (π a) (π₀ b) = K.op k a b

/-- `OpRelOn₂` is `OpRelIdx` with the operators kept. -/
theorem OpRelOn₂.idx {R : Type*} [Fintype R] [Fintype ι] [DecidableEq ι] {π π₀ : Equiv.Perm ι}
    {Sr Sc : Set ι} {K K' : KrausMap R ι ι} (h : OpRelOn₂ π π₀ Sr Sc K K') :
    OpRelIdx (Equiv.refl R) π π₀ Sr Sc K K' :=
  h

/-- **Two Kraus maps agree along `π` on the rows and the columns in `S`.** -/
def OpRelOn {R : Type*} [Fintype R] [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (S : Set ι)
    (K K' : KrausMap R ι ι) : Prop :=
  ∀ k a b, a ∈ S → b ∈ S → K'.op k (π a) (π b) = K.op k a b

variable {ℓ}

/-- **A nonzero entry in a row of the block has its column in the block.** -/
theorem mem_inBlock_of_ne_zero {A : Matrix ι ι ℂ} (hA : KeepsBlocks ℓ A) {r : L} {a c : ι}
    (ha : InBlock ℓ r a) (h : A a c ≠ 0) : InBlock ℓ r c := by
  rcases hc : ℓ c with _ | r'
  · exact Or.inl hc
  · have := hA r' a c hc h
    rcases ha with ha | ha
    · rw [ha] at this
      exact absurd this (by simp)
    · rw [ha] at this
      exact Or.inr (by rw [hc, Option.some.inj this])

/-- **A matrix maps the set `Gc` into the set `Gr`**: on a column in `Gc`, its nonzero rows are in
`Gr`. -/
def KeepsSet (Gc Gr : Set ι) (A : Matrix ι ι ℂ) : Prop :=
  ∀ a b, b ∈ Gc → A a b ≠ 0 → a ∈ Gr

/-- **A matrix keeps the blocks of the label on the columns in `G`.** -/
def KeepsBlocksOn (G : Set ι) (ℓ : ι → Option L) (A : Matrix ι ι ℂ) : Prop :=
  ∀ r' a b, b ∈ G → ℓ b = some r' → A a b ≠ 0 → ℓ a = some r'

/-- **A nonzero entry in a row of the block from a column in `G` has its column in the block.** -/
theorem mem_inBlock_of_ne_zero_on {G : Set ι} {A : Matrix ι ι ℂ} (hA : KeepsBlocksOn G ℓ A)
    {r : L} {a c : ι} (ha : InBlock ℓ r a) (hc : c ∈ G) (h : A a c ≠ 0) : InBlock ℓ r c := by
  rcases hc' : ℓ c with _ | r'
  · exact Or.inl hc'
  · have := hA r' a c hc hc' h
    rcases ha with ha | ha
    · rw [ha] at this
      exact absurd this (by simp)
    · rw [ha] at this
      exact Or.inr (by rw [hc', Option.some.inj this])

variable [Fintype ι]

/-- **One conjugation on the block of the states in `Gc` and `Gr`**: for matrices `A`, `A'` that
keep the blocks on the columns in `Gc` and `Gc'` and agree on the rows in `Gr` and the columns in
`Gc` of the block, read along `π` on the rows and `π₀` on the columns (both keeping the label, `π₀`
mapping the block of `Gc` onto that of `Gc'`), and matrices `M`, `M'` supported on `Gc` and `Gc'`
that agree along `π₀` on the block, `A' M' A'ᴴ` and `A M Aᴴ` agree along `π` on the rows and
columns in `Gr` of the block. -/
theorem mul_mul_conjTranspose_relabel_block (Gc Gc' Gr : Set ι) (π π₀ : Equiv.Perm ι)
    (hπ : ∀ a, ℓ (π a) = ℓ a) (hπ₀ : ∀ a, ℓ (π₀ a) = ℓ a) (r : L)
    (hπ₀G : ∀ a, InBlock ℓ r a → (π₀ a ∈ Gc' ↔ a ∈ Gc)) {A A' : Matrix ι ι ℂ}
    (hop : ∀ a b, a ∈ Gr → b ∈ Gc → InBlock ℓ r a → InBlock ℓ r b → A' (π a) (π₀ b) = A a b)
    (hA : KeepsBlocksOn Gc ℓ A) (hA' : KeepsBlocksOn Gc' ℓ A') {M M' : Matrix ι ι ℂ}
    (hMs : ∀ a b, M a b ≠ 0 → a ∈ Gc ∧ b ∈ Gc) (hM's : ∀ a b, M' a b ≠ 0 → a ∈ Gc' ∧ b ∈ Gc')
    (hM : ∀ a b, a ∈ Gc → b ∈ Gc → InBlock ℓ r a → InBlock ℓ r b → M' (π₀ a) (π₀ b) = M a b)
    (a b : ι) (haG : a ∈ Gr) (hbG : b ∈ Gr) (ha : InBlock ℓ r a) (hb : InBlock ℓ r b) :
    (A' * M' * A'ᴴ) (π a) (π b) = (A * M * Aᴴ) a b := by
  have hπU : ∀ c, InBlock ℓ r (π c) ↔ InBlock ℓ r c := fun c => by
    simp only [InBlock, hπ]
  have hπ₀U : ∀ c, InBlock ℓ r (π₀ c) ↔ InBlock ℓ r c := fun c => by
    simp only [InBlock, hπ₀]
  -- a column outside the block meets a row of the block only off the support
  have hzA : ∀ {x c d}, InBlock ℓ r x → ¬ InBlock ℓ r c → A x c * M c d = 0 :=
    fun {x c d} hx hc => by
    by_cases hcG : c ∈ Gc
    · rw [show A x c = 0 from by_contra fun h => hc (mem_inBlock_of_ne_zero_on hA hx hcG h),
        zero_mul]
    · rw [show M c d = 0 from by_contra fun h => hcG (hMs c d h).1, mul_zero]
  have hzA' : ∀ {x c d}, InBlock ℓ r x → ¬ InBlock ℓ r c →
      A' (π x) (π₀ c) * M' (π₀ c) (π₀ d) = 0 := fun {x c d} hx hc => by
    by_cases hcG : π₀ c ∈ Gc'
    · rw [show A' (π x) (π₀ c) = 0 from by_contra fun h => hc ((hπ₀U c).1
        (mem_inBlock_of_ne_zero_on hA' ((hπU x).2 hx) hcG h)), zero_mul]
    · rw [show M' (π₀ c) (π₀ d) = 0 from by_contra fun h => hcG (hM's _ _ h).1, mul_zero]
  have hzB : ∀ {x c d}, InBlock ℓ r x → ¬ InBlock ℓ r d → M c d * star (A x d) = 0 :=
    fun {x c d} hx hd => by
    by_cases hdG : d ∈ Gc
    · rw [show A x d = 0 from by_contra fun h => hd (mem_inBlock_of_ne_zero_on hA hx hdG h),
        star_zero, mul_zero]
    · rw [show M c d = 0 from by_contra fun h => hdG (hMs c d h).2, zero_mul]
  have hzB' : ∀ {x c d}, InBlock ℓ r x → ¬ InBlock ℓ r d →
      M' (π₀ c) (π₀ d) * star (A' (π x) (π₀ d)) = 0 := fun {x c d} hx hd => by
    by_cases hdG : π₀ d ∈ Gc'
    · rw [show A' (π x) (π₀ d) = 0 from by_contra fun h => hd ((hπ₀U d).1
        (mem_inBlock_of_ne_zero_on hA' ((hπU x).2 hx) hdG h)), star_zero, mul_zero]
    · rw [show M' (π₀ c) (π₀ d) = 0 from by_contra fun h => hdG (hM's _ _ h).2, zero_mul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← Equiv.sum_comp π₀]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Equiv.sum_comp π₀, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : InBlock ℓ r c
  · by_cases hd : InBlock ℓ r d
    · by_cases hcd : c ∈ Gc ∧ d ∈ Gc
      · obtain ⟨hcG, hdG⟩ := hcd
        rw [hop a c haG hcG ha hc, hM c d hcG hdG hc hd, hop b d hbG hdG hb hd]
      · have h1 : M c d = 0 := by_contra fun h => hcd (hMs c d h)
        have h2 : M' (π₀ c) (π₀ d) = 0 := by_contra fun h => hcd
          ⟨(hπ₀G c hc).1 (hM's _ _ h).1, (hπ₀G d hd).1 (hM's _ _ h).2⟩
        rw [h1, h2]
        simp
    · rw [mul_assoc, mul_assoc, hzB' hb hd, hzB hb hd, mul_zero, mul_zero]
  · rw [hzA' ha hc, hzA ha hc, zero_mul, zero_mul]

/-- **One Kraus map on the block of the states in `Gc` and `Gr`**
(`mul_mul_conjTranspose_relabel_block` for each operator). -/
theorem KrausMap.apply_relabel_block {R : Type*} [Fintype R] [DecidableEq ι]
    (Gc Gc' Gr : Set ι) (π π₀ : Equiv.Perm ι) (hπ : ∀ a, ℓ (π a) = ℓ a)
    (hπ₀ : ∀ a, ℓ (π₀ a) = ℓ a) (r : L) (hπ₀G : ∀ a, InBlock ℓ r a → (π₀ a ∈ Gc' ↔ a ∈ Gc))
    {K K' : KrausMap R ι ι} (ρ : Equiv.Perm R)
    (hop : ∀ k a b, a ∈ Gr → b ∈ Gc → InBlock ℓ r a → InBlock ℓ r b →
      K'.op (ρ k) (π a) (π₀ b) = K.op k a b)
    (hK : ∀ k, KeepsBlocksOn Gc ℓ (K.op k)) (hK' : ∀ k, KeepsBlocksOn Gc' ℓ (K'.op k))
    {M M' : Matrix ι ι ℂ} (hMs : ∀ a b, M a b ≠ 0 → a ∈ Gc ∧ b ∈ Gc)
    (hM's : ∀ a b, M' a b ≠ 0 → a ∈ Gc' ∧ b ∈ Gc')
    (hM : ∀ a b, a ∈ Gc → b ∈ Gc → InBlock ℓ r a → InBlock ℓ r b → M' (π₀ a) (π₀ b) = M a b)
    (a b : ι) (haG : a ∈ Gr) (hbG : b ∈ Gr) (ha : InBlock ℓ r a) (hb : InBlock ℓ r b) :
    K' M' (π a) (π b) = K M a b := by
  simp only [KrausMap.apply, Matrix.sum_apply]
  rw [← Equiv.sum_comp ρ]
  exact Finset.sum_congr rfl fun k _ =>
    mul_mul_conjTranspose_relabel_block Gc Gc' Gr π π₀ hπ hπ₀ r hπ₀G (hop k) (hK k) (hK' (ρ k))
      hMs hM's hM a b haG hbG ha hb

end Block

/-! ### The simulated query is unitary -/

/-- **A norm-preserving operator given by its matrix has orthonormal columns.** -/
theorem conjTranspose_mul_of_norm_kernelOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℂ) (h : ∀ v, ‖kernelOp K v‖ = ‖v‖) : (Matrix.of K)ᴴ * Matrix.of K = 1 := by
  have hi := (LinearMap.norm_map_iff_inner_map_map (kernelOp K)).1 h
  ext a b
  have := hi (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
  simp only [PiLp.inner_apply, kernelOp_apply, PiLp.single_apply, RCLike.inner_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  have hr : ∑ x, (if x = b then (1 : ℂ) else 0) * (starRingEnd ℂ) (if x = a then 1 else 0) =
      if a = b then 1 else 0 := by
    rw [Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  rw [← hr, ← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

/-! ### The density-matrix runs on a block -/

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : BitStr I J ≃ B)

section Run

variable {V R L : Type} [Fintype V] [DecidableEq V] [Fintype R] {t : ℕ}

/-- **A run of Kraus maps moving through sets of work registers stays supported on them**: for
Kraus maps whose step `i` maps the basis states with work register in the set before it
(`prevSeq G G₀ i`) into those with work register in `G i`, sets constant after the last step
(`hGc`), and an initial state supported on `G₀`, the run after step `n` is supported on `G n`. -/
theorem densityRun_supported (G : ℕ → Set V) (G₀ : Set V) (hGc : ∀ n, t < n → G n = G (n - 1))
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (hK : ∀ (i : Fin (t + 1)) k, KeepsSet
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G G₀ i}
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ G i} ((K i).op k))
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (hρ : ∀ a b, ρ₀ a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀) :
    ∀ n (a b : SimRegister V I J m t), densityRun e K ρ₀ n a b ≠ 0 → a.1.1 ∈ G n ∧ b.1.1 ∈ G n := by
  have hstep : ∀ (k : ℕ) (M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ prevSeq G G₀ k ∧ b.1.1 ∈ prevSeq G G₀ k) →
      ∀ a b, KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) k M a b ≠ 0 →
        a.1.1 ∈ G k ∧ b.1.1 ∈ G k := fun k M hM => by
    unfold KrausMap.stepAt
    split_ifs with hk
    · intro a b h
      simp only [KrausMap.apply, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply] at h
      obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
      rw [Finset.sum_mul] at hc
      obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
      have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul hd)
      have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
      have h3 := right_ne_zero_of_mul hd
      obtain ⟨hdS, hcS⟩ := hM d c h2
      simp only [KrausMap.tensorId, Matrix.kroneckerMap_apply] at h1 h3
      refine ⟨hK ⟨k, hk⟩ r a.1 d.1 hdS (left_ne_zero_of_mul h1),
        hK ⟨k, hk⟩ r b.1 c.1 hcS (left_ne_zero_of_mul fun h0 => h3 (by rw [h0, star_zero]))⟩
    · have hk0 : k ≠ 0 := by omega
      have : prevSeq G G₀ k = G k := by
        simp only [prevSeq, hk0, ↓reduceIte]
        exact (hGc k (by omega)).symm
      rw [← this]
      exact hM
  have hquery : ∀ (S : Set V) (M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S) →
      ∀ a b, (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ :
        Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) a b ≠ 0 →
        a.1.1 ∈ S ∧ b.1.1 ∈ S := fun S M hM a b h => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply] at h
    obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hc)
    have h1 := simQueryKernel_work e (left_ne_zero_of_mul hd)
    have h2 := simQueryKernel_work e (fun h0 => right_ne_zero_of_mul hc (by rw [h0, star_zero]))
    obtain ⟨hdS, hcS⟩ := hM d c (right_ne_zero_of_mul hd)
    exact ⟨h1 ▸ hdS, h2 ▸ hcS⟩
  intro n
  induction n with
  | zero =>
    simp only [densityRun]
    refine hstep 0 _ fun a b h => ?_
    simp only [Matrix.kroneckerMap_apply] at h
    exact hρ a.1 b.1 (left_ne_zero_of_mul h)
  | succ n ih =>
    simp only [densityRun]
    refine hstep (n + 1) _ ?_
    have : prevSeq G G₀ (n + 1) = G n := by simp [prevSeq]
    rw [this]
    exact hquery _ _ ih

/-- **The density-matrix runs on a block, along permutations and sets that change with the step**
(`densityRun_relabel` without a kept set for the block): for a label `ℓ` of the work register,
sets `G n` and `G' n` of work registers (after step `n`; `G₀`, `G₀'` of the initial state) through
which the Kraus maps `K` and `K'` move (`hG`, `hG'`) and on which their initial states are
supported, permutations `τ n` (after step `n`) and `τ₀` keeping `ℓ` and mapping the block of
`G n` onto that of `G' n`,
sets and permutations constant after the last step (`hGc`, `hGc'`, `hτc`), Kraus maps that keep
the blocks of `ℓ` on the columns in their set before their step (`hK`, `hK'`) and agree on the
rows in `G i` and the columns in the set before, with label `none` or `some r`, read along `τ i`
on the rows, along the previous permutation on the columns and along `ρ i` on the operators
(`hop`), and initial states that agree along `τ₀` there (`hρ`), the run of `K'` after
step `n` agrees with that of `K` along `τ n` on the basis states whose work register lies in
`G n` with label `none` or `some r`. -/
theorem densityRun_relabel_block (ℓ : V → Option L) (G G' : ℕ → Set V) (G₀ G₀' : Set V)
    (τ : ℕ → Equiv.Perm V) (τ₀ : Equiv.Perm V) (hτ : ∀ n v, ℓ (τ n v) = ℓ v)
    (hτ₀ : ∀ v, ℓ (τ₀ v) = ℓ v) (r : L) (hτG : ∀ n v, InBlock ℓ r v → (τ n v ∈ G' n ↔ v ∈ G n))
    (hτ₀G : ∀ v, InBlock ℓ r v → (τ₀ v ∈ G₀' ↔ v ∈ G₀)) (hGc : ∀ n, t < n → G n = G (n - 1))
    (hGc' : ∀ n, t < n → G' n = G' (n - 1)) (hτc : ∀ n, t < n → τ n = τ (n - 1))
    (K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (hG : ∀ (i : Fin (t + 1)) k, KeepsSet
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G G₀ i}
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ G i} ((K i).op k))
    (hG' : ∀ (i : Fin (t + 1)) k, KeepsSet
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G' G₀' i}
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ G' i} ((K' i).op k))
    (ρ : Fin (t + 1) → Equiv.Perm R)
    (hop : ∀ (i : Fin (t + 1)) k (a b : QueryReg V 1 (Bits m) (BitStr I J)), a.1 ∈ G i →
      b.1 ∈ prevSeq G G₀ i → InBlock ℓ r a.1 → InBlock ℓ r b.1 →
      (K' i).op (ρ i k) (((τ i).prodCongr (Equiv.refl _)) a)
        (((prevSeq τ τ₀ i).prodCongr (Equiv.refl _)) b) = (K i).op k a b)
    (hK : ∀ (i : Fin (t + 1)) k, KeepsBlocksOn
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G G₀ i}
      (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K i).op k))
    (hK' : ∀ (i : Fin (t + 1)) k, KeepsBlocksOn
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G' G₀' i}
      (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K' i).op k))
    (ρ₀ ρ₀' : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (hρs : ∀ a b, ρ₀ a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (hρs' : ∀ a b, ρ₀' a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀')
    (hρ : ∀ a b, a.1 ∈ G₀ → b.1 ∈ G₀ → InBlock ℓ r a.1 → InBlock ℓ r b.1 →
      ρ₀' ((τ₀.prodCongr (Equiv.refl _)) a) ((τ₀.prodCongr (Equiv.refl _)) b) = ρ₀ a b) :
    ∀ n (a b : SimRegister V I J m t), a.1.1 ∈ G n → b.1.1 ∈ G n → InBlock ℓ r a.1.1 →
      InBlock ℓ r b.1.1 →
      densityRun e K' ρ₀' n (simWorkPerm (τ n) a) (simWorkPerm (τ n) b) =
        densityRun e K ρ₀ n a b := by
  set ℓS : SimRegister V I J m t → Option L := fun p => ℓ p.1.1
  set GS : ℕ → Set (SimRegister V I J m t) := fun n => {p | p.1.1 ∈ G n}
  set GS₀ : Set (SimRegister V I J m t) := {p | p.1.1 ∈ G₀}
  have hπ : ∀ (σ : Equiv.Perm V), (∀ v, ℓ (σ v) = ℓ v) →
      ∀ a, ℓS (simWorkPerm (I := I) (J := J) (m := m) (t := t) σ a) = ℓS a :=
    fun σ hσ a => hσ a.1.1
  have hπG : ∀ (S S' : Set V) (σ : Equiv.Perm V), (∀ v, InBlock ℓ r v → (σ v ∈ S' ↔ v ∈ S)) →
      ∀ a : SimRegister V I J m t, InBlock ℓS r a → ((simWorkPerm σ a).1.1 ∈ S' ↔ a.1.1 ∈ S) :=
    fun S S' σ hσ a ha => hσ a.1.1 ha
  have hprevL : ∀ n v, ℓ (prevSeq τ τ₀ n v) = ℓ v := fun n v => by
    simp only [prevSeq]
    split_ifs
    · exact hτ₀ v
    · exact hτ _ v
  have hprevG : ∀ n v, InBlock ℓ r v → (prevSeq τ τ₀ n v ∈ prevSeq G' G₀' n ↔
      v ∈ prevSeq G G₀ n) := fun n v hv => by
    simp only [prevSeq]
    split_ifs
    · exact hτ₀G v hv
    · exact hτG _ v hv
  have hopT : ∀ (i : Fin (t + 1)) k (a b : SimRegister V I J m t), a.1.1 ∈ G i →
      b.1.1 ∈ prevSeq G G₀ i →
      InBlock ℓS r a → InBlock ℓS r b →
      ((K' i).tensorId (Slots I J m t)).op (ρ i k) (simWorkPerm (τ i) a)
        (simWorkPerm (prevSeq τ τ₀ i) b) = ((K i).tensorId (Slots I J m t)).op k a b :=
    fun i k a b haG hbG ha hb => by
      simp only [KrausMap.tensorId, Matrix.kroneckerMap_apply]
      rw [show (simWorkPerm (I := I) (J := J) (m := m) (t := t) (τ i) a).1 =
          ((τ i).prodCongr (Equiv.refl _)) a.1 from rfl,
        show (simWorkPerm (I := I) (J := J) (m := m) (t := t) (prevSeq τ τ₀ i) b).1 =
          ((prevSeq τ τ₀ i).prodCongr (Equiv.refl _)) b.1 from rfl, hop i k a.1 b.1 haG hbG ha hb]
      rfl
  have hKT : ∀ (S : ℕ → Set V) (S₀ : Set V) (K : Fin (t + 1) → KrausMap R
      (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))),
      (∀ (i : Fin (t + 1)) k, KeepsBlocksOn
        {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq S S₀ i}
        (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K i).op k)) →
      ∀ (i : Fin (t + 1)) k, KeepsBlocksOn {p : SimRegister V I J m t | p.1.1 ∈ prevSeq S S₀ i} ℓS
        (((K i).tensorId (Slots I J m t)).op k) :=
    fun S S₀ K hK i k r' a b hbG hb h => by
      simp only [KrausMap.tensorId, Matrix.kroneckerMap_apply] at h
      exact hK i k r' a.1 b.1 hbG hb (left_ne_zero_of_mul h)
  have hsupp := densityRun_supported e G G₀ hGc K hG ρ₀ hρs
  have hsupp' := densityRun_supported e G' G₀' hGc' K' hG' ρ₀' hρs'
  have hstep : ∀ (k : ℕ) (M M' : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ prevSeq G G₀ k ∧ b.1.1 ∈ prevSeq G G₀ k) →
      (∀ a b, M' a b ≠ 0 → a.1.1 ∈ prevSeq G' G₀' k ∧ b.1.1 ∈ prevSeq G' G₀' k) →
      (∀ a b, a.1.1 ∈ prevSeq G G₀ k → b.1.1 ∈ prevSeq G G₀ k → InBlock ℓS r a →
        InBlock ℓS r b →
        M' (simWorkPerm (prevSeq τ τ₀ k) a) (simWorkPerm (prevSeq τ τ₀ k) b) = M a b) →
      ∀ a b, a.1.1 ∈ G k → b.1.1 ∈ G k → InBlock ℓS r a → InBlock ℓS r b →
        KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) k M'
          (simWorkPerm (τ k) a) (simWorkPerm (τ k) b) =
          KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) k M a b := by
    intro k M M' hMs hM's hM a b haG hbG ha hb
    unfold KrausMap.stepAt
    split_ifs with hk
    · exact KrausMap.apply_relabel_block {p : SimRegister V I J m t | p.1.1 ∈ prevSeq G G₀ k}
        {p : SimRegister V I J m t | p.1.1 ∈ prevSeq G' G₀' k}
        {p : SimRegister V I J m t | p.1.1 ∈ G k} _ _ (hπ _ (hτ k)) (hπ _ (hprevL k)) r
        (hπG _ _ _ (hprevG k)) (ρ ⟨k, hk⟩) (hopT ⟨k, hk⟩) (hKT G G₀ K hK ⟨k, hk⟩)
        (hKT G' G₀' K' hK' ⟨k, hk⟩) hMs hM's hM
        a b haG hbG ha hb
    · have hk0 : k ≠ 0 := by omega
      have h1 : prevSeq τ τ₀ k = τ k := by
        simp only [prevSeq, hk0, ↓reduceIte]
        exact (hτc k (by omega)).symm
      have h2 : prevSeq G G₀ k = G k := by
        simp only [prevSeq, hk0, ↓reduceIte]
        exact (hGc k (by omega)).symm
      rw [← h1]
      exact hM a b (h2 ▸ haG) (h2 ▸ hbG) ha hb
  have hQK : ∀ S : Set V, KeepsBlocksOn {p : SimRegister V I J m t | p.1.1 ∈ S} ℓS
      (Matrix.of (simQueryKernel (I := I) (J := J) (m := m) e V t)) :=
    fun S r' a b _ hb h => by
      have := simQueryKernel_work e h
      simp only [ℓS] at hb ⊢
      rw [this]
      exact hb
  have hQs : ∀ (S : Set V) (M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S) →
      ∀ a b, (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ :
        Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) a b ≠ 0 →
        a.1.1 ∈ S ∧ b.1.1 ∈ S :=
    fun S M hM a b h => by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply] at h
      obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hc)
      have h1 := simQueryKernel_work e (left_ne_zero_of_mul hd)
      have h2 := simQueryKernel_work e (fun h0 => right_ne_zero_of_mul hc (by rw [h0, star_zero]))
      obtain ⟨hdS, hcS⟩ := hM d c (right_ne_zero_of_mul hd)
      exact ⟨h1 ▸ hdS, h2 ▸ hcS⟩
  have hkr : ∀ (S : ℕ → Set V) (S₀ : Set V) (ρ : Matrix (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)) ℂ), (∀ a b, ρ a b ≠ 0 → a.1 ∈ S₀ ∧ b.1 ∈ S₀) →
      ∀ a b, (ρ ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B))
        (dbSlots e t (∅ : DB (Bits m) B)) (1 : ℂ) : Matrix (SimRegister V I J m t)
          (SimRegister V I J m t) ℂ) a b ≠ 0 → a.1.1 ∈ prevSeq S S₀ 0 ∧ b.1.1 ∈ prevSeq S S₀ 0 :=
    fun S S₀ ρ hρ a b h => by
      simp only [Matrix.kroneckerMap_apply] at h
      exact hρ a.1 b.1 (left_ne_zero_of_mul h)
  intro n
  induction n with
  | zero =>
    intro a b haG hbG ha hb
    simp only [densityRun]
    refine hstep 0 _ _ (hkr G G₀ ρ₀ hρs) (hkr G' G₀' ρ₀' hρs') (fun a b haG hbG ha hb => ?_) a b
      haG hbG ha hb
    simp only [Matrix.kroneckerMap_apply]
    rw [show (simWorkPerm (I := I) (J := J) (m := m) (t := t) (prevSeq τ τ₀ 0) a).1 =
        (τ₀.prodCongr (Equiv.refl _)) a.1 from rfl,
      show (simWorkPerm (I := I) (J := J) (m := m) (t := t) (prevSeq τ τ₀ 0) b).1 =
        (τ₀.prodCongr (Equiv.refl _)) b.1 from rfl, hρ a.1 b.1 haG hbG ha hb]
    rfl
  | succ n ih =>
    intro a b haG hbG ha hb
    simp only [densityRun]
    have hpn : prevSeq τ τ₀ (n + 1) = τ n := by simp [prevSeq]
    have hpG : prevSeq G G₀ (n + 1) = G n := by simp [prevSeq]
    have hpG' : prevSeq G' G₀' (n + 1) = G' n := by simp [prevSeq]
    refine hstep (n + 1) _ _ (hpG ▸ hQs _ _ (hsupp n)) (hpG' ▸ hQs _ _ (hsupp' n))
      (fun a b haG hbG ha hb => ?_) a b haG hbG ha hb
    rw [hpn]
    rw [hpG] at haG hbG
    exact mul_mul_conjTranspose_relabel_block {p : SimRegister V I J m t | p.1.1 ∈ G n}
      {p : SimRegister V I J m t | p.1.1 ∈ G' n}
      {p : SimRegister V I J m t | p.1.1 ∈ G n} _ _ (hπ _ (hτ n)) (hπ _ (hτ n)) r
      (hπG _ _ _ (hτG n))
      (fun a b _ _ _ _ => by
        simp only [Matrix.of_apply]
        exact simQueryKernel_simWorkPerm e (τ n) a b) (hQK _) (hQK _) (hsupp n) (hsupp' n)
      (fun a b haG hbG ha hb => ih a b haG hbG ha hb) a b haG hbG ha hb

end Run

/-! ### The masses of the blocks -/

section Mass

variable {ι L R : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq L] [Fintype R]
  {ℓ : ι → Option L}

/-- **The indicator of a label value.** -/
def labelInd (ℓ : ι → Option L) (o : Option L) (c : ι) : ℂ :=
  if ℓ c = o then 1 else 0

omit [DecidableEq ι] [DecidableEq L] in
/-- Four sums reordered. -/
theorem sum_four_comm {M : Type*} [AddCommMonoid M] (s : Finset ι) (f : R → ι → ι → ι → M) :
    ∑ a ∈ s, ∑ k, ∑ c, ∑ d, f k a c d = ∑ c, ∑ d, ∑ k, ∑ a ∈ s, f k a c d := by
  calc ∑ a ∈ s, ∑ k, ∑ c, ∑ d, f k a c d = ∑ k, ∑ a ∈ s, ∑ c, ∑ d, f k a c d := Finset.sum_comm
    _ = ∑ k, ∑ c, ∑ a ∈ s, ∑ d, f k a c d :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ c, ∑ d, ∑ a ∈ s, f k a c d :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ k, ∑ d, ∑ a ∈ s, f k a c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ k, ∑ a ∈ s, f k a c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **The mass of block `r` after one family of conjugations**: for a family keeping the blocks
with `∑ (B k)ᴴ B k = 1`, the mass of block `r` of `∑ B k N (B k)ᴴ` is that of `N` plus the part
coming from the `none` block of `N` through the columns with label `none`. -/
theorem sum_filter_conj_eq (Gs : Set ι) (B : R → Matrix ι ι ℂ)
    (hB : ∀ k, KeepsBlocksOn Gs ℓ (B k)) (hBTP : ∑ k, (B k)ᴴ * B k = 1) (N : Matrix ι ι ℂ)
    (hN : ∀ a b, N a b ≠ 0 → a ∈ Gs ∧ b ∈ Gs) (r : L) :
    ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), (∑ k, B k * N * (B k)ᴴ) a a =
      ∑ c, labelInd ℓ (some r) c * N c c +
        ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), ∑ k, ∑ c, ∑ d,
          labelInd ℓ none c * labelInd ℓ none d * (B k a c * N c d * star (B k a d)) := by
  classical
  -- the overlaps of the columns `c`, `d` from the rows of block `r`
  set G : ι → ι → ℂ := fun c d =>
    ∑ k, ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), B k a c * star (B k a d) with hG
  have hTPe : ∀ c d, ∑ k, ∑ a, star (B k a d) * B k a c = if d = c then 1 else 0 := fun c d => by
    have h2 := congrFun (congrFun hBTP d) c
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] at h2
    exact h2
  -- a column of block `r` is overlapped only from block `r`
  have hGr : ∀ c d, c ∈ Gs → ℓ c = some r → G c d = if d = c then 1 else 0 := fun c d hcG hc => by
    rw [hG, ← hTPe c d]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with ha
    · ring
    · have : B k a c = 0 := by_contra fun h => ha (hB k r a c hcG hc h)
      simp [this]
  have hGr' : ∀ c d, d ∈ Gs → ℓ d = some r → G c d = if c = d then 1 else 0 :=
      fun c d hdG hd => by
    have h1 := hGr d c hdG hd
    have h2 : G c d = star (G d c) := by
      simp only [hG, star_sum, star_mul', star_star]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [h2, h1]
    split_ifs <;> simp
  -- the terms by the columns' labels
  have hterm : ∀ k a c d, ℓ a = some r →
      B k a c * N c d * star (B k a d) =
        (labelInd ℓ (some r) c * labelInd ℓ (some r) d + labelInd ℓ (some r) c * labelInd ℓ none d +
          labelInd ℓ none c * labelInd ℓ (some r) d) * N c d * (B k a c * star (B k a d)) +
        labelInd ℓ none c * labelInd ℓ none d * (B k a c * N c d * star (B k a d)) := by
    intro k a c d ha
    by_cases hN0 : N c d = 0
    · simp [hN0]
    obtain ⟨hcG, hdG⟩ := hN c d hN0
    by_cases hc0 : B k a c = 0
    · simp [hc0]
    by_cases hd0 : B k a d = 0
    · simp [hd0]
    rcases mem_inBlock_of_ne_zero_on (hB k) (Or.inr ha) hcG hc0 with hc | hc <;>
      rcases mem_inBlock_of_ne_zero_on (hB k) (Or.inr ha) hdG hd0 with hd | hd <;>
      simp [labelInd, hc, hd] <;> ring
  -- the overlaps of block `r` and the other labels give the mass of block `r` of `N`
  have hrow : ∀ c, ∑ d, (labelInd ℓ (some r) c * labelInd ℓ (some r) d +
      labelInd ℓ (some r) c * labelInd ℓ none d + labelInd ℓ none c * labelInd ℓ (some r) d) *
        N c d * G c d = labelInd ℓ (some r) c * N c c := fun c => by
    by_cases hcG : c ∈ Gs
    · by_cases hc : ℓ c = some r
      · rw [Finset.sum_eq_single c]
        · rw [hGr c c hcG hc]
          simp [labelInd, hc]
        · intro d _ hdc
          simp [hGr c d hcG hc, hdc]
        · simp
      · have h0 : labelInd ℓ (some r) c = 0 := by simp [labelInd, hc]
        rw [h0, zero_mul]
        refine Finset.sum_eq_zero fun d _ => ?_
        by_cases hN0 : N c d = 0
        · simp [hN0]
        have hdG := (hN c d hN0).2
        by_cases hd : ℓ d = some r
        · have hne : c ≠ d := fun h => hc (by rw [h]; exact hd)
          simp [hGr' c d hdG hd, hne]
        · have h1 : labelInd ℓ (some r) d = 0 := by simp [labelInd, hd]
          simp [h1]
    · have h0 : ∀ d, N c d = 0 := fun d => by_contra fun h => hcG (hN c d h).1
      simp [h0]
  have hentry : ∀ (k : R) (a : ι), (B k * N * (B k)ᴴ) a a =
      ∑ c, ∑ d, B k a c * N c d * star (B k a d) := fun k a => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  calc ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), (∑ k, B k * N * (B k)ᴴ) a a
      = ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), ∑ k, ∑ c, ∑ d,
          ((labelInd ℓ (some r) c * labelInd ℓ (some r) d + labelInd ℓ (some r) c *
            labelInd ℓ none d + labelInd ℓ none c * labelInd ℓ (some r) d) * N c d *
              (B k a c * star (B k a d)) +
            labelInd ℓ none c * labelInd ℓ none d * (B k a c * N c d * star (B k a d))) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Matrix.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hentry]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          hterm k a c d (Finset.mem_filter.1 ha).2
    _ = ∑ c, ∑ d, (labelInd ℓ (some r) c * labelInd ℓ (some r) d + labelInd ℓ (some r) c *
            labelInd ℓ none d + labelInd ℓ none c * labelInd ℓ (some r) d) * N c d * G c d +
          ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), ∑ k, ∑ c, ∑ d,
            labelInd ℓ none c * labelInd ℓ none d * (B k a c * N c d * star (B k a d)) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        rw [sum_four_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        simp only [hG, Finset.mul_sum]
    _ = _ := by
        simp only [hrow]


omit [DecidableEq ι] in
/-- **The overlaps of the rows of a block under a Kraus operator tensored with the identity.** -/
theorem sum_filter_kron_one {A : Type*} [Fintype A] [DecidableEq A] [DecidableEq ι]
    (B : R → Matrix ι ι ℂ) (r : L) (c d : ι × A) :
    ∑ k, ∑ a ∈ Finset.univ.filter (fun a : ι × A => ℓ a.1 = some r),
        (B k ⊗ₖ (1 : Matrix A A ℂ)) a c * star ((B k ⊗ₖ (1 : Matrix A A ℂ)) a d) =
      (if c.2 = d.2 then 1 else 0) *
        ∑ k, ∑ a ∈ Finset.univ.filter (fun a : ι => ℓ a = some r),
          B k a c.1 * star (B k a d.1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  by_cases h : ℓ a₁ = some r
  · simp only [h, ite_true]
    rw [Finset.sum_eq_single c.2 (fun x _ hx => by simp [Matrix.kroneckerMap_apply,
      Matrix.one_apply, hx]) (by simp)]
    by_cases hcd : c.2 = d.2 <;> simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hcd]
  · simp [h]

/-- **Two families of conjugations on the `none` block and the masses of the blocks**: for
families `A`, `A'` keeping the blocks on the columns in `Gs` and `Gs'` (sets with the same states
of label `none`), with `∑ (A k)ᴴ A k = 1` and `∑ (A' k)ᴴ A' k = 1`, agreeing on the rows in `Gr`
and the columns in `Gs` with label `none` with the same overlaps into every block from those
columns, and matrices `M`, `M'` supported on `Gs` and `Gs'` agreeing on the `none` block with the
same mass on every block, the images agree on the `none` block of `Gr` and have the same mass on
every block. -/
theorem sum_conj_block_mass (Gs Gs' Gr : Set ι) {A A' : R → Matrix ι ι ℂ}
    (hA : ∀ k, KeepsBlocksOn Gs ℓ (A k)) (hA' : ∀ k, KeepsBlocksOn Gs' ℓ (A' k))
    (hTP : ∑ k, (A k)ᴴ * A k = 1) (hTP' : ∑ k, (A' k)ᴴ * A' k = 1)
    (hnone : ∀ a, ℓ a = none → (a ∈ Gs' ↔ a ∈ Gs))
    (hrow : ∀ k a b, a ∈ Gr → b ∈ Gs → ℓ a = none → ℓ b = none → A' k a b = A k a b)
    (hgram : ∀ r c d, c ∈ Gs → d ∈ Gs → ℓ c = none → ℓ d = none →
      ∑ k, ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), A' k a c * star (A' k a d) =
        ∑ k, ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), A k a c * star (A k a d))
    {M M' : Matrix ι ι ℂ} (hMs : ∀ a b, M a b ≠ 0 → a ∈ Gs ∧ b ∈ Gs)
    (hM's : ∀ a b, M' a b ≠ 0 → a ∈ Gs' ∧ b ∈ Gs')
    (hMn : ∀ a b, a ∈ Gs → b ∈ Gs → ℓ a = none → ℓ b = none → M' a b = M a b)
    (hMm : ∀ r, ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), M' a a =
      ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), M a a) :
    (∀ a b, a ∈ Gr → b ∈ Gr → ℓ a = none → ℓ b = none →
      (∑ k, A' k * M' * (A' k)ᴴ) a b = (∑ k, A k * M * (A k)ᴴ) a b) ∧
    ∀ r, ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), (∑ k, A' k * M' * (A' k)ᴴ) a a =
      ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), (∑ k, A k * M * (A k)ᴴ) a a := by
  -- a nonzero entry in a row of label `none` has its column of label `none`
  have hcol : ∀ {S : Set ι} {B : Matrix ι ι ℂ}, KeepsBlocksOn S ℓ B → ∀ {a c}, ℓ a = none →
      c ∈ S → B a c ≠ 0 → ℓ c = none := fun {S B} hB {a c} ha hcG h => by
    rcases hc : ℓ c with _ | r'
    · rfl
    · have := hB r' a c hcG hc h
      rw [ha] at this
      exact absurd this (by simp)
  -- the terms through a column of label other than `none` vanish
  have hzl : ∀ {S : Set ι} {B N : Matrix ι ι ℂ}, KeepsBlocksOn S ℓ B →
      (∀ a b, N a b ≠ 0 → a ∈ S ∧ b ∈ S) → ∀ {x c d}, ℓ x = none → ℓ c ≠ none →
        B x c * N c d = 0 := fun {S B N} hB hN {x c d} hx hc => by
    by_cases hcS : c ∈ S
    · rw [show B x c = 0 from by_contra fun h => hc (hcol hB hx hcS h), zero_mul]
    · rw [show N c d = 0 from by_contra fun h => hcS (hN c d h).1, mul_zero]
  have hzr : ∀ {S : Set ι} {B N : Matrix ι ι ℂ}, KeepsBlocksOn S ℓ B →
      (∀ a b, N a b ≠ 0 → a ∈ S ∧ b ∈ S) → ∀ {x c d}, ℓ x = none → ℓ d ≠ none →
        N c d * star (B x d) = 0 := fun {S B N} hB hN {x c d} hx hd => by
    by_cases hdS : d ∈ S
    · rw [show B x d = 0 from by_contra fun h => hd (hcol hB hx hdS h), star_zero, mul_zero]
    · rw [show N c d = 0 from by_contra fun h => hdS (hN c d h).2, zero_mul]
  -- off `Gs` the `none` block of both matrices vanishes
  have hz : ∀ c d, ℓ c = none → ℓ d = none → ¬ (c ∈ Gs ∧ d ∈ Gs) → M c d = 0 ∧ M' c d = 0 :=
    fun c d hc hd h => ⟨by_contra fun h' => h (hMs c d h'), by_contra fun h' => h
      ⟨(hnone c hc).1 (hM's c d h').1, (hnone d hd).1 (hM's c d h').2⟩⟩
  have hentry : ∀ (B N : Matrix ι ι ℂ) (a b : ι),
      (B * N * Bᴴ) a b = ∑ c, ∑ d, B a c * N c d * star (B b d) := fun B N a b => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdiag : ∀ (N : Matrix ι ι ℂ) r, ∑ c, labelInd ℓ (some r) c * N c c =
      ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), N a a := fun N r => by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [labelInd]
    split_ifs <;> simp
  refine ⟨fun a b haG hbG ha hb => ?_, fun r => ?_⟩
  · simp only [Matrix.sum_apply, hentry]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    by_cases hc : ℓ c = none
    · by_cases hd : ℓ d = none
      · by_cases hcd : c ∈ Gs ∧ d ∈ Gs
        · obtain ⟨hcG, hdG⟩ := hcd
          rw [hrow k a c haG hcG ha hc, hMn c d hcG hdG hc hd, hrow k b d hbG hdG hb hd]
        · simp [(hz c d hc hd hcd).1, (hz c d hc hd hcd).2]
      · rw [mul_assoc, mul_assoc, hzr (hA' k) hM's hb hd, hzr (hA k) hMs hb hd, mul_zero,
          mul_zero]
    · rw [hzl (hA' k) hM's ha hc, hzl (hA k) hMs ha hc, zero_mul, zero_mul]
  · rw [sum_filter_conj_eq Gs' A' hA' hTP' M' hM's r, sum_filter_conj_eq Gs A hA hTP M hMs r, hdiag,
      hdiag, hMm r]
    congr 1
    rw [sum_four_comm, sum_four_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases hc : ℓ c = none
    · by_cases hd : ℓ d = none
      · by_cases hcd : c ∈ Gs ∧ d ∈ Gs
        · obtain ⟨hcG, hdG⟩ := hcd
          have hfac : ∀ B : R → Matrix ι ι ℂ, ∀ N : Matrix ι ι ℂ,
              ∑ k, ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r),
                labelInd ℓ none c * labelInd ℓ none d * (B k a c * N c d * star (B k a d)) =
              labelInd ℓ none c * labelInd ℓ none d * N c d *
                ∑ k, ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r),
                  B k a c * star (B k a d) :=
            fun B N => by
              simp only [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
              ring
          rw [hfac, hfac, hgram r c d hcG hdG hc hd, hMn c d hcG hdG hc hd]
        · simp [(hz c d hc hd hcd).1, (hz c d hc hd hcd).2]
      · simp [labelInd, hd]
    · simp [labelInd, hc]

end Mass

/-- **The simulated query has orthonormal columns.** -/
theorem simQueryKernel_unitary {V : Type} [Fintype V] [DecidableEq V] {t : ℕ} :
    (Matrix.of (simQueryKernel (I := I) (J := J) (m := m) e V t))ᴴ *
      Matrix.of (simQueryKernel (I := I) (J := J) (m := m) e V t) = 1 :=
  conjTranspose_mul_of_norm_kernelOp _ fun v => by
    rw [← simQuery_eq_kernelOp]
    exact norm_simQuery e v

section Mass

variable {V R L : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq L] {t : ℕ}

/-- **The density-matrix runs on the `none` block and the masses of the blocks**: for a label `ℓ`
of the work register, sets `G n` and `G' n` (after step `n`; `G₀`, `G₀'` of the initial state)
with the same states of label `none` (`hnone`, `hnone₀`) through which the trace-preserving Kraus
maps `K` and `K'` move (`hG`, `hG'`), constant after the last step (`hGc`, `hGc'`), Kraus maps that
keep the blocks of `ℓ` on the columns in their set before their step (`hK`, `hK'`), agree on the
rows in `G i` with label `none` from the columns in the set before with label `none` (`hrow`) and
whose rows of every block have the same overlaps from two columns with label `none` in the set
before (`hgram`), the runs from the same initial state, supported on `G₀` and `G₀'`, agree on the
basis states in `G n` with label `none` and give every block `some r` the same mass. -/
theorem densityRun_block_mass (ℓ : V → Option L) (G G' : ℕ → Set V) (G₀ G₀' : Set V)
    (hGc : ∀ n, t < n → G n = G (n - 1)) (hGc' : ∀ n, t < n → G' n = G' (n - 1))
    (hnone : ∀ n v, ℓ v = none → (v ∈ G' n ↔ v ∈ G n))
    (hnone₀ : ∀ v, ℓ v = none → (v ∈ G₀' ↔ v ∈ G₀))
    (K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (hG : ∀ (i : Fin (t + 1)) k, KeepsSet
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G G₀ i}
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ G i} ((K i).op k))
    (hG' : ∀ (i : Fin (t + 1)) k, KeepsSet
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G' G₀' i}
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ G' i} ((K' i).op k))
    (hK : ∀ (i : Fin (t + 1)) k, KeepsBlocksOn
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G G₀ i}
      (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K i).op k))
    (hK' : ∀ (i : Fin (t + 1)) k, KeepsBlocksOn
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq G' G₀' i}
      (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K' i).op k))
    (hTP : ∀ i, ∑ k, ((K i).op k)ᴴ * (K i).op k = 1)
    (hTP' : ∀ i, ∑ k, ((K' i).op k)ᴴ * (K' i).op k = 1)
    (hrow : ∀ (i : Fin (t + 1)) k (a b : QueryReg V 1 (Bits m) (BitStr I J)), a.1 ∈ G i →
      b.1 ∈ prevSeq G G₀ i → ℓ a.1 = none → ℓ b.1 = none → (K' i).op k a b = (K i).op k a b)
    (hgram : ∀ (i : Fin (t + 1)) r (c d : QueryReg V 1 (Bits m) (BitStr I J)),
      c.1 ∈ prevSeq G G₀ i → d.1 ∈ prevSeq G G₀ i → ℓ c.1 = none → ℓ d.1 = none →
      ∑ k, ∑ a ∈ Finset.univ.filter
          (fun a : QueryReg V 1 (Bits m) (BitStr I J) => ℓ a.1 = some r),
          (K' i).op k a c * star ((K' i).op k a d) =
        ∑ k, ∑ a ∈ Finset.univ.filter
            (fun a : QueryReg V 1 (Bits m) (BitStr I J) => ℓ a.1 = some r),
          (K i).op k a c * star ((K i).op k a d))
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (hρs : ∀ a b, ρ₀ a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (hρs' : ∀ a b, ρ₀ a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀') :
    ∀ n, (∀ a b : SimRegister V I J m t, a.1.1 ∈ G n → b.1.1 ∈ G n → ℓ a.1.1 = none →
        ℓ b.1.1 = none → densityRun e K' ρ₀ n a b = densityRun e K ρ₀ n a b) ∧
      ∀ r, ∑ a ∈ Finset.univ.filter (fun a : SimRegister V I J m t => ℓ a.1.1 = some r),
          densityRun e K' ρ₀ n a a =
        ∑ a ∈ Finset.univ.filter (fun a : SimRegister V I J m t => ℓ a.1.1 = some r),
          densityRun e K ρ₀ n a a := by
  set ℓS : SimRegister V I J m t → Option L := fun p => ℓ p.1.1
  have hKT : ∀ (S : ℕ → Set V) (S₀ : Set V) (K : Fin (t + 1) → KrausMap R
      (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))),
      (∀ (i : Fin (t + 1)) k, KeepsBlocksOn
        {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq S S₀ i}
        (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K i).op k)) →
      ∀ (i : Fin (t + 1)) k, KeepsBlocksOn {p : SimRegister V I J m t | p.1.1 ∈ prevSeq S S₀ i}
        ℓS (((K i).tensorId (Slots I J m t)).op k) :=
    fun S S₀ K hK i k r' a b hbG hb h => by
      simp only [KrausMap.tensorId, Matrix.kroneckerMap_apply] at h
      exact hK i k r' a.1 b.1 hbG hb (left_ne_zero_of_mul h)
  have hTPT : ∀ (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))), (∀ i, ∑ k, ((K i).op k)ᴴ * (K i).op k = 1) →
      ∀ i, ∑ k, (((K i).tensorId (Slots I J m t)).op k)ᴴ *
        ((K i).tensorId (Slots I J m t)).op k = 1 := fun K hTP i => by
    simp only [KrausMap.tensorId]
    have h : ∑ k, ((K i).op k ⊗ₖ (1 : Matrix (Slots I J m t) (Slots I J m t) ℂ))ᴴ *
        ((K i).op k ⊗ₖ (1 : Matrix (Slots I J m t) (Slots I J m t) ℂ)) =
        (∑ k, ((K i).op k)ᴴ * (K i).op k) ⊗ₖ (1 : Matrix (Slots I J m t) (Slots I J m t) ℂ) := by
      rw [Matrix.sum_kronecker]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul]
    rw [h, hTP i, Matrix.one_kronecker_one]
  have hrowT : ∀ (i : Fin (t + 1)) k (a b : SimRegister V I J m t), a.1.1 ∈ G i →
      b.1.1 ∈ prevSeq G G₀ i → ℓS a = none → ℓS b = none →
      ((K' i).tensorId (Slots I J m t)).op k a b = ((K i).tensorId (Slots I J m t)).op k a b :=
    fun i k a b haG hbG ha hb => by
      simp only [KrausMap.tensorId, Matrix.kroneckerMap_apply]
      rw [hrow i k a.1 b.1 haG hbG ha hb]
  have hgramT : ∀ (i : Fin (t + 1)) r (c d : SimRegister V I J m t),
      c.1.1 ∈ prevSeq G G₀ i → d.1.1 ∈ prevSeq G G₀ i → ℓS c = none → ℓS d = none →
      ∑ k, ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r),
          ((K' i).tensorId (Slots I J m t)).op k a c *
            star (((K' i).tensorId (Slots I J m t)).op k a d) =
        ∑ k, ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r),
          ((K i).tensorId (Slots I J m t)).op k a c *
            star (((K i).tensorId (Slots I J m t)).op k a d) := fun i r c d hcG hdG hc hd => by
    simp only [KrausMap.tensorId]
    rw [sum_filter_kron_one (ℓ := fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1),
      sum_filter_kron_one (ℓ := fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1),
      hgram i r c.1 d.1 hcG hdG hc hd]
  have hsupp := densityRun_supported e G G₀ hGc K hG ρ₀ hρs
  have hsupp' := densityRun_supported e G' G₀' hGc' K' hG' ρ₀ hρs'
  have hprevN : ∀ n v, ℓ v = none → (v ∈ prevSeq G' G₀' n ↔ v ∈ prevSeq G G₀ n) := fun n v hv => by
    simp only [prevSeq]
    split_ifs
    · exact hnone₀ v hv
    · exact hnone _ v hv
  have hstep : ∀ (k : ℕ) (M M' : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ prevSeq G G₀ k ∧ b.1.1 ∈ prevSeq G G₀ k) →
      (∀ a b, M' a b ≠ 0 → a.1.1 ∈ prevSeq G' G₀' k ∧ b.1.1 ∈ prevSeq G' G₀' k) →
      (∀ a b, a.1.1 ∈ prevSeq G G₀ k → b.1.1 ∈ prevSeq G G₀ k → ℓS a = none → ℓS b = none →
        M' a b = M a b) →
      (∀ r, ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r), M' a a =
        ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r), M a a) →
      (∀ a b, a.1.1 ∈ G k → b.1.1 ∈ G k → ℓS a = none → ℓS b = none →
        KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) k M' a b =
          KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) k M a b) ∧
      ∀ r, ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r),
          KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) k M' a a =
        ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r),
          KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) k M a a := by
    intro k M M' hMs hM's hMn hMm
    unfold KrausMap.stepAt
    split_ifs with hk
    · exact sum_conj_block_mass {p : SimRegister V I J m t | p.1.1 ∈ prevSeq G G₀ k}
        {p : SimRegister V I J m t | p.1.1 ∈ prevSeq G' G₀' k}
        {p : SimRegister V I J m t | p.1.1 ∈ G k} (hKT G G₀ K hK ⟨k, hk⟩)
        (hKT G' G₀' K' hK' ⟨k, hk⟩) (hTPT K hTP ⟨k, hk⟩) (hTPT K' hTP' ⟨k, hk⟩)
        (fun a ha => hprevN k a.1.1 ha) (hrowT ⟨k, hk⟩) (hgramT ⟨k, hk⟩) hMs hM's hMn hMm
    · have hk0 : k ≠ 0 := by omega
      have h2 : prevSeq G G₀ k = G k := by
        simp only [prevSeq, hk0, ↓reduceIte]
        exact (hGc k (by omega)).symm
      exact ⟨fun a b haG hbG ha hb => hMn a b (h2 ▸ haG) (h2 ▸ hbG) ha hb, hMm⟩
  have hQK : ∀ S : Set V, KeepsBlocksOn {p : SimRegister V I J m t | p.1.1 ∈ S} ℓS
      (Matrix.of (simQueryKernel (I := I) (J := J) (m := m) e V t)) :=
    fun S r' a b _ hb h => by
      have := simQueryKernel_work e h
      simp only [ℓS] at hb ⊢
      rw [this]
      exact hb
  have hQs : ∀ (S : Set V) (M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S) →
      ∀ a b, (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ :
        Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) a b ≠ 0 →
        a.1.1 ∈ S ∧ b.1.1 ∈ S :=
    fun S M hM a b h => by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply] at h
      obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hc)
      have h1 := simQueryKernel_work e (left_ne_zero_of_mul hd)
      have h2 := simQueryKernel_work e (fun h0 => right_ne_zero_of_mul hc (by rw [h0, star_zero]))
      obtain ⟨hdS, hcS⟩ := hM d c (right_ne_zero_of_mul hd)
      exact ⟨h1 ▸ hdS, h2 ▸ hcS⟩
  have hquery : ∀ (S S' : Set V) (M M' : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      (∀ v, ℓ v = none → (v ∈ S' ↔ v ∈ S)) →
      (∀ a b, M a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S) → (∀ a b, M' a b ≠ 0 → a.1.1 ∈ S' ∧ b.1.1 ∈ S') →
      (∀ a b, a.1.1 ∈ S → b.1.1 ∈ S → ℓS a = none → ℓS b = none → M' a b = M a b) →
      (∀ r, ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r), M' a a =
        ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r), M a a) →
      (∀ a b, a.1.1 ∈ S → b.1.1 ∈ S → ℓS a = none → ℓS b = none →
        (Matrix.of (simQueryKernel e V t) * M' * (Matrix.of (simQueryKernel e V t))ᴴ :
          Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) a b =
          (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ :
            Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) a b) ∧
      ∀ r, ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r),
          (Matrix.of (simQueryKernel e V t) * M' * (Matrix.of (simQueryKernel e V t))ᴴ :
            Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) a a =
        ∑ a ∈ Finset.univ.filter (fun a => ℓS a = some r),
          (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ :
            Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) a a := by
    intro S S' M M' hSS hMs hM's hMn hMm
    have h := sum_conj_block_mass (R := Unit) {p : SimRegister V I J m t | p.1.1 ∈ S}
      {p : SimRegister V I J m t | p.1.1 ∈ S'} {p : SimRegister V I J m t | p.1.1 ∈ S}
      (A := fun _ => Matrix.of (simQueryKernel (I := I) (J := J) (m := m) e V t))
      (A' := fun _ => Matrix.of (simQueryKernel (I := I) (J := J) (m := m) e V t))
      (fun _ => hQK S) (fun _ => hQK S') (by simpa using simQueryKernel_unitary e)
      (by simpa using simQueryKernel_unitary e) (fun a ha => hSS a.1.1 ha)
      (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) hMs hM's hMn hMm
    simpa using h
  have hkr : ∀ (S : ℕ → Set V) (S₀ : Set V), (∀ a b, ρ₀ a b ≠ 0 → a.1 ∈ S₀ ∧ b.1 ∈ S₀) →
      ∀ a b, (ρ₀ ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B))
        (dbSlots e t (∅ : DB (Bits m) B)) (1 : ℂ) : Matrix (SimRegister V I J m t)
          (SimRegister V I J m t) ℂ) a b ≠ 0 → a.1.1 ∈ prevSeq S S₀ 0 ∧ b.1.1 ∈ prevSeq S S₀ 0 :=
    fun S S₀ hρ a b h => by
      simp only [Matrix.kroneckerMap_apply] at h
      exact hρ a.1 b.1 (left_ne_zero_of_mul h)
  intro n
  induction n with
  | zero =>
    simp only [densityRun]
    exact hstep 0 _ _ (hkr G G₀ hρs) (hkr G' G₀' hρs') (fun _ _ _ _ _ _ => rfl) fun _ => rfl
  | succ n ih =>
    simp only [densityRun]
    have hpG : prevSeq G G₀ (n + 1) = G n := by simp [prevSeq]
    have hpG' : prevSeq G' G₀' (n + 1) = G' n := by simp [prevSeq]
    obtain ⟨q1, q2⟩ := hquery (G n) (G' n) _ _ (hnone n) (hsupp n) (hsupp' n) ih.1 ih.2
    exact hstep (n + 1) _ _ (hpG ▸ hQs _ _ (hsupp n)) (hpG' ▸ hQs _ _ (hsupp' n))
      (hpG ▸ q1) q2

end Mass

end GordieHowe.QROM
