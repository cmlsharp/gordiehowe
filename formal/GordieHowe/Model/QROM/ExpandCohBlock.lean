-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.ExpandCohRelabel
public import GordieHowe.Model.QROM.DensityRunBlock

@[expose] public section

/-!
# The expanded coherent run on one block of a label

The block lemmas of `GordieHowe/Model/QROM/DensityRunBlock.lean` for the law of the measured output
and database of the expanded coherent run (`simLaw` of `expandAdv`, read from the density-matrix
run by `simLaw_expandCoh_eq`). For a label `ℓ` of the work register that the Kraus maps keep once
set:

- `simLaw_expandCoh_relabel_block`: an algorithm and the same algorithm with other Kraus maps and
  another initial state, each moving through its sets of well-formed registers that may change
  with the step, agreeing on those rows and columns with label `none` or `some r` along
  permutations of the work register that keep the label, map the sets of the first onto those of
  the second and may change with the step, and along permutations of the operators, give the
  same probability to every event of the outcome that implies label `some r` and that the last
  permutation keeps. The expansion need only read the output through queries (`E.next`) that the
  last permutation does not change, not the whole output.
- `simLaw_expandCoh_block_mass`: trace-preserving Kraus maps moving through sets with the same
  states of label `none`, agreeing on the rows with label `none`, whose rows of every block have
  the same overlaps from the columns with label `none` (`rowGram`), give every block `some r` the
  same probability.

- `Alg.BlockRel`, `Alg.BlockNone`, `simLaw_expandCoh_of_blockRel`, `simLaw_expandCoh_of_blockNone`:
  the hypotheses as structures,
  for the transport through the wrappers of an adversary.

Auxiliary: `expPerm_expBasisPerm_of_next`, `expPerm_symm_expBasisPerm_of_next`,
`opRel_expKraus_of_next`, `opRelOn_expKraus_of_next`, `expSeq`, `expSeq_eq_pred`, `expSeq_of_le`,
`opRelIdx_expKraus_of_next`, `keepsSet_expKraus`, `keepsBlocksOn_expKraus` (the expansion's
classical steps commute with `τ` when the expansion's queries do not see `τ`);
`KrausMap.tp_permConj`, `KrausMap.tp_optionSome`, `KrausMap.tp_optionNone`, `KrausMap.tp_relabel`,
`KrausMap.tp_tensorId`, `tp_liftKraus`, `tp_expKraus` (trace preservation of the constructions);
`posSemidef_single_one`, `densityRun_posSemidef` (the run of a positive semidefinite state is
positive semidefinite);
`expKraus_op_congr_col`, `expKraus_op_congr_row`, `expKraus_op_congr_rc`,
`expKraus_rowGram_congr` (expanded Kraus maps agreeing on a set of columns, on a set of rows, on
both, and in their overlaps).
-/

open Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv KrausRel

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B C : Type} (e : BitStr I J ≃ B) (E : Expansion (Bits m) B C) (k : ℕ)

/-! ### The expansion's steps along a permutation its queries do not see -/

section ExpLift

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] {τ : Equiv.Perm V}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype V] [DecidableEq V] in
/-- **The expansion's classical steps commute with a permutation of the work register** whose
effect the expansion's queries do not see (`hE`). -/
theorem expPerm_expBasisPerm_of_next {o : V → C} (hE : ∀ v, E.next (o (τ v)) = E.next (o v))
    (j : ℕ) (b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) :
    expPerm e E k o j (expBasisPerm k τ b) = expBasisPerm k τ (expPerm e E k o j b) := by
  have hq : ∀ w a j, queryAt e E k (o (τ w)) a j = queryAt e E k (o w) a j := fun w a j => by
    simp only [queryAt, hE]
  have hp : ∀ w a j, prevQuery e E k (o (τ w)) a j = prevQuery e E k (o w) a j := fun w a j => by
    cases j with
    | zero => rfl
    | succ j => exact hq w a j
  obtain ⟨⟨w, s, a⟩, q⟩ := b
  cases j with
  | zero =>
    simp only [expPerm, Equiv.trans_apply]
    simp only [stashPerm, movePerm, Equiv.coe_fn_mk, expBasisPerm, expWorkPerm,
      Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id, hq, hp]
  | succ j =>
    simp only [expPerm, Equiv.trans_apply]
    unfold recordPerm
    split_ifs
    · simp only [Equiv.trans_apply, addAnsPerm, subAnsPerm, movePerm, Equiv.coe_fn_mk,
        expBasisPerm, expWorkPerm, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id, hq, hp]
    · simp only [Equiv.Perm.coe_one, id, movePerm, Equiv.coe_fn_mk, expBasisPerm, expWorkPerm,
        Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, hq, hp]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype V] [DecidableEq V] in
theorem expPerm_symm_expBasisPerm_of_next {o : V → C}
    (hE : ∀ v, E.next (o (τ v)) = E.next (o v)) (j : ℕ)
    (b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) :
    (expPerm e E k o j).symm (expBasisPerm k τ b) =
      expBasisPerm k τ ((expPerm e E k o j).symm b) := by
  apply (expPerm e E k o j).injective
  rw [Equiv.apply_symm_apply, expPerm_expBasisPerm_of_next e E k hE, Equiv.apply_symm_apply]

/-- **The expanded Kraus maps along a permutation the expansion's queries do not see.** -/
theorem opRel_expKraus_of_next {t : ℕ} (S : Set V)
    {K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ i, OpRel (queryWorkPerm τ) {p | p.1 ∈ S} (K i) (K' i)) {o : V → C}
    (hE : ∀ v, E.next (o (τ v)) = E.next (o v)) (i : Fin (t + k + 1)) :
    OpRel (expBasisPerm k τ) {b | b.1.1 ∈ S} (expKraus e E k K o i) (expKraus e E k K' o i) := by
  unfold expKraus
  split_ifs with h1 h2
  · exact OpRel.optionSome (OpRel.liftKraus k S (h _))
  · exact OpRel.optionSome (OpRel.permConj (OpRel.liftKraus k S (h _)) (σ := 1)
      (τ := expPerm e E k o 0) (fun _ => rfl) (expPerm_symm_expBasisPerm_of_next e E k hE 0)
      (fun b hb => hb))
  · exact OpRel.optionNone (OpRel.permConj (opRel_identity (expBasisPerm k τ) {b | b.1.1 ∈ S})
      (σ := 1) (τ := expPerm e E k o (i - t)) (fun _ => rfl)
      (expPerm_symm_expBasisPerm_of_next e E k hE _) (fun b hb => hb)) R

/-- **The expanded Kraus maps along a permutation on the rows and columns of a set**: the
`OpRelOn` form of `opRel_expKraus_of_next`. -/
theorem opRelOn_expKraus_of_next {t : ℕ} (S : Set V)
    {K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ i, OpRelOn (queryWorkPerm τ) {p | p.1 ∈ S} (K i) (K' i)) {o : V → C}
    (hE : ∀ v, E.next (o (τ v)) = E.next (o v)) (i : Fin (t + k + 1)) :
    OpRelOn (expBasisPerm k τ) {b | b.1.1 ∈ S} (expKraus e E k K o i)
      (expKraus e E k K' o i) := by
  have hl : ∀ j r (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V), a.1.1 ∈ S → b.1.1 ∈ S →
      (liftKraus k (K' j)).op r (expBasisPerm k τ a) (expBasisPerm k τ b) =
        (liftKraus k (K j)).op r a b := fun j r a b ha hb => by
    change ((K' j).op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V (expBasisPerm k τ a))
      (registerSplit k V (expBasisPerm k τ b)) =
      ((K j).op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V a) (registerSplit k V b)
    rw [registerSplit_expBasisPerm, registerSplit_expBasisPerm, Matrix.kroneckerMap_apply,
      Matrix.kroneckerMap_apply, h j r _ _ ha hb]
  intro r a b ha hb
  unfold expKraus
  split_ifs with h1 h2
  · rcases r with _ | r
    · rfl
    · exact hl _ r a b ha hb
  · rcases r with _ | r
    · rfl
    · change (liftKraus k (K' _)).op r ((expPerm e E k o 0).symm (expBasisPerm k τ a))
        (expBasisPerm k τ b) = (liftKraus k (K _)).op r ((expPerm e E k o 0).symm a) b
      rw [expPerm_symm_expBasisPerm_of_next e E k hE 0]
      refine hl _ r _ b ?_ hb
      show ((expPerm e E k o 0).symm a).1.1 ∈ S
      rw [expPerm_symm_fst_fst]
      exact ha
  · rcases r with _ | r
    · change (1 : Matrix _ _ ℂ) ((expPerm e E k o (i - t)).symm (expBasisPerm k τ a))
        (expBasisPerm k τ b) = (1 : Matrix _ _ ℂ) ((expPerm e E k o (i - t)).symm a) b
      simp only [expPerm_symm_expBasisPerm_of_next e E k hE, Matrix.one_apply,
        (expBasisPerm k τ).injective.eq_iff]
    · rfl

/-- **The value of the expanded run after step `n`**: the value at `A`'s step `min n t`, constant
after `A`'s last step. -/
def expSeq {α : Sort*} {t : ℕ} (x : Fin (t + 1) → α) (n : ℕ) : α :=
  x ⟨min n t, by omega⟩

omit [Fintype V] [DecidableEq V] [Fintype R] in
/-- After `A`'s last step the expanded value is constant. -/
theorem expSeq_eq_pred {α : Sort*} {t : ℕ} (x : Fin (t + 1) → α) {n : ℕ} (h : t < n) :
    expSeq x n = expSeq x (n - 1) := by
  unfold expSeq
  congr 1
  ext
  simp only
  omega

omit [Fintype V] [DecidableEq V] [Fintype R] in
/-- From `A`'s last step on, the expanded value is the last. -/
theorem expSeq_of_le {α : Sort*} {t : ℕ} (x : Fin (t + 1) → α) {n : ℕ} (h : t ≤ n) :
    expSeq x n = x (Fin.last t) := by
  unfold expSeq
  congr 1
  ext
  simp only [Fin.val_last]
  omega

/-- **The expanded Kraus maps along permutations and sets that change with the step**: Kraus
maps agreeing on the rows in `S ∩ G i` and the columns in `S` and the set before step `i`, read
along `τ i` on the rows, the previous permutation on the columns and `ρ i` on the operators, give
expanded Kraus maps agreeing so along `expSeq τ`, `expSeq G` and `expSeq ρ` (on the operators of
`A`'s steps), for an expansion whose queries do not see the last permutation (`hE`). -/
theorem opRelIdx_expKraus_of_next {t : ℕ} (S : Set V) (G : Fin (t + 1) → Set V) (G₀ : Set V)
    (τ : Fin (t + 1) → Equiv.Perm V) (τ₀ : Equiv.Perm V)
    {K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (ρ : Fin (t + 1) → Equiv.Perm R)
    (h : ∀ i : Fin (t + 1), OpRelIdx (ρ i) (queryWorkPerm (τ i))
      (queryWorkPerm (prevSeq (expSeq τ) τ₀ i))
      {p | p.1 ∈ S ∧ p.1 ∈ G i} {p | p.1 ∈ S ∧ p.1 ∈ prevSeq (expSeq G) G₀ i} (K i) (K' i))
    {o : V → C} (hE : ∀ v, E.next (o (τ (Fin.last t) v)) = E.next (o v)) (i : Fin (t + k + 1)) :
    OpRelIdx (Equiv.optionCongr (expSeq ρ i)) (expBasisPerm k (expSeq τ i))
      (expBasisPerm k (prevSeq (expSeq τ) τ₀ i))
      {b | b.1.1 ∈ S ∧ b.1.1 ∈ expSeq G i} {b | b.1.1 ∈ S ∧ b.1.1 ∈ prevSeq (expSeq G) G₀ i}
      (expKraus e E k K o i) (expKraus e E k K' o i) := by
  have hl : ∀ (j : Fin (t + 1)) r (σ σ₀ : Equiv.Perm V) (Sr Sc : Set V),
      OpRelIdx (ρ j) (queryWorkPerm σ) (queryWorkPerm σ₀) {p | p.1 ∈ Sr} {p | p.1 ∈ Sc} (K j)
        (K' j) →
      ∀ (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V), a.1.1 ∈ Sr → b.1.1 ∈ Sc →
      (liftKraus k (K' j)).op (ρ j r) (expBasisPerm k σ a) (expBasisPerm k σ₀ b) =
        (liftKraus k (K j)).op r a b := fun j r σ σ₀ Sr Sc hj a b ha hb => by
    change ((K' j).op (ρ j r) ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V (expBasisPerm k σ a))
      (registerSplit k V (expBasisPerm k σ₀ b)) =
      ((K j).op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V a) (registerSplit k V b)
    rw [registerSplit_expBasisPerm, registerSplit_expBasisPerm, Matrix.kroneckerMap_apply,
      Matrix.kroneckerMap_apply, hj r _ _ ha hb]
  intro r a b ha hb
  unfold expKraus
  split_ifs with h1 h2
  · -- a step of `A` before its last
    have he : expSeq τ i = τ ⟨i, by omega⟩ := by
      simp only [expSeq]
      congr 2
      omega
    have heG : expSeq G i = G ⟨i, by omega⟩ := by
      simp only [expSeq]
      congr 2
      omega
    have heρ : expSeq ρ i = ρ ⟨i, by omega⟩ := by
      simp only [expSeq]
      congr 2
      omega
    rcases r with _ | r
    · rfl
    · change (liftKraus k (K' _)).op (expSeq ρ i r) _ _ = _
      rw [he, heρ]
      refine hl ⟨i, by omega⟩ r _ _ {v | v ∈ S ∧ v ∈ G ⟨i, by omega⟩}
        {v | v ∈ S ∧ v ∈ prevSeq (expSeq G) G₀ (((⟨i, by omega⟩ : Fin (t + 1))) : ℕ)}
        (h ⟨i, by omega⟩) a b ?_ hb
      have := ha
      simp only [Set.mem_ofPred_eq, heG] at this
      exact this
  · -- `A`'s last step, followed by the expansion's first classical step
    have he : expSeq τ i = τ (Fin.last t) := by
      simp only [expSeq, Fin.last]
      congr 2
      omega
    have heG : expSeq G i = G (Fin.last t) := by
      simp only [expSeq, Fin.last]
      congr 2
      omega
    have hp : prevSeq (expSeq τ) τ₀ i =
        prevSeq (expSeq τ) τ₀ ((Fin.last t : Fin (t + 1)) : ℕ) := by
      simp only [Fin.val_last, h2]
    have hpG : prevSeq (expSeq G) G₀ i =
        prevSeq (expSeq G) G₀ ((Fin.last t : Fin (t + 1)) : ℕ) := by
      simp only [Fin.val_last, h2]
    have heρ : expSeq ρ i = ρ (Fin.last t) := by
      simp only [expSeq, Fin.last]
      congr 2
      omega
    rcases r with _ | r
    · rfl
    · change (liftKraus k (K' _)).op (expSeq ρ i r)
        ((expPerm e E k o 0).symm (expBasisPerm k (expSeq τ i) a))
        (expBasisPerm k (prevSeq (expSeq τ) τ₀ i) b) =
          (liftKraus k (K _)).op r ((expPerm e E k o 0).symm a) b
      rw [he, heρ, expPerm_symm_expBasisPerm_of_next e E k hE 0, hp]
      refine hl _ r _ _ {v | v ∈ S ∧ v ∈ G (Fin.last t)}
        {v | v ∈ S ∧ v ∈ prevSeq (expSeq G) G₀ ((Fin.last t : Fin (t + 1)) : ℕ)} (h (Fin.last t))
        _ b ?_ ?_
      · show ((expPerm e E k o 0).symm a).1.1 ∈ {v | v ∈ S ∧ v ∈ G (Fin.last t)}
        rw [expPerm_symm_fst_fst]
        have := ha
        simp only [Set.mem_ofPred_eq, heG] at this
        exact this
      · have := hb
        simp only [Set.mem_ofPred_eq, hpG] at this
        exact this
  · -- the expansion's classical steps
    have he : expSeq τ i = τ (Fin.last t) := by
      simp only [expSeq, Fin.last]
      congr 2
      omega
    have hp : prevSeq (expSeq τ) τ₀ i = τ (Fin.last t) := by
      have hi0 : (i : ℕ) ≠ 0 := by omega
      simp only [prevSeq, hi0, ↓reduceIte, expSeq, Fin.last]
      congr 2
      omega
    rcases r with _ | r
    · change (1 : Matrix _ _ ℂ) ((expPerm e E k o (i - t)).symm (expBasisPerm k (expSeq τ i) a))
        (expBasisPerm k (prevSeq (expSeq τ) τ₀ i) b) =
          (1 : Matrix _ _ ℂ) ((expPerm e E k o (i - t)).symm a) b
      rw [he, hp]
      simp only [expPerm_symm_expBasisPerm_of_next e E k hE, Matrix.one_apply,
        (expBasisPerm k (τ (Fin.last t))).injective.eq_iff]
    · rfl

/-- **The expanded Kraus maps move through the expanded sets**: Kraus maps whose step `i` maps the
basis states with work register in the set before it into `G i` give expanded Kraus maps that do
the same for `expSeq G`. -/
theorem keepsSet_expKraus {t : ℕ} (G : Fin (t + 1) → Set V) (G₀ : Set V)
    {K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ (i : Fin (t + 1)) k', KeepsSet
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ G i} ((K i).op k'))
    (o : V → C) (i : Fin (t + k + 1)) (k' : Option R) :
    KeepsSet {b : ExpBasis (X := Bits m) (Y := BitStr I J) k V | b.1.1 ∈ prevSeq (expSeq G) G₀ i}
      {b : ExpBasis (X := Bits m) (Y := BitStr I J) k V | b.1.1 ∈ expSeq G i}
      ((expKraus e E k K o i).op k') := by
  have hl : ∀ (j : Fin (t + 1)) r (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V),
      b.1.1 ∈ prevSeq (expSeq G) G₀ j → (liftKraus k (K j)).op r a b ≠ 0 → a.1.1 ∈ G j :=
    fun j r a b hb hne => by
      change ((K j).op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V a) (registerSplit k V b) ≠ 0
        at hne
      rw [Matrix.kroneckerMap_apply] at hne
      exact h j r _ _ hb (left_ne_zero_of_mul hne)
  intro a b hb hne
  unfold expKraus at hne
  split_ifs at hne with h1 h2
  · rcases k' with _ | r
    · exact absurd rfl hne
    · have he : expSeq G i = G ⟨i, by omega⟩ := by
        simp only [expSeq]
        congr 2
        omega
      show a.1.1 ∈ expSeq G i
      rw [he]
      exact hl _ r a b hb hne
  · rcases k' with _ | r
    · exact absurd rfl hne
    · have he : expSeq G i = G (Fin.last t) := by
        simp only [expSeq, Fin.last]
        congr 2
        omega
      have hp : prevSeq (expSeq G) G₀ i = prevSeq (expSeq G) G₀ ((Fin.last t : Fin (t + 1)) : ℕ) :=
        by simp only [Fin.val_last, h2]
      show a.1.1 ∈ expSeq G i
      rw [he, ← expPerm_symm_fst_fst e E k o 0 a]
      exact hl _ r _ b (hp ▸ hb) hne
  · rcases k' with _ | r
    · have he : expSeq G i = G (Fin.last t) := by
        simp only [expSeq, Fin.last]
        congr 2
        omega
      have hp : prevSeq (expSeq G) G₀ i = G (Fin.last t) := by
        have hi0 : (i : ℕ) ≠ 0 := by omega
        simp only [prevSeq, hi0, ↓reduceIte, expSeq, Fin.last]
        congr 2
        omega
      change (1 : Matrix _ _ ℂ) ((expPerm e E k o (i - t)).symm a) b ≠ 0 at hne
      rw [Matrix.one_apply] at hne
      have hab : (expPerm e E k o (i - t)).symm a = b := by
        by_contra hc
        exact hne (by simp [hc])
      show a.1.1 ∈ expSeq G i
      rw [he, ← expPerm_symm_fst_fst e E k o (i - t) a, hab, ← hp]
      exact hb
    · exact absurd rfl hne

/-- **The expanded Kraus maps keep the blocks on the expanded sets** (`keepsSet_expKraus` for the
blocks of a label). -/
theorem keepsBlocksOn_expKraus {L : Type} {t : ℕ} (ℓ : V → Option L) (G₀ : Set V)
    (G : Fin (t + 1) → Set V)
    {K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ (i : Fin (t + 1)) k', KeepsBlocksOn
      {p : QueryReg V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
      (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K i).op k'))
    (o : V → C) (i : Fin (t + k + 1)) (k' : Option R) :
    KeepsBlocksOn {b : ExpBasis (X := Bits m) (Y := BitStr I J) k V |
        b.1.1 ∈ prevSeq (expSeq G) G₀ i}
      (fun b : ExpBasis (X := Bits m) (Y := BitStr I J) k V => ℓ b.1.1)
      ((expKraus e E k K o i).op k') := by
  have hl : ∀ (j : Fin (t + 1)) r (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V) r',
      b.1.1 ∈ prevSeq (expSeq G) G₀ j → ℓ b.1.1 = some r' → (liftKraus k (K j)).op r a b ≠ 0 →
      ℓ a.1.1 = some r' :=
    fun j r a b r' hbG hb hne => by
      change ((K j).op r ⊗ₖ (1 : Matrix _ _ ℂ)) (registerSplit k V a) (registerSplit k V b) ≠ 0
        at hne
      rw [Matrix.kroneckerMap_apply] at hne
      exact h j r r' _ _ hbG hb (left_ne_zero_of_mul hne)
  intro r' a b hbG hb hne
  unfold expKraus at hne
  split_ifs at hne with h1 h2
  · rcases k' with _ | r
    · exact absurd rfl hne
    · exact hl ⟨i, by omega⟩ r a b r' hbG hb hne
  · rcases k' with _ | r
    · exact absurd rfl hne
    · have hp : prevSeq (expSeq G) G₀ i = prevSeq (expSeq G) G₀ ((Fin.last t : Fin (t + 1)) : ℕ) :=
        by simp only [Fin.val_last, h2]
      show ℓ a.1.1 = some r'
      rw [← expPerm_symm_fst_fst e E k o 0 a]
      exact hl _ r _ b r' (hp ▸ hbG) hb hne
  · rcases k' with _ | r
    · change (1 : Matrix _ _ ℂ) ((expPerm e E k o (i - t)).symm a) b ≠ 0 at hne
      rw [Matrix.one_apply] at hne
      have hab : (expPerm e E k o (i - t)).symm a = b := by
        by_contra hc
        exact hne (by simp [hc])
      show ℓ a.1.1 = some r'
      rw [← expPerm_symm_fst_fst e E k o (i - t) a, hab]
      exact hb
    · exact absurd rfl hne

end ExpLift

/-! ### Trace preservation of the constructions -/

section TP

variable {R ι κ : Type*} [Fintype R] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem KrausMap.tp_permConj {K : KrausMap R ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1)
    (σ τ : Equiv.Perm ι) : ∑ r, ((K.permConj σ τ).op r)ᴴ * (K.permConj σ τ).op r = 1 := by
  have h' : ∑ r, ((K.permConj σ τ).op r)ᴴ * (K.permConj σ τ).op r =
      (∑ r, (K.op r)ᴴ * K.op r).submatrix σ σ := by
    simp only [KrausMap.permConj]
    rw [submatrix_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [conjTranspose_submatrix, submatrix_mul_equiv]
  rw [h', h, submatrix_one_equiv]

theorem KrausMap.tp_optionSome {K : KrausMap R ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1) :
    ∑ r, (K.optionSome.op r)ᴴ * K.optionSome.op r = 1 := by
  simpa [KrausMap.optionSome, Fintype.sum_option] using h

theorem KrausMap.tp_optionNone {K : KrausMap Unit ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1) :
    ∑ r, ((K.optionNone R).op r)ᴴ * (K.optionNone R).op r = 1 := by
  simpa [KrausMap.optionNone, Fintype.sum_option] using h

theorem KrausMap.tp_relabel {K : KrausMap R ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1) (f : ι ≃ κ) :
    ∑ r, ((K.relabel f).op r)ᴴ * (K.relabel f).op r = 1 := by
  have h' : ∑ r, ((K.relabel f).op r)ᴴ * (K.relabel f).op r =
      (∑ r, (K.op r)ᴴ * K.op r).submatrix f.symm f.symm := by
    simp only [KrausMap.relabel]
    rw [submatrix_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [conjTranspose_submatrix, submatrix_mul_equiv]
  rw [h', h, submatrix_one_equiv]

theorem KrausMap.tp_tensorId {K : KrausMap R ι ι} (h : ∑ r, (K.op r)ᴴ * K.op r = 1)
    (A : Type*) [Fintype A] [DecidableEq A] :
    ∑ r, ((K.tensorId A).op r)ᴴ * (K.tensorId A).op r = 1 := by
  simp only [KrausMap.tensorId]
  have h' : ∑ r, (K.op r ⊗ₖ (1 : Matrix A A ℂ))ᴴ * (K.op r ⊗ₖ (1 : Matrix A A ℂ)) =
      (∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ (1 : Matrix A A ℂ) := by
    rw [Matrix.sum_kronecker]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  rw [h', h, Matrix.one_kronecker_one]

end TP

section TPExp

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R]

theorem tp_liftKraus {K : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))} (h : ∑ r, (K.op r)ᴴ * K.op r = 1) :
    ∑ r, ((liftKraus k K).op r)ᴴ * (liftKraus k K).op r = 1 :=
  KrausMap.tp_relabel (KrausMap.tp_tensorId h _) _

/-- **The expanded Kraus maps of trace-preserving maps are trace preserving.** -/
theorem tp_expKraus {t : ℕ} {K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))} (h : ∀ i, ∑ r, ((K i).op r)ᴴ * (K i).op r = 1)
    (o : V → C) (i : Fin (t + k + 1)) :
    ∑ r, ((expKraus e E k K o i).op r)ᴴ * (expKraus e E k K o i).op r = 1 := by
  unfold expKraus
  split_ifs
  · exact KrausMap.tp_optionSome (tp_liftKraus k (h _))
  · exact KrausMap.tp_optionSome (KrausMap.tp_permConj (tp_liftKraus k (h _)) _ _)
  · exact KrausMap.tp_optionNone (KrausMap.tp_permConj (by simp [KrausMap.identity]) _ _)

end TPExp

/-! ### The expanded coherent run on a block -/

section Law

open Classical in
/-- **The expanded coherent runs on a block** (`densityRun_relabel_block` read through
`simLaw_expandCoh_eq`): for a trace-preserving core algorithm `A` and the same algorithm with the
Kraus maps `K'` and the initial state `ρ'` (trace preserving too), sets `G i` and `G' i` of work
registers (after step `i`; `G₀`, `G₀'` of the initial state) through which `A`'s and the other
Kraus maps move (`hG`, `hG'`) and on which the initial states are supported (`hρs`, `hρs'`), a
label `ℓ` whose blocks both families keep on the columns in their set before their step (`hK`,
`hK'`), permutations `τ i` (after step `i`) and `τ₀` keeping `ℓ` and mapping the block of `G i`
onto that of `G' i`,
along which the Kraus maps (`hop`, rows in `G i` along `τ i`, columns in the set before along the
previous permutation, operators along `ρ i`) and the initial states (`hρ`)
agree on the basis states with label `none` or `some r`, and an expansion whose queries do not see
the last permutation (`hE`), every event `S` of the outcome that implies label `some r` (`hS`) and
that the last permutation keeps (`hSτ`) has the same probability. -/
theorem simLaw_expandCoh_relabel_block {O L : Type} (A : Alg (Bits m) (BitStr I J) O)
    (hA : A.TracePreserving)
    (K' : Fin (A.depth + 1) → KrausMap A.R (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (ρ' : MState (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (hA' : ({ A with step := K', init := ρ' } : Alg (Bits m) (BitStr I J) O).TracePreserving)
    (g : Option O → C) (ℓ : A.V → Option L) (G G' : Fin (A.depth + 1) → Set A.V)
    (G₀ G₀' : Set A.V) (τ : Fin (A.depth + 1) → Equiv.Perm A.V) (τ₀ : Equiv.Perm A.V)
    (hτ : ∀ i v, ℓ (τ i v) = ℓ v) (hτ₀ : ∀ v, ℓ (τ₀ v) = ℓ v) (r : L)
    (hτG : ∀ i v, InBlock ℓ r v → (τ i v ∈ G' i ↔ v ∈ G i))
    (hτ₀G : ∀ v, InBlock ℓ r v → (τ₀ v ∈ G₀' ↔ v ∈ G₀))
    (hG : ∀ (i : Fin (A.depth + 1)) k', KeepsSet
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ G i} ((A.step i).op k'))
    (hG' : ∀ (i : Fin (A.depth + 1)) k', KeepsSet
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G') G₀' i}
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ G' i} ((K' i).op k'))
    (ρ : Fin (A.depth + 1) → Equiv.Perm A.R)
    (hop : ∀ i : Fin (A.depth + 1), OpRelIdx (ρ i) (queryWorkPerm (τ i))
      (queryWorkPerm (prevSeq (expSeq τ) τ₀ i)) {p | InBlock ℓ r p.1 ∧ p.1 ∈ G i}
      {p | InBlock ℓ r p.1 ∧ p.1 ∈ prevSeq (expSeq G) G₀ i} (A.step i) (K' i))
    (hK : ∀ (i : Fin (A.depth + 1)) k', KeepsBlocksOn
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
      (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) ((A.step i).op k'))
    (hK' : ∀ (i : Fin (A.depth + 1)) k', KeepsBlocksOn
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G') G₀' i}
      (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K' i).op k'))
    (hρs : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (hρs' : ∀ a b, ρ'.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀')
    (hρ : ∀ a b : QueryReg A.V 1 (Bits m) (BitStr I J), a.1 ∈ G₀ → b.1 ∈ G₀ → InBlock ℓ r a.1 →
      InBlock ℓ r b.1 → ρ'.mat (queryWorkPerm τ₀ a) (queryWorkPerm τ₀ b) = A.init.mat a b)
    (hE : ∀ v, E.next (g (some (A.out (τ (Fin.last _) v)))) = E.next (g (some (A.out v))))
    (S : Set (BaseGame.Tuple (Bits m) B C k × DB (Bits m) B))
    (hS : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) I J m
        (A.depth + k),
      (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S → ℓ y.1.1.1 = some r)
    (hSτ : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) I J m
        (A.depth + k),
      (expOut e E k (fun v => g (some (A.out v))) (expWorkPerm k (τ (Fin.last _)) y.1.1),
        slotsDB e y.2) ∈ S ↔
        (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S) :
    simLaw e (expandAdv e E k (({ A with step := K', init := ρ' } : Alg (Bits m) (BitStr I J) O
      ).toQueryAlgCoh.mapOut g)) S = simLaw e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) S := by
  rw [simLaw_expandCoh_eq e E k _ hA' g S, simLaw_expandCoh_eq e E k A hA g S]
  -- the permutations and sets of the expanded run
  set τr : ℕ → Equiv.Perm (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) :=
    fun n => expWorkPerm k (expSeq τ n) with hτr
  set Gr : ℕ → Set (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) :=
    fun n => {w | w.1 ∈ expSeq G n} with hGr
  set Gr₀ : Set (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) := {w | w.1 ∈ G₀}
  have hprevGr : ∀ n, prevSeq Gr Gr₀ n = {w | w.1 ∈ prevSeq (expSeq G) G₀ n} := fun n => by
    simp only [prevSeq]
    split_ifs <;> rfl
  set Gr' : ℕ → Set (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) :=
    fun n => {w | w.1 ∈ expSeq G' n} with hGr'
  set Gr₀' : Set (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) := {w | w.1 ∈ G₀'}
  have hprevGr' : ∀ n, prevSeq Gr' Gr₀' n = {w | w.1 ∈ prevSeq (expSeq G') G₀' n} := fun n => by
    simp only [prevSeq]
    split_ifs <;> rfl
  have hprevτr : ∀ n, prevSeq τr (expWorkPerm k τ₀) n = expWorkPerm k (prevSeq (expSeq τ) τ₀ n) :=
    fun n => by
      simp only [prevSeq]
      split_ifs <;> rfl
  have hlast : τr (A.depth + k) = expWorkPerm k (τ (Fin.last _)) := by
    simp only [hτr, expSeq_of_le τ (Nat.le_add_right A.depth k)]
  have hlastG : Gr (A.depth + k) = {w | w.1 ∈ G (Fin.last _)} := by
    simp only [hGr, expSeq_of_le G (Nat.le_add_right A.depth k)]
  have hlastG' : Gr' (A.depth + k) = {w | w.1 ∈ G' (Fin.last _)} := by
    simp only [hGr', expSeq_of_le G' (Nat.le_add_right A.depth k)]
  set π := simWorkPerm (I := I) (J := J) (m := m) (t := A.depth + k) (τr (A.depth + k))
  rw [← Equiv.sum_comp π]
  have hrho : ∀ (S₀ : Set A.V) (ρ : MState (QueryReg A.V 1 (Bits m) (BitStr I J))),
      (∀ a b, ρ.mat a b ≠ 0 → a.1 ∈ S₀ ∧ b.1 ∈ S₀) →
      ∀ a b, ((ρ.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
        (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V) :
          Matrix (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V)
            (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V) ℂ) a b ≠ 0 →
        a.1.1 ∈ S₀ ∧ b.1.1 ∈ S₀ := fun S₀ ρ hρ a b h => by
    simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
    exact hρ _ _ (left_ne_zero_of_mul h)
  have hrel := densityRun_relabel_block e (fun w : ExpansionRegister (X := Bits m)
      (Y := BitStr I J) k A.V => ℓ w.1) Gr Gr' Gr₀ Gr₀' τr (expWorkPerm k τ₀) (fun n w => hτ _ w.1)
    (fun w => hτ₀ w.1) r (fun n w hw => hτG _ w.1 hw) (fun w hw => hτ₀G w.1 hw)
    (fun n hn => by
      simp only [hGr, expSeq_eq_pred G (show A.depth < n by omega)])
    (fun n hn => by
      simp only [hGr', expSeq_eq_pred G' (show A.depth < n by omega)])
    (fun n hn => by
      simp only [hτr, expSeq_eq_pred τ (show A.depth < n by omega)])
    (expKraus e E k A.step fun v => g (some (A.out v)))
    (expKraus e E k K' fun v => g (some (A.out v)))
    (fun i k' => by
      rw [hprevGr]
      exact keepsSet_expKraus e E k G G₀ hG _ i k')
    (fun i k' => by
      rw [hprevGr']
      exact keepsSet_expKraus e E k G' G₀' hG' _ i k')
    (fun i => Equiv.optionCongr (expSeq ρ i))
    (fun i k' a b haG hbG ha hb => by
      rw [hprevτr]
      rw [hprevGr] at hbG
      exact opRelIdx_expKraus_of_next e E k {v | InBlock ℓ r v} G G₀ τ τ₀ ρ
        (fun i => hop i) (o := fun v => g (some (A.out v))) hE i k' a b ⟨ha, haG⟩ ⟨hb, hbG⟩)
    (fun i k' => by
      rw [hprevGr]
      exact keepsBlocksOn_expKraus e E k ℓ G₀ G hK _ i k')
    (fun i k' => by
      rw [hprevGr']
      exact keepsBlocksOn_expKraus e E k ℓ G₀' G' hK' _ i k')
    ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
      (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V))
    ((ρ'.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
      (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V))
    (hrho G₀ A.init hρs) (hrho G₀' ρ' hρs')
    (fun a b haG hbG ha hb => by
      simp only [Matrix.submatrix_apply]
      rw [show (expWorkPerm k τ₀).prodCongr (Equiv.refl _) = expBasisPerm k τ₀ from rfl,
        registerSplit_expBasisPerm, registerSplit_expBasisPerm, Matrix.kroneckerMap_apply,
        Matrix.kroneckerMap_apply,
        hρ (registerSplit k A.V a).1 (registerSplit k A.V b).1 haG hbG ha hb])
    (A.depth + k)
  have hsupp := densityRun_supported e Gr Gr₀
    (fun n hn => by
      simp only [hGr, expSeq_eq_pred G (show A.depth < n by omega)])
    (expKraus e E k A.step fun v => g (some (A.out v)))
    (fun i k' => by
      rw [hprevGr]
      exact keepsSet_expKraus e E k G G₀ hG _ i k') _ (hrho G₀ A.init hρs) (A.depth + k)
  have hsupp' := densityRun_supported e Gr' Gr₀'
    (fun n hn => by
      simp only [hGr', expSeq_eq_pred G' (show A.depth < n by omega)])
    (expKraus e E k K' fun v => g (some (A.out v)))
    (fun i k' => by
      rw [hprevGr']
      exact keepsSet_expKraus e E k G' G₀' hG' _ i k') _ (hrho G₀' ρ' hρs') (A.depth + k)
  refine Finset.sum_congr rfl fun y _ => ?_
  have hπy : (π y).1.1 = expWorkPerm k (τ (Fin.last _)) y.1.1 := by
    simp only [π, simWorkPerm_apply, hlast]
  by_cases hy : (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S
  · have hy' := (hSτ y).2 hy
    have hb : InBlock (fun w : ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V => ℓ w.1)
        r y.1.1 := Or.inr (hS y hy)
    have hy'' : (expOut e E k (fun v => g (some (A.out v))) (π y).1.1, slotsDB e (π y).2) ∈ S := by
      rw [hπy]
      exact hy'
    simp only [hy, hy'', ite_true]
    by_cases hyG : y.1.1 ∈ Gr (A.depth + k)
    · rw [hrel y y hyG hyG hb hb]
    · have h1 : densityRun e (expKraus e E k A.step fun v => g (some (A.out v)))
          ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
            (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) (A.depth + k) y y = 0 :=
        by_contra fun h => hyG (hsupp y y h).1
      have hiff : (π y).1.1 ∈ Gr' (A.depth + k) ↔ y.1.1 ∈ Gr (A.depth + k) := by
        rw [hlastG', hlastG, hπy]
        exact hτG (Fin.last _) y.1.1.1 hb
      have hπG : ¬ (π y).1.1 ∈ Gr' (A.depth + k) := fun h => hyG (hiff.1 h)
      have h2 : densityRun e (expKraus e E k K' fun v => g (some (A.out v)))
          ((ρ'.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
            (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) (A.depth + k)
            (π y) (π y) = 0 :=
        by_contra fun h => hπG (hsupp' _ _ h).1
      rw [h1, h2]
  · have hy' : ¬ (expOut e E k (fun v => g (some (A.out v))) (π y).1.1, slotsDB e (π y).2) ∈ S :=
      fun h => hy ((hSτ y).1 (by rw [← hπy]; exact h))
    simp only [hy, hy', ite_false, zero_mul]

end Law

/-! ### The masses of the blocks of the expanded coherent run -/

section MassLaw

/-- **A diagonal unit matrix is positive semidefinite.** -/
theorem posSemidef_single_one {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι) :
    (Matrix.single d d (1 : ℂ)).PosSemidef := by
  have : Matrix.single d d (1 : ℂ) = Matrix.diagonal (Pi.single d 1) := by
    ext a b
    simp only [Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply]
    by_cases ha : a = d <;> by_cases hb : b = d <;> simp_all [eq_comm]
  rw [this]
  exact Matrix.PosSemidef.diagonal fun i => by by_cases hi : i = d <;> simp [hi]

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] {t : ℕ}

/-- **The density-matrix run of a positive semidefinite initial state is positive
semidefinite.** -/
theorem densityRun_posSemidef
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    {ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ}
    (hρ : ρ₀.PosSemidef) : ∀ n, (densityRun e K ρ₀ n).PosSemidef := by
  have hs := posSemidef_single_one (dbSlots e t (∅ : DB (Bits m) B))
  intro n
  induction n with
  | zero =>
    exact KrausMap.posSemidef_stepAt _ 0 (hρ.kronecker hs)
  | succ n ih =>
    exact KrausMap.posSemidef_stepAt _ (n + 1) (ih.mul_mul_conjTranspose_same _)

end MassLaw

section MassAlg

/-- **Expanded Kraus maps agreeing on a set of columns**: Kraus maps that agree on the columns whose
work register satisfies `P` give expanded Kraus maps that agree on those columns. -/
theorem expKraus_op_congr_col {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] {t : ℕ}
    (P : V → Prop) {K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ i k' (a b : QueryReg V 1 (Bits m) (BitStr I J)), P b.1 →
      (K' i).op k' a b = (K i).op k' a b) (o : V → C) (i : Fin (t + k + 1)) :
    ∀ k' (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V), P b.1.1 →
      (expKraus e E k K' o i).op k' a b = (expKraus e E k K o i).op k' a b := by
  intro k' a b hb
  have hl : ∀ j r (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V), P b.1.1 →
      (liftKraus k (K' j)).op r a b = (liftKraus k (K j)).op r a b := fun j r a b hb => by
    simp only [liftKraus, KrausMap.relabel, KrausMap.tensorId, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply]
    rw [h j r _ _ hb]
  unfold expKraus
  split_ifs with h1 h2
  · rcases k' with _ | r
    · rfl
    · exact hl _ r a b hb
  · rcases k' with _ | r
    · rfl
    · exact hl _ r _ b hb
  · rfl


/-- **Expanded Kraus maps agreeing on a set of rows**: Kraus maps whose step `i` agree on the rows
whose work register satisfies `P i` give expanded Kraus maps that agree on the rows satisfying
`expSeq P`. -/
theorem expKraus_op_congr_row {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] {t : ℕ}
    (P : Fin (t + 1) → V → Prop)
    {K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ i k' (a b : QueryReg V 1 (Bits m) (BitStr I J)), P i a.1 →
      (K' i).op k' a b = (K i).op k' a b) (o : V → C) (i : Fin (t + k + 1)) :
    ∀ k' (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V), expSeq P i a.1.1 →
      (expKraus e E k K' o i).op k' a b = (expKraus e E k K o i).op k' a b := by
  intro k' a b ha
  have hl : ∀ j r (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V), P j a.1.1 →
      (liftKraus k (K' j)).op r a b = (liftKraus k (K j)).op r a b := fun j r a b ha => by
    simp only [liftKraus, KrausMap.relabel, KrausMap.tensorId, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply]
    rw [h j r _ _ ha]
  unfold expKraus
  split_ifs with h1 h2
  · rcases k' with _ | r
    · rfl
    · refine hl _ r a b ?_
      have he : expSeq P i = P ⟨i, by omega⟩ := by
        simp only [expSeq]
        congr 2
        omega
      rw [he] at ha
      exact ha
  · rcases k' with _ | r
    · rfl
    · refine hl (Fin.last t) r _ b ?_
      show P (Fin.last t) ((expPerm e E k o 0).symm a).1.1
      rw [expPerm_symm_fst_fst, ← expSeq_of_le P (by omega : t ≤ (i : ℕ))]
      exact ha
  · rfl

/-- **Expanded Kraus maps agreeing on a set of rows and columns**: Kraus maps whose step `i` agree
on the rows whose work register satisfies `P i` and the columns whose work register satisfies
`Pc i` give expanded Kraus maps that agree on the rows satisfying `expSeq P` and the columns
satisfying `Pc`. -/
theorem expKraus_op_congr_rc {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] {t : ℕ}
    (P : Fin (t + 1) → V → Prop) (Pc : ℕ → V → Prop)
    {K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : ∀ i k' (a b : QueryReg V 1 (Bits m) (BitStr I J)), P i a.1 → Pc i b.1 →
      (K' i).op k' a b = (K i).op k' a b) (o : V → C) (i : Fin (t + k + 1)) :
    ∀ k' (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V), expSeq P i a.1.1 → Pc i b.1.1 →
      (expKraus e E k K' o i).op k' a b = (expKraus e E k K o i).op k' a b := by
  intro k' a b ha hb
  have hl : ∀ j r (a b : ExpBasis (X := Bits m) (Y := BitStr I J) k V), P j a.1.1 →
      Pc j b.1.1 → (liftKraus k (K' j)).op r a b = (liftKraus k (K j)).op r a b :=
    fun j r a b ha hb => by
    simp only [liftKraus, KrausMap.relabel, KrausMap.tensorId, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply]
    rw [h j r _ _ ha hb]
  unfold expKraus
  split_ifs with h1 h2
  · rcases k' with _ | r
    · rfl
    · refine hl _ r a b ?_ hb
      have he : expSeq P i = P ⟨i, by omega⟩ := by
        simp only [expSeq]
        congr 2
        omega
      rw [he] at ha
      exact ha
  · rcases k' with _ | r
    · rfl
    · refine hl (Fin.last t) r _ b ?_ ?_
      · show P (Fin.last t) ((expPerm e E k o 0).symm a).1.1
        rw [expPerm_symm_fst_fst, ← expSeq_of_le P (by omega : t ≤ (i : ℕ))]
        exact ha
      · show Pc t b.1.1
        rw [← h2]
        exact hb
  · rfl

/-- **The overlaps of the rows of block `r` from two columns** under a Kraus map. -/
noncomputable def rowGram {ι R L : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq L]
    (ℓ : ι → Option L) (r : L) (K : KrausMap R ι ι) (c d : ι) : ℂ :=
  ∑ k', ∑ a ∈ Finset.univ.filter (fun a => ℓ a = some r), K.op k' a c * star (K.op k' a d)

/-- **Expanded Kraus maps with the same overlaps into the blocks**: Kraus maps whose rows of every
block have the same overlaps from two columns with label `none` give expanded Kraus maps with the
same overlaps. -/
theorem expKraus_rowGram_congr {V R L : Type} [Fintype V] [DecidableEq V] [Fintype R]
    [DecidableEq L] {t : ℕ} (ℓ : V → Option L) (r : L)
    {K K' : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (Q : Fin (t + 1) → V → Prop)
    (h : ∀ i (c d : QueryReg V 1 (Bits m) (BitStr I J)), Q i c.1 → Q i d.1 →
      rowGram (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) r (K' i) c d =
        rowGram (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) r (K i) c d)
    (o : V → C) (i : Fin (t + k + 1)) (c d : ExpBasis (X := Bits m) (Y := BitStr I J) k V)
    (hcd : ∀ hi : (i : ℕ) ≤ t, Q ⟨i, by omega⟩ c.1.1 ∧ Q ⟨i, by omega⟩ d.1.1) :
    rowGram (fun p : ExpBasis (X := Bits m) (Y := BitStr I J) k V => ℓ p.1.1) r
        (expKraus e E k K' o i) c d =
      rowGram (fun p : ExpBasis (X := Bits m) (Y := BitStr I J) k V => ℓ p.1.1) r
        (expKraus e E k K o i) c d := by
  -- the overlaps of a lifted map, through the split of the expansion's registers
  have hlift : ∀ (Kj : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))) (c d : ExpBasis (X := Bits m) (Y := BitStr I J) k V),
      rowGram (fun p : ExpBasis (X := Bits m) (Y := BitStr I J) k V => ℓ p.1.1) r
          (liftKraus k Kj) c d =
        (if (registerSplit k V c).2 = (registerSplit k V d).2 then 1 else 0) *
          rowGram (fun p : QueryReg V 1 (Bits m) (BitStr I J) => ℓ p.1) r Kj
            (registerSplit k V c).1 (registerSplit k V d).1 := fun Kj c d => by
    rw [rowGram, rowGram, ← sum_filter_kron_one (ℓ := fun p : QueryReg V 1 (Bits m)
      (BitStr I J) => ℓ p.1)]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp (registerSplit k V).symm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [liftKraus, KrausMap.relabel, KrausMap.tensorId, Matrix.submatrix_apply,
      Equiv.symm_symm, Equiv.apply_symm_apply]
    rfl
  -- the overlaps after a permutation of the rows keeping the work register
  have hperm : ∀ (K₀ : KrausMap R (ExpBasis (X := Bits m) (Y := BitStr I J) k V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k V)) (τ : Equiv.Perm (ExpBasis (X := Bits m)
        (Y := BitStr I J) k V)), (∀ b, (τ b).1.1 = b.1.1) →
      rowGram (fun p : ExpBasis (X := Bits m) (Y := BitStr I J) k V => ℓ p.1.1) r
          (K₀.permConj 1 τ) c d =
        rowGram (fun p : ExpBasis (X := Bits m) (Y := BitStr I J) k V => ℓ p.1.1) r K₀ c d :=
    fun K₀ τ hτ => by
      simp only [rowGram, KrausMap.permConj, Matrix.submatrix_apply, Equiv.Perm.coe_one, id]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp τ]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Equiv.symm_apply_apply, hτ]
  have hsome : ∀ (K₀ : KrausMap R (ExpBasis (X := Bits m) (Y := BitStr I J) k V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k V)),
      rowGram (fun p : ExpBasis (X := Bits m) (Y := BitStr I J) k V => ℓ p.1.1) r
          K₀.optionSome c d =
        rowGram (fun p : ExpBasis (X := Bits m) (Y := BitStr I J) k V => ℓ p.1.1) r K₀ c d :=
    fun K₀ => by
      simp only [rowGram, KrausMap.optionSome, Fintype.sum_option, Option.elim]
      simp
  unfold expKraus
  split_ifs with h1 h2
  · obtain ⟨hc, hd⟩ := hcd (by omega)
    rw [hsome, hsome, hlift, hlift, h _ _ _ hc hd]
  · obtain ⟨hc, hd⟩ := hcd (by omega)
    have hl : (⟨i, by omega⟩ : Fin (t + 1)) = Fin.last t := Fin.ext h2
    rw [hl] at hc hd
    rw [hsome, hsome, hperm _ _ (expPerm_fst_fst e E k o 0), hperm _ _ (expPerm_fst_fst e E k o 0),
      hlift, hlift, h _ _ _ hc hd]
  · rfl

open Classical in
/-- **The expanded coherent runs give every block the same probability**
(`densityRun_block_mass` read through `simLaw_expandCoh_eq`): for a trace-preserving core
algorithm `A` and the same algorithm with the trace-preserving Kraus maps `K'`, sets `G i` and
`G' i` (after step `i`; `G₀`, `G₀'` of the initial state, which is supported on both) with the
same states of label `none` (`hnone`, `hnone₀`) through which `A`'s and the other Kraus maps move
(`hG`, `hG'`), a label `ℓ` whose blocks both keep on the columns in their set before their step
(`hK`, `hK'`), Kraus maps agreeing on the rows in `G i` with label `none` from the columns in the
set before with label `none` (`hrow`) whose rows of every block have the same overlaps from the
columns in the set before with label `none` (`hgram`), and an event `S` of the outcome that holds
exactly on the basis states with label `some r` (`hS`), the two runs give `S` the same
probability. -/
theorem simLaw_expandCoh_block_mass {O L : Type} [DecidableEq L] (A : Alg (Bits m) (BitStr I J) O)
    (hA : A.TracePreserving)
    (K' : Fin (A.depth + 1) → KrausMap A.R (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (hA' : ({ A with step := K' } : Alg (Bits m) (BitStr I J) O).TracePreserving)
    (g : Option O → C) (ℓ : A.V → Option L) (G G' : Fin (A.depth + 1) → Set A.V)
    (G₀ G₀' : Set A.V) (r : L) (hnone : ∀ i v, ℓ v = none → (v ∈ G' i ↔ v ∈ G i))
    (hnone₀ : ∀ v, ℓ v = none → (v ∈ G₀' ↔ v ∈ G₀))
    (hG : ∀ (i : Fin (A.depth + 1)) k', KeepsSet
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ G i} ((A.step i).op k'))
    (hG' : ∀ (i : Fin (A.depth + 1)) k', KeepsSet
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G') G₀' i}
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ G' i} ((K' i).op k'))
    (hK : ∀ (i : Fin (A.depth + 1)) k', KeepsBlocksOn
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
      (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) ((A.step i).op k'))
    (hK' : ∀ (i : Fin (A.depth + 1)) k', KeepsBlocksOn
      {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G') G₀' i}
      (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K' i).op k'))
    (hrow : ∀ (i : Fin (A.depth + 1)) k' (a b : QueryReg A.V 1 (Bits m) (BitStr I J)),
      a.1 ∈ G i → b.1 ∈ prevSeq (expSeq G) G₀ i → ℓ a.1 = none → ℓ b.1 = none →
        (K' i).op k' a b = (A.step i).op k' a b)
    (hgram : ∀ (i : Fin (A.depth + 1)) r' (c d : QueryReg A.V 1 (Bits m) (BitStr I J)),
      c.1 ∈ prevSeq (expSeq G) G₀ i → d.1 ∈ prevSeq (expSeq G) G₀ i → ℓ c.1 = none →
      ℓ d.1 = none →
      rowGram (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) r' (K' i) c d =
        rowGram (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) r' (A.step i) c d)
    (hρs : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (hρs' : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀')
    (S : Set (BaseGame.Tuple (Bits m) B C k × DB (Bits m) B))
    (hS : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) I J m
        (A.depth + k),
      (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S ↔ ℓ y.1.1.1 = some r) :
    simLaw e (expandAdv e E k (({ A with step := K' } : Alg (Bits m) (BitStr I J) O
      ).toQueryAlgCoh.mapOut g)) S = simLaw e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) S := by
  rw [simLaw_expandCoh_eq e E k _ hA' g S, simLaw_expandCoh_eq e E k A hA g S]
  set ρ₀ := (A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
      (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)
  have hρ₀ : ρ₀.PosSemidef :=
    (A.init.posSemidef.kronecker (posSemidef_single_one (fresh (X := Bits m) (Y := BitStr I J) k))
      ).submatrix _
  set Gr : ℕ → Set (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) :=
    fun n => {w | w.1 ∈ expSeq G n} with hGr
  set Gr₀ : Set (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) := {w | w.1 ∈ G₀}
  have hprevGr : ∀ n, prevSeq Gr Gr₀ n = {w | w.1 ∈ prevSeq (expSeq G) G₀ n} := fun n => by
    simp only [prevSeq]
    split_ifs <;> rfl
  set Gr' : ℕ → Set (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) :=
    fun n => {w | w.1 ∈ expSeq G' n} with hGr'
  set Gr₀' : Set (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) := {w | w.1 ∈ G₀'}
  have hprevGr' : ∀ n, prevSeq Gr' Gr₀' n = {w | w.1 ∈ prevSeq (expSeq G') G₀' n} := fun n => by
    simp only [prevSeq]
    split_ifs <;> rfl
  have hmass := (densityRun_block_mass e (fun w : ExpansionRegister (X := Bits m)
      (Y := BitStr I J) k A.V => ℓ w.1) Gr Gr' Gr₀ Gr₀'
    (fun n hn => by simp only [hGr, expSeq_eq_pred G (show A.depth < n by omega)])
    (fun n hn => by simp only [hGr', expSeq_eq_pred G' (show A.depth < n by omega)])
    (fun n w hw => by
      simp only [hGr, hGr', expSeq, Set.mem_setOf_eq]
      exact hnone _ w.1 hw)
    (fun w hw => hnone₀ w.1 hw)
    (expKraus e E k A.step fun v => g (some (A.out v)))
    (expKraus e E k K' fun v => g (some (A.out v)))
    (fun i k' => by
      rw [hprevGr]
      exact keepsSet_expKraus e E k G G₀ hG _ i k')
    (fun i k' => by
      rw [hprevGr']
      exact keepsSet_expKraus e E k G' G₀' hG' _ i k')
    (fun i k' => by
      rw [hprevGr]
      exact keepsBlocksOn_expKraus e E k ℓ G₀ G hK _ i k')
    (fun i k' => by
      rw [hprevGr']
      exact keepsBlocksOn_expKraus e E k ℓ G₀' G' hK' _ i k')
    (tp_expKraus e E k hA _) (tp_expKraus e E k hA' _)
    (fun i k' a b haG hbG ha hb => by
      rw [hprevGr] at hbG
      exact expKraus_op_congr_rc e E k (fun j v => v ∈ G j ∧ ℓ v = none)
        (fun n v => v ∈ prevSeq (expSeq G) G₀ n ∧ ℓ v = none)
        (fun j k'' x y hx hy => hrow j k'' x y hx.1 hy.1 hx.2 hy.2) _ i k' a b ⟨haG, ha⟩
        ⟨hbG, hb⟩)
    (fun i r' c d hcG hdG hc hd => by
      rw [hprevGr] at hcG hdG
      exact expKraus_rowGram_congr e E k ℓ r'
        (fun j v => v ∈ prevSeq (expSeq G) G₀ j ∧ ℓ v = none)
        (fun j x y hx hy => hgram j r' x y hx.1 hy.1 hx.2 hy.2) _ i c d
        fun _ => ⟨⟨hcG, hc⟩, ⟨hdG, hd⟩⟩)
    ρ₀ (fun a b h => by
      simp only [ρ₀, Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
      exact hρs _ _ (left_ne_zero_of_mul h))
    (fun a b h => by
      simp only [ρ₀, Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
      exact hρs' _ _ (left_ne_zero_of_mul h)) (A.depth + k)).2 r
  -- the sums over the block, through the nonnegative diagonal
  have hnn : ∀ (K : Fin (A.depth + k + 1) → KrausMap (Option A.R)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V)) y,
      0 ≤ (densityRun e K ρ₀ (A.depth + k) y y).re := fun K y =>
    (Complex.nonneg_iff.1 ((densityRun_posSemidef e K hρ₀ _).diag_nonneg)).1
  have hsum : ∀ (K : Fin (A.depth + k + 1) → KrausMap (Option A.R)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k A.V)),
      ∑ y, (if (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S then
        (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (densityRun e K ρ₀ (A.depth + k) y y).re =
      ENNReal.ofReal (∑ y ∈ Finset.univ.filter (fun y : SimRegister (ExpansionRegister
          (X := Bits m) (Y := BitStr I J) k A.V) I J m (A.depth + k) => ℓ y.1.1.1 = some r),
        densityRun e K ρ₀ (A.depth + k) y y).re := fun K => by
    rw [Complex.re_sum, ENNReal.ofReal_sum_of_nonneg fun y _ => hnn K y, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : ℓ y.1.1.1 = some r
    · simp [(hS y).2 hy, hy]
    · have : ¬ (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S :=
        fun h => hy ((hS y).1 h)
      simp [this, hy]
  rw [hsum, hsum, hmass]

end MassAlg

/-! ### The hypotheses as structures -/

section Structures

/-- **A core algorithm and the same algorithm with the Kraus maps `K'` on one block** of the
label `ℓ` of the work register, along sets `G i` (for `A`) and `G' i` (for `K'`) and permutations
`τ i` after step `i` (`G₀`, `G₀'`, `τ₀` of the initial state): each family moves from its set
before its step into its set after and keeps the blocks of `ℓ` on the columns of its set before;
they agree on the rows in `G i` and the columns in the set before with label `none` or `some r`,
read along `τ i` on the rows, along the previous permutation on the columns and along `ρ i` on the
operators; the initial state is supported on `G₀` and `G₀'` and invariant along `τ₀` on its block;
the permutations keep the label and map the block of `G i` onto that of `G' i` (the hypotheses of
`simLaw_expandCoh_relabel_block` at `ρ' = A.init`). -/
structure _root_.GordieHowe.Quantum.Alg.BlockRel {O L : Type} (A : Alg (Bits m) (BitStr I J) O)
    (K' : Fin (A.depth + 1) → KrausMap A.R (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (ℓ : A.V → Option L) (G G' : Fin (A.depth + 1) → Set A.V) (G₀ G₀' : Set A.V)
    (τ : Fin (A.depth + 1) → Equiv.Perm A.V) (τ₀ : Equiv.Perm A.V)
    (ρ : Fin (A.depth + 1) → Equiv.Perm A.R) (r : L) : Prop where
  /-- The permutations keep the label. -/
  label_eq : ∀ i v, ℓ (τ i v) = ℓ v
  /-- The initial permutation keeps the label. -/
  label_eq₀ : ∀ v, ℓ (τ₀ v) = ℓ v
  /-- The permutations map the block of the sets of `A` onto that of the sets of `K'`. -/
  set_eq : ∀ i v, InBlock ℓ r v → (τ i v ∈ G' i ↔ v ∈ G i)
  /-- The initial permutation maps the blocks of the initial sets onto each other. -/
  set_eq₀ : ∀ v, InBlock ℓ r v → (τ₀ v ∈ G₀' ↔ v ∈ G₀)
  /-- `A`'s Kraus maps move through the sets. -/
  keepsSet : ∀ (i : Fin (A.depth + 1)) k', KeepsSet
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ G i} ((A.step i).op k')
  /-- The other Kraus maps move through their sets. -/
  keepsSet' : ∀ (i : Fin (A.depth + 1)) k', KeepsSet
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G') G₀' i}
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ G' i} ((K' i).op k')
  /-- `A`'s Kraus maps keep the blocks on the columns of the set before their step. -/
  keeps : ∀ (i : Fin (A.depth + 1)) k', KeepsBlocksOn
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
    (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) ((A.step i).op k')
  /-- The other Kraus maps keep the blocks on the columns of their set before their step. -/
  keeps' : ∀ (i : Fin (A.depth + 1)) k', KeepsBlocksOn
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G') G₀' i}
    (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K' i).op k')
  /-- The two agree on the block along the permutations, the operators read along `ρ`. -/
  hop : ∀ i : Fin (A.depth + 1), OpRelIdx (ρ i) (queryWorkPerm (τ i))
    (queryWorkPerm (prevSeq (expSeq τ) τ₀ i)) {p | InBlock ℓ r p.1 ∧ p.1 ∈ G i}
    {p | InBlock ℓ r p.1 ∧ p.1 ∈ prevSeq (expSeq G) G₀ i} (A.step i) (K' i)
  /-- The initial state is supported on the initial set. -/
  init_supp : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀
  /-- The initial state is supported on the other initial set. -/
  init_supp' : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀'
  /-- The initial state is invariant on its block. -/
  init_eq : ∀ a b : QueryReg A.V 1 (Bits m) (BitStr I J), a.1 ∈ G₀ → b.1 ∈ G₀ →
    InBlock ℓ r a.1 → InBlock ℓ r b.1 →
    A.init.mat (queryWorkPerm τ₀ a) (queryWorkPerm τ₀ b) = A.init.mat a b

/-- **A core algorithm and the same algorithm with the Kraus maps `K'` off the blocks** of the
label `ℓ`, along sets `G i` after step `i` (`G₀` of the initial state): both families move from
the set before their step into `G i` and keep the blocks of `ℓ` on the columns of the set before;
they agree on the rows in `G i` with label `none` from the columns in the set before with label
`none`, and their rows of every block have the same overlaps from two columns in the set before
with label `none`; the initial state is supported on `G₀` and `G₀'`; the sets of `A` and of `K'`
have the same states of label `none` (the hypotheses of `simLaw_expandCoh_block_mass`). -/
structure _root_.GordieHowe.Quantum.Alg.BlockNone {O L : Type} [DecidableEq L]
    (A : Alg (Bits m) (BitStr I J) O)
    (K' : Fin (A.depth + 1) → KrausMap A.R (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J)))
    (ℓ : A.V → Option L) (G G' : Fin (A.depth + 1) → Set A.V) (G₀ G₀' : Set A.V) : Prop where
  /-- The sets of `A` and of `K'` have the same states of label `none`. -/
  none_eq : ∀ i v, ℓ v = none → (v ∈ G' i ↔ v ∈ G i)
  /-- The initial sets have the same states of label `none`. -/
  none_eq₀ : ∀ v, ℓ v = none → (v ∈ G₀' ↔ v ∈ G₀)
  /-- `A`'s Kraus maps move through the sets. -/
  keepsSet : ∀ (i : Fin (A.depth + 1)) k', KeepsSet
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ G i} ((A.step i).op k')
  /-- The other Kraus maps move through their sets. -/
  keepsSet' : ∀ (i : Fin (A.depth + 1)) k', KeepsSet
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G') G₀' i}
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ G' i} ((K' i).op k')
  /-- `A`'s Kraus maps keep the blocks on the columns of the set before their step. -/
  keeps : ∀ (i : Fin (A.depth + 1)) k', KeepsBlocksOn
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G) G₀ i}
    (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) ((A.step i).op k')
  /-- The other Kraus maps keep the blocks on the columns of their set before their step. -/
  keeps' : ∀ (i : Fin (A.depth + 1)) k', KeepsBlocksOn
    {p : QueryReg A.V 1 (Bits m) (BitStr I J) | p.1 ∈ prevSeq (expSeq G') G₀' i}
    (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) ((K' i).op k')
  /-- The two agree on the rows in `G i` with label `none`, from the columns in the set before
  with label `none`. -/
  row_none_eq : ∀ (i : Fin (A.depth + 1)) k' (a b : QueryReg A.V 1 (Bits m) (BitStr I J)),
    a.1 ∈ G i → b.1 ∈ prevSeq (expSeq G) G₀ i → ℓ a.1 = none → ℓ b.1 = none →
      (K' i).op k' a b = (A.step i).op k' a b
  /-- Their rows of every block have the same overlaps from two columns with label `none`. -/
  gram_eq : ∀ (i : Fin (A.depth + 1)) r (c d : QueryReg A.V 1 (Bits m) (BitStr I J)),
    c.1 ∈ prevSeq (expSeq G) G₀ i → d.1 ∈ prevSeq (expSeq G) G₀ i → ℓ c.1 = none →
    ℓ d.1 = none →
    rowGram (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) r (K' i) c d =
      rowGram (fun p : QueryReg A.V 1 (Bits m) (BitStr I J) => ℓ p.1) r (A.step i) c d
  /-- The initial state is supported on the initial set. -/
  init_supp : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀
  /-- The initial state is supported on the other initial set. -/
  init_supp' : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀' ∧ b.1 ∈ G₀'

/-- **`simLaw_expandCoh_relabel_block` from `Alg.BlockRel`**, at the initial state of `A`. -/
theorem simLaw_expandCoh_of_blockRel {O L : Type} {A : Alg (Bits m) (BitStr I J) O}
    (hA : A.TracePreserving)
    {K' : Fin (A.depth + 1) → KrausMap A.R (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J))}
    (hA' : ({ A with step := K' } : Alg (Bits m) (BitStr I J) O).TracePreserving)
    {ℓ : A.V → Option L} {G G' : Fin (A.depth + 1) → Set A.V} {G₀ G₀' : Set A.V}
    {τ : Fin (A.depth + 1) → Equiv.Perm A.V} {τ₀ : Equiv.Perm A.V}
    {ρ : Fin (A.depth + 1) → Equiv.Perm A.R} {r : L}
    (h : A.BlockRel K' ℓ G G' G₀ G₀' τ τ₀ ρ r) (g : Option O → C)
    (hE : ∀ v, E.next (g (some (A.out (τ (Fin.last _) v)))) = E.next (g (some (A.out v))))
    (S : Set (BaseGame.Tuple (Bits m) B C k × DB (Bits m) B))
    (hS : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) I J m
        (A.depth + k),
      (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S → ℓ y.1.1.1 = some r)
    (hSτ : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) I J m
        (A.depth + k),
      (expOut e E k (fun v => g (some (A.out v))) (expWorkPerm k (τ (Fin.last _)) y.1.1),
        slotsDB e y.2) ∈ S ↔
        (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S) :
    simLaw e (expandAdv e E k (({ A with step := K' } : Alg (Bits m) (BitStr I J) O
      ).toQueryAlgCoh.mapOut g)) S = simLaw e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) S :=
  simLaw_expandCoh_relabel_block e E k A hA K' A.init hA' g ℓ G G' G₀ G₀' τ τ₀ h.label_eq
    h.label_eq₀ r h.set_eq h.set_eq₀ h.keepsSet h.keepsSet' ρ h.hop h.keeps h.keeps' h.init_supp
    h.init_supp' h.init_eq hE S hS hSτ

/-- **`simLaw_expandCoh_block_mass` from `Alg.BlockNone`.** -/
theorem simLaw_expandCoh_of_blockNone {O L : Type} [DecidableEq L]
    {A : Alg (Bits m) (BitStr I J) O} (hA : A.TracePreserving)
    {K' : Fin (A.depth + 1) → KrausMap A.R (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J))}
    (hA' : ({ A with step := K' } : Alg (Bits m) (BitStr I J) O).TracePreserving)
    {ℓ : A.V → Option L} {G G' : Fin (A.depth + 1) → Set A.V} {G₀ G₀' : Set A.V}
    (h : A.BlockNone K' ℓ G G' G₀ G₀') (g : Option O → C) (r : L)
    (S : Set (BaseGame.Tuple (Bits m) B C k × DB (Bits m) B))
    (hS : ∀ y : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k A.V) I J m
        (A.depth + k),
      (expOut e E k (fun v => g (some (A.out v))) y.1.1, slotsDB e y.2) ∈ S ↔ ℓ y.1.1.1 = some r) :
    simLaw e (expandAdv e E k (({ A with step := K' } : Alg (Bits m) (BitStr I J) O
      ).toQueryAlgCoh.mapOut g)) S = simLaw e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) S :=
  simLaw_expandCoh_block_mass e E k A hA K' hA' g ℓ G G' G₀ G₀' r h.none_eq h.none_eq₀ h.keepsSet
    h.keepsSet' h.keeps h.keeps' h.row_none_eq h.gram_eq h.init_supp h.init_supp' S hS

end Structures

end GordieHowe.QROM
