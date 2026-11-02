-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignTable

@[expose] public section

/-!
# The reprogrammed query on parallel query pairs

The reprogrammed query of `GordieHowe/Model/Quantum/Core/Reprogram.lean` (Unruh 2017, ePrint
2017/398, p. 12, the unitary `U^{oracle,H,ℓ}`) on one query pair with its own ancilla
`(a, b, f) : X × Y × Bool`, with the assignments given as a table `T : X → Option Y`
(`GordieHowe/Model/Quantum/Interactive/AssignTable.lean`), and its lift to `n` parallel pairs,
each with its own ancilla, controlled by the rest of the basis state.

- `ancSwap T`: if the query input (flag clear) or the ancilla's input (flag set) has an entry in
  `T`, exchange the query pair with the ancilla's pair and flip the flag (`reprogSwap`).
  `ancAdd f`: add `f x` to the answer of the query pair (a query to `f`; with
  `f x = (T x).getD 0` it is `reprogAdd`). `ancPerm T h`: `ancSwap`, the query to `h`,
  `ancSwap`, the addition of the table entry (`reprogPerm`).
- `ancPerm_symm_anc_fst`, `ancPerm_symm_flag`, `ancPerm_symm_sys`: the inverse keeps the
  ancilla's input and flag, and with the flag clear acts on the query pair as the inverse of the
  query to `reprogT T h`.
- `liftPairs f`: the permutation of `QueryReg V n X Y × (Fin n → X × Y × Bool)` acting on pair `i`
  and ancilla `i` by `f v`, for the rest `v` of the basis state. `liftPairs_trans`: lifts
  compose.
- `ancMat x₀`: the clean ancillas, the product of the clean ancilla `reprogAnc x₀` of each pair.
- **`kronecker_ancMat_submatrix_liftPairs`**: if each `f v` acts on the ancillas as the inverse of
  `ancPerm` does (input and flag kept) and, with the flag clear, on the query pair as the inverse
  of a query to `g v`, then conjugating `ρ ⊗ ancMat x₀` by `liftPairs f` is conjugating `ρ` by the
  controlled query `queryPermOf g`, with the ancillas still clean. With `f v = ancPerm (T v) (h v)`
  this is `reprogQuery_eq_controlled` on `n` pairs with a table in place of an assignment list.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

/-! ### One pair -/

section Pair

variable {X Y : Type*} (T : X → Option Y)

/-- The pair of a query and its ancilla. -/
abbrev PairAnc (X Y : Type*) := (X × Y) × (X × Y × Bool)

/-- **Whether `ancSwap` exchanges**: with the flag clear, when the query input has an entry in
`T`; with the flag set, when the ancilla's input has one (`reprogCond`). -/
def ancCond (p : PairAnc X Y) : Bool :=
  if p.2.2.2 then (T p.2.1).isSome else (T p.1.1).isSome

/-- Exchange the query pair with the ancilla's pair and flip the flag (`swapFlip`). -/
def ancFlip (p : PairAnc X Y) : PairAnc X Y :=
  ((p.2.1, p.2.2.1), (p.1.1, p.1.2, !p.2.2.2))

theorem ancFlip_ancFlip (p : PairAnc X Y) : ancFlip (ancFlip p) = p := by
  obtain ⟨⟨x, y⟩, a, b, f⟩ := p
  simp [ancFlip]

theorem ancCond_ancFlip (p : PairAnc X Y) : ancCond T (ancFlip p) = ancCond T p := by
  obtain ⟨⟨x, y⟩, a, b, f⟩ := p
  cases f <;> simp [ancCond, ancFlip]

/-- **The exchange of the reprogrammed query** (`reprogSwap`): `ancFlip` where `ancCond`
holds; an involution. -/
def ancSwap : Equiv.Perm (PairAnc X Y) :=
  Function.Involutive.toPerm (fun p => if ancCond T p then ancFlip p else p) fun p => by
    by_cases h : ancCond T p = true
    · simp [h, ancCond_ancFlip T p, ancFlip_ancFlip]
    · simp [h]

theorem ancSwap_apply (p : PairAnc X Y) :
    ancSwap T p = if ancCond T p then ancFlip p else p :=
  rfl

theorem ancSwap_symm : (ancSwap T).symm = ancSwap T :=
  Function.Involutive.toPerm_symm _

variable [AddGroup Y]

/-- **A query to `f` on the query pair**: `(x, y) ↦ (x, y + f x)`, the ancilla unchanged. -/
def ancAdd (f : X → Y) : Equiv.Perm (PairAnc X Y) where
  toFun p := ((p.1.1, p.1.2 + f p.1.1), p.2)
  invFun p := ((p.1.1, p.1.2 - f p.1.1), p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem ancAdd_apply (f : X → Y) (p : PairAnc X Y) :
    ancAdd f p = ((p.1.1, p.1.2 + f p.1.1), p.2) :=
  rfl

theorem ancAdd_symm_apply (f : X → Y) (p : PairAnc X Y) :
    (ancAdd f).symm p = ((p.1.1, p.1.2 - f p.1.1), p.2) :=
  rfl

/-- **The reprogrammed query on one pair** (`reprogPerm`): `ancSwap`, the query to `h`,
`ancSwap`, then the table entry added. -/
def ancPerm (h : X → Y) : Equiv.Perm (PairAnc X Y) :=
  (((ancSwap T).trans (ancAdd h)).trans (ancSwap T)).trans (ancAdd fun x => (T x).getD 0)

/-- The inverse of the reprogrammed query keeps the ancilla's input. -/
theorem ancPerm_symm_anc_fst (h : X → Y) (p : PairAnc X Y) :
    ((ancPerm T h).symm p).2.1 = p.2.1 := by
  obtain ⟨⟨x, y⟩, a, b, f⟩ := p
  cases f <;>
  · simp only [ancPerm, Equiv.symm_trans_apply, ancSwap_symm, ancSwap_apply, ancAdd_symm_apply,
      ancCond, ancFlip]
    split_ifs <;> simp_all

/-- The inverse of the reprogrammed query keeps the flag. -/
theorem ancPerm_symm_flag (h : X → Y) (p : PairAnc X Y) :
    ((ancPerm T h).symm p).2.2.2 = p.2.2.2 := by
  obtain ⟨⟨x, y⟩, a, b, f⟩ := p
  cases f <;>
  · simp only [ancPerm, Equiv.symm_trans_apply, ancSwap_symm, ancSwap_apply, ancAdd_symm_apply,
      ancCond, ancFlip]
    split_ifs <;> simp_all

/-- **With the flag clear, the inverse of the reprogrammed query acts on the query pair as the
inverse of a query to `reprogT T h`.** -/
theorem ancPerm_symm_sys (h : X → Y) (p : PairAnc X Y) (hf : p.2.2.2 = false) :
    ((ancPerm T h).symm p).1 = (p.1.1, p.1.2 - reprogT T h p.1.1) := by
  obtain ⟨⟨x, y⟩, a, b, f⟩ := p
  simp only at hf
  subst hf
  rcases hT : T x with _ | t
  · simp [ancPerm, ancSwap_symm, ancSwap_apply, ancAdd_symm_apply, ancCond, hT, reprogT]
  · simp [ancPerm, ancSwap_symm, ancSwap_apply, ancAdd_symm_apply, ancCond, ancFlip, hT,
      reprogT]

end Pair

/-! ### Parallel pairs -/

section Lift

variable {V X Y : Type*} {n : ℕ}

/-- The ancillas of `n` query pairs. -/
abbrev AncReg (X Y : Type*) (n : ℕ) := Fin n → X × Y × Bool

/-- **A family of pair permutations controlled by the rest of the basis state, on `n` pairs**:
pair `i` and ancilla `i` are moved by `f v`. -/
def liftPairs (f : V → Equiv.Perm (PairAnc X Y)) :
    Equiv.Perm (QueryReg V n X Y × AncReg X Y n) where
  toFun p := ((p.1.1, fun i => (f p.1.1 (p.1.2 i, p.2 i)).1), fun i => (f p.1.1 (p.1.2 i, p.2 i)).2)
  invFun p := ((p.1.1, fun i => ((f p.1.1).symm (p.1.2 i, p.2 i)).1),
    fun i => ((f p.1.1).symm (p.1.2 i, p.2 i)).2)
  left_inv p := by simp
  right_inv p := by simp

theorem liftPairs_apply (f : V → Equiv.Perm (PairAnc X Y)) (p : QueryReg V n X Y × AncReg X Y n) :
    liftPairs f p =
      ((p.1.1, fun i => (f p.1.1 (p.1.2 i, p.2 i)).1), fun i => (f p.1.1 (p.1.2 i, p.2 i)).2) :=
  rfl

theorem liftPairs_symm_apply (f : V → Equiv.Perm (PairAnc X Y))
    (p : QueryReg V n X Y × AncReg X Y n) :
    (liftPairs f).symm p = ((p.1.1, fun i => ((f p.1.1).symm (p.1.2 i, p.2 i)).1),
      fun i => ((f p.1.1).symm (p.1.2 i, p.2 i)).2) :=
  rfl

/-- **Lifts compose.** -/
theorem liftPairs_trans (f g : V → Equiv.Perm (PairAnc X Y)) :
    (liftPairs (n := n) f).trans (liftPairs g) = liftPairs fun v => (f v).trans (g v) :=
  Equiv.ext fun p => by simp [liftPairs_apply]

/-- **A lift of queries is the controlled query**, the ancillas unchanged. -/
theorem liftPairs_ancAdd [AddGroup Y] (g : V → X → Y) :
    liftPairs (n := n) (fun v => ancAdd (g v)) = (queryPermOf g).prodCongr (Equiv.refl _) :=
  Equiv.ext fun p => by
    obtain ⟨⟨v, q⟩, a⟩ := p
    rfl

variable [Fintype X] [DecidableEq X] [Fintype Y]

/-- **The clean ancillas of `n` pairs**: the product of the clean ancilla of each pair
(`reprogAnc x₀`, the input `x₀`, the uniform superposition of answers, the flag clear). -/
noncomputable def ancMat (x₀ : X) : Matrix (AncReg X Y n) (AncReg X Y n) ℂ :=
  fun a a' => ∏ i, reprogAnc x₀ (a i) (a' i)

omit [Fintype X] in
theorem reprogAnc_congr (x₀ : X) {a b a' b' : X × Y × Bool} (h1 : a.1 = b.1) (h2 : a.2.2 = b.2.2)
    (h1' : a'.1 = b'.1) (h2' : a'.2.2 = b'.2.2) : reprogAnc x₀ a a' = reprogAnc
        (Y := Y) x₀ b b' := by
  simp only [reprogAnc, ancWeight, h1, h2, h1', h2']

theorem ancMat_eq_zero_of_flag (x₀ : X) {a a' : AncReg X Y n} {i : Fin n}
    (h : (a i).2.2 = true ∨ (a' i).2.2 = true) : ancMat x₀ a a' = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rcases h with h | h <;> simp [reprogAnc, ancWeight, h]

/-- **Conjugating a state with clean ancillas by a lift of pair permutations that act as controlled
queries is conjugating by the controlled query** (module docstring). -/
theorem kronecker_ancMat_submatrix_liftPairs [AddGroup Y] (x₀ : X)
    (f : V → Equiv.Perm (PairAnc X Y))
    (g : V → X → Y)
    (hanc : ∀ v p, ((f v).symm p).2.1 = p.2.1 ∧ ((f v).symm p).2.2.2 = p.2.2.2)
    (hsys : ∀ v p, p.2.2.2 = false → ((f v).symm p).1 = (p.1.1, p.1.2 - g v p.1.1))
    (ρ : Matrix (QueryReg V n X Y) (QueryReg V n X Y) ℂ) :
    (ρ ⊗ₖ ancMat x₀).submatrix (liftPairs f).symm (liftPairs f).symm =
      (ρ.submatrix (queryPermOf g).symm (queryPermOf g).symm) ⊗ₖ ancMat (n := n) x₀ := by
  ext ⟨⟨v, q⟩, a⟩ ⟨⟨v', q'⟩, a'⟩
  simp only [submatrix_apply, kroneckerMap_apply, liftPairs_symm_apply]
  have hM : ancMat x₀ (fun i => ((f v).symm (q i, a i)).2) (fun i => ((f v').symm (q' i, a' i)).2) =
      ancMat (Y := Y) x₀ a a' := by
    refine Finset.prod_congr rfl fun i _ => reprogAnc_congr x₀ ?_ ?_ ?_ ?_
    · exact (hanc v (q i, a i)).1
    · exact (hanc v (q i, a i)).2
    · exact (hanc v' (q' i, a' i)).1
    · exact (hanc v' (q' i, a' i)).2
  rw [hM]
  by_cases hf : (∀ i, (a i).2.2 = false) ∧ ∀ i, (a' i).2.2 = false
  · have e1 : ((v, fun i => ((f v).symm (q i, a i)).1) : QueryReg V n X Y) =
        (queryPermOf g).symm (v, q) := by
      rw [queryPermOf_symm_apply]
      exact Prod.ext rfl (funext fun i => hsys v (q i, a i) (hf.1 i))
    have e2 : ((v', fun i => ((f v').symm (q' i, a' i)).1) : QueryReg V n X Y) =
        (queryPermOf g).symm (v', q') := by
      rw [queryPermOf_symm_apply]
      exact Prod.ext rfl (funext fun i => hsys v' (q' i, a' i) (hf.2 i))
    rw [e1, e2]
  · have h0 : ancMat (Y := Y) x₀ a a' = 0 := by
      simp only [not_and_or, not_forall, Bool.not_eq_false] at hf
      rcases hf with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ancMat_eq_zero_of_flag x₀ (Or.inl hi)
      · exact ancMat_eq_zero_of_flag x₀ (Or.inr hi)
    rw [h0, mul_zero, mul_zero]

/-- **The reprogrammed query on `n` pairs** satisfies the hypotheses of
`kronecker_ancMat_submatrix_liftPairs` with the query to `reprogT T h`. -/
theorem kronecker_ancMat_submatrix_liftPairs_ancPerm [AddGroup Y] (x₀ : X)
    (T : V → X → Option Y) (h : V → X → Y) (ρ : Matrix (QueryReg V n X Y) (QueryReg V n X Y) ℂ) :
    (ρ ⊗ₖ ancMat x₀).submatrix (liftPairs fun v => ancPerm (T v) (h v)).symm
        (liftPairs fun v => ancPerm (T v) (h v)).symm =
      (ρ.submatrix (queryPermOf fun v => reprogT (T v) (h v)).symm
        (queryPermOf fun v => reprogT (T v) (h v)).symm) ⊗ₖ ancMat (n := n) x₀ :=
  kronecker_ancMat_submatrix_liftPairs x₀ _ _
    (fun v p => ⟨ancPerm_symm_anc_fst (T v) (h v) p, ancPerm_symm_flag (T v) (h v) p⟩)
    (fun v p hf => ancPerm_symm_sys (T v) (h v) p hf) ρ

end Lift

end GordieHowe.Quantum
