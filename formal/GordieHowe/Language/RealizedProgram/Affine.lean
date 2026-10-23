-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Cells
public import GordieHowe.ProofSystem.Program.System
public import GordieHowe.Language.RealizedProgram.Check

@[expose] public section

/-!
# GordieHowe: the affine rows of a program's domain

A predicate of the realized program whose target is `affine` (`GordieHowe.RealizedProgram.TargetsAdmit`: degree at most one in the
committed cells, `GordieHowe.RealizedProgram.cellDeg`) is a family of affine rows of its domain, one per coordinate
(`GordieHowe.RealizedProgram.affineRow`): the row's linear form is the gradient of the predicate's difference `e − e'`
at the cells (`GordieHowe.RealizedProgram.rowDiff`, the difference at each unit vector minus the difference at zero)
and its constant the difference at zero. The row holds exactly when the predicate's coordinate does
(`GordieHowe.RealizedProgram.affineRow_holds_iff`), because the difference is affine in the cells
(`GordieHowe.RealizedProgram.isAff_rowDiff`).

**Affine in the cells** (`IsAff`, `IsConst`): a function of the variables `z : κ → K` that is a
linear form plus a constant; a constant function. Both are closed under the operations of an
expression (`Expr.eval_isAff`): sums and differences, products with a constant factor, products
along an axis of length at most one, multiplexers with a constant selector or constant branches,
views, sparse rows and named operators with constant coefficients (`NamedOp.block_isAff`), Logic
builders on constant arguments or of width `0`, and shared expressions (`GordieHowe.RealizedProgram.refVal_isAff`). The
degree bookkeeping is the program's (`Expr.deg`): an expression of degree at most one in values that
are affine (degree one) or constant (degree zero) is affine, and of degree zero is constant.

**Which predicates are rows** (`GordieHowe.RealizedProgram.rowValueOk`): every value a side reads is a committed
value, a pad copy or a late value (affine in the cells: the late value is its message minus its pad
cell), or a public value that reads nothing of the committed assignment (`GordieHowe.RealizedProgram.pubB`); every
coefficient and operand is public. A predicate reading a bit view is not a row here: its bits are
not affine over the field in the words' cells (`Domain.viewRow`; none in stage A).
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Affine and constant functions of variables -/

section AffineLib

variable {K κ : Type} [Field K]

/-- **`g` is affine in the variables**: a linear form plus a constant. -/
def IsAff (g : (κ → K) → K) : Prop := ∃ (l : (κ → K) →ₗ[K] K) (c : K), ∀ z, g z = l z + c

/-- **`g` does not depend on the variables.** -/
def IsConst {β : Type*} (g : (κ → K) → β) : Prop := ∀ z z', g z = g z'

theorem IsConst.isAff {g : (κ → K) → K} (h : IsConst g) : IsAff g :=
  ⟨0, g 0, fun z => by simp [h z 0]⟩

omit [Field K] in
theorem isConst_const {β : Type*} (b : β) : IsConst (fun _ : κ → K => b) := fun _ _ => rfl

omit [Field K] in
theorem IsConst.comp {β γ : Type*} {g : (κ → K) → β} (h : IsConst g) (f : β → γ) :
    IsConst (fun z => f (g z)) := fun z z' => by dsimp only; rw [h z z']

omit [Field K] in
theorem IsConst.comp₂ {β γ δ : Type*} {g₁ : (κ → K) → β} {g₂ : (κ → K) → γ} (h₁ : IsConst g₁)
    (h₂ : IsConst g₂) (f : β → γ → δ) : IsConst (fun z => f (g₁ z) (g₂ z)) := fun z z' => by
  dsimp only
  rw [h₁ z z', h₂ z z']

theorem isAff_proj (k : κ) : IsAff (fun z : κ → K => z k) := ⟨LinearMap.proj k, 0, fun _ => by simp⟩

theorem IsAff.add {g₁ g₂ : (κ → K) → K} (h₁ : IsAff g₁) (h₂ : IsAff g₂) :
    IsAff (fun z => g₁ z + g₂ z) := by
  obtain ⟨l₁, c₁, h₁⟩ := h₁
  obtain ⟨l₂, c₂, h₂⟩ := h₂
  exact ⟨l₁ + l₂, c₁ + c₂, fun z => by dsimp only; rw [h₁, h₂, LinearMap.add_apply]; ring⟩

theorem IsAff.neg {g : (κ → K) → K} (h : IsAff g) : IsAff (fun z => -g z) := by
  obtain ⟨l, c, h⟩ := h
  exact ⟨-l, -c, fun z => by dsimp only; rw [h, LinearMap.neg_apply]; ring⟩

theorem IsAff.sub {g₁ g₂ : (κ → K) → K} (h₁ : IsAff g₁) (h₂ : IsAff g₂) :
    IsAff (fun z => g₁ z - g₂ z) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

theorem IsAff.mul_const {g g' : (κ → K) → K} (h : IsAff g) (hc : IsConst g') :
    IsAff (fun z => g z * g' z) := by
  obtain ⟨l, c, h⟩ := h
  exact ⟨g' 0 • l, c * g' 0, fun z => by
    dsimp only
    rw [h, hc z 0, LinearMap.smul_apply, smul_eq_mul]
    ring⟩

theorem IsAff.const_mul {g g' : (κ → K) → K} (hc : IsConst g') (h : IsAff g) :
    IsAff (fun z => g' z * g z) := by
  simpa only [mul_comm] using h.mul_const hc

theorem IsAff.ite (p : Prop) [Decidable p] {g₁ g₂ : (κ → K) → K} (h₁ : IsAff g₁) (h₂ : IsAff g₂) :
    IsAff (fun z => if p then g₁ z else g₂ z) := by
  by_cases hp : p
  · simpa only [if_pos hp] using h₁
  · simpa only [if_neg hp] using h₂

theorem IsAff.dite (p : Prop) [Decidable p] {g₁ : p → (κ → K) → K} {g₂ : ¬ p → (κ → K) → K}
    (h₁ : ∀ hp, IsAff (g₁ hp)) (h₂ : ∀ hp, IsAff (g₂ hp)) :
    IsAff (fun z => if hp : p then g₁ hp z else g₂ hp z) := by
  by_cases hp : p
  · simpa only [dif_pos hp] using h₁ hp
  · simpa only [dif_neg hp] using h₂ hp

theorem isAff_zero : IsAff (fun _ : κ → K => (0 : K)) := (isConst_const 0).isAff

theorem IsAff.sum {ι : Type*} (s : Finset ι) {g : ι → (κ → K) → K} (h : ∀ i ∈ s, IsAff (g i)) :
    IsAff (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isAff_zero (κ := κ) (K := K))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsAff.list_sum {α : Type*} (l : List α) {g : α → (κ → K) → K} (h : ∀ a ∈ l, IsAff (g a)) :
    IsAff (fun z => (l.map fun a => g a z).sum) := by
  induction l with
  | nil => simpa using (isAff_zero (κ := κ) (K := K))
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem a hb))

/-- **An affine function is its value at zero plus its gradient**: the differences at the unit
vectors, weighted by the variables. -/
theorem IsAff.eq_gradient [Fintype κ] [DecidableEq κ] {g : (κ → K) → K} (h : IsAff g) (z : κ → K) :
    g z = g 0 + ∑ k, z k * (g (fun j => if k = j then 1 else 0) - g 0) := by
  obtain ⟨l, c, h⟩ := h
  simp only [h, map_zero, zero_add, add_sub_cancel_right]
  rw [LinearMap.pi_apply_eq_sum_univ l z]
  simp only [smul_eq_mul]
  ring

end AffineLib

/-! ## Named operators preserve affine inputs -/

namespace Ops

variable {K : Type*} [Field K]

theorem negacyclic_eq (n : ℕ) (h x : ℕ → K) (j : ℕ) :
    negacyclic n h x j = if j < n then
      (∑ i : Fin n, ∑ k : Fin n, if (i : ℕ) + k = j then h i * x k else 0) -
        ∑ i : Fin n, ∑ k : Fin n, if (i : ℕ) + k = j + n then h i * x k else 0
    else 0 := by
  split_ifs with hj
  · exact negacyclic_apply n h x hj
  · simp [negacyclic, ofFin, hj]

theorem nttNatural_eq (n : ℕ) (ψ : K) (x : ℕ → K) (m : ℕ) :
    nttNatural n ψ x m = if m < n then ∑ i : Fin n, x i * ψ ^ ((2 * m + 1) * i) else 0 := by
  split_ifs with hm
  · exact nttNatural_apply n ψ x hm
  · simp [nttNatural, ofFin, hm]

end Ops

section

variable {ir : RealizedProgram} {I : Interp} {κ : Type} {f : ℕ}

/-- The negacyclic convolution with a fixed operand is affine in affine inputs. -/
theorem isAff_negacyclic (n : ℕ) (h : ℕ → (I f).K) {X : (κ → (I f).K) → ℕ → (I f).K}
    (hX : ∀ t, IsAff fun z => X z t) (j : ℕ) : IsAff fun z => Ops.negacyclic n h (X z) j := by
  simp only [Ops.negacyclic_eq]
  refine IsAff.ite _ (IsAff.sub ?_ ?_) isAff_zero <;>
  · refine IsAff.sum _ fun i _ => IsAff.sum _ fun k _ => IsAff.ite _ ?_ isAff_zero
    exact IsAff.const_mul (isConst_const _) (hX _)

/-- The natural-order transform is affine in affine inputs. -/
theorem isAff_nttNatural (n : ℕ) (ψ : (I f).K) {X : (κ → (I f).K) → ℕ → (I f).K}
    (hX : ∀ t, IsAff fun z => X z t) (m : ℕ) : IsAff fun z => Ops.nttNatural n ψ (X z) m := by
  simp only [Ops.nttNatural_eq]
  exact IsAff.ite _ (IsAff.sum _ fun i _ => (hX _).mul_const (isConst_const _)) isAff_zero

/-- **A named operator with a fixed operand reading is affine in affine inputs.** -/
theorem NamedOp.block_isAff (leaf : ir.Valuation I) :
    ∀ (op : NamedOp) {X : (κ → (I f).K) → ℕ → (I f).K}, (∀ t, IsAff fun z => X z t) →
      ∀ j, IsAff fun z => NamedOp.block ir f leaf op (X z) j
  | .negacyclicConv h form, X, hX, j => by
    simp only [NamedOp.block]
    exact isAff_negacyclic _ _ hX j
  | .polyMatVec a K L form, X, hX, j => by
    simp only [NamedOp.block]
    exact IsAff.ite _ (IsAff.sum _ fun l _ => isAff_negacyclic _ _ (fun s => hX _) _) isAff_zero
  | .polyBroadcast t K form, X, hX, j => by
    simp only [NamedOp.block]
    exact IsAff.ite _ (isAff_negacyclic _ _ hX _) isAff_zero
  | .ntt n psi .scheme, X, hX, j => by
    simp only [NamedOp.block, Ops.nttScheme]
    exact IsAff.ite _ (isAff_nttNatural _ _ hX _) isAff_zero
  | .ntt n psi .natural, X, hX, j => by
    simp only [NamedOp.block]
    exact isAff_nttNatural _ _ hX _
  | .inverseNtt n psi, X, hX, j => by
    simp only [NamedOp.block, Ops.inverseNtt]
    exact IsAff.ite _ (IsAff.const_mul (isConst_const _)
      (IsAff.sum _ fun m _ => (hX _).mul_const (isConst_const _))) isAff_zero
  | .nttTranspose n psi, X, hX, j => by
    simp only [NamedOp.block, Ops.nttTranspose]
    exact IsAff.ite _ (IsAff.sum _ fun m _ => IsAff.const_mul (isConst_const _) (hX _)) isAff_zero
  | .rowDot M R W, X, hX, j => by
    simp only [NamedOp.block, Ops.rowDot]
    exact IsAff.ite _ (IsAff.sum _ fun c _ => IsAff.const_mul (isConst_const _) (hX _)) isAff_zero
  | .macConv r w nch taps, X, hX, j => by
    simp only [NamedOp.block, Ops.macConv]
    exact IsAff.dite _ (fun _ => IsAff.sum _ fun c _ => IsAff.sum _ fun i _ =>
      IsAff.const_mul (isConst_const _) (hX _)) fun _ => isAff_zero
  | .acyclicConv h lx, X, hX, j => by
    simp only [NamedOp.block, Ops.acyclic]
    exact IsAff.ite _ (IsAff.sum _ fun a _ => IsAff.sum _ fun b _ =>
      IsAff.ite _ ((hX _).mul_const (isConst_const _)) isAff_zero) isAff_zero
  | .diagonal d, X, hX, j => by
    simp only [NamedOp.block, Ops.diagonal]
    exact IsAff.ite _ (IsAff.const_mul (isConst_const _) (hX _)) isAff_zero
  | .scale c, X, hX, j => by
    simp only [NamedOp.block]
    exact IsAff.ite _ (IsAff.const_mul (isConst_const _) (hX _)) isAff_zero
  | .constDiagonal d, X, hX, j => by
    simp only [NamedOp.block, Ops.diagonal]
    exact IsAff.ite _ (IsAff.const_mul (isConst_const _) (hX _)) isAff_zero
  | .sum w, X, hX, j => by
    simp only [NamedOp.block, Ops.sum]
    exact IsAff.ite _ (IsAff.sum _ fun t _ => hX _) isAff_zero
  | .fromDigits k base, X, hX, j => by
    simp only [NamedOp.block, Ops.fromDigits]
    exact IsAff.ite _ (IsAff.sum _ fun l _ => IsAff.const_mul (isConst_const _) (hX _)) isAff_zero
  | .batched b op, X, hX, j => by
    simp only [NamedOp.block]
    exact IsAff.ite _ (NamedOp.block_isAff leaf op (fun t => hX _) _) isAff_zero

/-! ## Logic builders of width zero -/

/-- **A Logic builder of width `0` is a constant**: it reads no bit of its arguments. -/
theorem LogicOp.eval_zero {R : Type*} [CommRing R] (op : LogicOp) (args args' : List (ℕ → R))
    (j : ℕ) : op.eval 0 args j = op.eval 0 args' j := by
  cases op <;> simp [LogicOp.eval, Ops.ltWord, Ops.leqWord, Ops.eqWord, Ops.ltReduce, Ops.eqReduce,
    Ops.andTree, Ops.orTree]

/-! ## Expressions of degree at most one -/

theorem foldr_max_eq_zero {l : List ℕ} : l.foldr max 0 = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem mem_degList {nd rd : ℕ → ℕ} {es : List Expr} {e : Expr} (he : e ∈ es) :
    e.deg nd rd ∈ Expr.degList nd rd es := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    simp only [Expr.degList, List.mem_cons]
    rcases List.mem_cons.1 he with rfl | h
    · exact .inl rfl
    · exact .inr (ih h)

variable (ir) in
/-- **A value's coordinates are affine, or constant at degree zero**, in the variables, at the
valuations `V`: `nd v ≤ 1` gives each coordinate (read in field `f`) affine, `nd v = 0` gives the
value constant. -/
structure LeafOk (V : (κ → (I f).K) → ir.Valuation I) (nd : ℕ → ℕ) (v : ℕ) : Prop where
  /-- The value is affine at degree at most one. -/
  aff : nd v ≤ 1 → ∀ i, IsAff fun z => (castElt (V z v i) : (I f).K)
  /-- The value is constant at degree zero. -/
  const : nd v = 0 → IsConst fun z => V z v

/-- **A shared expression is affine, or constant at degree zero**, at the readings `R`. -/
structure RefOk (R : (κ → (I f).K) → ℕ → ℕ → (I f).K) (rd : ℕ → ℕ) (k : ℕ) : Prop where
  /-- The shared expression is affine at degree at most one. -/
  aff : rd k ≤ 1 → ∀ i, IsAff fun z => R z k i
  /-- The shared expression is constant at degree zero. -/
  const : rd k = 0 → IsConst fun z => R z k

/-- A coefficient with constant values is constant. -/
theorem Coef.eval_isConst {V : (κ → (I f).K) → ir.Valuation I} {c : Coef}
    (h : ∀ v ∈ c.nodes, IsConst fun z => V z v) : IsConst fun z => Coef.eval ir f (V z) c := by
  cases c with
  | const => exact isConst_const _
  | node v i => exact (h v (by simp [Coef.nodes])).comp fun g => (castElt (g i) : (I f).K)

mutual

/-- **An expression of degree at most one is affine, and of degree zero constant**, in the
variables, when its values and shared expressions are (`LeafOk`, `RefOk`) and its coefficients and
operands are of degree zero. -/
theorem Expr.eval_isAff {V : (κ → (I f).K) → ir.Valuation I}
    {R : (κ → (I f).K) → ℕ → ℕ → (I f).K} {nd rd : ℕ → ℕ} {rl : ℕ → ℕ} :
    ∀ (e : Expr), (∀ v ∈ e.directNodes, LeafOk ir V nd v) → (∀ v ∈ e.coefNodes, nd v = 0) →
      (∀ k ∈ e.refs, RefOk R rd k) →
      (e.deg nd rd ≤ 1 → ∀ i, IsAff fun z => Expr.eval ir f (V z) (R z) rl e i) ∧
        (e.deg nd rd = 0 → IsConst fun z => Expr.eval ir f (V z) (R z) rl e)
  | .leaf v, hL, _, _ => by
    have h := hL v (by simp [Expr.directNodes])
    simp only [Expr.deg, Expr.eval]
    exact ⟨h.aff, fun h0 => (h.const h0).comp fun g i => (castElt (g i) : (I f).K)⟩
  | .add e e', hL, hC, hR | .sub e e', hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs, List.mem_append] at hL hC hR
    have ih := Expr.eval_isAff (rl := rl) e (fun v hv => hL v (.inl hv)) (fun v hv => hC v (.inl hv))
      (fun k hk => hR k (.inl hk))
    have ih' := Expr.eval_isAff (rl := rl) e' (fun v hv => hL v (.inr hv)) (fun v hv => hC v (.inr hv))
      (fun k hk => hR k (.inr hk))
    simp only [Expr.deg, Expr.eval, max_le_iff, Nat.max_eq_zero_iff]
    first
    | exact ⟨fun h i => (ih.1 h.1 i).add (ih'.1 h.2 i),
        fun h => (ih.2 h.1).comp₂ (ih'.2 h.2) fun g g' i => g i + g' i⟩
    | exact ⟨fun h i => (ih.1 h.1 i).sub (ih'.1 h.2 i),
        fun h => (ih.2 h.1).comp₂ (ih'.2 h.2) fun g g' i => g i - g' i⟩
  | .mul e e', hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs, List.mem_append] at hL hC hR
    have ih := Expr.eval_isAff (rl := rl) e (fun v hv => hL v (.inl hv)) (fun v hv => hC v (.inl hv))
      (fun k hk => hR k (.inl hk))
    have ih' := Expr.eval_isAff (rl := rl) e' (fun v hv => hL v (.inr hv)) (fun v hv => hC v (.inr hv))
      (fun k hk => hR k (.inr hk))
    simp only [Expr.deg, Expr.eval]
    refine ⟨fun h i => ?_, fun h => ?_⟩
    · rcases Nat.eq_zero_or_pos (e.deg nd rd) with h0 | h0
      · exact IsAff.const_mul ((ih.2 h0).comp fun g => g i) (ih'.1 (by omega) i)
      · exact (ih.1 (by omega) i).mul_const ((ih'.2 (by omega)).comp fun g => g i)
    · exact (ih.2 (by omega)).comp₂ (ih'.2 (by omega)) fun g g' i => g i * g' i
  | .concat e e', hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs, List.mem_append] at hL hC hR
    have ih := Expr.eval_isAff (rl := rl) e (fun v hv => hL v (.inl hv)) (fun v hv => hC v (.inl hv))
      (fun k hk => hR k (.inl hk))
    have ih' := Expr.eval_isAff (rl := rl) e' (fun v hv => hL v (.inr hv)) (fun v hv => hC v (.inr hv))
      (fun k hk => hR k (.inr hk))
    simp only [Expr.deg, Expr.eval, max_le_iff, Nat.max_eq_zero_iff]
    exact ⟨fun h i => IsAff.ite _ (ih.1 h.1 _) (ih'.1 h.2 _),
      fun h => (ih.2 h.1).comp₂ (ih'.2 h.2) fun g g' i =>
        if i < Expr.len ir rl e then g i else g' (i - Expr.len ir rl e)⟩
  | .scale c e, hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs, List.mem_append] at hL hC hR
    have ih := Expr.eval_isAff (rl := rl) e (fun v hv => hL v (.inr hv)) (fun v hv => hC v (.inr hv)) hR
    have hc : IsConst fun z => Coef.eval ir f (V z) c :=
      Coef.eval_isConst fun v hv => (hL v (.inl hv)).const (hC v (.inl hv))
    simp only [Expr.deg, Expr.eval]
    exact ⟨fun h i => IsAff.const_mul hc (ih.1 (by omega) i),
      fun h => hc.comp₂ (ih.2 (by omega)) fun a g i => a * g i⟩
  | .reindex idx e, hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs] at hL hC hR
    have ih := Expr.eval_isAff (rl := rl) e hL hC hR
    simp only [Expr.deg, Expr.eval]
    exact ⟨fun h i => ih.1 h _, fun h => (ih.2 h).comp fun g i => g (idx.entry i)⟩
  | .linear rows e, hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs, List.mem_append] at hL hC hR
    have ih := Expr.eval_isAff (rl := rl) e (fun v hv => hL v (.inr hv)) (fun v hv => hC v (.inr hv)) hR
    have hc : ∀ i, ∀ t ∈ rows.getD i [], IsConst fun z => Coef.eval ir f (V z) t.2 :=
      fun i t ht => Coef.eval_isConst fun v hv =>
        (hL v (.inl (mem_rowNodes_of_mem_getD ht hv))).const
          (hC v (.inl (mem_rowNodes_of_mem_getD ht hv)))
    simp only [Expr.deg, Expr.eval]
    refine ⟨fun h i => IsAff.list_sum _ fun t ht =>
      IsAff.const_mul (hc i t ht) (ih.1 (by omega) _), fun h z z' => funext fun i => ?_⟩
    show ((rows.getD i []).map _).sum = ((rows.getD i []).map _).sum
    congr 1
    refine List.map_congr_left fun t ht => ?_
    have h1 := hc i t ht z z'
    have h2 := ih.2 (by omega) z z'
    dsimp only at h1 h2
    rw [h1, h2]
  | .prod n e, hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs] at hL hC hR
    have ih := Expr.eval_isAff (rl := rl) e hL hC hR
    simp only [Expr.deg, Expr.eval]
    have hconst : e.deg nd rd = 0 →
        IsConst fun z i => ((List.range n).map fun t => Expr.eval ir f (V z) (R z) rl e (i * n + t)).prod :=
      fun h0 => (ih.2 h0).comp fun g i => ((List.range n).map fun t => g (i * n + t)).prod
    refine ⟨fun h i => ?_, fun h => ?_⟩
    · rcases Nat.eq_zero_or_pos (e.deg nd rd) with h0 | h0
      · exact ((hconst h0).comp fun g => g i).isAff
      · have hn : n ≤ 1 := by
          by_contra hn
          have : 2 * 1 ≤ n * e.deg nd rd := Nat.mul_le_mul (by omega) h0
          omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
        · simpa using (isAff_zero (κ := κ) (K := (I f).K)).add (isConst_const 1).isAff
        · simpa using ih.1 (by omega) (i * 1 + 0)
    · rcases Nat.mul_eq_zero.1 h with rfl | h0
      · exact fun _ _ => rfl
      · exact hconst h0
  | .mux b t e, hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs, List.mem_append] at hL hC hR
    have ihb := Expr.eval_isAff (rl := rl) b (fun v hv => hL v (.inl (.inl hv)))
      (fun v hv => hC v (.inl (.inl hv))) (fun k hk => hR k (.inl (.inl hk)))
    have iht := Expr.eval_isAff (rl := rl) t (fun v hv => hL v (.inl (.inr hv)))
      (fun v hv => hC v (.inl (.inr hv))) (fun k hk => hR k (.inl (.inr hk)))
    have ihe := Expr.eval_isAff (rl := rl) e (fun v hv => hL v (.inr hv)) (fun v hv => hC v (.inr hv))
      (fun k hk => hR k (.inr hk))
    simp only [Expr.deg, Expr.eval]
    refine ⟨fun h i => ?_, fun h => ?_⟩
    · rcases Nat.eq_zero_or_pos (b.deg nd rd) with h0 | h0
      · have hb := (ihb.2 h0).comp fun g => g i
        exact (IsAff.const_mul hb (iht.1 (by omega) i)).add
          (IsAff.const_mul (hb.comp fun a => 1 - a) (ihe.1 (by omega) i))
      · have ht := (iht.2 (by omega)).comp fun g => g i
        have he := (ihe.2 (by omega)).comp fun g => g i
        exact ((ihb.1 (by omega) i).mul_const ht).add
          (((isConst_const 1).isAff.sub (ihb.1 (by omega) i)).mul_const he)
    · exact ((ihb.2 (by omega)).comp₂ (iht.2 (by omega)) Prod.mk).comp₂ (ihe.2 (by omega))
        fun bt g i => bt.1 i * bt.2 i + (1 - bt.1 i) * g i
  | .apply op e, hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs, List.mem_append] at hL hC hR
    have ih := Expr.eval_isAff (rl := rl) e (fun v hv => hL v (.inr hv)) (fun v hv => hC v (.inr hv)) hR
    have hop : ∀ z, NamedOp.block ir f (V z) op = NamedOp.block ir f (V 0) op := fun z =>
      NamedOp.block_congr ir op fun v hv => (hL v (.inl (List.mem_append.1 hv))).const (hC v (.inl (List.mem_append.1 hv))) z 0
    simp only [Expr.deg, Expr.eval, NamedOp.apply, hop]
    exact ⟨fun h i => NamedOp.block_isAff (V 0) op (fun s => ih.1 (by omega) _) _,
      fun h => (ih.2 (by omega)).comp fun g i =>
        NamedOp.block ir f (V 0) op (fun t => g (i / NamedOp.rows ir op * NamedOp.cols ir op + t))
          (i % NamedOp.rows ir op)⟩
  | .ref k, _, _, hR => by
    have h := hR k (by simp [Expr.refs])
    simp only [Expr.deg, Expr.eval]
    exact ⟨h.aff, h.const⟩
  | .logic op w args, hL, hC, hR => by
    simp only [Expr.directNodes, Expr.coefNodes, Expr.refs] at hL hC hR
    simp only [Expr.deg, Expr.eval]
    have hconst : (Expr.degList nd rd args).foldr max 0 = 0 ∨ w = 0 →
        IsConst fun z i => op.eval w (Expr.evalList ir f (V z) (R z) rl args) i := by
      rintro (h0 | rfl)
      · exact (Expr.evalList_isConst (rl := rl) args hL hC hR fun e he =>
          foldr_max_eq_zero.1 h0 _ (mem_degList he)).comp fun gs i => op.eval w gs i
      · exact fun z z' => funext fun i => LogicOp.eval_zero op _ _ i
    refine ⟨fun h i => ((hconst ?_).comp fun g => g i).isAff, fun h => hconst ?_⟩
    · rcases Nat.eq_zero_or_pos w with hw | hw
      · exact .inr hw
      · left
        by_contra h0
        have : 2 * 1 * 1 ≤ 2 * w * (Expr.degList nd rd args).foldr max 0 :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
    · rcases Nat.mul_eq_zero.1 h with h0 | h0
      · exact .inr (by omega)
      · exact .inl h0

/-- **A list of expressions of degree zero is constant** in the variables. -/
theorem Expr.evalList_isConst {V : (κ → (I f).K) → ir.Valuation I}
    {R : (κ → (I f).K) → ℕ → ℕ → (I f).K} {nd rd : ℕ → ℕ} {rl : ℕ → ℕ} :
    ∀ (es : List Expr), (∀ v ∈ Expr.directNodesList es, LeafOk ir V nd v) →
      (∀ v ∈ Expr.coefNodesList es, nd v = 0) → (∀ k ∈ Expr.refsList es, RefOk R rd k) →
      (∀ e ∈ es, e.deg nd rd = 0) → IsConst fun z => Expr.evalList ir f (V z) (R z) rl es
  | [], _, _, _, _ => fun _ _ => rfl
  | e :: es, hL, hC, hR, h0 => by
    simp only [Expr.directNodesList, Expr.coefNodesList, Expr.refsList, List.mem_append] at hL hC hR
    have ih := Expr.evalList_isConst (rl := rl) es (fun v hv => hL v (.inr hv)) (fun v hv => hC v (.inr hv))
      (fun k hk => hR k (.inr hk)) fun e' he' => h0 e' (List.mem_cons_of_mem _ he')
    have he := (Expr.eval_isAff (rl := rl) e (fun v hv => hL v (.inl hv)) (fun v hv => hC v (.inl hv))
      (fun k hk => hR k (.inl hk))).2 (h0 e List.mem_cons_self)
    simp only [Expr.evalList]
    exact he.comp₂ ih List.cons

end

/-- **A shared expression of degree at most one is affine, and of degree zero constant**, with `n`
levels, when the values it reads are (`LeafOk`) and its coefficients are of degree zero. -/
theorem refVal_isAff {V : (κ → (I f).K) → ir.Valuation I} {nd : ℕ → ℕ} :
    ∀ n k, (∀ v ∈ ir.refClosure Expr.directNodes n k, LeafOk ir V nd v) →
      (∀ v ∈ ir.refClosure Expr.coefNodes n k, nd v = 0) →
      RefOk (fun z => ir.refVal (V z) n f) (ir.refDeg nd n) k
  | 0, _, _, _ => ⟨fun _ _ => isAff_zero, fun _ _ _ => rfl⟩
  | n + 1, k, hL, hC => by
    have h := Expr.eval_isAff (ir.expr k) (V := V) (R := fun z => ir.refVal (V z) n f)
      (rd := ir.refDeg nd n) (rl := ir.refLen ir.exprs.length)
      (fun v hv => hL v (List.mem_append_left _ hv)) (fun v hv => hC v (List.mem_append_left _ hv))
      fun k' hk' => refVal_isAff n k' (fun v hv => hL v (refClosure_mono_ref hk' hv))
        fun v hv => hC v (refClosure_mono_ref hk' hv)
    exact ⟨fun hd i => h.1 hd i, fun hd => h.2 hd⟩

/-- **An expression of degree at most one is affine** in the variables, through its shared
expressions, when the values it reads are (`LeafOk`) and its coefficients are of degree zero. -/
theorem evalE_isAff {V : (κ → (I f).K) → ir.Valuation I} {nd : ℕ → ℕ} {e : Expr}
    (hL : ∀ v ∈ ir.exprNodes e, LeafOk ir V nd v) (hC : ∀ v ∈ ir.closure Expr.coefNodes e, nd v = 0)
    (hd : ir.degOf nd e ≤ 1) (i : ℕ) : IsAff fun z => ir.evalE (V z) f e i :=
  (Expr.eval_isAff e (fun v hv => hL v (List.mem_append_left _ hv))
    (fun v hv => hC v (List.mem_append_left _ hv))
    (fun k hk => refVal_isAff _ k
      (fun v hv => hL v (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, hv⟩)))
      fun v hv => hC v (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, hv⟩)))).1 hd i

end

end GordieHowe.RealizedProgram

/-! ## Casts of affine values -/

namespace GordieHowe.RealizedProgram

theorem castElt_sub {I : Interp} {a b : ℕ} (x y : (I a).K) :
    (castElt (x - y) : (I b).K) = castElt x - castElt y := by
  by_cases h : a = b
  · subst h
    simp
  · simp [castElt_of_ne h]

theorem castElt_add {I : Interp} {a b : ℕ} (x y : (I a).K) :
    (castElt (x + y) : (I b).K) = castElt x + castElt y := by
  by_cases h : a = b
  · subst h
    simp
  · simp [castElt_of_ne h]

theorem castElt_mul {I : Interp} {a b : ℕ} (x y : (I a).K) :
    (castElt (x * y) : (I b).K) = castElt x * castElt y := by
  by_cases h : a = b
  · subst h
    simp
  · simp [castElt_of_ne h]

/-- **Two casts are one cast**, or `0` when the first changes the field identifier. -/
theorem castElt_castElt_eq {I : Interp} {a b c : ℕ} (x : (I a).K) :
    (castElt (castElt x : (I b).K) : (I c).K) = if a = b then castElt x else 0 := by
  split_ifs with h
  · subst h
    simp
  · rw [castElt_of_ne h, castElt_zero]

theorem castElt_castElt {I : Interp} {a b : ℕ} (x : (I a).K) :
    (castElt (castElt x : (I b).K) : (I a).K) = if a = b then x else 0 := by
  split_ifs with h
  · exact castElt_castElt_of_eq h x
  · rw [castElt_of_ne h, castElt_zero]

theorem castElt_ite {I : Interp} {a b : ℕ} (p : Prop) [Decidable p] (x y : (I a).K) :
    (castElt (if p then x else y) : (I b).K) = if p then castElt x else castElt y := by
  split_ifs <;> rfl

theorem castElt_dite {I : Interp} {a b : ℕ} (p : Prop) [Decidable p] (x : p → (I a).K)
    (y : (I a).K) : (castElt (if h : p then x h else y) : (I b).K) =
      if h : p then castElt (x h) else castElt y := by
  split_ifs <;> rfl

end GordieHowe.RealizedProgram

/-! ## The affine rows of a domain -/

namespace GordieHowe.RealizedProgram

open Export

/-- **The sides of a predicate of domain `d` with target `affine`**: a field `equal`'s, or a
`mod_0`'s field equation's. -/
def PredBody.rowSides (b : PredBody) (d : ℕ) : Option (Expr × Expr) :=
  match b with
  | .equal d' e e' .affine => if d' = d then some (e, e') else none
  | .mod d' 0 e e' real => if d' = d ∧ real.target = some .affine then some (e, e') else none
  | _ => none

section

/-- **A row predicate placed holds exactly when its sides agree** (`PlacedHolds`: a field `equal`
itself, a `mod_0` its field equation). -/
theorem placedHolds_iff_of_rowSides {ir : RealizedProgram} {I : Interp} {b : PredBody} {d : ℕ}
    {e e' : Expr} (h : b.rowSides d = some (e, e')) (rd : ir.Valuation I) :
    ir.PlacedHolds rd b ↔ ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i := by
  unfold PredBody.rowSides at h
  split at h
  · split_ifs at h with hd
    cases h
    subst hd
    rfl
  · split_ifs at h with hd
    cases h
    rw [hd.1]
    simp [PlacedHolds]
  · cases h

variable (ir : RealizedProgram)

/-- **A sum of constant multiples of committed values and constants**: a committed value, a
constant, a sum, or a constant multiple. Its values are affine in the cells
(`RealizedProgram.isAff_evalE_linPriv`). -/
def linPrivB : Expr → Bool
  | .leaf u =>
    match (ir.value u).kind with
    | .priv => true
    | .constant _ => true
    | _ => false
  | .add a b => linPrivB a && linPrivB b
  | .scale (.const _) a => linPrivB a
  | _ => false

/-- **A value a row may read**: a committed value, a pad copy or a late value (affine in the cells),
a value bound to a sum of constant multiples of committed values and constants (its digits,
`linPrivB`; affine in the cells through the realized assignment), or a public value reading nothing
of the committed assignment (`pubB`). -/
def rowValueOk (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .priv => true
  | .padCopy _ _ => true
  | .late => true
  | .bits _ _ => false
  | .bound x => ir.linPrivB x
  | _ => ir.pubB ir.fuel v

/-- **A side a row may have**: every value it reads may be read by a row (`rowValueOk`), every
coefficient and operand is public, and its degree in the cells is at most one. -/
def rowExprOk (e : Expr) : Bool :=
  (ir.exprNodes e).all ir.rowValueOk && (ir.closure Expr.coefNodes e).all (ir.cellNd · == 0) &&
    decide (ir.cellDeg e ≤ 1)

/-- **Predicate `p` is a family of affine rows of domain `d`**: a field `equal` of `d` with target
`affine`, or a `mod_0` of `d` whose field equation has target `affine`, whose sides may be rows'
(`rowExprOk`). -/
def isRow (d p : ℕ) : Bool :=
  match (ir.predicate p).body.rowSides d with
  | some (e, e') => ir.rowExprOk e && ir.rowExprOk e'
  | none => false

/-- **The predicates of domain `d` that are affine rows.** -/
def RowPred (d : ℕ) : Type := {p : Fin ir.predicates.length // ir.isRow d p = true}

instance (d : ℕ) : Fintype (ir.RowPred d) := Subtype.fintype _

/-- The row predicates are encoded by their indices. -/
instance (d : ℕ) : Encodable (ir.RowPred d) :=
  inferInstanceAs (Encodable {p : Fin ir.predicates.length // ir.isRow d p = true})

/-- The left side of a row predicate. -/
def rowLhs (d p : ℕ) : Expr := (((ir.predicate p).body.rowSides d).map (·.1)).getD default

/-- The right side of a row predicate. -/
def rowRhs (d p : ℕ) : Expr := (((ir.predicate p).body.rowSides d).map (·.2)).getD default

/-- **The affine rows of domain `d`**: one per row predicate and coordinate of its left side. -/
def Row (d : ℕ) : Type := Σ p : ir.RowPred d, Fin (ir.exprLen (ir.rowLhs d p.1))

instance (d : ℕ) : Fintype (ir.Row d) := inferInstanceAs (Fintype (Σ _ : ir.RowPred d, Fin _))

/-- The rows are encoded as the sigma type. -/
instance (d : ℕ) : Encodable (ir.Row d) := inferInstanceAs (Encodable (Σ _ : ir.RowPred d, Fin _))

variable (I : Interp)

/-- **The valuation of the cells `a` of domain `d`**: the reader of the layout's environment at the
statement `x`, the realized assignment (`bindAsg`) of the committed assignment read from the cells,
and the run `r`. -/
abbrev cellValuation (d : ℕ) (x : ir.Valuation I) (r : (ir.layout I).Run)
    (a : ir.Cell d → (I (ir.domainField d)).K) : ir.Valuation I :=
  ir.reader (ir.layoutEnv I x (ir.bindAsg (ir.ofCells I d a)) r)

/-- **The difference of row predicate `p` at coordinate `i`**, at the cells `a`: left side minus
right side, read by the cells' valuation. -/
def rowDiff (d : ℕ) (x : ir.Valuation I) (r : (ir.layout I).Run) (p i : ℕ)
    (a : ir.Cell d → (I (ir.domainField d)).K) : (I (ir.domainField d)).K :=
  ir.evalWith (ir.cellValuation I d x r a) d (ir.rowLhs d p) i -
    ir.evalWith (ir.cellValuation I d x r a) d (ir.rowRhs d p) i

/-- **The affine row of predicate `p` at coordinate `i`** of domain `d`: the gradient of the
difference (`rowDiff` at the unit vectors minus at zero) as the linear form, the difference at zero
as the constant. -/
def affineRow (d : ℕ) (q : ir.Row d) :
    AffineRow (ir.layout I) (ir.Valuation I) (I (ir.domainField d)).K (ir.Cell d) where
  form x r := ∑ k, (ir.rowDiff I d x r q.1.1 q.2 (fun j => if k = j then 1 else 0) -
    ir.rowDiff I d x r q.1.1 q.2 0) • LinearMap.proj k
  const x r := ir.rowDiff I d x r q.1.1 q.2 0

variable {ir I}

/-- **A sum of constant multiples of committed values and constants is affine** in the variables
(`linPrivB`), cast into any field, when the committed values and the constants are. -/
theorem isAff_evalE_linPriv {κ : Type} {g f : ℕ} {V : (κ → (I g).K) → ir.Valuation I}
    (hV : ∀ u, ((ir.value u).kind = .priv ∨ ∃ es, (ir.value u).kind = .constant es) → ∀ i,
      IsAff fun z => (castElt (V z u i) : (I g).K)) :
    ∀ {e : Expr}, ir.linPrivB e = true → ∀ i,
      IsAff fun z => (castElt (ir.evalE (V z) f e i) : (I g).K)
  | .leaf u, h, i => by
    unfold linPrivB at h
    split at h
    · rename_i hk
      change IsAff fun z => (castElt (castElt (V z u i) : (I f).K) : (I g).K)
      simp only [castElt_castElt_eq]
      exact IsAff.ite _ (hV u (.inl hk) i) isAff_zero
    · rename_i es hk
      change IsAff fun z => (castElt (castElt (V z u i) : (I f).K) : (I g).K)
      simp only [castElt_castElt_eq]
      exact IsAff.ite _ (hV u (.inr ⟨es, hk⟩) i) isAff_zero
    · cases h
  | .add a b, h, i => by
    simp only [linPrivB, Bool.and_eq_true] at h
    change IsAff fun z => (castElt (ir.evalE (V z) f a i + ir.evalE (V z) f b i) : (I g).K)
    simp only [castElt_add]
    exact (isAff_evalE_linPriv hV h.1 i).add (isAff_evalE_linPriv hV h.2 i)
  | .scale (.const c) a, h, i => by
    simp only [linPrivB] at h
    change IsAff fun z => (castElt ((I f).decode c * ir.evalE (V z) f a i) : (I g).K)
    simp only [castElt_mul]
    exact IsAff.const_mul (isConst_const _) (isAff_evalE_linPriv hV h i)
  | .sub _ _, h, _ | .scale (.node _ _) _, h, _ | .mul _ _, h, _ | .reindex _ _, h, _
  | .concat _ _, h, _ | .linear _ _, h, _ | .prod _ _, h, _ | .mux _ _ _, h, _
  | .apply _ _, h, _ | .ref _, h, _ | .logic _ _ _, h, _ => by simp [linPrivB] at h

/-- **The cells' valuation is affine, or constant, at every value a row may read.** -/
theorem leafOk_cellValuation {d : ℕ} {x : ir.Valuation I} {r : (ir.layout I).Run} {v : ℕ}
    (hv : ir.rowValueOk v = true) :
    LeafOk ir (f := ir.domainField d) (ir.cellValuation I d x r) ir.cellNd v := by
  rcases hk : (ir.value v).kind with
    _ | ⟨_ | ⟨name, args⟩ | e⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, m⟩ | u | xb
  case bound =>
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · have hval : ∀ z, ir.cellValuation I d x r z v i =
          ir.evalE (ir.committedRead (ir.ofCells I d z)) (ir.valueField v) xb i := fun z => by
        simp only [cellValuation, reader, fuel, read, hk, layoutEnv, bindAsg]
      simp only [hval]
      refine isAff_evalE_linPriv (fun u hu j => ?_) (by simpa [rowValueOk, hk] using hv) i
      rcases hu with hu | ⟨es, hu⟩
      · simp only [committedRead, hu, ofCells, castElt_dite, castElt_castElt]
        exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ =>
          (isConst_const _).isAff
      · simp only [committedRead, hu]
        exact (isConst_const _).isAff
    · simp [cellNd, isCommitted, hk] at h0
  case priv =>
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [cellValuation, reader_of_priv _ hk, layoutEnv,
        ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl), ofCells, castElt_dite,
        castElt_castElt]
      exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ => (isConst_const _).isAff
    · simp [cellNd, isCommitted, hk] at h0
  case padCopy =>
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [cellValuation, reader_of_padCopy _ hk, layoutEnv,
        ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl), ofCells, castElt_dite,
        castElt_castElt]
      exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ => (isConst_const _).isAff
    · simp [cellNd, isCommitted, hk] at h0
  case late =>
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [cellValuation, reader_of_late _ hk, layoutEnv, castElt_ite]
      refine IsAff.ite _ ?_ (isConst_const _).isAff
      simp only [castElt_sub, bindAsg, ofCells, castElt_dite, castElt_castElt]
      exact (isConst_const _).isAff.sub
        (IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ => (isConst_const _).isAff)
    · simp [cellNd, isCommitted, isLateNode, Kind.isLate, hk] at h0
  case bits => simp [rowValueOk, hk] at hv
  all_goals
    have hpub : ir.pubB ir.fuel v = true := by simpa [rowValueOk, hk] using hv
    have hc : IsConst fun z => ir.cellValuation I d x r z v := fun z z' =>
      reader_eq_of_pubB (a := ir.bindAsg (ir.ofCells I d z)) (a' := ir.bindAsg (ir.ofCells I d z'))
        (fun u i hu =>
          (padsAgreeOff_ofCells d z u i hu).trans (padsAgreeOff_ofCells d z' u i hu).symm) hpub
    exact ⟨fun _ i => (hc.comp fun g => (castElt (g i) : (I (ir.domainField d)).K)).isAff,
      fun _ => hc⟩

/-- **The difference of a row predicate is affine in the cells.** -/
theorem isAff_rowDiff {d : ℕ} {p : ℕ} (hp : ir.isRow d p = true) (x : ir.Valuation I)
    (r : (ir.layout I).Run) (i : ℕ) : IsAff (ir.rowDiff I d x r p i) := by
  have hside : ∀ e, ir.rowExprOk e = true →
      IsAff fun z => ir.evalWith (ir.cellValuation I d x r z) d e i := by
    intro e he
    simp only [rowExprOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at he
    exact evalE_isAff (fun v hv => leafOk_cellValuation (he.1.1 v hv)) he.1.2 he.2 i
  unfold isRow at hp
  unfold rowDiff rowLhs rowRhs
  split at hp
  · rename_i e e' h
    simp only [Bool.and_eq_true] at hp
    simp only [h, Option.map_some, Option.getD_some]
    exact (hside e hp.1).sub (hside e' hp.2)
  · simp at hp

/-- **The affine row holds exactly when the predicate's coordinate does.** -/
theorem affineRow_holds_iff {d : ℕ} (q : ir.Row d) (x : ir.Valuation I)
    (a : ir.Cell d → (I (ir.domainField d)).K) (r : (ir.layout I).Run) :
    (ir.affineRow I d q).Holds x a r ↔
      ir.evalWith (ir.cellValuation I d x r a) d (ir.rowLhs d q.1.1) q.2 =
        ir.evalWith (ir.cellValuation I d x r a) d (ir.rowRhs d q.1.1) q.2 := by
  have hform : (ir.affineRow I d q).form x r a = ∑ k, a k *
      (ir.rowDiff I d x r q.1.1 q.2 (fun j => if k = j then 1 else 0) -
        ir.rowDiff I d x r q.1.1 q.2 0) := by
    simp only [affineRow, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, mul_comm]
  rw [← sub_eq_zero, ← rowDiff, (isAff_rowDiff q.1.2 x r q.2).eq_gradient a, AffineRow.Holds, hform,
    add_comm]
  rfl

/-- **The rows of a row predicate hold exactly when the predicate placed holds** at the cells'
valuation (`PlacedHolds`: a field `equal` itself, a `mod_0` its field equation). -/
theorem affineRows_iff {d : ℕ} (p : ir.RowPred d) (x : ir.Valuation I)
    (a : ir.Cell d → (I (ir.domainField d)).K) (r : (ir.layout I).Run) :
    (∀ i, (ir.affineRow I d ⟨p, i⟩).Holds x a r) ↔
      ir.PlacedHolds (ir.cellValuation I d x r a) (ir.predicate p.1).body := by
  obtain ⟨e, e', h⟩ : ∃ e e', (ir.predicate p.1).body.rowSides d = some (e, e') := by
    have hp := p.2
    unfold isRow at hp
    split at hp
    · exact ⟨_, _, by assumption⟩
    · simp at hp
  have hl : ir.rowLhs d p.1 = e := by simp [rowLhs, h]
  have hr : ir.rowRhs d p.1 = e' := by simp [rowRhs, h]
  refine (forall_congr' fun i => affineRow_holds_iff ⟨p, i⟩ x a r).trans ?_
  dsimp only
  rw [placedHolds_iff_of_rowSides h]
  constructor
  · intro H i hi
    have := H ⟨i, hl ▸ hi⟩
    simp only [hl, hr] at this
    exact this
  · intro H i
    simp only [hl, hr]
    exact H i (hl ▸ i.2)

end

end GordieHowe.RealizedProgram
