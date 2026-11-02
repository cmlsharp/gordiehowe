-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Model.Quantum.Interactive.AbsorbBudget

@[expose] public section

/-!
# An adversary and a challenger at a fixed base part of a split oracle

An additive split `sp : Y ≃+ Y₁ × Y₂` of the oracle's values reads an oracle `H : X → Y` as a base
part `X → Y₁` and a part `X → Y₂`. A query `|x, y⟩ ↦ |x, y + H x⟩` is, after the relabelling
`y ↦ sp y = (y₁, y₂)`, the permutation `y₁ ↦ y₁ + H₁ x` of the base part (`H₁` the base part of
`H`), which reads no oracle once `H₁` is fixed, and the query `y₂ ↦ y₂ + H₂ x` of the other part.
At a fixed base part `H₁`, an adversary and a challenger of the oracle `X → Y` are therefore an
adversary and a challenger of the oracle `X → Y₂`.

- `splitReg sp`: the adversary's registers with the `Y₁`-parts of the query answers moved into
  the workspace. `basePerm H₁ on`: the local query `y₁ ↦ y₁ + H₁ x` on the branches selected by
  `on`.
- `AdaptiveIAlg.restrictAt sp H₁ A`: the adversary at the base part `H₁`, of the oracle `X → Y₂`.
  Its Kraus map number `k` is `A`'s read along `splitReg`, followed by `basePerm` on the branches
  `A` queries after it (`AdaptiveIAlg.stepOn`): `restrictAt_step_op`, and at the operator level
  `restrictAt_step_op_eq_mul` (the permutation matrix of `basePerm` times the relabelled
  operator). Its shape is `AlgShape.restrictAtS` (`restrictAt_toShape`).
- `Challenger.restrictAt sp H₁ C`: the challenger at the base part `H₁`, whose reply programs are
  `C`'s translated (`OracleProg.translate`) to read the answer `y₂` to a query `x` as
  `sp.symm (H₁ x, y₂)` (`restrictAt_respond`, `run_respond_restrictAt`); it reprograms nothing
  (`noAssign_restrictAt`).
- The mixed games: `AdaptiveIAlg.splitG` (the game registers of the restricted adversary read as
  the adversary's), `AdaptiveIAlg.baseG` (the local query on them), `liftG_restrictAt_op` (the
  Kraus maps of the restricted mixed game are the adversary's along `splitG` after `baseG`),
  `mgInit_restrictAt`, and the commutation of the slot permutations with the relabelling
  (`copyG_splitG`, `respG_splitG`, `logAt_splitG`, `oraclePerm_splitG`, `postG_splitG`).
  `AdaptiveIAlg.mgRun_restrictAt`: against environments with the same replies whose oracles in
  force are joined from `H₁` and the other's, the restricted mixed game is the adversary's read
  along `splitG`.
- `AdaptiveIAlg.tracePreserving_restrictAt`, `AdaptiveIAlg.withinBudget_restrictAt` (through
  `Env.splitLift`, an environment of the `Y₂`-oracle read at the base part), and
  `QueryBoundedAdversary.restrictAt`: a `t`-query adversary at the base part is a `t`-query
  adversary of the oracle `X → Y₂`.
- **The law**, for a challenger `C` that reprograms nothing (`Challenger.NoAssign`):
  `AdaptiveIAlg.outLaw_composeBothOut_restrictAt` (every readout of the output and the history,
  the restricted composition at the base part `fun x => (sp (H x)).1` and the oracle
  `fun x => (sp (H x)).2` has the output law of the composition at `H`),
  `QueryBoundedAdversary.transcriptLaw_restrictAt`, and the forms at a joined oracle
  `fun x => sp.symm (H₁ x, H₂ x)` (`outLaw_composeBothOut_restrictAt_join`,
  `transcriptLaw_restrictAt_join`). The challenger's history, replies and oracles in force:
  `Challenger.hist_oracleIn_restrictAt`, `Challenger.answer_restrictAt`,
  `Challenger.oracle_restrictAt`.
- `basePerm_of_subsingleton`: with a one-element base component the local query is the identity.
- Matrix tools: `KrausMap.ofPerm_submatrix_of_comm`, `KrausMap.apply_submatrix_of_op`,
  `KrausMap.tp_of_op_submatrix`, `dephase_submatrix`, `Circuit.run_concat_map_submatrix`,
  `PMF.ext_of_apply_some`.
-/

open Finset Matrix
open scoped BigOperators ENNReal ComplexOrder

namespace GordieHowe.Quantum

/-! ### Basis relabellings of matrices -/

section Relabel

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- **A basis permutation intertwined with a relabelling**: if `π (e₁ y) = e₂ (π' y)` for every
`y`, then `π'` applied to `M` read along `e₁` is `π` applied to `M`, read along `e₂`. -/
theorem KrausMap.ofPerm_submatrix_of_comm {π : Equiv.Perm ι} {π' : Equiv.Perm ι'} {e₁ e₂ : ι' → ι}
    (h : ∀ y, π (e₁ y) = e₂ (π' y)) (M : Matrix ι ι ℂ) :
    (KrausMap.ofPerm π') (M.submatrix e₁ e₁) = ((KrausMap.ofPerm π) M).submatrix e₂ e₂ := by
  have h' : ∀ y, e₁ (π'.symm y) = π.symm (e₂ y) := fun y => by
    rw [Equiv.eq_symm_apply, h, Equiv.apply_symm_apply]
  ext i j
  simp only [KrausMap.ofPerm_apply, submatrix_apply, h']

/-- **A Kraus map whose operators are another's read along a relabelling** acts on matrices read
along the relabelling as the other: if `K'.op r = (K.op r).submatrix e₁ e`, then
`K' (M.submatrix e e) = (K M).submatrix e₁ e₁`. -/
theorem KrausMap.apply_submatrix_of_op {R : Type*} [Fintype R] {K : KrausMap R ι ι}
    {K' : KrausMap R ι' ι'} {e₁ : ι' → ι} (e : ι' ≃ ι) (h : ∀ r, K'.op r = (K.op r).submatrix e₁ e)
    (M : Matrix ι ι ℂ) : K' (M.submatrix e e) = (K M).submatrix e₁ e₁ := by
  simp only [KrausMap.apply, h, submatrix_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

omit [Fintype ι'] [DecidableEq ι'] in
/-- **A matrix with its rows moved along `e`** is the matrix of `e` times it. -/
theorem submatrix_id_eq_one_submatrix_mul {κ : Type*} (M : Matrix ι κ ℂ) (e : ι → ι) :
    M.submatrix e id = (1 : Matrix ι ι ℂ).submatrix e id * M := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- **A Kraus map whose operators are a trace-preserving one's read along bijections is trace
preserving.** -/
theorem KrausMap.tp_of_op_submatrix {R : Type*} [Fintype R] {K : KrausMap R ι ι}
    {K' : KrausMap R ι' ι'} (e₁ e : ι' ≃ ι) (h : ∀ r, K'.op r = (K.op r).submatrix e₁ e)
    (hK : ∑ r, (K.op r)ᴴ * K.op r = 1) : ∑ r, (K'.op r)ᴴ * K'.op r = 1 := by
  simp only [h, conjTranspose_submatrix, submatrix_mul_equiv]
  rw [← submatrix_sum, hK, submatrix_one_equiv]

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
/-- **Dephasing commutes with a relabelling** that keeps the dephased function. -/
theorem dephase_submatrix {L : Type*} [DecidableEq L] (g : ι → L) (e : ι' → ι)
    (M : Matrix ι ι ℂ) : dephase (g ∘ e) (M.submatrix e e) = (dephase g M).submatrix e e := by
  ext i j
  simp [dephase]

end Relabel

section RelabelCircuit

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- **Concatenated circuits that act alike along a relabelling**: if each circuit `c' a` acts on
matrices read along `e` as `c a`, so does the concatenation of a list of them. -/
theorem Circuit.run_concat_map_submatrix {α : Type*} (e : ι' ≃ ι) (c : α → Circuit ι)
    (c' : α → Circuit ι')
    (h : ∀ a (σ : Matrix ι ι ℂ), (c' a).run (Equiv.refl _) (σ.submatrix e e) =
      ((c a).run (Equiv.refl _) σ).submatrix e e) (l : List α) (σ : Matrix ι ι ℂ) :
    (Circuit.concat (l.map c')).run (Equiv.refl _) (σ.submatrix e e) =
      ((Circuit.concat (l.map c)).run (Equiv.refl _) σ).submatrix e e := by
  induction l generalizing σ with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, Circuit.run_concat, Circuit.run_concat, h, ih]

end RelabelCircuit

/-- **Two laws on `Option α` that agree on every `some a` are equal.** -/
theorem PMF.ext_of_apply_some {α : Type*} {p q : PMF (Option α)}
    (h : ∀ a, p (some a) = q (some a)) : p = q := by
  have hs : ∀ r : PMF (Option α), r none + ∑' x, (if x = none then 0 else r x) = 1 := fun r => by
    convert (ENNReal.tsum_eq_add_tsum_ite (f := (r : Option α → ℝ≥0∞)) none).symm.trans r.tsum_coe
  have heq : (∑' x, if x = none then 0 else p x) = ∑' x, if x = none then 0 else q x := by
    refine tsum_congr fun x => ?_
    rcases x with _ | a
    · rfl
    · simp [h a]
  have hne : (∑' x, if x = none then 0 else q x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hs q]; exact le_add_self)
  have hn : p none = q none := by
    have := (hs p).trans (hs q).symm
    rw [heq] at this
    exact (ENNReal.add_left_inj hne).1 this
  ext x
  rcases x with _ | a
  · exact hn
  · exact h a

/-! ### The split of the query pairs -/

section SplitReg

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

/-- **The adversary's registers with the first components of the query answers in the
workspace**: the workspace carries `Y₁`-values `ys`, the query pairs `(x, y₂)` answer in `Y₂`, and
the pair `k` is read as the pair `(x, sp.symm (ys k, y₂))` with an answer in `Y`. -/
def splitReg (sp : Y ≃+ Y₁ × Y₂) (W : Type) (n : ℕ) (X Req Resp : Type) :
    DReg (W × (Fin n → Y₁)) n X Y₂ Req Resp ≃ DReg W n X Y Req Resp where
  toFun d := ((d.1.1.1, d.1.2), fun k => ((d.2 k).1, sp.symm (d.1.1.2 k, (d.2 k).2)))
  invFun d := (((d.1.1, fun k => (sp (d.2 k).2).1), d.1.2), fun k => ((d.2 k).1, (sp (d.2 k).2).2))
  left_inv d := by
    obtain ⟨⟨⟨w, ys⟩, rest⟩, p⟩ := d
    simp
  right_inv d := by
    obtain ⟨⟨w, rest⟩, p⟩ := d
    simp

/-- **The local query to the base component** on the registers of `splitReg`: on the branches
whose workspace `w` has `on w`, the `Y₁`-value of pair `k` becomes `ys k + H₁ x`, with `x` the
input of pair `k`. It reads the base oracle `H₁` and no other oracle. -/
def basePerm (H₁ : X → Y₁) {W : Type} (on : W → Bool) (n : ℕ) (Req Resp : Type) :
    Equiv.Perm (DReg (W × (Fin n → Y₁)) n X Y₂ Req Resp) where
  toFun d := (((d.1.1.1, fun k => if on d.1.1.1 then d.1.1.2 k + H₁ (d.2 k).1 else d.1.1.2 k),
    d.1.2), d.2)
  invFun d := (((d.1.1.1, fun k => if on d.1.1.1 then d.1.1.2 k - H₁ (d.2 k).1 else d.1.1.2 k),
    d.1.2), d.2)
  left_inv d := by
    obtain ⟨⟨⟨w, ys⟩, rest⟩, p⟩ := d
    by_cases h : on w <;> simp [h]
  right_inv d := by
    obtain ⟨⟨⟨w, ys⟩, rest⟩, p⟩ := d
    by_cases h : on w <;> simp [h]

end SplitReg

/-! ### The adversary at a fixed base part -/

namespace AdaptiveIAlg

variable {X Y Y₁ Y₂ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **The branches queried after the Kraus map number `k`**: after a map before a slot, the
branches whose kind is a query; after a map before a post batch, all; after the last map, none. -/
def stepOn (k : StepIdx A.slots A.post) (w : A.W) : Bool :=
  if (k : ℕ) < A.slots then !A.kind w else decide ((k : ℕ) < A.slots + A.post)

/-- **The adversary at the base part `H₁` of the split `sp`**, an adversary of the oracle
`X → Y₂`: its workspace holds `A`'s workspace and the `Y₁`-parts of the query answers
(`splitReg`); it has `A`'s width, slots, post batches, budget, kinds, Kraus index and output; its
Kraus map number `k` is `A`'s read along `splitReg`, followed by the local query `basePerm` to `H₁`
on the branches `A` queries after it (`stepOn`).

Running time: that of `A`, plus, after each Kraus map, the relabelling `splitReg` and, on each of
the `A.width` query pairs, one evaluation of `H₁` and one addition in `Y₁` (`basePerm`); polynomial
when `A` and `H₁` are. This running time is argued here, not proved in Lean. -/
def restrictAt : AdaptiveIAlg (shA.restrictAtS Y₁ Y₂) O where
  kind w := A.kind w.1
  init := MState.reindex (splitReg sp A.W A.width X Req Resp).symm A.init
  step k := ((A.step k).reindex (splitReg sp A.W A.width X Req Resp).symm).permConj (Equiv.refl _)
    (basePerm H₁ (A.stepOn k) A.width Req Resp)
  out w := A.out w.1

/-- **The shape of the restricted adversary** (`AlgShape.restrictAtS`). -/
theorem restrictAt_toShape : (A.restrictAt sp H₁).toShape = A.toShape.restrictAtS Y₁ Y₂ :=
  rfl

/-- The Kraus operators of the restricted adversary: `A`'s read along `splitReg`, after the local
query. -/
theorem restrictAt_step_op (k : StepIdx A.slots A.post) (r : A.R) :
    ((A.restrictAt sp H₁).step k).op r = ((A.step k).op r).submatrix
      ((splitReg sp A.W A.width X Req Resp) ∘ (basePerm H₁ (A.stepOn k) A.width Req Resp).symm)
      (splitReg sp A.W A.width X Req Resp) := by
  ext i j
  rfl

/-- **The Kraus maps of the restricted adversary are the local query after `A`'s relabelled Kraus
maps**, at the operator level: operator `r` is the permutation matrix of `basePerm` times operator
`r` of `A`'s Kraus map read along `splitReg`. -/
theorem restrictAt_step_op_eq_mul (k : StepIdx A.slots A.post) (r : A.R) :
    ((A.restrictAt sp H₁).step k).op r =
      (KrausMap.ofPerm (basePerm H₁ (A.stepOn k) A.width Req Resp)).op () *
        ((A.step k).reindex (splitReg sp A.W A.width X Req Resp).symm).op r :=
  submatrix_id_eq_one_submatrix_mul _ _

/-- **The restricted adversary's steps are channels** when `A`'s are. -/
theorem tracePreserving_restrictAt (hA : A.TracePreserving) :
    (A.restrictAt sp H₁).TracePreserving := fun k =>
  KrausMap.tp_of_op_submatrix ((basePerm H₁ (A.stepOn k) A.width Req Resp).symm.trans
    (splitReg sp A.W A.width X Req Resp)) (splitReg sp A.W A.width X Req Resp)
    (A.restrictAt_step_op sp H₁ k) (hA k)

/-- **The game registers of the restricted adversary read as those of the adversary**: the
`Y₁`-parts of the workspace joined to the `Y₂`-answers through `sp.symm`. -/
def splitG : (A.restrictAt sp H₁).toKindAlg.G ≃ A.toKindAlg.G where
  toFun g := ((((g.1.1.1.1, g.1.1.2), g.1.2), fun k => ((g.2 k).1, sp.symm (g.1.1.1.2 k, (g.2 k).2))))
  invFun g := (((((g.1.1.1, fun k => (sp (g.2 k).2).1), g.1.1.2), g.1.2),
    fun k => ((g.2 k).1, (sp (g.2 k).2).2)))
  left_inv g := by
    obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rest⟩, p⟩ := g
    simp
  right_inv g := by
    obtain ⟨⟨⟨w, c⟩, rest⟩, p⟩ := g
    simp

/-- **The local query of step `k` on the game registers** of the restricted adversary
(`basePerm` with the counter and the logs alongside). -/
def baseG (k : StepIdx A.slots A.post) : Equiv.Perm (A.restrictAt sp H₁).toKindAlg.G where
  toFun g := (((((g.1.1.1.1, fun i => if A.stepOn k g.1.1.1.1 then g.1.1.1.2 i + H₁ (g.2 i).1
      else g.1.1.1.2 i), g.1.1.2), g.1.2), g.2))
  invFun g := (((((g.1.1.1.1, fun i => if A.stepOn k g.1.1.1.1 then g.1.1.1.2 i - H₁ (g.2 i).1
      else g.1.1.1.2 i), g.1.1.2), g.1.2), g.2))
  left_inv g := by
    obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rest⟩, p⟩ := g
    by_cases h : A.stepOn k w <;> simp [h]
  right_inv g := by
    obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rest⟩, p⟩ := g
    by_cases h : A.stepOn k w <;> simp [h]

omit [AddGroup Y] in
/-- The Kraus operators of the mixed game of `toKindAlg`: those of `toKindAlg`, the identity on
the logs. -/
theorem toKindAlg_liftG_op_apply {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (k : StepIdx B.slots B.post)
    (r : B.R) (g h : B.toKindAlg.G) :
    (B.toKindAlg.liftG k).op r g h = (B.toKindAlg.step k).op r (splitLogs g).1 (splitLogs h).1 *
      (1 : Matrix (LogReg Req B.slots) (LogReg Req B.slots) ℂ) (splitLogs g).2 (splitLogs h).2 :=
  rfl

omit [AddGroup Y] in
/-- **The Kraus operators of `toKindAlg` before a slot**: the projection onto the branches within
the budget and the counter advanced on the query branches, around `A`'s operator. -/
theorem toKindAlg_step_op_of_lt {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) {k : StepIdx B.slots B.post}
    (hk : (k : ℕ) < B.slots) (r : B.R) (x y : DReg B.CntW B.width X Y Req Resp) :
    (B.toKindAlg.step k).op r x y = (if B.inBudget (B.cntShift.symm x) then 1 else 0) *
      ((B.step k).op r (B.cntSplit (B.cntShift.symm x)).1 (B.cntSplit y).1 *
        (1 : Matrix (Fin (B.budget + 2)) (Fin (B.budget + 2)) ℂ) (B.cntSplit (B.cntShift.symm x)).2
          (B.cntSplit y).2) := by
  rw [toKindAlg_step_of_lt B hk]
  simp only [KrausMap.permConj, KrausMap.restrict, Matrix.submatrix_apply, Matrix.diagonal_mul,
    Equiv.refl_apply]
  rfl

omit [AddGroup Y] in
/-- **The Kraus operators of `toKindAlg` from the last slot on**: `A`'s, the identity on the
counter. -/
theorem toKindAlg_step_op_of_not_lt {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) {k : StepIdx B.slots B.post}
    (hk : ¬ (k : ℕ) < B.slots) (r : B.R) (x y : DReg B.CntW B.width X Y Req Resp) :
    (B.toKindAlg.step k).op r x y = (B.step k).op r (B.cntSplit x).1 (B.cntSplit y).1 *
      (1 : Matrix (Fin (B.budget + 2)) (Fin (B.budget + 2)) ℂ) (B.cntSplit x).2 (B.cntSplit y).2 := by
  rw [AdaptiveIAlg.toKindAlg_step_of_not_lt _ hk]
  rfl

/-- **The Kraus maps of the mixed game of the restricted adversary** are the adversary's read along
`splitG`, after the local query `baseG`. -/
theorem liftG_restrictAt_op (k : StepIdx A.slots A.post) (r : A.R) :
    ((A.restrictAt sp H₁).toKindAlg.liftG k).op r = ((A.toKindAlg.liftG k).op r).submatrix
      ((A.splitG sp H₁) ∘ (A.baseG sp H₁ k).symm) (A.splitG sp H₁) := by
  ext i j
  obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rq, rs, lg⟩, p⟩ := i
  obtain ⟨⟨⟨⟨w', ys'⟩, c'⟩, rq', rs', lg'⟩, p'⟩ := j
  refine (toKindAlg_liftG_op_apply (A.restrictAt sp H₁) k r _ _).trans ?_
  refine Eq.trans ?_ (toKindAlg_liftG_op_apply A k r _ _).symm
  by_cases hk : (k : ℕ) < A.slots
  · refine (congrArg (· * _) (toKindAlg_step_op_of_lt (A.restrictAt sp H₁) (k := k) hk r _ _)).trans ?_
    refine Eq.trans ?_ (congrArg (· * _) (toKindAlg_step_op_of_lt A hk r _ _)).symm
    rfl
  · refine (congrArg (· * _) (toKindAlg_step_op_of_not_lt (A.restrictAt sp H₁) (k := k) hk r _ _)).trans ?_
    refine Eq.trans ?_ (congrArg (· * _) (toKindAlg_step_op_of_not_lt A hk r _ _)).symm
    rfl

/-- The restricted adversary has `A`'s kinds. -/
@[simp]
theorem restrictAt_kind (w : (A.restrictAt sp H₁).W) : (A.restrictAt sp H₁).kind w = A.kind w.1 :=
  rfl

omit [AddGroup Y] in
/-- Before slot `j`, the local query is made on the query branches. -/
@[simp]
theorem stepOn_slotStep (j : Fin A.slots) (w : A.W) :
    A.stepOn (slotStep j : StepIdx A.slots A.post) w = !A.kind w := by
  simp [stepOn]

omit [AddGroup Y] in
/-- Before post batch `b`, the local query is made on every branch. -/
@[simp]
theorem stepOn_postStep (b : Fin A.post) (w : A.W) :
    A.stepOn (postStep b : StepIdx A.slots A.post) w = true := by
  simp [stepOn]

omit [AddGroup Y] in
/-- After the last Kraus map no local query is made. -/
@[simp]
theorem stepOn_lastStep (w : A.W) : A.stepOn (lastStep : StepIdx A.slots A.post) w = false := by
  simp [stepOn]

/-- `baseG` after the last Kraus map is the identity. -/
theorem baseG_lastStep_symm_apply (g : (A.restrictAt sp H₁).toKindAlg.G) :
    (A.baseG sp H₁ lastStep).symm g = g := by
  obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rest⟩, p⟩ := g
  simp [baseG]

/-- **The initial state of the restricted mixed game** is the adversary's read along `splitG`. -/
theorem mgInit_restrictAt :
    (A.restrictAt sp H₁).toKindAlg.mgInit = A.toKindAlg.mgInit.submatrix (A.splitG sp H₁)
      (A.splitG sp H₁) := by
  ext g h
  obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rq, rs, lg⟩, p⟩ := g
  obtain ⟨⟨⟨⟨w', ys'⟩, c'⟩, rq', rs', lg'⟩, p'⟩ := h
  rfl

variable {Ω Ω' St St' : Type} {Q Q' : ℕ} [OracleState St X Y] [OracleState St' X Y₂]
  (E : Env Ω Req Resp X Y Q St) (E' : Env Ω' Req Resp X Y₂ Q' St') (ω : Ω) (ω' : Ω')

/-- The copy of a request commutes with the relabelling and the local query. -/
theorem copyG_splitG (k : StepIdx A.slots A.post) (j : Fin A.slots)
    (g : (A.restrictAt sp H₁).toKindAlg.G) :
    A.toKindAlg.copyG j (A.splitG sp H₁ ((A.baseG sp H₁ k).symm g)) =
      A.splitG sp H₁ ((A.baseG sp H₁ k).symm ((A.restrictAt sp H₁).toKindAlg.copyG j g)) := by
  obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rq, rs, lg⟩, p⟩ := g
  have hL : A.toKindAlg.copyG j (A.splitG sp H₁ ((A.baseG sp H₁ k).symm
      ((((w, ys), c), rq, rs, lg), p))) = (if A.kind w = true then _ else _, _) := rfl
  have hR : (A.restrictAt sp H₁).toKindAlg.copyG j ((((w, ys), c), rq, rs, lg), p) =
      (if A.kind w = true then _ else _, _) := rfl
  rw [hL, hR]
  by_cases h : A.kind w
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rfl

omit [OracleState St X Y] [OracleState St' X Y₂] in
/-- The reply commutes with the relabelling and the local query, for environments with the same
replies. -/
theorem respG_splitG (hans : ∀ (lg : LogReg Req A.slots) i, E.answer ω lg i = E'.answer ω' lg i)
    (k : StepIdx A.slots A.post) (j : Fin A.slots) (g : (A.restrictAt sp H₁).toKindAlg.G) :
    A.toKindAlg.respG E ω j (A.splitG sp H₁ ((A.baseG sp H₁ k).symm g)) =
      A.splitG sp H₁ ((A.baseG sp H₁ k).symm ((A.restrictAt sp H₁).toKindAlg.respG E' ω' j g)) := by
  obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rq, rs, lg⟩, p⟩ := g
  have hL : A.toKindAlg.respG E ω j (A.splitG sp H₁ ((A.baseG sp H₁ k).symm
      ((((w, ys), c), rq, rs, lg), p))) = (if A.kind w = true then _ else _, _) := rfl
  have hR : (A.restrictAt sp H₁).toKindAlg.respG E' ω' j ((((w, ys), c), rq, rs, lg), p) =
      (if A.kind w = true then _ else _, _) := rfl
  rw [hL, hR]
  by_cases h : A.kind w
  · simp only [h, ↓reduceIte]
    have ha := hans lg j
    erw [ha]
    rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The log of slot `j` read along the relabelling and the local query. -/
theorem logAt_splitG (k : StepIdx A.slots A.post) (j : Fin A.slots) :
    (A.restrictAt sp H₁).toKindAlg.logAt j =
      A.toKindAlg.logAt j ∘ (A.splitG sp H₁ ∘ (A.baseG sp H₁ k).symm) := by
  funext g
  obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rq, rs, lg⟩, p⟩ := g
  rfl

omit [Fintype Y] [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] in
/-- `sp.symm` is additive. -/
theorem symm_add_symm (a b : Y₁ × Y₂) : sp.symm a + sp.symm b = sp.symm (a + b) :=
  (map_add sp.symm a b).symm

/-- **The query of slot `j`** is the local query of the base part followed by the query of the
`Y₂`-part, read along the relabelling, for environments whose oracles in force are joined from
`H₁` and the other's. -/
theorem oraclePerm_splitG
    (hor : ∀ (lg : LogReg Req A.slots) x, E.oracle ω lg x = sp.symm (H₁ x, E'.oracle ω' lg x))
    (j : Fin A.slots) (g : (A.restrictAt sp H₁).toKindAlg.G) :
    E.oraclePerm A.toKindAlg.kind ω
        (A.splitG sp H₁ ((A.baseG sp H₁ (slotStep j)).symm g)) =
      A.splitG sp H₁ (E'.oraclePerm (A.restrictAt sp H₁).toKindAlg.kind ω' g) := by
  obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rq, rs, lg⟩, p⟩ := g
  refine Prod.ext rfl (funext fun i => Prod.ext rfl ?_)
  have hL : ((E.oraclePerm A.toKindAlg.kind ω (A.splitG sp H₁ ((A.baseG sp H₁ (slotStep j)).symm
      ((((w, ys), c), rq, rs, lg), p)))).2 i).2 =
      sp.symm (if A.stepOn (slotStep j) w = true then ys i - H₁ (p i).1 else ys i, (p i).2) +
        (if A.kind w = true then 0 else E.oracle ω (lg : LogReg Req A.slots)) (p i).1 := rfl
  have hR : ((A.splitG sp H₁ (E'.oraclePerm (A.restrictAt sp H₁).toKindAlg.kind ω'
      ((((w, ys), c), rq, rs, lg), p))).2 i).2 =
      sp.symm (ys i, (p i).2 + (if A.kind w = true then 0 else
        E'.oracle ω' (lg : LogReg Req A.slots)) (p i).1) := rfl
  rw [hL, hR, stepOn_slotStep]
  by_cases h : A.kind w
  · simp [h]
  · simp only [h, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
    erw [hor]
    rw [symm_add_symm, Prod.mk_add_mk, sub_add_cancel]

/-- **The post-phase query** is the local query of the base part followed by the query of the
`Y₂`-part, read along the relabelling. -/
theorem postG_splitG
    (hor : ∀ (lg : LogReg Req A.slots) x, E.oracle ω lg x = sp.symm (H₁ x, E'.oracle ω' lg x))
    (b : Fin A.post) (g : (A.restrictAt sp H₁).toKindAlg.G) :
    A.toKindAlg.postG E ω (A.splitG sp H₁ ((A.baseG sp H₁ (postStep b)).symm g)) =
      A.splitG sp H₁ ((A.restrictAt sp H₁).toKindAlg.postG E' ω' g) := by
  obtain ⟨⟨⟨⟨w, ys⟩, c⟩, rq, rs, lg⟩, p⟩ := g
  refine Prod.ext rfl (funext fun i => Prod.ext rfl ?_)
  have hL : ((A.toKindAlg.postG E ω (A.splitG sp H₁ ((A.baseG sp H₁ (postStep b)).symm
      ((((w, ys), c), rq, rs, lg), p)))).2 i).2 =
      sp.symm (if A.stepOn (postStep b) w = true then ys i - H₁ (p i).1 else ys i, (p i).2) +
        E.oracle ω (lg : LogReg Req A.slots) (p i).1 := rfl
  have hR : ((A.splitG sp H₁ ((A.restrictAt sp H₁).toKindAlg.postG E' ω'
      ((((w, ys), c), rq, rs, lg), p))).2 i).2 =
      sp.symm (ys i, (p i).2 + E'.oracle ω' (lg : LogReg Req A.slots) (p i).1) := rfl
  rw [hL, hR, stepOn_postStep]
  simp only [↓reduceIte]
  erw [hor]
  rw [symm_add_symm, Prod.mk_add_mk, sub_add_cancel]

/-- **Slot `j` of the restricted mixed game** acts on matrices read along `splitG` as slot `j` of
the adversary's. -/
theorem slot_restrictAt (hans : ∀ (lg : LogReg Req A.slots) i, E.answer ω lg i = E'.answer ω' lg i)
    (hor : ∀ (lg : LogReg Req A.slots) x, E.oracle ω lg x = sp.symm (H₁ x, E'.oracle ω' lg x))
    (deph : Bool) (j : Fin A.slots) (σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ) :
    (Circuit.kraus ((A.restrictAt sp H₁).toKindAlg.liftG (slotStep j))
        ((A.restrictAt sp H₁).toKindAlg.eventCirc E' ω' j deph)).run (Equiv.refl _)
        (σ.submatrix (A.splitG sp H₁) (A.splitG sp H₁)) =
      ((Circuit.kraus (A.toKindAlg.liftG (slotStep j)) (A.toKindAlg.eventCirc E ω j deph)).run
        (Equiv.refl _) σ).submatrix (A.splitG sp H₁) (A.splitG sp H₁) := by
  have h1 : ((A.restrictAt sp H₁).toKindAlg.liftG (slotStep j))
      (σ.submatrix (A.splitG sp H₁) (A.splitG sp H₁)) = ((A.toKindAlg.liftG (slotStep j)) σ).submatrix
        (A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm)
        (A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm) :=
    KrausMap.apply_submatrix_of_op (A.splitG sp H₁) (A.liftG_restrictAt_op sp H₁ (slotStep j)) σ
  have hc := KrausMap.ofPerm_submatrix_of_comm (π := A.toKindAlg.copyG j)
    (π' := (A.restrictAt sp H₁).toKindAlg.copyG j)
    (e₁ := A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm)
    (e₂ := A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm) (A.copyG_splitG sp H₁ (slotStep j) j)
  have hr := KrausMap.ofPerm_submatrix_of_comm (π := A.toKindAlg.respG E ω j)
    (π' := (A.restrictAt sp H₁).toKindAlg.respG E' ω' j)
    (e₁ := A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm)
    (e₂ := A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm)
    (A.respG_splitG sp H₁ E E' ω ω' hans (slotStep j) j)
  have ho := KrausMap.ofPerm_submatrix_of_comm (π := E.oraclePerm A.toKindAlg.kind ω)
    (π' := E'.oraclePerm (A.restrictAt sp H₁).toKindAlg.kind ω')
    (e₁ := A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm) (e₂ := A.splitG sp H₁)
    (A.oraclePerm_splitG sp H₁ E E' ω ω' hor j)
  have hd : ∀ M : Matrix A.toKindAlg.G A.toKindAlg.G ℂ,
      (KrausMap.measureFn ((A.restrictAt sp H₁).toKindAlg.logAt j))
        (M.submatrix (A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm)
          (A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm)) =
      ((KrausMap.measureFn (A.toKindAlg.logAt j)) M).submatrix
        (A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm)
        (A.splitG sp H₁ ∘ (A.baseG sp H₁ (slotStep j)).symm) := fun M => by
    rw [KrausMap.measureFn_apply, KrausMap.measureFn_apply, A.logAt_splitG sp H₁ (slotStep j) j,
      dephase_submatrix]
  cases deph
  · simp only [KindAlg.eventCirc, Bool.false_eq_true, ↓reduceIte, id, Circuit.run]
    rw [h1, hc, hr, ho]
  · simp only [KindAlg.eventCirc, ↓reduceIte, Circuit.run]
    rw [h1, hc, hd, hr, ho]

/-- **Post batch `b` of the restricted mixed game** acts on matrices read along `splitG` as post
batch `b` of the adversary's. -/
theorem post_restrictAt
    (hor : ∀ (lg : LogReg Req A.slots) x, E.oracle ω lg x = sp.symm (H₁ x, E'.oracle ω' lg x))
    (b : Fin A.post) (σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ) :
    (Circuit.kraus ((A.restrictAt sp H₁).toKindAlg.liftG (postStep b))
        (.kraus (KrausMap.ofPerm ((A.restrictAt sp H₁).toKindAlg.postG E' ω')) .nil)).run
        (Equiv.refl _) (σ.submatrix (A.splitG sp H₁) (A.splitG sp H₁)) =
      ((Circuit.kraus (A.toKindAlg.liftG (postStep b))
        (.kraus (KrausMap.ofPerm (A.toKindAlg.postG E ω)) .nil)).run
        (Equiv.refl _) σ).submatrix (A.splitG sp H₁) (A.splitG sp H₁) := by
  have h1 : ((A.restrictAt sp H₁).toKindAlg.liftG (postStep b))
      (σ.submatrix (A.splitG sp H₁) (A.splitG sp H₁)) = ((A.toKindAlg.liftG (postStep b)) σ).submatrix
        (A.splitG sp H₁ ∘ (A.baseG sp H₁ (postStep b)).symm)
        (A.splitG sp H₁ ∘ (A.baseG sp H₁ (postStep b)).symm) :=
    KrausMap.apply_submatrix_of_op (A.splitG sp H₁) (A.liftG_restrictAt_op sp H₁ (postStep b)) σ
  have ho := KrausMap.ofPerm_submatrix_of_comm (π := A.toKindAlg.postG E ω)
    (π' := (A.restrictAt sp H₁).toKindAlg.postG E' ω')
    (e₁ := A.splitG sp H₁ ∘ (A.baseG sp H₁ (postStep b)).symm) (e₂ := A.splitG sp H₁)
    (A.postG_splitG sp H₁ E E' ω ω' hor b)
  simp only [Circuit.run]
  rw [h1, ho]

/-- **The last Kraus map of the restricted mixed game** acts on matrices read along `splitG` as
the adversary's. -/
theorem last_restrictAt (σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ) :
    ((A.restrictAt sp H₁).toKindAlg.liftG lastStep)
        (σ.submatrix (A.splitG sp H₁) (A.splitG sp H₁)) =
      ((A.toKindAlg.liftG lastStep) σ).submatrix (A.splitG sp H₁) (A.splitG sp H₁) := by
  have h1 : ((A.restrictAt sp H₁).toKindAlg.liftG lastStep)
      (σ.submatrix (A.splitG sp H₁) (A.splitG sp H₁)) = ((A.toKindAlg.liftG lastStep) σ).submatrix
        (A.splitG sp H₁ ∘ (A.baseG sp H₁ lastStep).symm)
        (A.splitG sp H₁ ∘ (A.baseG sp H₁ lastStep).symm) :=
    KrausMap.apply_submatrix_of_op (A.splitG sp H₁) (A.liftG_restrictAt_op sp H₁ lastStep) σ
  rw [h1]
  have he : (A.splitG sp H₁ ∘ (A.baseG sp H₁ lastStep).symm) = A.splitG sp H₁ :=
    funext fun g => congrArg (A.splitG sp H₁) (A.baseG_lastStep_symm_apply sp H₁ g)
  rw [he]

/-- **The restricted mixed game is the adversary's read along the relabelling**: against an
environment `E'` of the oracle `X → Y₂` at the tape `ω'`, and an environment `E` of `X → Y` at
`ω` with the same replies (`hans`) whose oracles in force are joined from `H₁` and those of `E'`
(`hor`), the final state of the mixed game of `A.restrictAt sp H₁` is that of `A` read along
`splitG`. -/
theorem mgRun_restrictAt (hans : ∀ (lg : LogReg Req A.slots) i, E.answer ω lg i = E'.answer ω' lg i)
    (hor : ∀ (lg : LogReg Req A.slots) x, E.oracle ω lg x = sp.symm (H₁ x, E'.oracle ω' lg x))
    (deph : Bool) :
    (A.restrictAt sp H₁).toKindAlg.mgRun E' ω' deph =
      (A.toKindAlg.mgRun E ω deph).submatrix (A.splitG sp H₁) (A.splitG sp H₁) := by
  simp only [KindAlg.mgRun, KindAlg.mgCirc, Circuit.run_append]
  rw [mgInit_restrictAt, Circuit.run_concat_map_submatrix (A.splitG sp H₁) _ _ ?hs,
    Circuit.run_concat_map_submatrix (A.splitG sp H₁) _ _ ?hp]
  · simp only [Circuit.run]
    exact A.last_restrictAt sp H₁ _
  case hs =>
    intro j σ
    exact A.slot_restrictAt sp H₁ E E' ω ω' hans hor deph j σ
  case hp =>
    intro b σ
    exact A.post_restrictAt sp H₁ E E' ω ω' hor b σ

end AdaptiveIAlg

/-! ### The challenger at a fixed base part -/

namespace Challenger

variable {X Y Y₁ Y₂ Req Resp : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) (C : Challenger X Y Req Resp)

/-- **The challenger at the base part `H₁` of the split `sp`**, a challenger of the oracle
`X → Y₂`: `C`'s coins, request bound and query bound; its reply program is `C`'s translated
(`OracleProg.translate`) so that the answer `y₂` to a query `x` is read as `sp.symm (H₁ x, y₂)`,
with the reply's response kept and its assignments dropped (it reprograms nothing,
`noAssign_restrictAt`; the law theorems assume that `C` reprograms nothing). -/
abbrev restrictAt : Challenger X Y₂ Req Resp where
  Coins := C.Coins
  coins := C.coins
  Q := C.Q
  q := C.q
  respond c hist r := ((C.respond c hist r).translate id fun x y₂ => sp.symm (H₁ x, y₂)).mapOutput
    fun o => ⟨o.response, []⟩
  respond_queries c hist r H₂ := by
    rw [OracleProg.trace_mapOutput, OracleProg.trace_translate, List.length_map]
    exact C.respond_queries _ _ _ _

/-- The reply programs of the restricted challenger are `C`'s, translated. -/
theorem restrictAt_respond (c : C.Coins) (hist : List (HistoryEntry Req Resp)) (r : Req) :
    (C.restrictAt sp H₁).respond c hist r =
      ((C.respond c hist r).translate id fun x y₂ => sp.symm (H₁ x, y₂)).mapOutput
        fun o => ⟨o.response, []⟩ :=
  rfl

/-- **The reply of the restricted challenger** at the `Y₂`-oracle `H₂` is `C`'s response at the
oracle joined from `H₁` and `H₂`, with no assignments. -/
theorem run_respond_restrictAt (c : C.Coins) (hist : List (HistoryEntry Req Resp)) (r : Req)
    (H₂ : X → Y₂) :
    ((C.restrictAt sp H₁).respond c hist r).run H₂ =
      ⟨((C.respond c hist r).run fun x => sp.symm (H₁ x, H₂ x)).response, []⟩ := by
  rw [restrictAt_respond, OracleProg.run_mapOutput, OracleProg.run_translate]
  rfl

/-- **The restricted challenger reprograms nothing.** -/
theorem noAssign_restrictAt : (C.restrictAt sp H₁).NoAssign := fun c hist r G =>
  congrArg Reply.assignments (run_respond_restrictAt sp H₁ C c hist r G)

section Env

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Y₂] [Nonempty Y₂]

/-- **The restricted challenger keeps `C`'s history**, for a challenger that reprograms nothing:
after any requests, its history at the `Y₂`-oracle `H₂` is `C`'s at the oracle joined from `H₁` and
`H₂`. -/
theorem hist_oracleIn_restrictAt (hC : C.NoAssign) (H₂ : X → Y₂) (c : C.Coins) (rs : List Req) :
    ((C.restrictAt sp H₁).toPureEnv.oracleIn (H₂, c) rs).hist =
      (C.toPureEnv.oracleIn (fun x => sp.symm (H₁ x, H₂ x), c) rs).hist := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [Env.oracleIn_append_singleton, Env.oracleIn_append_singleton]
    by_cases hq : rs.length < C.Q
    · obtain ⟨h1, h2, -⟩ := (C.noAssign_restrictAt sp H₁).oracleIn H₂ c rs
      rw [update_toPureEnv_of_lt (C.restrictAt sp H₁) _ _ _ hq, update_toPureEnv_of_lt C _ _ _ hq]
      simp only
      obtain ⟨h1', h2', -⟩ := hC.oracleIn (fun x => sp.symm (H₁ x, H₂ x)) c rs
      rw [h1, h2, ih, h1', h2']
      congr 3
      exact congrArg Reply.response (run_respond_restrictAt sp H₁ C c _ r H₂)
    · rw [update_toPureEnv_of_le (C.restrictAt sp H₁) _ _ _ (not_lt.1 hq),
        update_toPureEnv_of_le C _ _ _ (not_lt.1 hq), ih]

/-- **The restricted challenger answers as `C`** at the joined oracle, for a challenger that
reprograms nothing. -/
theorem answer_restrictAt (hC : C.NoAssign) (H₂ : X → Y₂) (c : C.Coins) {m : ℕ}
    (lg : LogReg Req m) (k : Fin m) :
    (C.restrictAt sp H₁).toPureEnv.answer (H₂, c) lg k =
      C.toPureEnv.answer (fun x => sp.symm (H₁ x, H₂ x), c) lg k := by
  simp only [Env.answer]
  congr 1
  funext r
  by_cases h : (requestsBefore lg k).length < C.Q
  · rw [(C.noAssign_restrictAt sp H₁).answerAfter_eq H₂ c _ r h, hC.answerAfter_eq _ c _ r h,
      hist_oracleIn_restrictAt sp H₁ C hC, run_respond_restrictAt]
  · simp only [Env.answerAfter, h, ↓reduceDIte]

/-- **The oracles in force**: the joined oracle and `H₂`, for a challenger that reprograms
nothing. -/
theorem oracle_restrictAt (hC : C.NoAssign) (H₂ : X → Y₂) (c : C.Coins) {m : ℕ}
    (lg : LogReg Req m) (x : X) :
    C.toPureEnv.oracle (fun x => sp.symm (H₁ x, H₂ x), c) lg x =
      sp.symm (H₁ x, (C.restrictAt sp H₁).toPureEnv.oracle (H₂, c) lg x) := by
  rw [hC.oracle_eq, (C.noAssign_restrictAt sp H₁).oracle_eq]

end Env

end Challenger

/-! ### An environment of the `Y₂`-oracle read as one of the joined oracle -/

/-- **A state of an environment of the oracle `X → Y₂`, read at the base part `H₁`**: its oracle in
force is joined from `H₁` and the state's (`instOracleStateSplitState`). -/
structure SplitState {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
    (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) (St : Type) where
  /-- The state. -/
  st : St

instance instOracleStateSplitState {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
    (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) (St : Type) [OracleState St X Y₂] :
    OracleState (SplitState sp H₁ St) X Y :=
  ⟨fun s x => sp.symm (H₁ x, OracleState.toOracle (X := X) (Y := Y₂) s.st x)⟩

namespace Env

variable {X Y Y₁ Y₂ Req Resp Ω St : Type} {Q : ℕ} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) [OracleState St X Y₂] (E : Env Ω Req Resp X Y₂ Q St)

/-- **An environment of the oracle `X → Y₂` read at the base part `H₁`**: the same tape, replies
and states, with the oracles in force joined from `H₁` and `E`'s. -/
def splitLift : Env Ω Req Resp X Y Q (SplitState sp H₁ St) where
  μ := E.μ
  oracle₀ ω := ⟨E.oracle₀ ω⟩
  respond ω i req s := ⟨(E.respond ω i req s.st).response, ⟨(E.respond ω i req s.st).state⟩⟩

omit [OracleState St X Y₂] in
/-- The states of the lifted environment are `E`'s. -/
theorem oracleIn_splitLift (ω : Ω) (rs : List Req) :
    (E.splitLift sp H₁).oracleIn ω rs = ⟨E.oracleIn ω rs⟩ := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [oracleIn_append_singleton, oracleIn_append_singleton, ih]
    simp only [update]
    split_ifs <;> rfl

omit [OracleState St X Y₂] in
/-- The lifted environment has `E`'s replies. -/
theorem answer_splitLift (ω : Ω) {m : ℕ} (lg : LogReg Req m) (k : Fin m) :
    (E.splitLift sp H₁).answer ω lg k = E.answer ω lg k := by
  simp only [answer]
  congr 1
  funext r
  unfold answerAfter
  rw [oracleIn_splitLift]
  rfl

/-- The lifted environment's oracles in force are joined from `H₁` and `E`'s. -/
theorem oracle_splitLift (ω : Ω) {m : ℕ} (lg : LogReg Req m) (x : X) :
    (E.splitLift sp H₁).oracle ω lg x = sp.symm (H₁ x, E.oracle ω lg x) := by
  simp only [oracle, oracleIn_splitLift]
  rfl

end Env

/-! ### The law of the composition at a fixed base part -/

namespace AdaptiveIAlg

variable {X Y Y₁ Y₂ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Nonempty X]
  [Nonempty Y] [Nonempty Y₂]
  (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (C : Challenger X Y Req Resp)

/-- **The output and the history read from the placed restricted game registers** are those read
from the adversary's placed game registers, at the joined oracle. -/
theorem readout_emb_restrictAt (hC : C.NoAssign) {O' : Type}
    (g : O → List (HistoryEntry Req Resp) → O') (H₂ : X → Y₂) (c : C.Coins)
    (r : (A.restrictAt sp H₁).toKindAlg.G) :
    g ((A.restrictAt sp H₁).output (C.restrictAt sp H₁) ((A.restrictAt sp H₁).toKindAlg.emb
        (C.restrictAt sp H₁) H₂ c (A.restrictAt sp H₁).toKindAlg.slots r).1)
      ((A.restrictAt sp H₁).history (C.restrictAt sp H₁) ((A.restrictAt sp H₁).toKindAlg.emb
        (C.restrictAt sp H₁) H₂ c (A.restrictAt sp H₁).toKindAlg.slots r).1) =
    g (A.output C (A.toKindAlg.emb C (fun x => sp.symm (H₁ x, H₂ x)) c A.toKindAlg.slots
        (A.splitG sp H₁ r)).1)
      (A.history C (A.toKindAlg.emb C (fun x => sp.symm (H₁ x, H₂ x)) c A.toKindAlg.slots
        (A.splitG sp H₁ r)).1) := by
  have e1 : (A.restrictAt sp H₁).history (C.restrictAt sp H₁) ((A.restrictAt sp H₁).toKindAlg.emb
      (C.restrictAt sp H₁) H₂ c (A.restrictAt sp H₁).toKindAlg.slots r).1 =
      ((C.restrictAt sp H₁).stateAfter H₂ c (requestsBefore (splitLogs r).2 A.slots)).hist :=
    congrArg ChallengerRecord.history ((A.restrictAt sp H₁).toKindAlg.regState_eq
      (C.restrictAt sp H₁) H₂ c (splitLogs r).2 (J := A.slots) A.slots le_rfl)
  have e2 : A.history C (A.toKindAlg.emb C (fun x => sp.symm (H₁ x, H₂ x)) c A.toKindAlg.slots
      (A.splitG sp H₁ r)).1 = (C.stateAfter (fun x => sp.symm (H₁ x, H₂ x)) c
        (requestsBefore (splitLogs (A.splitG sp H₁ r)).2 A.slots)).hist :=
    congrArg ChallengerRecord.history (A.toKindAlg.regState_eq C (fun x => sp.symm (H₁ x, H₂ x)) c
      (splitLogs (A.splitG sp H₁ r)).2 (J := A.slots) A.slots le_rfl)
  rw [e1, e2]
  obtain ⟨⟨⟨⟨w, ys⟩, cnt⟩, rq, rs, lg⟩, p⟩ := r
  exact congrArg (g _) (Challenger.hist_oracleIn_restrictAt sp H₁ C hC H₂ c _)

/-- **The law of the composition at a fixed base part** (the joined form): for a challenger `C`
that reprograms nothing and every readout `g` of the adversary's output and the history, the
output law of the restricted adversary composed with the restricted challenger at the `Y₂`-oracle
`H₂` is the output law of `A` composed with `C` at the oracle joined from `H₁` and `H₂`. -/
theorem outLaw_composeBothOut_restrictAt_join (hC : C.NoAssign) {O' : Type}
    (g : O → List (HistoryEntry Req Resp) → O') (H₂ : X → Y₂) :
    ((A.restrictAt sp H₁).toKindAlg.composeBothOut (C.restrictAt sp H₁) fun v =>
        g ((A.restrictAt sp H₁).output (C.restrictAt sp H₁) v)
          ((A.restrictAt sp H₁).history (C.restrictAt sp H₁) v)).outLaw H₂ =
      (A.toKindAlg.composeBothOut C fun v => g (A.output C v) (A.history C v)).outLaw
        (fun x => sp.symm (H₁ x, H₂ x)) := by
  classical
  refine PMF.ext_of_apply_some fun o => ?_
  refine ((A.restrictAt sp H₁).toKindAlg.outLaw_composeBothOut_some (C.restrictAt sp H₁) _ H₂
    o).trans (Eq.trans ?_ (A.toKindAlg.outLaw_composeBothOut_some C _ _ o).symm)
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hm := A.mgRun_restrictAt sp H₁ C.toPureEnv (C.restrictAt sp H₁).toPureEnv
    (fun x => sp.symm (H₁ x, H₂ x), c) (H₂, c)
    (fun lg i => (Challenger.answer_restrictAt sp H₁ C hC H₂ c lg i).symm)
    (fun lg x => Challenger.oracle_restrictAt sp H₁ C hC H₂ c lg x) true
  rw [← (A.splitG sp H₁).sum_comp]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hm, submatrix_apply, A.readout_emb_restrictAt sp H₁ C hC g H₂ c r]

/-- **The law of the composition at the base part of the oracle**: for a challenger `C` that
reprograms nothing, every oracle `H` and every readout `g` of the adversary's output and the
history, the restricted adversary and challenger at the base part `fun x => (sp (H x)).1`,
composed at the oracle `fun x => (sp (H x)).2`, have the output law of `A` composed with `C` at
`H`. -/
theorem outLaw_composeBothOut_restrictAt (hC : C.NoAssign) {O' : Type}
    (g : O → List (HistoryEntry Req Resp) → O') (H : X → Y) :
    ((A.restrictAt sp fun x => (sp (H x)).1).toKindAlg.composeBothOut
        (C.restrictAt sp fun x => (sp (H x)).1) fun v =>
        g ((A.restrictAt sp fun x => (sp (H x)).1).output (C.restrictAt sp fun x => (sp (H x)).1) v)
          ((A.restrictAt sp fun x => (sp (H x)).1).history
            (C.restrictAt sp fun x => (sp (H x)).1) v)).outLaw (fun x => (sp (H x)).2) =
      (A.toKindAlg.composeBothOut C fun v => g (A.output C v) (A.history C v)).outLaw H := by
  rw [A.outLaw_composeBothOut_restrictAt_join sp _ C hC g]
  congr 1
  funext x
  simp

end AdaptiveIAlg

namespace AdaptiveIAlg

variable {X Y Y₁ Y₂ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Nonempty X]
  [Nonempty Y] [Nonempty Y₂]
  (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **The restricted adversary stays within its budget** when `A` does: against every challenger
of the oracle `X → Y₂` at every oracle and coins, its mixed game is `A`'s against the lifted
environment (`Env.splitLift`) read along `splitG`, which keeps the trace
(`WithinBudget.trace_mgRun_eq_one`). -/
theorem withinBudget_restrictAt (hA : A.WithinBudget) : (A.restrictAt sp H₁).WithinBudget := by
  refine (withinBudget_iff (A.restrictAt sp H₁)).2 fun C' H' => ?_
  rw [AdaptiveIAlg.outLaw_compose_none_eq, ENNReal.ofReal_eq_zero, sub_nonpos]
  have htr : ∀ M : Matrix A.toKindAlg.G A.toKindAlg.G ℂ,
      (M.submatrix (A.splitG sp H₁) (A.splitG sp H₁)).trace = M.trace := fun M => by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact Equiv.sum_comp (A.splitG sp H₁) fun i => M i i
  have h : ∀ c', ((A.restrictAt sp H₁).toKindAlg.mgRun C'.toPureEnv (H', c') true).trace.re = 1 := by
    intro c'
    rw [A.mgRun_restrictAt sp H₁ (C'.toPureEnv.splitLift sp H₁) C'.toPureEnv (H', c') (H', c')
      (fun lg i => Env.answer_splitLift sp H₁ _ _ lg i)
      (fun lg x => Env.oracle_splitLift sp H₁ _ _ lg x) true, htr]
    exact (congrArg Complex.re (hA.trace_mgRun_eq_one _ _)).trans Complex.one_re
  simp only [h, mul_one]
  have hsum : ∑ c', C'.coins c' = 1 := by
    rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  rw [← ENNReal.toReal_sum fun c _ => PMF.apply_ne_top _ c, hsum, ENNReal.toReal_one]

end AdaptiveIAlg

namespace QueryBoundedAdversary

variable {X Y Y₁ Y₂ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Nonempty X]
  [Nonempty Y] [Nonempty Y₂] {t : ℕ}
  (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) (A : QueryBoundedAdversary X Y Req Resp O t)

/-- **A `t`-query adversary at the base part `H₁`**: the same auxiliary input, and on each value
the adversary at the base part (`AdaptiveIAlg.restrictAt`), a `t`-query adversary of the oracle
`X → Y₂` (its width, budget and post batches are `A`'s). -/
def restrictAt : QueryBoundedAdversary X Y₂ Req Resp O t where
  Aux := A.Aux
  aux := A.aux
  sh a := (A.sh a).restrictAtS Y₁ Y₂
  alg a := (A.alg a).restrictAt sp H₁
  tracePreserving a := (A.alg a).tracePreserving_restrictAt sp H₁ (A.tracePreserving a)
  withinBudget a := (A.alg a).withinBudget_restrictAt sp H₁ (A.withinBudget a)
  queries_le a := A.queries_le a

/-- The shape of the adversary at the base part is `A`'s restricted (`AlgShape.restrictAtS`). -/
@[simp] theorem restrictAt_sh (a : (A.restrictAt sp H₁).Aux) :
    (A.restrictAt sp H₁).sh a = (A.sh a).restrictAtS Y₁ Y₂ :=
  rfl

/-- The adversary at the base part on an auxiliary value is `A`'s on it at the base part. -/
theorem alg_restrictAt (a : (A.restrictAt sp H₁).Aux) :
    (A.restrictAt sp H₁).alg a = (A.alg a).restrictAt sp H₁ :=
  rfl

/-- The adversary at the base part has `A`'s auxiliary input. -/
theorem aux_restrictAt (a : (A.restrictAt sp H₁).Aux) : (A.restrictAt sp H₁).aux a = A.aux a :=
  rfl

/-- **The transcript law at a fixed base part** (the joined form): for a challenger `C` that
reprograms nothing, the transcript law of the restricted adversary against the restricted
challenger at `H₂` is `A`'s against `C` at the oracle joined from `H₁` and `H₂`. -/
theorem transcriptLaw_restrictAt_join (C : Challenger X Y Req Resp) (hC : C.NoAssign)
    (H₂ : X → Y₂) :
    (A.restrictAt sp H₁).transcriptLaw (C.restrictAt sp H₁) H₂ =
      A.transcriptLaw C (fun x => sp.symm (H₁ x, H₂ x)) := by
  simp only [transcriptLaw]
  congr 1
  funext a
  exact (A.alg a).outLaw_composeBothOut_restrictAt_join sp H₁ C hC Prod.mk H₂

/-- **The transcript law at the base part of the oracle**: for a challenger `C` that reprograms
nothing and every oracle `H`, the transcript law of the adversary and the challenger at the base
part `fun x => (sp (H x)).1`, at the oracle `fun x => (sp (H x)).2`, is `A`'s against `C` at `H`. -/
theorem transcriptLaw_restrictAt (C : Challenger X Y Req Resp) (hC : C.NoAssign) (H : X → Y) :
    (A.restrictAt sp fun x => (sp (H x)).1).transcriptLaw (C.restrictAt sp fun x => (sp (H x)).1)
        (fun x => (sp (H x)).2) = A.transcriptLaw C H := by
  rw [transcriptLaw_restrictAt_join sp _ A C hC]
  congr 1
  funext x
  simp

end QueryBoundedAdversary

/-! ### The construction at a trivial base part -/

/-- **With a trivial base component the local query is the identity**: for `Y₁` with one element,
`basePerm` moves nothing, so the restricted adversary's Kraus maps are `A`'s read along
`splitReg`. -/
theorem basePerm_of_subsingleton {X Y₁ Y₂ W Req Resp : Type} [AddGroup Y₁] [AddGroup Y₂]
    [Subsingleton Y₁] (H₁ : X → Y₁) (on : W → Bool) (n : ℕ) :
    basePerm (Y₂ := Y₂) H₁ on n Req Resp = Equiv.refl _ := by
  ext d <;> first | rfl | exact Subsingleton.elim _ _

end GordieHowe.Quantum
