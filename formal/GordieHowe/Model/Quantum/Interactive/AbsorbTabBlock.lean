-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BlockRel
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeCirc

@[expose] public section

/-!
# The block hypotheses for an adversary absorbed with a table

For an adversary `A` with other Kraus maps `st'` and a relay `F`:

- `AdaptiveIAlg.absorbTabStep`, `AdaptiveIAlg.absorbTab_withStep`: the Kraus maps `st'` read
  through the absorption with a table.
- `AdaptiveIAlg.tabPart`, `AdaptiveIAlg.tabRest`, `AdaptiveIAlg.tabSplit`: `A`'s registers and the
  others inside those of the absorbed adversary; `AdaptiveIAlg.stepTab_op_apply`: the entries of
  the absorbed step, `A`'s step between the permutations of the step, the identity on the other
  registers; `AdaptiveIAlg.rowGram_stepTab`: its overlaps into a block.
- `AdaptiveIAlg.tabSet`: the well-formed states of the absorbed adversary at an index (`A`'s
  registers in the set of the index, the logs blank after it, the inner request register blank
  or the route of the index's log); `AdaptiveIAlg.keepsSet_stepTab`,
  `AdaptiveIAlg.keepsBlocksOn_stepTab`: the absorbed step moves them along and keeps the blocks.
- `AdaptiveIAlg.BlockNone.absorbTab`: the `none`-block hypotheses through the absorption.
- `AdaptiveIAlg.jTrip`, `AdaptiveIAlg.tTrip`: the witness swap `sw` of the request at the slot
  recorded by `J`, on `A`'s registers and on the absorbed ones (with the recorded slot's log and
  the inner request); `TwoRelay.SwapInv`: a relay that does not see `sw`;
  `AdaptiveIAlg.JSlotStep`: the recorded slot changes only at its step.
- `AdaptiveIAlg.BlockRel.absorbTab`: the block hypotheses along `jTrip` give those of the
  absorbed adversaries along `tTrip` and `tabSet`.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM KrausRel

/-- **`σ` on every entry of a log register.** -/
def logPerm {Req : Type} {m : ℕ} (σ : Equiv.Perm Req) : Equiv.Perm (LogReg Req m) :=
  Equiv.piCongrRight fun _ => Equiv.optionCongr σ

theorem logPerm_apply {Req : Type} {m : ℕ} (σ : Equiv.Perm Req) (lg : LogReg Req m) (k : Fin m) :
    logPerm σ lg k = (lg k).map σ :=
  rfl

/-- **The requests before a slot of the relabelled logs** are the relabelled requests. -/
theorem requestsBefore_logPerm {Req : Type} {m : ℕ} (σ : Equiv.Perm Req) (lg : LogReg Req m) :
    ∀ k, requestsBefore (logPerm σ lg) k = (requestsBefore lg k).map σ
  | 0 => rfl
  | k + 1 => by
    rw [requestsBefore, requestsBefore, requestsBefore_logPerm σ lg k, List.map_append]
    split_ifs
    · rw [logPerm_apply]
      cases lg _ <;> rfl
    · rfl

/-- A swap carried along a permutation. -/
theorem swap_apply_perm {α : Type*} [DecidableEq α] (e : Equiv.Perm α) (a b x : α) :
    Equiv.swap (e a) (e b) (e x) = e (Equiv.swap a b x) := by
  rw [Equiv.swap_apply_apply]
  simp

/-- **A permutation of each log entry**: `e i` on entry `i`. -/
def logFam {Req : Type} {m : ℕ} (e : Fin m → Equiv.Perm Req) : Equiv.Perm (LogReg Req m) :=
  Equiv.piCongrRight fun i => Equiv.optionCongr (e i)

theorem logFam_apply {Req : Type} {m : ℕ} (e : Fin m → Equiv.Perm Req) (lg : LogReg Req m)
    (i : Fin m) : logFam e lg i = (lg i).map (e i) :=
  rfl

/-- **The requests before a slot of logs permuted entrywise** are the requests, each permuted by
some entry's permutation. -/
theorem requestsBefore_logFam {Req : Type} {m : ℕ} (e : Fin m → Equiv.Perm Req)
    (lg : LogReg Req m) : ∀ k, List.Forall₂ (fun a b => ∃ i, a = e i b)
      (requestsBefore (logFam e lg) k) (requestsBefore lg k)
  | 0 => List.Forall₂.nil
  | k + 1 => by
    rw [requestsBefore, requestsBefore]
    refine List.rel_append (requestsBefore_logFam e lg k) ?_
    split_ifs with hk
    · rw [logFam_apply]
      cases lg ⟨k, hk⟩ with
      | none => exact List.Forall₂.nil
      | some q => exact List.Forall₂.cons ⟨⟨k, hk⟩, rfl⟩ List.Forall₂.nil
    · exact List.Forall₂.nil

theorem length_requestsBefore_logFam {Req : Type} {m : ℕ} (e : Fin m → Equiv.Perm Req)
    (lg : LogReg Req m) (k : ℕ) :
    (requestsBefore (logFam e lg) k).length = (requestsBefore lg k).length :=
  (requestsBefore_logFam e lg k).length_eq

/-- **Filtered indexed lists of related elements** have the same length, for a filter that does
not distinguish related elements. -/
theorem length_filter_zipIdx_of_forall₂ {α : Type*} {R : α → α → Prop} {P : α × ℕ → Bool}
    (hP : ∀ a b n, R a b → P (a, n) = P (b, n)) {l' l : List α} (h : List.Forall₂ R l' l) :
    ∀ n, ((l'.zipIdx n).filter P).length = ((l.zipIdx n).filter P).length := by
  induction h with
  | nil => intro n; rfl
  | @cons a b l' l hab _ ih =>
    intro n
    simp only [List.zipIdx_cons, List.filter_cons, hP a b n hab]
    split_ifs
    · simp [ih (n + 1)]
    · exact ih (n + 1)

/-- **A permutation if a condition holds**, else the identity. -/
def swIf {α : Type*} (p : Prop) [Decidable p] (e : Equiv.Perm α) : Equiv.Perm α :=
  if p then e else Equiv.refl α

theorem swIf_congr {α : Type*} {p p' : Prop} [Decidable p] [Decidable p'] (e : Equiv.Perm α)
    (h : p ↔ p') : swIf p e = swIf p' e := by
  unfold swIf
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.1 h1) h2
  · exact absurd (h.2 h2) h1
  · rfl

theorem swIf_apply_of_not {α : Type*} {p : Prop} [Decidable p] (e : Equiv.Perm α) (h : ¬ p)
    (x : α) : swIf p e x = x := by
  simp [swIf, h]

theorem swIf_apply_of {α : Type*} {p : Prop} [Decidable p] (e : Equiv.Perm α) (h : p) (x : α) :
    swIf p e x = e x := by
  simp [swIf, h]

namespace TwoRelay

variable {Req Resp Req₁ Resp₁ Req₂ Resp₂ : Type} (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

/-- **A relay that does not see a permutation `sw` of the requests**: the route of `sw q` is
`σ₁` of `q`'s, the outer requests and the replies are `q`'s, and `σ₁` fixes the blank inner
request. -/
structure SwapInv [Inhabited Req₁] (sw : Equiv.Perm Req) (σ₁ : Equiv.Perm Req₁) : Prop where
  /-- The route. -/
  route : ∀ c q, F.route₁ c (sw q) = σ₁ (F.route₁ c q)
  /-- The outer requests. -/
  outer : ∀ c q, F.outer c (sw q) = F.outer c q
  /-- The replies from the inner reply. -/
  answer₁ : ∀ c q a, F.answer₁ c (sw q) a = F.answer₁ c q a
  /-- The replies from the outer reply. -/
  answer₂ : ∀ c q b, F.answer₂ c (sw q) b = F.answer₂ c q b
  /-- The blank inner request is fixed. -/
  default : σ₁ default = default

variable {F}

theorem SwapInv.outer_swIf [Inhabited Req₁] {sw : Equiv.Perm Req} {σ₁ : Equiv.Perm Req₁}
    (h : F.SwapInv sw σ₁) (p : Prop) [Decidable p] (c : ℕ) (q : Req) :
    F.outer c (swIf p sw q) = F.outer c q := by
  by_cases hp : p
  · rw [swIf_apply_of _ hp, h.outer]
  · rw [swIf_apply_of_not _ hp]

theorem SwapInv.route_swIf [Inhabited Req₁] {sw : Equiv.Perm Req} {σ₁ : Equiv.Perm Req₁}
    (h : F.SwapInv sw σ₁) (p : Prop) [Decidable p] (c : ℕ) (q : Req) :
    F.route₁ c (swIf p sw q) = swIf p σ₁ (F.route₁ c q) := by
  by_cases hp : p
  · rw [swIf_apply_of _ hp, swIf_apply_of _ hp, h.route]
  · rw [swIf_apply_of_not _ hp, swIf_apply_of_not _ hp]

theorem SwapInv.answer₁_swIf [Inhabited Req₁] {sw : Equiv.Perm Req} {σ₁ : Equiv.Perm Req₁}
    (h : F.SwapInv sw σ₁) (p : Prop) [Decidable p] (c : ℕ) (q : Req) (a : Option Resp₁) :
    F.answer₁ c (swIf p sw q) a = F.answer₁ c q a := by
  by_cases hp : p
  · rw [swIf_apply_of _ hp, h.answer₁]
  · rw [swIf_apply_of_not _ hp]

theorem SwapInv.answer₂_swIf [Inhabited Req₁] {sw : Equiv.Perm Req} {σ₁ : Equiv.Perm Req₁}
    (h : F.SwapInv sw σ₁) (p : Prop) [Decidable p] (c : ℕ) (q : Req) (b : Option Resp₂) :
    F.answer₂ c (swIf p sw q) b = F.answer₂ c q b := by
  by_cases hp : p
  · rw [swIf_apply_of _ hp, h.answer₂]
  · rw [swIf_apply_of_not _ hp]

theorem SwapInv.default_swIf [Inhabited Req₁] {sw : Equiv.Perm Req} {σ₁ : Equiv.Perm Req₁}
    (h : F.SwapInv sw σ₁) (p : Prop) [Decidable p] :
    swIf p σ₁ (Inhabited.default : Req₁) = Inhabited.default := by
  by_cases hp : p
  · rw [swIf_apply_of _ hp, h.default]
  · rw [swIf_apply_of_not _ hp]

end TwoRelay

namespace AdaptiveIAlg

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)
  (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp))

/-- **The Kraus maps `st'` through the absorption with a table**, as `absorbTab` reads `A`'s. -/
def absorbTabStep : StepIdx A.slots A.post →
    KrausMap (A.absorb F.base).R
      (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
      (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :=
  (A.withStep st').stepTab F

/-- **The adversary with the Kraus maps `st'`, absorbed with a table**, is the absorbed adversary
with the Kraus maps `absorbTabStep`. -/
theorem absorbTab_withStep (tab : A.OuterTab Req₂ Resp₂) :
    (A.withStep st').absorbTab F tab = (A.absorbTab F tab).withStep (A.absorbTabStep F st') :=
  rfl

variable {A F}

variable (A F) in
/-- The adversary's registers inside those of the adversary absorbed with a table. -/
def tabPart (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    DReg A.W A.width X Y Req Resp :=
  (A.absSplit (((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)) d).1).1

variable (A F) in
/-- The other registers of the adversary absorbed with a table. -/
def tabRest (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂ :=
  ((A.absSplit (((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)) d).1).2,
    (((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)) d).2)

variable (A F) in
/-- **The entries of the step of the adversary absorbed with a table**: `A`'s step on its
registers between the permutations of the step, the identity on the others. -/
theorem stepTab_op_apply (k : StepIdx A.slots A.post) (i : (A.absorb F.base).R)
    (y x : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.stepTab F k).op i y x =
      (A.step k).op i.1.2 (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm y))
        (A.tabPart F (A.afterAtTab F k x)) *
      (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁)) _ ℂ)
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm y)).1
        (A.tabRest F (A.afterAtTab F k x)).1 *
      (1 : Matrix (A.OuterTab Req₂ Resp₂) _ ℂ)
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm y)).2
        (A.tabRest F (A.afterAtTab F k x)).2 := by
  rw [stepTab_eq, KrausMap.ofPerm_comp_comp_op_apply]
  rfl

variable (A F) in
theorem withStep_stepTab_op_apply (k : StepIdx A.slots A.post) (i : (A.absorb F.base).R)
    (y x : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    ((A.withStep st').stepTab F k).op i y x =
      (st' k).op i.1.2 (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm y))
        (A.tabPart F (A.afterAtTab F k x)) *
      (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁)) _ ℂ)
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm y)).1
        (A.tabRest F (A.afterAtTab F k x)).1 *
      (1 : Matrix (A.OuterTab Req₂ Resp₂) _ ℂ)
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm y)).2
        (A.tabRest F (A.afterAtTab F k x)).2 :=
  stepTab_op_apply (A.withStep st') F k i y x

omit [Fintype Req₁] [Fintype Resp₁] in
theorem work_storePerm (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    (A.storePerm j d).1.1.work = d.1.1.work := by
  unfold storePerm AlgShape.storePerm
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
  split_ifs <;> rfl

theorem work_answerPermTab (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    (A.answerPermTab F t j d).1.1.work = d.1.1.work := by
  unfold answerPermTab
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
  split <;> rfl

theorem work_clearPerm (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    (A.clearPerm F.base j d).1.1.work = d.1.1.work := by
  unfold clearPerm AlgShape.clearPerm
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
  split <;> rfl

theorem work_afterAtTab (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.afterAtTab F k d).1.1.1.work = d.1.1.1.work := by
  unfold afterAtTab
  split_ifs with hk
  · obtain ⟨⟨⟨w, t⟩, q₁, x₁⟩, p⟩ := d
    change (A.clearPerm F.base _ (A.answerPermTab F t _ (A.storePerm _ ((w, q₁, x₁), p)))).1.1.work
      = w.work
    rw [work_clearPerm, work_answerPermTab, work_storePerm]
  · rfl

theorem work_tabLift_symm (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    ((A.tabLift F (A.setAt F.base k)).symm d).1.1.1.work = d.1.1.1.work := by
  conv_rhs => rw [← (A.tabLift F (A.setAt F.base k)).apply_symm_apply d]
  obtain ⟨⟨⟨w, t⟩, q₁, x₁⟩, p⟩ := (A.tabLift F (A.setAt F.base k)).symm d
  exact (A.work_setAt F.base k ((w, q₁, x₁), p)).symm

theorem single_apply_perm {ι : Type*} [DecidableEq ι] (e : Equiv.Perm ι) (i j : ι) (c : ℂ)
    (a b : ι) : Matrix.single (e i) (e j) c (e a) (e b) = Matrix.single i j c a b := by
  simp only [Matrix.single_apply, e.injective.eq_iff]

variable (A F) in
/-- **The initial state of the adversary absorbed with a table**: `A`'s, with the other registers
blank and the table register at `tab`. -/
theorem init_absorbTab_mat (tab : A.OuterTab Req₂ Resp₂)
    (a b : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.absorbTab F tab).init.mat a b = A.init.mat (A.tabPart F a) (A.tabPart F b) *
      Matrix.single A.absBlank A.absBlank 1 (A.tabRest F a).1 (A.tabRest F b).1 *
      Matrix.single tab tab 1 (A.tabRest F a).2 (A.tabRest F b).2 := by
  rw [AdaptiveIAlg.withConst_init, AdaptiveIAlg.absorb_init]
  rfl

/-- The identity matrix along a permutation. -/
theorem one_apply_perm {ι : Type*} [DecidableEq ι] (e : Equiv.Perm ι) (a b : ι) :
    (1 : Matrix ι ι ℂ) (e a) (e b) = (1 : Matrix ι ι ℂ) a b := by
  simp only [Matrix.one_apply, e.injective.eq_iff]

theorem keepsBlocks_stepTab {L : Type} {ℓ : A.W → Option L}
    (h : ∀ k i, KeepsBlocks (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace)
      ((A.step k).op i)) (k : StepIdx A.slots A.post) (i : (A.absorb F.base).R) :
    KeepsBlocks (fun d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁
      Resp₁ => ℓ d.workspace.1.work) ((A.stepTab F k).op i) := by
  intro r' y x hx hne
  rw [stepTab_op_apply] at hne
  have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have := h k i.1.2 r' _ _ (by
    change ℓ (A.afterAtTab F k x).1.1.1.work = some r'
    rw [work_afterAtTab]
    exact hx) h1
  change ℓ ((A.tabLift F (A.setAt F.base k)).symm y).1.1.1.work = some r' at this
  rwa [work_tabLift_symm] at this

variable {L : Type} {ℓ : A.W → Option L} {r : L}

/-! ### The `none` block -/

variable (A F) in
/-- The registers of the adversary absorbed with a table as `A`'s and the others. -/
def tabSplit : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁ ≃
    DReg A.W A.width X Y Req Resp × (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) ×
      A.OuterTab Req₂ Resp₂) :=
  (((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).trans
    (A.absSplit.prodCongr (Equiv.refl _))).trans (Equiv.prodAssoc _ _ _)

theorem tabSplit_apply (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁
    Resp₁) : A.tabSplit F d = (A.tabPart F d, A.tabRest F d) :=
  rfl

theorem work_tabLift (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.tabLift F (A.setAt F.base k) d).1.1.1.work = d.1.1.1.work := by
  rw [← work_tabLift_symm (F := F) k, Equiv.symm_apply_apply]

variable (A F) in
/-- **The step's entries with the other registers as one**. -/
theorem stepTab_op_apply' (k : StepIdx A.slots A.post) (i : (A.absorb F.base).R)
    (y x : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.stepTab F k).op i y x =
      (A.step k).op i.1.2 (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm y))
        (A.tabPart F (A.afterAtTab F k x)) *
      (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) _ ℂ)
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm y)) (A.tabRest F (A.afterAtTab F k x))
      := by
  rw [stepTab_op_apply, mul_assoc]
  congr 1
  simp only [Matrix.one_apply, Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul]

variable (A F) in
/-- **The overlaps into a block of the step of the adversary absorbed with a table**: those of
`A`'s step at its registers, when the other registers agree, and zero otherwise. -/
theorem rowGram_stepTab [DecidableEq L] (k : StepIdx A.slots A.post) (r : L)
    (c d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    rowGram (fun p : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁
      => ℓ p.workspace.1.work) r (A.stepTab F k) c d =
      (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) _ ℂ)
        (A.tabRest F (A.afterAtTab F k c)) (A.tabRest F (A.afterAtTab F k d)) *
      rowGram (fun p : DReg A.W A.width X Y Req Resp => ℓ p.workspace) r (A.step k)
        (A.tabPart F (A.afterAtTab F k c)) (A.tabPart F (A.afterAtTab F k d)) := by
  have hs : ∀ v w : A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂,
      star ((1 : Matrix _ _ ℂ) v w) = (1 : Matrix _ _ ℂ) v w := fun v w => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have key : ∀ i' : A.R, (∑ a, if ℓ a.workspace.1.work = some r then
      ((A.step k).op i' (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm a))
          (A.tabPart F (A.afterAtTab F k c)) *
        (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) _ ℂ)
          (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm a))
          (A.tabRest F (A.afterAtTab F k c))) *
      star ((A.step k).op i' (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm a))
          (A.tabPart F (A.afterAtTab F k d)) *
        (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) _ ℂ)
          (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm a))
          (A.tabRest F (A.afterAtTab F k d))) else 0) =
      (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) _ ℂ)
        (A.tabRest F (A.afterAtTab F k c)) (A.tabRest F (A.afterAtTab F k d)) *
      ∑ u : DReg A.W A.width X Y Req Resp, if ℓ u.workspace = some r then
        (A.step k).op i' u (A.tabPart F (A.afterAtTab F k c)) *
          star ((A.step k).op i' u (A.tabPart F (A.afterAtTab F k d))) else 0 := fun i' => by
    set rc := A.tabRest F (A.afterAtTab F k c)
    set rd := A.tabRest F (A.afterAtTab F k d)
    set uc := A.tabPart F (A.afterAtTab F k c)
    set ud := A.tabPart F (A.afterAtTab F k d)
    rw [Fintype.sum_equiv (((A.tabSplit F).symm.trans (A.tabLift F (A.setAt F.base k))).symm) _
      (fun z => if ℓ z.1.workspace = some r then
        ((A.step k).op i' z.1 uc * (1 : Matrix _ _ ℂ) z.2 rc) *
          star ((A.step k).op i' z.1 ud * (1 : Matrix _ _ ℂ) z.2 rd) else 0) (fun a => by
        rw [← work_tabLift_symm (F := F) k a]
        rfl)]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [star_mul', hs]
    split_ifs
    · simp only [Matrix.one_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
      by_cases hcd : rc = rd
      · rw [if_pos hcd, Finset.sum_eq_single rd]
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
  unfold rowGram
  have hR : ∀ g : A.R → ℂ, ∑ i : (Unit × A.R) × Unit, g i.1.2 = ∑ i, g i := fun g => by
    simp [Fintype.sum_prod_type]
  rw [Finset.mul_sum, ← hR]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [stepTab_op_apply', Finset.sum_filter]
  exact key i.1.2

/-! ### The sets of well-formed states -/

/-- The set `G₀` before the first step and `G n` after step `n`, by an optional index. -/
def idxSet {T : Type*} (G : ℕ → Set T) (G₀ : Set T) : Option ℕ → Set T
  | none => G₀
  | some n => G n

/-- The index before step `k`: none before the first step, `k - 1` after it. -/
def prevIdx (k : ℕ) : Option ℕ := if k = 0 then none else some (k - 1)

theorem prevSeq_eq_idx {T : Sort*} (f : Option ℕ → T) (k : ℕ) :
    prevSeq (fun n => f (some n)) (f none) k = f (prevIdx k) := by
  unfold prevSeq prevIdx
  split_ifs <;> rfl

theorem prevSeq_eq_idxSet {T : Type*} (G : ℕ → Set T) (G₀ : Set T) (k : ℕ) :
    prevSeq G G₀ k = idxSet G G₀ (prevIdx k) := by
  unfold prevSeq prevIdx
  split_ifs <;> rfl

/-- The slots after an index: every slot after none, the slots after `n` after `some n`. -/
def AfterIdx : Option ℕ → ℕ → Prop
  | none, _ => True
  | some n, i => n < i

variable (A F) in
/-- **The inner request register at an index**: blank before the first step and from the last
slot on; at slot `n`, blank with log `n` blank, or the route of log `n`'s request. -/
def SlotCond : Option ℕ → LogReg Req A.slots → Req₁ → Prop
  | none, _, z => z = default
  | some n, lg, z => if h : n < A.slots then (lg ⟨n, h⟩ = none ∧ z = default) ∨
      ∃ q, lg ⟨n, h⟩ = some q ∧ z = F.route₁ (A.reqCount lg ⟨n, h⟩) q else z = default

variable (A F) in
/-- **The well-formed states of the adversary absorbed with a table** at an index: `A`'s
workspace, request and response in `G`, the logs blank after the index, and the inner request
register by `SlotCond`. -/
def tabSet (G : ℕ → Set (A.W × Req × Option Resp)) (G₀ : Set (A.W × Req × Option Resp))
    (idx : Option ℕ) :
    Set (((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) × Req₁ × Option Resp₁) :=
  {x | (x.1.1.work, x.1.1.request, x.1.1.response) ∈ idxSet G G₀ idx ∧
    (∀ i : Fin A.slots, AfterIdx idx i → x.1.1.logs i = none) ∧ SlotCond A F idx x.1.1.logs x.2.1}

variable (A F) in
/-- The states before `A`'s step `k` inside the absorbed step: `A`'s workspace, request and
response in `Gc`, the logs blank from slot `k` on, the inner request register blank. -/
def midSet (Gc : Set (A.W × Req × Option Resp)) (k : ℕ) :
    Set (((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) × Req₁ × Option Resp₁) :=
  {x | (x.1.1.work, x.1.1.request, x.1.1.response) ∈ Gc ∧
    (∀ i : Fin A.slots, k ≤ i → x.1.1.logs i = none) ∧ x.2.1 = default}

omit [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] in
theorem afterPermTab_apply_eq (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots) (w : A.W) (q : Req)
    (a : Option Resp) (lg : LogReg Req A.slots) (s : Fin A.slots → Option Resp₁) (z : Req₁)
    (y : Option Resp₁) (p : Fin A.width → X × Y) :
    ∃ a' s' y', A.afterPermTab F t j ((⟨w, q, a, lg, s⟩, z, y), p) =
      ((⟨w, q, a', lg, s'⟩, (match lg j with
        | none => z
        | some r => Equiv.swap default (F.route₁ (A.reqCount lg j) r) z), y'), p) := by
  unfold afterPermTab
  simp only [Equiv.trans_apply]
  unfold storePerm AlgShape.storePerm answerPermTab clearPerm AlgShape.clearPerm
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
  rcases h : lg j with _ | r
  · simp [h]
  · simp only [h, Option.isSome_some, if_true]
    exact ⟨_, _, _, rfl⟩

theorem mem_midSet_afterAtTab {G : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ : Set (A.W × Req × Option Resp)}
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx) (k : ℕ)
    (b : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (hb : b.1 ∈ A.tabSet F G G₀ (prevIdx k)) :
    (A.afterAtTab F k b).1 ∈ A.midSet F (idxSet G G₀ (prevIdx k)) k := by
  obtain ⟨⟨⟨⟨w, q, a, lg, s⟩, t⟩, z, y⟩, p⟩ := b
  obtain ⟨hA, hlog, hz⟩ := hb
  unfold afterAtTab
  split_ifs with hk
  · obtain ⟨a', s', y', he⟩ :=
      afterPermTab_apply_eq (A := A) (F := F) t ⟨k - 1, hk.2⟩ w q a lg s z y p
    have hpi : prevIdx k = some (k - 1) := by simp [prevIdx, hk.1.ne']
    rw [hpi] at hA hlog hz
    change ((((A.afterPermTab F t ⟨k - 1, hk.2⟩ ((⟨w, q, a, lg, s⟩, z, y), p)).1.1, t),
      (A.afterPermTab F t ⟨k - 1, hk.2⟩ ((⟨w, q, a, lg, s⟩, z, y), p)).1.2),
      (A.afterPermTab F t ⟨k - 1, hk.2⟩ ((⟨w, q, a, lg, s⟩, z, y), p)).2).1 ∈ _
    rw [he, hpi]
    refine ⟨hG _ _ _ a a' hA, fun i hi => hlog i (by change k - 1 < i; omega), ?_⟩
    change (match lg ⟨k - 1, hk.2⟩ with
      | none => z
      | some r => Equiv.swap default (F.route₁ (A.reqCount lg ⟨k - 1, hk.2⟩) r) z) = default
    simp only [SlotCond, hk.2, dif_pos] at hz
    rcases hz with ⟨h1, h2⟩ | ⟨q', h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]
      exact Equiv.swap_apply_right _ _
  · refine ⟨hA, fun i hi => hlog i ?_, ?_⟩
    · unfold prevIdx
      split_ifs with h0
      · trivial
      · change k - 1 < i
        have := i.isLt
        omega
    · change z = default
      unfold prevIdx at hz
      split_ifs at hz with h0
      · exact hz
      · simp only [SlotCond] at hz
        rw [dif_neg (by omega)] at hz
        exact hz

theorem mem_tabSet_setAt {G : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ : Set (A.W × Req × Option Resp)} (k : ℕ)
    (x : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (hA : (x.1.1.1.work, x.1.1.1.request, x.1.1.1.response) ∈ G k)
    (hlog : ∀ i : Fin A.slots, k ≤ i → x.1.1.1.logs i = none) (hz : x.1.2.1 = default) :
    (A.tabLift F (A.setAt F.base k) x).1 ∈ A.tabSet F G G₀ (some k) := by
  obtain ⟨⟨⟨⟨w, q, a, lg, s⟩, t⟩, z, y⟩, p⟩ := x
  change z = default at hz
  subst hz
  change (((((A.setAt F.base k ((⟨w, q, a, lg, s⟩, default, y), p)).1.1, t),
    (A.setAt F.base k ((⟨w, q, a, lg, s⟩, default, y), p)).1.2),
    (A.setAt F.base k ((⟨w, q, a, lg, s⟩, default, y), p)).2).1 ∈ _)
  rw [AdaptiveIAlg.setAt_def]
  split_ifs with hk
  · unfold setPerm AlgShape.setPerm
    simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    have hlk : lg ⟨k, hk⟩ = none := hlog ⟨k, hk⟩ le_rfl
    split_ifs with hkind
    · refine ⟨hA, fun i hi => ?_, ?_⟩
      · change k < (i : ℕ) at hi
        change Function.update lg ⟨k, hk⟩ _ i = none
        rw [Function.update_of_ne (fun e => by rw [e] at hi; exact lt_irrefl _ hi)]
        exact hlog i hi.le
      · simp only [SlotCond, dif_pos hk]
        refine Or.inr ⟨q, by simp [hlk], ?_⟩
        have hc : A.reqCount (Function.update lg ⟨k, hk⟩
            (Equiv.swap none (some q) (lg ⟨k, hk⟩))) ⟨k, hk⟩ = A.reqCount lg ⟨k, hk⟩ :=
          congrArg List.length (requestsBefore_congr fun k' hk' =>
            Function.update_of_ne (fun e => by subst e; simp at hk') _ _)
        rw [hc]
        exact Equiv.swap_apply_left _ _
    · refine ⟨hA, fun i hi => hlog i (le_of_lt hi), ?_⟩
      simp only [SlotCond, dif_pos hk]
      exact Or.inl ⟨hlk, trivial⟩
  · refine ⟨hA, fun i hi => absurd (lt_trans hi i.isLt) (by omega), ?_⟩
    simp only [SlotCond, dif_neg hk]
    rfl

theorem triple_tabLift_symm (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm d)).1 = (A.tabPart F d).1 := by
  conv_rhs => rw [← (A.tabLift F (A.setAt F.base k)).apply_symm_apply d]
  obtain ⟨⟨⟨⟨w, q, a, lg, s⟩, t⟩, z, y⟩, p⟩ := (A.tabLift F (A.setAt F.base k)).symm d
  change _ = ((A.setAt F.base k ((⟨w, q, a, lg, s⟩, z, y), p)).1.1.work,
    (A.setAt F.base k ((⟨w, q, a, lg, s⟩, z, y), p)).1.1.request,
    (A.setAt F.base k ((⟨w, q, a, lg, s⟩, z, y), p)).1.1.response)
  rw [AdaptiveIAlg.setAt_def]
  split_ifs
  · unfold setPerm AlgShape.setPerm
    simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split_ifs <;> rfl
  · rfl

/-- **The other registers agree** where an entry of the absorbed step with the Kraus maps `st` is
nonzero. -/
theorem withStepTab_ne_zero {st : StepIdx A.slots A.post → KrausMap A.R
      (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)}
    {k : StepIdx A.slots A.post} {i : (A.absorb F.base).R}
    {a b : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁}
    (hne : ((A.withStep st).stepTab F k).op i a b ≠ 0) :
    (st k).op i.1.2 (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm a))
        (A.tabPart F (A.afterAtTab F k b)) ≠ 0 ∧
      A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm a) =
        A.tabRest F (A.afterAtTab F k b) := by
  rw [withStep_stepTab_op_apply, mul_assoc] at hne
  refine ⟨left_ne_zero_of_mul hne, ?_⟩
  by_contra h
  have h' : ¬ ((A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm a)).1 =
      (A.tabRest F (A.afterAtTab F k b)).1 ∧
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm a)).2
        = (A.tabRest F (A.afterAtTab F k b)).2) := fun e => h (Prod.ext e.1 e.2)
  apply hne
  rw [not_and_or] at h'
  rcases h' with h' | h'
  · rw [Matrix.one_apply_ne h', zero_mul, mul_zero]
  · rw [Matrix.one_apply_ne h', mul_zero, mul_zero]

/-- **The absorbed step moves the well-formed states before step `k` into those after it.** -/
theorem keepsSet_stepTab {st : StepIdx A.slots A.post → KrausMap A.R
      (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)}
    {G : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ : Set (A.W × Req × Option Resp)}
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    {k : StepIdx A.slots A.post}
    (hA : ∀ i, KeepsSet {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
      {d | d.1 ∈ G k} ((st k).op i)) (i : (A.absorb F.base).R) :
    KeepsSet {d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁ |
      d.1 ∈ A.tabSet F G G₀ (prevIdx k)} {d | d.1 ∈ A.tabSet F G G₀ (some k)}
      (((A.withStep st).stepTab F k).op i) := fun a b hb hne => by
  obtain ⟨h1, h2⟩ := withStepTab_ne_zero hne
  obtain ⟨hm1, hm2, hm3⟩ := mem_midSet_afterAtTab hG k b hb
  have hrow := hA i.1.2 _ _ (by
    change _ ∈ prevSeq G G₀ k
    rw [prevSeq_eq_idxSet]
    exact hm1) h1
  rw [← (A.tabLift F (A.setAt F.base k)).apply_symm_apply a]
  refine mem_tabSet_setAt k _ hrow (fun j hj => ?_) ?_
  · have := congrArg (fun x => x.1.1 j) h2
    exact this.trans (hm2 j hj)
  · have := congrArg (fun x => x.1.2.2.1) h2
    exact this.trans hm3

/-- **The absorbed step keeps the blocks on the well-formed states before step `k`.** -/
theorem keepsBlocksOn_stepTab {st : StepIdx A.slots A.post → KrausMap A.R
      (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)}
    {L : Type} {ℓ : A.W → Option L} {G : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ : Set (A.W × Req × Option Resp)}
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    {k : StepIdx A.slots A.post}
    (hA : ∀ i, KeepsBlocksOn {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
      (fun d => ℓ d.workspace) ((st k).op i)) (i : (A.absorb F.base).R) :
    KeepsBlocksOn {d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁ |
      d.1 ∈ A.tabSet F G G₀ (prevIdx k)} (fun d => ℓ d.workspace.1.work)
      (((A.withStep st).stepTab F k).op i) := fun r' a b hb hl hne => by
  obtain ⟨h1, -⟩ := withStepTab_ne_zero hne
  obtain ⟨hm1, -, -⟩ := mem_midSet_afterAtTab hG k b hb
  have := hA i.1.2 r' _ _ (by
    change _ ∈ prevSeq G G₀ k
    rw [prevSeq_eq_idxSet]
    exact hm1) (by
    change ℓ (A.afterAtTab F k b).1.1.1.work = some r'
    rw [work_afterAtTab]
    exact hl) h1
  change ℓ ((A.tabLift F (A.setAt F.base k)).symm a).1.1.1.work = some r' at this
  rwa [work_tabLift_symm] at this

theorem prevSeq_tabSet (G : ℕ → Set (A.W × Req × Option Resp))
    (G₀ : Set (A.W × Req × Option Resp)) (k : ℕ) :
    prevSeq (fun n => A.tabSet F G G₀ (some n)) (A.tabSet F G G₀ none) k =
      A.tabSet F G G₀ (prevIdx k) :=
  prevSeq_eq_idx (A.tabSet F G G₀) k

/-- **The initial state of the absorbed adversary is supported on the well-formed states.** -/
theorem init_supp_absorbTab {G₀ : Set (A.W × Req × Option Resp)}
    (G : ℕ → Set (A.W × Req × Option Resp))
    (h : ∀ a b, A.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀) (tab : A.OuterTab Req₂ Resp₂)
    (a b : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (hab : (A.absorbTab F tab).init.mat a b ≠ 0) :
    a.1 ∈ A.tabSet F G G₀ none ∧ b.1 ∈ A.tabSet F G G₀ none := by
  rw [init_absorbTab_mat] at hab
  have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul hab)
  have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul hab)
  rw [Matrix.single_apply] at h2
  split_ifs at h2 with he
  · obtain ⟨ha, hb⟩ := h _ _ h1
    have hla := congrArg (fun x => x.1) he.1
    have hlb := congrArg (fun x => x.1) he.2
    have hza := congrArg (fun x => x.2.2.1) he.1
    have hzb := congrArg (fun x => x.2.2.1) he.2
    exact ⟨⟨ha, fun i _ => (congrFun hla i).symm, hza.symm⟩,
      ⟨hb, fun i _ => (congrFun hlb i).symm, hzb.symm⟩⟩
  · exact absurd rfl h2

variable [DecidableEq L]

theorem stepTab_row_none {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} (h : A.BlockNone st' ℓ G G' G₀ G₀')
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (k : StepIdx A.slots A.post) (i : (A.absorb F.base).R)
    (a b : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (ha : a.1 ∈ A.tabSet F G G₀ (some k)) (hb : b.1 ∈ A.tabSet F G G₀ (prevIdx k))
    (hl : ℓ a.workspace.1.work = none) (hbl : ℓ b.workspace.1.work = none) :
    ((A.withStep st').stepTab F k).op i a b = (A.stepTab F k).op i a b := by
  rw [withStep_stepTab_op_apply, stepTab_op_apply, h.row_none_eq k i.1.2 _ _ (by
    change (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm a)).1 ∈ G k
    rw [triple_tabLift_symm]
    exact ha.1) (by
    change _ ∈ prevSeq G G₀ k
    rw [prevSeq_eq_idxSet]
    exact (mem_midSet_afterAtTab hG k b hb).1) (by
    change ℓ ((A.tabLift F (A.setAt F.base k)).symm a).1.1.1.work = none
    rw [work_tabLift_symm]
    exact hl) (by
    change ℓ (A.afterAtTab F k b).1.1.1.work = none
    rw [work_afterAtTab]
    exact hbl)]

theorem stepTab_gram {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} (h : A.BlockNone st' ℓ G G' G₀ G₀')
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (k : StepIdx A.slots A.post) (r : L)
    (c d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (hc : c.1 ∈ A.tabSet F G G₀ (prevIdx k)) (hd : d.1 ∈ A.tabSet F G G₀ (prevIdx k))
    (hcl : ℓ c.workspace.1.work = none) (hdl : ℓ d.workspace.1.work = none) :
    rowGram (fun p : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁
      => ℓ p.workspace.1.work) r ((A.withStep st').stepTab F k) c d =
    rowGram (fun p : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁
      => ℓ p.workspace.1.work) r (A.stepTab F k) c d := by
  refine (rowGram_stepTab (A.withStep st') F k r c d).trans
    (Eq.trans ?_ (rowGram_stepTab A F k r c d).symm)
  congr 1
  refine h.gram_eq k r _ _ ?_ ?_ ?_ ?_
  · change _ ∈ prevSeq G G₀ k
    rw [prevSeq_eq_idxSet]
    exact (mem_midSet_afterAtTab hG k c hc).1
  · change _ ∈ prevSeq G G₀ k
    rw [prevSeq_eq_idxSet]
    exact (mem_midSet_afterAtTab hG k d hd).1
  · change ℓ (A.afterAtTab F k c).1.1.1.work = none
    rw [work_afterAtTab]
    exact hcl
  · change ℓ (A.afterAtTab F k d).1.1.1.work = none
    rw [work_afterAtTab]
    exact hdl

theorem keepsSet_stepTab_prev {st : StepIdx A.slots A.post → KrausMap A.R
      (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)}
    {G : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ : Set (A.W × Req × Option Resp)}
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    {k : StepIdx A.slots A.post}
    (hA : ∀ i, KeepsSet {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
      {d | d.1 ∈ G k} ((st k).op i)) (i : (A.absorb F.base).R) :
    KeepsSet {d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁ |
      d.1 ∈ prevSeq (fun n => A.tabSet F G G₀ (some n)) (A.tabSet F G G₀ none) k}
      {d | d.1 ∈ A.tabSet F G G₀ (some k)} (((A.withStep st).stepTab F k).op i) := by
  rw [prevSeq_tabSet]
  exact keepsSet_stepTab hG hA i

theorem keepsBlocksOn_stepTab_prev {st : StepIdx A.slots A.post → KrausMap A.R
      (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)}
    {G : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ : Set (A.W × Req × Option Resp)}
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    {k : StepIdx A.slots A.post}
    (hA : ∀ i, KeepsBlocksOn {d : DReg A.W A.width X Y Req Resp | d.1 ∈ prevSeq G G₀ k}
      (fun d => ℓ d.workspace) ((st k).op i)) (i : (A.absorb F.base).R) :
    KeepsBlocksOn {d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁ |
      d.1 ∈ prevSeq (fun n => A.tabSet F G G₀ (some n)) (A.tabSet F G G₀ none) k}
      (fun d => ℓ d.workspace.1.work) (((A.withStep st).stepTab F k).op i) := by
  rw [prevSeq_tabSet]
  exact keepsBlocksOn_stepTab hG hA i

theorem stepTab_gram_prev {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} (h : A.BlockNone st' ℓ G G' G₀ G₀')
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (k : StepIdx A.slots A.post) (r : L)
    (c d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (hc : c.1 ∈ prevSeq (fun n => A.tabSet F G G₀ (some n)) (A.tabSet F G G₀ none) k)
    (hd : d.1 ∈ prevSeq (fun n => A.tabSet F G G₀ (some n)) (A.tabSet F G G₀ none) k)
    (hcl : ℓ c.workspace.1.work = none) (hdl : ℓ d.workspace.1.work = none) :
    rowGram (fun p : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁
      => ℓ p.workspace.1.work) r ((A.withStep st').stepTab F k) c d =
    rowGram (fun p : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁
      => ℓ p.workspace.1.work) r (A.stepTab F k) c d := by
  rw [prevSeq_tabSet] at hc hd
  exact stepTab_gram st' h hG k r c d hc hd hcl hdl

theorem stepTab_row_none_prev {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} (h : A.BlockNone st' ℓ G G' G₀ G₀')
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (k : StepIdx A.slots A.post) (i : (A.absorb F.base).R)
    (a b : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (ha : a.1 ∈ A.tabSet F G G₀ (some k))
    (hb : b.1 ∈ prevSeq (fun n => A.tabSet F G G₀ (some n)) (A.tabSet F G G₀ none) k)
    (hl : ℓ a.workspace.1.work = none) (hbl : ℓ b.workspace.1.work = none) :
    ((A.withStep st').stepTab F k).op i a b = (A.stepTab F k).op i a b := by
  rw [prevSeq_tabSet] at hb
  exact stepTab_row_none st' h hG k i a b ha hb hl hbl

/-- **The well-formed states of the two families have the same states of label `none`**, when
the sets of the index do. -/
theorem tabSet_none_eq {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} (idx : Option ℕ)
    (hE : ∀ x : A.W × Req × Option Resp, ℓ x.1 = none →
      (x ∈ idxSet G' G₀' idx ↔ x ∈ idxSet G G₀ idx))
    (x : ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) × Req₁ × Option Resp₁)
    (hx : ℓ x.1.1.work = none) :
    x ∈ A.tabSet F G' G₀' idx ↔ x ∈ A.tabSet F G G₀ idx :=
  and_congr (hE _ hx) Iff.rfl

/-- **The `none`-block hypotheses through the absorption with a table**: along the well-formed
states (`tabSet`) of sets closed under changes of the response, with the label read on `A`'s
workspace. -/
theorem BlockNone.absorbTab {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} (h : A.BlockNone st' ℓ G G' G₀ G₀')
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (hG' : ∀ idx w q a a', (w, q, a) ∈ idxSet G' G₀' idx → (w, q, a') ∈ idxSet G' G₀' idx)
    (tab : A.OuterTab Req₂ Resp₂) :
    (A.absorbTab F tab).BlockNone (A.absorbTabStep F st') (fun w => ℓ w.1.work)
      (fun n => A.tabSet F G G₀ (some n)) (fun n => A.tabSet F G' G₀' (some n))
      (A.tabSet F G G₀ none) (A.tabSet F G' G₀' none) where
  none_eq n x hx := tabSet_none_eq (some n) (fun y hy => h.none_eq n y hy) x hx
  none_eq₀ x hx := tabSet_none_eq none (fun y hy => h.none_eq₀ y hy) x hx
  keepsSet k i := keepsSet_stepTab_prev (st := A.step) hG (h.keepsSet k) i
  keepsSet' k i := keepsSet_stepTab_prev (st := st') hG' (h.keepsSet' k) i
  keeps k i := keepsBlocksOn_stepTab_prev (st := A.step) hG (h.keeps k) i
  keeps' k i := keepsBlocksOn_stepTab_prev (st := st') hG' (h.keeps' k) i
  row_none_eq k i a b ha hb hl hbl := stepTab_row_none_prev st' h hG k i a b ha hb hl hbl
  gram_eq k r c d hc hd hcl hdl := stepTab_gram_prev st' h hG k r c d hc hd hcl hdl
  init_supp a b hab := init_supp_absorbTab G h.init_supp tab a b hab
  init_supp' a b hab := init_supp_absorbTab G' h.init_supp' tab a b hab


/-! ### The witness swap at one slot -/

section Swap

variable (σW : Equiv.Perm A.W) (sw : Equiv.Perm Req) (J : A.W → Option ℕ) (σ₁ : Equiv.Perm Req₁)

/-- Whether the slot recorded by `J` at the workspace `w` is the index. -/
def Hit (J : A.W → Option ℕ) (w : A.W) (idx : Option ℕ) : Prop := idx.isSome ∧ J w = idx

instance (w : A.W) (idx : Option ℕ) : Decidable (Hit J w idx) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem hit_some (w : A.W) (n : ℕ) : Hit J w (some n) ↔ J w = some n := by
  simp [Hit]

theorem not_hit_none (w : A.W) : ¬ Hit J w none := by
  simp [Hit]

variable (A) in
/-- **The witness swap of the adversary's registers at an index**: `σW` on the workspace, `sw` on
the request when the slot recorded by `J` is the index. -/
def jTrip (idx : Option ℕ) : Equiv.Perm (A.W × Req × Option Resp) where
  toFun x := (σW x.1, swIf (Hit J x.1 idx) sw x.2.1, x.2.2)
  invFun x := (σW.symm x.1, (swIf (Hit J (σW.symm x.1) idx) sw).symm x.2.1, x.2.2)
  left_inv x := by simp
  right_inv x := by simp

variable (A) in
/-- **The witness swap of the logs**: `sw` on the log of the slot recorded `jw`. -/
def logSw (jw : Option ℕ) : Equiv.Perm (LogReg Req A.slots) :=
  logFam fun i => swIf (jw = some (i : ℕ)) sw

variable (A) in
/-- **The witness swap of the absorbed adversary's registers at an index**: `jTrip` on `A`'s
registers, `logSw` on the logs, `σ₁` on the inner request when the recorded slot is the index. -/
def aTrip (idx : Option ℕ) :
    Equiv.Perm (A.AbsW (Resp' := Resp₁) × Req₁ × Option Resp₁) where
  toFun x := (⟨σW x.1.work, swIf (Hit J x.1.work idx) sw x.1.request, x.1.response,
    A.logSw sw (J x.1.work) x.1.logs, x.1.store⟩, swIf (Hit J x.1.work idx) σ₁ x.2.1, x.2.2)
  invFun x := (⟨σW.symm x.1.work, (swIf (Hit J (σW.symm x.1.work) idx) sw).symm x.1.request,
    x.1.response, (A.logSw sw (J (σW.symm x.1.work))).symm x.1.logs, x.1.store⟩,
    (swIf (Hit J (σW.symm x.1.work) idx) σ₁).symm x.2.1, x.2.2)
  left_inv x := by
    obtain ⟨⟨w, q, a, lg, s⟩, z, y⟩ := x
    simp
  right_inv x := by
    obtain ⟨⟨w, q, a, lg, s⟩, z, y⟩ := x
    simp

variable {σW sw J σ₁}

theorem reqCount_logSw (jw : Option ℕ) (lg : LogReg Req A.slots) (j : Fin A.slots) :
    A.reqCount (A.logSw sw jw lg) j = A.reqCount lg j :=
  length_requestsBefore_logFam _ _ _

theorem outerCount_logSw (hF : F.SwapInv sw σ₁) (jw : Option ℕ) (lg : LogReg Req A.slots)
    (j : Fin A.slots) : A.outerCount F (A.logSw sw jw lg) j = A.outerCount F lg j :=
  length_filter_zipIdx_of_forall₂ (P := fun p => (F.outer p.2 p.1).isSome)
    (fun a b n ⟨i, hab⟩ => by rw [hab, hF.outer_swIf]) (requestsBefore_logFam _ lg j) 0

theorem tabAnswer_logSw (hF : F.SwapInv sw σ₁) (t : A.OuterTab Req₂ Resp₂) (jw : Option ℕ)
    (lg : LogReg Req A.slots) (j : Fin A.slots) (r : Req) (a : Option Resp₁) :
    A.tabAnswer F t (A.logSw sw jw lg) j (swIf (jw = some (j : ℕ)) sw r) a =
      A.tabAnswer F t lg j r a := by
  unfold tabAnswer
  rw [reqCount_logSw, outerCount_logSw hF, hF.outer_swIf]
  rcases F.outer (A.reqCount lg j) r with _ | q
  · exact hF.answer₁_swIf _ _ _ _
  · exact hF.answer₂_swIf _ _ _ _

theorem logSw_apply (jw : Option ℕ) (lg : LogReg Req A.slots) (i : Fin A.slots) :
    A.logSw sw jw lg i = (lg i).map (swIf (jw = some (i : ℕ)) sw) :=
  rfl

theorem swap_route_swIf (hF : F.SwapInv sw σ₁) (p : Prop) [Decidable p] (c : ℕ) (q : Req)
    (z : Req₁) :
    Equiv.swap default (F.route₁ c (swIf p sw q)) (swIf p σ₁ z) =
      swIf p σ₁ (Equiv.swap default (F.route₁ c q) z) := by
  rw [hF.route_swIf]
  conv_lhs => rw [← hF.default_swIf p]
  exact swap_apply_perm _ _ _ _

theorem setPerm_aTrip (hk : ∀ x : A.W × Req × Option Resp, A.kind (σW x.1) = A.kind x.1)
    (hF : F.SwapInv sw σ₁)
    (k : Fin A.slots) (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    A.setPerm F.base k (tripPerm (A.aTrip σW sw J σ₁ (some k)) d) =
      tripPerm (A.aTrip σW sw J σ₁ (some k)) (A.setPerm F.base k d) := by
  obtain ⟨⟨⟨w, q, x, lg, s⟩, z, y⟩, p⟩ := d
  unfold setPerm AlgShape.setPerm
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, tripPerm, Equiv.prodCongr_apply,
    Prod.map, aTrip, Equiv.coe_fn_mk, Equiv.coe_refl, id, hk (w, q, x)]
  split_ifs
  · have hl : Function.update (A.logSw sw (J w) lg) k
        ((Equiv.swap none (some (swIf (Hit J w (some k)) sw q))) (A.logSw sw (J w) lg k)) =
        A.logSw sw (J w) (Function.update lg k ((Equiv.swap none (some q)) (lg k))) := by
      funext k'
      by_cases hk' : k' = k
      · subst hk'
        simp only [Function.update_self, logSw_apply]
        rw [swIf_congr sw (hit_some J w _)]
        exact swap_apply_perm (Equiv.optionCongr (swIf (J w = some (k' : ℕ)) sw)) none (some q)
          (lg k')
      · simp only [Function.update_of_ne hk', logSw_apply]
    simp only [hl, reqCount_logSw]
    rw [show F.base.route = F.route₁ from rfl, swap_route_swIf hF]
  · rfl

theorem storePerm_aTrip (idx : Option ℕ) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    A.storePerm j (tripPerm (A.aTrip σW sw J σ₁ idx) d) =
      tripPerm (A.aTrip σW sw J σ₁ idx) (A.storePerm j d) := by
  obtain ⟨⟨⟨w, q, x, lg, s⟩, z, y⟩, p⟩ := d
  have hs : (A.logSw sw (J w) lg j).isSome = (lg j).isSome := by
    rw [logSw_apply]
    cases lg j <;> rfl
  unfold storePerm AlgShape.storePerm
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, tripPerm, Equiv.prodCongr_apply,
    Prod.map, aTrip, Equiv.coe_fn_mk, Equiv.coe_refl, id, hs]
  split_ifs <;> rfl

theorem answerPermTab_aTrip (hF : F.SwapInv sw σ₁) (t : A.OuterTab Req₂ Resp₂)
    (idx : Option ℕ) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    A.answerPermTab F t j (tripPerm (A.aTrip σW sw J σ₁ idx) d) =
      tripPerm (A.aTrip σW sw J σ₁ idx) (A.answerPermTab F t j d) := by
  obtain ⟨⟨⟨w, q, x, lg, s⟩, z, y⟩, p⟩ := d
  unfold answerPermTab
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, tripPerm, Equiv.prodCongr_apply,
    Prod.map, aTrip, Equiv.coe_fn_mk, Equiv.coe_refl, id, logSw_apply]
  rcases h : lg j with _ | r
  · rfl
  · simp only [Option.map_some]
    rw [tabAnswer_logSw hF]

theorem clearPerm_aTrip (hF : F.SwapInv sw σ₁) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    A.clearPerm F.base j (tripPerm (A.aTrip σW sw J σ₁ (some j)) d) =
      tripPerm (A.aTrip σW sw J σ₁ (some j)) (A.clearPerm F.base j d) := by
  obtain ⟨⟨⟨w, q, x, lg, s⟩, z, y⟩, p⟩ := d
  unfold clearPerm AlgShape.clearPerm
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, tripPerm, Equiv.prodCongr_apply,
    Prod.map, aTrip, Equiv.coe_fn_mk, Equiv.coe_refl, id, logSw_apply]
  rcases lg j with _ | r
  · rfl
  · simp only [Option.map_some, reqCount_logSw]
    rw [show F.base.route = F.route₁ from rfl, swIf_congr sw (hit_some J w j).symm,
      swap_route_swIf hF]

theorem afterPermTab_aTrip (hF : F.SwapInv sw σ₁) (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    A.afterPermTab F t j (tripPerm (A.aTrip σW sw J σ₁ (some j)) d) =
      tripPerm (A.aTrip σW sw J σ₁ (some j)) (A.afterPermTab F t j d) := by
  simp only [afterPermTab, Equiv.trans_apply, storePerm_aTrip, answerPermTab_aTrip hF,
    clearPerm_aTrip hF]

theorem setAt_aTrip (hk : ∀ x : A.W × Req × Option Resp, A.kind (σW x.1) = A.kind x.1)
    (hF : F.SwapInv sw σ₁) (k : ℕ)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    A.setAt F.base k (tripPerm (A.aTrip σW sw J σ₁ (some k)) d) =
      tripPerm (A.aTrip σW sw J σ₁ (some k)) (A.setAt F.base k d) := by
  rw [AdaptiveIAlg.setAt_def]
  split_ifs with h
  · exact setPerm_aTrip hk hF ⟨k, h⟩ d
  · rfl

variable (σW sw J σ₁) in
variable (A F) in
/-- **The witness swap of the registers of the adversary absorbed with a table** at an index:
`aTrip` with the table register kept. -/
def tTrip (idx : Option ℕ) :
    Equiv.Perm (((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) × Req₁ × Option Resp₁) where
  toFun x := (((A.aTrip σW sw J σ₁ idx (x.1.1, x.2)).1, x.1.2),
    (A.aTrip σW sw J σ₁ idx (x.1.1, x.2)).2)
  invFun x := ((((A.aTrip σW sw J σ₁ idx).symm (x.1.1, x.2)).1, x.1.2),
    ((A.aTrip σW sw J σ₁ idx).symm (x.1.1, x.2)).2)
  left_inv x := by simp
  right_inv x := by simp

theorem tabLift_tTrip {idx : Option ℕ}
    {π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁)}
    (hπ : ∀ d, π (tripPerm (A.aTrip σW sw J σ₁ idx) d) = tripPerm (A.aTrip σW sw J σ₁ idx) (π d))
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    A.tabLift F π (tripPerm (A.tTrip F σW sw J σ₁ idx) d) =
      tripPerm (A.tTrip F σW sw J σ₁ idx) (A.tabLift F π d) := by
  obtain ⟨⟨⟨w, t⟩, q₁, x₁⟩, p⟩ := d
  have h := hπ ((w, q₁, x₁), p)
  change ((((π (tripPerm (A.aTrip σW sw J σ₁ idx) ((w, q₁, x₁), p))).1.1, t),
    (π (tripPerm (A.aTrip σW sw J σ₁ idx) ((w, q₁, x₁), p))).1.2),
    (π (tripPerm (A.aTrip σW sw J σ₁ idx) ((w, q₁, x₁), p))).2) = _
  rw [h]
  rfl

theorem afterAtTab_tTrip (hF : F.SwapInv sw σ₁) (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    A.afterAtTab F k (tripPerm (A.tTrip F σW sw J σ₁ (prevIdx k)) d) =
      tripPerm (A.tTrip F σW sw J σ₁ (prevIdx k)) (A.afterAtTab F k d) := by
  unfold afterAtTab
  split_ifs with hk
  · have hpi : prevIdx k = some (k - 1) := by simp [prevIdx, hk.1.ne']
    rw [hpi]
    obtain ⟨⟨⟨w, t⟩, q₁, x₁⟩, p⟩ := d
    have h := afterPermTab_aTrip (σW := σW) (J := J) hF t ⟨k - 1, hk.2⟩ ((w, q₁, x₁), p)
    change ((((A.afterPermTab F t ⟨k - 1, hk.2⟩ (tripPerm (A.aTrip σW sw J σ₁ (some (k - 1)))
        ((w, q₁, x₁), p))).1.1, t),
      (A.afterPermTab F t ⟨k - 1, hk.2⟩ (tripPerm (A.aTrip σW sw J σ₁ (some (k - 1)))
        ((w, q₁, x₁), p))).1.2),
      (A.afterPermTab F t ⟨k - 1, hk.2⟩ (tripPerm (A.aTrip σW sw J σ₁ (some (k - 1)))
        ((w, q₁, x₁), p))).2) = _
    rw [h]
    rfl
  · rfl

theorem tabLift_symm_tTrip
    (hk : ∀ x : A.W × Req × Option Resp, A.kind (σW x.1) = A.kind x.1)
    (hF : F.SwapInv sw σ₁) (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.tabLift F (A.setAt F.base k)).symm (tripPerm (A.tTrip F σW sw J σ₁ (some k)) d) =
      tripPerm (A.tTrip F σW sw J σ₁ (some k)) ((A.tabLift F (A.setAt F.base k)).symm d) := by
  rw [Equiv.symm_apply_eq, tabLift_tTrip (setAt_aTrip hk hF k), Equiv.apply_symm_apply]

theorem tabPart_tTrip (idx : Option ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    A.tabPart F (tripPerm (A.tTrip F σW sw J σ₁ idx) d) =
      tripPerm (A.jTrip σW sw J idx) (A.tabPart F d) :=
  rfl

variable (sw σ₁) in
variable (A) in
/-- The witness swap of the other registers, at the recorded slot `jw` and the index. -/
def restSw (jw idx : Option ℕ)
    (u : A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) :
    A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂ :=
  ((A.logSw sw jw u.1.1, u.1.2.1, swIf (idx.isSome ∧ jw = idx) σ₁ u.1.2.2.1, u.1.2.2.2), u.2)

theorem tabRest_tTrip (idx : Option ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    A.tabRest F (tripPerm (A.tTrip F σW sw J σ₁ idx) d) =
      A.restSw sw σ₁ (J d.1.1.1.work) idx (A.tabRest F d) :=
  rfl

theorem logSw_eq_of_blank {k : ℕ} {jx jy : Option ℕ} (hj : jx = jy ∨ (jy = none ∧ jx = some k))
    (lg : LogReg Req A.slots) (hl : ∀ i : Fin A.slots, k ≤ i → lg i = none) :
    A.logSw sw jx lg = A.logSw sw jy lg := by
  rcases hj with rfl | ⟨rfl, rfl⟩
  · rfl
  funext i
  rw [logSw_apply, logSw_apply]
  by_cases hi : (i : ℕ) = k
  · rw [hl i hi.ge]
    rfl
  · rw [swIf_congr (p := some k = some (i : ℕ)) (p' := False) sw (by simp [Ne.symm hi]),
      swIf_congr (p := none = some (i : ℕ)) (p' := False) sw (by simp)]

/-- **The witness swaps of the other registers before and after `A`'s step `k`** agree exactly
when the registers do, on registers with the logs blank from slot `k` on and the inner request
blank, the recorded slot set at most at step `k`. -/
theorem restSw_eq_iff (hd : σ₁ default = default) {k : ℕ} {jx jy : Option ℕ}
    (hj : jx = jy ∨ (jy = none ∧ jx = some k))
    (u v : A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂)
    (hv : ∀ i : Fin A.slots, k ≤ i → v.1.1 i = none) (hvz : v.1.2.2.1 = default) :
    A.restSw sw σ₁ jx (some k) u = A.restSw sw σ₁ jy (prevIdx k) v ↔ u = v := by
  obtain ⟨⟨lu, su, zu, yu⟩, tu⟩ := u
  obtain ⟨⟨lv, sv, zv, yv⟩, tv⟩ := v
  change zv = default at hvz
  subst hvz
  have hz : ∀ p : Prop, ∀ [Decidable p], swIf p σ₁ default = default := fun p _ => by
    by_cases hp : p
    · rw [swIf_apply_of _ hp, hd]
    · rw [swIf_apply_of_not _ hp]
  have hlv := logSw_eq_of_blank (sw := sw) hj lv hv
  simp only [restSw, hz, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    rw [← hlv] at h1
    refine ⟨⟨(A.logSw sw jx).injective h1, h2, ?_, h4⟩, h5⟩
    have := congrArg (swIf ((some k).isSome ∧ jx = some k) σ₁).symm h3
    rwa [Equiv.symm_apply_apply, ← hz ((some k).isSome ∧ jx = some k),
      Equiv.symm_apply_apply] at this
  · rintro ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    exact ⟨⟨hlv, rfl, hz _, rfl⟩, rfl⟩

variable (A) in
/-- **The recorded slot changes only at its step**: where a Kraus map of `A` is nonzero from a
column in the set before step `k`, the slot recorded by `J` is the column's, or is set to `k`
from none. -/
def JSlotStep (G : ℕ → Set (A.W × Req × Option Resp)) (G₀ : Set (A.W × Req × Option Resp))
    (J : A.W → Option ℕ) : Prop :=
  ∀ (k : StepIdx A.slots A.post) i (a b : DReg A.W A.width X Y Req Resp),
    b.1 ∈ prevSeq G G₀ k → (A.step k).op i a b ≠ 0 →
      J a.workspace = J b.workspace ∨ (J b.workspace = none ∧ J a.workspace = some k)

theorem withStep_stepTab_op_apply' (k : StepIdx A.slots A.post) (i : (A.absorb F.base).R)
    (y x : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    ((A.withStep st').stepTab F k).op i y x =
      (st' k).op i.1.2 (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm y))
        (A.tabPart F (A.afterAtTab F k x)) *
      (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) _ ℂ)
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm y)) (A.tabRest F (A.afterAtTab F k x))
      :=
  stepTab_op_apply' (A.withStep st') F k i y x

variable {L : Type} {ℓ : A.W → Option L} {r : L}

/-- **The absorbed steps agree on the block along the witness swaps**, in the entries of
`stepTab_op_apply'`. -/
theorem stepTab_hop_swap_core {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)}
    (h : A.BlockRel st' ℓ G G' G₀ G₀' (fun n => A.jTrip σW sw J (some n))
      (A.jTrip σW sw J none) r)
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (hF : F.SwapInv sw σ₁) (hJ : A.JSlotStep G G₀ J) (k : StepIdx A.slots A.post) (i : A.R)
    (a b : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (ha : InBlock ℓ r a.workspace.1.work ∧ a.1 ∈ A.tabSet F G G₀ (some k))
    (hb : InBlock ℓ r b.workspace.1.work ∧ b.1 ∈ A.tabSet F G G₀ (prevIdx k)) :
    (st' k).op i (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm
        (tripPerm (A.tTrip F σW sw J σ₁ (some k)) a)))
        (A.tabPart F (A.afterAtTab F k (tripPerm (A.tTrip F σW sw J σ₁ (prevIdx k)) b))) *
      (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) _ ℂ)
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm
          (tripPerm (A.tTrip F σW sw J σ₁ (some k)) a)))
        (A.tabRest F (A.afterAtTab F k (tripPerm (A.tTrip F σW sw J σ₁ (prevIdx k)) b))) =
    (A.step k).op i (A.tabPart F ((A.tabLift F (A.setAt F.base k)).symm a))
        (A.tabPart F (A.afterAtTab F k b)) *
      (1 : Matrix (A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂) _ ℂ)
        (A.tabRest F ((A.tabLift F (A.setAt F.base k)).symm a))
        (A.tabRest F (A.afterAtTab F k b)) := by
  have hk : ∀ x : A.W × Req × Option Resp, A.kind (σW x.1) = A.kind x.1 := h.kind_eq 0
  rw [tabLift_symm_tTrip hk hF, afterAtTab_tTrip hF, tabPart_tTrip, tabPart_tTrip,
    tabRest_tTrip, tabRest_tTrip]
  set x := (A.tabLift F (A.setAt F.base k)).symm a
  set y := A.afterAtTab F k b
  obtain ⟨hm1, hm2, hm3⟩ := mem_midSet_afterAtTab hG k b hb.2
  have hX : InBlock ℓ r (A.tabPart F x).workspace ∧ (A.tabPart F x).1 ∈ G k := by
    refine ⟨?_, ?_⟩
    · change InBlock ℓ r x.1.1.1.work
      rw [work_tabLift_symm]
      exact ha.1
    · rw [triple_tabLift_symm]
      exact ha.2.1
  have hY : InBlock ℓ r (A.tabPart F y).workspace ∧ (A.tabPart F y).1 ∈ prevSeq G G₀ k := by
    refine ⟨?_, ?_⟩
    · change InBlock ℓ r y.1.1.1.work
      rw [work_afterAtTab]
      exact hb.1
    · rw [prevSeq_eq_idxSet]
      exact hm1
  have hop := h.hop k i _ _ hX hY
  rw [prevSeq_eq_idx (fun idx => A.jTrip σW sw J idx)] at hop
  rw [hop]
  by_cases hz : (A.step k).op i (A.tabPart F x) (A.tabPart F y) = 0
  · rw [hz, zero_mul, zero_mul]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  exact if_congr (restSw_eq_iff hF.default (hJ k i _ _ hY.2 hz) _ _ hm2 hm3) rfl rfl

theorem swIf_eq_default_iff (hd : σ₁ default = default) (p : Prop) [Decidable p] (z : Req₁) :
    swIf p σ₁ z = default ↔ z = default := by
  by_cases hp : p
  · rw [swIf_apply_of _ hp, ← hd, σ₁.injective.eq_iff, hd]
  · rw [swIf_apply_of_not _ hp]

/-- **The witness swap keeps the well-formed states**, when its part on `A`'s registers keeps
the set of the index. -/
theorem tTrip_mem_tabSet {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)} (hF : F.SwapInv sw σ₁) (idx : Option ℕ)
    (hS : ∀ x, InBlock ℓ r x.1 →
      (A.jTrip σW sw J idx x ∈ idxSet G' G₀' idx ↔ x ∈ idxSet G G₀ idx))
    (x : ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) × Req₁ × Option Resp₁)
    (hx : InBlock ℓ r x.1.1.work) :
    A.tTrip F σW sw J σ₁ idx x ∈ A.tabSet F G' G₀' idx ↔ x ∈ A.tabSet F G G₀ idx := by
  obtain ⟨⟨⟨w, q, a, lg, s⟩, t⟩, z, y⟩ := x
  have hlog : (∀ i : Fin A.slots, AfterIdx idx i → A.logSw sw (J w) lg i = none) ↔
      (∀ i : Fin A.slots, AfterIdx idx i → lg i = none) := by
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [logSw_apply]
    cases lg i <;> simp
  have hslot : SlotCond A F idx (A.logSw sw (J w) lg) (swIf (Hit J w idx) σ₁ z) ↔
      SlotCond A F idx lg z := by
    cases idx with
    | none =>
      simp only [SlotCond]
      rw [swIf_apply_of_not _ (not_hit_none J w)]
    | some n =>
      simp only [SlotCond]
      split_ifs with hn
      · rw [logSw_apply, reqCount_logSw, swIf_congr σ₁ (hit_some J w n),
          swIf_eq_default_iff hF.default]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨q', h1, h2⟩)
          · left
            exact ⟨Option.map_eq_none_iff.1 h1, h2⟩
          · right
            obtain ⟨q₀, hq₀, rfl⟩ := Option.map_eq_some_iff.1 h1
            refine ⟨q₀, hq₀, ?_⟩
            rw [hF.route_swIf] at h2
            exact (swIf (J w = some n) σ₁).injective h2
        · rintro (⟨h1, h2⟩ | ⟨q', h1, h2⟩)
          · left
            exact ⟨by rw [h1]; rfl, h2⟩
          · right
            refine ⟨swIf (J w = some (n : ℕ)) sw q', by rw [h1]; rfl, ?_⟩
            rw [h2, hF.route_swIf]
      · exact swIf_eq_default_iff hF.default _ z
  exact and_congr (hS (w, q, a) hx) (and_congr hlog hslot)

theorem restSw_none_of_blank (jw : Option ℕ)
    (u : A.AbsRest (Req' := Req₁) (Resp' := Resp₁) × A.OuterTab Req₂ Resp₂)
    (hu : ∀ i, u.1.1 i = none) : A.restSw sw σ₁ jw none u = u := by
  obtain ⟨⟨lg, s, z, y⟩, t⟩ := u
  have hu' : ∀ i, lg i = none := hu
  have hl : A.logSw sw jw lg = lg := funext fun i => by
    rw [logSw_apply, hu' i]
    rfl
  simp only [restSw, hl]
  rw [swIf_apply_of_not _ (by simp)]

theorem stepTab_hop_field {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)}
    (h : A.BlockRel st' ℓ G G' G₀ G₀' (fun n => A.jTrip σW sw J (some n))
      (A.jTrip σW sw J none) r)
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (hF : F.SwapInv sw σ₁) (hJ : A.JSlotStep G G₀ J) (k : StepIdx A.slots A.post) :
    OpRelOn₂ (tripPerm (A.tTrip F σW sw J σ₁ (some k)))
      (tripPerm (prevSeq (fun n => A.tTrip F σW sw J σ₁ (some n)) (A.tTrip F σW sw J σ₁ none) k))
      {d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁ |
        InBlock ℓ r d.workspace.1.work ∧ d.1 ∈ A.tabSet F G G₀ (some k)}
      {d | InBlock ℓ r d.workspace.1.work ∧
        d.1 ∈ prevSeq (fun n => A.tabSet F G G₀ (some n)) (A.tabSet F G G₀ none) k}
      (A.stepTab F k) ((A.withStep st').stepTab F k) := by
  rw [prevSeq_eq_idx (A.tTrip F σW sw J σ₁), prevSeq_tabSet]
  intro i a b ha hb
  exact (withStep_stepTab_op_apply' st' k i _ _).trans
    ((stepTab_hop_swap_core st' h hG hF hJ k i.1.2 a b ha hb).trans
      (stepTab_op_apply' A F k i a b).symm)

theorem init_eq_absorbTab {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)}
    (h : A.BlockRel st' ℓ G G' G₀ G₀' (fun n => A.jTrip σW sw J (some n))
      (A.jTrip σW sw J none) r)
    (tab : A.OuterTab Req₂ Resp₂)
    (a b : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
    (ha : a.1 ∈ A.tabSet F G G₀ none) (hb : b.1 ∈ A.tabSet F G G₀ none)
    (hla : InBlock ℓ r a.workspace.1.work) (hlb : InBlock ℓ r b.workspace.1.work) :
    (A.absorbTab F tab).init.mat (tripPerm (A.tTrip F σW sw J σ₁ none) a)
      (tripPerm (A.tTrip F σW sw J σ₁ none) b) = (A.absorbTab F tab).init.mat a b := by
  have e1 := init_absorbTab_mat A F tab (tripPerm (A.tTrip F σW sw J σ₁ none) a)
    (tripPerm (A.tTrip F σW sw J σ₁ none) b)
  refine e1.trans (Eq.trans ?_ (init_absorbTab_mat A F tab a b).symm)
  rw [tabPart_tTrip, tabPart_tTrip, tabRest_tTrip,
    tabRest_tTrip, restSw_none_of_blank _ _ (fun i => ha.2.1 i trivial),
    restSw_none_of_blank _ _ (fun i => hb.2.1 i trivial),
    h.init_eq (A.tabPart F a) (A.tabPart F b) ha.1 hb.1 hla hlb]

variable [DecidableEq L] in
/-- **The block hypotheses through the absorption with a table, along the witness swap at one
slot**: for a relay that does not see `sw` (`hF`), sets closed under changes of the response
(`hG`), and a recorded slot `J` that changes only at its step (`hJ`), the block hypotheses of `A`
and `st'` along `jTrip` give those of the absorbed adversaries along `tTrip` and the well-formed
states `tabSet`, with the label read on `A`'s workspace. -/
theorem BlockRel.absorbTab {G G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀ G₀' : Set (A.W × Req × Option Resp)}
    (h : A.BlockRel st' ℓ G G' G₀ G₀' (fun n => A.jTrip σW sw J (some n))
      (A.jTrip σW sw J none) r)
    (hG : ∀ idx w q a a', (w, q, a) ∈ idxSet G G₀ idx → (w, q, a') ∈ idxSet G G₀ idx)
    (hG' : ∀ idx w q a a', (w, q, a) ∈ idxSet G' G₀' idx → (w, q, a') ∈ idxSet G' G₀' idx)
    (hF : F.SwapInv sw σ₁) (hJ : A.JSlotStep G G₀ J) (tab : A.OuterTab Req₂ Resp₂) :
    (A.absorbTab F tab).BlockRel (A.absorbTabStep F st') (fun w => ℓ w.1.work)
      (fun n => A.tabSet F G G₀ (some n)) (fun n => A.tabSet F G' G₀' (some n))
      (A.tabSet F G G₀ none) (A.tabSet F G' G₀' none)
      (fun n => A.tTrip F σW sw J σ₁ (some n)) (A.tTrip F σW sw J σ₁ none) r where
  label_eq n x := h.label_eq n (x.1.1.work, x.1.1.request, x.1.1.response)
  label_eq₀ x := h.label_eq₀ (x.1.1.work, x.1.1.request, x.1.1.response)
  kind_eq n x := h.kind_eq n (x.1.1.work, x.1.1.request, x.1.1.response)
  set_eq n x hx := tTrip_mem_tabSet hF (some n) (h.set_eq n) x hx
  set_eq₀ x hx := tTrip_mem_tabSet hF none h.set_eq₀ x hx
  keepsSet k i := keepsSet_stepTab_prev (st := A.step) hG (h.keepsSet k) i
  keepsSet' k i := keepsSet_stepTab_prev (st := st') hG' (h.keepsSet' k) i
  keeps k i := keepsBlocksOn_stepTab_prev (st := A.step) hG (h.keeps k) i
  keeps' k i := keepsBlocksOn_stepTab_prev (st := st') hG' (h.keeps' k) i
  hop k := stepTab_hop_field st' h hG hF hJ k
  init_supp a b hab := init_supp_absorbTab G h.init_supp tab a b hab
  init_supp' a b hab := init_supp_absorbTab G' h.init_supp' tab a b hab
  init_eq a b ha hb hla hlb := init_eq_absorbTab st' h tab a b ha hb hla hlb

end Swap

end AdaptiveIAlg


end GordieHowe.Quantum
