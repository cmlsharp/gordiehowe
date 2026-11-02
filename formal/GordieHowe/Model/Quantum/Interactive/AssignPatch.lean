-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignPairs
public import GordieHowe.Model.Quantum.Interactive.QueryBounded
public import GordieHowe.Model.Quantum.Interactive.Absorb

@[expose] public section

/-!
# An adversary that patches its queries with a table it holds

`AdaptiveIAlg.patchTag B tab out'`: the adversary `B` with each of its queries replaced by the
reprogrammed query (`GordieHowe/Model/Quantum/Core/Reprogram.lean`, Unruh 2017, ePrint 2017/398,
p. 12) for the table `tab w` read from its workspace, and each of its requests tagged with that
table. Its workspace is `B`'s with the ancillas of the `width` query pairs (`AncReg`, clean:
`ancMat`); its request register is `B`'s with a table register, blank `fun _ => none`.

The reprogrammed query of a query slot is split across the two steps around the slot: the step
before the slot ends with the exchange `ancSwap` of each query pair with its ancilla, on the
branches whose input has an entry in the table (`swapP`); the slot queries; the step after the slot
starts with the exchange again and the addition of the table entry (`finishP`). On a request
branch the step before the slot writes the table into the table register and the step after it
clears it (`tagP`). The post batches are patched in the same way, on every branch.

- `MState.tensor`: the product of two mixed states.
- `ancState x₀`: the clean ancillas as a mixed state.
- `patchSplit`, `swapP`, `finishP`, `tagP`, `patchBefore`, `patchAfter`, `patchTag`; its shape
  `AlgShape.patchTagS` (`patchTag_toShape`).
- `patchTag_tracePreserving`: the steps are `B`'s, tensored with the identity, between basis
  permutations.

-/

open Finset Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

namespace GordieHowe.Quantum

/-! ### Product states -/

/-- **The product of two mixed states**: `ρ ⊗ σ`. -/
noncomputable def MState.tensor {ι κ : Type*} [Fintype ι] [Fintype κ] (ρ : MState ι)
    (σ : MState κ) : MState (ι × κ) where
  mat := ρ.mat ⊗ₖ σ.mat
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_eq_one := by rw [trace_kronecker, ρ.trace_eq_one, σ.trace_eq_one, one_mul]

section Anc

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {n : ℕ}

/-- The clean ancillas as a normalized vector: `ancMat = ancVecᴴ * ancVec` (`ancMat_eq`). -/
noncomputable def ancVec (x₀ : X) : Matrix Unit (AncReg X Y n) ℂ :=
  Matrix.of fun _ a => ∏ i, ancWeight x₀ (a i) / (Real.sqrt (Fintype.card Y) : ℂ)

theorem ancMat_eq (x₀ : X) : ancMat (Y := Y) (n := n) x₀ = (ancVec x₀)ᴴ * ancVec x₀ := by
  ext a a'
  simp only [ancMat, reprogAnc, Matrix.mul_apply, Matrix.conjTranspose_apply, ancVec,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton]
  have hw : ∀ b : X × Y × Bool, (starRingEnd ℂ) (ancWeight x₀ b) = ancWeight x₀ b := fun b => by
    unfold ancWeight
    split_ifs <;> simp
  have hs : (starRingEnd ℂ) (Real.sqrt (Fintype.card Y) : ℂ) = (Real.sqrt (Fintype.card Y) : ℂ) :=
    Complex.conj_ofReal _
  rw [star_prod]
  simp only [Complex.star_def, map_div₀, hw, hs, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [div_mul_div_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _),
    Complex.ofReal_natCast]

theorem trace_ancMat (x₀ : X) : (ancMat (Y := Y) (n := n) x₀).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, ancMat]
  rw [← Fintype.prod_sum fun (_ : Fin n) (b : X × Y × Bool) => reprogAnc (Y := Y) x₀ b b]
  refine Finset.prod_eq_one fun i _ => ?_
  have := trace_reprogAnc (Y := Y) x₀
  simpa [Matrix.trace] using this

/-- **The clean ancillas of `n` pairs as a mixed state.** -/
noncomputable def ancState (x₀ : X) : MState (AncReg X Y n) where
  mat := ancMat x₀
  posSemidef := by
    rw [ancMat_eq]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_eq_one := trace_ancMat x₀

end Anc

namespace AdaptiveIAlg

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (tab : B.W → X → Option Y)

/-- The workspace of the patched adversary at the shape `s`: `s`'s workspace and the ancillas. -/
def _root_.GordieHowe.Quantum.AlgShape.PatchWS (s : AlgShape X Y Req Resp) : Type :=
  s.W × AncReg X Y s.width

instance (s : AlgShape X Y Req Resp) : Fintype s.PatchWS :=
  inferInstanceAs (Fintype (s.W × AncReg X Y s.width))

instance (s : AlgShape X Y Req Resp) : DecidableEq s.PatchWS :=
  inferInstanceAs (DecidableEq (s.W × AncReg X Y s.width))

/-- The workspace `w` with the ancillas `a`, at the shape `s`. -/
def _root_.GordieHowe.Quantum.AlgShape.PatchWS.mk {s : AlgShape X Y Req Resp} (w : s.W)
    (a : AncReg X Y s.width) : s.PatchWS := (w, a)

@[simp] theorem _root_.GordieHowe.Quantum.AlgShape.PatchWS.fst_mk {s : AlgShape X Y Req Resp}
    (w : s.W) (a : AncReg X Y s.width) : (AlgShape.PatchWS.mk w a).1 = w := rfl

@[simp] theorem _root_.GordieHowe.Quantum.AlgShape.PatchWS.snd_mk {s : AlgShape X Y Req Resp}
    (w : s.W) (a : AncReg X Y s.width) : (AlgShape.PatchWS.mk w a).2 = a := rfl

theorem _root_.GordieHowe.Quantum.AlgShape.PatchWS.mk_inj {s : AlgShape X Y Req Resp}
    {w w' : s.W} {a a' : AncReg X Y s.width} :
    AlgShape.PatchWS.mk w a = AlgShape.PatchWS.mk w' a' ↔ w = w' ∧ a = a' :=
  Prod.mk.injEq w a w' a' ▸ Iff.rfl

/-- The workspace of the patched adversary: `B`'s workspace and the ancillas. -/
abbrev PatchW (_B : AdaptiveIAlg shB O) : Type := shB.PatchWS

/-- The rest of the patched adversary's registers beside the query pairs and the ancillas. -/
abbrev PatchV : Type := B.W × (Req × (X → Option Y)) × Option Resp

/-- The registers of the patched adversary. -/
abbrev PatchReg : Type := DReg B.PatchW B.width X Y (Req × (X → Option Y)) Resp

instance : DecidableEq B.PatchW := inferInstance

instance : DecidableEq B.PatchReg := DReg.instDecidableEq

instance (s : AlgShape X Y Req Resp) :
    DecidableEq (DReg s.W s.width X Y Req Resp × (AncReg X Y s.width × (X → Option Y))) :=
  @instDecidableEqProd _ _ DReg.instDecidableEq inferInstance

/-- The patched registers at the shape `s` as the query pairs with the rest, and the ancillas. -/
def _root_.GordieHowe.Quantum.AlgShape.patchSplit (s : AlgShape X Y Req Resp) :
    DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp ≃
      QueryReg (s.W × (Req × (X → Option Y)) × Option Resp) s.width X Y × AncReg X Y s.width where
  toFun d := (((d.1.1.1, d.1.2.1, d.1.2.2), d.2), d.1.1.2)
  invFun p := (((p.1.1.1, p.2), p.1.1.2.1, p.1.1.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The patched registers as the query pairs with the rest, and the ancillas
(`AlgShape.patchSplit` at `B`'s shape). -/
abbrev patchSplit : B.PatchReg ≃ QueryReg B.PatchV B.width X Y × AncReg X Y B.width :=
  shB.patchSplit

/-- The patched registers at the shape `s` as the registers of `s` and the ancillas with the table
register. -/
def _root_.GordieHowe.Quantum.AlgShape.patchSplitB (s : AlgShape X Y Req Resp) :
    DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp ≃
      DReg s.W s.width X Y Req Resp × (AncReg X Y s.width × (X → Option Y)) where
  toFun d := (((d.1.1.1, d.1.2.1.1, d.1.2.2), d.2), (d.1.1.2, d.1.2.1.2))
  invFun p := (((p.1.1.1, p.2.1), (p.1.1.2.1, p.2.2), p.1.1.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The patched registers as `B`'s registers and the ancillas with the table register
(`AlgShape.patchSplitB` at `B`'s shape). -/
abbrev patchSplitB : B.PatchReg ≃
    DReg B.W B.width X Y Req Resp × (AncReg X Y B.width × (X → Option Y)) :=
  shB.patchSplitB

variable [AddGroup Y]

/-- **The exchanges with the ancillas** at the shape `s` (`ancSwap` for the table `tb` of the
workspace), on the branches selected by `on`. -/
def _root_.GordieHowe.Quantum.AlgShape.swapP (s : AlgShape X Y Req Resp)
    (tb : s.W → X → Option Y) (on : s.W → Bool) :
    Equiv.Perm (DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp) :=
  s.patchSplit.symm.permCongr
    (liftPairs fun v => if on v.1 then ancSwap (tb v.1) else Equiv.refl _)

/-- **The exchanges with the ancillas** (`ancSwap` for the table of the workspace), on the
branches selected by `on` (`AlgShape.swapP`). -/
abbrev swapP (on : B.W → Bool) : Equiv.Perm B.PatchReg := shB.swapP tab on

/-- **The end of a reprogrammed query** at the shape `s`: the exchanges with the ancillas and the
addition of the table entries, on the branches selected by `on`. -/
def _root_.GordieHowe.Quantum.AlgShape.finishP (s : AlgShape X Y Req Resp)
    (tb : s.W → X → Option Y) (on : s.W → Bool) :
    Equiv.Perm (DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp) :=
  s.patchSplit.symm.permCongr (liftPairs fun v => if on v.1 then
    (ancSwap (tb v.1)).trans (ancAdd fun x => (tb v.1 x).getD 0) else Equiv.refl _)

/-- **The end of a reprogrammed query**: the exchanges with the ancillas and the addition of the
table entries, on the branches selected by `on` (`AlgShape.finishP`). -/
abbrev finishP (on : B.W → Bool) : Equiv.Perm B.PatchReg := shB.finishP tab on

/-- **The tag of a request** at the shape `s`: the table `tb` of the workspace swapped with the
blank table in the table register, on the branches selected by `on`. An involution. -/
def _root_.GordieHowe.Quantum.AlgShape.tagP (s : AlgShape X Y Req Resp)
    (tb : s.W → X → Option Y) (on : s.W → Bool) :
    Equiv.Perm (DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp) :=
  Function.Involutive.toPerm
    (fun d => if on d.1.1.1 then
      ((d.1.1, (d.1.2.1.1, Equiv.swap (fun _ => none) (tb d.1.1.1) d.1.2.1.2), d.1.2.2), d.2)
      else d)
    fun d => by
      by_cases h : on d.1.1.1 = true
      · simp [h]
      · simp [h]

/-- **The tag of a request**: the table of the workspace swapped with the blank table in the table
register, on the branches selected by `on` (`AlgShape.tagP`). An involution. -/
abbrev tagP (on : B.W → Bool) : Equiv.Perm B.PatchReg := shB.tagP tab on

/-- **The permutation before slot `k`** at the shape `s`, for the kind `kind` and the table `tb`:
on a request branch the tag, on a query branch the exchanges; before a post batch the exchanges
on every branch; the identity after the last batch. -/
def _root_.GordieHowe.Quantum.AlgShape.patchBefore (s : AlgShape X Y Req Resp)
    (kind : s.W → Bool) (tb : s.W → X → Option Y) (k : ℕ) :
    Equiv.Perm (DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp) :=
  if k < s.slots then (s.tagP tb kind).trans (s.swapP tb fun w => !kind w)
  else if k < s.slots + s.post then s.swapP tb fun _ => true
  else Equiv.refl _

/-- **The permutation before slot `k`** (`AlgShape.patchBefore` at `B`'s kind). -/
abbrev patchBefore (k : ℕ) : Equiv.Perm B.PatchReg := shB.patchBefore B.kind tab k

/-- **The permutation after slot `k - 1`** at the shape `s`, for the kind `kind` and the table
`tb`: on a request branch the tag cleared, on a query branch the end of the reprogrammed query;
after a post batch the end of the reprogrammed query on every branch; the identity for
`k = 0`. -/
def _root_.GordieHowe.Quantum.AlgShape.patchAfter (s : AlgShape X Y Req Resp)
    (kind : s.W → Bool) (tb : s.W → X → Option Y) (k : ℕ) :
    Equiv.Perm (DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp) :=
  if 0 < k ∧ k - 1 < s.slots then (s.tagP tb kind).trans (s.finishP tb fun w => !kind w)
  else if s.slots < k then s.finishP tb fun _ => true
  else Equiv.refl _

/-- **The permutation after slot `k - 1`** (`AlgShape.patchAfter` at `B`'s kind). -/
abbrev patchAfter (k : ℕ) : Equiv.Perm B.PatchReg := shB.patchAfter B.kind tab k

/-- The step `step k` at the shape `s` on its registers, the identity on the ancillas and the
table register. -/
def _root_.GordieHowe.Quantum.AlgShape.patchLifted (s : AlgShape X Y Req Resp)
    (step : StepIdx s.slots s.post →
      KrausMap s.R (DReg s.W s.width X Y Req Resp) (DReg s.W s.width X Y Req Resp))
    (k : StepIdx s.slots s.post) :
    KrausMap s.R (DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp)
      (DReg s.PatchWS s.width X Y (Req × (X → Option Y)) Resp) :=
  ((step k).tensorId (AncReg X Y s.width × (X → Option Y))).reindex s.patchSplitB.symm

/-- The permutation before slot `k` through `B`'s helpers. -/
theorem patchBefore_def (k : ℕ) : B.patchBefore tab k =
    if k < B.slots then (B.tagP tab B.kind).trans (B.swapP tab fun w => !B.kind w)
    else if k < B.slots + B.post then B.swapP tab fun _ => true
    else Equiv.refl _ :=
  rfl

/-- The permutation after slot `k - 1` through `B`'s helpers. -/
theorem patchAfter_def (k : ℕ) : B.patchAfter tab k =
    if 0 < k ∧ k - 1 < B.slots then (B.tagP tab B.kind).trans (B.finishP tab fun w => !B.kind w)
    else if B.slots < k then B.finishP tab fun _ => true
    else Equiv.refl _ :=
  rfl

/-- `B`'s step `k` on its registers, the identity on the ancillas and the table register
(`AlgShape.patchLifted`). -/
abbrev patchLifted (k : StepIdx B.slots B.post) : KrausMap B.R B.PatchReg B.PatchReg :=
  shB.patchLifted B.step k

variable [Nonempty X] [Nonempty Y]

omit [Nonempty X] [Nonempty Y] in
/-- **The shape of the patched adversary** (`patchTag`): the workspace with the ancillas, the
Kraus index between the two permutations. -/
@[reducible] def _root_.GordieHowe.Quantum.AlgShape.patchTagS (s : AlgShape X Y Req Resp) :
    AlgShape X Y (Req × (X → Option Y)) Resp where
  W := s.PatchWS
  width := s.width
  width_pos := s.width_pos
  slots := s.slots
  post := s.post
  budget := s.budget
  R := (Unit × s.R) × Unit

/-- **The initial state of the patched adversary** at the shape `s`: `init` with clean ancillas
and a blank table register. Sealed; it unfolds through `AlgShape.patchInit_eq`. -/
@[irreducible, no_expose] noncomputable def _root_.GordieHowe.Quantum.AlgShape.patchInit
    (s : AlgShape X Y Req Resp) (init : MState (DReg s.W s.width X Y Req Resp)) :
    MState (DReg s.patchTagS.W s.patchTagS.width X Y (Req × (X → Option Y)) Resp) :=
  MState.reindex s.patchSplitB.symm
    (init.tensor ((ancState KindAlg.x₀).tensorKet (fun _ => none : X → Option Y)))

theorem _root_.GordieHowe.Quantum.AlgShape.patchInit_eq (s : AlgShape X Y Req Resp)
    (init : MState (DReg s.W s.width X Y Req Resp)) :
    s.patchInit init = MState.reindex s.patchSplitB.symm
      (init.tensor ((ancState KindAlg.x₀).tensorKet (fun _ => none : X → Option Y))) := by
  unfold AlgShape.patchInit; rfl

/-- **Step `k` of the patched adversary** at the shape `s`, for the kind `kind`, the steps `step`
and the table `tb`: `patchAfter k`, `step k`, `patchBefore k`. Sealed; it reads only the kind,
the steps and the table, and unfolds through `AlgShape.patchStep_eq`. -/
@[irreducible, no_expose] noncomputable def _root_.GordieHowe.Quantum.AlgShape.patchStep
    (s : AlgShape X Y Req Resp) (kind : s.W → Bool)
    (step : StepIdx s.slots s.post →
      KrausMap s.R (DReg s.W s.width X Y Req Resp) (DReg s.W s.width X Y Req Resp))
    (tb : s.W → X → Option Y) (k : StepIdx s.slots s.post) :
    KrausMap s.patchTagS.R (DReg s.patchTagS.W s.patchTagS.width X Y (Req × (X → Option Y)) Resp)
      (DReg s.patchTagS.W s.patchTagS.width X Y (Req × (X → Option Y)) Resp) :=
  (KrausMap.ofPerm (s.patchBefore kind tb k)).comp
    ((s.patchLifted step k).comp (KrausMap.ofPerm (s.patchAfter kind tb k)))

theorem _root_.GordieHowe.Quantum.AlgShape.patchStep_eq (s : AlgShape X Y Req Resp)
    (kind : s.W → Bool)
    (step : StepIdx s.slots s.post →
      KrausMap s.R (DReg s.W s.width X Y Req Resp) (DReg s.W s.width X Y Req Resp))
    (tb : s.W → X → Option Y) (k : StepIdx s.slots s.post) :
    s.patchStep kind step tb k = (KrausMap.ofPerm (s.patchBefore kind tb k)).comp
      ((s.patchLifted step k).comp (KrausMap.ofPerm (s.patchAfter kind tb k))) := by
  unfold AlgShape.patchStep; rfl

/-- **The adversary with its queries patched by the table `tab` of its workspace and its requests
tagged with it** (module docstring). Step `k` is `patchAfter k`, `B`'s step, `patchBefore k`. The
initial state is `B`'s with clean ancillas and a blank table register; the kind is `B`'s; the
output is `out'` of `B`'s workspace; the width, the slots, the post batches and the budget are
`B`'s. The initial state and the steps are the sealed `AlgShape.patchInit` and
`AlgShape.patchStep`, of `B`'s fields only (`patchTag_init`, `patchTag_step`).

Running time: that of `B`, plus `B.width` clean ancilla pairs and, around each Kraus map, the
basis permutations `patchBefore` and `patchAfter`: on each branch one evaluation of `tab` on the
workspace, then the table written into or cleared from the request register (`tagP`), or one
lookup of the table and one exchange with an ancilla per query pair, with the table entry added
after the query (`swapP`, `finishP`); polynomial when `B` and `tab` are. This running time is
argued here, not proved in Lean. -/
noncomputable abbrev patchTag (out' : B.W → O') : AdaptiveIAlg shB.patchTagS O' where
  kind w := B.kind w.1
  init := shB.patchInit B.init
  step := shB.patchStep B.kind B.step tab
  out w := out' w.1

/-- The kind of the patched adversary: `B`'s, of `B`'s workspace. -/
theorem patchTag_kind (out' : B.W → O') : (B.patchTag tab out').kind = fun w => B.kind w.1 := by
  rfl

/-- The initial state of the patched adversary: `B`'s with clean ancillas and a blank table
register. -/
theorem patchTag_init (out' : B.W → O') :
    (B.patchTag tab out').init = MState.reindex B.patchSplitB.symm
      (B.init.tensor ((ancState KindAlg.x₀).tensorKet (fun _ => none : X → Option Y))) :=
  shB.patchInit_eq B.init

/-- Step `k` of the patched adversary: `patchAfter k`, `B`'s step `k`, `patchBefore k`. -/
theorem patchTag_step (out' : B.W → O') (k : StepIdx B.slots B.post) :
    (B.patchTag tab out').step k = (KrausMap.ofPerm (B.patchBefore tab k)).comp
      ((B.patchLifted k).comp (KrausMap.ofPerm (B.patchAfter tab k))) :=
  shB.patchStep_eq B.kind B.step tab k

/-- The output of the patched adversary: `out'` of `B`'s workspace. -/
theorem patchTag_out (out' : B.W → O') : (B.patchTag tab out').out = fun w => out' w.1 := by
  rfl
theorem patchTag_toShape (out' : B.W → O') : (B.patchTag tab out').toShape = B.toShape.patchTagS :=
  rfl

/-- **Patching keeps trace preservation**: the steps are `B`'s, tensored with the identity,
between basis permutations. -/
theorem patchTag_tracePreserving (out' : B.W → O') (h : B.TracePreserving) :
    (B.patchTag tab out').TracePreserving := fun k => by
  rw [patchTag_step]
  exact KrausMap.comp_tp (KrausMap.tp_ofPerm _)
    (KrausMap.comp_tp (KrausMap.reindex_tp _ (KrausMap.tensorId_tp (h k) _)) (KrausMap.tp_ofPerm _))

end AdaptiveIAlg

end GordieHowe.Quantum
