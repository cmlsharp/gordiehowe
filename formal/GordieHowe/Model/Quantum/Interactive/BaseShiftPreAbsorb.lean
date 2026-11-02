-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftPre
public import GordieHowe.Model.Quantum.Interactive.AbsorbTabBlock

@[expose] public section

/-!
# Read-after permutations at the absorbed base

The trace-preserving form of an adversary absorbed with a table, with only its steps replaced by
`absorbTabStep F st'`, is read after (followed by) the permutation when `st'` is. The statement is at the
absorbed base `B.absorbTab F tab`, so no term mentions `B.withStep st'` absorbed.

- `AdaptiveIAlg.rightPerm_absorbTabStep_toTP`, `AdaptiveIAlg.leftPerm_absorbTabStep_toTP`.
- `AdaptiveIAlg.leftPerm_toTPKindAlg_steps`, `AdaptiveIAlg.leftPerm_absorbTabStep_toTP_steps`: against
  replaced steps on both sides.
- `AdaptiveIAlg.rightPerm_tpStepOf`, `AdaptiveIAlg.rightPerm_absorbTabStep_tpStepOf`: at
  `AdaptiveIAlg.tpStepOf`.
-/

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shB : AlgShape X Y Req Resp} {B : AdaptiveIAlg shB O} {F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂}

/-- **The trace-preserving form of `B` absorbed with a table, with the steps `absorbTabStep F st'`,
is read after the permutation** when `st'` is (`h`), for trace-preserving adversaries. -/
theorem rightPerm_absorbTabStep_toTP
    (st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.RightPerm π (st' k) (B.step k)) (hTP' : (B.withStep st').TracePreserving)
    (hTP : B.TracePreserving) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.RightPerm ((B.absorbTab F tab).cntPerm (preTabPerm F tab k π))
      (((B.absorbTab F tab).withStep (B.absorbTabStep F st')).toTPKindAlg.step k)
      ((B.absorbTab F tab).toTPKindAlg.step k) :=
  rightPerm_absorbTab_toTP st' k h hTP' hTP tab

/-- **The trace-preserving form of `B` absorbed with a table, with the steps `absorbTabStep F st'`,
is followed by the permutation** when `st'` is (`h`), for trace-preserving adversaries and a
permutation that keeps the kind and the request register. -/
theorem leftPerm_absorbTabStep_toTP
    (st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.LeftPerm π (st' k) (B.step k)) (hkind : ∀ d, B.kind (π d).1.1 = B.kind d.1.1)
    (hreq : ∀ d, (π d).1.2.1 = d.1.2.1) (hTP' : (B.withStep st').TracePreserving)
    (hTP : B.TracePreserving) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.LeftPerm (tpPermOf F tab π)
      (((B.absorbTab F tab).withStep (B.absorbTabStep F st')).toTPKindAlg.step k)
      ((B.absorbTab F tab).toTPKindAlg.step k) :=
  leftPerm_absorbTab_toTP st' k h hkind hreq hTP' hTP tab

/-- **The trace-preserving form with the Kraus maps `y` is followed by the permutation** against
that with the Kraus maps `x`, when `y` is `x` followed by it (`h`), for trace-preserving steps
and a permutation that keeps the kind (`AdaptiveIAlg.leftPerm_toTPKindAlg` at `C.withStep x`). -/
theorem leftPerm_toTPKindAlg_steps {shC : AlgShape X Y Req Resp} {C : AdaptiveIAlg shC O}
    {x y : StepIdx C.slots C.post → KrausMap C.R (DReg C.W C.width X Y Req Resp)
      (DReg C.W C.width X Y Req Resp)} {π : Equiv.Perm (DReg C.W C.width X Y Req Resp)}
    (k : StepIdx C.slots C.post) (h : KrausMap.LeftPerm π (y k) (x k))
    (hkind : ∀ d, C.kind (π d).1.1 = C.kind d.1.1)
    (hTP' : (C.withStep y).TracePreserving) (hTP : (C.withStep x).TracePreserving) :
    KrausMap.LeftPerm (C.cntPerm π) ((C.withStep y).toTPKindAlg.step k)
      ((C.withStep x).toTPKindAlg.step k) :=
  leftPerm_toTPKindAlg (C := C.withStep x) (st' := y) k h hkind hTP' hTP

/-- **The trace-preserving form of `B` absorbed with a table, with the steps `absorbTabStep F st'`,
is followed by the permutation** against that with the steps `absorbTabStep F s`, when `st'` is
`s` followed by it (`h`), for trace-preserving adversaries and a permutation that keeps the kind
and the request register. -/
theorem leftPerm_absorbTabStep_toTP_steps
    (s st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.LeftPerm π (st' k) (s k)) (hkind : ∀ d, B.kind (π d).1.1 = B.kind d.1.1)
    (hreq : ∀ d, (π d).1.2.1 = d.1.2.1) (hTP' : (B.withStep st').TracePreserving)
    (hTP : (B.withStep s).TracePreserving) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.LeftPerm (tpPermOf F tab π)
      (((B.absorbTab F tab).withStep (B.absorbTabStep F st')).toTPKindAlg.step k)
      (((B.absorbTab F tab).withStep (B.absorbTabStep F s)).toTPKindAlg.step k) :=
  leftPerm_toTPKindAlg_steps (C := B.absorbTab F tab) k
    (leftPerm_stepTab (B := B.withStep s) (F := F) st' k h hkind hreq tab) (fun _ => hkind _)
    (absorbTab_tracePreserving (B.withStep st') F hTP' tab)
    (absorbTab_tracePreserving (B.withStep s) F hTP tab)

/-- **The trace-preserving steps with the Kraus maps `y` are read after the permutation** against
`C`'s, when `y` is `C`'s read after it (`h`), for trace-preserving steps
(`AdaptiveIAlg.rightPerm_toTPKindAlg` at `AdaptiveIAlg.tpStepOf`). -/
theorem rightPerm_tpStepOf {shC : AlgShape X Y Req Resp} {C : AdaptiveIAlg shC O}
    {y : StepIdx C.slots C.post → KrausMap C.R (DReg C.W C.width X Y Req Resp)
      (DReg C.W C.width X Y Req Resp)} {π : Equiv.Perm (DReg C.W C.width X Y Req Resp)}
    (k : StepIdx C.slots C.post) (h : KrausMap.RightPerm π (y k) (C.step k))
    (hTP' : (C.withStep y).TracePreserving) (hTP : C.TracePreserving) :
    KrausMap.RightPerm (C.cntPerm π) (C.tpStepOf false y k) (C.toTPKindAlg.step k) :=
  rightPerm_toTPKindAlg (C := C) (st' := y) k h hTP' hTP

/-- **The trace-preserving steps of `B` absorbed with a table, with the Kraus maps `st'`, are read
after the permutation** against `B`'s when `st'` is (`h`), at the registers of `B` absorbed with
the table (`AdaptiveIAlg.tpStepOf`). -/
theorem rightPerm_absorbTabStep_tpStepOf
    (st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.RightPerm π (st' k) (B.step k)) (hTP' : (B.withStep st').TracePreserving)
    (hTP : B.TracePreserving) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.RightPerm ((B.absorbTab F tab).cntPerm (preTabPerm F tab k π))
      ((B.absorbTab F tab).tpStepOf false ((B.withStep st').stepTab F) k)
      ((B.absorbTab F tab).toTPKindAlg.step k) :=
  rightPerm_tpStepOf (C := B.absorbTab F tab) k (rightPerm_stepTab st' k h tab)
    (absorbTab_tracePreserving (B.withStep st') F hTP' tab)
    (absorbTab_tracePreserving B F hTP tab)

end AdaptiveIAlg

end GordieHowe.Quantum
