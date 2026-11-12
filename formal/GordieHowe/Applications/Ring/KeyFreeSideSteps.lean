-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeRelayB
public import GordieHowe.Model.Quantum.Interactive.MultiRelaySideSteps
public import GordieHowe.Model.Quantum.Interactive.BaseShiftRestrict
public import GordieHowe.Model.Quantum.Interactive.AbortBlock
public import GordieHowe.Applications.Ring.KeyFreeBlock

@[expose] public section

/-!
# The side reads of the key-free relay as side steps

An adversary with the key-free relay in side-read mode (`kfRelaySide`) absorbed has, at every base
component `ω`, the Kraus maps of the adversary absorbed at the zero base component read after the
side reads of its relay (`AdaptiveIAlg.SideSteps`, `sideSteps_absorbAssign_kfRelaySide`): the relay
at `ω` is the relay at `0` with the side function `ω` (`relayOf_kfRelaySide`), and its steps are
those at zero after the side additions conjugated before each step
(`Distinguisher.relaySideS_rightPerm`).

- `AdaptiveIAlg.relaySideSt`, `AdaptiveIAlg.sideSteps_relayAdv`: the Kraus maps at a side
  function and the side reads, for any relay.
- `relayOf_kfRelaySide`, `absorbAssign_kfRelaySide_eq`, `sideSteps_absorbAssign_kfRelaySide`.
-/

namespace GordieHowe

open Quantum Signature QROM OracleProg RingSignature.OracleSplit

namespace Quantum.AdaptiveIAlg


variable {m : ℕ} {Y Y₁ Req Resp O Req' Resp' O' : Type} [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited Req']
  {shA : AlgShape (Bits m) Y Req Resp} (A : AdaptiveIAlg shA O) (F : MultiRelay (Bits m) Y Req Resp Req' Resp' (Bits m) Y₁)
  (Q : ℕ) (out' : A.RelayWS (F.withSide 0) → O')

/-- **The Kraus maps of the relayed adversary at the side function `ω`**, on its registers: the
trace-preserving form of the relayed distinguisher with the relay's unitaries at `ω`
(`Distinguisher.relayStepAt`). -/
noncomputable abbrev relaySideSt (ω : Bits m → Y₁) :
    StepIdx (A.relayAdv (F.withSide 0) Q out').slots (A.relayAdv (F.withSide 0) Q out').post →
      KrausMap (A.relayAdv (F.withSide 0) Q out').R
        (DReg (A.relayAdv (F.withSide 0) Q out').W (A.relayAdv (F.withSide 0) Q out').width
          (Bits m) Y Req' Resp')
        (DReg (A.relayAdv (F.withSide 0) Q out').W (A.relayAdv (F.withSide 0) Q out').width
          (Bits m) Y Req' Resp') :=
  (((A.relayD (F.withSide 0) Q).toAdaptive Nat.one_pos (A.relayBudget (F.withSide 0) Q)
      out').withStep
    (Distinguisher.relayStepAt A.pureD F (A.budget + A.post) Q ω)).toTPKindAlg.step

/-- **The side reads of the relayed adversary**: the side additions of the relay conjugated before
each step (`Distinguisher.relaySideS`), at every side function. -/
noncomputable def sideSteps_relayAdv :
    (A.relayAdv (F.withSide 0) Q out').SideSteps (A.relaySideSt F Q out') where
  S := Distinguisher.relaySideS A.pureD F (A.budget + A.post) Q Nat.one_pos _ out'
  keeps_kind ω k d := by
    simp only [AdaptiveIAlg.relayAdv_eq]
    rw [A.relayD_eq (F.withSide 0) Q]
    exact Distinguisher.relaySideS_kind _ _ _ _ _ _ _ ω k d
  keeps_rr ω k d := by
    simp only [AdaptiveIAlg.relayAdv_eq]
    rw [A.relayD_eq (F.withSide 0) Q]
    exact (Distinguisher.relaySideS_keeps _ _ _ _ _ _ _ ω k d).1
  keeps_pairs ω k d := by
    simp only [AdaptiveIAlg.relayAdv_eq]
    rw [A.relayD_eq (F.withSide 0) Q]
    exact (Distinguisher.relaySideS_keeps _ _ _ _ _ _ _ ω k d).2
  rightPerm ω k := by
    simp only [AdaptiveIAlg.relayAdv_eq]
    unfold relaySideSt
    rw [A.relayD_eq (F.withSide 0) Q]
    exact Distinguisher.relaySideS_rightPerm (q := A.relayBudget (F.withSide 0) Q) A.pureD F
      (A.budget + A.post) Q Nat.one_pos out' ω k
  tracePreserving ω k :=
    AdaptiveIAlg.toTPKindAlg_step_tp (((A.relayD (F.withSide 0) Q).toAdaptive Nat.one_pos
      (A.relayBudget (F.withSide 0) Q) out').withStep
        (Distinguisher.relayStepAt A.pureD F (A.budget + A.post) Q ω)) (freeze := false) k

omit [Nonempty Y] in
/-- **The numbers of the relayed adversary**: width one, no post batches, and
`Distinguisher.relaySlotsS` slots at `A`'s width and its slots and post batches. -/
theorem relayAdv_numbers (F' : MultiRelay (Bits m) Y Req Resp Req' Resp' (Bits m) Y₁)
    (out'' : A.RelayWS F' → O') :
    (A.relayAdv F' Q out'').width = 1 ∧ (A.relayAdv F' Q out'').post = 0 ∧
      (A.relayAdv F' Q out'').slots =
        Distinguisher.relaySlotsS A.width (A.slots + A.post) F'.K F'.qR F'.qP :=
  ⟨rfl, rfl, rfl⟩

omit [Nonempty Y] in
/-- **The side reads of the relayed adversary**: at most `qS` before each Kraus map. -/
theorem sideSteps_relayAdv_nb_le
    (j : StepIdx (A.relayAdv (F.withSide 0) Q out').slots (A.relayAdv (F.withSide 0) Q out').post) :
    (A.sideSteps_relayAdv F Q out').S.nb j ≤ F.qS := by
  change (if (j : ℕ) = 0 then 0 else (if 0 < _ then F.qS else 0)) ≤ _
  split_ifs <;> omega

omit [Nonempty Y] in
/-- **The side reads of the relayed adversary in all**: at most `qS` per Kraus map. -/
theorem sum_sideSteps_relayAdv_nb_le :
    ∑ j, (A.sideSteps_relayAdv F Q out').S.nb j ≤
      ((A.relayAdv (F.withSide 0) Q out').slots + 1) * F.qS := by
  refine (Finset.sum_le_card_nsmul _ _ _ fun j _ =>
    A.sideSteps_relayAdv_nb_le F Q out' j).trans ?_
  simp [StepIdx, (relayAdv_numbers (A := A) (Q := Q) (F.withSide 0) out').2.1]

omit [Nonempty Y] in
/-- **The relayed adversary at a side function is the one at zero with the Kraus maps at that side
function** (`relaySideSt`, `Distinguisher.toAdaptive_relay_withSide`). -/
theorem relayAdv_withSide_eq_withStep (ω : Bits m → Y₁) :
    A.relayAdv (F.withSide ω) Q out' = (A.relayAdv (F.withSide 0) Q out').withStep
      (A.relaySideSt F Q out' ω) := by
  simp only [AdaptiveIAlg.relayAdv_eq]
  unfold relaySideSt
  rw [A.relayD_eq (F.withSide ω) Q, A.relayD_eq (F.withSide 0) Q,
    Distinguisher.toAdaptive_relay_withSide]
  exact abortAlg_withStep _ _

omit [Nonempty Y] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited Req'] in
/-- **Side reads of an adversary are side reads of it with its output read through `g`.** -/
def SideSteps.mapOut {shB₀ : AlgShape (Bits m) Y Req Resp} {B₀ : AdaptiveIAlg shB₀ O}
    {st : (Bits m → Y₁) → StepIdx B₀.slots B₀.post → KrausMap B₀.R
      (DReg B₀.W B₀.width (Bits m) Y Req Resp) (DReg B₀.W B₀.width (Bits m) Y Req Resp)}
    (h : B₀.SideSteps st) (g : O → O') : (B₀.mapOut g).SideSteps st where
  S := h.S
  keeps_kind := h.keeps_kind
  keeps_rr := h.keeps_rr
  keeps_pairs := h.keeps_pairs
  rightPerm := h.rightPerm
  tracePreserving ω := AdaptiveIAlg.mapOut_tracePreserving (h.tracePreserving ω) g

section Family

variable [Inhabited Req] {shA₀ : AlgShape (Bits m) Y Req Resp} (A₀ : AdaptiveIAlg shA₀ O)
  (G : (Bits m → Y₁) → AssignRelay (Bits m) Y Req Resp Req' Resp' (Bits m) Y₁) (Q' : ℕ)

/-- **The relayed adversary of a family of assigning relays at zero**: `A₀` with its requests
absorbed (`absorbAssignP`), relayed through the relay of `G 0` at side zero.

Running time: that of `relayAdv` on `absorbAssignP` of `A₀`. This running time is argued here,
not proved in Lean. -/
noncomputable abbrev assignSideBase :=
  (A₀.absorbAssignP Req' Resp' Q').relayAdv (((G 0).relayOf Q').withSide 0) Q'
    ((A₀.absorbAssignP Req' Resp' Q').relayOut ((G 0).relayOf Q'))

/-- **Its Kraus maps at the side function `ω`** (`relaySideSt`). -/
noncomputable abbrev assignSideSteps (ω : Bits m → Y₁) :=
  (A₀.absorbAssignP Req' Resp' Q').relaySideSt ((G 0).relayOf Q') Q'
    ((A₀.absorbAssignP Req' Resp' Q').relayOut ((G 0).relayOf Q')) ω

/-- **Its side reads** (`sideSteps_relayAdv`). -/
noncomputable def sideSteps_assignSideBase :
    (assignSideBase A₀ G Q').SideSteps (assignSideSteps A₀ G Q') :=
  sideSteps_relayAdv _ _ Q' _

/-- **The adversary with the relay at `ω` absorbed** is the relayed adversary at zero with the
Kraus maps at `ω`, when the relay at `ω` is the relay at zero with side `ω` (`hG`). -/
theorem absorbAssign_eq_assignSideBase (ω : Bits m → Y₁)
    (hG : (G ω).relayOf Q' = ((G 0).relayOf Q').withSide ω) :
    A₀.absorbAssign (G ω) Q' ≍ (assignSideBase A₀ G Q').withStep (assignSideSteps A₀ G Q' ω) := by
  -- TODO(unbundle-M4): the two sides are typed at the shapes of `G ω` and of `G 0`, which agree
  -- only through `hG`, so the equation is heterogeneous; transport along `hG` at a free relay.
  have key : ∀ F', F' = ((G 0).relayOf Q').withSide ω →
      (A₀.absorbAssignP Req' Resp' Q').relayAdv F' Q'
          ((A₀.absorbAssignP Req' Resp' Q').relayOut F') ≍
        (assignSideBase A₀ G Q').withStep (assignSideSteps A₀ G Q' ω) := by
    rintro F' rfl
    exact heq_of_eq (relayAdv_withSide_eq_withStep _ _ Q' _ ω)
  exact key _ hG

/-- **A function of adversaries of every shape takes the adversary with the relay at `ω` absorbed
to its value at the relayed adversary at zero with the Kraus maps at `ω`**, when the relay at `ω`
is the relay at zero with side `ω` (`hG`): `absorbAssign_eq_assignSideBase` read through such a
function, as an equation. -/
theorem absorbAssign_apply_eq_assignSideBase {α : Sort*}
    (f : ∀ {sh : AlgShape (Bits m) Y Req' Resp'}, AdaptiveIAlg sh (O × (Bits m → Option Y)) → α)
    (ω : Bits m → Y₁) (hG : (G ω).relayOf Q' = ((G 0).relayOf Q').withSide ω) :
    f (A₀.absorbAssign (G ω) Q') =
      f ((assignSideBase A₀ G Q').withStep (assignSideSteps A₀ G Q' ω)) := by
  -- TODO(unbundle-M4): the two sides are typed at the shapes of `G ω` and of `G 0`, which agree
  -- only through `hG`; transport along `hG` at a free relay.
  have key : ∀ F', F' = ((G 0).relayOf Q').withSide ω →
      f ((A₀.absorbAssignP Req' Resp' Q').relayAdv F' Q'
          ((A₀.absorbAssignP Req' Resp' Q').relayOut F')) =
        f ((assignSideBase A₀ G Q').withStep (assignSideSteps A₀ G Q' ω)) := by
    rintro F' rfl
    exact congrArg (fun X => f X) (relayAdv_withSide_eq_withStep _ _ Q' _ ω)
  exact key _ hG

end Family

end Quantum.AdaptiveIAlg

namespace RingSignature.KeyFree

open RingSignature.Insider

variable {m : ℕ} {Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁]
  (sp : OracleSplit Y Y₁ Y₂) {N n : ℕ} {T : Signature.SchemeTypes} {RMsg : Type} [DecidableEq T.PK]
  (B : BaseSigner (Bits m) Y N T RMsg)
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem (Bits m) Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {SC X₀ R Pb : Type}
  (pks : Fin n → B.PK)
  {ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg (Bits m) Y (Option (B.Pub × B.BSig × List (Assignment (Bits m) Y)))}
  (F : KFSignFactors sp Pb ksign) {stmtPω : (Bits m → Y₁) → RingStmt B → X₀}
  (S : KFStmt stmtPω)
  (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R) (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ}
  (sc : Fin Q → SC) [Inhabited B.Pub]

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The relay at a base component is the relay at zero with that side function.** -/
theorem relayOf_kfRelaySide (ω : Bits m → Y₁) (idle : MURequest (SignOracle.none B.core) n ⊕ R)
    (Q' : ℕ) :
    AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q' =
      (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc 0 idle) Q').withSide ω :=
  rfl

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁]
  [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The numbers of the key-free relay**: one oracle read, `qOut + qSt` side reads, one pad
sub-slot. -/
theorem kfRelaySide_numbers (ω : Bits m → Y₁)
    (idle : MURequest (SignOracle.none B.core) n ⊕ R) :
    (kfRelaySide sp B pks F S toR dummyR sc ω idle).qG = 1 ∧
      (kfRelaySide sp B pks F S toR dummyR sc ω idle).qS = F.qOut + S.qSt ∧
      (kfRelaySide sp B pks F S toR dummyR sc ω idle).qP = 1 :=
  ⟨rfl, rfl, rfl⟩

variable [Fintype (Req B PS adm n)] [DecidableEq (Req B PS adm n)] [Inhabited (Req B PS adm n)]
  [Fintype (Resp B PS adm)] [DecidableEq (Resp B PS adm)] [Fintype R] [DecidableEq R]
  [Fintype (MUResponse B.core ⊕ Pf)] [DecidableEq (MUResponse B.core ⊕ Pf)]
  [Fintype (MURequest (SignOracle.none B.core) n)] [DecidableEq (MURequest (SignOracle.none B.core) n)]
  [Inhabited (MURequest (SignOracle.none B.core) n ⊕ R)]
  {O : Type} {shA₀ : AlgShape (Bits m) Y (Req B PS adm n) (Resp B PS adm)} (A₀ : AdaptiveIAlg shA₀ O)
  (idle : MURequest (SignOracle.none B.core) n ⊕ R) (Q' : ℕ)

/-- **The relayed adversary of the key-free relay at zero**, at side zero: the base of its side
reads (`sideSteps_absorbAssign_kfRelaySide`).

Running time: that of `assignSideBase` at the key-free relay. This running time is argued here,
not proved in Lean. -/
noncomputable abbrev kfRelaySideBase :=
  (A₀.absorbAssignP _ _ Q').relayAdv
    ((AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc 0 idle) Q').withSide 0) Q'
    ((A₀.absorbAssignP _ _ Q').relayOut
      (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc 0 idle) Q'))

/-- **The Kraus maps of the key-free relay's relayed adversary at the base component `ω`**
(`AdaptiveIAlg.relaySideSt`). -/
noncomputable abbrev kfRelaySideSteps (ω : Bits m → Y₁) :
    StepIdx (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').slots
        (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').post →
      KrausMap (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').R
        (DReg (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').W
          (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').width (Bits m) Y
          (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf))
        (DReg (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').W
          (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').width (Bits m) Y
          (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Pf)) :=
  (A₀.absorbAssignP _ _ Q').relaySideSt
    (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc 0 idle) Q') Q'
    ((A₀.absorbAssignP _ _ Q').relayOut
      (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc 0 idle) Q')) ω

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The absorbed adversary is the relayed adversary at the relay at zero with side zero.** -/
theorem absorbAssign_kfRelaySide_eq : A₀.absorbAssign (kfRelaySide sp B pks F S toR dummyR sc 0 idle) Q' =
    (A₀.absorbAssignP _ _ Q').relayAdv
      ((AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc 0 idle) Q').withSide 0) Q'
      ((A₀.absorbAssignP _ _ Q').relayOut
          (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc 0 idle) Q')) := rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The absorbed adversary at a base component is the one at zero with the Kraus maps at that
component** (`AdaptiveIAlg.relaySideSt`, `relayAdv_withSide_eq_withStep`). -/
theorem absorbAssign_kfRelaySide_eq_withStep (ω : Bits m → Y₁) :
    A₀.absorbAssign (kfRelaySide sp B pks F S toR dummyR sc ω idle) Q' =
      (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').withStep
        (kfRelaySideSteps sp B pks F S toR dummyR sc A₀ idle Q' ω) := by
  -- TODO(unbundle-M4): rewriting with `relayOf_kfRelaySide` changes the shape index, and checking
  -- it by `rfl` unfolds the relay; transport along it at a free relay instead.
  have key : ∀ F', F' = (AssignRelay.relayOf (kfRelaySide sp B pks F S toR dummyR sc 0 idle)
      Q').withSide ω →
      (A₀.absorbAssignP _ _ Q').relayAdv F' Q' ((A₀.absorbAssignP _ _ Q').relayOut F') ≍
        (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').withStep
          (kfRelaySideSteps sp B pks F S toR dummyR sc A₀ idle Q' ω) := by
    rintro F' rfl
    exact heq_of_eq (AdaptiveIAlg.relayAdv_withSide_eq_withStep _ _ Q' _ ω)
  exact eq_of_heq (key _ (relayOf_kfRelaySide sp B pks F S toR dummyR sc ω idle Q'))

/-- **The side reads of the adversary with the key-free relay absorbed**, at every base component:
those of `AdaptiveIAlg.sideSteps_relayAdv` at the relay at zero, whose relay at `ω` is the relay
at `ω` (`relayOf_kfRelaySide`). -/
noncomputable def sideSteps_absorbAssign_kfRelaySide :
    (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').SideSteps
      (kfRelaySideSteps sp B pks F S toR dummyR sc A₀ idle Q') :=
  AdaptiveIAlg.sideSteps_relayAdv _ _ Q' _

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The numbers of the relayed adversary of the key-free relay**: width one, no post batches,
and `relaySlotsS` slots at `A₀`'s width and its slots and post batches. -/
theorem kfRelaySideBase_numbers :
    (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').width = 1 ∧
      (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').post = 0 ∧
      (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').slots =
        Distinguisher.relaySlotsS A₀.width (A₀.slots + A₀.post) 1 1 1 :=
  ⟨rfl, rfl, rfl⟩

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The side reads of the key-free relay**: at most `qOut + qSt` before each Kraus map. -/
theorem sideSteps_absorbAssign_kfRelaySide_nb_le
    (j : StepIdx (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').slots
      (kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').post) :
    (sideSteps_absorbAssign_kfRelaySide sp B pks F S toR dummyR sc A₀ idle Q').S.nb j ≤
      F.qOut + S.qSt := by
  change (if (j : ℕ) = 0 then 0 else (if 0 < _ then F.qOut + S.qSt else 0)) ≤ _
  split_ifs <;> omega

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The side reads of the key-free relay in all**: at most `qOut + qSt` per Kraus map. -/
theorem sum_sideSteps_absorbAssign_kfRelaySide_nb_le :
    ∑ j, (sideSteps_absorbAssign_kfRelaySide sp B pks F S toR dummyR sc A₀ idle Q').S.nb j ≤
      ((kfRelaySideBase sp B pks F S toR dummyR sc A₀ idle Q').slots + 1) * (F.qOut + S.qSt) := by
  refine (Finset.sum_le_card_nsmul _ _ _ fun j _ =>
    sideSteps_absorbAssign_kfRelaySide_nb_le sp B pks F S toR dummyR sc A₀ idle Q' j).trans ?_
  simp [StepIdx, (kfRelaySideBase_numbers sp B pks F S toR dummyR sc A₀ idle Q').2.1]

end RingSignature.KeyFree

end GordieHowe
