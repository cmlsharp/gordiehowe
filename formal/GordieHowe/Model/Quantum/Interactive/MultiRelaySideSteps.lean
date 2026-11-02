-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.MultiRelaySideAdds
public import GordieHowe.Model.Quantum.Interactive.FromDistinguisher
public import GordieHowe.Model.Quantum.Interactive.StepAddsOps
public import GordieHowe.Model.Quantum.Interactive.BaseShiftPre

@[expose] public section

/-!
# The relayed adversary's steps at a side function as its steps at zero after additions

The relayed distinguisher as an adversary (`Distinguisher.toAdaptive`): its Kraus map `k` at the
side function is the one at the zero side function read after the side additions conjugated
before the step, none at step `0` (`relayPreStepAdds`, `rightPerm_toAdaptive_relay`).

- `unitaryMat_permOp_trans`, `seqPerm_cast`: a basis permutation before a unitary; permutations
  in sequence along an equality of their number.
- `StepAdds.ofOpt`, `StepAdds.ofOpt_perm`: optional points.
- `AdaptiveIAlg.cntLens`, `AdaptiveIAlg.cntLens_liftPerm`: the counter as a part; the
  trace-preserving form is passed by `AdaptiveIAlg.rightPerm_toTPKindAlg` (`BaseShiftPre`).
- `Distinguisher.relay_step_zero_withSide'`, `Distinguisher.relayPreStepAdds`,
  `Distinguisher.relayPreStepAdds_perm_zero`,
  `Distinguisher.relayPreStepAdds_perm_of_ne`, `Distinguisher.relayPreStepAdds_perm_side`,
  `Distinguisher.rightPerm_toAdaptive_relay`.
- `Distinguisher.relayStepAt`, `Distinguisher.relaySideS`, `Distinguisher.relaySideS_perm`,
  `Distinguisher.tracePreserving_withStep_relayStepAt`, `Distinguisher.relaySideS_keeps`,
  `Distinguisher.relaySideS_kind`, `Distinguisher.relaySideS_rightPerm`: the fields of the side
  reads after the Kraus maps of the trace-preserving form.
-/

open scoped Matrix

namespace GordieHowe.Quantum

/-- **A basis permutation before a unitary**, as matrices: column `b` is column `P b`. -/
theorem unitaryMat_permOp_trans {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : QState ι ≃ₗᵢ[ℂ] QState ι) (P : Equiv.Perm ι) (a b : ι) :
    unitaryMat ((permOp P).trans U) a b = unitaryMat U a (P b) := by
  have h : permOp P (EuclideanSpace.single b (1 : ℂ)) = EuclideanSpace.single (P b) 1 := by
    ext i
    simp only [permOp_apply, PiLp.single_apply, Equiv.symm_apply_eq]
  simp only [unitaryMat, LinearIsometryEquiv.trans_apply, h]

/-- Permutations in sequence along an equality of their number. -/
theorem seqPerm_cast {Z : Type*} {n n' : ℕ} (h : n = n') (f : Fin n' → Equiv.Perm Z) :
    seqPerm n (fun i => f (Fin.cast h i)) = seqPerm n' f := by
  subst h
  rfl

namespace StepAdds

variable {Z K X V : Type*} [AddGroup V] [Inhabited X]

/-- **The additions with optional points**, at their points: on where the point is given. -/
def ofOpt (P : StepAdds Z K (Option X) V) : StepAdds Z K X V where
  nb := P.nb
  L := P.L
  on k i z := P.on k i z && (P.x k i z).isSome
  x k i z := (P.x k i z).getD default
  on_set k i z v := by simp only [P.on_set k i z v, P.x_set k i z v]
  x_set k i z v := by simp only [P.x_set k i z v]

/-- **The additions with optional points at `ω`** are the additions at `ω` extended by `0`. -/
theorem ofOpt_perm (P : StepAdds Z K (Option X) V) (ω : X → V) (k : K) :
    P.ofOpt.perm ω k = P.perm (fun o => o.elim 0 ω) k := by
  change seqPerm _ (fun i => (P.ofOpt.add ω k i).perm) = seqPerm _ (fun i => (P.add _ k i).perm)
  congr 1
  funext i
  refine Equiv.ext fun z => ?_
  rw [RegAdd.perm_apply, RegAdd.perm_apply]
  change (P.L k i).set z ((P.L k i).get z + (if (P.on k i z && (P.x k i z).isSome) = true then
      ω ((P.x k i z).getD default) else 0)) = (P.L k i).set z ((P.L k i).get z +
      (if P.on k i z = true then (P.x k i z).elim 0 ω else 0))
  rcases P.on k i z with _ | _ <;> rcases P.x k i z with _ | x <;> simp

end StepAdds

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **The adversary's registers in its registers with the counter**, as a part. -/
def cntLens {shC : AlgShape X Y Req Resp} (C : AdaptiveIAlg shC O) :
    RegLens C.CReg (DReg C.W C.width X Y Req Resp) where
  get z := (C.cntSplit z).1
  set z d := C.cntSplit.symm (d, (C.cntSplit z).2)
  get_set z d := by simp
  set_get z := by simp
  set_set z d d' := by simp

theorem cntLens_liftPerm {shC : AlgShape X Y Req Resp} (C : AdaptiveIAlg shC O)
    (π : Equiv.Perm (DReg C.W C.width X Y Req Resp)) : C.cntLens.liftPerm π = C.cntPerm π :=
  Equiv.ext fun _ => rfl

end AdaptiveIAlg

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
set_option quotPrecheck false in
local notation "RR0" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m (F.withSide 0))
  (Fin (F.withSide 0).qS → Ys)

omit [DecidableEq Ys] in
/-- **The first step of the relayed distinguisher does not read the side function.** -/
theorem relay_step_zero_withSide' (s : Xs → Ys) (k : Fin (relaySlots n m F + 1))
    (hk : (k : ℕ) = 0) : (D.relay (F.withSide s) b Q).step k = (D.relay F b Q).step k := by
  obtain ⟨_, _, _, h4, h5⟩ := perms_withSide D F b Q s
  simp only [relay, hk, ↓reduceIte]
  rw [h4, h5, D.ctrlStep_withSide F b Q s]

/-- The side additions conjugated before the step, as a list of additions. -/
noncomputable abbrev relayPreC : StepAdds RR Unit (Option Xs) Ys :=
  (sideAdds F b Q).conj (prePerm F b Q).symm

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
theorem relayPreNb_lt {k : Fin (relaySlots n m F + 1)}
    (i : Fin (if (k : ℕ) = 0 then 0 else (relayPreC (W := W) (n := n) (m := m) F b Q).nb ())) :
    (k : ℕ) ≠ 0 ∧ (i : ℕ) < (relayPreC (W := W) (n := n) (m := m) F b Q).nb () := by
  have hi := i.isLt
  split_ifs at hi with hk
  · exact absurd hi (Nat.not_lt_zero _)
  · exact ⟨hk, hi⟩

/-- **The side additions before each step of the relayed distinguisher** (`relayPreC`, none at
step `0`). -/
noncomputable def relayPreStepAdds : StepAdds RR (Fin (relaySlots n m F + 1)) (Option Xs) Ys where
  nb k := if (k : ℕ) = 0 then 0 else (relayPreC (W := W) (n := n) (m := m) F b Q).nb ()
  L _ i := (relayPreC (W := W) (n := n) (m := m) F b Q).L ()
    ⟨i, (relayPreNb_lt (W := W) (n := n) (m := m) F b Q i).2⟩
  on _ i := (relayPreC (W := W) (n := n) (m := m) F b Q).on ()
    ⟨i, (relayPreNb_lt (W := W) (n := n) (m := m) F b Q i).2⟩
  x _ i := (relayPreC (W := W) (n := n) (m := m) F b Q).x ()
    ⟨i, (relayPreNb_lt (W := W) (n := n) (m := m) F b Q i).2⟩
  on_set _ _ := (relayPreC (W := W) (n := n) (m := m) F b Q).on_set () _
  x_set _ _ := (relayPreC (W := W) (n := n) (m := m) F b Q).x_set () _

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
theorem relayPreStepAdds_perm_zero (ω : Option Xs → Ys) :
    (relayPreStepAdds (W := W) (n := n) (m := m) F b Q).perm ω 0 = 1 :=
  seqPerm_one _ _ fun i => absurd i.isLt (by simp [relayPreStepAdds])

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
theorem relayPreStepAdds_perm_of_ne (ω : Option Xs → Ys) {k : Fin (relaySlots n m F + 1)}
    (hk : (k : ℕ) ≠ 0) : (relayPreStepAdds (W := W) (n := n) (m := m) F b Q).perm ω k =
      (relayPreC (W := W) (n := n) (m := m) F b Q).perm ω () := by
  have h : (relayPreStepAdds (W := W) (n := n) (m := m) F b Q).nb k =
      (relayPreC (W := W) (n := n) (m := m) F b Q).nb () := by
    simp [relayPreStepAdds, hk]
  exact seqPerm_cast h (fun i => ((relayPreC (W := W) (n := n) (m := m) F b Q).add ω () i).perm)

variable {O : Type} (hn : 0 < 1) (q : ℕ)

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- **The side additions before the step at a side function** are the list `relayPreStepAdds` at
it: the side additions of the relay with that side function conjugated before the step. -/
theorem relayPreStepAdds_perm_side (sf : Xs → Ys) {k : Fin (relaySlots n m F + 1)}
    (hk : (k : ℕ) ≠ 0) :
    (relayPreStepAdds (W := W) (n := n) (m := m) F b Q).perm (fun o => o.elim 0 sf) k =
      (preAdds (F.withSide sf) b Q : Equiv.Perm RR) := by
  rw [relayPreStepAdds_perm_of_ne (W := W) (n := n) (m := m) F b Q _ hk, ← StepAdds.perm_conj,
    sideAdds_perm_side]
  unfold preAdds
  exact congrArg (fun P => (Equiv.symm P).permCongr (sideAddsPerm (F.withSide sf) b Q))
    (prePerm_withSide F b Q sf).symm

/-- **The relayed adversary's Kraus map `k` at a side function is the one at the zero side
function read after the side additions** (`relayPreStepAdds`). -/
theorem rightPerm_toAdaptive_relay (sf : Xs → Ys)
    (outs : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m (F.withSide sf))
      (Fin (F.withSide sf).qS → Ys) → O)
    (out0 : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m (F.withSide 0))
      (Fin (F.withSide 0).qS → Ys) → O)
    (k : StepIdx (relaySlots n m F) 0) (r : Unit) (a b' : RR) :
    (((D.relay (F.withSide sf) b Q).toAdaptive hn q outs).step k).op r a b' =
      (((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).step k).op r a
        ((relayPreStepAdds (W := W) (n := n) (m := m) F b Q).perm (fun o => o.elim 0 sf) k b') := by
  simp only [Distinguisher.toAdaptive_op]
  change unitaryMat ((D.relay (F.withSide sf) b Q).stepAt k) a b' =
    unitaryMat ((D.relay (F.withSide 0) b Q).stepAt k) a _
  have hlt : (k : ℕ) < relaySlots n m F + 1 := k.isLt
  have h1 : (D.relay (F.withSide sf) b Q).stepAt k =
      (D.relay (F.withSide sf) b Q).step ⟨k, hlt⟩ := by
    unfold Distinguisher.stepAt
    simp only [show (k : ℕ) < relaySlots n m (F.withSide sf) + 1 from hlt, ↓reduceDIte]
  have h2 : (D.relay (F.withSide 0) b Q).stepAt k =
      (D.relay (F.withSide 0) b Q).step ⟨k, hlt⟩ := by
    unfold Distinguisher.stepAt
    simp only [show (k : ℕ) < relaySlots n m (F.withSide 0) + 1 from hlt, ↓reduceDIte]
  rw [h1, h2]
  by_cases hk : (k : ℕ) = 0
  · rw [show (relayPreStepAdds (W := W) (n := n) (m := m) F b Q).perm
        (fun o => o.elim 0 sf) k = 1 from by
      rw [show k = 0 from Fin.ext hk]
      exact relayPreStepAdds_perm_zero (W := W) (n := n) (m := m) F b Q _,
      Equiv.Perm.one_apply]
    have e : (D.relay (F.withSide sf) b Q).step ⟨k, hlt⟩ =
        (D.relay (F.withSide 0) b Q).step ⟨k, hlt⟩ :=
      (relay_step_zero_withSide' D F b Q sf ⟨k, hlt⟩ hk).trans
        (relay_step_zero_withSide' D F b Q 0 ⟨k, hlt⟩ hk).symm
    rw [e]
  · rw [relayPreStepAdds_perm_side F b Q sf hk,
      D.relay_step_eq_pre_withSide_zero (F.withSide sf) b Q ⟨k, hlt⟩ hk]
    exact unitaryMat_permOp_trans
      ((D.relay (F.withSide 0) b Q).step ⟨k, hlt⟩ : QState RR ≃ₗᵢ[ℂ] QState RR)
      (preAdds (F.withSide sf) b Q) a b'

/-- **The relayed adversary's Kraus maps at the side function `sf`**, on the registers of the
relay. -/
noncomputable def relayStepAt (sf : Xs → Ys) (k : StepIdx (relaySlots n m (F.withSide 0)) 0) :
    KrausMap Unit RR0 RR0 :=
  Distinguisher.toAdaptiveStep (D.relay (F.withSide sf) b Q).step k

/-- The relayed adversary's Kraus maps at the side function `sf` are its unitaries. -/
theorem relayStepAt_eq (sf : Xs → Ys) (k : StepIdx (relaySlots n m (F.withSide 0)) 0) :
    relayStepAt D F b Q sf k = (KrausChannel.ofUnitary
      (unitaryMat ((D.relay (F.withSide sf) b Q).stepAt k))
      (unitaryMat_conjTranspose_mul _)).toKrausMap :=
  (D.relay (F.withSide sf) b Q).toAdaptiveStep_eq k

/-- **The relayed adversary at a side function is the one at zero with the Kraus maps at that side
function** (`relayStepAt`): the kinds agree, since the relay's sub-slot actions do not read the
side function (`MultiRelay.actAt_withSide`). -/
theorem toAdaptive_relay_withSide (sf : Xs → Ys)
    (out0 : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m (F.withSide 0))
      (Fin (F.withSide 0).qS → Ys) → O) :
    (D.relay (F.withSide sf) b Q).toAdaptive hn q out0 =
      ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).withStep (relayStepAt D F b Q sf) := by
  have hk : (D.relay (F.withSide sf) b Q).kind = (D.relay (F.withSide 0) b Q).kind := by
    funext w
    simp only [relay, MultiRelay.actAt_withSide]
  unfold Distinguisher.toAdaptive AdaptiveIAlg.withStep
  congr 1
  all_goals rfl

/-- **The side reads of the relayed adversary**, after the Kraus maps of its trace-preserving form:
the side additions conjugated before each step (`relayPreStepAdds`), at their points, on the
registers with the counter. -/
noncomputable abbrev relaySideS
    (out0 : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m (F.withSide 0))
      (Fin (F.withSide 0).qS → Ys) → O) [Inhabited Xs] :
    StepAdds ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).CReg
      (Fin (relaySlots n m (F.withSide 0) + 1)) Xs Ys :=
  (relayPreStepAdds (W := W) (n := n) (m := m) (F.withSide 0) b Q).ofOpt.comap
    ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).cntLens

section SideSteps

variable [Inhabited Xs]
  (out0 : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m (F.withSide 0))
    (Fin (F.withSide 0).qS → Ys) → O)

theorem relaySideS_perm (sf : Xs → Ys) (k : Fin (relaySlots n m (F.withSide 0) + 1)) :
    (relaySideS D F b Q hn q out0).perm sf k =
      ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).cntPerm
        ((relayPreStepAdds (W := W) (n := n) (m := m) (F.withSide 0) b Q).perm
          (fun o => o.elim 0 sf) k) := by
  exact (StepAdds.comap_perm _ _ sf k).trans ((AdaptiveIAlg.cntLens_liftPerm _ _).trans
    (congrArg _ (StepAdds.ofOpt_perm _ sf k)))

omit [Inhabited Xs] in
/-- **The steps at a side function are trace preserving.** -/
theorem tracePreserving_withStep_relayStepAt (sf : Xs → Ys) :
    (((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).withStep
      (relayStepAt D F b Q sf)).TracePreserving := fun k => by
  show ∑ r, ((relayStepAt D F b Q sf k).op r)ᴴ * (relayStepAt D F b Q sf k).op r = 1
  rw [relayStepAt_eq]
  change ∑ r : Unit, (unitaryMat ((D.relay (F.withSide sf) b Q).stepAt k))ᴴ *
    unitaryMat ((D.relay (F.withSide sf) b Q).stepAt k) = 1
  rw [Fintype.sum_unique]
  exact unitaryMat_conjTranspose_mul _

/-- **The side reads keep the requests and the responses, and the query pairs.** -/
theorem relaySideS_keeps (sf : Xs → Ys) (k : Fin (relaySlots n m (F.withSide 0) + 1))
    (d : ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).CReg) :
    ((relaySideS D F b Q hn q out0).perm sf k d).1.2 = d.1.2 ∧
      ((relaySideS D F b Q hn q out0).perm sf k d).2 = d.2 := by
  erw [relaySideS_perm, AdaptiveIAlg.cntPerm_apply]
  by_cases hk : (k : ℕ) = 0
  · erw [show k = 0 from Fin.ext hk, relayPreStepAdds_perm_zero]
    exact ⟨rfl, rfl⟩
  · erw [relayPreStepAdds_perm_side (F.withSide 0) b Q sf hk]
    obtain ⟨-, -, -, -, h5, h6⟩ := preAdds_keeps (F.withSide sf) b Q
      ((((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).cntSplit d).1 : RR0)
    exact ⟨h5, h6⟩

/-- **The side reads keep the kind** of the trace-preserving form. -/
theorem relaySideS_kind (sf : Xs → Ys) (k : Fin (relaySlots n m (F.withSide 0) + 1))
    (d : ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).CReg) :
    ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).toTPKindAlg.kind
        ((relaySideS D F b Q hn q out0).perm sf k d).1.1 =
      ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).toTPKindAlg.kind d.1.1 := by
  erw [relaySideS_perm, AdaptiveIAlg.cntPerm_apply]
  by_cases hk : (k : ℕ) = 0
  · erw [show k = 0 from Fin.ext hk, relayPreStepAdds_perm_zero]
    rfl
  · erw [relayPreStepAdds_perm_side (F.withSide 0) b Q sf hk]
    set z : RR0 := (((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).cntSplit d).1
    have h := actAt_preAdds (F.withSide sf) b Q z
    simp only [MultiRelay.actAt_withSide] at h
    have key : ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).kind
        ((preAdds (F.withSide sf) b Q) z).1.1 =
        ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).kind z.1.1 := by
      change ((F.withSide 0).actAt n b Q ((preAdds (F.withSide sf) b Q) z).1.1.record
        ((preAdds (F.withSide sf) b Q) z).1.1.store ((preAdds (F.withSide sf) b Q) z).1.1.side
        ((preAdds (F.withSide sf) b Q) z).1.1.time).isAsk =
        ((F.withSide 0).actAt n b Q z.1.1.record z.1.1.store z.1.1.side z.1.1.time).isAsk
      simp only [MultiRelay.actAt_withSide, h]
    exact congrArg (fun t => t || decide ((((D.relay (F.withSide 0) b Q).toAdaptive hn q
      out0).cntSplit d).2 = ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).ended)) key

/-- **The relayed adversary's trace-preserving steps at a side function are those at zero read
after the side reads** (`relaySideS`). -/
theorem relaySideS_rightPerm (sf : Xs → Ys) (k : StepIdx (relaySlots n m (F.withSide 0)) 0) (z)
    (a b' : ((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).CReg) :
    ((((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).withStep
      (relayStepAt D F b Q sf)).toTPKindAlg.step k).op z a b' =
      (((D.relay (F.withSide 0) b Q).toAdaptive hn q out0).toTPKindAlg.step k).op z a
        ((relaySideS D F b Q hn q out0).perm sf k b') := by
  erw [relaySideS_perm]
  exact AdaptiveIAlg.rightPerm_toTPKindAlg (C := (D.relay (F.withSide 0) b Q).toAdaptive hn q out0)
    (st' := relayStepAt D F b Q sf)
    (π := (relayPreStepAdds (W := W) (n := n) (m := m) (F.withSide 0) b Q).perm
      (fun o => o.elim 0 sf) k) k
    (fun r x y => rightPerm_toAdaptive_relay D (F.withSide 0) b Q hn q sf out0 out0 k r x y)
    (tracePreserving_withStep_relayStepAt D F b Q hn q out0 sf)
    (Distinguisher.toAdaptive_tracePreserving _ hn q out0) z a b'

end SideSteps

end Distinguisher

end GordieHowe.Quantum
