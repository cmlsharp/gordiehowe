-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftBridge
public import GordieHowe.Model.QROM.ExpandCohRelabelQ

@[expose] public section

/-!
# Additions after an adversary's Kraus maps and the bridge's request points

The request points of the bridge (`answerDelta`, `writeV`) do not read or write the adversary's
workspace, so they commute with additions on it.

- `absSetW`, `AbsWorkFix`, `afterPermTab_workFix`; `absSetWD`, `AbsDWorkFix`,
  `afterAtTab_workFix`, `absOuterSwap_workFix`, `answerDelta_workFix`.
- `AdaptiveIAlg.BaseW`: local queries of an adversary on a part of its workspace;
  `AdaptiveIAlg.BaseW.tp`: on its absorbed trace-preserving form; `absorbTab_toTP_withStep`,
  `AdaptiveIAlg.BaseW.leftPerm_tp`.
- `setWorkC`, `absV_setWorkC`, `liftV_setWorkC`, `repV_setWorkC`, `writeV_setWorkC`,
  `writeV_work`: the request points against replacing the workspace.
- `dropPos`, `dropPos_zero`, `dropPos_slot`, `dropPos_chal`, `dropPos_post`: the step and the
  pair of each adversary query of the composition.
- `AdaptiveIAlg.AddsW` (`AddsOn` at the adversary), `AdaptiveIAlg.tpWsLens`,
  `AdaptiveIAlg.AddsW.tp`, `AdaptiveIAlg.AddsW.leftPerm_tp`: sorted lists of additions after the
  adversary's Kraus maps, on the absorbed trace-preserving form; `seqPerm_map`, `seqPerm_append`,
  `dregPermOf`; the instances `AdaptiveIAlg.BaseW.toAddsW` (`tp_toAddsW`) and
  `StepAdds.toAddsW` (`StepAdds.toStepAdds_perm`); `AdaptiveIAlg.AddsW.append`,
  `AdaptiveIAlg.AddsW.perm_append`.
- `AdaptiveIAlg.AddsW.tp_liftC_eq`, `AdaptiveIAlg.AddsW.tp_block_eq`, `seqPerm_congr_apply`: the
  additions on the absorbed form do not depend on the table.
- `addsDrop`, `addsDrop_heq`, `addsDrop_cases`, `setWorkV`, `addsDrop_induct`, `addsDrop_comm`:
  the additions dropped after each of the adversary's queries of the composition, the identity
  after the challenger's; `baseDrop`, `baseDrop_eq`, `baseDrop_cases`: those of the local queries;
  `writeV_bound`: the request points do not depend on the bound of the logs.
-/

open Matrix
open scoped BigOperators ENNReal Kronecker

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

/-! ### Permutations of the absorbed registers that leave the adversary's workspace alone -/

/-- The absorbed registers with the adversary's workspace replaced by `w`. -/
def absSetW (s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁)
    (w : A.W) : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁ :=
  ((⟨w, s.1.1.request, s.1.1.response, s.1.1.logs, s.1.1.store⟩, s.1.2), s.2)

/-- **A permutation of the absorbed registers that neither reads nor writes the adversary's
workspace.** -/
def AbsWorkFix (π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J)
    Req₁ Resp₁)) : Prop :=
  ∀ s w, π (absSetW A s w) = absSetW A (π s) w ∧ (π s).1.1.work = s.1.1.work

variable {A}

theorem AbsWorkFix.trans {π₁ π₂ : Equiv.Perm (DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m)
    (BitStr I J) Req₁ Resp₁)} (h₁ : AbsWorkFix A π₁) (h₂ : AbsWorkFix A π₂) :
    AbsWorkFix A (π₁.trans π₂) := fun s w => by
  simp only [Equiv.trans_apply]
  rw [(h₁ s w).1, (h₂ _ w).1, (h₂ _ w).2, (h₁ s w).2]
  exact ⟨rfl, rfl⟩

theorem absSetW_self (s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁) :
    absSetW A s s.1.1.work = s :=
  rfl

theorem absSetW_absSetW
    (s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁)
    (w w' : A.W) : absSetW A (absSetW A s w) w' = absSetW A s w' :=
  rfl

theorem AbsWorkFix.symm {π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m)
    (BitStr I J) Req₁ Resp₁)} (h : AbsWorkFix A π) : AbsWorkFix A π.symm := fun s w => by
  have hw : (π.symm s).1.1.work = s.1.1.work := by
    have := (h (π.symm s) s.1.1.work).2
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨?_, hw⟩
  rw [Equiv.symm_apply_eq]
  have := (h (π.symm s) w).1
  rw [Equiv.apply_symm_apply] at this
  rw [this]

variable (A)

theorem afterPermTab_workFix (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots) :
    AbsWorkFix A (A.afterPermTab F t j) := fun s w => by
  rcases hl : s.1.1.logs j with _ | r
  · have hl' : (absSetW A s w).1.1.logs j = none := hl
    rw [afterPermTab_of_none A F t j hl, afterPermTab_of_none A F t j hl']
    exact ⟨rfl, rfl⟩
  · have hl' : (absSetW A s w).1.1.logs j = some r := hl
    rw [afterPermTab_of_some A F t j hl, afterPermTab_of_some A F t j hl']
    exact ⟨rfl, rfl⟩

/-- The absorbed registers with the table, with the adversary's workspace replaced by `w`. -/
def absSetWD (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) (w : A.W) : AbsD A Req₁ Resp₁ Req₂ Resp₂ :=
  (((⟨w, d.1.1.1.request, d.1.1.1.response, d.1.1.1.logs, d.1.1.1.store⟩, d.1.1.2), d.1.2), d.2)

/-- **A permutation of the absorbed registers with the table that neither reads nor writes the
adversary's workspace.** -/
def AbsDWorkFix (π : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂)) : Prop :=
  ∀ d w, π (absSetWD A d w) = absSetWD A (π d) w ∧ (π d).1.1.1.work = d.1.1.1.work

variable {A}

theorem AbsDWorkFix.trans {π₁ π₂ : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂)}
    (h₁ : AbsDWorkFix A π₁) (h₂ : AbsDWorkFix A π₂) : AbsDWorkFix A (π₁.trans π₂) := fun d w => by
  simp only [Equiv.trans_apply]
  rw [(h₁ d w).1, (h₂ _ w).1, (h₂ _ w).2, (h₁ d w).2]
  exact ⟨rfl, rfl⟩

theorem AbsDWorkFix.symm {π : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂)} (h : AbsDWorkFix A π) :
    AbsDWorkFix A π.symm := fun d w => by
  have hw : (π.symm d).1.1.1.work = d.1.1.1.work := by
    have := (h (π.symm d) d.1.1.1.work).2
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨?_, hw⟩
  rw [Equiv.symm_apply_eq]
  have := (h (π.symm d) w).1
  rw [Equiv.apply_symm_apply] at this
  rw [this]

variable (A)

theorem afterAtTab_workFix (k : ℕ) : AbsDWorkFix A (A.afterAtTab F k) := by
  by_cases h : 0 < k ∧ k - 1 < A.slots
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    intro d w
    have hj : n < A.slots := by omega
    rw [afterAtTab_succ A F ⟨n, hj⟩ d, afterAtTab_succ A F ⟨n, hj⟩ (absSetWD A d w)]
    have h1 := afterPermTab_workFix A F d.1.1.2 ⟨n, hj⟩ (absStrip A d) w
    exact ⟨congrArg (absIns A d.1.1.2) h1.1, h1.2⟩
  · rw [afterAtTab_of_not A F h]
    exact fun _ _ => ⟨rfl, rfl⟩

theorem absOuterSwap_workFix (j : Fin A.slots) (x : Option Resp₂) :
    AbsDWorkFix A (absOuterSwap A F j x) := fun d w => by
  simp only [absOuterSwap, Equiv.coe_fn_mk, absSetWD]
  rcases hl : d.1.1.1.logs j with _ | r
  · exact ⟨rfl, rfl⟩
  · rcases hq : F.outer (A.reqCount d.1.1.1.logs j) r with _ | q₂
    · simp only [hq]
      constructor <;> trivial
    · simp only [hq]
      constructor <;> trivial

/-- **The request point of slot `j` leaves the adversary's workspace alone.** -/
theorem answerDelta_workFix (j : Fin A.slots) (x : Option Resp₂) :
    AbsDWorkFix A (answerDelta A F j x) :=
  (afterAtTab_workFix A F _).trans ((absOuterSwap_workFix A F j x).trans
    (afterAtTab_workFix A F _).symm)

/-! ### Local queries of an adversary, on its absorbed trace-preserving form -/

/-- **Local queries of an adversary on a part of its workspace** (as `KindAlg.BaseQ`): a part `Lw`
of `Y₁`-values, one per query pair, and the branches `on k`; neither these nor the kind read the
part. -/
structure AdaptiveIAlg.BaseW {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (Y₁ : Type) where
  /-- The part of the workspace. -/
  Lw : RegLens B.W (Fin B.width → Y₁)
  /-- The branches of the local query after Kraus map `k`. -/
  on : StepIdx B.slots B.post → B.W → Bool
  on_set : ∀ k w v, on k (Lw.set w v) = on k w
  kind_set : ∀ w v, B.kind (Lw.set w v) = B.kind w

variable {Y₁ : Type} [AddGroup Y₁] {A}

/-- **The local queries on the absorbed trace-preserving form**, on the adversary's workspace in
it. -/
def AdaptiveIAlg.BaseW.tp (D : A.BaseW Y₁) (tab : A.OuterTab Req₂ Resp₂) :
    ((A.absorbTab F tab).toTPKindAlg).BaseQ Y₁ where
  Lw :=
    { get := fun w => D.Lw.get w.1.1.work
      set := fun w v => ((⟨D.Lw.set w.1.1.work v, w.1.1.request, w.1.1.response, w.1.1.logs,
        w.1.1.store⟩, w.1.2), w.2)
      get_set := fun w v => D.Lw.get_set w.1.1.work v
      set_get := fun w => by
        change ((⟨D.Lw.set w.1.1.work (D.Lw.get w.1.1.work), _, _, _, _⟩, _), _) = w
        rw [D.Lw.set_get]
        rfl
      set_set := fun w v v' => by
        simp only
        rw [show D.Lw.set (D.Lw.set w.1.1.work v) v' = D.Lw.set w.1.1.work v' from
          D.Lw.set_set _ _ _] }
  on k w := D.on k w.1.1.work
  on_set k w v := D.on_set k _ v
  kind_set w v := by
    show (A.kind (D.Lw.set w.1.1.work v) || decide (w.2 = (A.absorbTab F tab).ended)) =
      (A.kind w.1.1.work || decide (w.2 = (A.absorbTab F tab).ended))
    rw [show A.kind (D.Lw.set w.1.1.work v) = A.kind w.1.1.work from D.kind_set _ _]

/-- **The absorbed trace-preserving form of `A.withStep st'` is that of `A` with other steps.** -/
theorem absorbTab_toTP_withStep
    (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)) (tab : A.OuterTab Req₂ Resp₂) :
    ((A.withStep st').absorbTab F tab).toTPKindAlg =
      ((A.absorbTab F tab).toTPKindAlg).withStep
        ((A.withStep st').absorbTab F tab).toTPKindAlg.step :=
  rfl

/-- **The local queries through the absorbed trace-preserving form**, in the form of
`KindAlg.BaseQ`. -/
theorem AdaptiveIAlg.BaseW.leftPerm_tp (D : A.BaseW Y₁) (ω : Bits m → Y₁)
    (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (h : ∀ k, KrausMap.LeftPerm (wsAdd D.Lw (D.on k) (D.on_set k) ω Req Resp).perm (st' k)
      (A.step k))
    (hTP' : (A.withStep st').TracePreserving) (hTP : A.TracePreserving)
    (tab : A.OuterTab Req₂ Resp₂)
    (k : StepIdx A.slots A.post) :
    KrausMap.LeftPerm (wsAdd (D.tp F tab).Lw ((D.tp F tab).on k) ((D.tp F tab).on_set k) ω Req₁
      Resp₁).perm (((A.withStep st').absorbTab F tab).toTPKindAlg.step k)
      ((A.absorbTab F tab).toTPKindAlg.step k) := by
  have h1 := AdaptiveIAlg.leftPerm_absorbTab_toTP (B := A) (F := F) st' k (h k)
    (fun d => D.kind_set d.1.1 _) (fun _ => rfl) hTP' hTP tab
  have e : AdaptiveIAlg.tpPermOf F tab (wsAdd D.Lw (D.on k) (D.on_set k) ω Req Resp).perm =
      (wsAdd (D.tp F tab).Lw ((D.tp F tab).on k) ((D.tp F tab).on_set k) ω Req₁ Resp₁).perm :=
    Equiv.ext fun _ => rfl
  rw [e] at h1
  exact h1

/-! ### Lists of additions after the adversary's Kraus maps -/

/-- **A sorted list of additions after the Kraus maps of an adversary** (`AddsOn` at its
workspace, pairs, Kraus maps and kind). -/
abbrev AdaptiveIAlg.AddsW {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (Y₁ : Type) : Type :=
  AddsOn B.W B.width (StepIdx B.slots B.post) B.kind X Y₁

variable (A) in
/-- **A part of the adversary's workspace on the absorbed trace-preserving form.** -/
def AdaptiveIAlg.tpWsLens {V : Type} (L : RegLens A.W V) :
    RegLens (shA.absorbTabS Req₂ Resp₂ (Req₁ := Req₁) (Resp₁ := Resp₁)).tpKindS.W V where
  get w := L.get w.1.1.work
  set w v := ((⟨L.set w.1.1.work v, w.1.1.request, w.1.1.response, w.1.1.logs, w.1.1.store⟩,
    w.1.2), w.2)
  get_set w v := L.get_set w.1.1.work v
  set_get w := by
    change ((⟨L.set w.1.1.work (L.get w.1.1.work), _, _, _, _⟩, _), _) = w
    rw [L.set_get]
    rfl
  set_set w v v' := by
    simp only
    rw [L.set_set]

/-- **The additions on the absorbed trace-preserving form**, on the adversary's workspace in
it. -/
def AdaptiveIAlg.AddsW.tp (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) :
    ((A.absorbTab F tab).toTPKindAlg).AddsAt Y₁ where
  nb := P.nb
  Lw k i := A.tpWsLens (P.Lw k i)
  onw k i w := P.onw k i w.1.1.work
  readsAt := P.readsAt
  xr k i w u := P.xr k i w.1.1.work u
  onw_set k i w v := P.onw_set k i _ v
  xr_set k i u w v := P.xr_set k i u _ v
  xr_reads k i w u u' h := P.xr_reads k i _ u u' h
  kind_set k i w v := by
    show (A.kind ((P.Lw k i).set w.1.1.work v) || decide (w.2 = (A.absorbTab F tab).ended)) =
      (A.kind w.1.1.work || decide (w.2 = (A.absorbTab F tab).ended))
    rw [P.kind_set k i]
  sorted := P.sorted

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] in
/-- **A map of permutations that keeps the identity and products maps them in sequence.** -/
theorem seqPerm_map {Z Z' : Type*} (Φ : Equiv.Perm Z → Equiv.Perm Z') (h1 : Φ 1 = 1)
    (hmul : ∀ a b, Φ (a * b) = Φ a * Φ b) :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm Z), Φ (seqPerm n f) = seqPerm n fun i => Φ (f i)
  | 0, _ => h1
  | n + 1, f => by
    change Φ (f (Fin.last n) * seqPerm n fun i => f i.castSucc) =
      Φ (f (Fin.last n)) * seqPerm n fun i => Φ (f i.castSucc)
    rw [hmul, seqPerm_map Φ h1 hmul n]

/-- **The additions through the absorbed trace-preserving form**: its steps for `A.withStep st'`
are those for `A` followed by the additions, when `A.withStep st'`'s are `A`'s followed by them
(`h`), for trace-preserving adversaries. -/
theorem AdaptiveIAlg.AddsW.leftPerm_tp (P : A.AddsW Y₁) (ω : Bits m → Y₁)
    (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (h : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (A.step k))
    (hTP' : (A.withStep st').TracePreserving) (hTP : A.TracePreserving)
    (tab : A.OuterTab Req₂ Resp₂) (k : StepIdx A.slots A.post) :
    KrausMap.LeftPerm ((P.tp F tab).toStepAdds.perm ω k)
      ((((A.absorbTab F tab).toTPKindAlg).withStep
        ((A.withStep st').absorbTab F tab).toTPKindAlg.step).step k)
      ((A.absorbTab F tab).toTPKindAlg.step k) := by
  have h1 := AdaptiveIAlg.leftPerm_absorbTab_toTP (B := A) (F := F) st' k (h k)
    (fun d => P.toStepAdds.comp_perm_eq ω (g := fun d => A.kind d.1.1)
      (fun k i d v => P.kind_set k i d.1.1 v) k d) (fun d => P.toStepAdds.comp_perm_eq ω
        (g := fun d => d.1.2.1) (fun _ _ _ _ => rfl) k d) hTP' hTP tab
  have e : AdaptiveIAlg.tpPermOf F tab (P.toStepAdds.perm ω k) =
      (P.tp F tab).toStepAdds.perm ω k := by
    unfold StepAdds.perm
    rw [seqPerm_map (fun π => AdaptiveIAlg.tpPermOf F tab π) (Equiv.ext fun _ => rfl)
      (fun _ _ => Equiv.ext fun _ => rfl)]
    exact congrArg _ (funext fun i => Equiv.ext fun _ => rfl)
  rw [e] at h1
  exact h1

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] in
/-- **Two lists of permutations in sequence, the first one first.** -/
theorem seqPerm_append {Z : Type*} {m' : ℕ} (f : Fin m' → Equiv.Perm Z) :
    ∀ (n : ℕ) (g : Fin n → Equiv.Perm Z),
      seqPerm (m' + n) (Fin.append f g) = seqPerm n g * seqPerm m' f
  | 0, g => by
    change seqPerm m' (Fin.append f g) = 1 * seqPerm m' f
    rw [one_mul]
    congr 1
    funext i
    exact Fin.append_left f g i
  | n + 1, g => by
    change Fin.append f g (Fin.last (m' + n)) * seqPerm (m' + n) (fun i => Fin.append f g
      i.castSucc) = (g (Fin.last n) * seqPerm n fun i => g i.castSucc) * seqPerm m' f
    have e1 : Fin.append f g (Fin.last (m' + n)) = g (Fin.last n) := by
      rw [show (Fin.last (m' + n) : Fin (m' + (n + 1))) = Fin.natAdd m' (Fin.last n) from
        Fin.ext rfl, Fin.append_right]
    have e2 : (fun i : Fin (m' + n) => Fin.append f g i.castSucc) =
        Fin.append f fun i => g i.castSucc := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left, show (Fin.castAdd n j).castSucc = Fin.castAdd (n + 1) j from
          Fin.ext rfl, Fin.append_left]
      · rw [Fin.append_right, show (Fin.natAdd m' j).castSucc = Fin.natAdd m' j.castSucc from
          Fin.ext rfl, Fin.append_right]
    rw [e1, e2, seqPerm_append f n, mul_assoc]

/-- **A permutation of the workspace on the adversary's registers.** -/
def dregPermOf {W : Type} (n : ℕ) (X Y Req Resp : Type) (π : Equiv.Perm W) :
    Equiv.Perm (DReg W n X Y Req Resp) :=
  (π.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)

/-- **The local queries of `D` as a list of additions**: after Kraus map `k`, one addition per
pair `i`, coordinate `i` of the part receiving the value at pair `i`'s input. -/
def AdaptiveIAlg.BaseW.toAddsW (D : A.BaseW Y₁) : A.AddsW Y₁ where
  nb _ := A.width
  Lw _ i := D.Lw.comp (coordLens Y₁ i)
  onw k _ := D.on k
  readsAt _ i := some i
  xr _ i _ u := u i
  onw_set k _ w _ := D.on_set k w _
  xr_set _ _ _ _ _ := rfl
  xr_reads _ i _ _ _ h := h i rfl
  kind_set _ _ w _ := D.kind_set w _
  sorted _ _ _ h := by simpa [optIdx] using h

/-- **On the absorbed form, the list of the local queries is that of their absorbed form.** -/
theorem AdaptiveIAlg.BaseW.tp_toAddsW (D : A.BaseW Y₁) (tab : A.OuterTab Req₂ Resp₂) :
    D.toAddsW.tp F tab = (D.tp F tab).toAddsAt :=
  rfl

/-- **Additions on the workspace in sequence as a list of additions** reading the workspace alone
(`readsAt = none`), for additions that keep the kind (`hk`). -/
def StepAdds.toAddsW (D : StepAdds A.W (StepIdx A.slots A.post) (Bits m) Y₁)
    (hk : D.Keeps A.kind) : A.AddsW Y₁ where
  nb := D.nb
  Lw := D.L
  onw := D.on
  readsAt _ _ := none
  xr k i w _ := D.x k i w
  onw_set := D.on_set
  xr_set k i _ := D.x_set k i
  xr_reads _ _ _ _ _ _ := rfl
  kind_set := hk
  sorted _ _ _ _ := le_rfl

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] in
theorem StepAdds.toStepAdds_perm (D : StepAdds A.W (StepIdx A.slots A.post) (Bits m) Y₁)
    (hk : D.Keeps A.kind) (ω : Bits m → Y₁) (k : StepIdx A.slots A.post) :
    (D.toAddsW hk).toStepAdds.perm ω k =
      dregPermOf A.width (Bits m) (BitStr I J) Req Resp (D.perm ω k) := by
  unfold StepAdds.perm
  rw [seqPerm_map (dregPermOf A.width (Bits m) (BitStr I J) Req Resp)
    (Equiv.ext fun _ => rfl) (fun _ _ => Equiv.ext fun _ => rfl)]
  exact congrArg _ (funext fun i => Equiv.ext fun _ => rfl)

/-- **Two lists of additions, the first one first**, when every drop point of the first is at
most every drop point of the second (`hPQ`). -/
def AdaptiveIAlg.AddsW.append (P Q : A.AddsW Y₁)
    (hPQ : ∀ k i j, optIdx (P.readsAt k i) ≤ optIdx (Q.readsAt k j)) : A.AddsW Y₁ where
  nb k := P.nb k + Q.nb k
  Lw k := Fin.append (P.Lw k) (Q.Lw k)
  onw k := Fin.append (P.onw k) (Q.onw k)
  readsAt k := Fin.append (P.readsAt k) (Q.readsAt k)
  xr k := Fin.append (P.xr k) (Q.xr k)
  onw_set k i := Fin.addCases (motive := fun i => (Fin.append (P.Lw k) (Q.Lw k) i).Indep
    (Fin.append (P.onw k) (Q.onw k) i)) (fun j => by
      simp only [Fin.append_left]
      exact P.onw_set k j) (fun j => by
      simp only [Fin.append_right]
      exact Q.onw_set k j) i
  xr_set k i u := Fin.addCases (motive := fun i => (Fin.append (P.Lw k) (Q.Lw k) i).Indep
    fun w => Fin.append (P.xr k) (Q.xr k) i w u) (fun j => by
      simp only [Fin.append_left]
      exact P.xr_set k j u) (fun j => by
      simp only [Fin.append_right]
      exact Q.xr_set k j u) i
  xr_reads k i w u u' := Fin.addCases (motive := fun i =>
    (∀ i', Fin.append (P.readsAt k) (Q.readsAt k) i = some i' → u i' = u' i') →
      Fin.append (P.xr k) (Q.xr k) i w u = Fin.append (P.xr k) (Q.xr k) i w u') (fun j h => by
      simp only [Fin.append_left] at h ⊢
      exact P.xr_reads k j w u u' h) (fun j h => by
      simp only [Fin.append_right] at h ⊢
      exact Q.xr_reads k j w u u' h) i
  kind_set k i := Fin.addCases (motive := fun i => (Fin.append (P.Lw k) (Q.Lw k) i).Indep A.kind)
    (fun j => by
      simp only [Fin.append_left]
      exact P.kind_set k j) (fun j => by
      simp only [Fin.append_right]
      exact Q.kind_set k j) i
  sorted k i j hij := by
    refine Fin.addCases (motive := fun i => i ≤ j → optIdx (Fin.append (P.readsAt k)
      (Q.readsAt k) i) ≤ optIdx (Fin.append (P.readsAt k) (Q.readsAt k) j)) (fun i₁ h => ?_)
      (fun i₂ h => ?_) i hij
    · refine Fin.addCases (motive := fun j => Fin.castAdd (Q.nb k) i₁ ≤ j →
        optIdx (Fin.append (P.readsAt k) (Q.readsAt k) (Fin.castAdd (Q.nb k) i₁)) ≤
          optIdx (Fin.append (P.readsAt k) (Q.readsAt k) j)) (fun j₁ h => ?_) (fun j₂ _ => ?_)
        j h
      · simp only [Fin.append_left]
        exact P.sorted k i₁ j₁ (Fin.le_def.2 (Fin.le_def.1 h))
      · simp only [Fin.append_left, Fin.append_right]
        exact hPQ k i₁ j₂
    · refine Fin.addCases (motive := fun j => Fin.natAdd (P.nb k) i₂ ≤ j →
        optIdx (Fin.append (P.readsAt k) (Q.readsAt k) (Fin.natAdd (P.nb k) i₂)) ≤
          optIdx (Fin.append (P.readsAt k) (Q.readsAt k) j)) (fun j₁ h => ?_) (fun j₂ h => ?_)
        j h
      · exfalso
        have h' := Fin.le_def.1 h
        simp only [Fin.coe_natAdd, Fin.coe_castAdd] at h'
        omega
      · simp only [Fin.append_right]
        exact Q.sorted k i₂ j₂ (Fin.le_def.2 (by
          have h' := Fin.le_def.1 h
          simp only [Fin.coe_natAdd] at h'
          omega))

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] in
/-- **The additions of two lists, the first one first.** -/
theorem AdaptiveIAlg.AddsW.perm_append (P Q : A.AddsW Y₁)
    (hPQ : ∀ k i j, optIdx (P.readsAt k i) ≤ optIdx (Q.readsAt k j)) (ω : Bits m → Y₁)
    (k : StepIdx A.slots A.post) :
    ((P.append Q hPQ).toStepAdds (Y := BitStr I J) (Req := Req) (Resp := Resp)).perm ω k =
      (Q.toStepAdds.perm ω k) * P.toStepAdds.perm ω k := by
  unfold StepAdds.perm
  rw [← seqPerm_append]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Equiv.ext fun d => ?_
    simp only [StepAdds.add, AddsOn.toStepAdds, RegAdd.perm_apply, AdaptiveIAlg.AddsW.append,
      Fin.append_left]
    rfl
  · refine Equiv.ext fun d => ?_
    simp only [StepAdds.add, AddsOn.toStepAdds, RegAdd.perm_apply, AdaptiveIAlg.AddsW.append,
      Fin.append_right]
    rfl

/-! ### The bridge's writes and the local queries -/

section Writes

variable (d₂ : Req₂) (D : A.BaseW Y₁) (ω : Bits m → Y₁)

/-- The composition's registers with the adversary's workspace replaced by `x`. -/
noncomputable def setWorkC (c : (bridgeCompose A C₁ F).V) (x : A.W) : (bridgeCompose A C₁ F).V :=
  (⟨(((A.tpWsLens (RegLens.self A.W)).set c.1.adv.1.1 x, c.1.adv.1.2), c.1.adv.2),
    c.1.chal⟩, c.2)

theorem absV_setWorkC (c : (bridgeCompose A C₁ F).V) (x : A.W) :
    absV A C₁ F (setWorkC C₁ F c x) = absSetWD A (absV A C₁ F c) x :=
  rfl

/-- **A lift of a permutation that leaves the workspace alone commutes with replacing it.** -/
theorem liftV_setWorkC {π : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂)} (hπ : AbsDWorkFix A π)
    (c : (bridgeCompose A C₁ F).V) (x : A.W) :
    liftV A C₁ F π (setWorkC C₁ F c x) = setWorkC C₁ F (liftV A C₁ F π c) x := by
  have e := (hπ (absV A C₁ F c) x).1
  simp only [liftV, Equiv.coe_fn_mk]
  rw [absV_setWorkC, e]
  rfl

theorem repV_setWorkC (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (c : (bridgeCompose A C₁ F).V)
    (x : A.W) : repV A C₁ F d₂ tab T k (setWorkC C₁ F c x) = repV A C₁ F d₂ tab T k c := by
  have hl : (setWorkC C₁ F c x).1.adv.1.1.1.1.logs = c.1.adv.1.1.1.1.logs := rfl
  have hr : ∀ j, reqV A C₁ F d₂ j (setWorkC C₁ F c x) = reqV A C₁ F d₂ j c := fun j => by
    simp only [reqV, hl]
  have hh : histV A C₁ F d₂ T k (setWorkC C₁ F c x) = histV A C₁ F d₂ T k c := by
    funext j
    simp only [histV, hr]
  simp only [repV, hh, hr]

/-- **The request point commutes with replacing the workspace.** -/
theorem writeV_setWorkC (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (c : (bridgeCompose A C₁ F).V)
    (x : A.W) :
    writeV A C₁ F d₂ tab T k (setWorkC C₁ F c x) =
      setWorkC C₁ F (writeV A C₁ F d₂ tab T k c) x := by
  rcases h : answerSlot A C₁ k with _ | j
  · rw [writeV_of_none A C₁ F d₂ tab T h]
    rfl
  · rw [writeV_of_some A C₁ F d₂ tab T h, writeV_of_some A C₁ F d₂ tab T h, repV_setWorkC]
    exact liftV_setWorkC C₁ F (answerDelta_workFix A F j _) c x

theorem writeV_work (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (c : (bridgeCompose A C₁ F).V) :
    (writeV A C₁ F d₂ tab T k c).1.adv.1.1.1.1.work = c.1.adv.1.1.1.1.work ∧
      (writeV A C₁ F d₂ tab T k c).1.adv.2 = c.1.adv.2 ∧
      (writeV A C₁ F d₂ tab T k c).1.chal = c.1.chal ∧ (writeV A C₁ F d₂ tab T k c).2 = c.2 := by
  rcases h : answerSlot A C₁ k with _ | j
  · rw [writeV_of_none A C₁ F d₂ tab T h]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [writeV_of_some A C₁ F d₂ tab T h]
    have hs := answerDelta_sndFix A F j (repV A C₁ F d₂ tab T k c) (absV A C₁ F c).1
      (absV A C₁ F c).2 (absV A C₁ F c).2
    refine ⟨(answerDelta_workFix A F j _ (absV A C₁ F c) (absV A C₁ F c).1.1.1.work).2, ?_, rfl,
      rfl⟩
    change (answerDelta A F j _ (absV A C₁ F c)).2 = _
    exact (congrArg Prod.snd hs).trans rfl

end Writes

/-! ### The drops of the local queries, and the extraction run through the bridge -/

section Chain

variable (d₂ : Req₂) (D : A.BaseW Y₁) (ω : Bits m → Y₁)

/-- **The position of the drop after query `n`** of the composition: in slot `s`, after the
challenger's `q` queries, the query of pair `i` is query `s · (q + width) + q + i + 1` (queries
counted from 1); in post
batch `b`, query `slots · (q + width) + b · width + i + 1`. The step after which the local query
of the pair is made, and the pair; none after the challenger's queries and elsewhere. -/
def dropPos (n : ℕ) : Option (StepIdx A.slots A.post × Fin A.width) :=
  if h : 1 ≤ n ∧ n ≤ A.slots * (C₁.q + A.width) then
    if hr : C₁.q ≤ (n - 1) % (C₁.q + A.width) then
      some (⟨(n - 1) / (C₁.q + A.width), by
        have hw := A.width_pos
        have : (n - 1) / (C₁.q + A.width) < A.slots := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          omega
        omega⟩, ⟨(n - 1) % (C₁.q + A.width) - C₁.q, by
        have hw := A.width_pos
        have := Nat.mod_lt (n - 1) (show 0 < C₁.q + A.width by omega)
        omega⟩)
    else none
  else if h' : A.slots * (C₁.q + A.width) < n ∧
      n ≤ A.slots * (C₁.q + A.width) + A.post * A.width then
    some (⟨A.slots + (n - 1 - A.slots * (C₁.q + A.width)) / A.width, by
      have hw := A.width_pos
      have : (n - 1 - A.slots * (C₁.q + A.width)) / A.width < A.post := by
        rw [Nat.div_lt_iff_lt_mul hw]
        omega
      omega⟩, ⟨(n - 1 - A.slots * (C₁.q + A.width)) % A.width, Nat.mod_lt _ A.width_pos⟩)
  else none

/-- **No position before the first query.** -/
theorem dropPos_zero : dropPos (A := A) C₁ 0 = none := by
  have h1 : ¬ (1 ≤ 0 ∧ 0 ≤ A.slots * (C₁.q + A.width)) := by omega
  have h2 : ¬ (A.slots * (C₁.q + A.width) < 0 ∧
      0 ≤ A.slots * (C₁.q + A.width) + A.post * A.width) := by omega
  unfold dropPos
  simp only [h1, h2, ↓reduceDIte]

/-- **The position after the query of pair `i` of slot `j`.** -/
theorem dropPos_slot (j : Fin A.slots) (i : Fin A.width) :
    dropPos (A := A) C₁ ((j : ℕ) * (C₁.q + A.width) + C₁.q + i + 1) = some (slotStep j, i) := by
  have hw := A.width_pos
  have hL : 0 < C₁.q + A.width := by omega
  have hr : (C₁.q + (i : ℕ)) < C₁.q + A.width := by have := i.isLt; omega
  have hn : 1 ≤ (j : ℕ) * (C₁.q + A.width) + C₁.q + i + 1 ∧
      (j : ℕ) * (C₁.q + A.width) + C₁.q + i + 1 ≤ A.slots * (C₁.q + A.width) := by
    refine ⟨by omega, ?_⟩
    have := Nat.mul_le_mul_right (C₁.q + A.width) (show (j : ℕ) + 1 ≤ A.slots from j.isLt)
    rw [Nat.add_mul, one_mul] at this
    omega
  have hm : ((j : ℕ) * (C₁.q + A.width) + C₁.q + i + 1 - 1) % (C₁.q + A.width) = C₁.q + i := by
    rw [show (j : ℕ) * (C₁.q + A.width) + C₁.q + i + 1 - 1 = C₁.q + i + j * (C₁.q + A.width) by
      omega, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have hd : ((j : ℕ) * (C₁.q + A.width) + C₁.q + i + 1 - 1) / (C₁.q + A.width) = j := by
    rw [show (j : ℕ) * (C₁.q + A.width) + C₁.q + i + 1 - 1 = C₁.q + i + j * (C₁.q + A.width) by
      omega, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hr, Nat.zero_add]
  have hr' : C₁.q ≤ ((j : ℕ) * (C₁.q + A.width) + C₁.q + i + 1 - 1) % (C₁.q + A.width) := by
    rw [hm]
    omega
  unfold dropPos
  simp only [hn, hr', and_self, ↓reduceDIte]
  congr 2
  · exact Fin.ext hd
  · exact Fin.ext (by simp only [hm]; omega)

/-- **No position after the challenger's queries.** -/
theorem dropPos_chal (j : Fin A.slots) (i : Fin C₁.q) :
    dropPos (A := A) C₁ ((j : ℕ) * (C₁.q + A.width) + i + 1) = none := by
  have hw := A.width_pos
  have hr : (i : ℕ) < C₁.q + A.width := by have := i.isLt; omega
  have hn : 1 ≤ (j : ℕ) * (C₁.q + A.width) + i + 1 ∧
      (j : ℕ) * (C₁.q + A.width) + i + 1 ≤ A.slots * (C₁.q + A.width) := by
    refine ⟨by omega, ?_⟩
    have := Nat.mul_le_mul_right (C₁.q + A.width) (show (j : ℕ) + 1 ≤ A.slots from j.isLt)
    rw [Nat.add_mul, one_mul] at this
    omega
  have hm : ((j : ℕ) * (C₁.q + A.width) + i + 1 - 1) % (C₁.q + A.width) = i := by
    rw [show (j : ℕ) * (C₁.q + A.width) + i + 1 - 1 = i + j * (C₁.q + A.width) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have hr' : ¬ C₁.q ≤ ((j : ℕ) * (C₁.q + A.width) + i + 1 - 1) % (C₁.q + A.width) := by
    rw [hm]
    exact Nat.not_le.2 i.isLt
  unfold dropPos
  simp only [hn, hr', and_self, ↓reduceDIte]

/-- **The position after the query of pair `i` of post batch `b`.** -/
theorem dropPos_post (b : Fin A.post) (i : Fin A.width) :
    dropPos (A := A) C₁ (A.slots * (C₁.q + A.width) + (b : ℕ) * A.width + i + 1) =
      some (postStep b, i) := by
  have hw := A.width_pos
  have hn1 : ¬ (1 ≤ A.slots * (C₁.q + A.width) + (b : ℕ) * A.width + i + 1 ∧
      A.slots * (C₁.q + A.width) + (b : ℕ) * A.width + i + 1 ≤ A.slots * (C₁.q + A.width)) := by
    omega
  have hn : A.slots * (C₁.q + A.width) < A.slots * (C₁.q + A.width) + (b : ℕ) * A.width + i + 1 ∧
      A.slots * (C₁.q + A.width) + (b : ℕ) * A.width + i + 1 ≤
        A.slots * (C₁.q + A.width) + A.post * A.width := by
    refine ⟨by omega, ?_⟩
    have := Nat.mul_le_mul_right A.width (show (b : ℕ) + 1 ≤ A.post from b.isLt)
    rw [Nat.add_mul, one_mul] at this
    have := i.isLt
    omega
  have he : A.slots * (C₁.q + A.width) + (b : ℕ) * A.width + i + 1 - 1 -
      A.slots * (C₁.q + A.width) = i + b * A.width := by omega
  unfold dropPos
  simp only [hn1, hn, and_self, ↓reduceDIte]
  congr 2
  · refine Fin.ext ?_
    simp only [he, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  · refine Fin.ext ?_
    simp only [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

/-- **The additions on the absorbed form do not depend on the table**: at a table and at the empty
table they act alike. -/
theorem AdaptiveIAlg.AddsW.tp_liftC_eq (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) (k i pos)
    (p : ReprogrammedQueryReg (((A.absorbTab F tab).toTPKindAlg).CW C₁) (Bits m) (BitStr I J)) :
    (P.tp F tab).liftC (C := C₁) ω k i pos p =
      (P.tp F (tab₀ A)).liftC (C := C₁) ω k i pos p := by
  rw [KindShape.AddsAt.liftC_apply, KindShape.AddsAt.liftC_apply (P := P.tp F (tab₀ A)) (i := i)]
  rfl

omit [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] in
theorem seqPerm_congr_apply {Z : Type*} :
    ∀ (n : ℕ) (f g : Fin n → Equiv.Perm Z), (∀ i z, f i z = g i z) →
      ∀ z, seqPerm n f z = seqPerm n g z
  | 0, _, _, _, _ => rfl
  | n + 1, f, g, h, z => by
    change f (Fin.last n) (seqPerm n (fun i => f i.castSucc) z) =
      g (Fin.last n) (seqPerm n (fun i => g i.castSucc) z)
    rw [seqPerm_congr_apply n _ _ (fun i => h i.castSucc), h]

/-- **The additions dropped at a pair on the absorbed form do not depend on the table.** -/
theorem AdaptiveIAlg.AddsW.tp_block_eq (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) (k)
    (c : ℕ) (pos)
    (p : ReprogrammedQueryReg (((A.absorbTab F tab).toTPKindAlg).CW C₁) (Bits m) (BitStr I J)) :
    (P.tp F tab).block (C := C₁) ω k c pos p =
      (P.tp F (tab₀ A)).block (C := C₁) ω k c pos
        p := by
  unfold KindShape.AddsAt.block
  exact seqPerm_congr_apply (P.nb k)
    (fun i => if decide (optIdx (P.readsAt k i) = c) then
      (P.tp F tab).liftC (C := C₁) ω k i pos else 1)
    (fun i => if decide (optIdx (P.readsAt k i) = c) then
      (P.tp F (tab₀ A)).liftC (C := C₁) ω k i pos
        else 1)
    (fun i z => by
      by_cases h : optIdx (P.readsAt k i) = c
      · simp only [h, decide_true, ↓reduceIte]
        exact AdaptiveIAlg.AddsW.tp_liftC_eq C₁ F ω P tab k i pos z
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Equiv.Perm.coe_one, id]) p

/-- **The additions dropped after query `n`** of the composition (`dropPos`): after the query of
pair `i` of the slot or post batch after Kraus map `s`, the additions after `s` dropped at pair
`i`, reading their inputs from the query register or the reprogramming ancilla; the identity after
the challenger's queries and elsewhere. The table `tab` only types the drops (as permutations of
the registers of the composition at `tab`); they are read on the absorbed form at the empty table,
which acts alike at every table (`AdaptiveIAlg.AddsW.tp_liftC_eq`,
`AdaptiveIAlg.AddsW.tp_block_eq`). -/
noncomputable def addsDrop (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) (n : ℕ) :
    Equiv.Perm (ReprogrammedQueryReg (((A.absorbTab F tab).toTPKindAlg).CW C₁) (Bits m)
      (BitStr I J)) :=
  match dropPos (A := A) C₁ n with
  | none => 1
  | some p => (P.tp F (tab₀ A)).block (C := C₁) ω
      p.1 p.2 (posTil p.2)

/-- **The drops of additions at a table are those at the empty table.** -/
theorem addsDrop_heq (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) :
    HEq (addsDrop C₁ F ω P tab) (addsDrop C₁ F ω P (tab₀ A)) :=
  HEq.rfl

/-- **A drop of additions is the identity or the additions dropped at a pair.** -/
theorem addsDrop_cases (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) (n : ℕ) :
    addsDrop C₁ F ω P tab n = 1 ∨ ∃ (s : StepIdx A.slots A.post) (c : Fin A.width),
      addsDrop C₁ F ω P tab n =
        (P.tp F (tab₀ A)).block (C := C₁) ω s c
          (posTil c) := by
  unfold addsDrop
  rcases dropPos (A := A) C₁ n with _ | p
  · exact Or.inl rfl
  · exact Or.inr ⟨p.1, p.2, rfl⟩

/-- The composed registers with the adversary's workspace replaced. -/
noncomputable def setWorkV {tab : A.OuterTab Req₂ Resp₂}
    (p : ReprogrammedQueryReg (((A.absorbTab F tab).toTPKindAlg).CW C₁) (Bits m) (BitStr I J))
    (x : A.W) :
    ReprogrammedQueryReg (((A.absorbTab F tab).toTPKindAlg).CW C₁) (Bits m) (BitStr I J) :=
  setWs p ((A.tpWsLens (RegLens.self A.W)).set (wsOf p) x)

/-- **A drop of additions changes only the adversary's workspace**: a property of the composed
registers kept by replacing the workspace holds after it. -/
theorem addsDrop_induct (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) (n : ℕ)
    (R : ReprogrammedQueryReg (((A.absorbTab F tab).toTPKindAlg).CW C₁) (Bits m) (BitStr I J) →
      Prop) (hR : ∀ p x, R p → R (setWorkV C₁ F p x)) (p) (hp : R p) :
    R (addsDrop C₁ F ω P tab n p) := by
  rcases addsDrop_cases C₁ F ω P tab n with h | ⟨s, c, h⟩
  · rw [h]
    exact hp
  · rw [h]
    exact (P.tp F (tab₀ A)).block_induct ω s c _ R
      (fun i q v hq => hR q _ hq) p hp

/-- **A permutation of the composed registers that commutes with replacing the adversary's
workspace, keeps it, the adversary's pairs and the ancilla, commutes with the drops of
additions.** -/
theorem addsDrop_comm (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂)
    {τ : Equiv.Perm (((A.absorbTab F tab).toTPKindAlg).CW C₁ × (Bits m × BitStr I J × Bool))}
    (hset : ∀ p x, queryWorkPerm τ (setWorkV C₁ F p x) = setWorkV C₁ F (queryWorkPerm τ p) x)
    (hwork : ∀ v, (τ v).1.adv.1.1.1.1.work = v.1.adv.1.1.1.1.work)
    (hpairs : ∀ v, (τ v).1.adv.2 = v.1.adv.2) (hanc : ∀ v, (τ v).2 = v.2) (n : ℕ) (p) :
    queryWorkPerm τ (addsDrop C₁ F ω P tab n p) =
      addsDrop C₁ F ω P tab n (queryWorkPerm τ p) := by
  rcases addsDrop_cases C₁ F ω P tab n with h | ⟨s, c, h⟩
  · rw [h]
    rfl
  · rw [h]
    exact (P.tp F (tab₀ A)).block_conj' ω _ s c _ _
      (fun i q v => by
        have := hset q ((P.Lw s i).set q.1.1.adv.1.1.1.1.work v)
        change _ = setWorkV C₁ F (tab := tab) _ ((P.Lw s i).set (τ q.1).1.adv.1.1.1.1.work v)
        erw [hwork]
        exact this)
      (fun i q => by
        change (P.Lw s i).get (τ q.1).1.adv.1.1.1.1.work = (P.Lw s i).get q.1.1.adv.1.1.1.1.work
        erw [hwork])
      (fun i q => by
        change P.onw s i (τ q.1).1.adv.1.1.1.1.work = P.onw s i q.1.1.adv.1.1.1.1.work
        erw [hwork])
      (fun i q u => by
        change P.xr s i (τ q.1).1.adv.1.1.1.1.work u = P.xr s i q.1.1.adv.1.1.1.1.work u
        erw [hwork])
      (fun i q i' _ => by
        have e1 : ((queryWorkPerm τ) q).1 = τ q.1 := rfl
        have e2 : ((queryWorkPerm τ) q).2 = q.2 := rfl
        unfold readP posTil
        have e3 : ((queryWorkPerm τ) q).1.2 = q.1.2 := hanc q.1
        have e4 : ((queryWorkPerm τ) q).1.1.adv.2 = q.1.1.adv.2 := hpairs q.1
        split_ifs
        · simp only [XPos.read]
          erw [e3, e2]
        · simp only [XPos.read]
          erw [e4]) p

/-- **The local query dropped after query `n`** of the composition (`addsDrop` of the local
queries as a list, `BaseW.toAddsW`). -/
noncomputable def baseDrop (tab : A.OuterTab Req₂ Resp₂) (n : ℕ) :
    Equiv.Perm (ReprogrammedQueryReg (((A.absorbTab F tab).toTPKindAlg).CW C₁) (Bits m)
      (BitStr I J)) :=
  addsDrop C₁ F ω D.toAddsW tab n

/-- **The local query dropped after query `n`**, written out: after the query of pair `i` of the
slot or post batch after Kraus map `s`, the local query of pair `i` after `s`, reading its input
from the query register or the reprogramming ancilla; the identity elsewhere. -/
theorem baseDrop_eq (n : ℕ) :
    baseDrop C₁ F D ω (tab₀ A) n = match dropPos (A := A) C₁ n with
      | none => 1
      | some p => (D.tp F (tab₀ A)).carry (C := C₁) ω p.1
          (fun j : Fin A.width => decide (j = p.2)) fun _ => .til := by
  unfold baseDrop addsDrop
  rcases dropPos (A := A) C₁ n with _ | p
  · rfl
  · rw [D.tp_toAddsW]
    exact (D.tp F (tab₀ A)).block_toAddsAt ω p.1 p.2

/-- **A drop is the identity or a local query reading the query register or the ancilla.** -/
theorem baseDrop_cases (n : ℕ) :
    baseDrop C₁ F D ω (tab₀ A) n = 1 ∨ ∃ s pend,
      baseDrop C₁ F D ω (tab₀ A) n = (D.tp F (tab₀ A)).carry (C := C₁) ω s pend fun _ => .til := by
  rw [baseDrop_eq]
  rcases dropPos (A := A) C₁ n with _ | p
  · exact Or.inl rfl
  · exact Or.inr ⟨p.1, _, rfl⟩

/-- **The request point `k` does not depend on the bound of the logs** past `k`. -/
theorem writeV_bound (tab : A.OuterTab Req₂ Resp₂) {T T' k : ℕ} (hk : k ≤ T + 1)
    (hk' : k ≤ T' + 1) : writeV A C₁ F d₂ tab T k = writeV A C₁ F d₂ tab T' k := by
  refine Equiv.ext fun c => ?_
  rcases h : answerSlot A C₁ k with _ | j
  · rw [writeV_of_none A C₁ F d₂ tab T h, writeV_of_none A C₁ F d₂ tab T' h]
  · rw [writeV_of_some A C₁ F d₂ tab T h, writeV_of_some A C₁ F d₂ tab T' h]
    have hr : repV A C₁ F d₂ tab T k c = repV A C₁ F d₂ tab T' k c := by
      rw [repV_eq_repLog, repV_eq_repLog]
      unfold repLog
      rw [requestsBefore_histLog A C₁ F d₂ T k _ k le_rfl hk,
        requestsBefore_histLog A C₁ F d₂ T' k _ k le_rfl hk']
    rw [hr]

end Chain

end GordieHowe.Quantum
