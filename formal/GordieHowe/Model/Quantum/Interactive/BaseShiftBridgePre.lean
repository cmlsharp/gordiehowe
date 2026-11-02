-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftPreChain
public import GordieHowe.Model.Quantum.Interactive.BaseShiftBridgeSide
public import GordieHowe.Model.Quantum.Interactive.BaseShiftRestrict

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The permutations before the Kraus maps as additions on the bridge

For additions `S` on the adversary's registers, the lifted permutations at the starts of the query
intervals at `S.perm ω` (`KindAlg.prePerms`, `AdaptiveIAlg.preT`), on the bridge's registers
(`bridgeDropPerms`), are the additions `bridgePreData S`: `S` read through the absorption with the
empty table, conjugated by the table's handling of the previous slot, read through the
trace-preserving form and the composed registers, conjugated by the permutation tail before the
piece, and pulled back to the bridge step at the start of the piece's first query interval.

- `bridgeQLens`, `bridgeDropPerms_eq_liftPerm`, `bridgeDropPerms_trans`: the composed registers on
  the bridge's registers; drops in sequence.
- `absTabLens`, `liftPerm_absTabLens`, `tpQLens`, `liftPerm_tpQLens`: the adversary's registers
  on the registers absorbed with a table and on the composed registers of the trace-preserving
  form.
- `preAdds`, `preAdds_perm`: the additions at the starts of the query intervals, per piece.
- `preAt`, `bridgePreData`, `bridgePreData_nb`, `bridgePreData_perm`: on the bridge's registers.
- `CoSimSchedule.slotQ_eq_sum`, `sum_optElim_le`, `KindAlg.segStart_of_preStepAt`, `preAt_inj`,
  `slotQ_bridgePreData_le`: the query slots of `bridgePreData S`, at most the number of additions
  of `S`.
- `bridgePreData_append_perm`: after additions on the bridge that act as the drops of a list `P`,
  the drops of `P` and then the permutations at the starts of the query intervals.
- `AdaptiveIAlg.SideSteps.splitAdds`, `AdaptiveIAlg.SideSteps.splitAdds_perm`,
  `bridgePreData_restrict_perm`: at the side reads of `AdaptiveIAlg.SideSteps` read through
  `splitReg`, for the restricted adversary.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  [Nonempty (Bits m)] {Y₁ : Type} [AddGroup Y₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

/-- **The composed registers on the bridge's registers**: the core register and the query
pair. -/
def bridgeQLens : RegLens (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
    (ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) (Bits m) (BitStr I J))
    where
  get p := (p.1.1.1.1, p.2)
  set p q := ((((q.1, p.1.1.1.2), p.1.1.2), p.1.2), q.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- **The drops `β` at a step of the composition** are `β` on the composed registers. -/
theorem bridgeDropPerms_eq_liftPerm
    (β : ℕ → Equiv.Perm (ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁)
      (Bits m) (BitStr I J))) (k : Fin (bT A C₁ F kq + 1))
    (h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1) :
    bridgeDropPerms e A C₁ F d₂ E kq d₀ β k = (bridgeQLens e A C₁ F d₂ E kq d₀).liftPerm (β k) :=
  Equiv.ext fun p => bridgeDropPerms_apply_lt e A C₁ F d₂ E kq d₀ β k h p

/-- **Drops in sequence**: the drops `β` and then `β'` on the bridge's registers. -/
theorem bridgeDropPerms_trans
    (β β' : ℕ → Equiv.Perm (ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁)
      (Bits m) (BitStr I J))) (k : Fin (bT A C₁ F kq + 1)) :
    bridgeDropPerms e A C₁ F d₂ E kq d₀ (fun j => (β j).trans (β' j)) k =
      bridgeDropPerms e A C₁ F d₂ E kq d₀ β' k * bridgeDropPerms e A C₁ F d₂ E kq d₀ β k := by
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropPerms_eq_liftPerm e A C₁ F d₂ E kq d₀ _ k h,
      bridgeDropPerms_eq_liftPerm e A C₁ F d₂ E kq d₀ _ k h,
      bridgeDropPerms_eq_liftPerm e A C₁ F d₂ E kq d₀ _ k h, ← RegLens.liftPerm_mul]
    rfl
  · refine Equiv.ext fun p => ?_
    rw [Equiv.Perm.mul_apply, bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ _ k h,
      bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ _ k h,
      bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ _ k h]

/-- **The adversary's registers on the registers absorbed with a table.** -/
def absTabLens : RegLens (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width (Bits m)
    (BitStr I J) Req₁ Resp₁) (DReg A.W A.width (Bits m) (BitStr I J) Req Resp) :=
  ((fstLens _ _).transport ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂))).comp
    ((fstLens _ _).transport A.absSplit)

omit [Nonempty (Bits m)] in
/-- **A permutation on the absorbed registers** is `tabPerm`. -/
theorem liftPerm_absTabLens (tab : A.OuterTab Req₂ Resp₂)
    (π : Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)) :
    (absTabLens A F).liftPerm π = AdaptiveIAlg.tabPerm F tab π :=
  rfl

/-- **The registers of the trace-preserving form on its composed registers**: through the
ancilla, the rest of the composed registers and the query counter. -/
noncomputable def tpQLens : RegLens
    (ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) (Bits m) (BitStr I J))
    (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width (Bits m) (BitStr I J) Req₁
      Resp₁) :=
  ((fstLens _ _).transport (ancSplit _ _ _)).comp
    (((fstLens _ _).transport ((A.absorbTab F (tab₀ A)).toTPKindAlg.advSplit C₁).symm).comp
      ((fstLens _ _).transport (A.absorbTab F (tab₀ A)).cntSplit))

omit [Nonempty (Bits m)] in
/-- **A permutation on the composed registers** is its counter lift, lifted (`KindAlg.advLift`,
`AdaptiveIAlg.cntPerm`). -/
theorem liftPerm_tpQLens
    (π : Equiv.Perm (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width (Bits m)
      (BitStr I J) Req₁ Resp₁)) :
    (tpQLens A C₁ F).liftPerm π =
      KindAlg.advLift (T := (A.absorbTab F (tab₀ A)).toTPKindAlg) C₁
        ((A.absorbTab F (tab₀ A)).cntPerm π) :=
  rfl

variable (S : StepAdds (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
  (StepIdx A.slots A.post) (Bits m) Y₁)

/-- **The additions `S` at the start of the query interval of each piece**, on the composed
registers: through the absorption with the empty table, conjugated by the handling of the
previous slot (`afterAtTab`), through the trace-preserving form, conjugated by the permutation
tail before the piece (`preTail`). -/
noncomputable def preAdds : StepAdds
    (ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) (Bits m) (BitStr I J))
    (StepIdx A.slots A.post) (Bits m) Y₁ :=
  (((S.comap (absTabLens A F)).conjAt fun k => A.afterAtTab F k).comap
    (tpQLens A C₁ F)).conjAt fun k => (A.absorbTab F (tab₀ A)).toTPKindAlg.preTail C₁ k

omit [Nonempty (Bits m)] in
/-- **The additions at the start of the query interval of piece `k`** are the lifted `S.perm ω k`
conjugated by the permutation tail before the piece. -/
theorem preAdds_perm (ω : Bits m → Y₁) (k : StepIdx A.slots A.post) :
    (preAdds A C₁ F S).perm ω k =
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.preTail C₁ k)⁻¹ *
        KindAlg.advLift (T := (A.absorbTab F (tab₀ A)).toTPKindAlg) C₁
          (A.preT F (S.perm ω) k) * (A.absorbTab F (tab₀ A)).toTPKindAlg.preTail C₁ k := by
  unfold preAdds
  rw [StepAdds.conjAt_perm, StepAdds.comap_perm, StepAdds.conjAt_perm, StepAdds.comap_perm]
  rfl

/-- **The piece whose first query interval starts at bridge step `n`**, at the steps of the
composition (`KindAlg.preStepAt`); none after them. -/
noncomputable def preAt (n : ℕ) : Option (StepIdx A.slots A.post) :=
  if n < (bridgeCompose A C₁ F).depth + 1 then
    (A.absorbTab F (tab₀ A)).toTPKindAlg.preStepAt C₁ n
  else none

/-- **The additions at the starts of the query intervals on the bridge's registers**: before
bridge step `n`, those of the piece `preAt n`. -/
noncomputable def bridgePreData : StepAdds (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m)
    (BitStr I J)) (Fin (bT A C₁ F kq + 1)) (Bits m) Y₁ :=
  ((preAdds A C₁ F S).comap (bridgeQLens e A C₁ F d₂ E kq d₀)).pullOpt fun n => preAt A C₁ F n

omit [Nonempty (Bits m)] in
/-- The number of additions before bridge step `n`. -/
theorem bridgePreData_nb (n : Fin (bT A C₁ F kq + 1)) :
    (bridgePreData e A C₁ F d₂ E kq d₀ S).nb n = (preAt A C₁ F n).elim 0 S.nb :=
  rfl

/-- **The additions at the starts of the query intervals on the bridge are the lifted
permutations there** (module docstring). -/
theorem bridgePreData_perm (ω : Bits m → Y₁) (n : Fin (bT A C₁ F kq + 1)) :
    (bridgePreData e A C₁ F d₂ E kq d₀ S).perm ω n =
      bridgeDropPerms e A C₁ F d₂ E kq d₀
        (fun j => KindAlg.prePerms C₁ (A.preT F (S.perm ω)) j) n := by
  unfold bridgePreData
  rw [StepAdds.pullOpt_perm]
  by_cases h : (n : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropPerms_eq_liftPerm e A C₁ F d₂ E kq d₀ _ n h]
    simp only [preAt, h, ↓reduceIte]
    unfold KindAlg.prePerms
    rcases (A.absorbTab F (tab₀ A)).toTPKindAlg.preStepAt C₁ n with _ | k
    · exact (RegLens.liftPerm_one _).symm
    · exact (StepAdds.comap_perm _ _ ω k).trans (congrArg _ (preAdds_perm A C₁ F S ω k))
  · refine Equiv.ext fun p => ?_
    rw [bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ _ n h]
    simp only [preAt, h, ↓reduceIte, Option.elim, Equiv.Perm.one_apply]

/-- **The query slots of the blocks before `K`** are the sum of their counts. -/
theorem CoSimSchedule.slotQ_eq_sum {t : ℕ} (nb : Fin (t + 1) → ℕ) :
    ∀ K, CoSimSchedule.slotQ nb K = ∑ n ∈ Finset.range K, CoSimSchedule.nbAt nb n
  | 0 => rfl
  | K + 1 => by
    rw [Finset.sum_range_succ, ← CoSimSchedule.slotQ_eq_sum nb K]
    rfl

/-- **Counts at an optional index with each index hit at most once** sum to at most their
total. -/
theorem sum_optElim_le {K : Type*} [Fintype K] [DecidableEq K] (g : ℕ → Option K) (f : K → ℕ)
    (hg : ∀ n n' k, g n = some k → g n' = some k → n = n') (s : Finset ℕ) :
    ∑ n ∈ s, (g n).elim 0 f ≤ ∑ k, f k := by
  have h1 : ∀ n, (g n).elim 0 f = ∑ k, if g n = some k then f k else 0 := fun n => by
    rcases g n with _ | k
    · simp
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have hc : (s.filter fun n => g n = some k).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb =>
      hg a b k (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  nlinarith [Nat.zero_le (f k)]

/-- **The piece whose first query interval starts at `n`** starts there. -/
theorem KindAlg.segStart_of_preStepAt {X Y Req Resp O : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    [Nonempty X] [AddGroup Y] {ksT : KindShape X Y Req Resp} {T : KindAlg ksT O} (C : Challenger X Y Req Resp) {n : ℕ}
    {k : StepIdx T.slots T.post} (h : T.preStepAt C n = some k) : T.segStart C k = n := by
  unfold KindAlg.preStepAt at h
  split_ifs at h with hn
  · rw [← Option.some.inj h]
    exact Fin.find_spec hn

omit [Nonempty (Bits m)] in
/-- **Each piece starts at most one bridge step.** -/
theorem preAt_inj (n n' : ℕ) (k : StepIdx A.slots A.post) (h : preAt A C₁ F n = some k)
    (h' : preAt A C₁ F n' = some k) : n = n' := by
  unfold preAt at h h'
  by_cases hn : n < (bridgeCompose A C₁ F).depth + 1
  · by_cases hn' : n' < (bridgeCompose A C₁ F).depth + 1
    · simp only [hn, hn', ↓reduceIte] at h h'
      exact (KindAlg.segStart_of_preStepAt C₁ h).symm.trans (KindAlg.segStart_of_preStepAt C₁ h')
    · simp only [hn', ↓reduceIte, reduceCtorEq] at h'
  · simp only [hn, ↓reduceIte, reduceCtorEq] at h

omit [Nonempty (Bits m)] in
/-- **The query slots of the additions at the starts of the query intervals** are at most the
number of additions of `S`. -/
theorem slotQ_bridgePreData_le :
    CoSimSchedule.slotQ (bridgePreData e A C₁ F d₂ E kq d₀ S).nb (bT A C₁ F kq + 1) ≤
      ∑ k, S.nb k := by
  rw [CoSimSchedule.slotQ_eq_sum]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun n hn => ?_)
    (sum_optElim_le (fun n => preAt A C₁ F n) S.nb (preAt_inj A C₁ F) _)
  simp only [CoSimSchedule.nbAt, Finset.mem_range.1 hn, ↓reduceDIte]
  rfl

/-- **After additions `Pb₀` on the bridge that act as the drops of `P`** (`hPb₀`), the additions
`bridgePreData S` act as the drops of `P` and then the lifted permutations at the starts of the
query intervals at `S.perm ω`. -/
theorem bridgePreData_append_perm (P : A.AddsW Y₁)
    (Pb₀ : StepAdds (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
      (Fin (bT A C₁ F kq + 1)) (Bits m) Y₁)
    (hPb₀ : ∀ ω n, Pb₀.perm ω n = bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω n)
    (ω : Bits m → Y₁) (n : Fin (bT A C₁ F kq + 1)) :
    (Pb₀.append (bridgePreData e A C₁ F d₂ E kq d₀ S)).perm ω n =
      bridgeDropPerms e A C₁ F d₂ E kq d₀ (fun j => (addsDrop C₁ F ω P (tab₀ A) j).trans
        (KindAlg.prePerms C₁ (A.preT F (S.perm ω)) j)) n := by
  rw [StepAdds.perm_append, bridgePreData_perm, hPb₀, bridgeDropPerms_trans]
  rfl

section Restrict

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddGroup Y] [Fintype Y₁] [DecidableEq Y₁]
  (sp : Y ≃+ Y₁ × BitStr I J) {shA₀ : AlgShape (Bits m) Y Req Resp} {A₀ : AdaptiveIAlg shA₀ O}
  {st : (Bits m → Y₁) → StepIdx A₀.slots A₀.post →
    KrausMap A₀.R (DReg A₀.W A₀.width (Bits m) Y Req Resp) (DReg A₀.W A₀.width (Bits m) Y Req Resp)}

/-- **The side reads on the registers of the restricted adversary**, read through `splitReg`. -/
def AdaptiveIAlg.SideSteps.splitAdds (SS : A₀.SideSteps st) :
    StepAdds (DReg (A₀.restrictAt sp 0).W (A₀.restrictAt sp 0).width (Bits m) (BitStr I J) Req
      Resp) (StepIdx (A₀.restrictAt sp 0).slots (A₀.restrictAt sp 0).post) (Bits m) Y₁ :=
  SS.S.comap ((RegLens.self _).transport (splitReg sp A₀.W A₀.width (Bits m) Req Resp))

omit [Nonempty (Bits m)] in
/-- **The side reads on the restricted registers** are `S.perm ω k` read through `splitReg`. -/
theorem AdaptiveIAlg.SideSteps.splitAdds_perm (SS : A₀.SideSteps st) (ω : Bits m → Y₁)
    (k : StepIdx A₀.slots A₀.post) :
    (SS.splitAdds sp).perm ω k =
      (splitReg sp A₀.W A₀.width (Bits m) Req Resp).symm.permCongr (SS.S.perm ω k) :=
  StepAdds.comap_perm _ _ ω k

/-- **The forger's additions at the side reads, for the restricted adversary**: after additions
`Pb₀` on the bridge of `A₀.restrictAt sp 0` that act as the drops of `P` (`hPb₀`), the additions
`bridgePreData` of the side reads read through `splitReg` act as the drops of `P` and then the
lifted permutations at the starts of the query intervals at those side reads. -/
theorem bridgePreData_restrict_perm (SS : A₀.SideSteps st)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)
    (E : Expansion (Bits m) B (ExtReg (A₀.restrictAt sp 0) C₁ Req₂ Resp₂))
    (d₀ : ExtReg (A₀.restrictAt sp 0) C₁ Req₂ Resp₂) (P : (A₀.restrictAt sp 0).AddsW Y₁)
    (Pb₀ : StepAdds (QueryReg (bridgeAlg e (A₀.restrictAt sp 0) C₁ F d₂ E kq d₀).W 1 (Bits m)
      (BitStr I J)) (Fin (bT (A₀.restrictAt sp 0) C₁ F kq + 1)) (Bits m) Y₁)
    (hPb₀ : ∀ ω n, Pb₀.perm ω n = bridgeDropAdds e (A₀.restrictAt sp 0) C₁ F d₂ E kq d₀ P ω n)
    (ω : Bits m → Y₁) (n : Fin (bT (A₀.restrictAt sp 0) C₁ F kq + 1)) :
    (Pb₀.append (bridgePreData e (A₀.restrictAt sp 0) C₁ F d₂ E kq d₀ (SS.splitAdds sp))).perm
        ω n =
      bridgeDropPerms e (A₀.restrictAt sp 0) C₁ F d₂ E kq d₀
        (fun j => (addsDrop C₁ F ω P (tab₀ (A₀.restrictAt sp 0)) j).trans
          (KindAlg.prePerms C₁ ((A₀.restrictAt sp 0).preT F fun k =>
            (splitReg sp A₀.W A₀.width (Bits m) Req Resp).symm.permCongr (SS.S.perm ω k)) j))
        n := by
  rw [bridgePreData_append_perm e (A₀.restrictAt sp 0) C₁ F d₂ E kq d₀ _ P Pb₀ hPb₀ ω n]
  have h : (SS.splitAdds sp).perm ω = fun k =>
      (splitReg sp A₀.W A₀.width (Bits m) Req Resp).symm.permCongr (SS.S.perm ω k) :=
    funext fun k => AdaptiveIAlg.SideSteps.splitAdds_perm sp SS ω k
  rw [h]

end Restrict

end GordieHowe.Quantum
