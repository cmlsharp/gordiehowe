-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftDrops
public import GordieHowe.Model.Quantum.Interactive.StepAddsOps

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# Side reads together with the local queries, as additions on the bridge

For side reads `S` on the adversary's workspace (`StepAdds`, keeping the kind) followed by the
local queries of `D` (`AdaptiveIAlg.BaseW`), as one sorted list of additions (`sideAdds`, the side
reads first), the drops of the list on the bridge's registers (`bridgeDropAdds`) are the
additions `bridgeSideData S` followed by those of the local queries (`bridgeDropData`): the side
reads after Kraus map `s` are dropped with the local query of pair `0` after `s`.

- `wsCW`, `bridgeWsLens`: the adversary's workspace on the composed and the bridge's registers.
- `sideAdds`: the side reads, then the local queries, as one list.
- `sideAdds_off`: no addition of the list after a Kraus map where neither list has one.
- `sideAt`, `bridgeSideData`, `bridgeSideData_nb`: the side reads on the bridge's registers, at
  the drops of pair `0`.
- `liftC_sideAdds_left`, `liftC_sideAdds_right`, `block_sideAdds`, `addsDrop_sideAdds`: the drops
  of the list are those of the local queries after the side reads.
- `bridgeSideData_perm`: the additions on the bridge are the drops of the list.
- `CoSimSchedule.slotQ_add`, `slotQ_bridgeSideData_append`: the query slots of the additions,
  `bT + 1` for the local queries and those of the side reads.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

/-- **The query slots of two counts per block** are the sums of their query slots. -/
theorem CoSimSchedule.slotQ_add {t : ℕ} (a c : Fin (t + 1) → ℕ) :
    ∀ n, CoSimSchedule.slotQ (fun k => a k + c k) n =
      CoSimSchedule.slotQ a n + CoSimSchedule.slotQ c n
  | 0 => rfl
  | n + 1 => by
    simp only [CoSimSchedule.slotQ, CoSimSchedule.slotQ_add a c n, CoSimSchedule.nbAt]
    split <;> omega

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  [Nonempty (Bits m)] {Y₁ : Type} [AddGroup Y₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
  (D : A.BaseW Y₁) (S : StepAdds A.W (StepIdx A.slots A.post) (Bits m) Y₁) (hS : S.Keeps A.kind)

/-- The adversary's workspace on the composed work register with the ancilla. -/
def wsCW : RegLens (((A.absorbTab F (tab₀ A)).toTPKindAlg).CW C₁ × (Bits m × BitStr I J × Bool))
    A.W :=
  { get := fun w => (A.tpWsLens (RegLens.self A.W)).get w.1.adv.1.1
    set := fun w v => (⟨(((A.tpWsLens (RegLens.self A.W)).set w.1.adv.1.1 v,
      w.1.adv.1.2), w.1.adv.2), w.1.chal⟩, w.2)
    get_set := fun _ _ => by simp
    set_get := fun _ => by simp
    set_set := fun _ _ _ => by simp }

/-- The adversary's workspace on the bridge's registers. -/
def bridgeWsLens : RegLens (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
    A.W :=
  (fstLens _ _).comp ((fstLens _ _).comp ((fstLens _ _).comp ((fstLens _ _).comp
    (wsCW A C₁ F))))

/-- **The side reads, then the local queries, as one sorted list of additions.** -/
def sideAdds : A.AddsW Y₁ :=
  (S.toAddsW hS).append D.toAddsW fun _ _ _ => Nat.zero_le _

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Nonempty (Bits m)] in
/-- **No addition of the list after Kraus map `k`** when there is no side read (`hSk`) and no local
query (`hDk`) after it. -/
theorem sideAdds_off {k : StepIdx A.slots A.post} (hSk : S.Off k) (hDk : ∀ w, D.on k w = false) :
    (sideAdds A D S hS).Off k := by
  intro i w
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact (congrFun (Fin.append_left (S.on k) (fun (_ : Fin A.width) => D.on k) j) w).trans
      (hSk j w)
  · exact (congrFun (Fin.append_right (S.on k) (fun (_ : Fin A.width) => D.on k) j) w).trans
      (hDk w)

/-- **The step of the side reads dropped before bridge step `k`**: at the drop of pair `0` after
Kraus map `s` (`dropPos`), the side reads after `s`; none elsewhere. -/
noncomputable def sideAt (k : ℕ) : Option (StepIdx A.slots A.post) :=
  if k < (bridgeCompose A C₁ F).depth + 1 then
    match dropPos (A := A) C₁ k with
    | some p => if (p.2 : ℕ) = 0 then some p.1 else none
    | none => none
  else none

/-- **The side reads on the bridge's registers**: before bridge step `k`, the side reads after
`sideAt k` on the adversary's workspace. -/
noncomputable def bridgeSideData : StepAdds (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m)
    (BitStr I J)) (Fin (bT A C₁ F kq + 1)) (Bits m) Y₁ :=
  (S.comap (bridgeWsLens e A C₁ F d₂ E kq d₀)).pullOpt fun k => sideAt A C₁ F k

omit [Nonempty (Bits m)] in
/-- The number of side reads before bridge step `k`. -/
theorem bridgeSideData_nb (k : Fin (bT A C₁ F kq + 1)) :
    (bridgeSideData e A C₁ F d₂ E kq d₀ S).nb k = (sideAt A C₁ F k).elim 0 S.nb :=
  rfl

/-- The adversary's workspace on the composed registers. -/
def wsQ : RegLens (ReprogrammedQueryReg (((A.absorbTab F (tab₀ A)).toTPKindAlg).CW C₁) (Bits m)
    (BitStr I J)) A.W :=
  (fstLens _ _).comp (wsCW A C₁ F)

variable (ω : Bits m → Y₁)

omit [Nonempty (Bits m)] in
/-- **The side reads of the list on the absorbed form** are the side reads on the workspace. -/
theorem liftC_sideAdds_left (s : StepIdx A.slots A.post) (j : Fin (S.nb s))
    (pos : Fin A.width → XPos) :
    ((sideAdds A D S hS).tp F (tab₀ A)).liftC (C := C₁) ω s (Fin.castAdd A.width j) pos =
      (wsQ A C₁ F).liftPerm ((S.add ω s j).perm) := by
  refine Equiv.ext fun q => ?_
  erw [KindShape.AddsAt.liftC_apply]
  simp only [KindShape.AddsAt.fC, sideAdds, AdaptiveIAlg.AddsW.append, AdaptiveIAlg.AddsW.tp,
    StepAdds.toAddsW]
  have h1 : Fin.append (S.L s) (D.toAddsW.Lw s) (Fin.castAdd A.width j) = S.L s j :=
    Fin.append_left _ _ _
  have h2 : Fin.append (S.on s) (D.toAddsW.onw s) (Fin.castAdd A.width j) = S.on s j :=
    Fin.append_left _ _ _
  have h3 : Fin.append (fun i w (_ : Fin A.width → Bits m) => S.x s i w) (D.toAddsW.xr s)
      (Fin.castAdd A.width j) = fun w _ => S.x s j w :=
    Fin.append_left _ _ _
  simp only [h1, h2, h3]
  rfl

omit [Nonempty (Bits m)] in
/-- **The local queries of the list on the absorbed form** are those of `D`. -/
theorem liftC_sideAdds_right (s : StepIdx A.slots A.post) (j : Fin A.width)
    (pos : Fin A.width → XPos) :
    ((sideAdds A D S hS).tp F (tab₀ A)).liftC (C := C₁) ω s (Fin.natAdd (S.nb s) j) pos =
      (D.toAddsW.tp F (tab₀ A)).liftC (C := C₁) ω s j pos := by
  refine Equiv.ext fun q => ?_
  erw [KindShape.AddsAt.liftC_apply, KindShape.AddsAt.liftC_apply]
  simp only [KindShape.AddsAt.fC, sideAdds, AdaptiveIAlg.AddsW.append, AdaptiveIAlg.AddsW.tp]
  have h1 : Fin.append (fun i => (S.toAddsW hS).Lw s i) (D.toAddsW.Lw s)
      (Fin.natAdd (S.nb s) j) = D.toAddsW.Lw s j :=
    Fin.append_right _ _ _
  have h2 : Fin.append (fun i => (S.toAddsW hS).onw s i) (D.toAddsW.onw s)
      (Fin.natAdd (S.nb s) j) = D.toAddsW.onw s j :=
    Fin.append_right _ _ _
  have h3 : Fin.append (fun i => (S.toAddsW hS).xr s i) (D.toAddsW.xr s)
      (Fin.natAdd (S.nb s) j) = D.toAddsW.xr s j :=
    Fin.append_right _ _ _
  simp only [h1, h2, h3]
  rfl

/-- **The drops of the list at pair `c` after Kraus map `s`** are the side reads after `s` (at
pair `0`), then the local queries of `D`. -/
theorem block_sideAdds (s : StepIdx A.slots A.post) (c : ℕ) (pos : Fin A.width → XPos) :
    ((sideAdds A D S hS).tp F (tab₀ A)).block (C := C₁) ω s c pos =
      (D.toAddsW.tp F (tab₀ A)).block (C := C₁) ω s c pos *
        (if c = 0 then (wsQ A C₁ F).liftPerm (S.perm ω s) else 1) := by
  unfold KindShape.AddsAt.block
  have hf : (fun i : Fin (S.nb s + A.width) =>
      if decide (optIdx (((sideAdds A D S hS).tp F (tab₀ A)).readsAt s i) = c) then
        ((sideAdds A D S hS).tp F (tab₀ A)).liftC (C := C₁) ω s i pos else 1) =
      Fin.append (fun j : Fin (S.nb s) => if c = 0 then (wsQ A C₁ F).liftPerm ((S.add ω s j).perm)
        else 1)
        (fun j : Fin A.width => if decide (optIdx ((D.toAddsW.tp F (tab₀ A)).readsAt s j) = c) then
          (D.toAddsW.tp F (tab₀ A)).liftC (C := C₁) ω s j pos else 1) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      erw [liftC_sideAdds_left]
      have hr : ((sideAdds A D S hS).tp F (tab₀ A)).readsAt s (Fin.castAdd A.width j) = none :=
        Fin.append_left _ _ _
      erw [hr]
      by_cases hc : c = 0 <;> simp [optIdx, hc, eq_comm]
    · rw [Fin.append_right]
      erw [liftC_sideAdds_right]
      have hr : ((sideAdds A D S hS).tp F (tab₀ A)).readsAt s (Fin.natAdd (S.nb s) j) =
          (D.toAddsW.tp F (tab₀ A)).readsAt s j :=
        Fin.append_right _ _ _
      erw [hr]
  refine (congrArg (seqPerm (S.nb s + A.width)) hf).trans ?_
  rw [seqPerm_append]
  congr 1
  by_cases hc : c = 0
  · simp only [hc, ↓reduceIte]
    unfold StepAdds.perm
    rw [seqPerm_map (wsQ A C₁ F).liftPerm (wsQ A C₁ F).liftPerm_one (wsQ A C₁ F).liftPerm_mul]
  · simp only [hc, ↓reduceIte]
    exact seqPerm_one _ _ fun _ => rfl

/-- **The drops of the list after query `n`** are the side reads dropped there (at pair `0`), then
the local queries of `D`. -/
theorem addsDrop_sideAdds (n : ℕ) :
    addsDrop C₁ F ω (sideAdds A D S hS) (tab₀ A) n =
      addsDrop C₁ F ω D.toAddsW (tab₀ A) n *
        (match dropPos (A := A) C₁ n with
          | none => 1
          | some p => if (p.2 : ℕ) = 0 then (wsQ A C₁ F).liftPerm (S.perm ω p.1) else 1) := by
  unfold addsDrop
  rcases dropPos (A := A) C₁ n with _ | ⟨s, c⟩
  · rfl
  · exact block_sideAdds A C₁ F D S hS ω s c (posTil c)

/-- **The side reads on the bridge followed by the local queries are the drops of the list**
(module docstring). -/
theorem bridgeSideData_perm [Inhabited Req₂] (k : Fin (bT A C₁ F kq + 1)) :
    ((bridgeSideData e A C₁ F d₂ E kq d₀ S).append (bridgeDropData e A C₁ F d₂ E kq d₀ D)).perm
        ω k = bridgeDropAdds e A C₁ F d₂ E kq d₀ (sideAdds A D S hS) ω k := by
  rw [StepAdds.perm_append, bridgeDropData_perm]
  refine Equiv.ext fun p => ?_
  rw [Equiv.Perm.mul_apply]
  unfold bridgeSideData
  rw [StepAdds.pullOpt_perm]
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDrop_apply_lt e A C₁ F d₂ E kq d₀ D ω k h,
      bridgeDropAdds_apply_lt e A C₁ F d₂ E kq d₀ _ ω k h, addsDrop_sideAdds]
    simp only [sideAt, h, ↓reduceIte]
    rcases dropPos (A := A) C₁ k with _ | ⟨s, c⟩
    · rfl
    · by_cases hc : (c : ℕ) = 0
      · simp only [hc, ↓reduceIte, Option.elim, StepAdds.comap_perm]
        rfl
      · simp only [hc, ↓reduceIte, Option.elim]
        rfl
  · rw [bridgeDrop_apply_ge e A C₁ F d₂ E kq d₀ D ω k h,
      bridgeDropAdds_apply_ge e A C₁ F d₂ E kq d₀ _ ω k h]
    simp only [sideAt, h, ↓reduceIte, Option.elim]
    rfl

omit [Nonempty (Bits m)] in
/-- **The query slots of the side reads followed by the local queries**: one per bridge step for
the local queries, and those of the side reads. -/
theorem slotQ_bridgeSideData_append :
    CoSimSchedule.slotQ ((bridgeSideData e A C₁ F d₂ E kq d₀ S).append
      (bridgeDropData e A C₁ F d₂ E kq d₀ D)).nb (bT A C₁ F kq + 1) =
      CoSimSchedule.slotQ (bridgeSideData e A C₁ F d₂ E kq d₀ S).nb (bT A C₁ F kq + 1) +
        (bT A C₁ F kq + 1) := by
  rw [show ((bridgeSideData e A C₁ F d₂ E kq d₀ S).append
      (bridgeDropData e A C₁ F d₂ E kq d₀ D)).nb =
      fun k => (bridgeSideData e A C₁ F d₂ E kq d₀ S).nb k + 1 from rfl,
    CoSimSchedule.slotQ_add, CoSimSchedule.slotQ_one _ le_rfl]

end GordieHowe.Quantum
