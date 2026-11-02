-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftBridgeDrop
public import GordieHowe.Model.Quantum.Interactive.CoSimScratch

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The drops of the bridge as local additions

`bridgeDropData`: the drops of the local queries of `D` on the bridge's registers
(`bridgeDrop`) as local additions (`StepAdds`, one before each step): before a step `k` of the
composition at the position of the drop of pair `i` after Kraus map `s` (`dropPos`), coordinate
`i` of the part `D.Lw` of the adversary's workspace (`dropCoord`), the branches `D.on s`
(`dropOn`), the point read from the query register or the reprogramming ancilla. `bridgeDropData_perm`: the additions of
`ω` are the drops at `ω`, so the bridge with the drops is the bridge read after the additions
(`bridgeAlgDrop_eq`).
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
  (D : A.BaseW Y₁)

/-- The coordinate of the drop before step `k` (`dropPos`; pair `0` where there is none). -/
def dropCoord (k : ℕ) : Fin A.width :=
  match dropPos (A := A) C₁ k with
  | none => ⟨0, A.width_pos⟩
  | some p => p.2

/-- Whether the drop before step `k` is made on the workspace `w`: before a step of the
composition, at a position of a drop (`dropPos`), on the branches of the local query. -/
noncomputable def dropOn (k : ℕ) (w : (A.absorbTab F (tab₀ A)).toTPKindAlg.W) : Bool :=
  if k < (bridgeCompose A C₁ F).depth + 1 then
    match dropPos (A := A) C₁ k with
    | none => false
    | some p => (D.tp F (tab₀ A)).on p.1 w
  else false

omit [Nonempty (Bits m)] [AddGroup Y₁] in
/-- `dropOn` does not read the part. -/
theorem dropOn_set (k : ℕ) (w : (A.absorbTab F (tab₀ A)).toTPKindAlg.W) (v : Fin A.width → Y₁) :
    dropOn A C₁ F D k ((D.tp F (tab₀ A)).Lw.set w v) = dropOn A C₁ F D k w := by
  unfold dropOn
  split_ifs
  · rcases dropPos (A := A) C₁ k with _ | p
    · rfl
    · exact (D.tp F (tab₀ A)).on_set _ _ _
  · rfl

/-- **The drops of the bridge as local additions** (module docstring): one addition before each
step. -/
noncomputable def bridgeDropData : StepAdds (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m)
    (BitStr I J)) (Fin (bT A C₁ F kq + 1)) (Bits m) Y₁ where
  nb _ := 1
  L k _ :=
    (fstLens _ _).comp ((fstLens _ _).comp ((fstLens _ _).comp ((fstLens _ _).comp
      (((D.tp F (tab₀ A)).wLens (C := C₁)).comp
        (coordLens Y₁ (dropCoord A C₁ k))))))
  on k _ p := dropOn A C₁ F D k p.1.1.1.1.1.adv.1.1
  x _ _ p := if p.1.1.1.1.2.2.2 then p.1.1.1.1.2.1 else (p.2 0).1
  on_set k _ _ _ := dropOn_set A C₁ F D k _ _
  x_set _ _ _ _ := rfl

theorem update_add_ite_decide {ι : Type} [DecidableEq ι] (g : ι → Y₁) (i j : ι) (b : Bool)
    (a : Y₁) :
    Function.update g i (g i + if b = true then a else 0) j =
      g j + if (decide (j = i) && b) = true then a else 0 := by
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

variable [Inhabited Req₂] (ω : Bits m → Y₁)

/-- **The additions of `ω` are the drops at `ω`.** -/
theorem bridgeDropData_perm (k : Fin (bT A C₁ F kq + 1)) :
    (bridgeDropData e A C₁ F d₂ E kq d₀ D).perm ω k = bridgeDrop e A C₁ F d₂ E kq d₀ D ω k := by
  ext1 p
  change ((bridgeDropData e A C₁ F d₂ E kq d₀ D).L k ⟨0, Nat.one_pos⟩).set p
    (((bridgeDropData e A C₁ F d₂ E kq d₀ D).L k ⟨0, Nat.one_pos⟩).get p +
      if (bridgeDropData e A C₁ F d₂ E kq d₀ D).on k ⟨0, Nat.one_pos⟩ p then
        ω ((bridgeDropData e A C₁ F d₂ E kq d₀ D).x k ⟨0, Nat.one_pos⟩ p) else 0) = _
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDrop_apply_lt e A C₁ F d₂ E kq d₀ D ω k h]
    rw [baseDrop_eq]
    simp only [bridgeDropData, dropOn, dropCoord, h, ↓reduceIte]
    rcases hp : dropPos (A := A) C₁ (k : ℕ) with _ | ⟨s, i⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, RegLens.set_get]
      rfl
    · simp only [RegLens.comp, fstLens, coordLens, KindShape.BaseQ.wLens]
      congr
      funext j
      dsimp only [KindShape.BaseQ.carryW, KindShape.BaseQ.wLens, XPos.read]
      exact update_add_ite_decide _ _ _ _ _
  · rw [bridgeDrop_apply_ge e A C₁ F d₂ E kq d₀ D ω k h]
    simp only [bridgeDropData, dropOn, h, ↓reduceIte, Bool.false_eq_true, add_zero]
    exact RegLens.set_get _ _

/-- **The bridge with the drops is the bridge read after the additions.** -/
theorem bridgeAlgDrop_eq :
    bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω =
      (bridgeAlg e A C₁ F d₂ E kq d₀).withPerm ((bridgeDropData e A C₁ F d₂ E kq d₀ D).perm ω) := by
  have h : bridgeDrop e A C₁ F d₂ E kq d₀ D ω = (bridgeDropData e A C₁ F d₂ E kq d₀ D).perm ω :=
    funext fun k => (bridgeDropData_perm e A C₁ F d₂ E kq d₀ D ω k).symm
  rw [← h]
  rfl

end GordieHowe.Quantum
