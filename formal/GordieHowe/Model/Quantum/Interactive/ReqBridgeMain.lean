-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridgeSupp
public import GordieHowe.Model.Quantum.Interactive.WithConstTP

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The bridge with the table's request points

`simLaw_bridge_withSteps`: the bridge with the request points of a table (`bridgeSteps`) has the law
of the expanded coherent run of the composition at the empty table with its Kraus maps read after
the request points (`Alg.precomp`).

- `simLaw_withSteps_of_write`: a query algorithm with request points on the registers of the
  expanded coherent run of an algorithm, whose writes act on the core register (`cohLiftAt`) before
  its steps, has the law of the expanded coherent run of the precomposed algorithm.
- The bridge's writes on the core register (`bridgeWrite_apply_lt`, `bridgeWrite_apply_ge`,
  `bridgeWrite_heq_lt`) and the bridge's register as the expanded run's (`bridgeReg_eq`).
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

section Generic

variable {Req' Resp' C : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  (E' : Expansion (Bits m) B C) (k : ℕ) {O' : Type} (A' : Alg (Bits m) (BitStr I J) O')
  (g : Option O' → C) (σ : Fin (A'.depth + 1) → Equiv.Perm A'.V)

/-- **A query algorithm with request points on the registers of the expanded coherent run of
`A'`, with its steps read after `σ`**, has the law of the expanded coherent run of `A'.precomp σ`:
for steps `S i = U_i ∘ π i` with `π` the precomposition of `σ` through the dilation, for a
trace-preserving `A'`. -/
theorem simLaw_ofQueryAlg_withSteps (hA : A'.TracePreserving)
    (req : Fin (A'.depth + k + 1) → (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W → Req')
    (write : Fin (A'.depth + k + 1) → Option Resp' →
      Equiv.Perm (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W)
    (hrw : ∀ k b w, req k (write k b w) = req k w)
    (S : Fin (A'.depth + k + 1) →
      QState (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
        QState (QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (QueryAlg.precompPerm (expandCohDilation A' g e E' k)
      (cohPrecompPerm k A' σ) i)).trans ((expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).step i)) :
    simLaw e ((ReqQueryAlg.ofQueryAlg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)) req write
      hrw).withSteps S) =
      simLaw e (expandAdv e E' k ((A'.precomp fun j => queryWorkPerm (σ j)).toQueryAlgCoh.mapOut g)) :=
  simLaw_steps_of_dilation e E' k A' g σ hA (expandCohDilation A' g e E' k) (fun _ => rfl) rfl
    (fun _ => rfl) S hS

/-- **A query algorithm with request points whose registers are the expanded coherent run of `A'`,
with its steps read after `σ`**, has the law of the expanded coherent run of `A'.precomp σ`: for
steps `S i = U_i ∘ π i` with `π` the precomposition of `σ` through the dilation carried to `G`
(`hG`), for a trace-preserving `A'`. -/
theorem simLaw_withSteps_transport (hA : A'.TracePreserving)
    (G : ReqQueryAlg (Bits m) (BitStr I J) Req' Resp' (A'.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hG : expandAdv e E' k (A'.toQueryAlgCoh.mapOut g) = G.withSteps G.step)
    (S : Fin (A'.depth + k + 1) →
      QState (QueryReg G.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (QueryAlg.precompPerm
      (hG ▸ expandCohDilation A' g e E' k :
        (G.withSteps G.step).Dilation (ExpandAdv.ExpansionRegister (X := Bits m) (Y := BitStr I J) k
          (A'.V × Bool)) A'.HaltAnc (Option (A'.R ⊕ Bool))) (cohPrecompPerm k A' σ) i)).trans
            (G.step i)) :
    simLaw e (G.withSteps S) =
      simLaw e (expandAdv e E' k ((A'.precomp fun j => queryWorkPerm (σ j)).toQueryAlgCoh.mapOut g)) :=
  simLaw_steps_transport e E' k A' g σ hA (G.withSteps G.step) hG S hS

/-- `precompPerm_transport_lt` with the instances of this file. -/
theorem precompPerm_transport_lt'
    (Q : QueryAlg (Bits m) (BitStr I J) (A'.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hQ : expandAdv e E' k (A'.toQueryAlgCoh.mapOut g) = Q) {i : Fin (A'.depth + k + 1)}
    (h : (i : ℕ) < A'.depth + 1) (p : QueryReg Q.W 1 (Bits m) (BitStr I J)) :
    QueryAlg.precompPerm (hQ ▸ expandCohDilation A' g e E' k :
        Q.Dilation (ExpandAdv.ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A'.V × Bool))
          A'.HaltAnc (Option (A'.R ⊕ Bool))) (cohPrecompPerm k A' σ) i p =
      hQ ▸ cohLiftAt e E' k A' g (σ ⟨i, h⟩) (hQ.symm ▸ p) := by
  subst hQ
  exact precompPerm_cohPrecompPerm_of_lt e E' k A' g σ h p

/-- `precompPerm_transport_ge` with the instances of this file. -/
theorem precompPerm_transport_ge'
    (Q : QueryAlg (Bits m) (BitStr I J) (A'.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hQ : expandAdv e E' k (A'.toQueryAlgCoh.mapOut g) = Q) {i : Fin (A'.depth + k + 1)}
    (h : ¬ (i : ℕ) < A'.depth + 1) (p : QueryReg Q.W 1 (Bits m) (BitStr I J)) :
    QueryAlg.precompPerm (hQ ▸ expandCohDilation A' g e E' k :
        Q.Dilation (ExpandAdv.ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A'.V × Bool))
          A'.HaltAnc (Option (A'.R ⊕ Bool))) (cohPrecompPerm k A' σ) i p = p := by
  subst hQ
  exact precompPerm_cohPrecompPerm_of_ge e E' k A' g σ h p

/-- `precompPerm_transport_lt'` between registers related by `HEq`. -/
theorem precompPerm_transport_heq
    (Q : QueryAlg (Bits m) (BitStr I J) (A'.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hQ : expandAdv e E' k (A'.toQueryAlgCoh.mapOut g) = Q) {i : Fin (A'.depth + k + 1)}
    (h : (i : ℕ) < A'.depth + 1) (p : QueryReg Q.W 1 (Bits m) (BitStr I J))
    (p' : QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J))
    (hp : HEq p p') :
    HEq (QueryAlg.precompPerm (hQ ▸ expandCohDilation A' g e E' k :
        Q.Dilation (ExpandAdv.ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A'.V × Bool))
          A'.HaltAnc (Option (A'.R ⊕ Bool))) (cohPrecompPerm k A' σ) i p)
      (cohLiftAt e E' k A' g (σ ⟨i, h⟩) p') := by
  subst hQ
  obtain rfl := eq_of_heq hp
  exact heq_of_eq (precompPerm_cohPrecompPerm_of_lt e E' k A' g σ h p)

/-- **A query algorithm with request points whose registers are the expanded coherent run of `A'`
(`hG`), with its writes acting as `σ` on the core register** (`h1`, `h2`) before its steps (`hS`),
has the law of the expanded coherent run of `A'.precomp σ`, for a trace-preserving `A'`. -/
theorem simLaw_withSteps_of_write (hA : A'.TracePreserving)
    (G : ReqQueryAlg (Bits m) (BitStr I J) Req' Resp' (A'.depth + k) (BaseGame.Tuple (Bits m) B C k))
    (hG : expandAdv e E' k (A'.toQueryAlgCoh.mapOut g) = G.withSteps G.step)
    (π' : Fin (A'.depth + k + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (hT : QueryReg G.W 1 (Bits m) (BitStr I J) =
      QueryReg (expandAdv e E' k (A'.toQueryAlgCoh.mapOut g)).W 1 (Bits m) (BitStr I J))
    (h1 : ∀ (i : Fin (A'.depth + k + 1)) p (h : (i : ℕ) < A'.depth + 1),
      HEq (π' i p) (cohLiftAt e E' k A' g (σ ⟨i, h⟩) (cast hT p)))
    (h2 : ∀ (i : Fin (A'.depth + k + 1)) p, ¬ (i : ℕ) < A'.depth + 1 → π' i p = p)
    (S : Fin (A'.depth + k + 1) →
      QState (QueryReg G.W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ] QState (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (hS : ∀ i, S i = (permOp (π' i)).trans (G.step i)) :
    simLaw e (G.withSteps S) =
      simLaw e (expandAdv e E' k ((A'.precomp fun j => queryWorkPerm (σ j)).toQueryAlgCoh.mapOut g)) :=
  simLaw_withSteps_transport e E' k A' g σ hA G hG S fun i =>
    (hS i).trans (congrArg (fun π => (permOp π).trans (G.step i)) (Equiv.ext fun p =>
      if h : (i : ℕ) < A'.depth + 1 then
        eq_of_heq ((h1 i p h).trans
          (precompPerm_transport_heq e E' k A' g σ _ hG h p _ (cast_heq hT p).symm).symm)
      else (h2 i p h).trans (precompPerm_transport_ge' e E' k A' g σ _ hG h p).symm))

end Generic

/-- **The step after a slot is a step of the composition**: a request point at step `k` lies within
the composition's depth. -/
theorem answerSlot_le_depth {k : ℕ} {j : Fin A.slots} (h : answerSlot A C₁ k = some j) :
    k ≤ (bridgeCompose A C₁ F).depth := by
  have hD : (bridgeCompose A C₁ F).depth =
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries :=
    ReprogrammedCircuit.depth_compiledAlg _ _ _ _
  rw [hD, KindAlg.queries_fullCircBoth]
  unfold answerSlot at h
  split_ifs at h with hh
  obtain ⟨⟨c, hc⟩, h1, h2⟩ := hh
  have hq : 0 < C₁.q + A.width := by have := A.width_pos; omega
  have hkc : k / (C₁.q + A.width) = c := by
    rw [hc, Nat.mul_div_cancel_left _ hq]
  have hc' : c ≤ A.slots := by omega
  have : k ≤ A.slots * (C₁.q + A.width) := by
    rw [hc, mul_comm]
    exact Nat.mul_le_mul_right _ hc'
  change k ≤ A.slots * (C₁.q + A.width) + A.width * A.post
  omega

theorem answerSlot_eq_none_of_depth_lt {k : ℕ} (hk : (bridgeCompose A C₁ F).depth < k) :
    answerSlot A C₁ k = none := by
  rcases h : answerSlot A C₁ k with _ | j
  · rfl
  · exact absurd (answerSlot_le_depth A C₁ F h) (by omega)

theorem bridgeWrite_apply (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeWrite e A C₁ F d₂ E kq d₀ tab k p =
      ((bridgeAlg e A C₁ F d₂ E kq d₀).write k (bridgeRep e A C₁ F d₂ E kq d₀ tab k p.1) p.1, p.2) :=
  rfl

theorem liftAbs_eq_liftV (π : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂))
    (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    liftAbs e A C₁ F E kq d₀ π w =
      (((liftV A C₁ F π w.1.1.1, w.1.1.2), w.1.2), w.2) :=
  rfl

theorem bridgeAlg_write_of_none {k : Fin (bT A C₁ F kq + 1)} (h : answerSlot A C₁ k = none)
    (x : Option Resp₂) : (bridgeAlg e A C₁ F d₂ E kq d₀).write k x = Equiv.refl _ := by
  change (match answerSlot A C₁ k with
    | none => Equiv.refl _
    | some j => liftAbs e A C₁ F E kq d₀ (answerDelta A F j x)) = _
  rw [h]

theorem bridgeAlg_write_of_some {k : Fin (bT A C₁ F kq + 1)} {j : Fin A.slots}
    (h : answerSlot A C₁ k = some j) (x : Option Resp₂) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).write k x = liftAbs e A C₁ F E kq d₀ (answerDelta A F j x) := by
  change (match answerSlot A C₁ k with
    | none => Equiv.refl _
    | some j => liftAbs e A C₁ F E kq d₀ (answerDelta A F j x)) = _
  rw [h]

theorem writeV_of_none (tab : A.OuterTab Req₂ Resp₂) (T : ℕ) {k : ℕ} (h : answerSlot A C₁ k = none) :
    writeV A C₁ F d₂ tab T k = Equiv.refl _ := by
  unfold writeV
  rw [h]

theorem writeV_of_some (tab : A.OuterTab Req₂ Resp₂) (T : ℕ) {k : ℕ} {j : Fin A.slots}
    (h : answerSlot A C₁ k = some j) (v : (bridgeCompose A C₁ F).V) :
    writeV A C₁ F d₂ tab T k v = liftV A C₁ F (answerDelta A F j (repV A C₁ F d₂ tab T k v)) v := by
  unfold writeV
  rw [h]
  rfl

/-- The work register of the expanded coherent purification of the composition, the bridge's. -/
abbrev bridgeW : Type :=
  (expandAdv e E kq ((bridgeCompose A C₁ F).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A)))).W

theorem bridgeWrite_cast (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    (bridgeWrite e A C₁ F d₂ E kq d₀ tab k :
      Equiv.Perm (QueryReg (bridgeW e A C₁ F E kq d₀) 1 (Bits m) (BitStr I J))) p =
      bridgeWrite e A C₁ F d₂ E kq d₀ tab k p :=
  rfl

theorem bridgeWrite_apply_lt₀ (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeWrite e A C₁ F d₂ E kq d₀ tab k p =
      ((((writeV A C₁ F d₂ tab (bT A C₁ F kq) k p.1.1.1.1, p.1.1.1.2), p.1.1.2), p.1.2), p.2) := by
  rw [bridgeWrite_apply]
  rcases h : answerSlot A C₁ k with _ | j
  · rw [bridgeAlg_write_of_none e A C₁ F d₂ E kq d₀ h]
    simp only [writeV, h, Equiv.refl_apply]
    rfl
  · rw [bridgeAlg_write_of_some e A C₁ F d₂ E kq d₀ h, liftAbs_eq_liftV]
    simp only [writeV, h]
    rfl

theorem bridgeWrite_apply_lt (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeWrite e A C₁ F d₂ E kq d₀ tab k p =
      cohLiftAt e E kq ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id) (extOut A C₁ F d₀ (tab₀ A)) (writeV A C₁ F d₂ tab (bT A C₁ F kq) k) p :=
  bridgeWrite_apply_lt₀ e A C₁ F d₂ E kq d₀ tab k p

theorem bridgeWrite_apply_ge (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J))
    (hd : ¬ (k : ℕ) < (bridgeCompose A C₁ F).depth + 1) :
    bridgeWrite e A C₁ F d₂ E kq d₀ tab k p = p := by
  rw [bridgeWrite_apply]
  have h : answerSlot A C₁ k = none := answerSlot_eq_none_of_depth_lt A C₁ F (by omega)
  rw [bridgeAlg_write_of_none e A C₁ F d₂ E kq d₀ h]
  rfl

/-- The bridge's register is the register of the expanded coherent run of the composition. -/
theorem bridgeReg_eq : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J) =
    QueryReg (expandAdv e E kq (((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A)))).W 1 (Bits m) (BitStr I J) := by
  with_reducible rfl

/-- `bridgeWrite_apply_lt` across `bridgeReg_eq`. -/
theorem bridgeWrite_heq_lt (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    HEq (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p)
      (cohLiftAt e E kq ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id) (extOut A C₁ F d₀ (tab₀ A)) (writeV A C₁ F d₂ tab (bT A C₁ F kq) k)
        (cast (bridgeReg_eq e A C₁ F d₂ E kq d₀) p)) := by
  with_reducible
    refine (heq_of_eq (bridgeWrite_apply_lt e A C₁ F d₂ E kq d₀ tab k p)).trans ?_
    exact heq_of_eq (congrArg _ (eq_of_heq (cast_heq (bridgeReg_eq e A C₁ F d₂ E kq d₀) p).symm))

/-- The composition is trace preserving. -/
theorem bridgeCompose_tracePreserving : (bridgeCompose A C₁ F).TracePreserving :=
  (AdaptiveIAlg.stepsTP_toTPKindAlg _).tracePreserving_composeBothOut C₁ id

/-- The bridge's registers, initial state, steps and output, as a query algorithm. -/
noncomputable abbrev bridgeQ :=
  (bridgeAlg e A C₁ F d₂ E kq d₀).withSteps (bridgeAlg e A C₁ F d₂ E kq d₀).step

/-- **The bridge with the table's request points has the law of the expanded coherent run of the
composition with its Kraus maps read after the request points** (`Alg.precomp`). -/
theorem simLaw_bridge_withSteps (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).withSteps (bridgeSteps e A C₁ F d₂ E kq d₀ tab)) =
      simLaw e (expandAdv e E kq ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).precomp fun j =>
        queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).toQueryAlgCoh.mapOut
          (extOut A C₁ F d₀ (tab₀ A)))) :=
  simLaw_withSteps_of_write e E kq ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id) (extOut A C₁ F d₀ (tab₀ A))
    (fun j => writeV A C₁ F d₂ tab (bT A C₁ F kq) j) (bridgeCompose_tracePreserving A C₁ F)
    (bridgeAlg e A C₁ F d₂ E kq d₀) rfl (bridgeWrite e A C₁ F d₂ E kq d₀ tab)
    (bridgeReg_eq e A C₁ F d₂ E kq d₀)
    (fun i p _ => bridgeWrite_heq_lt e A C₁ F d₂ E kq d₀ tab i p)
    (fun i p h => bridgeWrite_apply_ge e A C₁ F d₂ E kq d₀ tab i p h)
    (bridgeSteps e A C₁ F d₂ E kq d₀ tab) (fun _ => rfl)

end GordieHowe.Quantum
