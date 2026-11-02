-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.ExpandCohRelabel
public import GordieHowe.Model.Quantum.Interactive.ConstReg
public import GordieHowe.Model.Quantum.Interactive.AdaptiveTP

@[expose] public section

/-!
# The trace-preserving form of an adversary with a constant register

The value of a constant classical register (`AdaptiveIAlg.withConst`) enters only the initial
state, so the trace-preserving form at one value is the one at another value with the initial
state replaced (`toTPKindAlg_withConst`), and the expanded coherent runs of their compositions
have the law of the composition of the latter (`simLaw_congr_kindAlg`).

- `AdaptiveIAlg.toTPKindAlg_withConst`: the trace-preserving forms at two values.
- `KindAlg.composeBothOut_withInit`: the composition with the initial state replaced.
- `KindAlg.simLaw_congr_kindAlg`: equal adversaries, outputs equal up to the type, give runs of the
  same law.
-/

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {Req Resp O T Z B' : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (C : Challenger (Bits m) (BitStr I J) Req Resp) (e : BitStr I J ≃ B')
  (E : Expansion (Bits m) B' Z) (k : ℕ)

/-- **Equal adversaries with outputs equal up to the type** give expanded coherent runs of their
compositions with the same law. -/
theorem KindAlg.simLaw_congr_kindAlg {ksK : KindShape (Bits m) (BitStr I J) Req Resp} {K K' : KindAlg ksK O} (h : K = K')
    (g : Option (K.CW C) → Z) (g' : Option (K'.CW C) → Z) (hg : HEq g g') :
    simLaw e (expandAdv e E k (((K.composeBothOut C id).toQueryAlgCoh).mapOut g)) =
      simLaw e (expandAdv e E k (((K'.composeBothOut C id).toQueryAlgCoh).mapOut g')) := by
  subst h
  cases hg
  rfl

/-- **The composition with the initial state replaced** is the composition of the adversary with
the initial state replaced. -/
theorem KindAlg.composeBothOut_withInit {ksK : KindShape (Bits m) (BitStr I J) Req Resp} (K : KindAlg ksK O)
    (ρ : MState (DReg K.W K.width (Bits m) (BitStr I J) Req Resp)) :
    (({ K with init := ρ } : KindAlg _ O).composeBothOut C id) =
      { K.composeBothOut C id with
        init := MState.withAnc KindAlg.x₀
          (({ K with init := ρ } : KindAlg _ O).initSys C) } :=
  rfl

variable [Fintype T] [DecidableEq T] {shB : AlgShape (Bits m) (BitStr I J) Req Resp} (B : AdaptiveIAlg shB O)
  (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg (B.W × T) B.width (Bits m) (BitStr I J) Req Resp)
        (DReg (B.W × T) B.width (Bits m) (BitStr I J) Req Resp))

/-- **The trace-preserving form at the value `t` of a constant register** is the one at `t'` with
the initial state at `t`. -/
theorem AdaptiveIAlg.toTPKindAlg_withConst (t t' : T) :
    (B.withConst T t st).toTPKindAlg =
      { (B.withConst T t' st).toTPKindAlg with init := (B.withConst T t st).toTPKindAlg.init } := by
  unfold AdaptiveIAlg.toTPKindAlg
  dsimp only
  congr 1

/-- **The trace-preserving steps with replaced Kraus maps do not read the constant register's
value** (`AdaptiveIAlg.tpStepOf`). -/
theorem AdaptiveIAlg.tpStepOf_withConst (t t' : T)
    (y : StepIdx B.slots B.post →
      KrausMap B.R (DReg (B.W × T) B.width (Bits m) (BitStr I J) Req Resp)
        (DReg (B.W × T) B.width (Bits m) (BitStr I J) Req Resp)) :
    (B.withConst T t st).tpStepOf false y = (B.withConst T t' st).tpStepOf false y :=
  rfl

/-! ### The initial state along a relabelling of the workspace -/

namespace KindAlg

variable [Nonempty (BitStr I J)] {ksK : KindShape (Bits m) (BitStr I J) Req Resp} (K : KindAlg ksK O)

/-- A permutation of the workspace on the adversary's registers. -/
def dLift (φ : Equiv.Perm K.W) : Equiv.Perm (DReg K.W K.width (Bits m) (BitStr I J) Req Resp) :=
  (φ.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)

/-- A permutation of the workspace on the composed registers with the reprogramming ancilla. -/
def vLift (φ : Equiv.Perm K.W) : Equiv.Perm (K.CW C × (Bits m × BitStr I J × Bool)) where
  toFun c := (⟨K.dLift φ c.1.adv, c.1.chal⟩, c.2)
  invFun c := (⟨(K.dLift φ).symm c.1.adv, c.1.chal⟩, c.2)
  left_inv c := by simp
  right_inv c := by simp

/-- **The initial state of the composition along a relabelling of the workspace**: if `K`'s initial
state is `ρ` relabelled by `φ`, the composition's is the one of `K` started at `ρ`, relabelled. -/
theorem composeBothOut_init_relabel (φ : Equiv.Perm K.W)
    (ρ : MState (DReg K.W K.width (Bits m) (BitStr I J) Req Resp))
    (hρ : K.init.mat = ρ.mat.submatrix (K.dLift φ).symm (K.dLift φ).symm) :
    (K.composeBothOut C id).init.mat =
      (({ K with init := ρ } : KindAlg _ O).composeBothOut C id).init.mat.submatrix
        ((K.vLift C φ).prodCongr (Equiv.refl _)).symm ((K.vLift C φ).prodCongr (Equiv.refl _)).symm := by
  ext p p'
  simp only [MState.withAnc, withAnc, KindAlg.initSys, MState.mix, MState.reindex,
    MState.tensorKet_mat, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, hρ]
  rfl

/-- **The composition's initial state reads the adversary's**: a nonzero entry has nonzero
adversary entries. -/
theorem composeBothOut_init_ne {ρ : MState (DReg K.W K.width (Bits m) (BitStr I J) Req Resp)}
    {p p' : QueryReg (K.CW C × (Bits m × BitStr I J × Bool)) 1 (Bits m) (BitStr I J)}
    (h : (({ K with init := ρ } : KindAlg _ O).composeBothOut C
      id).init.mat p p' ≠ 0) : ρ.mat p.1.1.adv p'.1.1.adv ≠ 0 := by
  intro h0
  apply h
  simp only [MState.withAnc, withAnc, KindAlg.initSys, MState.mix, MState.reindex,
    MState.tensorKet_mat, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  rw [Finset.sum_eq_zero fun ω _ => ?_, zero_mul]
  change ((_ : ℂ) • (ρ.mat p.1.1.adv p'.1.1.adv * _)) = 0
  rw [h0, zero_mul, smul_zero]

end KindAlg

namespace AdaptiveIAlg

variable [Fintype T] [DecidableEq T] {shB : AlgShape (Bits m) (BitStr I J) Req Resp} (B : AdaptiveIAlg shB O)
  (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg (B.W × T) B.width (Bits m) (BitStr I J) Req Resp)
        (DReg (B.W × T) B.width (Bits m) (BitStr I J) Req Resp))

/-- The swap of two values of the constant register, on the trace-preserving form's workspace. -/
def constSwap (t t' : T) : Equiv.Perm ((B.W × T) × Fin (B.budget + 2)) :=
  ((Equiv.refl B.W).prodCongr (Equiv.swap t t')).prodCongr (Equiv.refl _)

/-- **The initial state of the trace-preserving form at `t'`** is the one at `t` along the swap of
`t` and `t'`. -/
theorem toTPKindAlg_withConst_init (t t' : T) :
    (B.withConst T t' st).toTPKindAlg.init.mat =
      (B.withConst T t st).toTPKindAlg.init.mat.submatrix
        ((B.withConst T t' st).toTPKindAlg.dLift (B.constSwap t t')).symm
        ((B.withConst T t' st).toTPKindAlg.dLift (B.constSwap t t')).symm := by
  ext ⟨⟨⟨⟨w, x⟩, c⟩, rr⟩, qs⟩ ⟨⟨⟨⟨w', x'⟩, c'⟩, rr'⟩, qs'⟩
  have key : (Matrix.single t t (1 : ℂ)) (Equiv.swap t t' x) (Equiv.swap t t' x') =
      (Matrix.single t' t' (1 : ℂ)) x x' := by
    have e1 : ∀ y : T, (t = Equiv.swap t t' y ↔ t' = y) := fun y => by
      rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, eq_comm]
    simp only [Matrix.single_apply, e1]
  change B.init.mat ((w, rr), qs) ((w', rr'), qs') * (Matrix.single t' t' (1 : ℂ)) x x' *
      (Matrix.single (0 : Fin (B.budget + 2)) 0 (1 : ℂ)) c c' =
    B.init.mat ((w, rr), qs) ((w', rr'), qs') *
      (Matrix.single t t (1 : ℂ)) (Equiv.swap t t' x) (Equiv.swap t t' x') *
      (Matrix.single (0 : Fin (B.budget + 2)) 0 (1 : ℂ)) c c'
  rw [key]

/-- **The trace-preserving form's initial state at `t` holds `t`** in the constant register. -/
theorem toTPKindAlg_withConst_init_ne (t : T)
    {d d' : DReg (shB.withConstS T).CntW B.width (Bits m) (BitStr I J) Req Resp}
    (h : (B.withConst T t st).toTPKindAlg.init.mat d d' ≠ 0) : d.1.1.1.2 = t ∧ d'.1.1.1.2 = t := by
  obtain ⟨⟨⟨⟨w, x⟩, c⟩, rr⟩, qs⟩ := d
  obtain ⟨⟨⟨⟨w', x'⟩, c'⟩, rr'⟩, qs'⟩ := d'
  change B.init.mat ((w, rr), qs) ((w', rr'), qs') * (Matrix.single t t (1 : ℂ)) x x' *
      (Matrix.single (0 : Fin (B.budget + 2)) 0 (1 : ℂ)) c c' ≠ 0 at h
  have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  rw [Matrix.single_apply] at h2
  split_ifs at h2 with hh
  · exact ⟨hh.1.symm, hh.2.symm⟩
  · exact absurd rfl h2

variable [Nonempty (BitStr I J)]

/-- **The composition at `t'` has the initial state of the composition at `t'` started at the
initial state at `t`**, along the swap of `t` and `t'`. -/
theorem composeBothOut_withConst_init (t t' : T) :
    ((B.withConst T t' st).toTPKindAlg.composeBothOut C id).init.mat =
      (MState.withAnc KindAlg.x₀
        (({ (B.withConst T t' st).toTPKindAlg with init := (B.withConst T t st).toTPKindAlg.init } :
          KindAlg _ O).initSys C)).mat.submatrix
        (((B.withConst T t' st).toTPKindAlg.vLift C (B.constSwap t t')).prodCongr (Equiv.refl _)).symm
        (((B.withConst T t' st).toTPKindAlg.vLift C (B.constSwap t t')).prodCongr (Equiv.refl _)).symm :=
  KindAlg.composeBothOut_init_relabel C _ _ _ (B.toTPKindAlg_withConst_init st t t')

/-- **The expanded coherent run of the composition at `t`** has the law of the composition at `t'`
started at the initial state at `t`, for outputs equal up to the type. -/
theorem simLaw_withConst_reinit (t t' : T) (g : Option ((B.withConst T t st).toTPKindAlg.CW C) → Z)
    (g' : Option ((B.withConst T t' st).toTPKindAlg.CW C) → Z) (hg : HEq g g') :
    simLaw e (expandAdv e E k ((((B.withConst T t st).toTPKindAlg.composeBothOut C id).toQueryAlgCoh).mapOut g)) =
      simLaw e (expandAdv e E k ((({ (B.withConst T t' st).toTPKindAlg.composeBothOut C id with
        init := MState.withAnc KindAlg.x₀
          (({ (B.withConst T t' st).toTPKindAlg with init := (B.withConst T t st).toTPKindAlg.init } :
            KindAlg _ O).initSys C) } :
          Alg (Bits m) (BitStr I J) _).toQueryAlgCoh).mapOut g')) :=
  (KindAlg.simLaw_congr_kindAlg C e E k (B.toTPKindAlg_withConst st t t') g g' hg).trans
    (congrArg (fun Q : Alg (Bits m) (BitStr I J) ((B.withConst T t' st).toTPKindAlg.CW C) =>
      simLaw e (expandAdv e E k ((Q.toQueryAlgCoh).mapOut g')))
      (KindAlg.composeBothOut_withInit C _ _))

end AdaptiveIAlg

end GordieHowe.Quantum
