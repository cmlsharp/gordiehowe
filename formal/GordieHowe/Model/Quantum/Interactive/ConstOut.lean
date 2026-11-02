-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Compressed
public import GordieHowe.Model.Quantum.Core.Dilation
public import GordieHowe.Model.Quantum.Interactive.AbsorbBudget
public import GordieHowe.Model.Quantum.Interactive.ProgAlg
public import GordieHowe.Model.Quantum.Interactive.QueryBounded
public import GordieHowe.Model.Quantum.Interactive.TPRun
public import GordieHowe.Model.RingSignature.Adversary

@[expose] public section

/-!
# Adversaries that output a drawn value

An adversary of the model that makes no query and no request and outputs a value drawn from a
fixed distribution: the members of the adversary class whose run is a classical draw.

- `AdaptiveIAlg.constAlg X Y Req Resp o`: the adversary with a one-point workspace, no slot, no
  query batch, an arbitrary basis state as its initial state, the identity as its one step, and the
  output `o`. `submatrix_kronecker_one_one`, `constAlg_liftG_apply`: its lifted steps are the
  identity. `constAlg_mgRun`: its mixed game ends in its initial state, against every environment;
  `trace_mgRun_constAlg`: of trace `1`. `outLaw_composeBothOut_constAlg`: a composition read by a
  constant map `f` outputs that constant with probability `1`.
- `QueryBoundedAdversary.ofLaw X Y Req Resp μ`: the `0`-query adversary that draws `o` from `μ`
  as its auxiliary input and runs `constAlg o`. `transcriptLaw_ofLaw`: against every challenger
  and at every oracle its transcript is `o` drawn from `μ` with the empty history.
-/

open Matrix
open scoped BigOperators ENNReal Kronecker

/-- **A distribution with an atom of mass `1` is the point mass there.** -/
theorem PMF.eq_pure_of_apply_eq_one {α : Type*} {p : PMF α} {a : α} (h : p a = 1) :
    p = PMF.pure a := by
  ext b
  by_cases hb : b = a
  · subst hb
    rw [h, PMF.pure_apply_self]
  · rw [PMF.pure_apply_of_ne _ _ hb]
    refine (PMF.apply_eq_zero_iff p b).2 ?_
    rw [(PMF.apply_eq_one_iff p a).1 h]
    exact hb

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable (X Y Req Resp : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [Nonempty Y]
  [Nonempty Req] {O : Type}

/-- The shape of `constAlg`: a one-point workspace, width one, no slot, no post batch, no
budget, one Kraus operator. -/
@[reducible] def _root_.GordieHowe.Quantum.AlgShape.constS : AlgShape X Y Req Resp where
  W := Unit
  width := 1
  width_pos := Nat.one_pos
  slots := 0
  post := 0
  budget := 0
  R := Unit

/-- **The adversary that outputs `o`**: a one-point workspace, no slot, no query batch, an
arbitrary basis state of its registers as its initial state, the identity as its one step. -/
noncomputable def constAlg (o : O) : AdaptiveIAlg (AlgShape.constS X Y Req Resp) O where
  kind _ := false
  init := MState.ofVec (EuclideanSpace.single (Classical.arbitrary _) 1) (by simp)
  step _ := KrausMap.identity _
  out _ := o

variable {X Y Req Resp} (o : O)

/-- A reindexed Kronecker product of a reindexed Kronecker product of identities is the
identity. -/
theorem submatrix_kronecker_one_one {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    [DecidableEq ε] (e₁ : α ≃ β × γ) (e₂ : δ ≃ α × ε) :
    ((((1 : Matrix β β ℂ) ⊗ₖ (1 : Matrix γ γ ℂ)).submatrix e₁ e₁) ⊗ₖ
      (1 : Matrix ε ε ℂ)).submatrix e₂ e₂ = 1 := by
  rw [one_kronecker_one, submatrix_one_equiv, one_kronecker_one, submatrix_one_equiv]

/-- **The lifted steps of `constAlg` are the identity.** -/
theorem constAlg_liftG_apply (k : StepIdx 0 0)
    (ρ : Matrix (constAlg X Y Req Resp o).toKindAlg.G (constAlg X Y Req Resp o).toKindAlg.G ℂ) :
    (constAlg X Y Req Resp o).toKindAlg.liftG k ρ = ρ := by
  have hop : ∀ r, ((constAlg X Y Req Resp o).toKindAlg.liftG k).op r = 1 := by
    intro r
    simp only [KindAlg.liftG, KrausMap.reindex, KrausMap.tensorId, AdaptiveIAlg.toKindAlg,
        AlgShape.kindStep_eq, AdaptiveIAlg.kindS, AdaptiveIAlg.CntW, AlgShape.CntW, KindAlg.W,
        KindAlg.width, KindAlg.slots, KindAlg.post, KindAlg.R]
    split_ifs with h
    · exact absurd h (Nat.not_lt_zero _)
    · exact submatrix_kronecker_one_one _ _
  rw [KrausMap.apply]
  simp only [hop, Matrix.one_mul, Matrix.mul_one, conjTranspose_one]
  change ∑ _x : Unit, ρ = ρ
  simp

/-- **The mixed game of `constAlg` ends in its initial state**: it has no slot and no query
batch, and its one step is the identity. -/
theorem constAlg_mgRun [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y]
    (E : Env Ω Req Resp X Y Q St) (ω : Ω) (deph : Bool) :
    (constAlg X Y Req Resp o).toKindAlg.mgRun E ω deph =
      (constAlg X Y Req Resp o).toKindAlg.mgInit := by
  simp only [KindAlg.mgRun, KindAlg.mgCirc]
  rw [Circuit.run_append, Circuit.run_append]
  change Circuit.run _ _ (Circuit.run _ (Circuit.concat ((List.finRange 0).map _))
    (Circuit.run _ (Circuit.concat ((List.finRange 0).map _)) _)) = _
  simp only [List.finRange_zero]
  exact constAlg_liftG_apply o _ _

/-- **The mixed game of `constAlg` keeps the trace.** -/
theorem trace_mgRun_constAlg [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y]
    (E : Env Ω Req Resp X Y Q St) (ω : Ω) (deph : Bool) :
    ((constAlg X Y Req Resp o).toKindAlg.mgRun E ω deph).trace = 1 := by
  rw [constAlg_mgRun]
  exact (constAlg X Y Req Resp o).toKindAlg.mgInitM.trace_eq_one

/-- **The step of `constAlg` is a channel.** -/
theorem constAlg_tracePreserving : (constAlg X Y Req Resp o).TracePreserving := by
  intro k
  change ∑ _r : Unit, ((1 : Matrix (DReg Unit 1 X Y Req Resp) (DReg Unit 1 X Y Req Resp) ℂ)ᴴ *
    1) = 1
  rw [Finset.univ_unique, Finset.sum_singleton, conjTranspose_one]
  exact Matrix.one_mul _

variable [AddGroup Y]

/-- **A composition of `constAlg` read by a constant map outputs the constant**: against every
challenger and at every oracle, with probability `1`. -/
theorem outLaw_composeBothOut_constAlg (C : Challenger X Y Req Resp) {O' : Type}
    [DecidableEq O'] (f : (constAlg X Y Req Resp o).toKindAlg.CW C → O') (o' : O')
    (hf : ∀ v, f v = o') (H : X → Y) :
    ((constAlg X Y Req Resp o).toKindAlg.composeBothOut C f).outLaw H = PMF.pure (some o') := by
  refine PMF.eq_pure_of_apply_eq_one ?_
  rw [KindAlg.outLaw_composeBothOut_some]
  have hd : ∀ c : C.Coins, ∑ r : (constAlg X Y Req Resp o).toKindAlg.G,
      (if f ((constAlg X Y Req Resp o).toKindAlg.emb C H c
          (constAlg X Y Req Resp o).toKindAlg.slots r).1 = o' then
        ((constAlg X Y Req Resp o).toKindAlg.mgRun C.toPureEnv (H, c) true r r).re else 0) = 1 := by
    intro c
    simp only [hf, ↓reduceIte]
    have h := congrArg Complex.re (trace_mgRun_constAlg o C.toPureEnv (H, c) true)
    rw [Matrix.trace, Complex.re_sum, Complex.one_re] at h
    exact h
  simp only [hd, mul_one]
  have hsum : ∑ c, C.coins c = 1 := by
    rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  rw [← ENNReal.toReal_sum fun c _ => PMF.apply_ne_top _ c, hsum, ENNReal.toReal_one,
    ENNReal.ofReal_one]

/-- **`constAlg` stays within its budget**: its composition always terminates. -/
theorem constAlg_withinBudget : (constAlg X Y Req Resp o).WithinBudget := by
  refine (withinBudget_iff _).2 fun C H => ?_
  rw [outLaw_compose_none_eq, ENNReal.ofReal_eq_zero, sub_nonpos]
  have h : ∀ c, ((constAlg X Y Req Resp o).toKindAlg.mgRun C.toPureEnv (H, c) true).trace.re = 1 :=
    fun c => (congrArg Complex.re (trace_mgRun_constAlg o _ _ _)).trans Complex.one_re
  simp only [h, mul_one]
  have hsum : ∑ c, C.coins c = 1 := by
    rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  rw [← ENNReal.toReal_sum fun c _ => PMF.apply_ne_top _ c, hsum, ENNReal.toReal_one]

end AdaptiveIAlg

namespace QueryBoundedAdversary

variable (X Y Req Resp : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [Nonempty Req] {O : Type}

/-- **The adversary that outputs a draw from `μ`**: the auxiliary input `o` drawn from `μ`, then
`constAlg o`. It makes no query and no request. -/
noncomputable def ofLaw (μ : PMF O) : QueryBoundedAdversary X Y Req Resp O 0 where
  Aux := O
  aux := μ
  sh o := (AdaptiveIAlg.constAlg X Y Req Resp o).toShape
  alg o := AdaptiveIAlg.constAlg X Y Req Resp o
  tracePreserving o := AdaptiveIAlg.constAlg_tracePreserving o
  withinBudget o := AdaptiveIAlg.constAlg_withinBudget o
  queries_le _ := le_of_eq (by simp [AdaptiveIAlg.constAlg])

variable {X Y Req Resp}

/-- **The transcript of `ofLaw μ`**: against every challenger and at every oracle, the output is
drawn from `μ` and the history is empty. -/
theorem transcriptLaw_ofLaw (μ : PMF O) (C : Challenger X Y Req Resp) (H : X → Y) :
    (ofLaw X Y Req Resp μ).transcriptLaw C H = μ.map fun o => some (o, []) := by
  classical
  rw [transcriptLaw, PMF.map]
  congr 1
  funext o
  exact AdaptiveIAlg.outLaw_composeBothOut_constAlg o C _ (o, []) (fun _ => rfl) H

end QueryBoundedAdversary

end GordieHowe.Quantum
