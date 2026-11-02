-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Split
public import GordieHowe.Model.Quantum.Interactive.SplitRestrict

@[expose] public section

/-!
# The ring game at a fixed base part of the split oracle

For an additive split `sp : OracleSplit Y Y₁ Y₂` of the oracle's values
(`GordieHowe/Applications/Ring/MLDSAW1Split.lean`), an interactive adversary composed with a
classical challenger that reprograms nothing is, at the base part `OracleSplit.base sp H` of the
oracle, the restricted adversary composed with the restricted challenger
(`GordieHowe/Model/Quantum/Interactive/SplitRestrict.lean`) at the oracle `OracleSplit.prf sp H`,
with the same law.

- `Quantum.AdaptiveIAlg.outLaw_composeBothOut_restrictAt_base`,
  `Quantum.QueryBoundedAdversary.transcriptLaw_restrictAt_base`: the laws at a fixed oracle `H`,
  in the components `base sp H` and `prf sp H`.
- `Quantum.AdaptiveIAlg.toOuterMeasure_realLaw_restrictAt`: **the random-oracle form**. With `H`
  uniform, the probability of an event of the output (with the history) and of the oracle read as
  its two components is the average, over a uniform base part `H₁`, of the probability of the event
  under the restricted composition at `H₁` with its own uniform oracle `X → Y₂`
  (`OracleSplit.map_uniform_split`: the two components of a uniform oracle are independent and
  uniform).
-/

open scoped ENNReal

namespace GordieHowe

open RingSignature RingSignature.OracleSplit

namespace Quantum.AdaptiveIAlg

variable {X Y Y₁ Y₂ Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Nonempty X]
  [Nonempty Y] [Nonempty Y₂]
  (sp : OracleSplit Y Y₁ Y₂) {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (C : Challenger X Y Req Resp)

/-- **The law of the composition at the base part of the oracle**: for a challenger `C` that
reprograms nothing, every oracle `H` and every readout `g` of the output and the history, the
adversary and the challenger at the base part `base sp H`, composed at the oracle `prf sp H`, have
the output law of `A` composed with `C` at `H`. -/
theorem outLaw_composeBothOut_restrictAt_base (hC : C.NoAssign)
    (g : O → List (HistoryEntry Req Resp) → O') (H : X → Y) :
    ((A.restrictAt sp (base sp H)).toKindAlg.composeBothOut (C.restrictAt sp (base sp H))
        fun v => g ((A.restrictAt sp (base sp H)).output (C.restrictAt sp (base sp H)) v)
          ((A.restrictAt sp (base sp H)).history (C.restrictAt sp (base sp H)) v)).outLaw
        (prf sp H) =
      (A.toKindAlg.composeBothOut C fun v => g (A.output C v) (A.history C v)).outLaw H :=
  A.outLaw_composeBothOut_restrictAt sp C hC g H

variable [Nonempty Y₁]

/-- **The random-oracle form of the law at a fixed base part**: for a challenger `C` that
reprograms nothing, a readout `g` of the output and the history, and an event `E` of the outcome
and of the oracle's two components (the second read through `e₂`), the probability of `E` under
`A` composed with `C` with the oracle uniform is the average over a uniform base part `H₁` of the
probability of `E` at `H₁` under the restricted adversary composed with the restricted challenger
at `H₁`, with their uniform oracle `X → Y₂` read through `e₂`. -/
theorem toOuterMeasure_realLaw_restrictAt (hC : C.NoAssign)
    (g : O → List (HistoryEntry Req Resp) → O') {B : Type} (e₂ : Y₂ ≃ B)
    (E : Option O' → (X → Y₁) → (X → B) → Prop) :
    ((A.toKindAlg.composeBothOut C fun v => g (A.output C v) (A.history C v)).realLaw
        (Equiv.refl Y)).toOuterMeasure {p | E p.out (base sp p.oracle) (e₂ ∘ prf sp p.oracle)} =
      ∑' H₁, PMF.uniformOfFintype (X → Y₁) H₁ *
        (((A.restrictAt sp H₁).toKindAlg.composeBothOut (C.restrictAt sp H₁) fun v =>
          g ((A.restrictAt sp H₁).output (C.restrictAt sp H₁) v)
            ((A.restrictAt sp H₁).history (C.restrictAt sp H₁) v)).realLaw e₂).toOuterMeasure
          {p | E p.out H₁ p.oracle} := by
  set F : (X → Y₁) × (X → Y₂) → ℝ≥0∞ := fun G =>
    ((A.toKindAlg.composeBothOut C fun v => g (A.output C v) (A.history C v)).outLaw
      ((splitEquiv sp).symm G)).toOuterMeasure {o | E o G.1 (e₂ ∘ G.2)} with hF
  have hL : ((A.toKindAlg.composeBothOut C fun v => g (A.output C v) (A.history C v)).realLaw
      (Equiv.refl Y)).toOuterMeasure {p | E p.out (base sp p.oracle) (e₂ ∘ prf sp p.oracle)} =
      ∑ H, PMF.uniformOfFintype (X → Y) H * F (splitEquiv sp H) := by
    rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [PMF.toOuterMeasure_map_apply, hF]
    simp only [Equiv.symm_apply_apply]
    rfl
  have hR : ∀ H₁ : X → Y₁,
      (((A.restrictAt sp H₁).toKindAlg.composeBothOut (C.restrictAt sp H₁) fun v =>
        g ((A.restrictAt sp H₁).output (C.restrictAt sp H₁) v)
          ((A.restrictAt sp H₁).history (C.restrictAt sp H₁) v)).realLaw e₂).toOuterMeasure
        {p | E p.out H₁ p.oracle} =
      ∑ H₂, PMF.uniformOfFintype (X → Y₂) H₂ * F (H₁, H₂) := by
    intro H₁
    rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun H₂ _ => ?_
    rw [PMF.toOuterMeasure_map_apply, hF, A.outLaw_composeBothOut_restrictAt_join sp H₁ C hC g H₂]
    rfl
  rw [hL, tsum_fintype]
  simp only [hR]
  rw [← (splitEquiv sp).symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type, Finset.mul_sum, ← mul_assoc]
  refine Finset.sum_congr rfl fun H₁ _ => Finset.sum_congr rfl fun H₂ _ => ?_
  congr 1
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr (splitEquiv sp), Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]

end Quantum.AdaptiveIAlg

namespace Quantum.QueryBoundedAdversary

variable {X Y Y₁ Y₂ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Nonempty X]
  [Nonempty Y] [Nonempty Y₂] {t : ℕ}
  (sp : OracleSplit Y Y₁ Y₂) (A : QueryBoundedAdversary X Y Req Resp O t)

/-- **The transcript law at the base part of the oracle**: for a challenger `C` that reprograms
nothing and every oracle `H`, the adversary and the challenger at the base part `base sp H` have,
at the oracle `prf sp H`, the transcript law of `A` against `C` at `H`. -/
theorem transcriptLaw_restrictAt_base (C : Challenger X Y Req Resp) (hC : C.NoAssign)
    (H : X → Y) :
    (A.restrictAt sp (base sp H)).transcriptLaw (C.restrictAt sp (base sp H)) (prf sp H) =
      A.transcriptLaw C H :=
  A.transcriptLaw_restrictAt sp C hC H

end Quantum.QueryBoundedAdversary

end GordieHowe
