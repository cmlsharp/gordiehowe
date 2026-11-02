-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AbsorbAssign
public import GordieHowe.Model.RingSignature.Transcript

@[expose] public section

/-!
# Absorbing an assigning challenger through a second relay

The absorption of an assigning challenger (`GordieHowe/Model/Quantum/Interactive/AbsorbAssign.lean`)
relays the outer challenger's requests through a relay `G₁` that the outer challenger runs. At a
fixed oracle `H`, a second relay `G₂` whose programs run as `G₁`'s and make `G₁`'s main requests
at every oracle `reprogT T H` read through the table `T` they are given may replace `G₁` in the
absorbed adversary: the challengers `chalT` of the two relays answer alike at `H`, so the patched
absorbed adversary has the same law against both, and the relay step goes through `G₂`.

- `OracleProg.run_recMain_congr`: two programs with the same run and the same one main request
  run alike when recording it.
- `AssignRelay.AgreeAt`: two relays agree at `H`. `AssignRelay.run_respond_chalT_congr`: the two
  `chalT` then answer alike at `H`.
- `AdaptiveIAlg.toOuterMeasure_le_absorbAssign_swap` (**the law through a second relay**):
  `toOuterMeasure_le_absorbAssign_tab` with the absorbed adversary of `G₂`.
- `QueryBoundedAdversary.assignLaw_le_absorbAssign_swap`: the same for `t`-query adversaries.
-/

open Finset

namespace GordieHowe

namespace OracleProg

variable {X Y Req' Resp' R : Type}

/-- **Two programs with the same run and the same one main request run alike when recording it.** -/
theorem run_recMain_congr (T : X → Option Y) (h : X → Y) (m : Req' → Option Resp')
    (p p' : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R)
    (hrun : p.run (combineAns (Quantum.reprogT T h) m) =
      p'.run (combineAns (Quantum.reprogT T h) m))
    (htr : (p.trace (combineAns (Quantum.reprogT T h) m)).filterMap Sum.getRight? =
      (p'.trace (combineAns (Quantum.reprogT T h) m)).filterMap Sum.getRight?)
    (hone : ((p.trace (combineAns (Quantum.reprogT T h) m)).filterMap Sum.getRight?).length = 1) :
    (recMain T p).run (combineAns h m) = (recMain T p').run (combineAns h m) := by
  obtain ⟨r', hr'⟩ : ∃ r', (p.trace (combineAns (Quantum.reprogT T h) m)).filterMap
      Sum.getRight? = [r'] := by
    rcases hl : (p.trace (combineAns (Quantum.reprogT T h) m)).filterMap Sum.getRight? with
      _ | ⟨a, _ | ⟨b, l⟩⟩
    · rw [hl] at hone; simp at hone
    · exact ⟨a, rfl⟩
    · rw [hl] at hone; simp at hone
  refine Prod.ext ?_ ?_
  · rw [run_recMain_fst, run_recMain_fst, hrun]
  · rw [run_recMain_snd T h m p r' [] hr', run_recMain_snd T h m p' r' [] (htr ▸ hr')]

end OracleProg

namespace Quantum

namespace AssignRelay

open GordieHowe.OracleProg

variable {X Y Req Resp Req' Resp' Xs Ys Xs₁ Ys₁ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] [AddGroup Ys₁] [Fintype Ys₁]
  [DecidableEq Ys₁]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y]
  [Inhabited Req'] (C' : Challenger X Y Req' Resp') (Q : ℕ)

/-- **Two relays agree at the oracle `H`**: at every table `T`, request number and request, their
programs, with their side reads answered by their side functions, run alike at the oracle
`reprogT T H` read through `T` and make the same main request, and the relays have the same
padding request. -/
def AgreeAt (H : X → Y) (G₁ : AssignRelay X Y Req Resp Req' Resp' Xs₁ Ys₁)
    (G₂ : AssignRelay X Y Req Resp Req' Resp' Xs Ys) : Prop :=
  (∀ T c r m, (G₁.elimProg T c r).run (combineAns (reprogT T H) m) =
      (G₂.elimProg T c r).run (combineAns (reprogT T H) m)) ∧
    (∀ T c r m, ((G₁.elimProg T c r).trace (combineAns (reprogT T H) m)).filterMap
        Sum.getRight? = ((G₂.elimProg T c r).trace (combineAns (reprogT T H) m)).filterMap
          Sum.getRight?) ∧
    G₁.idle = G₂.idle

omit [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] [AddGroup Ys₁] [Fintype Ys₁] [DecidableEq Ys₁]
  [DecidableEq X] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] in
/-- A relay agrees with itself. -/
theorem AgreeAt.refl (H : X → Y) (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) :
    G.AgreeAt H G :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl⟩

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Nonempty Y] [Inhabited X] [AddGroup Y] [Inhabited Req'] [Fintype Ys] [DecidableEq Ys]
  [Fintype Ys₁] [DecidableEq Ys₁] in
/-- **The challengers `chalT` of two relays answer alike at `H`** when the relays agree at `H`
(`AgreeAt`). -/
theorem run_respond_chalT_congr (G₁ : AssignRelay X Y Req Resp Req' Resp' Xs₁ Ys₁)
    (G₂ : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (H : X → Y) (hag : G₁.AgreeAt H G₂)
    (c' : C'.Coins)
    (hist : List (HistoryEntry (TaggedReq X Y Req Q) (RespD X Y Resp Req' Resp')))
    (req : TaggedReq X Y Req Q) :
    ((chalT C' G₁ Q).respond c' hist req).run H = ((chalT C' G₂ Q).respond c' hist req).run H := by
  rw [chalT_respond, chalT_respond, run_mapOutput, run_mapOutput, relayProg, relayProg, run_lower,
    run_lower, run_recMain_congr req.2 H _ _ _ (hag.1 _ _ _ _) (hag.2.1 _ _ _ _)
      (G₁.elim_asks_eq_one _ _ _ _ _), hag.2.2]

end AssignRelay

namespace AdaptiveIAlg

variable {X Y Req Resp O Req' Resp' Xs Ys Xs₁ Ys₁ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] [AddGroup Ys₁] [Fintype Ys₁]
  [DecidableEq Ys₁]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)
variable {C : Challenger X Y Req Resp} {C' : Challenger X Y Req' Resp'}

/-- **Absorbing an assigning challenger through a second relay** (module docstring): as
`toOuterMeasure_le_absorbAssign_tab`, with the absorbed adversary of a second relay `G₂ s` whose
programs run as `G₁ s`'s and make the same main request at every oracle `reprogT T H` read through
the table `T` they are given, with the same padding request (`hag`, `AssignRelay.AgreeAt`);
`himp` is stated for `G₂ s`. -/
theorem toOuterMeasure_le_absorbAssign_swap {S : Type} [Fintype S] (σ : PMF S)
    (G₁ : S → AssignRelay X Y Req Resp Req' Resp' Xs₁ Ys₁)
    (G₂ : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G₁ s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G₁ s)) (hNA : C'.NoAssign) (hQ : C.Q ≤ C'.Q) (H : X → Y)
    (hag : ∀ s, (G₁ s).AgreeAt H (G₂ s))
    (E : O × List Req × (X → Y) → Prop)
    (E' : S → (O × (X → Option Y)) × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ s o (T : X → Option Y) (hP : List (AssignRelay.TaggedReq X Y Req C.Q))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hP.map AssignRelay.TaggedReq.req, reprogT T H) →
      (G₂ s).Explains C.Q H T hP hist' →
      E' s ((o, T), hist')) :
    ((A.toKindAlg.composeBothOut C (A.assignReadout C H)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ∑ s, σ s * (((A.absorbAssign (G₂ s) C.Q).toKindAlg.composeBothOut C' fun v =>
        ((A.absorbAssign (G₂ s) C.Q).output C' v, (A.absorbAssign (G₂ s) C.Q).history C' v)).outLaw
          H).toOuterMeasure {x | ∃ p ∈ x, E' s p} := by
  rw [A.toOuterMeasure_eq_sum_absorbAssignP_tab σ G₁ e hcoins hrel hS H E]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_
    (A.toOuterMeasure_chalT_le_absorbAssign (G₂ s) C.Q hNA hQ H E (E' s) (himp s))) zero_le
  have hR := AssignRelay.run_respond_chalT_congr C' C.Q (G₁ s) (G₂ s) H (hag s)
  have hNA₂ := AssignRelay.noAssign_chalT C' (G₂ s) C.Q
  have hAA : ∀ c' rs req, (AssignRelay.chalT C' (G₁ s) C.Q).toPureEnv.answerAfter (H, c') rs req =
      (AssignRelay.chalT C' (G₂ s) C.Q).toPureEnv.answerAfter (H, c') rs req :=
    fun c' rs req => Challenger.answerAfter_toPureEnv_map_at
      (C := AssignRelay.chalT C' (G₁ s) C.Q) (C' := AssignRelay.chalT C' (G₂ s) C.Q) id rfl hNA₂ H
      (fun c hist r => hR c hist r)
      c' rs req
  refine KindAlg.toOuterMeasure_outLaw_congr_emb (B := (A.absorbAssignP Req' Resp' C.Q).toKindAlg)
    (C := AssignRelay.chalT C' (G₁ s) C.Q) (C' := AssignRelay.chalT C' (G₂ s) C.Q) id
    (PMF.map_id _) H
    (fun c _ lg k => Challenger.answer_toPureEnv_map_at
      (C := AssignRelay.chalT C' (G₁ s) C.Q) (C' := AssignRelay.chalT C' (G₂ s) C.Q) id rfl hNA₂ H
      (fun c hist r => hR c hist r)
      c lg k)
    (fun c _ lg => Challenger.oracle_toPureEnv_map_at
      (C := AssignRelay.chalT C' (G₁ s) C.Q) (C' := AssignRelay.chalT C' (G₂ s) C.Q) id rfl hNA₂ H
      (fun c hist r => hR c hist r)
      c lg) _ _ fun c r => ?_
  have hh : (A.absorbAssignP Req' Resp' C.Q).history (AssignRelay.chalT C' (G₁ s) C.Q)
      ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' (G₁ s) C.Q) H c
        (A.absorbAssignP Req' Resp' C.Q).toKindAlg.slots r).1 =
      (A.absorbAssignP Req' Resp' C.Q).history (AssignRelay.chalT C' (G₂ s) C.Q)
      ((A.absorbAssignP Req' Resp' C.Q).toKindAlg.emb (AssignRelay.chalT C' (G₂ s) C.Q) H (id c)
        (A.absorbAssignP Req' Resp' C.Q).toKindAlg.slots r).1 := by
    unfold AdaptiveIAlg.history
    erw [KindAlg.history_stateAt_emb, KindAlg.history_stateAt_emb]
    exact congrArg (fun f => histAlong f _) (funext fun rs => funext fun req => hAA c rs req)
  unfold patchReadout TabOrigin
  rw [hh]
  rfl

end AdaptiveIAlg

namespace QueryBoundedAdversary

variable {X Y Req Resp O Req' Resp' Xs Ys Xs₁ Ys₁ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] [AddGroup Ys₁] [Fintype Ys₁]
  [DecidableEq Ys₁]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}
variable {C : Challenger X Y Req Resp} {C' : Challenger X Y Req' Resp'}

/-- **Absorbing an assigning challenger through a second relay, for `t`-query adversaries**
(`AdaptiveIAlg.toOuterMeasure_le_absorbAssign_swap` at each auxiliary value): the output, answered
requests and final oracle in force of `𝒜` against `C` lie in `E` with at most the probability that
the transcript of `𝒜.absorbAssign σ G qG hG qP hP C.Q` against `C'` lies in `E'`, under the
hypotheses of
`AdaptiveIAlg.toOuterMeasure_le_absorbAssign_swap`. -/
theorem assignLaw_le_absorbAssign_swap (𝒜 : QueryBoundedAdversary X Y Req Resp O t) {S : Type}
    [Fintype S] (σ : PMF S) (G₁ : S → AssignRelay X Y Req Resp Req' Resp' Xs₁ Ys₁)
    (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys) (qG : ℕ)
    (hG : ∀ s, (G s).qG ≤ qG) (qP : ℕ) (hP : ∀ s, (G s).qP ≤ qP) (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G₁ s).RelaysChallenger C (e.symm (s, c')) C' c')
    (hS : ∀ s, AssignRelay.SafeAssign C' (G₁ s)) (hNA : C'.NoAssign) (hQ : C.Q ≤ C'.Q) (H : X → Y)
    (hag : ∀ s, (G₁ s).AgreeAt H (G s))
    (E : O × List Req × (X → Y) → Prop)
    (E' : (O × (X → Option Y)) × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ s o (T : X → Option Y) (hP : List (AssignRelay.TaggedReq X Y Req C.Q))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hP.map AssignRelay.TaggedReq.req, reprogT T H) →
      (G s).Explains C.Q H T hP hist' →
      E' ((o, T), hist')) :
    (𝒜.assignLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbAssign σ G qG hG qP hP C.Q).transcriptLaw C' H).toOuterMeasure
        {x | ∃ p ∈ x, E' p} := by
  rw [assignLaw, transcriptLaw, absorbAssign, PMF.bind_bind, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_fintype]
  have h := (𝒜.alg a).toOuterMeasure_le_absorbAssign_swap σ G₁ G e hcoins hrel hS hNA hQ H hag E
    (fun _ => E') himp
  simp only [Function.comp_apply]
  exact h

end QueryBoundedAdversary

end Quantum

end GordieHowe
