-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RevealedHybrid
public import GordieHowe.Model.Quantum.Interactive.ClassicalSimLogs
public import GordieHowe.Model.Quantum.Interactive.QueryBoundedZK

@[expose] public section

/-!
# Adaptive reprogramming at revealed points against classical challengers

Grilo, Hövelmanns, Hülsing and Majenz ("Tight adaptive reprogramming in the QROM", ASIACRYPT
2021, ePrint 2020/1361; GHHM21), Theorem 1, equation (2), bounds the advantage of distinguishing
a random oracle from one reprogrammed at `r` adaptively chosen points by
`|Pr[Repro_1] − Pr[Repro_0]| ≤ ∑_r (√(q̂_r p_max^(r)) + ½ q̂_r p_max^(r))`.

Here the reprogramming is done by a challenger. For a `RevealedPair` of challengers `C₀` (which
reprograms nothing) and `C₁` (which, at request `e`, reprograms the component `Y₁` of the oracle,
through `sp : Y ≃+ Y₁ × Y₂`, on a set of points of `B` that contains each point with probability
at most `ε` over the request's fresh coins),
`Distinguisher.abs_sum_acceptWithAt_revealed_le` bounds the difference of the acceptance
probabilities of a distinguisher with a budget of `q` slots of `n` parallel queries by
`∑_{e < Q} (√(ε W_e) + ε W_e / 2)` with `W_e = n q + C₀.q e`: `W_e` charges the adversary's
queries and the plain challenger's classical reads before request `e`. The accepted event may
read the outcome, the request logs and the final oracle in force.

`AdaptiveIAlg.advantage_revealed_le` transfers the bound to interactive adversaries through their
dilation with the post phase as query slots (`KindAlg.dilPost`, `AdaptiveIAlg.dilPostBudget`):
an event of the output, the logs and the final oracle in force of the composition has the coin
average of the probability of `KindAlg.postEvent` in the pure game
(`KindAlg.toOuterMeasure_outLaw_composeBothOut_event`). `advantage_revealed_le_of_queries_le`
states it for an adversary making at most `t` queries. The `_mixB` forms
(`Distinguisher.abs_sum_acceptWithAt_revealed_le_mixB`, `AdaptiveIAlg.advantage_revealed_le_mixB`,
`advantage_revealed_le_mixB_of_queries_le`) fix the oracle off `B` and its second components and
sum over the first components on `B`, for adversaries and events that read those. `toReal_toOuterMeasure_mem_image_le` is the
union bound for the point probability of a set of `K` points.

The proof differs from GHHM21's: each reprogramming is bounded by a reflection bound
(`O2H/RevealedStep.lean`) in place of their trace-norm step, and the expected distance of the state from its
average over the reprogrammed set by an Efron–Stein junta-degree bound (`O2H/JuntaDegree.lean`,
`O2H/StageDegree.lean`) in place of their support Lemma 1.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace Distinguisher

variable {W X Y Y₁ Y₂ Req Resp : Type} [Fintype W] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y]
  [Nonempty Y] [Nonempty Req] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  [Nonempty Y₁] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ}
  {C₀ C₁ : Challenger X Y Req Resp} (P : C₀.RevealedPair sp B ε C₁)

include P in
/-- **Adaptive reprogramming at revealed points in the pure game** (GHHM21 Theorem 1): for a
distinguisher with a budget of `q` query slots of `n` parallel queries and an event of its
outcome, its logs and the final oracle in force, the acceptance probabilities against `C₀` and
against `C₁`, averaged over the uniform oracle and the coins, differ by at most
`∑_{e < Q} (√(ε W_e) + ε W_e / 2)` with `W_e = n q + C₀.q e`. -/
theorem abs_sum_acceptWithAt_revealed_le {q : ℕ} (bud : D.Budget q)
    (Pev : DReg W n X Y Req Resp → LogReg Req m → (X → Y) → Prop) :
    |∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ∑ c, (C₀.coins c).toReal * D.acceptWithAt C₀.toPureEnv Pev (H, c) -
      ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ∑ c, (C₁.coins c).toReal * D.acceptWithAt C₁.toPureEnv Pev (H, c)| ≤
      ∑ e ∈ range C₀.Q, (√(ε * (n * q + C₀.q * e)) + ε * (n * q + C₀.q * e) / 2) := by
  set a : ℕ → ℝ := fun e => ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
    ∑ ψ, (P.hLaw ψ).toReal * D.acceptWithAt (P.hyb e).toPureEnv Pev (H, ψ)
  have h₀ : ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
      ∑ c, (C₀.coins c).toReal * D.acceptWithAt C₀.toPureEnv Pev (H, c) = a C₀.Q := by
    simp only [a, D.sum_acceptWithAt_hyb_Q P Pev]
  have h₁ : ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
      ∑ c, (C₁.coins c).toReal * D.acceptWithAt C₁.toPureEnv Pev (H, c) = a 0 := by
    simp only [a, D.sum_acceptWithAt_hyb_zero P Pev]
  rw [h₀, h₁, abs_sub_comm, ← Finset.sum_range_sub' a C₀.Q]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
  exact D.abs_sum_acceptWithAt_hyb_succ_le P bud (Finset.mem_range.1 he) Pev

open Classical in
include P in
/-- **Adaptive reprogramming at revealed points at fixed values off `B` and fixed second
components**: as `abs_sum_acceptWithAt_revealed_le`, with the oracle `H` mixed with `g` on `B`
and summed over `g`, the bound scaled by `|Y₁^X|`. -/
theorem abs_sum_acceptWithAt_revealed_le_mixB {q : ℕ} (bud : D.Budget q)
    (Pev : DReg W n X Y Req Resp → LogReg Req m → (X → Y) → Prop) (H : X → Y) :
    |∑ g : X → Y₁, ∑ c, (C₀.coins c).toReal * D.acceptWithAt C₀.toPureEnv Pev (mixB sp B H g, c) -
      ∑ g : X → Y₁, ∑ c, (C₁.coins c).toReal *
        D.acceptWithAt C₁.toPureEnv Pev (mixB sp B H g, c)| ≤
      Fintype.card (X → Y₁) *
        ∑ e ∈ range C₀.Q, (√(ε * (n * q + C₀.q * e)) + ε * (n * q + C₀.q * e) / 2) := by
  set a : ℕ → ℝ := fun e => ∑ g : X → Y₁,
    ∑ ψ, (P.hLaw ψ).toReal * D.acceptWithAt (P.hyb e).toPureEnv Pev (mixB sp B H g, ψ)
  have h₀ : ∑ g : X → Y₁, ∑ c, (C₀.coins c).toReal *
      D.acceptWithAt C₀.toPureEnv Pev (mixB sp B H g, c) = a C₀.Q := by
    simp only [a, D.sum_acceptWithAt_hyb_Q P Pev]
  have h₁ : ∑ g : X → Y₁, ∑ c, (C₁.coins c).toReal *
      D.acceptWithAt C₁.toPureEnv Pev (mixB sp B H g, c) = a 0 := by
    simp only [a, D.sum_acceptWithAt_hyb_zero P Pev]
  rw [h₀, h₁, abs_sub_comm, ← Finset.sum_range_sub' a C₀.Q, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
  exact D.abs_sum_acceptWithAt_hyb_succ_le_mixB P bud (Finset.mem_range.1 he) Pev H

end Distinguisher

/-! ### Interactive adversaries -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)

/-- **The dilated adversary with its post phase as query slots** (`dilateIn` at every output,
`Distinguisher.withPostSlots`): the distinguisher whose final outcomes carry the adversary's
output and halting flag. -/
noncomputable def dilPost :
    Distinguisher (A.DW × Bool) X Y Req Resp A.width (A.slots + A.post) :=
  (A.dilateIn Set.univ).withPostSlots (fun j => A.uStepD (A.slots + 1 + j)) A.post

/-- **An event of the output, the logs and the final oracle, read on the outcomes of
`dilPost`**: the outcome is placed with the post flag set, its logs are the adversary's logs
extended by blank post slots, the halting flag is clear and the event holds at the output. -/
def postEvent (E : O → LogReg Req A.slots → (X → Y) → Prop) :
    DReg (A.DW × Bool) A.width X Y Req Resp → LogReg Req (A.slots + A.post) → (X → Y) → Prop :=
  fun d' lg' H => ∃ d lg, d' = withFlag true d ∧ lg' = extLogs A.post lg ∧ d.1.1.2.1 = false ∧
    E (A.out d.1.1.1) lg H

/-- **An event of the composition's output, logs and final oracle in force** has the coin average
of the probability of `postEvent` in the pure game of `dilPost`. -/
theorem toOuterMeasure_outLaw_composeBothOut_event (C : Challenger X Y Req Resp) (H : X → Y)
    (E : O → LogReg Req A.slots → (X → Y) → Prop) :
    ((A.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, E (A.out v.adv.workspace) v.chal.logs
          (C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)} =
      ENNReal.ofReal (∑ c, (C.coins c).toReal *
        A.dilPost.acceptWithAt C.toPureEnv (A.postEvent E) (H, c)) := by
  classical
  rw [A.toOuterMeasure_outLaw_composeBothOut_id C H (fun v => E (A.out v.adv.workspace)
    v.chal.logs (C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs))]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  set T : LogReg Req A.slots → Set O := fun lg => {o | E o lg (C.toPureEnv.oracle (H, c) lg)}
    with hT
  have hr : ∀ r : A.G, (if E (A.out (A.emb C H c A.slots r).1.adv.workspace)
      (A.emb C H c A.slots r).1.chal.logs (C.toPureEnv.oracle
        (H, (A.emb C H c A.slots r).1.chal.coins) (A.emb C H c A.slots r).1.chal.logs) then
      (A.mgRun C.toPureEnv (H, c) true r r).re else 0) =
      ∑ lg : LogReg Req A.slots, if A.out r.1.1 ∈ T lg ∧
        (splitLogs r).2 ∈ ({lg} : Set (LogReg Req A.slots)) then
        (A.mgRun C.toPureEnv (H, c) true r r).re else 0 := fun r => by
    rw [Finset.sum_eq_single (splitLogs r).2
      (fun lg _ hlg => ite_eq_right_iff.2 fun h => absurd h.2.symm hlg)
      (fun h => absurd (Finset.mem_univ _) h)]
    exact if_congr ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩ rfl rfl
  rw [Finset.sum_congr rfl fun r _ => hr r, Finset.sum_comm]
  have hlg : ∀ lg : LogReg Req A.slots, (∑ r : A.G,
      if A.out r.1.1 ∈ T lg ∧ (splitLogs r).2 ∈ ({lg} : Set _) then
        (A.mgRun C.toPureEnv (H, c) true r r).re else 0) =
      (A.dilateIn (T lg)).acceptProbOnAt C.toPureEnv A.postOp {lg} (H, c) := fun lg => by
    rw [acceptProbOnAt_dilateIn, ← mgAcceptOn_deph]
    unfold mgAcceptOn
    exact Finset.sum_congr rfl fun r _ => by congr
  simp only [hlg]
  have hF : ∀ T' : Set O, (A.dilateIn T').final C.toPureEnv A.postOp (H, c) =
      (A.dilateIn Set.univ).final C.toPureEnv A.postOp (H, c) := fun _ => rfl
  have hpost : A.postOp = fun H => Distinguisher.postN
      (fun j => A.uStepD (A.slots + 1 + j)) H A.post :=
    funext fun H => A.postOpN_eq_postN H _
  have hrun : A.dilPost.run C.toPureEnv (H, c) = A.dilPost.final C.toPureEnv noPost (H, c) := by
    simp only [Distinguisher.final, noPost]
    rw [GordieHowe.Quantum.logControlled_refl]
  rw [Distinguisher.acceptWithAt, hrun, dilPost, Distinguisher.final_withPostSlots, ← hpost,
    prob_embV (embR_injective _ true)]
  simp only [Distinguisher.acceptProbOnAt, hF, prob, norm_mask_sq, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single (splitLogs r).2 ?_ (fun h => absurd (Finset.mem_univ _) h)]
  · refine if_congr ?_ rfl rfl
    have hs : splitLogs (embR A.post true r) =
        (withFlag true (splitLogs r).1, extLogs A.post (splitLogs r).2) :=
      rfl
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hs]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩
      refine ⟨(splitLogs r).1, (splitLogs r).2, rfl, rfl, h1, ?_⟩
      rw [Distinguisher.oracle_extLogs]
      exact h2
    · rintro ⟨d, lg, hd, hl, h1, h2⟩
      obtain rfl := withFlag_injective true hd
      obtain rfl := extLogs_injective A.post hl
      rw [Distinguisher.oracle_extLogs] at h2
      exact ⟨⟨h1, h2⟩, rfl⟩
  · intro lg _ hlg
    exact ite_eq_right_iff.2 fun h => absurd h.2.symm hlg

end KindAlg

namespace AdaptiveIAlg

variable {X Y Y₁ Y₂ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [Nonempty Req] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  [Nonempty Y₁] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

open Classical in
/-- `dilBudget` at the output `o`, carried to `dilateIn` (same kind, initial state and steps). -/
noncomputable def dilBudget_dilateIn (o : O) : (A.toKindAlg.dilateIn Set.univ).Budget A.budget :=
  (A.dilBudget o).ofSteps (by rw [KindAlg.dilate_kind]; rfl) (by rw [KindAlg.dilate_init]; rfl)
    (funext fun k => by rw [KindAlg.dilate_step]; rfl)

open Classical in
/-- **The dilated adversary accepting at every output has a budget of `budget` query slots**
(`dilBudget` at any output; with no outputs there are no workspaces). -/
noncomputable def dilInBudget : (A.toKindAlg.dilateIn Set.univ).Budget A.budget where
  inv k c := if h : Nonempty O then (A.dilBudget h.some).inv k c else ∅
  init hm := by
    by_cases h : Nonempty O
    · simp only [h, ↓reduceDIte]
      exact (A.dilBudget_dilateIn h.some).init hm
    · intro r
      exact (h ⟨A.toKindAlg.out r.1.1.1⟩).elim
  step k hk c b v hv := by
    by_cases h : Nonempty O
    · simp only [h, ↓reduceDIte] at hv ⊢
      exact (A.dilBudget_dilateIn h.some).step k hk c b v hv
    · intro r
      exact (h ⟨A.toKindAlg.out r.1.1.1⟩).elim
  cap k hk c w hw hkind := by
    by_cases h : Nonempty O
    · simp only [h, ↓reduceDIte] at hw
      exact (A.dilBudget_dilateIn h.some).cap k hk c w hw hkind
    · exact (h ⟨A.toKindAlg.out w.1⟩).elim

/-- **The dilated adversary with its post phase as slots has a budget of `budget + post` query
slots.** -/
noncomputable def dilPostBudget : A.toKindAlg.dilPost.Budget (A.budget + A.post) :=
  Distinguisher.Budget.withPostSlots _ _ _ A.dilInBudget

/-- **Adaptive reprogramming at revealed points against an interactive adversary** (GHHM21
Theorem 1). -/
theorem advantage_revealed_le {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ}
    {C₀ C₁ : Challenger X Y Req Resp} (P : C₀.RevealedPair sp B ε C₁)
    (E : O → LogReg Req A.slots → (X → Y) → Prop) :
    |∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((A.toKindAlg.composeBothOut C₀ id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, E (A.toKindAlg.out v.adv.workspace) v.chal.logs
            (C₀.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)}).toReal -
      ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((A.toKindAlg.composeBothOut C₁ id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, E (A.toKindAlg.out v.adv.workspace) v.chal.logs
            (C₁.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)}).toReal| ≤
      ∑ e ∈ range C₀.Q, (√(ε * (A.width * (A.budget + A.post) + C₀.q * e)) +
        ε * (A.width * (A.budget + A.post) + C₀.q * e) / 2) := by
  have h := fun (C : Challenger X Y Req Resp) (H : X → Y) =>
    (congrArg ENNReal.toReal (A.toKindAlg.toOuterMeasure_outLaw_composeBothOut_event C H E)).trans
      (ENNReal.toReal_ofReal (Finset.sum_nonneg fun c _ =>
        mul_nonneg ENNReal.toReal_nonneg (prob_nonneg _ _)))
  simp only [h]
  have hb := Distinguisher.abs_sum_acceptWithAt_revealed_le A.toKindAlg.dilPost P A.dilPostBudget
    (A.toKindAlg.postEvent E)
  push_cast at hb
  exact hb

/-- **`advantage_revealed_le` for an adversary making at most `t` queries**: with
`width (budget + post) ≤ t` and `W = t + C₀.q Q`, at most `Q (√(ε W) + ε W / 2)`. -/
theorem advantage_revealed_le_of_queries_le {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ}
    {C₀ C₁ : Challenger X Y Req Resp} (P : C₀.RevealedPair sp B ε C₁)
    (E : O → LogReg Req A.slots → (X → Y) → Prop) {t : ℕ}
    (ht : A.width * (A.budget + A.post) ≤ t) :
    |∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((A.toKindAlg.composeBothOut C₀ id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, E (A.toKindAlg.out v.adv.workspace) v.chal.logs
            (C₀.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)}).toReal -
      ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((A.toKindAlg.composeBothOut C₁ id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, E (A.toKindAlg.out v.adv.workspace) v.chal.logs
            (C₁.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)}).toReal| ≤
      C₀.Q * (√(ε * (t + C₀.q * C₀.Q)) + ε * (t + C₀.q * C₀.Q) / 2) := by
  refine (A.advantage_revealed_le P E).trans ?_
  rcases Nat.eq_zero_or_pos C₀.Q with hQ | hQ
  · simp [hQ]
  -- The point probability bound at an empty history forces `0 ≤ ε`.
  have hε : 0 ≤ ε := by
    obtain ⟨ω₀, -⟩ := P.ν.support_nonempty
    obtain ⟨c₀, -⟩ := P.ζ.support_nonempty
    exact ENNReal.toReal_nonneg.trans (P.pts_le ω₀ (fun _ => c₀) [] (Classical.arbitrary Req)
      (fun _ => Classical.arbitrary Y) (Classical.arbitrary X) hQ)
  calc ∑ e ∈ range C₀.Q, (√(ε * (A.width * (A.budget + A.post) + C₀.q * e)) +
        ε * (A.width * (A.budget + A.post) + C₀.q * e) / 2) ≤
      ∑ _e ∈ range C₀.Q, (√(ε * (t + C₀.q * C₀.Q)) + ε * (t + C₀.q * C₀.Q) / 2) := by
        refine Finset.sum_le_sum fun e he => ?_
        have hW : ((A.width * (A.budget + A.post) + C₀.q * e : ℕ) : ℝ) ≤
            ((t + C₀.q * C₀.Q : ℕ) : ℝ) :=
          Nat.cast_le.2 (Nat.add_le_add ht (Nat.mul_le_mul_left _ (Finset.mem_range.1 he).le))
        push_cast at hW
        have hm := mul_le_mul_of_nonneg_left hW hε
        exact add_le_add (Real.sqrt_le_sqrt hm) (by linarith)
    _ = _ := by simp [mul_add]

open Classical in
/-- **`advantage_revealed_le` at fixed values off `B` and fixed second components**: the oracle
`H` mixed with `g` on `B`, summed over `g`, the bound scaled by `|Y₁^X|`. For adversaries or
events that read the oracle off `B` or its second components. -/
theorem advantage_revealed_le_mixB {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ}
    {C₀ C₁ : Challenger X Y Req Resp} (P : C₀.RevealedPair sp B ε C₁)
    (E : O → LogReg Req A.slots → (X → Y) → Prop) (H : X → Y) :
    |∑ g : X → Y₁,
        (((A.toKindAlg.composeBothOut C₀ id).outLaw (mixB sp B H g)).toOuterMeasure
          {o | ∃ v ∈ o, E (A.toKindAlg.out v.adv.workspace) v.chal.logs
            (C₀.toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)}).toReal -
      ∑ g : X → Y₁,
        (((A.toKindAlg.composeBothOut C₁ id).outLaw (mixB sp B H g)).toOuterMeasure
          {o | ∃ v ∈ o, E (A.toKindAlg.out v.adv.workspace) v.chal.logs
            (C₁.toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)}).toReal| ≤
      Fintype.card (X → Y₁) * ∑ e ∈ range C₀.Q,
        (√(ε * (A.width * (A.budget + A.post) + C₀.q * e)) +
          ε * (A.width * (A.budget + A.post) + C₀.q * e) / 2) := by
  have h := fun (C : Challenger X Y Req Resp) (H : X → Y) =>
    (congrArg ENNReal.toReal (A.toKindAlg.toOuterMeasure_outLaw_composeBothOut_event C H E)).trans
      (ENNReal.toReal_ofReal (Finset.sum_nonneg fun c _ =>
        mul_nonneg ENNReal.toReal_nonneg (prob_nonneg _ _)))
  simp only [h]
  have hb := Distinguisher.abs_sum_acceptWithAt_revealed_le_mixB A.toKindAlg.dilPost P
    A.dilPostBudget (A.toKindAlg.postEvent E) H
  push_cast at hb
  exact hb

open Classical in
/-- **`advantage_revealed_le_mixB` for an adversary making at most `t` queries**: with
`width (budget + post) ≤ t` and `W = t + C₀.q Q`, at most `|Y₁^X| Q (√(ε W) + ε W / 2)`. -/
theorem advantage_revealed_le_mixB_of_queries_le {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ}
    {C₀ C₁ : Challenger X Y Req Resp} (P : C₀.RevealedPair sp B ε C₁)
    (E : O → LogReg Req A.slots → (X → Y) → Prop) (H : X → Y) {t : ℕ}
    (ht : A.width * (A.budget + A.post) ≤ t) :
    |∑ g : X → Y₁,
        (((A.toKindAlg.composeBothOut C₀ id).outLaw (mixB sp B H g)).toOuterMeasure
          {o | ∃ v ∈ o, E (A.toKindAlg.out v.adv.workspace) v.chal.logs
            (C₀.toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)}).toReal -
      ∑ g : X → Y₁,
        (((A.toKindAlg.composeBothOut C₁ id).outLaw (mixB sp B H g)).toOuterMeasure
          {o | ∃ v ∈ o, E (A.toKindAlg.out v.adv.workspace) v.chal.logs
            (C₁.toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)}).toReal| ≤
      Fintype.card (X → Y₁) * C₀.Q * (√(ε * (t + C₀.q * C₀.Q)) + ε * (t + C₀.q * C₀.Q) / 2) := by
  refine (A.advantage_revealed_le_mixB P E H).trans ?_
  rcases Nat.eq_zero_or_pos C₀.Q with hQ | hQ
  · simp [hQ]
  -- The point probability bound at an empty history forces `0 ≤ ε`.
  have hε : 0 ≤ ε := by
    obtain ⟨ω₀, -⟩ := P.ν.support_nonempty
    obtain ⟨c₀, -⟩ := P.ζ.support_nonempty
    exact ENNReal.toReal_nonneg.trans (P.pts_le ω₀ (fun _ => c₀) [] (Classical.arbitrary Req)
      (fun _ => Classical.arbitrary Y) (Classical.arbitrary X) hQ)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc ∑ e ∈ range C₀.Q, (√(ε * (A.width * (A.budget + A.post) + C₀.q * e)) +
        ε * (A.width * (A.budget + A.post) + C₀.q * e) / 2) ≤
      ∑ _e ∈ range C₀.Q, (√(ε * (t + C₀.q * C₀.Q)) + ε * (t + C₀.q * C₀.Q) / 2) := by
        refine Finset.sum_le_sum fun e he => ?_
        have hW : ((A.width * (A.budget + A.post) + C₀.q * e : ℕ) : ℝ) ≤
            ((t + C₀.q * C₀.Q : ℕ) : ℝ) :=
          Nat.cast_le.2 (Nat.add_le_add ht (Nat.mul_le_mul_left _ (Finset.mem_range.1 he).le))
        push_cast at hW
        have hm := mul_le_mul_of_nonneg_left hW hε
        exact add_le_add (Real.sqrt_le_sqrt hm) (by linarith)
    _ = _ := by simp [mul_add]

end AdaptiveIAlg

/-! ### Sets of points of bounded point probability -/

/-- **A set of `K` points, each of point probability at most `δ`, contains a given point with
probability at most `K δ`** (the union bound): for the set `{pt i c | i}` with `c ← ζ`. -/
theorem toReal_toOuterMeasure_mem_image_le {C X : Type*} [Fintype C] [DecidableEq X] {K : ℕ}
    (ζ : PMF C) (pt : Fin K → C → X) {δ : ℝ}
    (hδ : ∀ i x, (ζ.toOuterMeasure {c | pt i c = x}).toReal ≤ δ) (x : X) :
    (ζ.toOuterMeasure {c | x ∈ Finset.univ.image fun i => pt i c}).toReal ≤ K * δ := by
  have hU : {c | x ∈ Finset.univ.image fun i => pt i c} =
      ⋃ i ∈ (Finset.univ : Finset (Fin K)), {c | pt i c = x} := by
    ext c
    simp
  have hfin : ∀ i, ζ.toOuterMeasure {c | pt i c = x} ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  have hle : ζ.toOuterMeasure {c | x ∈ Finset.univ.image fun i => pt i c} ≤
      ∑ i, ζ.toOuterMeasure {c | pt i c = x} := by
    rw [hU]
    exact MeasureTheory.measure_biUnion_finset_le _ _
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => hfin i) hle).trans ?_
  rw [ENNReal.toReal_sum fun i _ => hfin i]
  calc ∑ i, (ζ.toOuterMeasure {c | pt i c = x}).toReal ≤ ∑ _i : Fin K, δ :=
        Finset.sum_le_sum fun i _ => hδ i x
    _ = K * δ := by simp

end GordieHowe.Quantum
