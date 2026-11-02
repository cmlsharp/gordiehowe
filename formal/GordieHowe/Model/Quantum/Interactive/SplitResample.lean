-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.SplitHybrid

@[expose] public section

/-!
# Resampling the draws of a split challenger

Two split challengers with the same keys law and number of requests, whose reply programs at
every keys, request number and request have the same law over their own draws, give every event
of the adversary's registers, the logs, the keys and the final oracle in force the same
probability (`SplitChallenger.toOuterMeasure_outLaw_eq_of_map_reply_eq`).

- `PMF.map_fst_bind_map_prod`, `PMF.map_snd_bind_map_prod`: the marginals of a product law.
- `SplitChallenger.evProb_comp_eq`: a challenger whose reply reads its draw through `f` has the
  event probability of the challenger with the pushed-forward draw law.
- `SplitChallenger.abs_evProb_hybReply_sub_le_of_tvDist`, `SplitChallenger.evProb_eq_of_map_eq`:
  the hybrid of `SplitHybrid` with the step bounded by the distance of the reply laws.
-/

open Finset
open scoped BigOperators ENNReal

namespace PMF

variable {α β : Type*}

/-- The first marginal of the product law `p ⊗ q`. -/
theorem map_fst_bind_map_prod (p : PMF α) (q : PMF β) :
    (p.bind fun a => q.map fun b => (a, b)).map Prod.fst = p := by
  rw [map_bind]
  simp only [map_comp, Function.comp_def]
  exact (congrArg p.bind (funext fun a => map_const q a)).trans (bind_pure p)

/-- The second marginal of the product law `p ⊗ q`. -/
theorem map_snd_bind_map_prod (p : PMF α) (q : PMF β) :
    (p.bind fun a => q.map fun b => (a, b)).map Prod.snd = q := by
  rw [map_bind]
  simp only [map_comp, Function.comp_def]
  exact (bind_const p _).trans (map_id q)

end PMF

namespace GordieHowe.Quantum.SplitChallenger

variable {X Y Req Resp K D : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] {O : Type}
  {D' : Type} [Fintype D'] [DecidableEq D']

omit [Nonempty X] in
/-- **Reading the draw through a map**: if `S₂` has the keys and number of requests of `S₁` and
its draw law pushed through `f` is `S₁`'s, then reply programs reading `S₂`'s draw through `f`
give the event `S₁`'s coin-averaged pure game probability. -/
theorem evProb_comp_eq (S₁ : SplitChallenger X Y Req Resp K D)
    (S₂ : SplitChallenger X Y Req Resp K D') (f : D' → D) (hk : S₂.keys = S₁.keys)
    (hQ : S₂.Q = S₁.Q) (hd : S₂.draw.map f = S₁.draw)
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop)
    (R : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp)) :
    S₂.evProb B H P (fun κ d => R κ (f d)) = S₁.evProb B H P R := by
  obtain ⟨k₁, p₁, Q, q₁, r₁, h₁⟩ := S₁
  obtain ⟨k₂, p₂, Q₂, q₂, r₂, h₂⟩ := S₂
  dsimp only at hk hQ hd
  subst hk hQ hd
  set S₁ : SplitChallenger X Y Req Resp K D := ⟨k₂, p₂.map f, Q₂, q₁, r₁, h₁⟩
  set S₂ : SplitChallenger X Y Req Resp K D' := ⟨k₂, p₂, Q₂, q₂, r₂, h₂⟩
  set φ : K × (Fin Q₂ → D') → K × (Fin Q₂ → D) := fun c => (c.1, fun i => f (c.2 i))
  have hcoin : S₂.coinLaw.map φ = S₁.coinLaw := by
    simp only [coinLaw, S₁, S₂, PMF.map_bind, PMF.map_comp]
    congr 1
    funext κ
    rw [← PMF.pi_map (fun _ : Fin Q₂ => p₂) (fun _ => f), PMF.map_comp]
    rfl
  unfold evProb
  rw [← hcoin, PMF.sum_toReal_map_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1

omit [Nonempty X] in
/-- **One step of the hybrid, by the distance of the reply laws**: hybrids `j` and `j + 1` give
the event probabilities within `e` if at each keys and request the laws of the two reply programs
at request `j` over that request's draw are within `e` (`abs_evProb_hybReply_sub_le`). -/
theorem abs_evProb_hybReply_sub_le_of_tvDist (S : SplitChallenger X Y Req Resp K D)
    (reply' : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp))
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop)
    {j : ℕ} (hj : j < S.Q) {e : ℝ} (he0 : 0 ≤ e)
    (he : ∀ κ r, PMF.tvDist (S.draw.map fun d => S.reply κ d j r)
      (S.draw.map fun d => reply' κ d j r) ≤ e) :
    |S.evProb B H P (S.hybReply reply' j) - S.evProb B H P (S.hybReply reply' (j + 1))| ≤ e := by
  classical
  set j' : Fin S.Q := ⟨j, hj⟩
  set Dd := B.unitOut.dilate ()
  set Ej := S.oracleEnv (S.hybReply reply' j)
  set w : (Fin S.Q → D) → ℝ := fun d => ∏ i, (S.draw (d i)).toReal
  have hcoin : ∀ (κ : K) (d : Fin S.Q → D), (S.coinLaw (κ, d)).toReal = (S.keys κ).toReal * w d :=
    fun κ d => by rw [coinLaw_apply, ENNReal.toReal_mul, ENNReal.toReal_prod]
  have hw1 : ∑ d, w d = 1 := by
    simpa [w, PMF.toReal_pi_apply] using PMF.sum_toReal (PMF.pi fun _ : Fin S.Q => S.draw)
  have hsplit : ∀ R, S.evProb B H P R = ∑ κ, (S.keys κ).toReal * ∑ d, w d *
      Dd.probOracleAt B.unitOut.postOp (S.oracleEnv R)
        (fun F => B.unitOut.dilSet (evSet B P κ F)) (H, κ, d) := fun R => by
    rw [evProb, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hcoin, mul_assoc]
  have hR0 : ∀ κ x (c : Fin S.Q) r, c ≠ j' →
      S.hybReply reply' j κ x c r = S.hybReply reply' j κ x c r := fun _ _ _ _ _ => rfl
  have hR1 : ∀ κ x (c : Fin S.Q) r, c ≠ j' →
      S.hybReply reply' (j + 1) κ x c r = S.hybReply reply' j κ x c r := by
    intro κ x c r hc
    have hcj : (c : ℕ) ≠ j := fun h => hc (Fin.ext h)
    simp only [hybReply]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩
  rw [hsplit, hsplit, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ κ, |(S.keys κ).toReal * ∑ d, w d * Dd.probOracleAt B.unitOut.postOp
          (S.oracleEnv (S.hybReply reply' j)) (fun F => B.unitOut.dilSet (evSet B P κ F)) (H, κ, d) -
        (S.keys κ).toReal * ∑ d, w d * Dd.probOracleAt B.unitOut.postOp
          (S.oracleEnv (S.hybReply reply' (j + 1))) (fun F => B.unitOut.dilSet (evSet B P κ F))
          (H, κ, d)|
      ≤ ∑ κ, (S.keys κ).toReal * e := Finset.sum_le_sum fun κ _ => by
        rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        rw [sum_prod_toReal_mul_eq_sum_update S.draw j' (fun d => Dd.probOracleAt B.unitOut.postOp
            (S.oracleEnv (S.hybReply reply' j)) (fun F => B.unitOut.dilSet (evSet B P κ F))
            (H, κ, d)),
          sum_prod_toReal_mul_eq_sum_update S.draw j' (fun d => Dd.probOracleAt B.unitOut.postOp
            (S.oracleEnv (S.hybReply reply' (j + 1))) (fun F => B.unitOut.dilSet (evSet B P κ F))
            (H, κ, d)), ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ d, |w d * ∑ τ, (S.draw τ).toReal * Dd.probOracleAt B.unitOut.postOp
                (S.oracleEnv (S.hybReply reply' j)) (fun F => B.unitOut.dilSet (evSet B P κ F))
                (H, κ, Function.update d j' τ) -
              w d * ∑ τ, (S.draw τ).toReal * Dd.probOracleAt B.unitOut.postOp
                (S.oracleEnv (S.hybReply reply' (j + 1)))
                (fun F => B.unitOut.dilSet (evSet B P κ F)) (H, κ, Function.update d j' τ)|
            ≤ ∑ d, w d * e := Finset.sum_le_sum fun d _ => by
              rw [← mul_sub, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun _ _ =>
                ENNReal.toReal_nonneg)]
              refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun _ _ =>
                ENNReal.toReal_nonneg)
              simp only [S.probOracleAt_update_eq Dd B.unitOut.postOp _ _ j' hR0,
                S.probOracleAt_update_eq Dd B.unitOut.postOp _ _ j' hR1]
              refine Dd.abs_sum_probOracleAt_withResponse_sub_le B.unitOut.postOp Ej (H, κ, d) j'
                (logLocal_dilSet B P κ) _ _ he0 fun req rs _ => ?_
              set H' := Ej.oracleIn (H, κ, d) rs
              refine le_trans (le_of_eq ?_) ((PMF.tvDist_map_le _ _
                (fun pr => (S.oracleEnv fun _ _ _ _ => pr).respond (H, κ, d) j' req H')).trans
                (he κ req))
              rw [PMF.map_comp, PMF.map_comp]
              congr 2 <;> funext τ <;>
                simp [oracleEnv, hybReply, j', Function.update_self]
          _ = e := by rw [← Finset.sum_mul, hw1, one_mul]
    _ = e := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

omit [Nonempty X] in
/-- **Equal reply laws give equal event probabilities**: if at each request number `j < Q`, keys
and request the two reply programs have the same law over that request's draw, the event's
coin-averaged pure games against `reply` and `reply'` are equal. -/
theorem evProb_eq_of_map_eq (S : SplitChallenger X Y Req Resp K D)
    (reply' : K → D → ℕ → Req → OracleProg X Y (Reply X Y Resp))
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop)
    (hmap : ∀ j < S.Q, ∀ κ r,
      S.draw.map (fun d => S.reply κ d j r) = S.draw.map (fun d => reply' κ d j r)) :
    S.evProb B H P S.reply = S.evProb B H P reply' := by
  have h0 : S.hybReply reply' 0 = S.reply := by
    funext κ d i r
    simp [hybReply]
  have hQ : S.evProb B H P (S.hybReply reply' S.Q) = S.evProb B H P reply' := by
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine (B.unitOut.dilate ()).probOracleAt_eq_of_agree B.unitOut.postOp
      (E := S.oracleEnv (S.hybReply reply' S.Q)) (E' := S.oracleEnv reply') rfl
      (funext fun i => ?_) _
    funext req H'
    simp [oracleEnv, hybReply]
  have key : ∀ j ≤ S.Q, S.evProb B H P S.reply = S.evProb B H P (S.hybReply reply' j) := by
    intro j
    induction j with
    | zero => intro _; rw [h0]
    | succ j ih =>
      intro hj
      have h := S.abs_evProb_hybReply_sub_le_of_tvDist reply' B H P (j := j) (by omega) le_rfl
        fun κ r => by rw [hmap j (by omega) κ r, PMF.tvDist_self]
      rw [ih (by omega)]
      linarith [abs_le.1 h]
  rw [key S.Q le_rfl, hQ]

/-- **Resampling the draws.** Two split challengers with the same keys law and number of
requests, whose reply programs at every keys, request number `i < Q` and request have the same
law over their own draws, give every event of the adversary's registers, the logs, the keys and
the final oracle in force the same probability.

Both are compared with the challenger on independent pairs of draws `(d, d')`, answering from `d`
(which is `S`, `evProb_comp_eq` with `Prod.fst`) or from `d'` (which is `S'`, with `Prod.snd`);
the two reply laws of the pair challenger agree at every request, so the hybrid over the requests
(`evProb_eq_of_map_eq`) makes its two event probabilities equal. -/
theorem toOuterMeasure_outLaw_eq_of_map_reply_eq
    (S : SplitChallenger X Y Req Resp K D) (S' : SplitChallenger X Y Req Resp K D')
    (hkeys : S.keys = S'.keys) (hQ : S.Q = S'.Q)
    (hmap : ∀ κ i r, i < S.Q →
      S.draw.map (fun d => S.reply κ d i r) = S'.draw.map (fun d => S'.reply κ d i r))
    {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (H : X → Y)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → K → (X → Y) → Prop) :
    ((B.composeBothOut S.toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs v.chal.coins.1
          (H.reprogram (B.postAss S.toChallenger v.chal))} =
      ((B.composeBothOut S'.toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs v.chal.coins.1
          (H.reprogram (B.postAss S'.toChallenger v.chal))} := by
  rw [S.toOuterMeasure_outLaw_eq B H P, S'.toOuterMeasure_outLaw_eq B H P]
  congr 1
  let S₂ : SplitChallenger X Y Req Resp K (D × D') :=
    { keys := S.keys
      draw := S.draw.bind fun a => S'.draw.map fun b => (a, b)
      Q := S.Q
      q := S.q
      reply := fun κ d => S.reply κ d.1
      reply_queries := fun κ d => S.reply_queries κ d.1 }
  have h1 : S₂.draw.map Prod.fst = S.draw := PMF.map_fst_bind_map_prod _ _
  have h2 : S₂.draw.map Prod.snd = S'.draw := PMF.map_snd_bind_map_prod _ _
  have hS := evProb_comp_eq S S₂ Prod.fst rfl rfl h1 B H P S.reply
  have hS' := evProb_comp_eq S' S₂ Prod.snd hkeys hQ h2 B H P S'.reply
  have hmap₂ : ∀ j < S₂.Q, ∀ κ r, S₂.draw.map (fun d => S₂.reply κ d j r) =
      S₂.draw.map (fun d => S'.reply κ d.2 j r) := by
    intro j hj κ r
    calc S₂.draw.map (fun d => S₂.reply κ d j r)
        = (S₂.draw.map Prod.fst).map (fun d => S.reply κ d j r) := by rw [PMF.map_comp]; rfl
      _ = (S₂.draw.map Prod.snd).map (fun d => S'.reply κ d j r) := by
          rw [h1, h2, hmap κ j r hj]
      _ = S₂.draw.map (fun d => S'.reply κ d.2 j r) := by rw [PMF.map_comp]; rfl
  have h3 := S₂.evProb_eq_of_map_eq (fun κ d => S'.reply κ d.2) B H P hmap₂
  change S.evProb B H P S.reply = S'.evProb B H P S'.reply
  rw [← hS, ← hS']
  exact h3

end GordieHowe.Quantum.SplitChallenger
