-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.RevealedBound
public import GordieHowe.Model.Quantum.O2H.StageDegree

@[expose] public section

/-!
# One reprogramming at a revealed set in a game, averaged over the fresh coin

`abs_sum_acceptWithAt_sub_le` (`GordieHowe/Model/Quantum/O2H/RevealedBound.lean`) bounds, at a
fixed `θ`, the effect of reprogramming at request `e` by the parts `γ_b` of the state of `E₀`
before the request and their distances from the averages over the reprogrammed set `S`. Here the
set is drawn with a fresh coin `c ← ζ` of the request (`θ` is `upd θ c`): the state before request
`e` does not read the coin (`hpre_ans`, `hpre_orc`), and every point is in the set with
probability at most `ε` (`hpt`). The states before request `e` have degree at most
`W = n q + d e` in the oracle (`stage_mem_degLE`, `GordieHowe/Model/Quantum/O2H/StageDegree.lean`),
for a distinguisher with a budget of `q` query slots of `n` parallel queries and answers to the
first `e` requests of degree at most `d`. So the averaged squared distance is at most
`ε W ‖γ_b‖²` (`sum_norm_sub_avgAt_sq_le`, `norm_sub_avgOn_sq_le`,
`GordieHowe/Model/Quantum/O2H/JuntaDegree.lean`), and

`avg_abs_sum_acceptWithAt_sub_le`: the coin average of the difference of the acceptance
probabilities, averaged over the oracle part `g` and the fresh values `z`, is at most
`√(ε W) + ε W / 2`.

This is GHHM21 (Grilo, Hövelmanns, Hülsing, Majenz, "Tight adaptive reprogramming in the QROM",
ASIACRYPT 2021) Theorem 6 in a game, with GHHM21 equation (12), `E_x ‖(1 − Π_x) γ‖² ≤ q p_max`, in
the form `E_c ‖(1 − Π_S) γ‖² ≤ ε W ‖γ‖²`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### General helpers -/

/-- **Jensen for the square root**: `∑ w √x ≤ √(∑ w x)` for nonnegative weights summing to one. -/
theorem sum_mul_sqrt_le_sqrt_sum {κ : Type*} (s : Finset κ) (w x : κ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) (h1 : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i * √(x i) ≤ √(∑ i ∈ s, w i * x i) := by
  refine Real.le_sqrt_of_sq_le ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => √(w i)) (fun i => √(w i) * √(x i))
  calc (∑ i ∈ s, w i * √(x i)) ^ 2 = (∑ i ∈ s, √(w i) * (√(w i) * √(x i))) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
    _ ≤ _ := hcs
    _ = ∑ i ∈ s, w i * x i := by
        have h₁ : ∑ i ∈ s, √(w i) ^ 2 = 1 := by
          rw [← h1]
          exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
        rw [h₁, one_mul]
        exact Finset.sum_congr rfl fun i hi => by
          rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hx i hi)]

section AvgFam

variable {ι X Y : Type*} [Fintype ι] [Fintype X] [DecidableEq X] [Fintype Y]

/-- A component of the average of a family of states is the average of the component. -/
theorem avgFam_apply_eq_avgOn (S : Finset X) (γ : (X → Y) → QState ι) (h : X → Y) (i : ι) :
    avgFam S γ h i = Junta.avgOn S (Junta.ofFun fun g => γ g i) h := by
  simp [avgFam, Junta.avgOn_apply, Junta.ofFun_apply]

/-- The summed squared norms of a family of states, by components. -/
theorem sum_norm_sq_eq_sum_ofFun (γ : (X → Y) → QState ι) :
    ∑ g, ‖γ g‖ ^ 2 = ∑ i, ‖Junta.ofFun fun g => γ g i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Junta.ofFun_apply]
  exact Finset.sum_comm

/-- The summed squared distances of a family of states from its averages, by components. -/
theorem sum_norm_sub_avgFam_sq_eq (S : Finset X) (γ : (X → Y) → QState ι) :
    ∑ g, ‖γ g - avgFam S γ g‖ ^ 2 =
      ∑ i, ‖Junta.ofFun (fun g => γ g i) - Junta.avgOn S (Junta.ofFun fun g => γ g i)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, PiLp.sub_apply, avgFam_apply_eq_avgOn, Junta.ofFun_apply]
  exact Finset.sum_comm

end AvgFam

namespace Distinguisher

variable {W X Y Y₁ Req A Θ Cn : Type*} [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] [Fintype Cn] {n m Q : ℕ} (D : Distinguisher W X Y Req A n m)
  {St St' : Type _} [OracleState St X Y] [OracleState St' X Y]
  {E₀ : Env (Θ × ((X → Y₁) × (X → Y₁))) Req A X Y Q St}
  {E₁ : Env (Θ × ((X → Y₁) × (X → Y₁))) Req A X Y Q St'} {e : ℕ}
  {S : Θ → List Req → Req → Finset X}

omit [DecidableEq X] in
/-- **The block states of a run have squared norms summing to at most one.** -/
theorem sum_norm_blockState_sq_le {Ω : Type*} (E : Env Ω Req A X Y Q St) (e : ℕ) (ω : Ω) :
    ∑ b, ‖D.blockState E e b ω‖ ^ 2 ≤ 1 := by
  have hrun : ‖D.run E ω‖ = 1 := by
    rw [Distinguisher.run, Distinguisher.stage, norm_hybrid, D.norm_gameInit]
  have h := prob_eq_add_sum_evLogs e Set.univ (D.run E ω)
  rw [prob_univ, hrun, one_pow] at h
  have hb : ∀ b, ‖D.blockState E e b ω‖ ^ 2 = prob (Set.univ ∩ logsIn (evLogs e b)) (D.run E ω) :=
    fun b => by
      rw [Set.univ_inter, prob, D.mask_evLogs_run, LinearIsometryEquiv.norm_map]
  simp only [hb]
  linarith [prob_nonneg (Set.univ ∩ logsIn (madeLogs e)ᶜ) (D.run E ω)]

/-- **One reprogramming at a revealed set in a game, averaged over the fresh coin of the
request.** -/
theorem avg_abs_sum_acceptWithAt_sub_le [Nonempty X] [Nonempty Req] {q d : ℕ} (bud : D.Budget q) (hyp : RevealedHyp E₀ E₁ e S)
    (θ : Θ) (upd : Θ → Cn → Θ) (ζ : PMF Cn)
    (hpre_ans : ∀ c c' g rs req, rs.length < e →
      E₀.answerAfter (upd θ c, (g, z₀)) rs req = E₀.answerAfter (upd θ c', (g, z₀)) rs req)
    (hpre_orc : ∀ c c' g (rs : List Req), rs.length ≤ e →
      (OracleState.toOracle (E₀.oracleIn (upd θ c, (g, z₀)) rs) : X → Y) =
        OracleState.toOracle (E₀.oracleIn (upd θ c', (g, z₀)) rs))
    (horc : ∀ c (rs : List Req), rs.length ≤ e → Junta.ReadsPointwise fun g =>
      (OracleState.toOracle (E₀.oracleIn (upd θ c, (g, z₀)) rs) : X → Y))
    (hans : ∀ c (rs : List Req) req a, rs.length < e →
      Junta.ofFun (fun g => if E₀.answerAfter (upd θ c, (g, z₀)) rs req = a then 1 else 0) ∈
        Junta.degLE d)
    {ε : ℝ} (hpt : ∀ (rs : List Req) req x, rs.length = e →
      (ζ.toOuterMeasure {c | x ∈ S (upd θ c) rs req}).toReal ≤ ε)
    (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop) :
    ∑ c, (ζ c).toReal * |∑ g, ∑ z, D.acceptWithAt E₁ P (upd θ c, (g, z)) -
        ∑ g, ∑ z, D.acceptWithAt E₀ P (upd θ c, (g, z))| ≤
      (Fintype.card (X → Y₁) : ℝ) ^ 2 *
        (√(ε * (n * q + d * e)) + ε * (n * q + d * e) / 2) := by
  classical
  set N : ℝ := (Fintype.card (X → Y₁) : ℝ) with hN
  set K : ℝ := ε * (n * q + d * e) with hKdef
  have hε : 0 ≤ ε := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨r⟩ := ‹Nonempty Req›
    exact ENNReal.toReal_nonneg.trans (hpt (List.replicate e r) r x (by simp))
  have hK : 0 ≤ K := mul_nonneg hε (by positivity)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  obtain ⟨c₀, -⟩ := ζ.support_nonempty
  set w : Cn → ℝ := fun c => (ζ c).toReal with hw
  have hw0 : ∀ c, 0 ≤ w c := fun c => ENNReal.toReal_nonneg
  have hw1 : ∑ c, w c = 1 := PMF.sum_toReal ζ
  -- The block states before request `e` do not read the coin.
  set γ : Fin m × LogReg Req m × Req → (X → Y₁) → QState (GameReg W n X Y Req A m) :=
    fun b g => D.blockState E₀ e b (upd θ c₀, (g, z₀)) with hγdef
  have hγ : ∀ c b g, D.blockState E₀ e b (upd θ c, (g, z₀)) = γ b g := fun c b g =>
    D.blockState_eq_of_agree E₀ E₀ (fun rs req h => hpre_ans c c₀ g rs req h)
      (fun rs h => hpre_orc c c₀ g rs h) b
  set a : Fin m × LogReg Req m × Req → ℝ := fun b => ∑ g, ‖γ b g‖ ^ 2 with hadef
  set eb : Fin m × LogReg Req m × Req → Cn → ℝ := fun b c =>
    ∑ g, ‖γ b g - avgFam (S (upd θ c) (requests b.2.1) b.2.2) (γ b) g‖ ^ 2 with hebdef
  have ha0 : ∀ b, 0 ≤ a b := fun b => Finset.sum_nonneg fun g _ => sq_nonneg _
  have heb0 : ∀ b c, 0 ≤ eb b c := fun b c => Finset.sum_nonneg fun g _ => sq_nonneg _
  have hper : ∀ c, |∑ g, ∑ z, D.acceptWithAt E₁ P (upd θ c, (g, z)) -
      ∑ g, ∑ z, D.acceptWithAt E₀ P (upd θ c, (g, z))| ≤
      N * ∑ b, (√(a b) * √(eb b c) + eb b c / 2) := fun c => by
    have h := D.abs_sum_acceptWithAt_sub_le hyp (upd θ c) P
    simp only [hγ] at h
    exact h
  have hsumA : ∑ b, a b ≤ N := by
    rw [hadef]
    dsimp only
    rw [Finset.sum_comm]
    calc ∑ g : X → Y₁, ∑ b, ‖γ b g‖ ^ 2 ≤ ∑ _g : X → Y₁, (1 : ℝ) :=
          Finset.sum_le_sum fun g _ => D.sum_norm_blockState_sq_le E₀ e _
      _ = N := by simp [hN]
  -- The coin average of the distances from the averages.
  have hE : ∀ b, ∑ c, w c * eb b c ≤ K * a b := by
    intro b
    by_cases hb : (requests b.2.1).length = e
    · set f : GameReg W n X Y Req A m → QState (X → Y₁) :=
        fun r => Junta.ofFun fun g => γ b g r with hfdef
      have hdeg : ∀ r, f r ∈ Junta.degLE (n * q + d * e) := by
        intro r
        by_cases hr : r ∈ D.evBlock e b
        · have hlen : (requests (splitLogs r).2).length = e := by rw [hr.1]; exact hb
          by_cases hqb : queriesBefore (splitLogs r).2 b.1 ≤ q
          · have h := D.stage_mem_degLE E₀ (fun g => (upd θ c₀, (g, z₀))) (horc c₀) (hans c₀)
              b.1 r hlen.le
            rw [hlen] at h
            have hf : f r = Junta.ofFun fun g => D.stage E₀ (upd θ c₀, (g, z₀)) b.1 r := by
              ext g
              simp [hfdef, hγdef, blockState, mask_apply_of_mem _ hr]
            rw [hf]
            exact Junta.degLE_mono (by gcongr) h
          · have hf : f r = Junta.ofFun fun _ => 0 := by
              ext g
              simp only [hfdef, hγdef, blockState, Junta.ofFun_apply, mask_apply_of_mem _ hr]
              exact Budget.stage_supported D bud E₀ _ b.1.2 r hqb
            rw [hf]
            exact Junta.ofFun_const_mem_degLE 0 _
        · have hf : f r = Junta.ofFun fun _ => 0 := by
            ext g
            simp [hfdef, hγdef, blockState, mask_apply_of_notMem _ hr]
          rw [hf]
          exact Junta.ofFun_const_mem_degLE 0 _
      set T : Cn → Finset X := fun c => S (upd θ c) (requests b.2.1) b.2.2 with hTdef
      set t : GameReg W n X Y Req A m → X → ℝ := fun r x => ‖f r - Junta.avgAt x (f r)‖ ^ 2
        with htdef
      have hpt' : ∀ x, ∑ c, w c * (if x ∈ T c then 1 else 0) ≤ ε := by
        intro x
        have h := hpt (requests b.2.1) b.2.2 x hb
        rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum
          (fun c _ => ne_top_of_le_ne_top (PMF.apply_ne_top ζ c) (Set.indicator_le_self _ _ c))] at h
        refine le_of_eq_of_le (Finset.sum_congr rfl fun c _ => ?_) h
        by_cases hx : x ∈ T c
        · simp [hw, hx, show x ∈ S (upd θ c) (requests b.2.1) b.2.2 from hx]
        · simp [hw, hx, show x ∉ S (upd θ c) (requests b.2.1) b.2.2 from hx]
      have heb : ∀ c, eb b c ≤ ∑ r, ∑ x ∈ T c, t r x := fun c => by
        rw [hebdef]
        dsimp only
        rw [sum_norm_sub_avgFam_sq_eq]
        exact Finset.sum_le_sum fun r _ => Junta.norm_sub_avgOn_sq_le _ _
      have hA : a b = ∑ r, ‖f r‖ ^ 2 := sum_norm_sq_eq_sum_ofFun (γ b)
      calc ∑ c, w c * eb b c ≤ ∑ c, w c * ∑ r, ∑ x ∈ T c, t r x :=
            Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (heb c) (hw0 c)
        _ = ∑ c, ∑ r, ∑ x, t r x * (w c * if x ∈ T c then 1 else 0) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            have hs : ∑ x ∈ T c, w c * t r x = ∑ x, if x ∈ T c then w c * t r x else 0 := by
              rw [Finset.sum_ite_mem, Finset.univ_inter]
            rw [Finset.mul_sum, hs]
            exact Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
        _ = ∑ r, ∑ x, t r x * ∑ c, w c * (if x ∈ T c then 1 else 0) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
        _ ≤ ∑ r, ∑ x, t r x * ε := Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (hpt' x) (sq_nonneg _)
        _ = ε * ∑ r, ∑ x, t r x := by
            simp only [Finset.mul_sum]
            exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => mul_comm _ _
        _ ≤ ε * ∑ r, ((n * q + d * e : ℕ) : ℝ) * ‖f r‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ =>
              Junta.sum_norm_sub_avgAt_sq_le (hdeg r)) hε
        _ = K * a b := by
            rw [hA, hKdef, Finset.mul_sum, Finset.mul_sum]
            push_cast
            exact Finset.sum_congr rfl fun r _ => by ring
    · have h0 : ∀ g, γ b g = 0 := fun g => by
        ext r
        simp [hγdef, blockState, evBlock, hb]
      have hz : ∀ c, eb b c = 0 := fun c => by
        simp [hebdef, h0, avgFam]
      have ha : a b = 0 := by simp [hadef, h0]
      simp [hz, ha]
  have hjensen : ∀ b, ∑ c, w c * √(eb b c) ≤ √(∑ c, w c * eb b c) := fun b =>
    sum_mul_sqrt_le_sqrt_sum _ _ _ (fun c _ => hw0 c) (fun c _ => heb0 b c) hw1
  calc ∑ c, (ζ c).toReal * |∑ g, ∑ z, D.acceptWithAt E₁ P (upd θ c, (g, z)) -
        ∑ g, ∑ z, D.acceptWithAt E₀ P (upd θ c, (g, z))|
      ≤ ∑ c, w c * (N * ∑ b, (√(a b) * √(eb b c) + eb b c / 2)) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hper c) (hw0 c)
    _ = N * ∑ b, (√(a b) * ∑ c, w c * √(eb b c) + (∑ c, w c * eb b c) / 2) := by
        simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
    _ ≤ N * ∑ b, (√(a b) * √(K * a b) + K * a b / 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) hN0
        refine add_le_add (mul_le_mul_of_nonneg_left ((hjensen b).trans
          (Real.sqrt_le_sqrt (hE b))) (Real.sqrt_nonneg _)) ?_
        linarith [hE b]
    _ = N * ((∑ b, a b) * (√K + K / 2)) := by
        rw [Finset.sum_mul]
        refine congrArg _ (Finset.sum_congr rfl fun b _ => ?_)
        rw [Real.sqrt_mul' K (ha0 b)]
        linear_combination (√K) * Real.mul_self_sqrt (ha0 b)
    _ ≤ N * (N * (√K + K / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumA (by positivity)) hN0
    _ = N ^ 2 * (√K + K / 2) := by ring

end Distinguisher

end GordieHowe.Quantum
