-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.RevealedGame

@[expose] public section

/-!
# One reprogramming at a revealed set in a game: the bound

Two environments `E₀`, `E₁` of the pure game (`GordieHowe/Model/Quantum/Pure/Game.lean`) on tapes
`(θ, (g, z))`: `g : X → Y₁` is the part of the random oracle that may be reprogrammed (for a split
oracle, the first component of the values on a domain `B`), `z : X → Y₁` are fresh values, and `θ`
is everything else. `E₁` reprograms the oracle at request number `e` on a finite set
`S θ rs req` (which depends on the earlier requests `rs` and the request `req`) to the fresh values
and reveals it; `E₀` does not. `RevealedHyp` states how the two are related:

- before request `e` they agree, and neither reads the fresh values (`pre_ans`, `pre_orc`);
- `E₀` never reads the fresh values (`free_ans`, `free_orc`);
- from request `e` on, `E₁` at `(θ, (g, z))` is `E₀` at `(θ, swapOn S (g, z))`, the tape with the
  values of `g` and `z` on `S` exchanged (`event_ans`, `post_ans`, `post_orc`).

The last condition is the relabelling of the proof: after the reprogramming, the oracle of `E₁` is
`g` with `z` on `S`, which is the oracle of `E₀` at the exchanged tape.

`abs_sum_acceptWithAt_sub_le`: for an event of the distinguisher's output, its logs and the final
oracle in force (`acceptWithAt`), the acceptance probabilities summed over `(g, z)` differ by at
most `|Y₁^X| ∑_b (√(∑_g ‖γ_b g‖²) √(∑_g ‖γ_b g − Π_S γ_b g‖²) + ½ ∑_g ‖γ_b g − Π_S γ_b g‖²)`,
where `b` ranges over the event blocks `(k, lg, req)` (request number `e` made at slot `k`, after
the logs `lg`, with request `req`) and `γ_b g` is the part of the state of `E₀` at the oracle `g`
before slot `k` on the block (`blockState`). The proof splits the acceptance probability by the
slot of request `e` (`acceptWithAt_eq_add_sum`): the parts on the branches that never make it agree
(`prob_notMade_eq`); on a block, the run of `E₁` from slot `k` is the run of `E₀` at the exchanged
tape (`prob_block_E₁`); exchanging the tape back (`sum_setOn_swap`) leaves the one reprogramming of
`GordieHowe/Model/Quantum/O2H/RevealedStep.lean` (`abs_sum_prob_sub_le`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### The hypotheses -/

variable {X Y Y₁ Req A Θ : Type*} {Q : ℕ} {St St' : Type _} [OracleState St X Y]
  [OracleState St' X Y] [DecidableEq X]

/-- **Reprogramming at request `e` on a revealed set, as a relation of two environments** on the
tapes `(θ, (g, z))` (see the module docstring). -/
structure RevealedHyp (E₀ : Env (Θ × ((X → Y₁) × (X → Y₁))) Req A X Y Q St)
    (E₁ : Env (Θ × ((X → Y₁) × (X → Y₁))) Req A X Y Q St') (e : ℕ)
    (S : Θ → List Req → Req → Finset X) : Prop where
  pre_ans : ∀ θ g z z' rs req, rs.length < e →
    E₁.answerAfter (θ, (g, z)) rs req = E₀.answerAfter (θ, (g, z')) rs req
  pre_orc : ∀ θ g z z' (rs : List Req), rs.length ≤ e →
    (OracleState.toOracle (E₁.oracleIn (θ, (g, z)) rs) : X → Y) =
      OracleState.toOracle (E₀.oracleIn (θ, (g, z')) rs)
  free_ans : ∀ θ g z z' rs req, E₀.answerAfter (θ, (g, z)) rs req = E₀.answerAfter (θ, (g, z')) rs req
  free_orc : ∀ θ g z z' (rs : List Req),
    (OracleState.toOracle (E₀.oracleIn (θ, (g, z)) rs) : X → Y) =
      OracleState.toOracle (E₀.oracleIn (θ, (g, z')) rs)
  event_ans : ∀ θ g z rs req, rs.length = e →
    E₁.answerAfter (θ, (g, z)) rs req = E₀.answerAfter (θ, Junta.swapOn (S θ rs req) (g, z)) rs req
  post_ans : ∀ θ g z rs req rs' req', rs.length = e →
    E₁.answerAfter (θ, (g, z)) (rs ++ req :: rs') req' =
      E₀.answerAfter (θ, Junta.swapOn (S θ rs req) (g, z)) (rs ++ req :: rs') req'
  post_orc : ∀ θ g z rs req rs', rs.length = e →
    (OracleState.toOracle (E₁.oracleIn (θ, (g, z)) (rs ++ req :: rs')) : X → Y) =
      OracleState.toOracle (E₀.oracleIn (θ, Junta.swapOn (S θ rs req) (g, z)) (rs ++ req :: rs'))

namespace Distinguisher

variable {W : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Y₁] [DecidableEq Y₁]
  [Nonempty Y₁] [Fintype Req] [Fintype A] [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m)
  {E₀ : Env (Θ × ((X → Y₁) × (X → Y₁))) Req A X Y Q St}
  {E₁ : Env (Θ × ((X → Y₁) × (X → Y₁))) Req A X Y Q St'} {e : ℕ}
  {S : Θ → List Req → Req → Finset X}

/-- The fixed fresh values at which the states of `E₀` are read (it never reads them). -/
noncomputable def z₀ : X → Y₁ := fun _ => Classical.arbitrary Y₁

/-- **The accepting basis states** of an event of the output, the logs and the final oracle in
force. -/
def accSet {Ω' : Type*} {St'' : Type _} [OracleState St'' X Y] (E : Env Ω' Req A X Y Q St'')
    (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop) (ω : Ω') :
    Set (GameReg W n X Y Req A m) :=
  {r | P (splitLogs r).1 (splitLogs r).2 (E.oracle ω (splitLogs r).2)}

omit [DecidableEq X] in
/-- The acceptance probability is the probability of the accepting basis states. -/
theorem acceptWithAt_eq_prob {Ω' : Type*} {St'' : Type _} [OracleState St'' X Y]
    (E : Env Ω' Req A X Y Q St'') (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop)
    (ω : Ω') : D.acceptWithAt E P ω = prob (accSet E P ω) (D.run E ω) := rfl

omit [DecidableEq X] in
/-- **The acceptance probability split by the slot of request `e`.** -/
theorem acceptWithAt_eq_add_sum {Ω' : Type*} {St'' : Type _} [OracleState St'' X Y]
    (E : Env Ω' Req A X Y Q St'') (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop)
    (ω : Ω') (e : ℕ) :
    D.acceptWithAt E P ω = prob (accSet E P ω ∩ logsIn (madeLogs e)ᶜ) (D.run E ω) +
      ∑ b, prob (accSet E P ω) (D.contOp E ω b.1 (D.blockState E e b ω)) := by
  rw [acceptWithAt_eq_prob, prob_eq_add_sum_evLogs e]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [prob_inter_eq_prob_mask, mask_evLogs_run]

omit [DecidableEq X] [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- The probability of a set in a vector masked to `L` is that of its part in `L`. -/
theorem prob_mask_eq_inter (C L : Set (GameReg W n X Y Req A m))
    (x : QState (GameReg W n X Y Req A m)) : prob C (mask L x) = prob (C ∩ L) (mask L x) := by
  rw [prob_inter_eq_prob_mask, mask_mask]

/-- The accepting set of `E₀` on the oracle `h`, on the final logs of the block `b`. -/
def blockAcc (E₀ : Env (Θ × ((X → Y₁) × (X → Y₁))) Req A X Y Q St)
    (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop) (θ : Θ) (e : ℕ)
    (b : Fin m × LogReg Req m × Req) (h : X → Y₁) : Set (GameReg W n X Y Req A m) :=
  accSet E₀ P (θ, (h, z₀)) ∩ logsIn (evLogs e b)

omit [Fintype Y₁] [DecidableEq Y₁] in
/-- **The block term of `E₁` is the block term of `E₀` at the exchanged oracle.** -/
theorem prob_block_E₁ (hyp : RevealedHyp E₀ E₁ e S) (θ : Θ)
    (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop) (b : Fin m × LogReg Req m × Req)
    (g z : X → Y₁) :
    prob (accSet E₁ P (θ, (g, z))) (D.contOp E₁ (θ, (g, z)) b.1 (D.blockState E₁ e b (θ, (g, z)))) =
      prob (blockAcc E₀ P θ e b (Junta.setOn (S θ (requests b.2.1) b.2.2) g z))
        (D.contOp E₀ (θ, (Junta.setOn (S θ (requests b.2.1) b.2.2) g z, z₀)) b.1
          (D.blockState E₀ e b (θ, (g, z₀)))) := by
  classical
  set T := S θ (requests b.2.1) b.2.2
  have hγ : D.blockState E₁ e b (θ, (g, z)) = D.blockState E₀ e b (θ, (g, z₀)) :=
    D.blockState_eq_of_agree E₁ E₀ (fun rs req h => hyp.pre_ans θ g z z₀ rs req h)
      (fun rs h => hyp.pre_orc θ g z z₀ rs h) b
  have hw := D.mask_evLogs_run E₁ (θ, (g, z)) e b
  by_cases hb : (requests b.2.1).length = e
  · have hc : D.contOp E₁ (θ, (g, z)) b.1 (D.blockState E₀ e b (θ, (g, z₀))) =
        D.contOp E₀ (θ, (Junta.setOn T g z, z₀)) b.1 (D.blockState E₀ e b (θ, (g, z₀))) := by
      rw [D.contOp_eq_of_evBlock E₁ E₀ e b (hyp.event_ans θ g z _ _ hb)
        (fun rs' req' => hyp.post_ans θ g z _ _ rs' req' hb) (fun rs' => hyp.post_orc θ g z _ _ rs' hb)
        (v := D.blockState E₀ e b (θ, (g, z₀))) (supported_mask _ _), Junta.swapOn_apply,
        D.contOp_congr E₀ E₀ (fun rs req => hyp.free_ans θ _ _ z₀ rs req)
          (fun rs => hyp.free_orc θ _ _ z₀ rs) b.1]
    rw [← hc, ← hγ, ← hw, prob_mask_eq_inter, hw, hγ, hc, blockAcc]
    congr 1
    ext r
    simp only [accSet, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_logsIn]
    refine and_congr_left fun hr => ?_
    obtain ⟨rs', hrs'⟩ := requests_of_mem_evLogs hr
    rw [Env.oracle, Env.oracle, hrs', hyp.post_orc θ g z _ _ rs' hb, Junta.swapOn_apply,
      hyp.free_orc θ _ _ z₀]
  · have h0 : D.blockState E₀ e b (θ, (g, z₀)) = 0 := by
      ext r
      simp [blockState, evBlock, hb]
    rw [hγ, h0, map_zero, map_zero]
    simp [prob]

omit [Fintype Y₁] [DecidableEq Y₁] in
/-- **The block term of `E₀`** at the fixed fresh values. -/
theorem prob_block_E₀ (hyp : RevealedHyp E₀ E₁ e S) (θ : Θ)
    (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop) (b : Fin m × LogReg Req m × Req)
    (g z : X → Y₁) :
    prob (accSet E₀ P (θ, (g, z))) (D.contOp E₀ (θ, (g, z)) b.1 (D.blockState E₀ e b (θ, (g, z)))) =
      prob (blockAcc E₀ P θ e b g)
        (D.contOp E₀ (θ, (g, z₀)) b.1 (D.blockState E₀ e b (θ, (g, z₀)))) := by
  classical
  have hst : ∀ k, D.stage E₀ (θ, (g, z)) k = D.stage E₀ (θ, (g, z₀)) k :=
    D.stage_congr E₀ E₀ (fun rs req => hyp.free_ans θ g z z₀ rs req)
      (fun rs => hyp.free_orc θ g z z₀ rs)
  have hct := D.contOp_congr E₀ E₀ (fun rs req => hyp.free_ans θ g z z₀ rs req)
    (fun rs => hyp.free_orc θ g z z₀ rs) b.1
  have hacc : accSet E₀ P (θ, (g, z)) = accSet E₀ P (θ, (g, z₀)) := by
    ext r
    simp only [accSet, Set.mem_ofPred_eq, Env.oracle, hyp.free_orc θ g z z₀]
  rw [blockState, hst, ← blockState, hct, hacc, ← D.mask_evLogs_run, prob_mask_eq_inter]
  rfl

omit [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] in
/-- **The parts on the branches that never make request `e` agree.** -/
theorem prob_notMade_eq (hyp : RevealedHyp E₀ E₁ e S) (θ : Θ)
    (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop) (g z : X → Y₁) :
    prob (accSet E₁ P (θ, (g, z)) ∩ logsIn (madeLogs e)ᶜ) (D.run E₁ (θ, (g, z))) =
      prob (accSet E₀ P (θ, (g, z)) ∩ logsIn (madeLogs e)ᶜ) (D.run E₀ (θ, (g, z))) := by
  classical
  have hset : accSet E₁ P (θ, (g, z)) ∩ logsIn (madeLogs e)ᶜ =
      accSet E₀ P (θ, (g, z)) ∩ logsIn (madeLogs e)ᶜ := by
    ext r
    simp only [accSet, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_logsIn, Set.mem_compl_iff,
      madeLogs, Set.mem_ofPred_eq, not_lt]
    refine and_congr_left fun hr => ?_
    rw [Env.oracle, Env.oracle, hyp.pre_orc θ g z z _ hr]
  rw [hset, prob_inter_eq_prob_mask, prob_inter_eq_prob_mask,
    D.mask_run_notMade_eq E₁ E₀ (fun rs req h => hyp.pre_ans θ g z z rs req h)
      (fun rs h => hyp.pre_orc θ g z z rs h)]

omit [DecidableEq Y₁] in
/-- **One reprogramming at a revealed set in a game, at a fixed `θ`.** -/
theorem abs_sum_acceptWithAt_sub_le (hyp : RevealedHyp E₀ E₁ e S) (θ : Θ)
    (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop) :
    |∑ g, ∑ z, D.acceptWithAt E₁ P (θ, (g, z)) - ∑ g, ∑ z, D.acceptWithAt E₀ P (θ, (g, z))| ≤
      Fintype.card (X → Y₁) * ∑ b : Fin m × LogReg Req m × Req,
        (√(∑ g, ‖D.blockState E₀ e b (θ, (g, z₀))‖ ^ 2) *
            √(∑ g, ‖D.blockState E₀ e b (θ, (g, z₀)) -
              avgFam (S θ (requests b.2.1) b.2.2) (fun g => D.blockState E₀ e b (θ, (g, z₀))) g‖ ^ 2) +
          (∑ g, ‖D.blockState E₀ e b (θ, (g, z₀)) -
              avgFam (S θ (requests b.2.1) b.2.2)
                (fun g => D.blockState E₀ e b (θ, (g, z₀))) g‖ ^ 2) / 2) := by
  set N := Fintype.card (X → Y₁)
  have h₁ : ∀ g z, D.acceptWithAt E₁ P (θ, (g, z)) =
      prob (accSet E₁ P (θ, (g, z)) ∩ logsIn (madeLogs e)ᶜ) (D.run E₁ (θ, (g, z))) +
        ∑ b, prob (blockAcc E₀ P θ e b (Junta.setOn (S θ (requests b.2.1) b.2.2) g z))
          (D.contOp E₀ (θ, (Junta.setOn (S θ (requests b.2.1) b.2.2) g z, z₀)) b.1
            (D.blockState E₀ e b (θ, (g, z₀)))) := fun g z => by
    rw [D.acceptWithAt_eq_add_sum E₁ P _ e]
    simp only [D.prob_block_E₁ hyp θ P]
  have h₀ : ∀ g z, D.acceptWithAt E₀ P (θ, (g, z)) =
      prob (accSet E₀ P (θ, (g, z)) ∩ logsIn (madeLogs e)ᶜ) (D.run E₀ (θ, (g, z))) +
        ∑ b, prob (blockAcc E₀ P θ e b g)
          (D.contOp E₀ (θ, (g, z₀)) b.1 (D.blockState E₀ e b (θ, (g, z₀)))) := fun g z => by
    rw [D.acceptWithAt_eq_add_sum E₀ P _ e]
    simp only [D.prob_block_E₀ hyp θ P]
  have hd : ∑ g, ∑ z, D.acceptWithAt E₁ P (θ, (g, z)) - ∑ g, ∑ z, D.acceptWithAt E₀ P (θ, (g, z)) =
      ∑ b : Fin m × LogReg Req m × Req,
        (∑ g, ∑ z, prob (blockAcc E₀ P θ e b (Junta.setOn (S θ (requests b.2.1) b.2.2) g z))
          (D.contOp E₀ (θ, (Junta.setOn (S θ (requests b.2.1) b.2.2) g z, z₀)) b.1
            (D.blockState E₀ e b (θ, (g, z₀)))) -
        ∑ g, ∑ _z : X → Y₁, prob (blockAcc E₀ P θ e b g)
          (D.contOp E₀ (θ, (g, z₀)) b.1 (D.blockState E₀ e b (θ, (g, z₀))))) := by
    simp only [h₁, h₀, D.prob_notMade_eq hyp θ P, ← Finset.sum_sub_distrib, add_sub_add_left_eq_sub]
    rw [Finset.sum_congr rfl fun g _ => Finset.sum_comm, Finset.sum_comm]
  rw [hd, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  set T := S θ (requests b.2.1) b.2.2
  set γ := fun g => D.blockState E₀ e b (θ, (g, z₀))
  set V := fun h => D.contOp E₀ (θ, (h, z₀)) b.1
  set Ab := blockAcc E₀ P θ e b
  have hswap : ∑ g, ∑ z, prob (Ab (Junta.setOn T g z)) (V (Junta.setOn T g z) (γ g)) =
      ∑ h, ∑ z, prob (Ab h) (V h (γ (Junta.setOn T h z))) := by
    rw [← sum_setOn_swap T (fun g z => prob (Ab (Junta.setOn T g z)) (V (Junta.setOn T g z) (γ g)))]
    simp only [Junta.setOn_setOn_left, Junta.setOn_setOn_right, Junta.setOn_self]
  rw [hswap, abs_sub_comm]
  exact abs_sum_prob_sub_le γ V Ab T

end Distinguisher

end GordieHowe.Quantum
