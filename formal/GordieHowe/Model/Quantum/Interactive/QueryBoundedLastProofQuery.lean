-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.QueryBounded
public import GordieHowe.Model.QROM.SaltedZKProofQuery

@[expose] public section

/-!
# Everlasting zero knowledge against query-bounded adversaries

The paper's everlasting zero knowledge (`def:narg-zk-post`, Definition 6.2) bounds the queries an
adversary makes before its last proof query, whose position is chosen at run time, and leaves the
queries after it unbounded. For a query-bounded adversary (`QueryBoundedAdversary`) this is
`QueryBoundedAdversary.QueriesBeforeLastProofQuery`: on every value of the auxiliary input, every
proof query comes after at most `q` query slots, with `width * q ≤ t`
(`AdaptiveIAlg.RequestsAfterAtMost`). Every adversary satisfies it at its query budget
(`AdaptiveIAlg.requestsAfterAtMost_budget`).

- `AdaptiveIAlg.dilRequestBudget`: the dilated adversary has a request budget
  (`Distinguisher.RequestBudget`), its ended branches halted, and its post phase rejects them.
- `GordieHowe.QROM.EverlastingZeroKnowledge`: the notion over query-bounded adversaries.
- `GordieHowe.QROM.EverlastingZeroKnowledgePure.everlastingZeroKnowledge`: the pure notion gives
  it, by deferred measurement (`AdaptiveIAlg.toReal_compose`).
-/

open Finset Matrix
open scoped BigOperators ENNReal

namespace GordieHowe

namespace Quantum.AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : AdaptiveIAlg X Y Req Resp O)

/-- **Every proof query comes after at most `q` query slots**, in the model's semantics: the adversary
with its query counter (`toKindAlg`) moves no weight from a branch within its budget to a branch
that makes a proof query at a slot after more than `q` query slots. The query slots after the last proof query of a
branch are not charged. -/
def RequestsAfterAtMost (q : ℕ) : Prop :=
  ∀ k : StepIdx A.slots A.post, (k : ℕ) < A.slots →
    ∀ (r : A.R) (y x : DReg A.toKindAlg.W A.width X Y Req Resp), A.wcnt x.workspace ≤ A.budget →
      A.kind y.workspace.1 = true → q < A.wcnt y.workspace → (A.toKindAlg.step k).op r y x = 0

/-- **The budget bounds the query slots before every proof query**: a branch within its budget stays
within it, so it makes a proof query after at most `budget` query slots. -/
theorem requestsAfterAtMost_budget : A.RequestsAfterAtMost A.budget := by
  intro k hk r y x hx hkind hq
  refine A.step_op_eq_zero hk hx r y x rfl fun h => ?_
  rw [hkind, if_pos rfl, add_zero] at h
  omega

variable [Nonempty X] [AddGroup Y] [Nonempty Y] [DecidableEq O]

/-- **The dilated adversary has a request budget of `q` slots** (`Distinguisher.RequestBudget`)
when every proof query comes after at most `q` query slots: the invariant of `dilBudget`, with a
request branch at no more than `q` query slots; the halted branches are those with the halting
flag. -/
def dilRequestBudget {q : ℕ} (hq : A.RequestsAfterAtMost q) (o : O) :
    (A.toKindAlg.dilate o).RequestBudget q where
  inv k c := {w | MixedAlg.Clean (k + 1) w.2.2 ∧
    (w.2.1 = true ∨ (A.wcnt w.1 = c + (if A.kind w.1.1 then 0 else 1) ∧ A.wcnt w.1 ≤ A.budget ∧
      (A.kind w.1.1 = true → A.wcnt w.1 ≤ q)))}
  init hm := by
    have h0 := A.toKindAlg.dilate_init_supported o (P := fun w => A.wcnt w = 0)
      A.suppIn_mgInit_wcnt
    exact A.toKindAlg.uStepD_supported (k := 0) (by omega)
      (P := fun w => A.wcnt w = 0)
      (Q := fun w => A.wcnt w = 0 + (if A.kind w.1 then 0 else 1) ∧ A.wcnt w ≤ A.budget ∧
        (A.kind w.1 = true → A.wcnt w ≤ q))
      (fun r y x hx hy => by
        by_cases h2 : A.wcnt y.workspace = 0 + (if A.kind y.workspace.1 then 0 else 1) ∧
            A.wcnt y.workspace ≤ A.budget
        · have h3 : A.kind y.workspace.1 = true ∧ q < A.wcnt y.workspace := by
            by_contra h'
            exact hy ⟨h2.1, h2.2, fun hk => by
              by_contra hlt
              exact h' ⟨hk, not_le.1 hlt⟩⟩
          exact hq ⟨0, by omega⟩ hm r y x (by rw [hx]; exact Nat.zero_le _) h3.1 h3.2
        · exact A.step_op_eq_zero (k := ⟨0, by omega⟩) hm (Nat.zero_le _) r y x hx h2) h0
  step k hk c b v hv := by
    have hks : k + 1 < A.slots := hk
    set c' := if b then c else c + 1
    have hv' : Supported {d : DReg A.toKindAlg.DW A.width X Y Req Resp |
        MixedAlg.Clean (k + 1) d.workspace.2.2 ∧
          (d.workspace.2.1 = true ∨ (A.wcnt d.workspace.1 = c' ∧ A.wcnt d.workspace.1 ≤ A.budget))} v := by
      refine Supported.mono hv fun d hd => ?_
      obtain ⟨⟨hc, hh⟩, hkind⟩ := hd
      refine ⟨hc, ?_⟩
      rcases hh with h | h
      · exact Or.inl h
      · by_cases hhalt : d.workspace.2.1 = true
        · exact Or.inl hhalt
        · right
          rw [Bool.not_eq_true] at hhalt
          have hb : A.kind d.workspace.1.1 = b := by
            have : (A.kind d.workspace.1.1 || d.workspace.2.1) = b := hkind
            rwa [hhalt, Bool.or_false] at this
          subst hb
          refine ⟨?_, h.2.1⟩
          rw [h.1]
          by_cases hkd : A.kind d.workspace.1.1 = true <;> simp [c', hkd]
    exact A.toKindAlg.uStepD_supported (k := k + 1) (by change k + 1 < A.slots + A.post + 1; omega)
      (P := fun w => A.wcnt w = c' ∧ A.wcnt w ≤ A.budget)
      (Q := fun w => A.wcnt w = c' + (if A.kind w.1 then 0 else 1) ∧ A.wcnt w ≤ A.budget ∧
        (A.kind w.1 = true → A.wcnt w ≤ q))
      (fun r y x hx hy => by
        by_cases h2 : A.wcnt y.workspace = c' + (if A.kind y.workspace.1 then 0 else 1) ∧
            A.wcnt y.workspace ≤ A.budget
        · have h3 : A.kind y.workspace.1 = true ∧ q < A.wcnt y.workspace := by
            by_contra h'
            exact hy ⟨h2.1, h2.2, fun hk => by
              by_contra hlt
              exact h' ⟨hk, not_le.1 hlt⟩⟩
          exact hq ⟨k + 1, by omega⟩ hks r y x hx.2 h3.1 h3.2
        · exact A.step_op_eq_zero (k := ⟨k + 1, by omega⟩) (c := c') hks (hx.1 ▸ hx.2) r y x
            hx.1 h2) hv'
  halted := {w | w.2.1 = true}
  halted_step k hk c v hv := by
    have hv' : Supported {d : DReg A.toKindAlg.DW A.width X Y Req Resp |
        MixedAlg.Clean (k + 1) d.workspace.2.2 ∧ (d.workspace.2.1 = true ∨ False)} v :=
      hv.mono fun d hd => ⟨hd.1.1, Or.inl hd.2⟩
    have h := A.toKindAlg.uStepD_supported (k := k + 1)
      (by change k + 1 < A.slots + A.post + 1; change k + 1 < A.slots + 1 at hk; omega)
      (P := fun _ => False) (Q := fun _ => False) (fun _ _ _ hx _ => hx.elim) hv'
    refine h.mono fun d hd => ?_
    rcases hd.2 with hf | hf
    · exact ⟨⟨hd.1, Or.inl hf⟩, hf⟩
    · exact hf.elim
  capReq k hk c w hw hkind hnh := by
    have hflag : w.2.1 = false := by
      simpa using hnh
    have hk' : (A.kind w.1.1 || w.2.1) = true := hkind
    rw [hflag, Bool.or_false] at hk'
    rcases hw.2 with h | h
    · rw [hflag] at h
      exact absurd h Bool.false_ne_true
    · have := h.2.2 hk'
      rw [h.1, hk', if_pos rfl, add_zero] at this
      exact this

omit [Nonempty X] [Nonempty Y] [DecidableEq O] in
/-- The post phase keeps a halted branch halted, batch by batch. -/
theorem supported_postOpN_halted (H : X → Y) :
    ∀ b ≤ A.toKindAlg.post, ∀ v : QState (DReg A.toKindAlg.DW A.width X Y Req Resp),
      Supported {d | MixedAlg.Clean (A.toKindAlg.slots + 1) d.workspace.2.2 ∧
        d.workspace.2.1 = true} v →
      Supported {d | MixedAlg.Clean (A.toKindAlg.slots + 1 + b) d.workspace.2.2 ∧
        d.workspace.2.1 = true} (A.toKindAlg.postOpN H b v)
  | 0, _, v, hv => hv
  | b + 1, hb, v, hv => by
    have ih := supported_postOpN_halted H b (by omega) v hv
    have hp : Supported {d : DReg A.toKindAlg.DW A.width X Y Req Resp |
        MixedAlg.Clean (A.toKindAlg.slots + 1 + b) d.workspace.2.2 ∧
          (d.workspace.2.1 = true ∨ False)}
        (permOp (queryPerm H) (A.toKindAlg.postOpN H b v)) :=
      ih.permOp fun d hd => ⟨hd.1, Or.inl hd.2⟩
    have h := A.toKindAlg.uStepD_supported (k := A.toKindAlg.slots + 1 + b) (by omega)
      (P := fun _ => False) (Q := fun _ => False) (fun _ _ _ hx _ => hx.elim) hp
    refine (show Supported _ (A.toKindAlg.uStepD (A.toKindAlg.slots + 1 + b)
      (permOp (queryPerm H) (A.toKindAlg.postOpN H b v))) from h).mono fun d hd => ?_
    rcases hd.2 with hf | hf
    · exact ⟨by rw [← add_assoc]; exact hd.1, hf⟩
    · exact hf.elim

omit [Nonempty X] [Nonempty Y] in
/-- **The post phase rejects the halted branches** of `dilRequestBudget`: it keeps them halted,
and the dilated adversary accepts only with the halting flag clear. -/
theorem postRejectsHalted_dilRequestBudget {q : ℕ} (hq : A.RequestsAfterAtMost q) (o : O) :
    (A.dilRequestBudget hq o).PostRejectsHalted A.toKindAlg.postOp := by
  intro H c v hv r hr
  have hv' : Supported {d : DReg A.toKindAlg.DW A.width X Y Req Resp |
      MixedAlg.Clean (A.toKindAlg.slots + 1) d.workspace.2.2 ∧ d.workspace.2.1 = true} v :=
    hv.mono fun d hd => ⟨hd.1.1, hd.2⟩
  have h := A.supported_postOpN_halted H A.toKindAlg.post le_rfl v hv'
  refine h r fun hd => ?_
  have hflag : r.workspace.2.1 = false := hr.1
  rw [hd.2] at hflag
  exact absurd hflag (by decide)

end Quantum.AdaptiveIAlg

namespace Quantum.QueryBoundedAdversary

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {T : ℕ} (𝒜 : QueryBoundedAdversary X Y Req Resp O T)

/-- **At most `t` queries before the last proof query** (the query bound of the paper's
`def:narg-zk-post`): on every value of the auxiliary input there is a number `q` of query slots,
`width * q ≤ t`, after at most which every proof query comes (`AdaptiveIAlg.RequestsAfterAtMost`), on
every branch, wherever its last proof query falls at run time. The queries after the last proof query are
not charged. -/
def QueriesBeforeLastProofQuery (t : ℕ) : Prop :=
  ∀ a, ∃ q, (𝒜.alg a).width * q ≤ t ∧ (𝒜.alg a).RequestsAfterAtMost q

end Quantum.QueryBoundedAdversary

namespace QROM

variable {X Y Stmt Wit Proof Coins SimCoins : Type} (rel : Stmt → Wit → Prop) [DecidableRel rel]
  [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [AddGroup Y]
  [Fintype Stmt] [Fintype Wit] [DecidableEq Stmt] [DecidableEq Wit] [Fintype Proof]
  [DecidableEq Proof] [Nonempty X] [DecidableEq Y] [Fintype Coins] [DecidableEq Coins]
  [Fintype SimCoins] [DecidableEq SimCoins]

/-- **Everlasting zero knowledge against query-bounded adversaries** (Unruh
2017 Definition 6, p. 14, over the paper's `(t, Q)`-adversaries, `def:adversary`, with the query
bound of `def:narg-zk-post`): for all `t` and `Q`, every query-bounded adversary that outputs a bit
and makes at most `t` queries before its last proof query on every branch
(`QueriesBeforeLastProofQuery`), and any number after it, outputs `true` against the real challenger
of `P` and against the simulated challenger of `S`, each answering the first `Q` proof queries, with
probabilities at most `ε t Q` apart. -/
def _root_.GordieHowe.QROM.EverlastingZeroKnowledge (P : NARG.Prover X Y Stmt Wit Proof Coins)
    (S : NARG.Simulator X Y Stmt Proof SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (t Q T : ℕ) (𝒟 : Quantum.QueryBoundedAdversary X Y (ProofQuery Stmt Wit) Proof Bool T),
    𝒟.QueriesBeforeLastProofQuery t →
    GordieHowe.advantage (𝒟.acceptProb (realChallenger rel P Q)).toReal
      (𝒟.acceptProb (simChallenger rel S Q)).toReal ≤ ε t Q

variable {rel}

/-- **Zero knowledge of the pure images against request budgets gives everlasting zero
knowledge against query-bounded adversaries**: by deferred measurement
(`AdaptiveIAlg.toReal_compose`) each adversary, on each value of its auxiliary input, has the
acceptance probabilities of its dilation in the pure game, which has a request budget of `q`
slots with `width * q ≤ t` (`AdaptiveIAlg.dilRequestBudget`) and a post phase that rejects its
halted branches; averaging over the auxiliary input keeps the bound. -/
theorem EverlastingZeroKnowledgePure.everlastingZeroKnowledge
    {P : NARG.Prover X Y Stmt Wit Proof Coins} {S : NARG.Simulator X Y Stmt Proof SimCoins}
    {ε : ℕ → ℕ → ℝ}
    (h : EverlastingZeroKnowledgePure rel P.toFn S.toFn ε) :
    GordieHowe.QROM.EverlastingZeroKnowledge rel P S ε := by
  intro t Q T 𝒟 h𝒟
  refine PMF.abs_toReal_tsum_mul_sub_le 𝒟.aux (fun _ => PMF.toOuterMeasure_apply_le_one _ _)
    (fun _ => PMF.toOuterMeasure_apply_le_one _ _) fun a => ?_
  obtain ⟨q, hq, hreq⟩ := h𝒟 a
  rw [Quantum.AdaptiveIAlg.toReal_compose, Quantum.AdaptiveIAlg.toReal_compose, acceptProb_real, acceptProb_sim]
  exact h t _ _ _ Q q _ _ ((𝒟.alg a).dilRequestBudget hreq true)
    ((𝒟.alg a).postRejectsHalted_dilRequestBudget hreq true) hq

end QROM

end GordieHowe
