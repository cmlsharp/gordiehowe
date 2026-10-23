-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Budget

@[expose] public section

/-!
# Query budgets before the last request

A query budget (`Distinguisher.Budget`) charges every query slot of a branch. Zero knowledge after
the last request (the paper's everlasting zero knowledge, Definition 6.2, `def:narg-zk-post`)
charges only the queries a branch makes before its last request, wherever that request falls at run
time, and leaves the queries after it unbounded. A **request budget** of `q` slots
(`Distinguisher.RequestBudget`) states this as an invariant of the run: a branch that requests at a
slot has queried at no more than `q` slots before it. Queries are not capped. Since the bound holds
before every request, it holds before the last one, and a branch whose count exceeds `q` never
requests again.

- `Budget.toRequestBudget`: a budget of `q` query slots is a request budget of `q` slots.
-/

namespace GordieHowe.Quantum

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m)

/-- **A request budget of `q` slots**: a family `inv k c` of sets of workspaces, the workspaces
possible after step `k`, before slot `k`, on a branch that queried at `c` of the slots before `k`,
kept by the steps as in `Budget`, and a set `halted` of workspaces that the steps keep on these
workspaces, such that a branch that requests at slot `k` and has not halted has queried at no more
than `q` slots before it (`capReq`). The queries after the last request of a branch are not charged.
The halted workspaces are those of a dilated adversary whose branch has ended (`KindAlg.dilate`),
which read as requests at every later slot and do not accept (`RequestBudget.PostRejectsHalted`);
for a distinguisher without them, `halted = ∅` (`Budget.toRequestBudget`). -/
structure RequestBudget (q : ℕ) where
  /-- The workspaces possible before slot `k` after `c` query slots. -/
  inv : ℕ → ℕ → Set W
  init : 0 < m → Supported {r : DReg W n X Y Req A | r.workspace ∈ inv 0 0} (D.step 0 D.init)
  step : ∀ (k : ℕ) (hk : k + 1 < m) (c : ℕ) (b : Bool) (v : QState (DReg W n X Y Req A)),
    Supported {r : DReg W n X Y Req A | r.workspace ∈ inv k c ∧ D.kind r.workspace = b} v →
    Supported {r : DReg W n X Y Req A | r.workspace ∈ inv (k + 1) (if b then c else c + 1)}
      (D.step ⟨k + 1, by omega⟩ v)
  /-- The workspaces of the branches that have ended. -/
  halted : Set W
  halted_step : ∀ (k : ℕ) (hk : k + 1 < m + 1) (c : ℕ) (v : QState (DReg W n X Y Req A)),
    Supported {r : DReg W n X Y Req A | r.workspace ∈ inv k c ∧ r.workspace ∈ halted} v →
      Supported {r : DReg W n X Y Req A | r.workspace ∈ inv (k + 1) c ∧ r.workspace ∈ halted}
        (D.step ⟨k + 1, hk⟩ v)
  capReq : ∀ k < m, ∀ c w, w ∈ inv k c → D.kind w = true → w ∉ halted → c ≤ q

variable {D} in
/-- **A final unitary rejects the halted branches** of a request budget: for every oracle it
maps vectors on the halted workspaces possible after the last step to vectors with no weight on
the accepting set. -/
def RequestBudget.PostRejectsHalted {q : ℕ} (rb : D.RequestBudget q)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) : Prop :=
  ∀ (H : X → Y) (c : ℕ) (v : QState (DReg W n X Y Req A)),
    Supported {r : DReg W n X Y Req A | r.workspace ∈ rb.inv m c ∧ r.workspace ∈ rb.halted} v →
      ∀ r ∈ D.accept, post H v r = 0

variable {D}

/-- **A budget is a request budget** of the same number of slots: the workspaces of the budget
on the branches that queried at no more than `q` slots. A branch queries only below the cap
(`Budget.cap`), so its count stays at most `q`. -/
def Budget.toRequestBudget {q : ℕ} (bud : D.Budget q) : D.RequestBudget q where
  inv k c := {w | w ∈ bud.inv k c ∧ c ≤ q}
  init hm := fun r hr => bud.init hm r fun h => hr ⟨h, Nat.zero_le _⟩
  step k hk c b v hv := by
    have hv' : Supported {r : DReg W n X Y Req A |
        r.workspace ∈ bud.inv k c ∧ D.kind r.workspace = b} v :=
      fun r hr => by
        by_contra hne
        refine hr ⟨?_, ?_⟩
        · by_contra h
          exact hne (hv r fun h' => h h'.1.1)
        · by_contra h
          exact hne (hv r fun h' => h h'.2)
    have hstep := bud.step k hk c b v hv'
    cases b
    · by_cases hc : c < q
      · intro r hr
        exact hstep r fun h => hr ⟨h, by simp only [Bool.false_eq_true, ↓reduceIte]; omega⟩
      · have hv0 : v = 0 := by
          ext r
          by_contra hne
          refine hv r (fun h => ?_) |> fun h0 => hne h0
          exact hc (bud.cap k (by omega) c r.workspace h.1.1 h.2)
        intro r _
        rw [hv0, map_zero]
        rfl
    · by_cases hc : c ≤ q
      · intro r hr
        exact hstep r fun h => hr ⟨h, by simpa using hc⟩
      · have hv0 : v = 0 := by
          ext r
          exact hv r fun h => hc h.1.2
        intro r _
        rw [hv0, map_zero]
        rfl
  halted := ∅
  halted_step _ _ _ v hv := by
    have hv0 : v = 0 := by
      ext d
      exact hv d fun h => h.2
    rw [hv0, map_zero]
    intro _ _
    rfl
  capReq _ _ _ _ hw _ _ := hw.2

/-- With no halted workspaces, every final unitary rejects them. -/
theorem Budget.postRejectsHalted_toRequestBudget {q : ℕ} (bud : D.Budget q)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    bud.toRequestBudget.PostRejectsHalted post := fun H c v hv r _ => by
  have hv0 : v = 0 := by
    ext d
    exact hv d fun h => h.2
  rw [hv0, map_zero]
  rfl

end Distinguisher

end GordieHowe.Quantum
