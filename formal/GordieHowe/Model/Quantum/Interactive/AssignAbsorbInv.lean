-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignRelayOuter

@[expose] public section

/-!
# The table held by an absorbed adversary

An adversary with its requests absorbed (`AdaptiveIAlg.absorb`,
`GordieHowe/Model/Quantum/Interactive/Absorb.lean`) stores the main reply of each slot. When each
main reply reveals a table (`rv`), the table of the stored replies in slot order (`storeTab`) is,
on the absorbed adversary's run, after each of its steps, the table `T₁` of the main requests so
far, whenever `T₁` is the tables of the main replies overridden in slot order (`hT`): the
hypotheses `hinv`, `hinvPost` of `AdaptiveIAlg.mgRun_patchTag`.

- `foldUpTo f k`: the tables `f 0, …, f (k - 1)` overridden in order. `foldUpTo_succ`,
  `foldT_map_eq_foldUpTo`, `foldUpTo_congr`.
- `AdaptiveIAlg.storeTab`: the table of the stored replies.
- `AdaptiveIAlg.liftG_absorb_placeStart`: the absorbed adversary's step `k` on a placed state
  (`placeStart`), before slot `k`.
- `AdaptiveIAlg.suppIn_patchInv_absorb`, `AdaptiveIAlg.suppIn_patchInv_absorb_post`: the
  invariants.
- `AssignRelay.tabAfter_eq_foldUpTo`: `chalD`'s table of the assignments in force is the tables
  its replies reveal, overridden in slot order.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Tables of the first slots -/

section FoldUpTo

variable {X Y : Type*} {m : ℕ}

/-- **The tables of the slots below `k`**, overridden in slot order. -/
def foldUpTo (f : Fin m → X → Option Y) (k : ℕ) : X → Option Y :=
  foldT (((List.finRange m).take k).map f)

theorem foldUpTo_zero (f : Fin m → X → Option Y) : foldUpTo f 0 = fun _ => none :=
  rfl

theorem foldUpTo_succ (f : Fin m → X → Option Y) {k : ℕ} (hk : k < m) :
    foldUpTo f (k + 1) = overT (foldUpTo f k) (f ⟨k, hk⟩) := by
  simp only [foldUpTo]
  rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hk), List.getElem_finRange]
  simp [List.map_append, foldT_append_singleton]

theorem foldUpTo_congr {f g : Fin m → X → Option Y} {k : ℕ}
    (h : ∀ i : Fin m, (i : ℕ) < k → f i = g i) :
    foldUpTo f k = foldUpTo g k := by
  simp only [foldUpTo]
  congr 1
  refine List.map_congr_left fun i hi => h i ?_
  have := List.mem_take_iff_getElem.1 hi
  obtain ⟨j, hj, rfl⟩ := this
  simp only [List.getElem_finRange, Fin.coe_cast]
  omega

theorem foldT_append_of_none (l₁ l₂ : List (X → Option Y)) (h : ∀ t ∈ l₂, t = fun _ => none) :
    foldT (l₁ ++ l₂) = foldT l₁ := by
  induction l₂ using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton l t ih =>
    rw [← List.append_assoc, foldT_append_singleton, h t (by simp), overT_none_right,
      ih fun t' ht' => h t' (by simp [ht'])]

/-- **Tables blank from slot `k` on**: the tables of all slots are those of the slots below
`k`. -/
theorem foldT_map_eq_foldUpTo (f : Fin m → X → Option Y) {k : ℕ}
    (h : ∀ i : Fin m, k ≤ (i : ℕ) → f i = fun _ => none) :
    foldT ((List.finRange m).map f) = foldUpTo f k := by
  have hn : ∀ t ∈ ((List.finRange m).drop k).map f, t = fun _ => none := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
    refine h i ?_
    have := List.mem_drop_iff_getElem.1 hi
    obtain ⟨j, hj, rfl⟩ := this
    simp only [List.getElem_finRange, Fin.coe_cast]
    omega
  rw [foldUpTo]
  conv_lhs => rw [← List.take_append_drop k (List.finRange m), List.map_append,
    foldT_append_of_none _ _ hn]

end FoldUpTo

theorem SuppIn.of_embed {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι] {e : κ → ι}
    {S : Set ι} (h : ∀ x, e x ∈ S) (X : Matrix κ κ ℂ) : SuppIn S (embed e X) := by
  intro a b hab
  rcases hab with ha | hb
  · exact embed_apply_of_notMem_left X (fun x hx => ha (by rw [← hx]; exact h x)) b
  · exact embed_apply_of_notMem_right X a (fun x hx => hb (by rw [← hx]; exact h x))

/-! ### The table of the stored replies -/

namespace AdaptiveIAlg

variable {X Y Req Resp O Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req']
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : SideRelay Req Resp Req' Resp')

/-- **The table of the stored main replies** of an absorbed adversary's workspace, in slot order,
each reply read through `rv`. -/
def storeTab (rv : Resp' → X → Option Y) (w : A.AbsW (Resp' := Resp')) : X → Option Y :=
  foldT ((List.finRange A.slots).map fun i => (w.store i).elim (fun _ => none) rv)

variable {Ω' St' : Type} {Q' : ℕ} [OracleState St' X Y] (E' : Env Ω' Req' Resp' X Y Q' St')
  (ω' : Ω') {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St) (ω : Ω)
  [AddGroup Y] [Nonempty X]

/-- **The absorbed adversary's step `k` on a placed state** before slot `k`: the placement after the
main request of slot `k` is written, of the adversary's step and its copy. -/
theorem liftG_absorb_placeStart (k : Fin A.slots) {σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ}
    (hσ : SuppIn (A.toKindAlg.blankFrom k) σ) :
    (A.absorb F).toKindAlg.liftG (slotStep k) (embed (A.placeStart F E' ω' k) σ) =
      embed (A.placeSet F E' ω' k) ((A.toKindAlg.liftG (slotStep k) σ).submatrix
        (A.toKindAlg.copyG k).symm (A.toKindAlg.copyG k).symm) := by
  have hτ : SuppIn (A.toKindAlg.blankFrom k) (A.toKindAlg.liftG (slotStep k) σ) :=
    KindAlg.SuppIn.liftG A.toKindAlg hσ _
  rw [absorb_liftG_apply,
    submatrix_embed_of_forall (fun a => A.gamePerm_afterAt_placeStart F E' ω' k a),
    gameCntStep_placeClean,
    submatrix_embed (π' := A.toKindAlg.copyG k) (S := A.toKindAlg.blankFrom k)
      (fun a ha => A.gamePerm_setAt_placeClean F E' ω' k (ha k le_rfl)) hτ]

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req']
  [OracleState St' X Y] [AddGroup Y] [Nonempty X] in
/-- **The stored table below slot `k`** is the tables of the main replies below `k`. -/
theorem storeTab_storeBelow [OracleState St' X Y] (rv : Resp' → X → Option Y) (k : ℕ)
    (w : A.W) (rq : Req) (rs : Option Resp) (lg : LogReg Req A.slots) :
    A.storeTab rv ⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩ =
      foldUpTo (fun i => (E'.answer ω' (F.logs lg) i).elim (fun _ => none) rv) k := by
  rw [storeTab, foldT_map_eq_foldUpTo (k := k) _ fun i hi => by simp [storeBelow, not_lt.2 hi]]
  exact foldUpTo_congr fun i hi => by simp [storeBelow, hi, mainAns]

variable (rv : Resp' → X → Option Y) (T₁ : List Req' → X → Option Y)
  (hT : ∀ (L : LogReg Req' A.slots) (k : ℕ), k ≤ A.slots →
    T₁ (requestsBefore L k) = foldUpTo (fun i => (E'.answer ω' L i).elim (fun _ => none) rv) k)

include hT in
/-- **The invariant of the absorbed adversary's run before each slot** (the hypothesis `hinv` of
`mgRun_patchTag`): after its step `k`, the table of its stored replies is `T₁` of the main requests
so far. -/
theorem suppIn_patchInv_absorb (hR : F.Relays E ω E' ω' A.slots)
    (hinj : ∀ c, Function.Injective (F.route c)) (k : Fin A.slots) :
    SuppIn ((A.absorb F).patchInv (A.storeTab rv) T₁ k)
      ((A.absorb F).toKindAlg.liftG (slotStep k) ((A.absorb F).toKindAlg.slotsRun E' ω'
        ((List.finRange A.slots).take k) (A.absorb F).toKindAlg.mgInit)) := by
  have hlen : ((List.finRange A.slots).take k).length = k := by simp
  have hl : ((List.finRange A.slots).take k).map Fin.val =
      List.range' 0 ((List.finRange A.slots).take k).length := by
    rw [hlen, List.map_take, List.map_coe_finRange_eq_range, List.take_range, min_eq_left k.2.le,
      List.range_eq_range']
  have hd0 : dephase (A.toKindAlg.logsBelow 0) A.toKindAlg.mgInit = A.toKindAlg.mgInit := by
    have hl : ∀ a b, A.toKindAlg.logsBelow 0 a = A.toKindAlg.logsBelow 0 b := fun a b =>
      funext fun k => by simp [KindAlg.logsBelow]
    ext a b
    simp [dephase, hl a b]
  obtain ⟨h1, h2, -⟩ := A.run_slots_absorb F E' ω' E ω hR hinj _ 0 hl
    A.toKindAlg.suppIn_mgInit hd0
  rw [hlen, Nat.zero_add] at h1 h2
  have h0 : A.placeStart F E' ω' 0 = A.placeClean F E' ω' 0 := by simp [placeStart]
  rw [A.mgInit_absorb F E' ω', ← h0]
  change SuppIn _ ((A.absorb F).toKindAlg.liftG (slotStep k) ((Circuit.concat _).run _ _))
  rw [h1, A.liftG_absorb_placeStart F E' ω' k h2]
  refine SuppIn.of_embed (fun g => ?_) _
  obtain ⟨⟨⟨w, c⟩, rq, rs, lg⟩, qs⟩ := g
  change LogReg Req A.slots at lg
  change A.storeTab rv ⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩ =
    T₁ (requestsBefore (F.logs (Function.update lg k none)) k)
  rw [A.storeTab_storeBelow F E' ω' rv k, ← hT _ k k.2.le]
  exact congrArg T₁ (requestsBefore_congr fun i hi =>
    (A.relayLogs_update_of_lt F lg k none hi).symm)

include hT in
/-- **The invariant of the absorbed adversary's run before each post batch** (the hypothesis
`hinvPost` of `mgRun_patchTag`). -/
theorem suppIn_patchInv_absorb_post (hR : F.Relays E ω E' ω' A.slots)
    (hinj : ∀ c, Function.Injective (F.route c)) (b : Fin A.post) :
    SuppIn ((A.absorb F).patchInv (A.storeTab rv) T₁ A.slots)
      ((A.absorb F).toKindAlg.liftG (postStep b) ((A.absorb F).toKindAlg.postsRun E' ω'
        ((List.finRange A.post).take b) ((A.absorb F).toKindAlg.slotsRun E' ω'
          (List.finRange A.slots) (A.absorb F).toKindAlg.mgInit))) := by
  have hd0 : dephase (A.toKindAlg.logsBelow 0) A.toKindAlg.mgInit = A.toKindAlg.mgInit := by
    have hl : ∀ a b, A.toKindAlg.logsBelow 0 a = A.toKindAlg.logsBelow 0 b := fun a b =>
      funext fun k => by simp [KindAlg.logsBelow]
    ext a b
    simp [dephase, hl a b]
  obtain ⟨h1, -, -⟩ := A.run_slots_absorb F E' ω' E ω hR hinj (List.finRange A.slots) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange])
    A.toKindAlg.suppIn_mgInit hd0
  rw [List.length_finRange, Nat.zero_add] at h1
  have h0 : A.placeStart F E' ω' 0 = A.placeClean F E' ω' 0 := by simp [placeStart]
  have hlb : ((List.finRange A.post).take b).length = b := by simp
  have h2 := A.run_posts_absorb F E' ω' E ω hR ((List.finRange A.post).take b) 0
    (by rw [hlb, List.map_take, List.map_coe_finRange_eq_range, List.take_range,
      min_eq_left b.2.le, List.range_eq_range'])
    ((Circuit.concat ((List.finRange A.slots).map fun k : Fin A.slots =>
      Circuit.kraus (A.toKindAlg.liftG (slotStep k)) (A.toKindAlg.eventCirc E ω k true))).run
        (Equiv.refl _) A.toKindAlg.mgInit)
  rw [hlb] at h2
  simp only [Nat.zero_add] at h2
  rw [A.mgInit_absorb F E' ω', ← h0]
  change SuppIn _ ((A.absorb F).toKindAlg.liftG (postStep b) ((Circuit.concat _).run _
    ((Circuit.concat _).run _ _)))
  rw [h1]
  erw [h2]
  rw [A.liftG_placeStart_of_le F E' ω' (postStep b) (by simp)]
  refine SuppIn.of_embed (fun g => ?_) _
  obtain ⟨⟨⟨w, c⟩, rq, rs, lg⟩, qs⟩ := g
  change LogReg Req A.slots at lg
  change A.storeTab rv ⟨w, rq, rs, lg, A.storeBelow F E' ω' (A.slots + b) lg⟩ =
    T₁ (requestsBefore (F.logs lg) A.slots)
  rw [hT _ A.slots le_rfl, storeTab,
    foldT_map_eq_foldUpTo (k := A.slots) _ fun i hi => absurd i.2 (by omega)]
  exact foldUpTo_congr fun i hi => by
    simp [storeBelow, show (i : ℕ) < A.slots + b by omega, mainAns]

end AdaptiveIAlg

namespace AssignRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C' : Challenger X Y Req' Resp') (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)

/-- **`chalD`'s table of the assignments in force is the tables its replies reveal**, overridden in
slot order (the hypothesis `hT` of `AdaptiveIAlg.suppIn_patchInv_absorb`). -/
theorem tabAfter_eq_foldUpTo (H : X → Y) (c' : C'.Coins) {m : ℕ}
    (L : LogReg (Req × Fin (Q + 1)) m) : ∀ k, k ≤ m →
    G.tabAfter Q H c' (requestsBefore L k) =
      foldUpTo (fun i => ((chalD C' G Q).toPureEnv.answer (H, c') L i).elim (fun _ => none)
        fun x => x.2.1) k
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := tabAfter_eq_foldUpTo H c' L k (by omega)
    rw [requestsBefore_succ_of_lt L hk, foldUpTo_succ _ hk, ← ih]
    rcases hL : L ⟨k, hk⟩ with _ | r
    · simp [Env.answer, hL]
    · simp only [Option.toList_some, Env.answer, hL, Option.elim]
      simp only [tabAfter]
      rw [Env.oracleIn_append_singleton]
      by_cases hq : (requestsBefore L k).length < Q
      · rw [Challenger.update_toPureEnv_of_lt _ _ _ _ hq,
          Challenger.answerAfter_toPureEnv_of_lt _ _ _ _ hq]
        simp only [lastAssign_append, chalD_respond, OracleProg.run_mapOutput, Option.elim,
            recordOf]
      · rw [Challenger.update_toPureEnv_of_le _ _ _ _ (not_lt.1 hq),
          Challenger.answerAfter_toPureEnv_of_le _ _ _ _ (not_lt.1 hq)]
        simp

end AssignRelay

end GordieHowe.Quantum
