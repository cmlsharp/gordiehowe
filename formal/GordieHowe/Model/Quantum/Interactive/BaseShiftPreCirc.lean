-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftPre

@[expose] public section

/-!
# The composition of a kind algorithm whose Kraus maps are read after permutations

For Kraus maps `st` of a kind algorithm `T` that are `T`'s read after permutations `σ k`
(`KrausMap.RightPerm`), the adversary's Kraus maps on the composed registers are read after the
lifted permutations (`KindAlg.rightPerm_advKraus`, `KindAlg.rightPerm_advKraus_liftAnc`), and the
gates of each piece of the composed circuit after its last query are basis permutations
(`Circuit.PermTail`): the pair exchanges and the reprogramming's permutations.

- `Circuit.PermTail.append`, `Circuit.append_nil`.
- `ReprogrammedCircuit.permTail_toCircuit_append`,
  `ReprogrammedCircuit.permTail_toCircuit_concat`.
- `KindAlg.advLift`, `KindAlg.rightPerm_advKraus_liftAnc`, `KindAlg.advTail`,
  `KindAlg.permTail_advQueries`.
- `KindAlg.advTail_adv`, `KindAlg.preTail_adv`, `KindAlg.setAdv1`, `KindAlg.advTail_setAdv1`,
  `KindAlg.preTail_setAdv1`, `KindAlg.preTail_inv_setAdv1`, `KindAlg.advLift_eq_setAdv1`: the tails
  keep and commute with the adversary's workspace and request-response registers.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Permutation tails of compiled circuits -/

namespace Circuit

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The tail of an appended circuit with queries is its own.** -/
theorem PermTail.append {d : Circuit ι} {g : Equiv.Perm ι} (h : PermTail d g)
    (hq : 0 < d.queries) : ∀ c : Circuit ι, PermTail (c ++ d) g
  | Circuit.nil => h
  | Circuit.kraus K c => PermTail.krausQ K (PermTail.append h hq c)
      (by have := queries_append c d; change 0 < (c ++ d).queries; omega)
  | Circuit.query c => PermTail.query (PermTail.append h hq c)

/-- **Appending the empty circuit.** -/
theorem append_nil : ∀ c : Circuit ι, c ++ nil = c
  | nil => rfl
  | kraus K c => by rw [kraus_append, append_nil c]
  | query c => by rw [query_append, append_nil c]

end Circuit

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y]

theorem permTail_toCircuit_append {d : ReprogrammedCircuit V X Y} {g : Equiv.Perm _}
    (h : Circuit.PermTail d.toCircuit g) (hq : 0 < d.queries) (c : ReprogrammedCircuit V X Y) :
    Circuit.PermTail (c ++ d).toCircuit g := by
  rw [toCircuit_append]
  exact h.append (by rw [queries_toCircuit]; exact hq) _

omit [AddGroup Y] in
theorem append_nil' : ∀ c : ReprogrammedCircuit V X Y, c ++ nil = c
  | nil => rfl
  | kraus K c => by rw [kraus_append, append_nil' c]
  | rquery a c => by rw [rquery_append, append_nil' c]

omit [AddGroup Y] in
theorem append_assoc' : ∀ a b c : ReprogrammedCircuit V X Y, a ++ b ++ c = a ++ (b ++ c)
  | nil, _, _ => rfl
  | kraus K a, b, c => by simp only [kraus_append, append_assoc' a b c]
  | rquery q a, b, c => by simp only [rquery_append, append_assoc' a b c]

omit [AddGroup Y] in
theorem concat_append' (l₁ l₂ : List (ReprogrammedCircuit V X Y)) :
    concat (l₁ ++ l₂) = concat l₁ ++ concat l₂ := by
  induction l₁ with
  | nil => rfl
  | cons c l ih => simp only [List.cons_append, concat, ih, append_assoc']

/-- **The tail of a concatenation of circuits with queries is the last one's.** -/
theorem permTail_toCircuit_concat {g : Equiv.Perm _} :
    ∀ (l : List (ReprogrammedCircuit V X Y)) (hne : l ≠ []), (∀ x ∈ l, 0 < x.queries) →
      Circuit.PermTail (l.getLast hne).toCircuit g → Circuit.PermTail (concat l).toCircuit g
  | [x], _, _, h => by
    rw [concat, concat]
    change Circuit.PermTail (x ++ nil).toCircuit g
    rw [toCircuit_append]
    have e : x.toCircuit ++ (nil : ReprogrammedCircuit V X Y).toCircuit = x.toCircuit :=
      Circuit.append_nil _
    rw [e]
    exact h
  | x :: y :: l, _, hq, h => by
    rw [concat]
    refine permTail_toCircuit_append ?_ ?_ x
    · exact permTail_toCircuit_concat (y :: l) (List.cons_ne_nil _ _)
        (fun z hz => hq z (List.mem_cons_of_mem _ hz)) h
    · rw [queries_concat]
      have := hq y (by simp)
      simp only [List.map_cons, List.sum_cons]
      omega

end ReprogrammedCircuit

/-! ### The adversary's gates on the composed registers -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  {ksT : KindShape X Y Req Resp} {T : KindAlg ksT O} (C : Challenger X Y Req Resp)

/-- **A permutation of the adversary's registers on the composed registers with the ancilla.** -/
def advLift (σ : Equiv.Perm (DReg T.W T.width X Y Req Resp)) :
    Equiv.Perm (ReprogrammedQueryReg (T.CW C) X Y) :=
  liftQ ((T.advSplit C).permCongr (σ.prodCongr (Equiv.refl _)))

/-- **The adversary's Kraus maps on the composed registers are read after the lifted
permutation** when its Kraus maps are (`h`). -/
theorem rightPerm_advKraus_liftAnc
    {st : StepIdx T.slots T.post → KrausMap T.R (DReg T.W T.width X Y Req Resp)
      (DReg T.W T.width X Y Req Resp)} (k : StepIdx T.slots T.post)
    {σ : Equiv.Perm (DReg T.W T.width X Y Req Resp)}
    (h : KrausMap.RightPerm σ (st k) (T.step k)) :
    KrausMap.RightPerm (T.advLift C σ) ((T.withStep st).advKraus C k).liftAnc
      (T.advKraus C k).liftAnc :=
  (((h.tensorId _).reindex (T.advSplit C)).tensorId _).reindex _

/-- **The gates after the query of pair `k` of a batch with the assignments `ass`**: the
reprogramming's exchange and addition, then the pair's exchange back. -/
def advTail (ass : T.CW C → List (Assignment X Y)) (k : Fin T.width) :
    Equiv.Perm (ReprogrammedQueryReg (T.CW C) X Y) :=
  (1 * liftQ (T.advSwap C k)) * (reprogAdd ass * reprogSwap ass)

/-- **The tail of the adversary's query batch**: that of its last pair. -/
theorem permTail_advQueries (ass : T.CW C → List (Assignment X Y)) :
    Circuit.PermTail (T.advQueries C ass).toCircuit
      (T.advTail C ass ⟨T.width - 1, by have := T.width_pos; omega⟩) := by
  have hpair : ∀ k : Fin T.width, Circuit.PermTail
      ((ReprogrammedCircuit.kraus (KrausMap.ofPerm (T.advSwap C k))
        (.rquery ass (.kraus (KrausMap.ofPerm (T.advSwap C k)) .nil))).toCircuit)
      (T.advTail C ass k) := fun k => by
    refine Circuit.PermTail.krausQ _ (Circuit.PermTail.krausQ _ (Circuit.PermTail.query ?_)
      (by simp [Circuit.queries])) (by simp [ReprogrammedCircuit.toCircuit, Circuit.queries])
    refine Circuit.PermTail.krausP _ (reprogAdd ass * reprogSwap ass)
      (Circuit.PermTail.krausP _ (liftQ (T.advSwap C k)) Circuit.PermTail.nil rfl fun ρ => ?_)
      rfl fun ρ => ?_
    · rw [liftAnc_ofPerm_apply, KrausMap.ofPerm_apply]
    · rw [KrausMap.comp_apply, KrausMap.ofPerm_apply, KrausMap.ofPerm_apply,
        Circuit.submatrix_perm_mul]
  unfold advQueries
  refine ReprogrammedCircuit.permTail_toCircuit_concat _ (by simp [T.width_pos.ne'])
    (fun x hx => ?_) ?_
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    simp [ReprogrammedCircuit.queries]
  · rw [List.getLast_map]
    have e : (List.finRange T.width).getLast (by simp [T.width_pos.ne']) =
        ⟨T.width - 1, by have := T.width_pos; omega⟩ := by
      rw [List.getLast_eq_getElem]
      simp
    rw [e]
    exact hpair _

/-! ### The composed circuit as pieces, one per Kraus map of the adversary -/

theorem List.map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by simp

/-- **The gates of piece `m` after the adversary's Kraus map `m`**: for a slot, its request
measurement, the challenger's queries, the reply and the adversary's queries; for a post batch,
the adversary's queries; none after the last Kraus map. -/
noncomputable def restN (m : ℕ) : ReprogrammedCircuit (T.CW C) X Y :=
  if h : m < T.slots then .kraus (T.measReq C ⟨m, h⟩) (T.chalQueries C ⟨m, h⟩ ++
    .kraus (KrausMap.ofPerm (T.writeReply C ⟨m, h⟩))
      (T.advQueries C fun v => T.advAss C ⟨m, h⟩ v.chal))
  else if m < T.slots + T.post then T.advQueries C fun v => T.postAss C v.chal
  else .nil

/-- **Piece `m` of the composed circuit**: the adversary's Kraus map `m`, then `restN m`. -/
noncomputable def pieceN (m : ℕ) : ReprogrammedCircuit (T.CW C) X Y :=
  if h : m < T.slots + T.post + 1 then .kraus (T.advKraus C ⟨m, h⟩) (T.restN C m) else .nil

theorem pieceN_slot (j : Fin T.slots) : T.pieceN C j = T.slotCircBoth C j := by
  have h : (j : ℕ) < T.slots + T.post + 1 := by omega
  simp only [pieceN, h, ↓reduceDIte, restN, j.isLt, slotCircBoth]

theorem pieceN_post (b : Fin T.post) : T.pieceN C (T.slots + b) = T.postCirc C b := by
  have h : T.slots + (b : ℕ) < T.slots + T.post + 1 := by omega
  have h1 : ¬ T.slots + (b : ℕ) < T.slots := by omega
  have h2 : T.slots + (b : ℕ) < T.slots + T.post := by omega
  simp only [pieceN, h, ↓reduceDIte, restN, h1, h2, ↓reduceIte, postCirc]

theorem pieceN_last : T.pieceN C (T.slots + T.post) = .kraus (T.advKraus C lastStep) .nil := by
  have h : T.slots + T.post < T.slots + T.post + 1 := by omega
  have h1 : ¬ T.slots + T.post < T.slots := by have := T.width_pos; omega
  simp only [pieceN, h, ↓reduceDIte, restN, h1, ↓reduceIte, lt_irrefl]

/-- **The composed circuit is the concatenation of the pieces.** -/
theorem fullCircBoth_eq_concat : T.fullCircBoth C =
    ReprogrammedCircuit.concat ((List.range (T.slots + T.post + 1)).map (T.pieceN C)) := by
  have h1 : (List.finRange T.slots).map (fun j => T.slotCircBoth C j) =
      (List.range T.slots).map (T.pieceN C) := by
    rw [← List.map_val_finRange, List.map_map]
    exact List.map_congr_left fun j _ => (T.pieceN_slot C j).symm
  have h2 : (List.finRange T.post).map (T.postCirc C) =
      ((List.range T.post).map (T.slots + ·)).map (T.pieceN C) := by
    rw [← List.map_val_finRange, List.map_map, List.map_map]
    exact List.map_congr_left fun b _ => (T.pieceN_post C b).symm
  rw [List.range_succ, List.range_add, List.map_append, List.map_append,
    ReprogrammedCircuit.concat_append', ReprogrammedCircuit.concat_append', ← h1, ← h2]
  simp only [List.map_cons, List.map_nil, ReprogrammedCircuit.concat,
    ReprogrammedCircuit.append_nil', pieceN_last]
  rfl

/-! ### The query intervals of the composition with the Kraus maps read after permutations -/

/-- **The first query interval of piece `m`**: `m · (q + width)` for the slots, then `width` per post
batch. -/
def segStart (m : ℕ) : ℕ :=
  if m ≤ T.slots then m * (C.q + T.width) else T.slots * (C.q + T.width) + (m - T.slots) * T.width

theorem queries_restN {m : ℕ} (hm : m < T.slots + T.post) :
    T.segStart C (m + 1) = T.segStart C m + (T.restN C m).queries := by
  unfold segStart restN
  by_cases h : m < T.slots
  · simp only [h, ↓reduceDIte, ReprogrammedCircuit.queries, ReprogrammedCircuit.queries_append,
      queries_chalQueries, queries_advQueries, show m + 1 ≤ T.slots by omega, show m ≤ T.slots by
      omega, ↓reduceIte]
    ring
  · simp only [h, hm, ↓reduceDIte, ↓reduceIte, queries_advQueries]
    by_cases h3 : m = T.slots
    · subst h3
      simp only [le_refl, ↓reduceIte, show ¬ T.slots + 1 ≤ T.slots by omega]
      simp
    · simp only [show ¬ m + 1 ≤ T.slots by omega, show ¬ m ≤ T.slots by omega, ↓reduceIte]
      rw [show m + 1 - T.slots = (m - T.slots) + 1 by omega, add_mul, one_mul]
      ring

theorem segStart_lt (m : ℕ) : T.segStart C m < T.segStart C (m + 1) := by
  have := T.width_pos
  unfold segStart
  by_cases h : m < T.slots
  · simp only [show m + 1 ≤ T.slots by omega, show m ≤ T.slots by omega, ↓reduceIte]
    nlinarith
  · by_cases h3 : m = T.slots
    · subst h3
      simp only [le_refl, ↓reduceIte, show ¬ T.slots + 1 ≤ T.slots by omega]
      simp only [Nat.add_sub_cancel_left, one_mul]
      omega
    · simp only [show ¬ m + 1 ≤ T.slots by omega, show ¬ m ≤ T.slots by omega, ↓reduceIte]
      rw [show m + 1 - T.slots = (m - T.slots) + 1 by omega, add_mul, one_mul]
      omega

theorem segStart_strictMono : StrictMono (T.segStart C) :=
  strictMono_nat_of_lt_succ (T.segStart_lt C)

/-- **The permutation tail before piece `m`**: that of the adversary's queries of piece `m - 1`
(`advTail` of its last pair, at the slot's or the post batches' assignments); the identity before
the first piece. -/
noncomputable def preTail (m : ℕ) : Equiv.Perm (ReprogrammedQueryReg (T.CW C) X Y) :=
  if h : 0 < m ∧ m ≤ T.slots then
    T.advTail C (fun v => T.advAss C ⟨m - 1, by omega⟩ v.chal)
      ⟨T.width - 1, by have := T.width_pos; omega⟩
  else if 0 < m then
    T.advTail C (fun v => T.postAss C v.chal) ⟨T.width - 1, by have := T.width_pos; omega⟩
  else 1

omit [Nonempty X] in
/-- **The tail of a query batch keeps the adversary's workspace and request-response registers.** -/
theorem advTail_adv (ass : T.CW C → List (Assignment X Y)) (k : Fin T.width)
    (p : ReprogrammedQueryReg (T.CW C) X Y) : (T.advTail C ass k p).1.1.adv.1 = p.1.1.adv.1 := by
  simp only [advTail, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, liftQ_apply, reprogSwap_apply,
    reprogAdd]
  split_ifs <;> rfl

omit [Nonempty X] in
/-- **The tails keep the adversary's workspace and request-response registers.** -/
theorem preTail_adv (m : ℕ) (p : ReprogrammedQueryReg (T.CW C) X Y) :
    (T.preTail C m p).1.1.adv.1 = p.1.1.adv.1 := by
  unfold preTail
  split_ifs
  · exact T.advTail_adv C _ _ p
  · exact T.advTail_adv C _ _ p
  · rfl

/-- **The composed registers with the adversary's workspace and request-response registers
replaced by `w`.** -/
def setAdv1 (p : ReprogrammedQueryReg (T.CW C) X Y) (w : T.W × Req × Option Resp) :
    ReprogrammedQueryReg (T.CW C) X Y :=
  ((⟨(w, p.1.1.adv.2), p.1.1.chal⟩, p.1.2), p.2)

omit [Nonempty X] in
/-- **The tail of a query batch commutes with replacing the adversary's workspace and
request-response registers**, for assignments that read only the challenger's registers. -/
theorem advTail_setAdv1 (ass : T.CW C → List (Assignment X Y))
    (hass : ∀ (v : T.CW C) w, ass ⟨(w, v.adv.2), v.chal⟩ = ass v) (k : Fin T.width)
    (p : ReprogrammedQueryReg (T.CW C) X Y) (w : T.W × Req × Option Resp) :
    T.advTail C ass k (T.setAdv1 C p w) = T.setAdv1 C (T.advTail C ass k p) w := by
  have h1 : ∀ q : ReprogrammedQueryReg (T.CW C) X Y, ass (T.setAdv1 C q w).1.1 = ass q.1.1 :=
    fun q => hass q.1.1 w
  simp only [advTail, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, liftQ_apply, reprogSwap_apply]
  have hc : reprogCond ass (T.setAdv1 C p w) ↔ reprogCond ass p := by
    unfold reprogCond
    rw [h1]
    rfl
  by_cases h : reprogCond ass p
  · rw [if_pos (hc.2 h), if_pos h]
    simp only [reprogAdd, queryPermOf_apply]
    rw [show (swapFlip (T.setAdv1 C p w)).1.1 = (T.setAdv1 C p w).1.1 from rfl, h1]
    rfl
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
    simp only [reprogAdd, queryPermOf_apply]
    rw [h1]
    rfl

omit [Nonempty X] in
/-- **The tails commute with replacing the adversary's workspace and request-response
registers.** -/
theorem preTail_setAdv1 (m : ℕ) (p : ReprogrammedQueryReg (T.CW C) X Y)
    (w : T.W × Req × Option Resp) :
    T.preTail C m (T.setAdv1 C p w) = T.setAdv1 C (T.preTail C m p) w := by
  unfold preTail
  split_ifs
  · exact T.advTail_setAdv1 C _ (fun _ _ => rfl) _ p w
  · exact T.advTail_setAdv1 C _ (fun _ _ => rfl) _ p w
  · rfl

omit [Nonempty X] in
theorem preTail_inv_setAdv1 (m : ℕ) (p : ReprogrammedQueryReg (T.CW C) X Y)
    (w : T.W × Req × Option Resp) :
    (T.preTail C m)⁻¹ (T.setAdv1 C p w) = T.setAdv1 C ((T.preTail C m)⁻¹ p) w := by
  apply (T.preTail C m).injective
  rw [preTail_setAdv1]
  simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]

/-- **A lifted permutation that keeps the query pairs replaces the adversary's workspace and
request-response registers.** -/
theorem advLift_eq_setAdv1 {σ : Equiv.Perm (DReg T.W T.width X Y Req Resp)}
    (hσ : ∀ d, (σ d).2 = d.2) (p : ReprogrammedQueryReg (T.CW C) X Y) :
    T.advLift C σ p = T.setAdv1 C p (σ p.1.1.adv).1 := by
  have h := hσ p.1.1.adv
  simp only [advLift, liftQ_apply, Equiv.permCongr_apply, setAdv1, ancSplit, advSplit,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  rw [← h]

/-- **The gates of piece `m` after its last query are its permutation tail.** -/
theorem permTail_restN {m : ℕ} (hm : m < T.slots + T.post) :
    Circuit.PermTail (T.restN C m).toCircuit (T.preTail C (m + 1)) := by
  unfold restN preTail
  by_cases h : m < T.slots
  · simp only [h, ↓reduceDIte, show 0 < m + 1 ∧ m + 1 ≤ T.slots from ⟨by omega, by omega⟩,
      Nat.add_sub_cancel]
    refine Circuit.PermTail.krausQ _ ?_ ?_
    · refine ReprogrammedCircuit.permTail_toCircuit_append ?_ ?_ _
      · exact Circuit.PermTail.krausQ _ (T.permTail_advQueries C _)
          (by rw [ReprogrammedCircuit.queries_toCircuit, queries_advQueries]; exact T.width_pos)
      · simp only [ReprogrammedCircuit.queries, queries_advQueries]
        exact T.width_pos
    · rw [ReprogrammedCircuit.queries_toCircuit, ReprogrammedCircuit.queries_append]
      simp only [ReprogrammedCircuit.queries, queries_advQueries]
      have := T.width_pos
      omega
  · simp only [h, hm, ↓reduceDIte, ↓reduceIte, show 0 < m + 1 by omega, true_and,
      show ¬ m + 1 ≤ T.slots by omega]
    exact T.permTail_advQueries C _

/-- **The piece whose first query interval starts at `n`**, if any. -/
noncomputable def preStepAt (n : ℕ) : Option (StepIdx T.slots T.post) :=
  if h : ∃ k : StepIdx T.slots T.post, T.segStart C k = n then some (Fin.find _ h) else none

theorem preStepAt_segStart (k : StepIdx T.slots T.post) :
    T.preStepAt C (T.segStart C k) = some k := by
  have h : ∃ k' : StepIdx T.slots T.post, T.segStart C k' = T.segStart C k := ⟨k, rfl⟩
  simp only [preStepAt, h, ↓reduceDIte, Option.some.injEq]
  exact Fin.ext ((T.segStart_strictMono C).injective (Fin.find_spec h))

theorem preStepAt_eq_none {n : ℕ} (h : ∀ k : StepIdx T.slots T.post, T.segStart C k ≠ n) :
    T.preStepAt C n = none := by
  simp only [preStepAt, not_exists.2 h, ↓reduceDIte]

variable (σ : StepIdx T.slots T.post → Equiv.Perm (DReg T.W T.width X Y Req Resp))

/-- **The permutations at the starts of the query intervals**: at the interval of piece `k`, the
lifted permutation `σ k` conjugated by the permutation tail before it; the identity elsewhere. -/
noncomputable def prePerms (n : ℕ) : Equiv.Perm (ReprogrammedQueryReg (T.CW C) X Y) :=
  match T.preStepAt C n with
  | none => 1
  | some k => (T.preTail C k)⁻¹ * T.advLift C (σ k) * T.preTail C k

/-- **The interval permutations of the pieces from `m` on**: the lifted `σ m` at the first
interval, `prePerms` after it. -/
noncomputable def sufPerms (m i : ℕ) : Equiv.Perm (ReprogrammedQueryReg (T.CW C) X Y) :=
  if i = 0 then (if h : m < T.slots + T.post + 1 then T.advLift C (σ ⟨m, h⟩) else 1)
  else T.prePerms C σ (T.segStart C m + i)

theorem prePerms_of_between {m n : ℕ} (h₁ : T.segStart C m < n) (h₂ : n < T.segStart C (m + 1)) :
    T.prePerms C σ n = 1 := by
  have hn : ∀ k : StepIdx T.slots T.post, T.segStart C k ≠ n := fun k hk => by
    rcases Nat.lt_or_ge (k : ℕ) (m + 1) with hlt | hge
    · have := (T.segStart_strictMono C).monotone (Nat.lt_succ_iff.1 hlt)
      omega
    · have := (T.segStart_strictMono C).monotone hge
      omega
  simp only [prePerms, T.preStepAt_eq_none C hn]

theorem prePerms_of_last {n : ℕ} (h : T.segStart C (T.slots + T.post) < n) :
    T.prePerms C σ n = 1 := by
  have hn : ∀ k : StepIdx T.slots T.post, T.segStart C k ≠ n := fun k hk => by
    have := (T.segStart_strictMono C).monotone (show (k : ℕ) ≤ T.slots + T.post by omega)
    omega
  simp only [prePerms, T.preStepAt_eq_none C hn]

theorem prePerms_segStart (k : StepIdx T.slots T.post) :
    T.prePerms C σ (T.segStart C k) = (T.preTail C k)⁻¹ * T.advLift C (σ k) * T.preTail C k := by
  simp only [prePerms, T.preStepAt_segStart C k]

variable {σ}

/-- **The pieces from `m` on, with the Kraus maps read after the permutations, have the query
intervals of the pieces of `T` read after `sufPerms m`.** -/
theorem segPerm_suf
    {st : StepIdx T.slots T.post → KrausMap T.R (DReg T.W T.width X Y Req Resp)
      (DReg T.W T.width X Y Req Resp)}
    (hst : ∀ k, KrausMap.RightPerm (σ k) (st k) (T.step k)) :
    ∀ d m, m + d = T.slots + T.post + 1 → Circuit.SegPerm (T.sufPerms C σ m)
      (ReprogrammedCircuit.concat ((List.range' m d).map ((T.withStep st).pieceN C))).toCircuit
      (ReprogrammedCircuit.concat ((List.range' m d).map (T.pieceN C))).toCircuit
  | 0, m, hm => by
    have e : T.sufPerms C σ m = fun _ => 1 := funext fun i => by
      unfold sufPerms
      rcases i with _ | i
      · simp [show ¬ m < T.slots + T.post + 1 by omega]
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
        refine T.prePerms_of_last C σ ?_
        have := (T.segStart_strictMono C) (show T.slots + T.post < m by omega)
        omega
    rw [e]
    exact Circuit.SegPerm.nil
  | d + 1, m, hm => by
    have hmN : m < T.slots + T.post + 1 := by omega
    have ih := segPerm_suf hst d (m + 1) (by omega)
    rw [List.range'_succ, List.map_cons, List.map_cons, ReprogrammedCircuit.concat,
      ReprogrammedCircuit.concat]
    have hp : (T.withStep st).pieceN C m =
        .kraus ((T.withStep st).advKraus C ⟨m, hmN⟩) (T.restN C m) := by
      simp only [pieceN, hmN, ↓reduceDIte]
      rfl
    have hp' : T.pieceN C m = .kraus (T.advKraus C ⟨m, hmN⟩) (T.restN C m) := by
      simp only [pieceN, hmN, ↓reduceDIte]
    rw [hp, hp', ReprogrammedCircuit.kraus_append, ReprogrammedCircuit.kraus_append]
    simp only [ReprogrammedCircuit.toCircuit]
    rw [ReprogrammedCircuit.toCircuit_append, ReprogrammedCircuit.toCircuit_append]
    have hK : ∀ ρ, ((T.withStep st).advKraus C ⟨m, hmN⟩).liftAnc ρ =
        (T.advKraus C ⟨m, hmN⟩).liftAnc (ρ.submatrix (T.advLift C (σ ⟨m, hmN⟩)).symm
          (T.advLift C (σ ⟨m, hmN⟩)).symm) :=
      (T.rightPerm_advKraus_liftAnc C ⟨m, hmN⟩ (hst ⟨m, hmN⟩)).apply
    by_cases hlast : m < T.slots + T.post
    · have hq := queries_restN C hlast
      have hq0 : 0 < (T.restN C m).queries := by
        have := T.segStart_lt C m
        omega
      have hap := Circuit.SegPerm.append_same (T.permTail_restN C hlast) ih
      rw [ReprogrammedCircuit.queries_toCircuit] at hap
      have h0 : Circuit.prefixPerms (T.restN C m).queries (T.preTail C (m + 1))
          (T.sufPerms C σ (m + 1)) 0 = 1 := by
        simp [Circuit.prefixPerms, hq0]
      have hseg := Circuit.SegPerm.kraus _ _ (T.advLift C (σ ⟨m, hmN⟩)) hap fun ρ => by
        rw [h0, hK]
        rfl
      convert hseg using 1
      funext i
      unfold sufPerms
      rcases i with _ | i
      · simp [hmN]
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Circuit.prefixPerms]
        rcases Nat.lt_trichotomy (i + 1) (T.restN C m).queries with hi | hi | hi
        · simp only [hi, ↓reduceIte]
          exact T.prePerms_of_between C σ (m := m) (by omega) (by omega)
        · have e1 : T.segStart C m + (i + 1) =
              T.segStart C ((⟨m + 1, by omega⟩ : StepIdx T.slots T.post) : ℕ) := by
            simp only
            omega
          rw [e1, prePerms_segStart]
          simp [hi, show m + 1 < T.slots + T.post + 1 by omega]
        · simp only [show ¬ i + 1 < (T.restN C m).queries by omega,
            show i + 1 ≠ (T.restN C m).queries by omega, ↓reduceIte,
            show i + 1 - (T.restN C m).queries ≠ 0 by omega]
          congr 1
          omega
    · have hm' : m = T.slots + T.post := by omega
      have hr : T.restN C m = .nil := by
        simp only [restN, show ¬ m < T.slots by omega, ↓reduceDIte, hlast, ↓reduceIte]
      rw [hr]
      have hap := Circuit.SegPerm.append_same (c := (ReprogrammedCircuit.nil :
        ReprogrammedCircuit (T.CW C) X Y).toCircuit) Circuit.PermTail.nil ih
      have h0 : Circuit.prefixPerms (ReprogrammedCircuit.nil :
          ReprogrammedCircuit (T.CW C) X Y).toCircuit.queries 1 (T.sufPerms C σ (m + 1)) 0 = 1 := by
        simp [Circuit.prefixPerms, sufPerms, Circuit.queries, ReprogrammedCircuit.toCircuit,
          show ¬ m + 1 < T.slots + T.post + 1 by omega]
      have hseg := Circuit.SegPerm.kraus _ _ (T.advLift C (σ ⟨m, hmN⟩)) hap fun ρ => by
        rw [h0, hK]
        rfl
      convert hseg using 1
      funext i
      unfold sufPerms
      rcases i with _ | i
      · simp [hmN]
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Circuit.prefixPerms,
          ReprogrammedCircuit.toCircuit, Circuit.queries, Nat.not_lt_zero, Nat.sub_zero]
        rw [hm'] at *
        rw [T.prePerms_of_last C σ (by have := T.segStart_lt C (T.slots + T.post); omega),
          T.prePerms_of_last C σ (by have := T.segStart_lt C (T.slots + T.post); omega)]

/-- **The composition with the Kraus maps read after the permutations `σ`** (`hst`) has the query
intervals of the composition of `T` read after `prePerms σ`. -/
theorem segPerm_fullCircBoth
    {st : StepIdx T.slots T.post → KrausMap T.R (DReg T.W T.width X Y Req Resp)
      (DReg T.W T.width X Y Req Resp)}
    (hst : ∀ k, KrausMap.RightPerm (σ k) (st k) (T.step k)) :
    Circuit.SegPerm (T.prePerms C σ) ((T.withStep st).fullCircBoth C).toCircuit
      (T.fullCircBoth C).toCircuit := by
  rw [fullCircBoth_eq_concat, fullCircBoth_eq_concat, List.range_eq_range']
  have h := T.segPerm_suf C hst (T.slots + T.post + 1) 0 (by omega)
  convert h using 1
  funext i
  unfold sufPerms
  have hs0 : T.segStart C 0 = 0 := by simp [segStart]
  rcases i with _ | i
  · have e := T.prePerms_segStart C σ (0 : StepIdx T.slots T.post)
    simp only [Fin.val_zero, hs0] at e
    rw [e]
    simp [preTail]
  · simp [hs0]

end KindAlg

end GordieHowe.Quantum
