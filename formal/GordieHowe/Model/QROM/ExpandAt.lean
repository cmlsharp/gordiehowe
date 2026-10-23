-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.ExpandAdv

@[expose] public section

/-!
# The expansion inserted before a segment of queries

`expandAdv e E k 𝒜` (CMS19 Proposition 8.11, `GordieHowe/Model/QROM/ExpandAdv.lean`) appends the classical
expansion `E` after the last query of `𝒜`, controlled by `𝒜`'s output. `expandAt e E k 𝒜 s κ`
(our construction) inserts it after `𝒜`'s step `s`, before `𝒜`'s query `s + 1`, controlled by a
classical function `κ` of `𝒜`'s work register read at that point. Its steps are `𝒜`'s steps `0, …, s`
on `𝒜`'s registers; `openPerm` (the query register into the stash, query `0` prepared); the `k`
expansion queries with `expPerm` between them; `closePerm` (the last answer recorded, the query
input returned to `default`, the stash swapped back); then `𝒜`'s steps `s + 1, …, t`. Its output
is `𝒜`'s output, the expansion's queries recomputed from `κ` and the answer slots, and the answers.

When `𝒜`'s steps after `s` keep the classes of `κ` (`KeepsClasses`: each commutes with the
projections onto `{κ ∈ T}` on the state of the run it acts on) and `κ` is a function `π` of the
output on the final state, the run of `expandAt` with every classical oracle is `𝒜`'s run with the
expansion's answers written into the answer slots (`hybrid_expAtStep_of_le`, `stage_expandAt`), and
its law is `𝒜`'s with the output expanded by `E` read through `π` (`expandAt_realLaw`): CMS19
Proposition 8.11's quantum half for the inserted expansion.
-/

open GordieHowe.Quantum

namespace GordieHowe.QROM

variable {X Y B C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- An expansion read through a map of its inputs: `E.comapIn π` runs `E` on `π c`. -/
def Expansion.comapIn {C' : Type} (E : Expansion X B C) (π : C' → C) : Expansion X B C' :=
  ⟨fun c ans => E.next (π c) ans⟩

namespace ExpandAt

open ExpandAdv

variable (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {W : Type} (κ : W → C)

/-- Return the query input from the last expansion query (`prevQuery k`) to `default`, controlled
by registers it does not change. -/
def unmovePerm : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) where
  toFun b := (b.1, fun _ => (Equiv.swap (prevQuery e E k (κ b.1.1) b.1.2.2 k) default (b.2 0).1,
    (b.2 0).2))
  invFun b := (b.1, fun _ => (Equiv.swap (prevQuery e E k (κ b.1.1) b.1.2.2 k) default (b.2 0).1,
    (b.2 0).2))
  left_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp only [Equiv.swap_apply_self, Prod.mk.injEq, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]
  right_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp only [Equiv.swap_apply_self, Prod.mk.injEq, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]

/-- **Open the expansion**: the query register into the stash, then (if `k > 0`) query `0`
prepared. -/
def openPerm : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) :=
  (stashPerm k).trans (if 0 < k then movePerm e E k κ 0 else 1)

/-- **Close the expansion**: the last answer recorded, the query input returned to `default`, the
stash swapped back into the query register. -/
def closePerm : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) :=
  (recordPerm k (k - 1)).trans ((unmovePerm e E k κ).trans (stashPerm k))

end ExpandAt

open ExpandAdv ExpandAt

variable {C' : Type}

/-- The unitaries of the expansion inserted after `𝒜`'s step `s`, indexed by `ℕ`: `𝒜`'s unitaries
before `s`; `𝒜`'s unitary `s` and `openPerm` (and `closePerm` when `k = 0`); `expPerm` between
the expansion's queries; `closePerm` after the last; then `𝒜`'s unitaries from `s + 1` on. -/
noncomputable def expAtStep (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C') (s : ℕ) (κ : 𝒜.W → C) (i : ℕ) :
    QState (ExpBasis (X := X) (Y := Y) k 𝒜.W) ≃ₗᵢ[ℂ] QState (ExpBasis (X := X) (Y := Y) k 𝒜.W) :=
  if i < s then lift k ((𝒜.toOracleAlg ∅).stepAt () i)
  else if i = s then (lift k ((𝒜.toOracleAlg ∅).stepAt () s)).trans
    (permOp (if k = 0 then (openPerm e E k κ).trans (closePerm e E k κ) else openPerm e E k κ))
  else if i < s + k then permOp (expPerm e E k κ (i - s))
  else if i = s + k then permOp (closePerm e E k κ)
  else lift k ((𝒜.toOracleAlg ∅).stepAt () (i - k))

/-- **The expansion inserted before a segment of queries** (our construction; module docstring):
the `(t + k)`-query algorithm that runs `𝒜` up to its step `s`, the classical `k`-query expansion
`E` on the input `κ w` read from the work register, and the rest of `𝒜`. Its output is `𝒜`'s
output with the expansion's queries recomputed from `κ` and the answer slots, and the answers
read through `e`.

Running time: that of `𝒜`, plus `k` classical queries whose inputs the expansion `E` computes from
`κ w` and the earlier answers; polynomial when `𝒜`, `κ` and `E` are. This running time is argued
here, not proved in Lean. -/
noncomputable def expandAt (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C') (s : ℕ) (κ : 𝒜.W → C) :
    QueryAlg X Y (t + k) (BaseGame.Tuple X B C' k) where
  W := ExpansionRegister (X := X) (Y := Y) k 𝒜.W
  init := ExpandAdv.embed k 𝒜.init
  norm_init := by rw [norm_embed, 𝒜.norm_init]
  step i := expAtStep e E k 𝒜 s κ i
  out b := ⟨fun j => queryAt e E k (κ b.1) b.2.2 j, fun j => e (b.2.2 j), 𝒜.out b.1⟩

namespace ExpandAt

variable (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {W : Type} (κ : W → C)

/-- **The classical block of the inserted expansion** against the oracle `H`: `openPerm`, then the
`k` queries with `expPerm` between them and `closePerm` after the last. -/
def blockRun (H : X → Y) : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) :=
  if k = 0 then (openPerm e E k κ).trans (closePerm e E k κ)
  else (expRun e E k κ H (k - 1)).trans ((queryPerm H).trans (closePerm e E k κ))

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- **The classical block writes the expansion's answers**: from `𝒜`'s basis state `(w, q)` with
fresh registers it returns `(w, q)` with the stash `(default, 0)` and the answers of the
expansion against `H` on the input `κ w` in the answer slots. -/
theorem blockRun_apply (H : X → Y) (w : W) (q : Fin 1 → X × Y) :
    blockRun e E k κ H ((registerSplit k W).symm ((w, q), fresh k)) =
      (registerSplit k W).symm ((w, q), ((default, 0), ansUpTo e E k H (κ w) k)) := by
  have hq : (fun _ : Fin 1 => q 0) = q := funext fun i => by rw [Subsingleton.elim i 0]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [blockRun, if_true, openPerm, closePerm, Equiv.trans_apply, lt_irrefl, if_false]
    simp [registerSplit, fresh, stashPerm, recordPerm, unmovePerm, prevQuery, ansUpTo, hq]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hrun := expRun_apply e E (k' + 1) κ H w q k' (by omega)
    simp only [blockRun, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Equiv.trans_apply,
      hrun, queryPerm_apply, closePerm, recordPerm, dif_pos (Nat.lt_succ_self k')]
    have h0 : ansUpTo e E (k' + 1) H (κ w) k' ⟨k', Nat.lt_succ_self k'⟩ = 0 :=
      ansUpTo_apply_of_le e E (k' + 1) H (κ w) k' _ le_rfl
    have hup : ansUpTo e E (k' + 1) H (κ w) (k' + 1) =
        Function.update (ansUpTo e E (k' + 1) H (κ w) k') ⟨k', Nat.lt_succ_self k'⟩
          (H (queryAt e E (k' + 1) (κ w) (ansUpTo e E (k' + 1) H (κ w) k') k')) := by
      rw [ansUpTo, dif_pos (Nat.lt_succ_self k')]
    have hqa : queryAt e E (k' + 1) (κ w) (ansUpTo e E (k' + 1) H (κ w) (k' + 1)) k' =
        queryAt e E (k' + 1) (κ w) (ansUpTo e E (k' + 1) H (κ w) k') k' :=
      queryAt_ansUpTo e E (k' + 1) H (κ w) (Nat.le_succ k')
    have hslot : ansUpTo e E (k' + 1) H (κ w) (k' + 1) ⟨k', Nat.lt_succ_self k'⟩ =
        H (queryAt e E (k' + 1) (κ w) (ansUpTo e E (k' + 1) H (κ w) k') k') := by
      rw [hup, Function.update_self]
    simp only [addAnsPerm, subAnsPerm, unmovePerm, stashPerm, Equiv.coe_fn_mk, h0, zero_add,
      prevQuery, ← hup, hqa, Equiv.swap_apply_left, registerSplit, Equiv.coe_fn_symm_mk, hq]
    rw [hslot, sub_self]

end ExpandAt

namespace ExpandAt

variable (k : ℕ) {W : Type} [Fintype W]

/-- A state of `𝒜`'s registers with the stash and the answer slots in the basis state `r`. -/
noncomputable def embedAt (r : (X × Y) × (Fin k → Y)) (v : QState (QueryReg W 1 X Y)) :
    QState (ExpBasis (X := X) (Y := Y) k W) :=
  relabel (registerSplit k W).symm (tensorKet v r)

omit [Inhabited X] [AddCommGroup Y] in
theorem embedAt_apply (r : (X × Y) × (Fin k → Y)) (v : QState (QueryReg W 1 X Y))
    (b : ExpBasis (X := X) (Y := Y) k W) :
    embedAt k r v b = if (registerSplit k W b).2 = r then v (registerSplit k W b).1 else 0 := by
  rw [embedAt, relabel_apply, Equiv.symm_symm, tensorKet_apply]
  split_ifs <;> simp

theorem embed_eq_embedAt (v : QState (QueryReg W 1 X Y)) : ExpandAdv.embed k v = embedAt k (fresh k) v :=
  rfl

/-- **A state with the answers `a w` written**: on each class of the work register with the same
answers `α`, `𝒜`'s state with the stash `(default, 0)` and the answer slots `α`. -/
noncomputable def embedAns (a : W → Fin k → Y) (v : QState (QueryReg W 1 X Y)) :
    QState (ExpBasis (X := X) (Y := Y) k W) :=
  ∑ α : Fin k → Y, embedAt k ((default, 0), α) (mask {r | a r.1 = α} v)

theorem embedAns_apply (a : W → Fin k → Y) (v : QState (QueryReg W 1 X Y))
    (b : ExpBasis (X := X) (Y := Y) k W) :
    embedAns k a v b = if (registerSplit k W b).2 = ((default, 0), a (registerSplit k W b).1.1)
      then v (registerSplit k W b).1 else 0 := by
  rw [embedAns, WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [embedAt_apply, mask_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (a (registerSplit k W b).1.1)]
    · rw [if_pos h]
      simp
    · intro α _ hα
      rw [if_neg (fun h' => hα (by rw [h] at h'; exact (Prod.mk.inj h').2.symm))]
    · simp
  · refine Finset.sum_eq_zero fun α _ => ?_
    split_ifs with h'
    · rw [Set.indicator_of_notMem]
      intro hm
      apply h
      rw [h']
      simp only [Set.mem_setOf_eq] at hm
      rw [hm]
    · rfl

omit [Inhabited X] [AddCommGroup Y] in
theorem lift_embedAt (U : QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y))
    (r : (X × Y) × (Fin k → Y)) (v : QState (QueryReg W 1 X Y)) :
    lift k U (embedAt k r v) = embedAt k r (U v) := by
  simp only [lift, embedAt, LinearIsometryEquiv.trans_apply, relabel_symm]
  congr 1
  rw [← relabel_symm, LinearIsometryEquiv.apply_symm_apply]
  ext ⟨i, r'⟩
  rw [controlled_apply, tensorKet_apply]
  by_cases hr : r' = r
  · subst hr
    simp only [tensorKet_apply, if_true, mul_one]
  · simp only [tensorKet_apply, hr, if_false, mul_zero]
    have : (WithLp.toLp 2 fun i' => (0 : ℂ) : QState (QueryReg W 1 X Y)) = 0 := rfl
    rw [this, map_zero]
    rfl

/-- **`𝒜`'s unitary acts on a state with the answers written** when it keeps the classes of the
answers: `lift U (embedAns a v) = embedAns a (U v)` if `U` commutes with the projection onto each
class `{a w = α}` at `v`. -/
theorem lift_embedAns (U : QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y))
    (a : W → Fin k → Y) {v : QState (QueryReg W 1 X Y)}
    (hU : ∀ α, U (mask {r | a r.1 = α} v) = mask {r | a r.1 = α} (U v)) :
    lift k U (embedAns k a v) = embedAns k a (U v) := by
  rw [embedAns, map_sum, embedAns]
  exact Finset.sum_congr rfl fun α _ => by rw [lift_embedAt, hU]

omit [Inhabited X] in
theorem queryPerm_embedAt (H : X → Y) (r : (X × Y) × (Fin k → Y)) (v : QState (QueryReg W 1 X Y)) :
    permOp (queryPerm H) (embedAt k r v) = embedAt k r (permOp (queryPerm H) v) := by
  ext b
  rfl

theorem queryPerm_embedAns (H : X → Y) (a : W → Fin k → Y) (v : QState (QueryReg W 1 X Y)) :
    permOp (queryPerm H) (embedAns k a v) = embedAns k a (permOp (queryPerm H) v) := by
  ext b
  rw [permOp_apply, embedAns_apply, embedAns_apply, permOp_apply]
  rfl

variable (e : Y ≃ B) (E : Expansion X B C) (κ : W → C)

/-- **The classical block on a state with fresh registers writes the expansion's answers**
(`blockRun_apply`). -/
theorem permOp_blockRun_embed (H : X → Y) (v : QState (QueryReg W 1 X Y)) :
    permOp (blockRun e E k κ H) (ExpandAdv.embed k v) =
      embedAns k (fun w => ansUpTo e E k H (κ w) k) v := by
  set π := blockRun e E k κ H
  set A : W → Fin k → Y := fun w => ansUpTo e E k H (κ w) k
  have hπ : ∀ r : QueryReg W 1 X Y,
      π ((registerSplit k W).symm (r, fresh k)) = (registerSplit k W).symm (r, ((default, 0), A r.1)) :=
    fun r => blockRun_apply e E k κ H r.1 r.2
  ext b
  rw [permOp_apply, embedAns_apply, embed_eq_embedAt, embedAt_apply]
  by_cases hz : (registerSplit k W (π.symm b)).2 = fresh k
  · set r₀ := (registerSplit k W (π.symm b)).1
    have hb : b = (registerSplit k W).symm (r₀, ((default, 0), A r₀.1)) := by
      rw [← hπ, ← hz, Prod.mk.eta, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    have hsplit : registerSplit k W b = (r₀, ((default, 0), A r₀.1)) := by
      rw [hb, Equiv.apply_symm_apply]
    rw [if_pos hz, hsplit, if_pos rfl]
  · rw [if_neg hz]
    split_ifs with h
    · exfalso
      apply hz
      have hb : b = π ((registerSplit k W).symm ((registerSplit k W b).1, fresh k)) := by
        rw [hπ, ← h, Prod.mk.eta, Equiv.symm_apply_apply]
      rw [hb, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · rfl

end ExpandAt

open ExpandAt

/-- **The steps of `𝒜` after its step `s` keep the classes of `κ`** on the runs of `𝒜`: for every
classical oracle `H`, each unitary `j` with `s < j ≤ t` commutes with the projection onto
`{κ ∈ T}`, for every set `T`, at the state of the run it acts on (the run after query `j`). -/
def KeepsClasses {t : ℕ} (𝒜 : QueryAlg X Y t C') (s : ℕ) (κ : 𝒜.W → C) : Prop :=
  ∀ (H : X → Y) (j : ℕ), s < j → j ≤ t → ∀ T : Set C,
    (𝒜.toOracleAlg ∅).stepAt () j (mask {r | κ r.1 ∈ T}
        (permOp (queryPerm H) ((𝒜.toOracleAlg ∅).stage (queryPerm H) () (j - 1)))) =
      mask {r | κ r.1 ∈ T} ((𝒜.toOracleAlg ∅).stepAt () j
        (permOp (queryPerm H) ((𝒜.toOracleAlg ∅).stage (queryPerm H) () (j - 1))))

section Runs

variable (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ} (𝒜 : QueryAlg X Y t C') {s : ℕ}
  (κ : 𝒜.W → C) (H : X → Y)

/-- The answers the inserted expansion writes against `H`. -/
abbrev ansOf : 𝒜.W → Fin k → Y := fun w => ansUpTo e E k H (κ w) k

/-- **The run of the inserted expansion with oracle `H`**: `𝒜`'s run with fresh registers up to
step `s`; after the expansion, `𝒜`'s run with the expansion's answers written. -/
theorem hybrid_expAtStep_of_le (hs : s ≤ t) (hκ : KeepsClasses 𝒜 s κ) :
    ∀ j, s + j ≤ t →
      hybrid (expAtStep e E k 𝒜 s κ) (fun _ => permOp (queryPerm H)) (ExpandAdv.embed k 𝒜.init) (s + k + j) =
        embedAns k (ansOf e E k 𝒜 κ H)
          (hybrid ((𝒜.toOracleAlg ∅).stepAt ()) (fun _ => permOp (queryPerm H)) 𝒜.init (s + j)) := by
  set U := (𝒜.toOracleAlg ∅).stepAt ()
  set UE := expAtStep e E k 𝒜 s κ
  set O : ℕ → QState (QueryReg 𝒜.W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg 𝒜.W 1 X Y) :=
    fun _ => permOp (queryPerm H)
  set OE : ℕ → QState (ExpBasis (X := X) (Y := Y) k 𝒜.W) ≃ₗᵢ[ℂ]
      QState (ExpBasis (X := X) (Y := Y) k 𝒜.W) := fun _ => permOp (queryPerm H)
  -- before the expansion
  have hpre : ∀ i < s, hybrid UE OE (ExpandAdv.embed k 𝒜.init) i = ExpandAdv.embed k (hybrid U O 𝒜.init i) := by
    intro i hi
    induction i with
    | zero =>
      rw [hybrid_zero, hybrid_zero]
      simp only [UE, expAtStep, if_pos hi]
      exact lift_embed k _ _
    | succ i ih =>
      rw [hybrid_succ, hybrid_succ, ih (by omega)]
      simp only [UE, OE, O, expAtStep, if_pos hi, queryPerm_embed]
      exact lift_embed k _ _
  -- after `𝒜`'s step `s`
  have hs0 : hybrid UE OE (ExpandAdv.embed k 𝒜.init) s =
      permOp (if k = 0 then (openPerm e E k κ).trans (closePerm e E k κ) else openPerm e E k κ)
        (ExpandAdv.embed k (hybrid U O 𝒜.init s)) := by
    have hst : UE s = (lift k (U s)).trans
        (permOp (if k = 0 then (openPerm e E k κ).trans (closePerm e E k κ) else openPerm e E k κ)) := by
      simp only [UE, expAtStep, lt_irrefl, if_false, if_true]
      rfl
    cases s with
    | zero =>
      rw [hybrid_zero, hst, LinearIsometryEquiv.trans_apply, lift_embed, hybrid_zero]
    | succ s =>
      rw [hybrid_succ, hpre s (by omega), hst, LinearIsometryEquiv.trans_apply, queryPerm_embed,
        lift_embed, hybrid_succ]
  -- the block
  have hblock : hybrid UE OE (ExpandAdv.embed k 𝒜.init) (s + k) =
      permOp (blockRun e E k κ H) (ExpandAdv.embed k (hybrid U O 𝒜.init s)) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [add_zero, hs0, blockRun, if_pos rfl, if_pos rfl]
    · have hmid : ∀ j < k, hybrid UE OE (ExpandAdv.embed k 𝒜.init) (s + j) =
          permOp (expRun e E k κ H j) (ExpandAdv.embed k (hybrid U O 𝒜.init s)) := by
        intro j hj
        induction j with
        | zero =>
          rw [add_zero, hs0, if_neg (by omega), expRun, expPerm, openPerm, if_pos hk]
        | succ j ih =>
          have hst : UE (s + (j + 1)) = permOp (expPerm e E k κ (j + 1)) := by
            simp only [UE, expAtStep]
            rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
          rw [← add_assoc, hybrid_succ, ih (by omega), add_assoc, hst, expRun, ExpandAdv.permOp_trans,
            ExpandAdv.permOp_trans]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hst : UE (s + k' + 1) = permOp (closePerm e E (k' + 1) κ) := by
        simp only [UE, expAtStep, if_neg (show ¬ s + k' + 1 < s by omega),
          if_neg (show s + k' + 1 ≠ s by omega), if_neg (show ¬ s + k' + 1 < s + (k' + 1) by omega),
          if_pos (show s + k' + 1 = s + (k' + 1) by omega)]
      rw [← add_assoc, hybrid_succ, hmid k' (by omega), hst, blockRun, if_neg (by omega),
        Nat.add_sub_cancel, ExpandAdv.permOp_trans, ExpandAdv.permOp_trans]
  intro j hj
  induction j with
  | zero =>
    rw [add_zero, add_zero, hblock, permOp_blockRun_embed]
  | succ j ih =>
    have hst : UE (s + k + j + 1) = lift k (U (s + j + 1)) := by
      simp only [UE, expAtStep, if_neg (show ¬ s + k + j + 1 < s by omega),
        if_neg (show s + k + j + 1 ≠ s by omega), if_neg (show ¬ s + k + j + 1 < s + k by omega),
        if_neg (show s + k + j + 1 ≠ s + k by omega), show s + k + j + 1 - k = s + j + 1 by omega]
      rfl
    rw [← add_assoc, hybrid_succ, ih (by omega), hst]
    simp only [OE]
    rw [queryPerm_embedAns, lift_embedAns, ← add_assoc, hybrid_succ]
    intro α
    have := hκ H (s + (j + 1)) (by omega) hj {c | ansUpTo e E k H c k = α}
    rw [show s + (j + 1) - 1 = s + j by omega] at this
    exact this

end Runs

/-! ### The law of the inserted expansion -/

section Law

variable (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ} (𝒜 : QueryAlg X Y t C') {s : ℕ}
  (κ : 𝒜.W → C) (H : X → Y)

/-- **The final state of the inserted expansion** with oracle `H`: `𝒜^H` with the expansion's
answers written. -/
theorem expandAt_final (hs : s ≤ t) (hκ : KeepsClasses 𝒜 s κ) :
    (expandAt e E k 𝒜 s κ).final H = embedAns k (ansOf e E k 𝒜 κ H) (𝒜.final H) := by
  have h := hybrid_expAtStep_of_le e E k 𝒜 κ H hs hκ (t - s) (by omega)
  rw [show s + k + (t - s) = t + k by omega, show s + (t - s) = t by omega] at h
  have hf : 𝒜.final H =
      hybrid ((𝒜.toOracleAlg ∅).stepAt ()) (fun _ => permOp (queryPerm H)) 𝒜.init t := rfl
  rw [hf, ← h]
  refine hybrid_congr_le _ _ _ fun i hi => ?_
  exact (expandAt e E k 𝒜 s κ).toOracleAlg ∅ |>.stepAt_of_lt (Nat.lt_succ_of_le hi)

omit [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y] in
theorem ansUpTo_comapIn (π : C' → C) (c : C') :
    ∀ j, ansUpTo e (E.comapIn π) k H c j = ansUpTo e E k H (π c) j
  | 0 => rfl
  | j + 1 => by
    rw [ansUpTo, ansUpTo, ansUpTo_comapIn π c j]
    rfl

/-- The Born law of a state with answers written: the law of `𝒜`'s state, with the answers of the
work register value written beside it. -/
theorem born_embedAns {W : Type} [Fintype W] [DecidableEq W] (a : W → Fin k → Y)
    (v : QState (QueryReg W 1 X Y)) (hv : ‖v‖ = 1) (h : ‖embedAns k a v‖ = 1) :
    born (embedAns k a v) h =
      (born v hv).map fun r => (registerSplit k W).symm (r, ((default, 0), a r.1)) := by
  ext b
  rw [PMF.map_apply, tsum_fintype]
  simp only [born, PMF.ofFintype_apply, embedAns_apply]
  split_ifs with hb
  · rw [Finset.sum_eq_single (registerSplit k W b).1]
    · rw [if_pos]
      rw [← hb, Prod.mk.eta, Equiv.symm_apply_apply]
    · intro r _ hr
      rw [if_neg]
      intro h'
      apply hr
      rw [h', Equiv.apply_symm_apply]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp
    · intro r _
      rw [if_neg]
      intro h'
      apply hb
      rw [h', Equiv.apply_symm_apply]

omit [Inhabited X] [AddCommGroup Y] in
/-- Two maps that agree on the basis states where a unit vector does not vanish push its Born law
forward to the same law. -/
theorem born_map_congr {W : Type} [Fintype W] {β : Type} (v : QState W) (hv : ‖v‖ = 1)
    {f g : W → β} (h : ∀ r, v r ≠ 0 → f r = g r) : (born v hv).map f = (born v hv).map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun r => ?_
  by_cases hr : v r = 0
  · simp [born, hr]
  · rw [h r hr]

/-- **CMS19 Proposition 8.11's quantum half for the inserted expansion**: if `𝒜`'s steps after `s`
keep the classes of `κ` and `κ` is `π` of the output on every final state, the law of the output of
`expandAt e E k 𝒜 s κ` and the oracle is the law of `𝒜`'s output and the oracle with the output
expanded by `E` read through `π` (`Expansion.comapIn`). -/
theorem expandAt_realLaw [Nonempty Y] (π : C' → C) (hs : s ≤ t) (hκ : KeepsClasses 𝒜 s κ)
    (hout : ∀ (H : X → Y) (r : QueryReg 𝒜.W 1 X Y), 𝒜.final H r ≠ 0 → κ r.1 = π (𝒜.out r.1)) :
    (expandAt e E k 𝒜 s κ).realLaw e =
      (𝒜.realLaw e).map fun p => ⟨(E.comapIn π).expand p.oracle p.out, p.oracle⟩ := by
  rw [QueryAlg.realLaw, QueryAlg.realLaw, PMF.map_bind]
  congr 1
  funext H
  rw [PMF.map_comp]
  have hfin := expandAt_final e E k 𝒜 κ H hs hκ
  have hn : ‖embedAns k (ansOf e E k 𝒜 κ H) (𝒜.final H)‖ = 1 := by
    rw [← hfin]
    exact QueryAlg.norm_final _ H
  have hb : born ((expandAt e E k 𝒜 s κ).final H) ((expandAt e E k 𝒜 s κ).norm_final H) =
      (born (𝒜.final H) (𝒜.norm_final H)).map
        fun r => (registerSplit k 𝒜.W).symm (r, ((default, 0), ansOf e E k 𝒜 κ H r.1)) := by
    rw [← born_embedAns k _ _ (𝒜.norm_final H) hn]
    simp only [born, hfin]
    rfl
  rw [QueryAlg.outLaw, QueryAlg.outLaw, hb]
  conv_lhs => erw [PMF.map_comp, PMF.map_comp]
  rw [PMF.map_comp]
  refine born_map_congr (𝒜.final H) (𝒜.norm_final H) fun r hr => ?_
  have hκr := hout H r hr
  simp only [Function.comp_apply, expandAt, registerSplit, Equiv.coe_fn_symm_mk, Expansion.expand,
    Outcome.mk.injEq, and_true]
  congr 1
  · funext i
    simp only [ansOf]
    rw [queries_eq, ansUpTo_comapIn, hκr]
    rfl
  · funext i
    simp only [ansOf]
    rw [queries_eq, ansUpTo_comapIn, hκr, ansUpTo_self e E k H (π (𝒜.out r.1)) i]
    rfl

end Law

/-! ### Masks that read the expansion's registers -/

namespace ExpandAt

variable (k : ℕ) {W : Type} [Fintype W]

/-- **A mask on a state with answers written**: a projection onto the basis states whose work
register `w` and expansion registers `z` satisfy `M w z` acts on each class of the answers as
the projection onto `{M w ((default, 0), α)}`. -/
theorem mask_embedAns (a : W → Fin k → Y) (M : W → (X × Y) × (Fin k → Y) → Prop)
    (v : QState (QueryReg W 1 X Y)) :
    mask {b | M (registerSplit k W b).1.1 (registerSplit k W b).2} (embedAns k a v) =
      ∑ α : Fin k → Y, embedAt k ((default, 0), α)
        (mask {r | a r.1 = α ∧ M r.1 ((default, 0), α)} v) := by
  ext b
  rw [mask_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [embedAt_apply, mask_apply]
  by_cases hM : M (registerSplit k W b).1.1 (registerSplit k W b).2
  · rw [Set.indicator_of_mem (show b ∈ {b | M (registerSplit k W b).1.1 (registerSplit k W b).2}
      from hM), embedAns_apply]
    split_ifs with h
    · rw [Finset.sum_eq_single (a (registerSplit k W b).1.1)]
      · rw [if_pos h, Set.indicator_of_mem]
        exact ⟨rfl, h ▸ hM⟩
      · intro α _ hα
        rw [if_neg (fun h' => hα (by rw [h] at h'; exact (Prod.mk.inj h').2.symm))]
      · simp
    · refine (Finset.sum_eq_zero fun α _ => ?_).symm
      split_ifs with h'
      · rw [Set.indicator_of_notMem]
        rintro ⟨hm, -⟩
        apply h
        rw [h', hm]
      · rfl
  · rw [Set.indicator_of_notMem (show b ∉ {b | M (registerSplit k W b).1.1 (registerSplit k W b).2}
      from hM)]
    refine (Finset.sum_eq_zero fun α _ => ?_).symm
    split_ifs with h'
    · rw [Set.indicator_of_notMem]
      rintro ⟨-, hm⟩
      exact hM (h' ▸ hm)
    · rfl

variable {C : Type} (κ : W → C)

/-- **`𝒜`'s unitary commutes with a mask that reads the control and the expansion's registers**
on a state with the answers of the control written, when it keeps the classes of the control on
that state. -/
theorem lift_mask_embedAns (U : QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y))
    (A : C → Fin k → Y) (M : C → (X × Y) × (Fin k → Y) → Prop) {v : QState (QueryReg W 1 X Y)}
    (hU : ∀ T : Set C, U (mask {r | κ r.1 ∈ T} v) = mask {r | κ r.1 ∈ T} (U v)) :
    lift k U (mask {b | M (κ (registerSplit k W b).1.1) (registerSplit k W b).2}
        (embedAns k (fun w => A (κ w)) v)) =
      mask {b | M (κ (registerSplit k W b).1.1) (registerSplit k W b).2}
        (lift k U (embedAns k (fun w => A (κ w)) v)) := by
  have hcls : ∀ α : Fin k → Y, {r : QueryReg W 1 X Y | A (κ r.1) = α ∧ M (κ r.1) ((default, 0), α)} =
      {r | κ r.1 ∈ {c | A c = α ∧ M c ((default, 0), α)}} := fun α => rfl
  rw [mask_embedAns k _ (fun w z => M (κ w) z), lift_embedAns k U _ fun α => hU {c | A c = α},
    mask_embedAns k _ (fun w z => M (κ w) z), map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [lift_embedAt, hcls, hU]

end ExpandAt

end GordieHowe.QROM
