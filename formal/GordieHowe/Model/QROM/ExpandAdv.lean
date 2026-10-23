-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.QueryAlg
public import GordieHowe.Model.Quantum.Pure.Game
public import GordieHowe.Model.QROM.Expansion

@[expose] public section

/-!
# The expanded adversary of CMS19 Proposition 8.11

Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum Random Oracle Model" (CMS19, ePrint
2019/834), proof of Proposition 8.11, p. 42:

    Let B be the algorithm that, when given access to an oracle h, runs A^h to obtain π and then
    outputs BCSExpand^h(π). The query complexity of B is t + O(q log ℓ) because A makes t queries
    and BCSExpand makes O(q log ℓ) queries.

and section 8.5.2, p. 43: "B merely extends A with some classical computation that depends on
A's (classical) output."

`expandAdv e E k 𝒜` is `B` for a `t`-query algorithm `𝒜` (`QueryAlg`) with output in `C` and a
classical `k`-query expansion `E` (`Expansion`, `BCSExpand`): a `(t + k)`-query algorithm in the
same model. Its work register is `𝒜`'s work register, a stash for `𝒜`'s query register, and `k`
answer slots (`ExpansionRegister`), initially `(default, 0)` and `0`. It runs `𝒜`'s steps on its own
registers; then, as reversible classical computation (basis permutations):

- `stashPerm` swaps the query register with the stash, so the query register holds
  `(default, 0)`;
- before query `j`, `movePerm j` changes the query input from the previous query to
  `E.next c (answers 0 … j−1)` (`queryAt`), where `c` is `𝒜`'s output read from the work
  register; this is the swap of the two inputs, controlled by registers it does not change;
- after query `j`, `recordPerm j` adds the answer register to answer slot `j` and then subtracts
  slot `j` from the answer register, which returns it to `0`.

The output is read from the work register: `𝒜`'s output `c`, the queries recomputed from `c`
and the answer slots, and the answers read through `e`.

`expand_adversary` proves CMS19 Proposition 8.11's quantum half for this construction: the law
of `B`'s output and the oracle is the law of `𝒜`'s output and the oracle, with the output
expanded (`Expansion.expand`). The proof is composition of runs: after `𝒜`'s steps the state is
`𝒜^h ⊗ |fresh registers⟩`, and every later step is a basis permutation, so the output law is the
pushforward of `𝒜^h`'s along the classical run of the expansion.
-/

open GordieHowe.Quantum

namespace GordieHowe.QROM

variable {X Y B C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

namespace ExpandAdv

variable (e : Y ≃ B) (E : Expansion X B C) (k : ℕ)

/-- Query `j` of the expansion on the input `c` with the answers `a` in the answer slots:
`E.next c` of the first `j` answers, read through `e`. -/
def queryAt (c : C) (a : Fin k → Y) (j : ℕ) : X :=
  E.next c ((List.ofFn fun i => e (a i)).take j)

/-- The query input held before query `j` is prepared: `default` for `j = 0`, else query
`j − 1`. -/
def prevQuery (c : C) (a : Fin k → Y) : ℕ → X
  | 0 => default
  | j + 1 => queryAt e E k c a j

variable (W : Type)

/-- The work register of the expanded adversary: `𝒜`'s work register, the stash for `𝒜`'s query
register, and `k` answer slots. -/
abbrev ExpansionRegister := W × (X × Y) × (Fin k → Y)

/-- The basis of the expanded adversary. -/
abbrev ExpBasis := QueryReg (ExpansionRegister (X := X) (Y := Y) k W) 1 X Y

variable {W}

/-- Swap the query register with the stash. -/
def stashPerm : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) where
  toFun b := ((b.1.1, b.2 0, b.1.2.2), fun _ => b.1.2.1)
  invFun b := ((b.1.1, b.2 0, b.1.2.2), fun _ => b.1.2.1)
  left_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp only [Prod.mk.injEq, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]
  right_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp only [Prod.mk.injEq, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]

variable (o : W → C)

/-- Prepare query `j`: swap the query input between query `j − 1` (or `default`) and query `j`,
computed from the output `o w` and the answer slots, which it does not change. -/
def movePerm (j : ℕ) : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) where
  toFun b := (b.1, fun _ => (Equiv.swap (prevQuery e E k (o b.1.1) b.1.2.2 j)
    (queryAt e E k (o b.1.1) b.1.2.2 j) (b.2 0).1, (b.2 0).2))
  invFun b := (b.1, fun _ => (Equiv.swap (prevQuery e E k (o b.1.1) b.1.2.2 j)
    (queryAt e E k (o b.1.1) b.1.2.2 j) (b.2 0).1, (b.2 0).2))
  left_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp only [Equiv.swap_apply_self, Prod.mk.injEq, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]
  right_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp only [Equiv.swap_apply_self, Prod.mk.injEq, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]

/-- Add the answer register to answer slot `i`. -/
def addAnsPerm (i : Fin k) : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) where
  toFun b := ((b.1.1, b.1.2.1, Function.update b.1.2.2 i (b.1.2.2 i + (b.2 0).2)), b.2)
  invFun b := ((b.1.1, b.1.2.1, Function.update b.1.2.2 i (b.1.2.2 i - (b.2 0).2)), b.2)
  left_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp
  right_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp

/-- Subtract answer slot `i` from the answer register. -/
def subAnsPerm (i : Fin k) : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) where
  toFun b := (b.1, fun _ => ((b.2 0).1, (b.2 0).2 - b.1.2.2 i))
  invFun b := (b.1, fun _ => ((b.2 0).1, (b.2 0).2 + b.1.2.2 i))
  left_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp only [sub_add_cancel, Prod.mk.injEq, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]
  right_inv b := by
    obtain ⟨⟨w, s, a⟩, q⟩ := b
    simp only [add_sub_cancel_right, Prod.mk.injEq, true_and]
    exact funext fun i => by rw [Subsingleton.elim i 0]

/-- Record the answer to query `j` in answer slot `j` and clear the answer register. -/
def recordPerm (j : ℕ) : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W) :=
  if h : j < k then (addAnsPerm k ⟨j, h⟩).trans (subAnsPerm k ⟨j, h⟩) else 1

/-- The classical step after `𝒜`'s last unitary (`j = 0`) and after query `j − 1` (`j ≥ 1`). -/
def expPerm : ℕ → Equiv.Perm (ExpBasis (X := X) (Y := Y) k W)
  | 0 => (stashPerm k).trans (movePerm e E k o 0)
  | j + 1 => (recordPerm k j).trans (movePerm e E k o (j + 1))

variable (W) in
/-- `QueryReg (ExpansionRegister k W) 1 X Y` with `𝒜`'s registers first and the fresh registers second. -/
def registerSplit : ExpBasis (X := X) (Y := Y) k W ≃ QueryReg W 1 X Y × ((X × Y) × (Fin k → Y)) where
  toFun b := ((b.1.1, b.2), b.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The initial content of the fresh registers: stash `(default, 0)`, answer slots `0`. -/
def fresh : (X × Y) × (Fin k → Y) := ((default, 0), 0)

variable [Fintype W] [DecidableEq W]

/-- A state of `𝒜`'s registers with the fresh registers in their initial content. -/
noncomputable def embed (v : QState (QueryReg W 1 X Y)) : QState (ExpBasis (X := X) (Y := Y) k W) :=
  relabel (registerSplit k W).symm (tensorKet v (fresh (X := X) (Y := Y) k))

/-- A unitary of `𝒜`, acting as the identity on the fresh registers. -/
noncomputable def lift (U : QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y)) :
    QState (ExpBasis (X := X) (Y := Y) k W) ≃ₗᵢ[ℂ] QState (ExpBasis (X := X) (Y := Y) k W) :=
  (relabel (registerSplit k W)).trans ((controlled fun _ => U).trans (relabel (registerSplit k W)).symm)

omit [DecidableEq W] in
theorem norm_embed (v : QState (QueryReg W 1 X Y)) : ‖embed k v‖ = ‖v‖ := by
  rw [embed, LinearIsometryEquiv.norm_map, norm_tensorKet]

omit [Fintype W] [DecidableEq W]

/-- The unitaries of the expanded adversary, indexed by `ℕ`: `𝒜`'s unitaries `0, …, t − 1` on
its registers; `𝒜`'s unitary `t` followed by `expPerm 0`; then `expPerm (i − t)`. -/
noncomputable def expStep (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ} {C' : Type}
    (𝒜 : QueryAlg X Y t C') (o : 𝒜.W → C) (i : ℕ) :
    QState (ExpBasis (X := X) (Y := Y) k 𝒜.W) ≃ₗᵢ[ℂ] QState (ExpBasis (X := X) (Y := Y) k 𝒜.W) :=
  if i < t then lift k ((𝒜.toOracleAlg ∅).stepAt () i)
  else if i = t then (lift k ((𝒜.toOracleAlg ∅).stepAt () t)).trans (permOp (expPerm e E k o 0))
  else permOp (expPerm e E k o (i - t))

end ExpandAdv

open ExpandAdv

/-- **The expanded adversary** of CMS19 Proposition 8.11 (proof, p. 42): the `(t + k)`-query
algorithm that runs `𝒜` and then the classical `k`-query expansion `E` on its output, and outputs
`BCSExpand^h(π)`: the queries, their answers read through `e`, and `𝒜`'s output.

Running time: that of `𝒜`, then `k` classical queries, each input computed by the expansion `E` from
`𝒜`'s output and the earlier answers; polynomial when `𝒜` and `E` are. This running time is argued
here, not proved in Lean. -/
noncomputable def expandAdv (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C) : QueryAlg X Y (t + k) (BaseGame.Tuple X B C k) where
  W := ExpansionRegister (X := X) (Y := Y) k 𝒜.W
  init := ExpandAdv.embed k 𝒜.init
  norm_init := by rw [norm_embed, 𝒜.norm_init]
  step i := expStep e E k 𝒜 𝒜.out i
  out b := ⟨fun j => queryAt e E k (𝒜.out b.1) b.2.2 j, fun j => e (b.2.2 j), 𝒜.out b.1⟩

namespace ExpandAdv

variable (e : Y ≃ B) (E : Expansion X B C) (k : ℕ)

/-! ### The classical run of the expansion -/

section ClassicalRun

omit [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]

omit [AddCommGroup Y] in
/-- `queryAt` reads only the answer slots before `j`. -/
theorem queryAt_congr (c : C) {a a' : Fin k → Y} {j : ℕ}
    (h : ∀ l : Fin k, l.1 < j → a l = a' l) : queryAt e E k c a j = queryAt e E k c a' j := by
  unfold queryAt
  congr 1
  refine List.ext_getElem (by simp) fun l h1 h2 => ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  simp only [List.length_take, List.length_ofFn, lt_min_iff] at h1
  rw [h ⟨l, h1.2⟩ h1.1]

/-- The answer slots after the first `j` queries against `H`, on the input `c`. -/
def ansUpTo (H : X → Y) (c : C) : ℕ → Fin k → Y
  | 0 => 0
  | j + 1 => if h : j < k then
      Function.update (ansUpTo H c j) ⟨j, h⟩ (H (queryAt e E k c (ansUpTo H c j) j))
    else ansUpTo H c j

theorem ansUpTo_apply_of_le (H : X → Y) (c : C) :
    ∀ (j : ℕ) (i : Fin k), j ≤ i.1 → ansUpTo e E k H c j i = 0
  | 0, _, _ => rfl
  | j + 1, i, hi => by
    rw [ansUpTo]
    split_ifs with h
    · rw [Function.update_of_ne (fun hh => by rw [hh] at hi; simp at hi)]
      exact ansUpTo_apply_of_le H c j i (by omega)
    · exact ansUpTo_apply_of_le H c j i (by omega)

/-- Later queries do not change the earlier answer slots. -/
theorem ansUpTo_apply_of_lt (H : X → Y) (c : C) {i : ℕ} :
    ∀ j, i ≤ j → ∀ l : Fin k, l.1 < i → ansUpTo e E k H c j l = ansUpTo e E k H c i l := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ j hij ih =>
    intro l hl
    rw [ansUpTo]
    split_ifs with h
    · rw [Function.update_of_ne (fun hh => by rw [hh] at hl; simp at hl; omega)]
      exact ih l hl
    · exact ih l hl

theorem queryAt_ansUpTo (H : X → Y) (c : C) {i j : ℕ} (hij : i ≤ j) :
    queryAt e E k c (ansUpTo e E k H c j) i = queryAt e E k c (ansUpTo e E k H c i) i :=
  queryAt_congr e E k c fun l hl => ansUpTo_apply_of_lt e E k H c j hij l hl

/-- After all `k` queries, answer slot `i` holds the oracle's answer to query `i`. -/
theorem ansUpTo_self (H : X → Y) (c : C) (i : Fin k) :
    ansUpTo e E k H c k i = H (queryAt e E k c (ansUpTo e E k H c k) i) := by
  rw [ansUpTo_apply_of_lt e E k H c k (i := i.1 + 1) i.2 i (Nat.lt_succ_self _),
    queryAt_ansUpTo e E k H c i.2.le, ansUpTo, dif_pos i.2, Function.update_self]

/-- The queries of the expansion against `e ∘ H` are the queries read off the final answer
slots. -/
theorem run_eq (H : X → Y) (c : C) :
    ∀ j ≤ k, E.run (e ∘ H) c j =
      List.ofFn fun l : Fin j => queryAt e E k c (ansUpTo e E k H c k) l
  | 0, _ => rfl
  | j + 1, hj => by
    rw [Expansion.run, run_eq H c j (by omega), List.ofFn_succ_last]
    congr 2
    rw [queryAt]
    congr 1
    refine List.ext_getElem (by simp; omega) fun l h1 h2 => ?_
    simp only [List.length_map, List.length_ofFn] at h1
    simp only [List.getElem_map, List.getElem_ofFn, List.getElem_take, Function.comp_apply]
    rw [← ansUpTo_self e E k H c ⟨l, by omega⟩]

theorem queries_eq (H : X → Y) (c : C) (i : Fin k) :
    E.queries (e ∘ H) c i = queryAt e E k c (ansUpTo e E k H c k) i := by
  simp only [Expansion.queries, run_eq e E k H c k le_rfl, List.getElem_ofFn]

end ClassicalRun

variable {W : Type} (o : W → C)

/-- The classical steps of the expansion with the oracle steps between them: `expRun H j` is
`expPerm 0`, then `j` times an oracle step and the next classical step. -/
def expRun (H : X → Y) : ℕ → Equiv.Perm (ExpBasis (X := X) (Y := Y) k W)
  | 0 => expPerm e E k o 0
  | j + 1 => (expRun H j).trans ((queryPerm H).trans (expPerm e E k o (j + 1)))

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- **The classical run of the expansion**: from `𝒜`'s basis state `(w, q)` with fresh
registers, after `j ≤ k` queries the work register holds `w`, `𝒜`'s query register in the
stash and the first `j` answers, and the query register holds query `j` with answer `0`. -/
theorem expRun_apply (H : X → Y) (w : W) (q : Fin 1 → X × Y) :
    ∀ j ≤ k, expRun e E k o H j ((registerSplit k W).symm ((w, q), fresh k)) =
      ((w, q 0, ansUpTo e E k H (o w) j),
        fun _ => (queryAt e E k (o w) (ansUpTo e E k H (o w) j) j, 0))
  | 0, _ => by
    simp [expRun, expPerm, registerSplit, fresh, stashPerm, movePerm, prevQuery, ansUpTo]
  | j + 1, hj => by
    have ih := expRun_apply H w q j (by omega)
    have hjk : j < k := by omega
    rw [expRun, Equiv.trans_apply, ih, Equiv.trans_apply, queryPerm_apply, expPerm,
      Equiv.trans_apply, recordPerm, dif_pos hjk]
    have h0 : ansUpTo e E k H (o w) j ⟨j, hjk⟩ = 0 := ansUpTo_apply_of_le e E k H (o w) j _ le_rfl
    have hup : ansUpTo e E k H (o w) (j + 1) = Function.update (ansUpTo e E k H (o w) j) ⟨j, hjk⟩
        (H (queryAt e E k (o w) (ansUpTo e E k H (o w) j) j)) := by
      rw [ansUpTo, dif_pos hjk]
    have hq : queryAt e E k (o w) (ansUpTo e E k H (o w) (j + 1)) j =
        queryAt e E k (o w) (ansUpTo e E k H (o w) j) j :=
      queryAt_ansUpTo e E k H (o w) (Nat.le_succ j)
    simp only [addAnsPerm, subAnsPerm, movePerm, Equiv.coe_trans, Equiv.coe_fn_mk,
      Function.comp_apply, h0, zero_add, Function.update_self, sub_self, prevQuery]
    rw [← hup, hq, Equiv.swap_apply_left]

/-! ### Composition of runs -/

variable [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
theorem lift_embed (U : QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y))
    (v : QState (QueryReg W 1 X Y)) : lift k U (embed k v) = embed k (U v) := by
  simp only [lift, embed, LinearIsometryEquiv.trans_apply, relabel_symm]
  congr 1
  rw [← relabel_symm, LinearIsometryEquiv.apply_symm_apply]
  ext ⟨i, r⟩
  rw [controlled_apply, tensorKet_apply]
  by_cases hr : r = fresh k
  · subst hr
    simp only [tensorKet_apply, if_true, mul_one]
  · simp only [tensorKet_apply, hr, if_false, mul_zero]
    have : (WithLp.toLp 2 fun i' => (0 : ℂ) : QState (QueryReg W 1 X Y)) = 0 := rfl
    rw [this, map_zero]
    rfl

omit [DecidableEq W] in
theorem queryPerm_embed (H : X → Y) (v : QState (QueryReg W 1 X Y)) :
    permOp (queryPerm H) (embed k v) = embed k (permOp (queryPerm H) v) := by
  ext b
  rfl

omit [DecidableEq X] [Inhabited X] [DecidableEq Y] [AddCommGroup Y] [DecidableEq W] in
theorem permOp_trans (π π' : Equiv.Perm (ExpBasis (X := X) (Y := Y) k W))
    (v : QState (ExpBasis (X := X) (Y := Y) k W)) :
    permOp (π.trans π') v = permOp π' (permOp π v) := by
  ext b
  rfl

/-- Decidable equality on the expansion's basis, assembled from its factors (the default instance
search exceeds its size limit on the concrete registers of the simulation). -/
instance instDecidableEqExpBasis {X Y : Type} [DecidableEq X] [DecidableEq Y] {k : ℕ} {W : Type}
    [DecidableEq W] : DecidableEq (ExpBasis (X := X) (Y := Y) k W) :=
  have : DecidableEq (ExpansionRegister (X := X) (Y := Y) k W) := inferInstance
  inferInstance

/-- The expansion's basis is finite, assembled from its factors (as `instDecidableEqExpBasis`). -/
instance instFintypeExpBasis {X Y : Type} [Fintype X] [Fintype Y] {k : ℕ}
    {W : Type} [Fintype W] : Fintype (ExpBasis (X := X) (Y := Y) k W) :=
  have : Fintype (ExpansionRegister (X := X) (Y := Y) k W) := inferInstance
  inferInstance

end ExpandAdv

/-- The run of the expanded adversary with oracle `H`: before `𝒜`'s last unitary it is `𝒜`'s
run with fresh registers; then the classical run of the expansion. -/
theorem hybrid_expStep (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C) (H : X → Y) :
    hybrid (expStep e E k 𝒜 𝒜.out) (fun _ => permOp (queryPerm H)) (ExpandAdv.embed k 𝒜.init) (t + k) =
      permOp (expRun e E k 𝒜.out H k) (ExpandAdv.embed k (𝒜.final H)) := by
  set U := (𝒜.toOracleAlg ∅).stepAt ()
  have hpre : ∀ i < t, hybrid (expStep e E k 𝒜 𝒜.out) (fun _ => permOp (queryPerm H))
      (ExpandAdv.embed k 𝒜.init) i = ExpandAdv.embed k (hybrid U (fun _ => permOp (queryPerm H)) 𝒜.init i) := by
    intro i hi
    induction i with
    | zero =>
      rw [hybrid_zero, hybrid_zero, expStep, if_pos hi]
      exact lift_embed k _ _
    | succ i ih =>
      rw [hybrid_succ, hybrid_succ, ih (by omega), expStep, if_pos hi, queryPerm_embed]
      exact lift_embed k _ _
  have hlast : hybrid (expStep e E k 𝒜 𝒜.out) (fun _ => permOp (queryPerm H)) (ExpandAdv.embed k 𝒜.init) t =
      permOp (expPerm e E k 𝒜.out 0) (ExpandAdv.embed k (𝒜.final H)) := by
    have hs : expStep e E k 𝒜 𝒜.out t =
        (lift k (U t)).trans (permOp (expPerm e E k 𝒜.out 0)) := by
      rw [expStep, if_neg (lt_irrefl t), if_pos rfl]
    have hf : 𝒜.final H = hybrid U (fun _ => permOp (queryPerm H)) 𝒜.init t := rfl
    cases t with
    | zero =>
      rw [hybrid_zero, hs, LinearIsometryEquiv.trans_apply, lift_embed, hf, hybrid_zero]
    | succ t =>
      rw [hybrid_succ, hpre t (by omega), hs, LinearIsometryEquiv.trans_apply, queryPerm_embed,
        lift_embed, hf, hybrid_succ]
  have hexp : ∀ j ≤ k, hybrid (expStep e E k 𝒜 𝒜.out) (fun _ => permOp (queryPerm H))
      (ExpandAdv.embed k 𝒜.init) (t + j) = permOp (expRun e E k 𝒜.out H j) (ExpandAdv.embed k (𝒜.final H)) := by
    intro j hj
    induction j with
    | zero => exact hlast
    | succ j ih =>
      have hs : expStep e E k 𝒜 𝒜.out (t + (j + 1)) = permOp (expPerm e E k 𝒜.out (j + 1)) := by
        rw [expStep, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
      rw [← add_assoc, hybrid_succ, ih (by omega), add_assoc, hs, expRun, ExpandAdv.permOp_trans,
        ExpandAdv.permOp_trans]
  exact hexp k le_rfl

/-- The final state of the expanded adversary: `𝒜^h` with fresh registers, followed by the
classical run of the expansion. -/
theorem expandAdv_final (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C) (H : X → Y) :
    (expandAdv e E k 𝒜).final H = permOp (expRun e E k 𝒜.out H k) (ExpandAdv.embed k (𝒜.final H)) := by
  rw [← hybrid_expStep]
  refine hybrid_congr_le _ _ _ fun i hi => ?_
  exact (expandAdv e E k 𝒜).toOracleAlg ∅ |>.stepAt_of_lt (Nat.lt_succ_of_le hi)

theorem ExpandAdv.born_embed {W : Type} [Fintype W] [DecidableEq W] (k : ℕ)
    (v : QState (QueryReg W 1 X Y)) (hv : ‖v‖ = 1) (h : ‖embed k v‖ = 1) :
    born (embed k v) h =
      ((born v hv).map fun i => (i, fresh (X := X) (Y := Y) k)).map (registerSplit k W).symm := by
  rw [← born_tensorKet v hv]
  exact born_relabel _ _ _

/-- The expanded adversary's output after the classical run of the expansion from `𝒜`'s basis
state `(w, q)` is `BCSExpand` of `𝒜`'s output `𝒜.out w`. -/
theorem expandAdv_out_expRun (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C) (H : X → Y) (w : 𝒜.W) (q : Fin 1 → X × Y) :
    (expandAdv e E k 𝒜).out (expRun e E k 𝒜.out H k ((registerSplit k 𝒜.W).symm ((w, q), fresh k))).1 =
      E.expand (k := k) (e ∘ H) (𝒜.out w) := by
  rw [expRun_apply e E k 𝒜.out H w q k le_rfl]
  simp only [expandAdv, Expansion.expand, BaseGame.Tuple.mk.injEq, and_true]
  refine ⟨funext fun i => (queries_eq e E k H _ i).symm, funext fun i => ?_⟩
  rw [queries_eq, Function.comp_apply, ← ansUpTo_self e E k H (𝒜.out w) i]

/-- The output law of the expanded adversary with oracle `H`: the output law of `𝒜` with
oracle `H`, expanded against `e ∘ H`. -/
theorem expandAdv_outLaw (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C) (H : X → Y) :
    (expandAdv e E k 𝒜).outLaw H = (𝒜.outLaw H).map fun c => E.expand (k := k) (e ∘ H) c := by
  have hn : ‖ExpandAdv.embed k (𝒜.final H)‖ = 1 := by rw [norm_embed, QueryAlg.norm_final]
  have hb : born ((expandAdv e E k 𝒜).final H) ((expandAdv e E k 𝒜).norm_final H) =
      (((born (𝒜.final H) (𝒜.norm_final H)).map fun i => (i, fresh (X := X) (Y := Y) k)).map
        (registerSplit k 𝒜.W).symm).map (expRun e E k 𝒜.out H k) := by
    rw [← born_embed k _ (𝒜.norm_final H) hn, ← born_permOp _ _ hn]
    ext i
    simp only [born, PMF.ofFintype_apply]
    rw [expandAdv_final]
    rfl
  unfold QueryAlg.outLaw
  rw [hb, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  erw [PMF.map_comp]
  refine congrArg (fun f => PMF.map f (born (𝒜.final H) (𝒜.norm_final H))) (funext ?_)
  rintro ⟨w, q⟩
  exact expandAdv_out_expRun e E k 𝒜 H w q

/-- **CMS19 Proposition 8.11** (p. 42), quantum half: the expanded adversary `expandAdv e E k 𝒜`
outputs `E.expand h π = ⟨a, h ∘ a, π⟩` for the output `π` of `𝒜^h`, jointly with the same uniform
oracle `h` (read through `e`). -/
theorem expand_adversary [Nonempty Y] (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C) :
    (expandAdv e E k 𝒜).realLaw e =
      (𝒜.realLaw e).map fun p => ⟨E.expand p.oracle p.out, p.oracle⟩ := by
  rw [QueryAlg.realLaw, QueryAlg.realLaw, PMF.map_bind]
  congr 1
  funext H
  rw [expandAdv_outLaw, PMF.map_comp, PMF.map_comp]
  rfl

end GordieHowe.QROM
