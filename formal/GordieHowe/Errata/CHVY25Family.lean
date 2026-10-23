-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Errata.CHVY25
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Fin.Embedding

@[expose] public section

/-!
# An erratum against CHVY25: a family of instances

The family, in Longfellow's layout with `t = NREQ`:
block `k = BLOCK = NREQ + 1`, `WR = 1` (witness block `[RANDOM[k − 1], WITNESS[1]]`, so the
dot-sum check reads the response at the single node `k − 1 = NREQ`), `DBLOCK = 2k − 1`, and
`n = 2k + 1` opened-candidate columns at the nodes `2k − 1, …, 4k − 1`. The witness row is zero,
the constraint is `W[0] = 1`, and the `IDOT` row is committed as the values of `X^(2k−1)` at the
opened-candidate columns.

For a challenge `α`, the prover answers with a polynomial `p` of degree `≤ 2k − 2` with
`p(k − 1) = α`, of the form `X^(2k−1) − ∏_{q ∈ S} (X − node q)`, which agrees with the `IDOT` row
exactly on `S`:
- if `α = (k − 1)^(2k−1) − ∏_{q ∈ S} (k − 1 − node q)` for a set `S` of `2k − 1` columns, the
  prover uses that `S` (`Entry`, a table of such challenges with the two columns left out of `S`);
- otherwise `S` is a fixed set of `2k − 2` columns times one more linear factor `X − c`, with `c`
  solving `p(k − 1) = α` (`resp`).

`acceptProb_ge` bounds the acceptance from below by
`(g·C(2k − 1, t) + (|F| − g)·C(2k − 2, t))/(|F|·C(n, t))`, where `g` is the number of tabled
challenges, under `Facts` (the node conditions, the product of all node factors, and the table's
entries), which each instance checks by `decide +kernel`. The instances are in
`GordieHowe.Errata.CHVY25FamilyData`.
-/

namespace GordieHowe.Errata.CHVY25.Family

open Finset Polynomial

variable {F : Type} [Field F] {nreq : ℕ}

/-- The number of opened-candidate columns, `n = 2k + 1 = 2·NREQ + 3`. -/
abbrev cols (nreq : ℕ) : ℕ := 2 * nreq + 3

/-- The witness node `NREQ = k − 1`. -/
def wnode (nreq : ℕ) : F := (nreq : F)

/-- `∏_{q ∈ s} (X − node q)` over a set of opened-candidate columns. -/
noncomputable def nodePoly (s : Finset (Fin (cols nreq))) : F[X] :=
  ∏ q ∈ s, (X - C (colNode nreq 1 q))

theorem nodePoly_monic (s : Finset (Fin (cols nreq))) : (nodePoly (F := F) s).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_nodePoly (s : Finset (Fin (cols nreq))) :
    (nodePoly (F := F) s).natDegree = #s := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

theorem eval_nodePoly (s : Finset (Fin (cols nreq))) (x : F) :
    (nodePoly s).eval x = ∏ q ∈ s, (x - colNode nreq 1 q) := by
  simp [nodePoly, eval_prod]

theorem eval_nodePoly_of_mem {s : Finset (Fin (cols nreq))} {q : Fin (cols nreq)} (hq : q ∈ s) :
    (nodePoly s).eval (colNode (F := F) nreq 1 q) = 0 := by
  rw [eval_nodePoly]
  exact prod_eq_zero hq (sub_self _)

/-- The difference of two monic polynomials of the same degree `d` has degree `< d`. -/
theorem degree_sub_lt_of_monic {f g : F[X]} {d : ℕ} (hf : f.Monic) (hg : g.Monic)
    (hfd : f.natDegree = d) (hgd : g.natDegree = d) : (f - g).degree < d := by
  have h := degree_sub_lt_left (p := f) (q := g)
    (by rw [degree_eq_natDegree hf.ne_zero, degree_eq_natDegree hg.ne_zero, hfd, hgd])
    hf.ne_zero (by rw [hf.leadingCoeff, hg.leadingCoeff])
  rwa [degree_eq_natDegree hf.ne_zero, hfd] at h

/-- The tableau: one witness row, zero (so `W[0] = 0`); the `IDOT` row is `X^(2k−1)` at the
opened-candidate columns; `IQD` is zero. -/
def tableau : Tableau F nreq 1 (cols nreq) 1 where
  rows _ _ := 0
  idot q := colNode nreq 1 q ^ dblock nreq 1
  iqd _ := 0

/-- The constraint `W[0] = 1`, which the zero witness violates. -/
def constraints : Constraints F 1 1 1 where
  A _ _ _ := 1
  b _ := 1

theorem tableau_not_satisfies : ¬ (tableau (F := F) (nreq := nreq)).Satisfies constraints := by
  intro h
  have := h 0
  simp [tableau, constraints, Tableau.witness] at this

/-- A tabled challenge: `alpha` is reached with agreement `2k − 1` on the columns other than `a`
and `b`. -/
structure Entry (F : Type) (n : ℕ) where
  /-- The challenge. -/
  alpha : F
  /-- The first column left out. -/
  a : Fin n
  /-- The second column left out. -/
  b : Fin n

/-- The columns other than the entry's two. -/
def Entry.kept (e : Entry F (cols nreq)) : Finset (Fin (cols nreq)) := univ \ {e.a, e.b}

/-- A table entry is correct relative to `P = ∏_q (k − 1 − node q)`: the two columns differ and
`((k − 1)^(2k−1) − alpha)·(k − 1 − node a)·(k − 1 − node b) = P`, so
`∏_{q ≠ a, b} (k − 1 − node q) = (k − 1)^(2k−1) − alpha`. -/
structure Entry.Valid (e : Entry F (cols nreq)) (P : F) : Prop where
  a_ne_b : e.a ≠ e.b
  check : (wnode nreq ^ dblock nreq 1 - e.alpha) * (wnode nreq - colNode nreq 1 e.a) *
    (wnode nreq - colNode nreq 1 e.b) = P

theorem Entry.valid_iff (e : Entry F (cols nreq)) (P : F) :
    e.Valid P ↔ e.a ≠ e.b ∧ (wnode nreq ^ dblock nreq 1 - e.alpha) *
      (wnode nreq - colNode nreq 1 e.a) * (wnode nreq - colNode nreq 1 e.b) = P :=
  ⟨fun h => ⟨h.a_ne_b, h.check⟩, fun h => ⟨h.1, h.2⟩⟩

instance [DecidableEq F] (e : Entry F (cols nreq)) (P : F) : Decidable (e.Valid P) :=
  decidable_of_iff _ (e.valid_iff P).symm

omit [Field F] in
theorem Entry.card_kept {e : Entry F (cols nreq)} (h : e.a ≠ e.b) :
    #e.kept = 2 * nreq + 1 := by
  rw [Entry.kept, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
    card_pair h]
  unfold cols
  omega

/-- The fixed `2k − 2` columns `0, …, 2k − 3` used for untabled challenges. -/
def baseCols (nreq : ℕ) : Finset (Fin (cols nreq)) :=
  (univ : Finset (Fin (2 * nreq))).map (Fin.castLEEmb (by unfold cols; omega))

theorem card_baseCols : #(baseCols nreq) = 2 * nreq := by
  simp [baseCols]

/-- The facts each instance checks by computation: the nodes `0 … NCOL − 1` are distinct, the
witness node is not an opened-candidate node, `P` is the product of all node factors at the
witness node, and every table entry is correct. -/
structure Facts (F : Type) [Field F] (nreq : ℕ) (P : F) (tbl : List (Entry F (cols nreq))) :
    Prop where
  nodes_injective : Function.Injective (fun i : Fin (dblock nreq 1 + cols nreq) => (i : F))
  wnode_ne : ∀ q : Fin (cols nreq), wnode nreq ≠ colNode (F := F) nreq 1 q
  prod_eq : ∏ q : Fin (cols nreq), (wnode nreq - colNode nreq 1 q) = P
  valid : ∀ e ∈ tbl, e.Valid P
  nodup : (tbl.map Entry.alpha).Nodup

variable [DecidableEq F]

/-- The response polynomial to the challenge `α`: `X^(2k−1) − ∏_{q ≠ a, b} (X − node q)` for a
tabled `α`, and otherwise `X^(2k−1) − (∏_{q ∈ baseCols} (X − node q))·(X − c)` with
`c = (k − 1) − ((k − 1)^(2k−1) − α)/∏_{q ∈ baseCols} (k − 1 − node q)`. -/
noncomputable def resp (tbl : List (Entry F (cols nreq))) (α : F) : F[X] :=
  match tbl.find? (fun e => decide (e.alpha = α)) with
  | some e => X ^ dblock nreq 1 - nodePoly e.kept
  | none => X ^ dblock nreq 1 - nodePoly (baseCols nreq) *
      (X - C (wnode nreq - (wnode nreq ^ dblock nreq 1 - α) /
        (nodePoly (baseCols nreq)).eval (wnode nreq)))

/-- The family's prover: `y_dot` is the values of `resp tbl α` at the nodes `0 … DBLOCK − 1`;
the quadratic response is zero. -/
noncomputable def prover (tbl : List (Entry F (cols nreq))) : Prover F nreq 1 1 where
  dot α i := (resp tbl (α 0)).eval (i : F)
  qpr _ _ := 0

/-- The set of columns on which the response to `α` agrees with the `IDOT` row by construction. -/
def agreeCols (tbl : List (Entry F (cols nreq))) (α : F) : Finset (Fin (cols nreq)) :=
  match tbl.find? (fun e => decide (e.alpha = α)) with
  | some e => e.kept
  | none => baseCols nreq

section Facts

variable {P : F} {tbl : List (Entry F (cols nreq))} (h : Facts F nreq P tbl)
include h

omit [DecidableEq F] in
theorem nodes_dblock_injective :
    Function.Injective (fun i : Fin (dblock nreq 1) => (i : F)) := by
  intro i j hij
  have := @h.nodes_injective (Fin.castLE (by omega) i) (Fin.castLE (by omega) j) (by simpa using hij)
  exact Fin.castLE_injective _ this

omit [DecidableEq F] in
theorem prod_base_ne_zero : (nodePoly (baseCols nreq)).eval (wnode (F := F) nreq) ≠ 0 := by
  rw [eval_nodePoly]
  exact prod_ne_zero_iff.2 fun q _ => sub_ne_zero.2 (h.wnode_ne q)

omit [DecidableEq F] in
/-- For a correct entry, `∏_{q ≠ a, b} (k − 1 − node q) = (k − 1)^(2k−1) − alpha`. -/
theorem eval_entry_cols {e : Entry F (cols nreq)} (he : e ∈ tbl) :
    (nodePoly e.kept).eval (wnode (F := F) nreq) = wnode nreq ^ dblock nreq 1 - e.alpha := by
  have hv := h.valid e he
  have hsplit := prod_sdiff (f := fun q => wnode (F := F) nreq - colNode nreq 1 q)
    (subset_univ {e.a, e.b})
  rw [prod_pair hv.a_ne_b, h.prod_eq] at hsplit
  have ha := sub_ne_zero.2 (h.wnode_ne e.a)
  have hb := sub_ne_zero.2 (h.wnode_ne e.b)
  rw [eval_nodePoly, Entry.kept]
  have hc := hv.check
  apply mul_right_cancel₀ (mul_ne_zero ha hb)
  rw [hsplit, ← hc]
  ring

theorem degree_resp_lt (α : F) : (resp tbl α).degree < dblock nreq 1 := by
  unfold resp
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    refine degree_sub_lt_of_monic (monic_X_pow _) (nodePoly_monic _) (natDegree_X_pow _) ?_
    rw [natDegree_nodePoly, Entry.card_kept (h.valid e hmem).a_ne_b]
    unfold dblock block
    omega
  · refine degree_sub_lt_of_monic (monic_X_pow _)
      ((nodePoly_monic _).mul (monic_X_sub_C _)) (natDegree_X_pow _) ?_
    rw [(nodePoly_monic _).natDegree_mul (monic_X_sub_C _), natDegree_nodePoly, card_baseCols,
      natDegree_X_sub_C]
    unfold dblock block
    omega

theorem eval_resp_wnode (α : F) : (resp tbl α).eval (wnode nreq) = α := by
  unfold resp
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    have hα : e.alpha = α := by simpa using List.find?_some he
    rw [eval_sub, eval_pow, eval_X, eval_entry_cols h hmem, hα]
    ring
  · have h0 := prod_base_ne_zero h
    rw [eval_sub, eval_mul, eval_pow, eval_X, eval_sub, eval_X, eval_C]
    field_simp
    ring

omit h in
theorem eval_resp_of_mem_agreeCols (α : F) {q : Fin (cols nreq)} (hq : q ∈ agreeCols tbl α) :
    (resp tbl α).eval (colNode nreq 1 q) = colNode nreq 1 q ^ dblock nreq 1 := by
  unfold resp
  unfold agreeCols at hq
  split at hq
  · simp [eval_nodePoly_of_mem hq]
  · simp [eval_nodePoly_of_mem hq]

theorem card_agreeCols (α : F) :
    #(agreeCols tbl α) = if α ∈ (tbl.map Entry.alpha).toFinset then 2 * nreq + 1 else 2 * nreq := by
  unfold agreeCols
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    have hα : e.alpha = α := by simpa using List.find?_some he
    have hin : α ∈ (tbl.map Entry.alpha).toFinset := by simpa using ⟨e, hmem, hα⟩
    simp only [hin, ↓reduceIte]
    exact Entry.card_kept (h.valid e hmem).a_ne_b
  · rename_i hn
    have hin : α ∉ (tbl.map Entry.alpha).toFinset := by
      simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
      intro e he hα
      exact (List.find?_eq_none.1 hn e he) (by simpa using hα)
    simp only [hin, ↓reduceIte]
    exact card_baseCols

theorem dotSum (α : Fin 1 → F) : DotSum constraints (prover tbl) α := by
  have hw : ((witnessPos (nreq := nreq) (0 : Fin 1) : ℕ) : F) = wnode nreq := by
    simp [witnessPos, wnode]
  simp only [DotSum, prover, Fin.sum_univ_one, constraints, mul_one]
  rw [hw, eval_resp_wnode h]

theorem accepts_column (α : Fin 1 → F) {q : Fin (cols nreq)} (hq : q ∈ agreeCols tbl (α 0)) :
    DotColumn tableau constraints (prover tbl) α q ∧ QuadColumn tableau (prover tbl) α q := by
  have hrows : ∀ i, (tableau (F := F) (nreq := nreq)).rows i = 0 := fun _ => rfl
  have hq0 : yquad (nreq := nreq) (wr := 1) ((prover (F := F) tbl).qpr α) = 0 := by
    funext j
    simp [yquad, prover]
  refine ⟨?_, ?_⟩
  · simp only [DotColumn, hrows, extendAt_zero, mul_zero, Finset.sum_const_zero, add_zero]
    rw [show (prover tbl).dot α = fun i : Fin (dblock nreq 1) => (resp tbl (α 0)).eval (i : F)
      from rfl, extendAt_eval (nodes_dblock_injective h) (degree_resp_lt h _),
      eval_resp_of_mem_agreeCols _ hq]
    rfl
  · rw [QuadColumn, hq0, extendAt_zero]
    rfl

variable [Fintype F]

/-- **The family's acceptance, from below.** Every challenge passes the dot-sum check; a tabled
challenge passes at `2k − 1` columns and any other at `2k − 2`. -/
theorem acceptProb_ge :
    ((tbl.length * (2 * nreq + 1).choose nreq +
        (Fintype.card F - tbl.length) * (2 * nreq).choose nreq : ℕ) : ℚ) /
        (Fintype.card F * (cols nreq).choose nreq) ≤
      acceptProb tableau constraints (prover tbl) := by
  rw [acceptProb_eq, pow_one]
  gcongr ?_ / _
  norm_cast
  set G := (tbl.map Entry.alpha).toFinset
  have hG : #G = tbl.length := by
    rw [List.toFinset_card_of_nodup h.nodup, List.length_map]
  have hle : ∀ α : Fin 1 → F,
      (if α 0 ∈ G then (2 * nreq + 1).choose nreq else (2 * nreq).choose nreq) ≤
        if DotSum constraints (prover tbl) α then
          (#{q | DotColumn tableau constraints (prover tbl) α q ∧
            QuadColumn tableau (prover tbl) α q}).choose nreq else 0 := by
    intro α
    simp only [dotSum h α, ↓reduceIte]
    have hsub : agreeCols tbl (α 0) ⊆ univ.filter (fun q => DotColumn tableau constraints
        (prover tbl) α q ∧ QuadColumn tableau (prover tbl) α q) := fun q hq =>
      mem_filter.2 ⟨mem_univ q, accepts_column h α hq⟩
    have hc := card_le_card hsub
    rw [card_agreeCols h] at hc
    split_ifs at hc ⊢ <;> exact Nat.choose_le_choose _ hc
  refine le_trans (le_of_eq ?_) (sum_le_sum fun α _ => hle α)
  rw [← (Equiv.funUnique (Fin 1) F).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul, filter_mem_eq_inter, univ_inter,
    hG, filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ _),
    card_univ, hG]

end Facts

/-- Distinct challenge values from a strictly increasing list of their representatives. -/
theorem nodup_of_isChain {p : ℕ} [NeZero p] {tbl : List (Entry (ZMod p) (cols nreq))}
    (hc : List.IsChain (· < ·) (tbl.map fun e => e.alpha.val)) : (tbl.map Entry.alpha).Nodup := by
  have hp : (tbl.map fun e => e.alpha.val).Nodup := (List.isChain_iff_pairwise.1 hc).imp ne_of_lt
  rw [show (tbl.map fun e => e.alpha.val) = (tbl.map Entry.alpha).map ZMod.val by
    simp [List.map_map, Function.comp_def]] at hp
  exact hp.of_map _

/-- An instance refutes the summed bound, at code length `len`, when the lower bound of
`acceptProb_ge` exceeds it. -/
theorem not_theorem44Summed [Fintype F] {P : F} {tbl : List (Entry F (cols nreq))} {len : ℕ}
    (h : Facts F nreq P tbl) (hr : 2 * block nreq 1 < len)
    (hlt : (((len + block nreq 1 + 1) / 2).choose nreq : ℚ) / len.choose nreq +
        (len + 1) / Fintype.card F +
          ((2 * block nreq 1 - 2).choose nreq / len.choose nreq + 1 / Fintype.card F) <
      ((tbl.length * (2 * nreq + 1).choose nreq +
        (Fintype.card F - tbl.length) * (2 * nreq).choose nreq : ℕ) : ℚ) /
        (Fintype.card F * (cols nreq).choose nreq)) :
    ¬ Theorem44Summed F nreq 1 (cols nreq) 1 1 len := by
  intro hT
  have hb := hT ⟨h.nodes_injective⟩ hr constraints tableau tableau_not_satisfies (prover tbl)
  exact absurd (hlt.trans_le (acceptProb_ge h)) (not_lt.2 hb)

end GordieHowe.Errata.CHVY25.Family
