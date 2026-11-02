-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.AdaptiveCompleteness

@[expose] public section

/-!
# Adaptive completeness of a salted argument against a classical oracle program

The fresh-slice reduction of `GordieHowe/Model/ROM/AdaptiveCompleteness.lean` (Unruh 2017,
ePrint 2017/398, Definition 5, p. 14) for an adversary given as a classical oracle program
(`GordieHowe.OracleProg`) with at most `t` queries, in place of a `t`-query algorithm `ROM.Alg`.
The argument is the same: the program reads the oracle only at its trace (`OracleProg.run_congr`),
and a uniform salt drawn after the run is carried by one of its at most `t` queries with
probability at most `t / |Sd|`.

- `OracleProg.prob_hit_le`: one of the queries of a program with at most `t` queries carries a
  uniform salt with probability at most `t / |Sd|`.
- `OracleProg.prob_bad_le_fresh`: the fresh-slice reduction (identical until a query carries the
  salt, then the exchange of the slices).
- `OracleProg.prob_bad_coins_le`: with the honest prover's coins, the event `Bad r σ H (p.run H)`
  has probability at most `δ + t / |Sd|` under the fresh-slice bound `δ`.
-/

namespace GordieHowe.OracleProg

open GordieHowe.IOP GordieHowe.QROM GordieHowe.ROM
open scoped ENNReal

variable {A B O : Type} [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B] {Sd : Type}
  [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] (saltOf : A → Option Sd) (p : OracleProg A B O)
  {t : ℕ}

omit [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B] [DecidableEq Sd] in
/-- **A query of a program carries a uniform salt with probability at most `t / |Sd|`**: over a
uniform salt `σ`, one of the at most `t` queries of `p` against a fixed oracle has salt `σ`. -/
theorem prob_hit_le (hp : p.QueriesLE t) (h : A → B) :
    Pr[σ ← Sd : ∃ a ∈ p.trace h, saltOf a = some σ] ≤ t / Fintype.card Sd := by
  classical
  let l := p.trace h
  calc _ ≤ Pr[σ ← Sd : ∃ i : Fin l.length, saltOf l[i] = some σ] :=
        QROM.probUniform_mono fun σ ⟨a, ha, hs⟩ => by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
          exact ⟨⟨i, hi⟩, hs⟩
    _ ≤ ∑ i : Fin l.length, Pr[σ ← Sd : saltOf l[i] = some σ] := probUniform_exists_le _
    _ ≤ ∑ _i : Fin l.length, (1 : ℝ≥0∞) / Fintype.card Sd := Finset.sum_le_sum fun i _ => by
          refine (probUniform_le_card_div ((saltOf l[i]).toFinset) fun σ hσ => ?_).trans ?_
          · simpa using hσ
          · gcongr
            cases saltOf l[i] <;> simp
    _ = l.length / Fintype.card Sd := by simp [ENNReal.div_eq_inv_mul, mul_comm]
    _ ≤ t / Fintype.card Sd := by
          gcongr
          exact_mod_cast hp h

/-- **The fresh-slice reduction against a program with at most `t` queries**: over a uniform salt
`σ` and a uniform oracle `H`, the event `Bad σ H (p.run H)` has probability at most that of
`Bad σ (replaceSlice saltOf σ H F) (p.run H)` over a further uniform `F`, plus `t / |Sd|`. -/
theorem prob_bad_le_fresh (hp : p.QueriesLE t) (Bad : Sd → (A → B) → O → Prop) :
    Pr[q ← Sd × (A → B) : Bad q.1 q.2 (p.run q.2)] ≤
      Pr[q ← Sd × ((A → B) × (A → B)) :
          Bad q.1 (replaceSlice saltOf q.1 q.2.1 q.2.2) (p.run q.2.1)] +
        t / Fintype.card Sd := by
  classical
  have hext : Pr[q ← Sd × (A → B) : Bad q.1 q.2 (p.run q.2)] =
      Pr[q ← Sd × ((A → B) × (A → B)) : Bad q.1 q.2.1 (p.run q.2.1)] := by
    rw [← probUniform_prod_fst (Y := A → B)
      (fun q : Sd × (A → B) => Bad q.1 q.2 (p.run q.2))]
    exact (QROM.probUniform_equiv (Equiv.prodAssoc Sd (A → B) (A → B)).symm
      (fun z : (Sd × (A → B)) × (A → B) => Bad z.1.1 z.1.2 (p.run z.1.2))).symm
  rw [hext]
  let Hit : Sd × ((A → B) × (A → B)) → Prop := fun q =>
    ∃ a ∈ p.trace q.2.1, saltOf a = some q.1
  let Sw : Sd × ((A → B) × (A → B)) → Prop := fun q =>
    Bad q.1 q.2.1 (p.run (replaceSlice saltOf q.1 q.2.1 q.2.2))
  have hcover : ∀ q : Sd × ((A → B) × (A → B)), Bad q.1 q.2.1 (p.run q.2.1) → Sw q ∨ Hit q := by
    intro q hq
    by_cases hh : Hit q
    · exact Or.inr hh
    · left
      have : p.run q.2.1 = p.run (replaceSlice saltOf q.1 q.2.1 q.2.2) :=
        run_congr p fun a ha =>
          (replaceSlice_apply_of_ne saltOf fun hs => hh ⟨a, ha, hs⟩).symm
      change Bad q.1 q.2.1 _
      rw [← this]
      exact hq
  have hSw : Pr[q ← Sd × ((A → B) × (A → B)) : Sw q] =
      Pr[q ← Sd × ((A → B) × (A → B)) :
        Bad q.1 (replaceSlice saltOf q.1 q.2.1 q.2.2) (p.run q.2.1)] := by
    rw [← QROM.probUniform_equiv (Equiv.prodCongrRight fun σ => sliceSwap saltOf σ)]
    congr 1
    funext q
    change Bad q.1 (sliceSwap saltOf q.1 q.2).1 (p.run (replaceSlice saltOf q.1
      (sliceSwap saltOf q.1 q.2).1 (sliceSwap saltOf q.1 q.2).2)) = _
    rw [replaceSlice_sliceSwap]
    rfl
  have hHit : Pr[q ← Sd × ((A → B) × (A → B)) : Hit q] ≤ t / Fintype.card Sd := by
    rw [← QROM.probUniform_equiv (Equiv.prodComm ((A → B) × (A → B)) Sd) Hit]
    exact probUniform_prod_le fun q => p.prob_hit_le saltOf hp q.1
  exact (QROM.probUniform_mono hcover).trans
    ((QROM.probUniform_or_le _ _).trans (add_le_add hSw.le hHit))

/-- **Adaptive completeness of a salted argument with coins against a program with at most `t`
queries**: if, at every salt `σ`, oracle `g` and output `o`, the event `Bad r σ H o` has
probability at most `δ` over uniform coins `r` and a fresh slice of `σ` (`hslice`), then over
uniform coins `r`, a uniform salt `σ` and a uniform oracle `H`, the event `Bad r σ H (p.run H)`
has probability at most `δ + t / |Sd|`. -/
theorem prob_bad_coins_le (hp : p.QueriesLE t) {R : Type} [Fintype R] [Nonempty R]
    {Bad : R → Sd → (A → B) → O → Prop} {δ : ℝ≥0∞}
    (hslice : ∀ σ g o, Pr[q ← R × (A → B) : Bad q.1 σ (replaceSlice saltOf σ g q.2) o] ≤ δ) :
    ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * Pr[q ← Sd × (A → B) : Bad r q.1 q.2 (p.run q.2)] ≤
      δ + t / Fintype.card Sd := by
  refine (sum_inv_card_mul_le_add fun r => p.prob_bad_le_fresh saltOf hp (Bad r)).trans
    (add_le_add ?_ le_rfl)
  rw [← probUniform_prod_eq_sum (fun z : R × (Sd × ((A → B) × (A → B))) =>
    Bad z.1 z.2.1 (replaceSlice saltOf z.2.1 z.2.2.1 z.2.2.2) (p.run z.2.2.1)),
    ← QROM.probUniform_equiv (coinsReorder R Sd (A → B)).symm]
  exact probUniform_prod_le fun σ => probUniform_prod_le fun H => hslice σ H (p.run H)

end GordieHowe.OracleProg
