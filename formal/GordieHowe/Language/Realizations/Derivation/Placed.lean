-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation
public import GordieHowe.Language.Realizations.RealizeField
public import GordieHowe.Language.RealizedProgram.CellsLowering

@[expose] public section

/-!
# GordieHowe: the placed predicates from valid derivations

The honest prover's domains hold on its cells (`GordieHowe.RealizedProgram.holds_of_sat_derivs`)
where the source predicates hold and the derivations are valid (`DerivationsValid`).

* **A placed predicate holds where its predicate does and the realized program holds**
  (`GordieHowe.RealizedProgram.placedHolds_of_derivs`): a `mod_0` has its field equation by the
  realized program (`RealizedAt.integer`), a `mod_p` in the field form by its field `equal` row
  (`DerivationsValid.fieldRows`, `fieldEq_of_fieldRow`); every other `mod_q` is placed by its
  realization circuits, and every other predicate is placed as written.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **A `mod_p` whose field equation is a row has it** (`fieldRowB`): under the leaf facts, the
field `equal` `e + (p − 1)·e' = 0` gives `e = e'` in the field. -/
theorem fieldEq_of_fieldRow (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d q : ℕ}
    {e e' : Expr} {real : ModRealization} (hpo : ir.PredOk (.mod d q e e' real))
    (hc : q = ir.charOf (ir.domainField d)) (h2q : 2 < q)
    (hrow : ir.predicates.any (fun p => ir.fieldRowB d e e' p.body) = true) :
    ∀ i < ir.exprLen e, ir.evalWith rd d e i = ir.evalWith rd d e' i := by
  have hd : d < ir.domains.length := (hpo.1 (d, e) (by simp [PredBody.exprs])).1
  have hdF := domainField_lt hwf hd
  have h2 : 2 < ir.charOf (ir.domainField d) := hc ▸ h2q
  obtain ⟨-, hcharF, -, hdec⟩ := modData hwf hI hL hd h2
  obtain ⟨pr, hpr, hrow⟩ := List.any_eq_true.1 hrow
  obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hpr
  unfold fieldRowB at hrow
  split at hrow
  · rename_i d' e₁ c e₂ z tgt hbody
    simp only [Bool.and_eq_true, beq_iff_eq] at hrow
    obtain ⟨⟨⟨⟨hd', h1⟩, h2'⟩, hc'⟩, hz⟩ := hrow
    subst d'
    have hH := hF.equals pid hpid (by rw [hbody]; rfl)
    rw [hbody, Expr.eq_of_beq h1, Expr.eq_of_beq h2'] at hH
    intro i hi
    have hrowi := hH i hi
    simp only [evalWith, evalE_add, evalE_scale_const] at hrowi
    rw [evalE_leaf_constAll hL hF hz hdF (by omega) hi, hdec c (by omega)] at hrowi
    have hc1 : ((c : ℕ) : (I (ir.domainField d)).K) = -1 := by
      have : ((c + 1 : ℕ) : (I (ir.domainField d)).K) = 0 := by
        rw [hc']
        exact CharP.cast_eq_zero _ _
      push_cast at this
      linear_combination this
    rw [hc1, Nat.cast_zero] at hrowi
    simp only [evalWith]
    linear_combination hrowi
  · cases hrow

/-- **A placed predicate holds** (`PlacedHolds`) where its predicate holds, given valid derivations
and the field equations of the `mod_0`s (`hint`, the realized program's `integer`): a `mod_p` in
the field form by its row (`fieldEq_of_fieldRow`), every other `mod_q` with `q ≠ 0` trivially. -/
theorem placedHolds_of_derivs (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {sr : List (ℕ × ℕ)} {D : Derivations}
    (hv : ir.DerivationsValid primeNodes sr D) {rd : ir.Valuation I} (hF : ir.LeafFacts rd)
    {pid : ℕ} (hpid : pid < ir.predicates.length)
    (hint : ∀ d lhs rhs real, (ir.predicate pid).body = .mod d 0 lhs rhs real →
      ∀ i < ir.exprLen lhs, ir.evalWith rd d lhs i = ir.evalWith rd d rhs i)
    (h : ir.HoldsWith rd (ir.predicate pid).body) : ir.PlacedHolds rd (ir.predicate pid).body := by
  have hpo := hwf.predicates _ (predicate_mem hpid)
  have hrows := hv.fieldRows pid hpid
  revert hint h hpo hrows
  generalize (ir.predicate pid).body = b
  intro hint h hpo hrows
  cases b with
  | mod d q e e' real =>
    by_cases hq : q = 0
    · subst hq
      rw [placedHolds_mod_zero_iff]
      exact hint d e e' real rfl
    · by_cases hf : real.form = .field
      · simp only [PlacedHolds, hf, or_true, ↓reduceIte]
        obtain ⟨hc, h2, hrow⟩ := hrows d q e e' real rfl hq hf
        exact fieldEq_of_fieldRow hwf hI hL hF hpo hc h2 hrow
      · simp only [PlacedHolds, hq, hf, or_self, ↓reduceIte]
  | _ => exact h

/-- **The placed predicates hold, from valid derivations**: domain `d`'s predicate holds on the cells `a` where the source predicates hold, the
realized program holds and the value ranges hold. -/
theorem holds_of_sat_derivs (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {treeNodes : ℕ → List String}
    (hv : ir.CellsValid) (hl : ir.Local treeNodes) {sr : List (ℕ × ℕ)} {D : Derivations}
    (hd : ir.DerivationsValid primeNodes sr D)
    {x : ir.Valuation I} {a : ∀ d : Fin ir.domains.length, ir.Cell d → (I (ir.domainField d)).K}
    {r : (ir.layout I).Run} (hbase : ∀ (d : Fin ir.domains.length) k, a d k ∈ ir.cellBase I d k)
    (hsat : ir.SatAt (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I a)) r))
    (hreal : ir.Realized I x (ir.ofAllCells I a) r) (d : Fin ir.domains.length) :
    (ir.domainOf I d).Holds x (a d) r := by
  have hpred : ∀ p, p < ir.predicates.length → (ir.predicate p).body.domain? = some (d : ℕ) →
      ir.PlacedHolds (ir.cellValuation I d x r (a d)) (ir.predicate p).body := fun p hp hd' =>
    (placedHolds_cellValuation_iff hl a d hp hd').2
      (placedHolds_of_derivs hwf hI hL hd hsat.leafFacts hp
        (fun d' lhs rhs real hb => hreal.integer _ (predicate_mem hp) d' lhs rhs real hb)
        (hsat.preds _ (predicate_mem hp)))
  have hlow : ∀ p, p < ir.predicates.length → ir.Lowered d p →
      ir.PlacedHolds (ir.cellValuation I d x r (a d)) (ir.predicate p).body := fun p hp h =>
    hpred p hp (hl.domain_of_lowered h)
  refine ⟨hbase d, fun c => ?_, fun q => ?_, fun i => quadRow_holds_of_placed i.1.1.2 i.1.2
    (hlow _ i.1.1.2 (.quad i.1.1.2 i.1.2)) i.2, fun b => ?_, fun q => ?_⟩
  · change ir.CircuitHolds I c.1 (ir.cellValuation I d x r (a d))
    intro e he
    have hok := hv.entries c.1 c.1.2 e he
    cases e with
    | typeCheck p =>
      exact hpred p (of_decide_eq_true hok) (c.2 ▸ hl.placed c.1 c.1.2 p (.inr he))
    | alignment _ => trivial
    | pred p => exact hpred p (of_decide_eq_true hok) (c.2 ▸ hl.placed c.1 c.1.2 p (.inl he))
    | realization rc =>
      cases rc with
      | logup t g =>
        simp only [entryOkB, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨v, hnode, hf⟩ := exists_chalNode_of_alphaNodeB (hv.alpha t hok.1)
        exact (logupHoldsAt_cellValuation_iff hl a d c.2 he).2
          ((ir.logupHoldsAt_reader_iff _ hnode hf).2 (hreal.logup t hok.1 g hok.2))
      | macH p =>
        simp only [entryOkB, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨dx, x', dy, y, k, real, v, hb, hn, hbx, hv', hf⟩ := exists_of_macHNodeB hok.2
        exact (macHHolds_cellValuation_iff hl a d c.2 he).2
          ((macHHolds_reader_iff _ hb hn hv' hf).2
            (hreal.macH _ (predicate_mem hok.1) _ _ _ _ _ _ hb hn hbx))
      | named _ => trivial
      | unmodeled _ => trivial
  · exact (affineRows_iff q.1 x (a d) r).2 (hlow _ q.1.1.2 (.row q.1.1.2 q.1.2)) q.2
  · rcases b with b | b
    · have hb := partsOk_of_cols b.2
      refine (batchRelation_holds_iff (Interp.zeroDecodes_of_lawful hI hL) hb x r (a d)).2
        fun p hp => ?_
      exact hlow p (hb.parts p hp) (.batch b hp)
    · have hb := bitsBatchOk b.2.1
      refine (bitsBatchRelation_holds_iff (Interp.zeroDecodes_of_lawful hI hL) b.2.1 b.2.2 x r
        (a d)).2 fun p hp => ?_
      refine hpred p ((partsOk_of_bits b.2.1).parts p hp) ?_
      rw [← hb.1.domain]
      exact hl.batches b.1 b.1.2 p hp
  · exact (viewRows_iff q.1 x (a d) r).2 (hlow _ q.1.1.2 (.viewRow q.1.1.2 q.1.2)) q.2

end

end GordieHowe.RealizedProgram
