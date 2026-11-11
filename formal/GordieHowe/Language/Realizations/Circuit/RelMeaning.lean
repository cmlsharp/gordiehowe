-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelEntry

@[expose] public section

/-!
# GordieHowe: the soundness of an entry's meaning check

An entry's asserted root has print `X`, and the circuit shows every coordinate of `X` zero. The
meaning check (`GordieHowe.RealizedProgram.entryMeaningB`) then gives the entry's meaning
(`GordieHowe.RealizedProgram.EntryHolds`,
`GordieHowe.RealizedProgram.entryHolds_of_entryMeaningB`):

* **The normal forms over shared-expression atoms** are sound (`nfS_sound`) and a difference the
  zero check accepts is zero (`zeroLoop_sound`), so `nfUnitEqB X Y` makes `X` equal to `Y` or `−Y`
  below `X`'s length (`nfUnitEqB_sound`).
* **A placed field equation** `l = r` follows when `X = ±(l − r)` is zero below `X`'s length and
  `l` is no longer than `X` (`sides_of_nfUnitEqB`).
-/

namespace GordieHowe.RealizedProgram

section

variable {ir : RealizedProgram} {I : Interp} {rd : ir.Valuation I} {f p : ℕ}

/-- **`nfUnitEqB X Y` makes `X` equal to `Y` or to `−Y`** below `X`'s length, in domain `d`. -/
theorem nfUnitEqB_sound {d chr neg1 : ℕ} [CharP (I (ir.domainField d)).K chr]
    (hN : NormModel rd (ir.domainField d) chr) (hneg : (I (ir.domainField d)).decode neg1 = -1)
    {«X» «Y» : Expr} (h : ir.nfUnitEqB d chr neg1 «X» «Y» = true) :
    (∀ i < ir.exprLen «X», ir.evalWith rd d «X» i = ir.evalWith rd d «Y» i) ∨
      ∀ i < ir.exprLen «X», ir.evalWith rd d «X» i = -ir.evalWith rd d «Y» i := by
  unfold nfUnitEqB at h
  simp only at h
  split at h
  · rename_i a b ha hb
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    have hr : ∀ i < ir.exprLen «X», i < (List.range (ir.exprLen «X»)).length ∧
        (List.range (ir.exprLen «X»)).getD i 0 = i := fun i hi => by
      refine ⟨by simpa using hi, ?_⟩
      simp only [List.getD_eq_getElem?_getD, List.getElem?_range hi, Option.getD_some]
    have eX : ∀ i < ir.exprLen «X», ir.evalWith rd d «X» i = sVal rd (ir.domainField d) i a :=
      fun i hi => by
        have e := nfS_sound hN _ _ _ a ha i (hr i hi).1
        rwa [(hr i hi).2] at e
    have eY : ∀ i < ir.exprLen «X», ir.evalWith rd d «Y» i = sVal rd (ir.domainField d) i b :=
      fun i hi => by
        have e := nfS_sound hN _ _ _ b hb i (hr i hi).1
        rwa [(hr i hi).2] at e
    rcases h with h | ⟨hlt, h⟩
    · left
      intro i hi
      have hz := zeroLoop_sound hN _ _ h i hi
      rw [sVal_sAdd, sVal_sScale, natCast_intCode hN.pos] at hz
      rw [eX i hi, eY i hi]
      push_cast at hz
      linear_combination hz
    · right
      intro i hi
      have hz := zeroLoop_sound hN _ _ h i hi
      rw [sVal_sAdd, sVal_sScale, sVal_sScale, natCast_intCode hN.pos, ← hN.dec neg1 hlt,
        hneg] at hz
      rw [eX i hi, eY i hi]
      push_cast at hz
      linear_combination hz
  · cases h

/-- **A zero `X = ±(l − r)` gives the field equation `l = r`**, `l` no longer than `X`. -/
theorem sides_of_nfUnitEqB {d chr neg1 : ℕ} [CharP (I (ir.domainField d)).K chr]
    (hN : NormModel rd (ir.domainField d) chr) (hneg : (I (ir.domainField d)).decode neg1 = -1)
    {«X» l r : Expr} (hl : ir.exprLen l ≤ ir.exprLen «X»)
    (h : ir.nfUnitEqB d chr neg1 «X» (.sub l r) = true)
    (hX : ∀ i < ir.exprLen «X», ir.evalWith rd d «X» i = 0) :
    ∀ i < ir.exprLen l, ir.evalWith rd d l i = ir.evalWith rd d r i := by
  intro i hi
  have hiX : i < ir.exprLen «X» := lt_of_lt_of_le hi hl
  have hs : ir.evalWith rd d (.sub l r) i = 0 := by
    rcases nfUnitEqB_sound hN hneg h with h' | h'
    · rw [← h' i hiX, hX i hiX]
    · rw [← neg_eq_zero, ← h' i hiX, hX i hiX]
  simp only [evalWith, evalE_sub] at hs
  exact sub_eq_zero.1 hs

end

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {rd : ir.Valuation I}
  {c chr neg1 : ℕ}

/-- **A placed predicate's sides give its meaning**: the predicate body of `placedSides?` holds
placed when its sides agree below the left side's length. -/
theorem placedHolds_of_placedSides {b : PredBody} {d : ℕ} {l r : Expr}
    (hb : placedSides? b = some (d, l, r))
    (h : ∀ i < ir.exprLen l, ir.evalWith rd d l i = ir.evalWith rd d r i) :
    ir.PlacedHolds rd b := by
  unfold placedSides? at hb
  split at hb
  · cases hb
    exact h
  · rename_i d' q l' r' real
    split_ifs at hb with hq
    cases hb
    have hq' : q = 0 ∨ real.form = .field := by
      simpa only [Bool.or_eq_true, Nat.beq_eq, decide_eq_true_eq] using hq
    simp only [PlacedHolds, hq', ↓reduceIte]
    exact h
  · cases hb

/-- **The meaning check is sound**: an entry whose root's print `X` meets `entryMeaningB`, every
coordinate of `X` zero, holds (`EntryHolds`). -/
theorem entryHolds_of_entryMeaningB [CharP (I (ir.circField c)).K chr]
    (hN : ir.NormModel rd (ir.circField c) chr) (hneg : (I (ir.circField c)).decode neg1 = -1)
    {en : CircuitEntry} {«X» : Option Expr}
    (h : ir.entryMeaningB c chr neg1 en «X» = true)
    (hX : ∀ «Y», «X» = some «Y» → ∀ i < ir.exprLen «Y», ir.evalWith rd (ir.circuit c).domain «Y» i = 0) :
    ir.EntryHolds rd en := by
  -- the predicate case, shared by `typeCheck` and `pred`
  have hpred : ∀ (p : ℕ) («Y» : Expr), «X» = some «Y» →
      (match placedSides? (ir.predicate p).body with
        | some (d, l, r) =>
          Nat.beq d (ir.circuit c).domain && Nat.beq (ir.exprLen l) (ir.exprLen «Y») &&
            ir.nfUnitEqB d chr neg1 «Y» (.sub l r)
        | none => false) = true →
      ir.PlacedHolds rd (ir.predicate p).body := by
    intro p «Y» hY hm
    have hXY := hX «Y» hY
    split at hm
    · rename_i d l r hs
      simp only [Bool.and_eq_true, Nat.beq_eq] at hm
      obtain ⟨⟨rfl, hl⟩, hu⟩ := hm
      exact placedHolds_of_placedSides hs (sides_of_nfUnitEqB hN hneg hl.le hu hXY)
    · cases hm
  cases en with
  | typeCheck p =>
    cases «X» with
    | none => simp [entryMeaningB] at h
    | some «Y» => exact hpred p «Y» rfl h
  | pred p =>
    cases «X» with
    | none => simp [entryMeaningB] at h
    | some «Y» => exact hpred p «Y» rfl h
  | alignment _ => trivial
  | realization _ => simp [entryMeaningB] at h

end GordieHowe.RealizedProgram
