-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.TwoFields

@[expose] public section

/-!
# GordieHowe: the honest strategy from the source, MACs with an ungrouped digit tail

A MAC whose tail is a `mod_2` in the ungrouped digit form (compiler/mac.h with compiler/mod.h
`kDigits`: the left side committed by an accumulator `acc`, a lower digit `low` and the derived top
digit, bounded by `in`s, and the no-wrap range on `q · (low + B · top)`), as the ML-DSA programs
realize their MACs (`DigitsMac`). The generated values (`GordieHowe.RealizedProgram.genSrc`): the accumulator is the
natural of the tail's left side's integer reading (`digitsAccNat`), the lower digit its quotient by
`q`'s first base-`B` digit (`lowDigitNat`).

* At the honest environment such a MAC satisfies its predicates,
  where its operands are bits.
* The realization's facts give the realization's predicates at the
  honest environment where the source environment satisfies their obligations.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-! ## A MAC with an ungrouped digit tail -/

variable (ir primeNodes) in
/-- **A MAC whose tail is a `mod_2` in the ungrouped digit form** (compiler/mac.h with
compiler/mod.h `kDigits`): a MAC (`MacBase`) whose tail has the digits `[low, top]` (`low` a value,
`top` derived from the accumulator `acc`, which commits the left side by a row), and the facts the
honest values need: the owners of the accumulator and the lower digit, which are late values of
their domain's field; the left side reads no late value; the convolutions fit the characteristic;
the lookups on the digits and the no-wrap range `2 low + 2 B top` have room (`lowRoom`, `topRoom`,
`wrapRoom`). Data and properties of the program, decided per program. -/
structure DigitsMac extends ir.MacBase primeNodes where
  /-- The accumulator. -/
  acc : ℕ
  /-- The lower digit. -/
  low : ℕ
  /-- The derived top digit. -/
  top : Expr
  hdig : realT.digits = [.leaf low, top]
  hT : realT.isDigitsTail = true
  hacc : ir.digitsAcc realT = acc
  accRow : ir.accRowB dy acc L = true
  derived : ir.topDerivedB dy 2 R realT acc = true
  accOwn : ir.digitsAccOwner? acc = some t
  accTag : ir.tagOwner? acc = none
  accGr : ir.accOwner? acc = none
  accDig : ir.digitsOwner? acc = none
  accHist : ir.histOwner? acc = none
  accLt : acc < ir.values.length
  accLate : ir.IsLate acc
  accField : ir.valueField acc = ir.domainField dy
  lowOwn : ir.lowDigitOwner? low = some (t, 0)
  lowTag : ir.tagOwner? low = none
  lowGr : ir.accOwner? low = none
  lowDig : ir.digitsOwner? low = none
  lowHist : ir.histOwner? low = none
  lowDAcc : ir.digitsAccOwner? low = none
  lowLt : low < ir.values.length
  lowLate : ir.IsLate low
  lowField : ir.valueField low = ir.domainField dy
  lowSize : (ir.value low).size = u.width
  accSize : (ir.value acc).size = u.width
  topLen : ir.exprLen top = u.width
  lNoLate : ∀ v ∈ ir.exprNodes L, ir.NoLateRead v
  hw : 0 < u.width
  convFit : 2 * u.width < ir.charOf (ir.domainField dy)
  accMax : 1 + u.chunks * Conv.convMax u.width u.taps.toFinset < ir.charOf (ir.domainField dy)
  radixPos : 0 < realT.radix
  radixChar : 2 * realT.radix < ir.charOf (ir.domainField dy)
  lowRoom : ∀ p ∈ ir.predicates, ∀ d N r, p.body = .mem d [.leaf low] (.range N) (.lookup r) →
    d = dy ∧ realT.radix ≤ N
  topRoom : ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
    D.beq top = true →
      d = dy ∧ (1 + u.chunks * Conv.convMax u.width u.taps.toFinset) / (2 * realT.radix) < N
  wrapRoom : ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) r →
    D.beq (.add (.scale (.const 2) (.leaf low)) (.scale (.const (2 * realT.radix)) top)) = true →
      d = dy ∧ 1 + u.chunks * Conv.convMax u.width u.taps.toFinset < N

/-! ## A group with a static and a late histogram -/

/-- **The needles of a group's members reading no late value.** -/
def staticNeedles (rd : ir.Valuation I) (f t g : ℕ) : List (I f).K :=
  ((ir.members t g).filter fun m => !ir.memberReadsLate m).flatMap (ir.memberVals rd f)

/-- **A group's needles are its late and static members' needles**, up to order. -/
theorem groupNeedles_perm (rd : ir.Valuation I) (f t g : ℕ) :
    (((ir.members t g).filter ir.memberReadsLate).flatMap (ir.memberVals rd f) ++
      ir.staticNeedles rd f t g).Perm (ir.groupNeedles rd f t g) := by
  unfold staticNeedles groupNeedles
  rw [← List.flatMap_append]
  exact List.Perm.flatMap_right _ (List.filter_append_perm _ _)

/-! ## The values a table's rows read -/

variable (ir) in
/-- **The values the rows of table `t` read** (`tableRow`): none for a range, the first column for
a committed table, the expression's values for a table of an expression's coordinates. -/
def tableRowReads (t : ℕ) : List ℕ :=
  match (ir.table t).rows with
  | .range _ => []
  | .columns cols => [cols.headD 0]
  | .expr e' => ir.exprNodes e'

/-- **A table's rows depend only on the values they read** (`tableRowReads`). -/
theorem tableRow_congr_reads {rd rd' : ir.Valuation I} {f t : ℕ}
    (h : ∀ w ∈ ir.tableRowReads t, rd w = rd' w) : ir.tableRow rd f t = ir.tableRow rd' f t := by
  funext j
  unfold tableRow
  unfold tableRowReads at h
  split
  · rfl
  · rename_i cols hc
    rw [hc] at h
    rw [h _ (List.mem_singleton_self _)]
  · rename_i e' he
    rw [he] at h
    rw [evalE_congr h]

/-- **The honest counts depend only on the needles' and the rows' values.** -/
theorem honestCounts_congr {rd rd' : ir.Valuation I} {t g : ℕ}
    (hn : ∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle), rd w = rd' w)
    (hr : ∀ w ∈ ir.tableRowReads t, rd w = rd' w) :
    ir.honestCounts rd t g = ir.honestCounts rd' t g := by
  unfold honestCounts
  rw [groupNeedles_congr hn, tableRow_congr_reads hr]

/-! ## The facts the realization's honest values need -/

/-- **The groups with no late histogram count their needles** in the environment `e`: their
histograms are the honest counts (`honestCounts`). -/
def StaticHistsCount (e : ir.Env I) : Prop :=
  ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, (ir.groupOf t g).lateMult = none →
    Range.combined (ir.staticHist (ir.reader e) (ir.chalField (ir.alphaOf t)) t g)
        (ir.lateHist (ir.reader e) (ir.chalField (ir.alphaOf t)) t g) =
      ir.honestCounts (ir.reader e) t g

/-- **The node-typed values other than the generated late values lie in their types** in the
environment `e`. -/
def SrcTypesHold (e : ir.Env I) : Prop :=
  ∀ v < ir.values.length, (ir.value v).typeSource = .node → (ir.IsLate v → ir.IsSourceValue v) →
    ∀ i < (ir.value v).size, (I (ir.valueField v)).InType (ir.value v).type (ir.reader e v i)

/-! ## Checkers for the digit tails' room -/

variable (ir) in
/-- **`DigitsMac.topRoom`, as a check**: every lookup of a single record `D` with `D.beq top` into
a range `[0, N)` is of domain `dy` with `m < N`. -/
def topRoomB (top : Expr) (dy m : ℕ) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .mem d [D] (.range N) (.lookup _) => !(D.beq top) || (d == dy && decide (m < N))
    | _ => true

theorem topRoom_of_B {top : Expr} {dy m : ℕ} (h : ir.topRoomB top dy m = true) :
    ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
      D.beq top = true → d = dy ∧ m < N := by
  intro p hp d D N r hb hD
  have := List.all_eq_true.1 h p hp
  simp only [hb, hD, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  exact this

variable (ir) in
/-- **`DigitsMac.wrapRoom`, as a check**: every membership of a single record `D` with `D.beq W`
in a range `[0, N)` is of domain `dy` with `m < N`. -/
def wrapRoomB (W : Expr) (dy m : ℕ) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .mem d [D] (.range N) _ => !(D.beq W) || (d == dy && decide (m < N))
    | _ => true

theorem wrapRoom_of_B {W : Expr} {dy m : ℕ} (h : ir.wrapRoomB W dy m = true) :
    ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) r →
      D.beq W = true → d = dy ∧ m < N := by
  intro p hp d D N r hb hD
  have := List.all_eq_true.1 h p hp
  simp only [hb, hD, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  exact this

/-- **`DigitsMac.lowRoom` from `digitsRoomB`.** -/
theorem lowRoom_of_B {low dy B : ℕ} (h : ir.digitsRoomB low dy B = true) :
    ∀ p ∈ ir.predicates, ∀ d N r, p.body = .mem d [.leaf low] (.range N) (.lookup r) →
      d = dy ∧ B ≤ N := fun p hp d N r hb =>
  have h' := digitsRoom_of_B h p hp d N r hb
  ⟨h'.1, h'.2.2⟩

end

end GordieHowe.RealizedProgram
