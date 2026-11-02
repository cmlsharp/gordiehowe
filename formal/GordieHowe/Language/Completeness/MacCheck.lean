-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Mac
public import GordieHowe.Language.Honest.Check
public import GordieHoweNative.Language.Completeness.MacCheck
public import GordieHowe.Language.RealizedProgram.Reader

@[expose] public section

/-!
# GordieHowe: completeness certificates, the checks of the honest MACs

The MACs of a completeness certificate (`MacBaseC`, `DigitsMacC`, `OneDigitMacC`, `GroupedMacC`,
`MacFormC`) built from Boolean checks on a MAC site (`macBaseCB`, `digitsMacCB`, `oneDigitMacCB`,
`groupedMacCB`, `macTailCB`, `MacBaseC.ofB`, `DigitsMacC.ofB`, `OneDigitMacC.ofB`,
`GroupedMacC.ofB`, `MacFormC.ofB`), the check that a predicate plays a given role in a MAC
(`macRoleAtB`, its twin `macRoleAtE`, `roleC_of_macRoleAtB`), and the MAC's source facts at the
certificate's honest environment from an accepting execution (`MacBaseC.source_honestC`). The MAC
checks over the fields of characteristic `2` (`TwoMacC`, from the check `twoMacCB` by
`TwoMacC.ofB`): their tails hold at the honest environment (`TwoMacC.tail_honest`) from their source
facts (`TwoMacC.source_honestC`), and their tags are honest (`TwoMacC.macTag_honest`).

The definitions are in `GordieHoweNative/Language/Completeness/MacCheck.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {S : Structure}

variable (ir primeNodes) in
/-- **Every cross-field `equal` has an interval-free MAC realization**: the structural checks
(`EventsOk`) the MACs' checks over a field need. -/
def MacsRealizable : Prop := ir.EventsOk primeNodes

variable (ir primeNodes S) in
/-- **`PReader.macBaseB` at the program is `macBaseCB`.** -/
theorem macBaseB_ofProgram (G : Gens) (st : MacSite) :
    @PReader.macBaseB ir (PReader.ofProgram ir) primeNodes S G st =
      ir.macBaseCB primeNodes S G st := by
  unfold PReader.macBaseB macBaseCB
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, PReader.ofProgram_nPreds, PReader.ofProgram_nValues,
    PReader.ofProgram_value, PReader.ofProgram_predicate]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
      h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, h23, h24, h25⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.lt, h.cross⟩, h.side⟩, h.blind⟩, h.tail⟩, h.opOk⟩, h.dyLt⟩,
        h.opExpr⟩, h.tailMod⟩, h.tailD⟩, h.tailQ⟩, h.tailR⟩, h.units⟩, h.tagGen⟩, h.tagNotSource⟩,
        h.tagLate⟩, h.tag1⟩, h.xNoLate⟩, h.yNoLate⟩, h.opNoLate⟩, h.powNoLate⟩, h.blindCopy⟩,
        h.macChar⟩, h.powField⟩, h.width⟩

variable (ir) in
/-- **`PReader.digitsMacB` at the program is `digitsMacCB`.** -/
theorem digitsMacB_ofProgram (G : Gens) (st : MacSite) :
    @PReader.digitsMacB ir (PReader.ofProgram ir) G st = ir.digitsMacCB G st := by
  unfold PReader.digitsMacB digitsMacCB
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, PReader.ofProgram_nPreds, PReader.ofProgram_nValues,
    PReader.ofProgram_value, PReader.ofProgram_predicate]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
      h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, h23, h24, h25, h26⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.tailForm, h.two⟩, h.derived⟩, h.accGen⟩, h.accNotSource⟩,
        h.accLt⟩, h.accLate⟩, h.accField⟩, h.lowGen⟩, h.lowNotSource⟩, h.lowLt⟩, h.lowLate⟩,
        h.lowField⟩, h.lowSize⟩, h.accSize⟩, h.topLen⟩, h.lNoLate⟩, h.hw⟩, h.conv⟩, h.convFit⟩,
        h.accMax⟩, h.radixPos⟩, h.radixChar⟩, h.lowRoom⟩, h.topRoom⟩, h.wrapRoom⟩

/-- **`macBaseCB` is sound** (`MacBaseFactsC`). -/
theorem macBaseFactsC_of_B {G : Gens} {st : MacSite} (h : ir.macBaseCB primeNodes S G st = true) :
    ir.MacBaseFactsC (primeNodes := primeNodes) S G st :=
  of_decide_eq_true h

namespace MacBaseFactsC

variable {G : Gens} {st : MacSite} (F : ir.MacBaseFactsC (primeNodes := primeNodes) S G st)
include F

/-- **The site's predicate is its cross-field `equal`** (`body_eq_macCross`). -/
theorem hb : (ir.predicate st.pid).body = .cross (ir.macCross st.pid).dx (ir.macCross st.pid).x
    (ir.macCross st.pid).dy (ir.macCross st.pid).y (ir.macCross st.pid).k (ir.macCross st.pid).real :=
  body_eq_macCross F.cross

/-- **The site's MAC check over its field** (`MacFieldCheck`): the
hosted MAC's interval-free shape from the structural checks (`hreal`, `MacHostedCore`) for `y`'s
field, or, where no domain hosts the MAC, its interval-free two-tail shape (`MacTwoCore`) and the
site's check over a field of odd characteristic. -/
theorem macFieldCheck (hreal : ir.MacsRealizable primeNodes) :
    ir.MacFieldCheck primeNodes S st.pid (ir.macCross st.pid).dx (ir.macCross st.pid).x
      (ir.macCross st.pid).dy (ir.macCross st.pid).y (ir.macCross st.pid).k
      (ir.macCross st.pid).real (ir.siteDom st) (ir.macCheckOp st) (ir.macBlind st) := by
  have hS := F.side
  have hop := F.opOk
  unfold macOpOkB at hop
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 F.blind
  unfold macFieldCheckB at hS
  have hRz := hreal.macs _ F.lt _ _ _ _ _ _ F.hb
  simp only [macCoreOkB] at hRz
  rcases hx : (ir.macCross st.pid).real.blindX with _ | bx
  · rw [hx] at hS hRz hop
    rw [hb] at hRz
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hS
    have hxs : st.xSide = false := hS.1
    refine Or.inl ⟨MacHostedCore.of_B hRz, ?_, ?_, ?_, ?_⟩
    · simp [siteDom, hxs]
    · simpa [siteDom, siteOp, hxs] using hop
    · simp [macBlind, hxs, hb]
    · simpa [siteDom, hxs] using hS.2
  · rw [hx] at hS hRz hop
    rw [Expr.eq_of_beq hop]
    rw [hb] at hRz
    have hc := MacTwoCore.of_B hRz
    simp only [Bool.and_eq_true] at hS
    obtain ⟨hS, hch⟩ := hS
    have hch' : MacChars ir (ir.macCross st.pid).dx (ir.macCross st.pid).dy := of_decide_eq_true hch
    have hodd := macOddFieldOk_of_atB hS
    have hbs : ir.macBlind st = if st.xSide then bx else b := by simp [macBlind, hx, hb]
    cases hxs : st.xSide
    · simp only [hxs, Bool.false_eq_true, ite_false] at hbs
      simp only [siteDom, siteOp, hxs, Bool.false_eq_true, ite_false] at hodd ⊢
      rw [hbs] at hodd ⊢
      exact Or.inr (Or.inr ⟨bx, hx, hb, hc, hch'.1, hodd, rfl, rfl⟩)
    · simp only [hxs, ite_true] at hbs
      simp only [siteDom, siteOp, hxs, ite_true] at hodd ⊢
      rw [hbs] at hodd ⊢
      exact Or.inr (Or.inl ⟨b, hx, hb, hc, hch'.2, hodd, rfl, rfl⟩)

/-- **The tail is a predicate of the program** (`macTailAtB`). -/
theorem tail_lt : ir.macTail st < ir.predicates.length := by
  have h := F.tail
  unfold macTailAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- **The tail is a `mod_2` of the site's domain** (`macTailParts`). -/
theorem hbt : (ir.predicate (ir.macTail st)).body = .mod (ir.siteDom st) 2
    (ir.macTailParts st).lhs (ir.macTailParts st).rhs (ir.macTailParts st).real := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 F.tailMod
  have he : ir.macTailParts st = m := by simp [macTailParts, hm]
  rw [← F.tailD, ← F.tailQ, he, ← predicateT_eq]
  exact PredBody.eq_of_modParts? hm

/-- **The tail's left side is in the MAC unit form with units `macUnitsAt`.** -/
theorem hu : macUnits? (ir.macTailParts st).lhs = some (ir.macUnitsAt st) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 F.units
  simp [macUnitsAt, hu]

end MacBaseFactsC

variable (primeNodes) in
/-- **The MAC of a MAC site `st` with its tail at the certificate's generators** (`MacBaseC`), from the covered MAC realizations (`hreal`) and the check `macBaseCB`. -/
def MacBaseC.ofB (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes) {G : Gens}
    (st : MacSite) (h : ir.macBaseCB primeNodes S G st = true) : ir.MacBaseC primeNodes S G where
  pid := st.pid
  dx := (ir.macCross st.pid).dx
  x := (ir.macCross st.pid).x
  cdy := (ir.macCross st.pid).dy
  cy := (ir.macCross st.pid).y
  k := (ir.macCross st.pid).k
  real := (ir.macCross st.pid).real
  hpid := (macBaseFactsC_of_B h).lt
  hb := (macBaseFactsC_of_B h).hb
  dy := (ir.siteDom st)
  y := (ir.macCheckOp st)
  sb := ir.macBlind st
  hside := (macBaseFactsC_of_B h).macFieldCheck hreal
  dyLt := (macBaseFactsC_of_B h).dyLt
  yOk := (macBaseFactsC_of_B h).opExpr
  t := ir.macTail st
  ht := (macBaseFactsC_of_B h).tail_lt
  htB := (macBaseFactsC_of_B h).tail
  realT := (ir.macTailParts st).real
  L := (ir.macTailParts st).lhs
  R := (ir.macTailParts st).rhs
  hbt := (macBaseFactsC_of_B h).hbt
  u := ir.macUnitsAt st
  hu := (macBaseFactsC_of_B h).hu
  tagGen := (macBaseFactsC_of_B h).tagGen
  tagNotSource := (macBaseFactsC_of_B h).tagNotSource
  tagLate := (macBaseFactsC_of_B h).tagLate
  xNoLate := fun _ hv => noLateRead_of_B hwf ((macBaseFactsC_of_B h).xNoLate _ hv)
  cyNoLate := fun _ hv => noLateRead_of_B hwf ((macBaseFactsC_of_B h).yNoLate _ hv)
  yNoLate := fun _ hv => noLateRead_of_B hwf ((macBaseFactsC_of_B h).opNoLate _ hv)
  powNoLate := noLateRead_of_B hwf (macBaseFactsC_of_B h).powNoLate
  blindCopy := kind_of_isPadCopyB (macBaseFactsC_of_B h).blindCopy
  macChar := (macBaseFactsC_of_B h).macChar

/-- **`digitsMacCB` is sound** (`DigitsMacFactsC`). -/
theorem digitsMacFactsC_of_B {G : Gens} {st : MacSite} (h : ir.digitsMacCB G st = true) :
    ir.DigitsMacFactsC G st :=
  of_decide_eq_true h

/-- **The digits of the tail are `[low, top]`** (`macLow`, `macTop`). -/
theorem DigitsMacFactsC.hdig {G : Gens} {st : MacSite} (F : ir.DigitsMacFactsC G st) :
    (ir.macTailParts st).real.digits = [.leaf (ir.macLow st), ir.macTop st] := by
  have h := F.two
  unfold macLow macTop
  split at h
  · rename_i l t hd
    rw [hd]
  · cases h

variable (primeNodes) in
/-- **The MAC of a MAC site `st` with an ungrouped digit tail at the certificate's generators**
(`DigitsMacC`), from the covered MAC realizations (`hreal`) and the checks
`macBaseCB` and `digitsMacCB`. -/
def DigitsMacC.ofB (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes) {G : Gens}
    (st : MacSite) (h : ir.macBaseCB primeNodes S G st = true) (hd : ir.digitsMacCB G st = true) :
    ir.DigitsMacC primeNodes S G where
  toMacBaseC := MacBaseC.ofB primeNodes hwf hreal st h
  acc := ir.macDigitsAcc st
  low := ir.macLow st
  top := ir.macTop st
  hdig := (digitsMacFactsC_of_B hd).hdig
  hT := (digitsMacFactsC_of_B hd).tailForm
  hacc := rfl
  derived := (digitsMacFactsC_of_B hd).derived
  accGen := (digitsMacFactsC_of_B hd).accGen
  accNotSource := (digitsMacFactsC_of_B hd).accNotSource
  accLt := (digitsMacFactsC_of_B hd).accLt
  accLate := (digitsMacFactsC_of_B hd).accLate
  accField := (digitsMacFactsC_of_B hd).accField
  lowGen := (digitsMacFactsC_of_B hd).lowGen
  lowNotSource := (digitsMacFactsC_of_B hd).lowNotSource
  lowLt := (digitsMacFactsC_of_B hd).lowLt
  lowLate := (digitsMacFactsC_of_B hd).lowLate
  lowField := (digitsMacFactsC_of_B hd).lowField
  lowSize := (digitsMacFactsC_of_B hd).lowSize
  accSize := (digitsMacFactsC_of_B hd).accSize
  topLen := (digitsMacFactsC_of_B hd).topLen
  lNoLate := fun _ hv => noLateRead_of_B hwf ((digitsMacFactsC_of_B hd).lNoLate _ hv)
  hw := (digitsMacFactsC_of_B hd).hw
  convFit := (digitsMacFactsC_of_B hd).convFit
  accMax := by
    change 1 + (ir.macUnitsAt st).chunks *
      Conv.convMax (ir.macUnitsAt st).width (ir.macUnitsAt st).taps.toFinset < _
    rw [convMax_eq_macConvMaxAt (digitsMacFactsC_of_B hd).conv]
    exact (digitsMacFactsC_of_B hd).accMax
  radixPos := (digitsMacFactsC_of_B hd).radixPos
  radixChar := (digitsMacFactsC_of_B hd).radixChar
  lowRoom := lowRoom_of_B (digitsMacFactsC_of_B hd).lowRoom
  topRoom := by
    change ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
      D.beq (ir.macTop st) = true → d = (ir.siteDom st) ∧
        (1 + (ir.macUnitsAt st).chunks *
          Conv.convMax (ir.macUnitsAt st).width (ir.macUnitsAt st).taps.toFinset) /
            (2 * (ir.macTailParts st).real.radix) < N
    rw [convMax_eq_macConvMaxAt (digitsMacFactsC_of_B hd).conv]
    exact topRoom_of_B (digitsMacFactsC_of_B hd).topRoom
  wrapRoom := by
    change ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) r →
      D.beq (ir.macWrapExpr st) = true → d = (ir.siteDom st) ∧
        1 + (ir.macUnitsAt st).chunks *
          Conv.convMax (ir.macUnitsAt st).width (ir.macUnitsAt st).taps.toFinset < N
    rw [convMax_eq_macConvMaxAt (digitsMacFactsC_of_B hd).conv]
    exact wrapRoom_of_B (digitsMacFactsC_of_B hd).wrapRoom

/-- **`oneDigitMacCB` is sound** (`OneDigitMacFactsC`). -/
theorem oneDigitMacFactsC_of_B {G : Gens} {st : MacSite} (h : ir.oneDigitMacCB G st = true) :
    ir.OneDigitMacFactsC G st :=
  of_decide_eq_true h

variable (primeNodes) in
/-- **The MAC of a MAC site `st` with a one-digit tail at the certificate's generators**
(`OneDigitMacC`), from the covered MAC realizations (`hreal`) and the checks
`macBaseCB` and `oneDigitMacCB`. -/
def OneDigitMacC.ofB (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes) {G : Gens}
    (st : MacSite) (h : ir.macBaseCB primeNodes S G st = true) (hd : ir.oneDigitMacCB G st = true) :
    ir.OneDigitMacC primeNodes S G where
  toMacBaseC := MacBaseC.ofB primeNodes hwf hreal st h
  acc := ir.macOneAcc st
  hT := (oneDigitMacFactsC_of_B hd).tailForm
  hacc := rfl
  derived := (oneDigitMacFactsC_of_B hd).derived
  accGen := (oneDigitMacFactsC_of_B hd).accGen
  accNotSource := (oneDigitMacFactsC_of_B hd).accNotSource
  accLt := (oneDigitMacFactsC_of_B hd).accLt
  accLate := (oneDigitMacFactsC_of_B hd).accLate
  accField := (oneDigitMacFactsC_of_B hd).accField
  accSize := (oneDigitMacFactsC_of_B hd).accSize
  quotLen := (oneDigitMacFactsC_of_B hd).quotLen
  lNoLate := fun _ hv => noLateRead_of_B hwf ((oneDigitMacFactsC_of_B hd).lNoLate _ hv)
  hw := (oneDigitMacFactsC_of_B hd).hw
  convFit := (oneDigitMacFactsC_of_B hd).convFit
  accMax := by
    change 1 + (ir.macUnitsAt st).chunks *
      Conv.convMax (ir.macUnitsAt st).width (ir.macUnitsAt st).taps.toFinset < _
    rw [convMax_eq_macConvMaxAt (oneDigitMacFactsC_of_B hd).conv]
    exact (oneDigitMacFactsC_of_B hd).accMax
  quotRoom := by
    change ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
      D.beq (ir.macTailParts st).real.quotExpr = true → d = (ir.siteDom st) ∧
        (1 + (ir.macUnitsAt st).chunks *
          Conv.convMax (ir.macUnitsAt st).width (ir.macUnitsAt st).taps.toFinset) / 2 < N
    rw [convMax_eq_macConvMaxAt (oneDigitMacFactsC_of_B hd).conv]
    exact topRoom_of_B (oneDigitMacFactsC_of_B hd).quotRoom

/-- **`groupedMacCB` is sound** (`GroupedMacFactsC`). -/
theorem groupedMacFactsC_of_B {G : Gens} {st : MacSite}
    (h : ir.groupedMacCB G st = true) :
    ir.GroupedMacFactsC G st :=
  of_decide_eq_true h

namespace GroupedMacFactsC

variable {G : Gens} {st : MacSite} (F : ir.GroupedMacFactsC G st)
include F

/-- **The tail's grouping** (`macGrouping`). -/
theorem hG : (ir.macTailParts st).real.grouped = some (ir.macGrouping st) := by
  obtain ⟨Gm, hG⟩ := Option.isSome_iff_exists.1 F.grouped
  simp [macGrouping, hG]

/-- **The accumulators are the leaf `macGroupAcc`.** -/
theorem hA : (ir.macGrouping st).accumulators = some (.leaf (ir.macGroupAcc st)) := by
  have h := F.accLeaf
  unfold macGroupAcc
  split at h
  · rename_i a ha
    rw [ha]
  · cases h

/-- **The quotient digits are the leaf `macGroupGq`.** -/
theorem hD : (ir.macGrouping st).groupDigits = .leaf (ir.macGroupGq st) := by
  have h := F.gqLeaf
  unfold macGroupGq
  split at h
  · rename_i g hg
    rw [hg]
  · cases h

end GroupedMacFactsC

variable (primeNodes) in
/-- **The MAC of a MAC site `st` with a grouped tail at the certificate's generators**
(`GroupedMacC`), from the covered MAC realizations (`hreal`) and the checks
`macBaseCB` and `groupedMacCB`. -/
def GroupedMacC.ofB (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes) {G : Gens}
    (st : MacSite) (h : ir.macBaseCB primeNodes S G st = true)
    (hg : ir.groupedMacCB G st = true) : ir.GroupedMacC primeNodes S G where
  toMacBaseC := MacBaseC.ofB primeNodes hwf hreal st h
  core := (groupedMacFactsC_of_B hg).core
  quotRange := (groupedMacFactsC_of_B hg).quotRange
  Gm := ir.macGrouping st
  hG := (groupedMacFactsC_of_B hg).hG
  acc := ir.macGroupAcc st
  hA := (groupedMacFactsC_of_B hg).hA
  gq := ir.macGroupGq st
  hD := (groupedMacFactsC_of_B hg).hD
  accGen := (groupedMacFactsC_of_B hg).accGen
  accNotSource := (groupedMacFactsC_of_B hg).accNotSource
  accLt := (groupedMacFactsC_of_B hg).accLt
  accLate := (groupedMacFactsC_of_B hg).accLate
  accField := (groupedMacFactsC_of_B hg).accField
  gqGen := (groupedMacFactsC_of_B hg).gqGen
  gqNotSource := (groupedMacFactsC_of_B hg).gqNotSource
  gqLt := (groupedMacFactsC_of_B hg).gqLt
  gqLate := (groupedMacFactsC_of_B hg).gqLate
  gqField := (groupedMacFactsC_of_B hg).gqField
  fit := by
    change ∀ fc ∈ (ir.macGrouping st).groups,
      fc.2 * Conv.convMax (ir.macUnitsAt st).width (ir.macUnitsAt st).taps.toFinset / 2 < _
    rw [convMax_eq_macConvMaxAt (groupedMacFactsC_of_B hg).conv]
    exact (groupedMacFactsC_of_B hg).fit
  digitsRoom := digitsRoom_of_B (groupedMacFactsC_of_B hg).digitsRoom
  finalRoom := finalRoom_of_B (groupedMacFactsC_of_B hg).finalRoom

variable (ir primeNodes) in
/-- **A MAC check over a field with its tail's form, at the certificate's generators**
(`MacFormC`): a grouped tail (`GroupedMacC`), an ungrouped digit
tail (`DigitsMacC`) or a one-digit tail (`OneDigitMacC`). -/
inductive MacFormC (S : Structure) (G : Gens) where
  /-- A MAC with a grouped tail. -/
  | grouped (M : ir.GroupedMacC primeNodes S G)
  /-- A MAC with an ungrouped digit tail. -/
  | digits (M : ir.DigitsMacC primeNodes S G)
  /-- A MAC with a one-digit tail. -/
  | oneDigit (M : ir.OneDigitMacC primeNodes S G)

namespace MacFormC

variable {G : Gens}

/-- **The MAC with its tail** (`MacBaseC`). -/
def base : ir.MacFormC primeNodes S G → ir.MacBaseC primeNodes S G
  | .grouped M => M.toMacBaseC
  | .digits M => M.toMacBaseC
  | .oneDigit M => M.toMacBaseC

/-- **The predicates the MAC's honest values satisfy** (`GroupedMacC.Role`, `DigitsMacC.Role`,
`OneDigitMacC.Role`). -/
def Role : ir.MacFormC primeNodes S G → PredBody → Prop
  | .grouped M, b => M.Role b
  | .digits M, b => M.Role b
  | .oneDigit M, b => M.Role b

variable {Inp : Type} (hgen : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I)
  (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

/-- **The MAC's predicates hold at the honest values** (`Role`; `GroupedMacC.role_holds`,
`DigitsMacC.role_holds`, `OneDigitMacC.role_holds`), where the source facts hold. -/
theorem role_holds (M : ir.MacFormC primeNodes S G) (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (hB : ir.BlindsArePadCopies)
    (hpow2 : ∀ j < M.base.real.width,
      (I M.base.real.macField).decode (2 ^ j) = (I M.base.real.macField).decode 2 ^ j)
    (htag1 : (ir.value M.base.real.tag).size = 1) (hS : M.base.Source HE)
    {p : Predicate} (hp : p ∈ ir.predicates) (hr : M.Role p.body) :
    ir.HoldsWith HE p.body := by
  cases M with
  | grouped M => exact M.role_holds hgen stmtOf val SL y c π hwf hI hL hM hB hpow2 htag1 hS hp hr
  | digits M => exact M.role_holds hgen stmtOf val SL y c π hwf hI hL hM hB hpow2 htag1 hS hp hr
  | oneDigit M => exact M.role_holds hgen stmtOf val SL y c π hwf hI hL hM hB hpow2 htag1 hS hp hr

/-- **The MAC's honest tag** (`MacTagAt`; `macTagC_honest`) at the honest environment of the
certificate. -/
theorem macTag_honest (M : ir.MacFormC primeNodes S G) :
    ir.MacTagAt HE M.base.dx M.base.x M.base.real (castElt ((ir.honestEnv I (stmtOf y) (val y)
        (ir.genLateOf I hgen stmtOf val SL y) c π).chal M.base.real.key 0)) := by
  cases M with
  | grouped M => exact M.macTag_honest hgen stmtOf val SL y c π
  | digits M => exact M.macTag_honest hgen stmtOf val SL y c π
  | oneDigit M => exact M.macTag_honest hgen stmtOf val SL y c π

end MacFormC

variable (primeNodes) in
/-- **The MAC of a MAC site `st` with its tail at the certificate's generators** (`MacFormC`), by the tail's form: grouped (`GroupedMacC.ofB`), one-digit (`OneDigitMacC.ofB`) or
the ungrouped digit form (`DigitsMacC.ofB`), from the covered MAC realizations (`hreal`) and the
checks `macBaseCB` and `macTailCB`. -/
def MacFormC.ofB (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes) {G : Gens}
    (st : MacSite) (h : ir.macBaseCB primeNodes S G st = true)
    (ht : ir.macTailCB G st = true) : ir.MacFormC primeNodes S G :=
  if hg : (ir.macTailParts st).real.grouped.isSome = true then
    .grouped (GroupedMacC.ofB primeNodes hwf hreal st h (by
      unfold macTailCB at ht
      rwa [if_pos hg] at ht))
  else if ho : (ir.macTailParts st).real.isOneDigitTail = true then
    .oneDigit (OneDigitMacC.ofB primeNodes hwf hreal st h (by
      unfold macTailCB at ht
      rwa [if_neg hg, if_pos ho] at ht))
  else
    .digits (DigitsMacC.ofB primeNodes hwf hreal st h (by
      unfold macTailCB at ht
      rwa [if_neg hg, if_neg ho] at ht))

section OfB

variable (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes) {G : Gens} {st : MacSite}
  (h : ir.macBaseCB primeNodes S G st = true) (ht : ir.macTailCB G st = true) {Inp : Type}
  (hgen : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp)
  (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

/-- **The MAC of a site's predicates hold at the honest values** (`MacFormC.role_holds` at
`MacFormC.ofB`), where the source facts of the site's MAC (`MacBaseC.ofB`) hold. -/
theorem MacFormC.ofB_role_holds (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    (hM : I.MacModel ir) (hB : ir.BlindsArePadCopies)
    (hpow2 : ∀ j < (ir.macCross st.pid).real.width,
      (I (ir.macCross st.pid).real.macField).decode (2 ^ j) =
        (I (ir.macCross st.pid).real.macField).decode 2 ^ j)
    (htag1 : (ir.value (ir.macCross st.pid).real.tag).size = 1)
    (hS : (MacBaseC.ofB primeNodes hwf hreal st h).Source HE) {p : Predicate}
    (hp : p ∈ ir.predicates) (hr : (MacFormC.ofB primeNodes hwf hreal st h ht).Role p.body) :
    ir.HoldsWith HE p.body := by
  unfold MacFormC.ofB at hr
  split at hr
  · exact (GroupedMacC.ofB primeNodes hwf hreal st h _).role_holds hgen stmtOf val SL y c π hwf hI
      hL hM hB hpow2 htag1 hS hp hr
  split at hr
  · exact (OneDigitMacC.ofB primeNodes hwf hreal st h _).role_holds hgen stmtOf val SL y c π hwf hI
      hL hM hB hpow2 htag1 hS hp hr
  · exact (DigitsMacC.ofB primeNodes hwf hreal st h _).role_holds hgen stmtOf val SL y c π hwf hI
      hL hM hB hpow2 htag1 hS hp hr

include hwf hreal h ht in
/-- **The MAC of a site's honest tag** (`GroupedMacC.macTag_honest`, `OneDigitMacC.macTag_honest`,
`DigitsMacC.macTag_honest` at the site's tail form), with the site's cross-field `equal`. -/
theorem MacFormC.ofB_macTag_honest :
    ir.MacTagAt HE (ir.macCross st.pid).dx (ir.macCross st.pid).x (ir.macCross st.pid).real
      (castElt ((ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π).chal
        (ir.macCross st.pid).real.key 0)) := by
  unfold macTailCB at ht
  by_cases hg : (ir.macTailParts st).real.grouped.isSome = true
  · rw [if_pos hg] at ht
    exact (GroupedMacC.ofB primeNodes hwf hreal st h ht).macTag_honest hgen stmtOf val SL y c π
  rw [if_neg hg] at ht
  by_cases ho : (ir.macTailParts st).real.isOneDigitTail = true
  · rw [if_pos ho] at ht
    exact (OneDigitMacC.ofB primeNodes hwf hreal st h ht).macTag_honest hgen stmtOf val SL y c π
  · rw [if_neg ho] at ht
    exact (DigitsMacC.ofB primeNodes hwf hreal st h ht).macTag_honest hgen stmtOf val SL y c π

end OfB

variable (ir primeNodes) in
/-- **`macRoleAtB` as a check whose failure names the predicate** (`StructReason.macRole`). -/
def macRoleAtE (S : Structure) (st : MacSite) (role : MacRole) (q : ℕ) :
    Except StructFailure Unit :=
  Twin.guardE (ir.macRoleAtB primeNodes S st role q) ⟨q, 0, .macRole⟩

theorem okB_macRoleAtE (S : Structure) (st : MacSite) (role : MacRole) (q : ℕ) :
    Twin.okB (ir.macRoleAtE primeNodes S st role q) = ir.macRoleAtB primeNodes S st role q :=
  Twin.okB_guardE _ _

/-- **`macRoleAtB` is sound**: predicate `q` is a predicate of the MAC of `st` (`MacFormC.Role`),
at every role. -/
theorem roleC_of_macRoleAtB (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes)
    {G : Gens} {st : MacSite} {role : MacRole} {q : ℕ} (h : ir.macBaseCB primeNodes S G st = true)
    (ht : ir.macTailCB G st = true) (hr : ir.macRoleAtB primeNodes S st role q = true) :
    (MacFormC.ofB primeNodes hwf hreal st h ht).Role (ir.predicate q).body := by
  unfold MacFormC.ofB
  split
  · rename_i hg
    show (GroupedMacC.ofB primeNodes hwf hreal st h _).Role _
    cases role with
    | tail =>
      simp only [macRoleAtB, beq_iff_eq] at hr
      subst hr
      exact Or.inl rfl
    | h =>
      simp only [macRoleAtB, beq_iff_eq] at hr
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hr, rfl⟩))))
    | groupRow g =>
      simp only [macRoleAtB, Bool.and_eq_true, decide_eq_true_eq, predicateT_eq] at hr
      exact Or.inr (Or.inl ⟨g, hr.1.2, hr.2⟩)
    | residues =>
      simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq] at hr
      obtain ⟨-, hres⟩ := hr
      refine Or.inr (Or.inr (Or.inl ?_))
      split at hres
      · rename_i d R₁ R₂ R₃ tgt hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hres
        obtain ⟨⟨⟨hd, h1⟩, h2⟩, h3⟩ := hres
        exact ⟨R₁, R₂, R₃, tgt, by rw [hb, hd]; rfl, h1, h2, h3⟩
      · cases hres
    | gqLookup =>
      simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq] at hr
      obtain ⟨-, hgq⟩ := hr
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      split at hgq
      · rename_i d g N r hb
        simp only [beq_iff_eq] at hgq
        subst hgq
        exact ⟨d, N, r, hb⟩
      · cases hgq
    | quotLookup =>
      simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq] at hr
      obtain ⟨-, hfin⟩ := hr
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      split at hfin
      · rename_i d D N r hb
        exact ⟨d, D, N, r, hb, hfin⟩
      · cases hfin
    | accRow | lowLookup | topLookup | wrap =>
      simp [macRoleAtB, hg] at hr
  · rename_i hg
    split
    · rename_i ho
      show (OneDigitMacC.ofB primeNodes hwf hreal st h _).Role _
      cases role with
      | tail =>
        simp only [macRoleAtB, beq_iff_eq] at hr
        subst hr
        exact Or.inl rfl
      | h =>
        simp only [macRoleAtB, beq_iff_eq] at hr
        exact Or.inr (Or.inr (Or.inr ⟨q, hr, rfl⟩))
      | accRow =>
        simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq, ho, if_true] at hr
        obtain ⟨-, hacc⟩ := hr
        refine Or.inr (Or.inl ?_)
        split at hacc
        · rename_i d Lr z tg hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hacc
          obtain ⟨⟨hd', hz⟩, ht'⟩ := hacc
          exact ⟨Lr, z, tg, by rw [hb, hd']; rfl, hz, ht'⟩
        · cases hacc
      | quotLookup =>
        simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq] at hr
        obtain ⟨-, hq⟩ := hr
        refine Or.inr (Or.inr (Or.inl ?_))
        split at hq
        · rename_i d D N r hb
          exact ⟨d, D, N, r, hb, hq⟩
        · cases hq
      | groupRow _ | residues | gqLookup =>
        simp [macRoleAtB, hg] at hr
      | lowLookup | topLookup | wrap =>
        simp [macRoleAtB, ho] at hr
    · rename_i ho
      show (DigitsMacC.ofB primeNodes hwf hreal st h _).Role _
      cases role with
      | tail =>
        simp only [macRoleAtB, beq_iff_eq] at hr
        subst hr
        exact Or.inl rfl
      | h =>
        simp only [macRoleAtB, beq_iff_eq] at hr
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hr, rfl⟩))))
      | accRow =>
        simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq, ho, Bool.false_eq_true,
          if_false] at hr
        obtain ⟨-, hacc⟩ := hr
        refine Or.inr (Or.inl ?_)
        split at hacc
        · rename_i d Lr z tg hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hacc
          obtain ⟨⟨hd', hz⟩, ht'⟩ := hacc
          exact ⟨Lr, z, tg, by rw [hb, hd']; rfl, hz, ht'⟩
        · cases hacc
      | lowLookup =>
        simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq] at hr
        obtain ⟨-, hlow⟩ := hr
        refine Or.inr (Or.inr (Or.inl ?_))
        split at hlow
        · rename_i d l N r hb
          simp only [beq_iff_eq] at hlow
          subst hlow
          exact ⟨d, N, r, hb⟩
        · cases hlow
      | topLookup =>
        simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq] at hr
        obtain ⟨-, htop⟩ := hr
        refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        split at htop
        · rename_i d D N r hb
          exact ⟨d, D, N, r, hb, htop⟩
        · cases htop
      | wrap =>
        simp only [macRoleAtB, Bool.and_eq_true, predicateT_eq] at hr
        obtain ⟨-, hwrap⟩ := hr
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        split at hwrap
        · rename_i d D N r hb
          exact ⟨d, D, N, r, hb, hwrap⟩
        · cases hwrap
      | groupRow _ | residues | gqLookup =>
        simp [macRoleAtB, hg] at hr
      | quotLookup =>
        simp [macRoleAtB, hg, ho] at hr

/-- **The check `macIvlB` of a site gives its MAC's interval facts** (`macIvlAtB`): the
cross-field `equal` is a source predicate and the check's operand reads within `[0, 1]` by the
source values' intervals. -/
theorem MacBaseC.ofB_ivl (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes) {G : Gens}
    {st : MacSite} (h : ir.macBaseCB primeNodes S G st = true)
    (hi : ir.macIvlB primeNodes S st = true) :
    ir.inSource (ir.predicate (MacBaseC.ofB primeNodes hwf hreal st h).pid) = true ∧
      IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes S)
        (ir.domainField (MacBaseC.ofB primeNodes hwf hreal st h).dy)
        (MacBaseC.ofB primeNodes hwf hreal st h).y) 0 1 := by
  unfold macIvlB macIvlAtB at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, predicateT_eq] at hi
  exact hi

namespace MacBaseC

variable {G : Gens} (M : ir.MacBaseC primeNodes S G)

/-- **The source facts depend only on the operands' readings**: readers
agreeing on the `x` operand, the cross-field `equal`'s `y` operand and the check's operand. -/
theorem Source.congr {rd rd' : ir.Valuation I}
    (h : ∀ v, v ∈ ir.exprNodes M.x ∨ v ∈ ir.exprNodes M.cy ∨ v ∈ ir.exprNodes M.y → rd v = rd' v)
    (hS : M.Source rd) : M.Source rd' := by
  have hx : ir.evalWith rd M.dx M.x = ir.evalWith rd' M.dx M.x :=
    funext fun i => congrFun (evalE_congr fun v hv => h v (Or.inl hv)) i
  have hy : ir.evalWith rd M.dy M.y = ir.evalWith rd' M.dy M.y :=
    funext fun i => congrFun (evalE_congr fun v hv => h v (Or.inr (Or.inr hv))) i
  have hyi : ir.evalIntWith rd M.dy M.y = ir.evalIntWith rd' M.dy M.y :=
    evalIntWith_congr fun v hv => h v (Or.inr (Or.inr hv))
  refine ⟨(holdsWith_congr fun v hv => h v ?_).1 hS.cross, ?_, ?_, ?_⟩
  · have hv' : v ∈ ir.exprNodes M.x ∨ v ∈ ir.exprNodes M.cy := by
      simpa [predNodes, PredBody.exprs, tableCols] using hv
    exact hv'.imp_right Or.inl
  · rw [← hx]
    exact hS.xbits
  · rw [← hy]
    exact hS.ybits
  · rw [← hy, ← hyi]
    exact hS.yint

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  (R : ir.CommittedFacts I G) {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
  (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads)

include hwf hI hL R hA in
/-- **The MAC's source facts hold at the source environment** of the honest committed values where
the execution accepts: the cross-field `equal`, a source predicate (`hsrc`),
holds and reads bits by the agreement on the source values (`SourceAcceptingAt.crossBits`), and the
check's operand's integer reading is its indicator by its interval from the source values' (`hw`,
`exprIvl_within_of`). -/
theorem source_srcEnvC (hbd : ir.StmtBounded I x) (hsrc : ir.inSource (ir.predicate M.pid) = true)
    (hw : IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField M.dy) M.y) 0 1) :
    M.Source (ir.reader (ir.srcEnvL I x (ir.genCommitted I G x s) (ir.padSpaceLate I l) c π)) := by
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  have hcb : ir.CrossBitsAt I (ir.srcEnvL I x (ir.genCommitted I G x s) (ir.padSpaceLate I l) c π) :=
    (agreeOnSourceVals_srcEnvC hwf hI hL R hA π).symm.crossBitsAt R.sourceValid R.srcNoMessage
      hA.crossBits
  have hcr := hsat.preds _ (predicate_mem M.hpid) hsrc
  rw [M.hb] at hcr
  obtain ⟨hx, hy⟩ := hcb _ (predicate_mem M.hpid) hsrc _ _ _ _ _ _ M.hb
  have hpo := hwf.predicates _ (predicate_mem M.hpid)
  rw [M.hb] at hpo
  have hyok : M.dy < ir.domains.length ∧ ir.ExprOk (ir.domainField M.dy) M.y := ⟨M.dyLt, M.yOk⟩
  refine ⟨hcr, hx, M.ybits_of hwf hI hL (fun _ _ hk i => reader_of_constant _ hk i) hx hy
    (by have := M.char; omega), fun j hj => ?_⟩
  obtain ⟨⟨h0, h1⟩, hc⟩ := exprIvl_within_of hwf hI hL (ivlFacts_srcEnvC hwf hI hL R hA π hbd)
    (ir.ivlTab_justified primeNodes S.ivlTrie ir.declaredRanges) hyok.1 M.char hyok.2 hw hj
  rcases (by omega : ir.evalIntWith (ir.reader (ir.srcEnvL I x (ir.genCommitted I G x s)
      (ir.padSpaceLate I l) c π)) M.dy M.y j = 0 ∨
      ir.evalIntWith (ir.reader (ir.srcEnvL I x (ir.genCommitted I G x s)
        (ir.padSpaceLate I l) c π)) M.dy M.y j = 1) with h | h
  · rw [← hc, h]
    simp
  · rw [← hc, h]
    simp

end MacBaseC

namespace MacBaseC

variable {G : Gens} (M : ir.MacBaseC primeNodes S G) {Inp : Type} (hG : ir.CGenFacts I G)
  (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp)
  (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)
  (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  (R : ir.CommittedFacts I G) {s l : ir.Valuation I}

set_option hygiene false in
/-- The honest environment of the honest inputs `y`. -/
local notation "HE" => ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hG stmtOf val SL y) c π

include hwf hI hL R in
/-- **The MAC's source facts hold at the certificate's honest environment** where the execution
accepts: they hold at the source environment of the honest committed
values (`source_srcEnvC`), with the honest committed values `genCommitted` (`hval`) and the source
late values the execution's in their pad spaces (`hSL`), and the operands read no late value, so
they read alike at the honest environment (`reader_honestEnvC_srcEnvL_of_noGen`). -/
theorem source_honestC (hA : ir.SourceAcceptingAt I (ir.execEnv I (stmtOf y) s l c))
    (hbd : ir.StmtBounded I (stmtOf y)) (hval : val y = ir.genCommitted I G (stmtOf y) s)
    (hSL : SL.late y c = ir.padSpaceLate I l) (hsrc : ir.inSource (ir.predicate M.pid) = true)
    (hw : IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField M.dy) M.y) 0 1) :
    M.Source (ir.reader HE) := by
  have hS := M.source_srcEnvC hwf hI hL R hA π hbd hsrc hw
  rw [← hval, ← hSL] at hS
  refine hS.congr M fun v hv => ?_
  refine (reader_honestEnvC_srcEnvL_of_noGen hG stmtOf val SL y c π ?_).symm
  rcases hv with hv | hv | hv
  · exact (M.xNoLate v hv).noGen
  · exact (M.cyNoLate v hv).noGen
  · rw [← M.units.2.1] at hv
    exact (M.yNoLate v hv).noGen

end MacBaseC

/-! ## The MAC checks over the fields of characteristic `2` -/

variable (ir primeNodes) in
/-- **A MAC check over a field of characteristic `2` with its tail, at the certificate's generators
`G`** (`TwoMacC`): the cross-field `equal` `pid` with its MAC
realization, the check over a field of characteristic `2` (`MacFieldCheckTwo`) with its domain `dy`,
operand `y` and blind `sb`; its tail `t`, the field `equal` `sb + macConv(r)(y) = bits(T)`
(`macTailTwoB`); and the facts its honest values need: the tag generated as this MAC's tag, a late
value and no source value; the operands read no late value; the blind is the tag's pad copy. Data
and properties of the program, decided per program. -/
structure TwoMacC (G : Gens) where
  /-- The cross-field `equal`. -/
  pid : ℕ
  /-- Its `x` domain. -/
  dx : ℕ
  /-- Its `x` operand. -/
  x : Expr
  /-- Its `y` domain. -/
  cdy : ℕ
  /-- Its `y` operand. -/
  cy : Expr
  /-- Its kind. -/
  k : CrossKind
  /-- Its MAC realization. -/
  real : MacRealization
  hpid : pid < ir.predicates.length
  hb : (ir.predicate pid).body = .cross dx x cdy cy k real
  /-- The check's domain. -/
  dy : ℕ
  /-- The check's operand. -/
  y : Expr
  /-- The check's blind. -/
  sb : ℕ
  hside : ir.MacFieldCheckTwo primeNodes pid dx x cdy cy k real dy y sb
  /-- The tail. -/
  t : ℕ
  ht : t < ir.predicates.length
  htB : ir.macTailTwoB pid dy y sb real t = true
  /-- The tag is generated as this MAC's tag. -/
  tagGen : G.at real.tag = .tag pid
  /-- The tag is no source value. -/
  tagNotSource : ¬ ir.IsSourceValue real.tag
  tagLate : ir.IsLate real.tag
  xNoLate : ∀ v ∈ ir.exprNodes x, ir.NoLateRead v
  cyNoLate : ∀ v ∈ ir.exprNodes cy, ir.NoLateRead v
  blindCopy : (ir.value sb).kind = .padCopy real.tag "polynomialBits"

namespace TwoMacC

variable {G : Gens} (M : ir.TwoMacC primeNodes G)

/-- **The MAC's two-tail shape** (`MacTwoCore`). -/
theorem twoTail : ir.MacTwoCore M.pid M.x M.cy M.k M.real := by
  rcases M.hside with ⟨b, -, -, h, -⟩ | ⟨bx, -, -, h, -⟩ <;> exact h

/-- **Both operands' domains have characteristic above `1`** (`MacChars`). -/
theorem chars : MacChars ir M.dx M.cdy := by
  rcases M.hside with ⟨b, -, -, -, h, -⟩ | ⟨bx, -, -, -, h, -⟩ <;> exact h

/-- **The check's facts** (`MacTwoFieldOk`). -/
theorem sideOk : ir.MacTwoFieldOk primeNodes M.pid M.dy M.y M.sb M.real := by
  rcases M.hside with ⟨b, -, -, -, -, h, h1, h2⟩ | ⟨bx, -, -, -, -, h, h1, h2⟩ <;> rw [h1, h2] <;>
    exact h

/-- **The check is over one of the cross-field `equal`'s operands.** -/
theorem side_eq : (M.dy = M.cdy ∧ M.y = M.cy) ∨ (M.dy = M.dx ∧ M.y = M.x) := by
  rcases M.hside with ⟨b, -, -, -, -, -, h1, h2⟩ | ⟨bx, -, -, -, -, -, h1, h2⟩
  exacts [.inr ⟨h1, h2⟩, .inl ⟨h1, h2⟩]

/-- **What holds of both operands holds of the check's operand.** -/
theorem side_of {P : ℕ → Expr → Prop} (hx : P M.dx M.x) (hy : P M.cdy M.cy) : P M.dy M.y := by
  rcases M.side_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> assumption

/-- **The check's operand is an expression of the cross-field `equal`.** -/
theorem side_mem : (M.dy, M.y) ∈ (PredBody.cross M.dx M.x M.cdy M.cy M.k M.real).exprs :=
  M.side_of (P := fun d z => (d, z) ∈ (PredBody.cross M.dx M.x M.cdy M.cy M.k M.real).exprs)
    (by simp [PredBody.exprs]) (by simp [PredBody.exprs])

/-- **The tag** (`macTagB`). -/
theorem tag : ir.macTagB M.real = true := by
  have h := M.twoTail
  exact h.tag

/-- **The cross-field `equal` compares bits.** -/
theorem width : M.k.width = 1 := by
  have h := M.twoTail
  exact h.width

/-- **The MAC field is a field of the program.** -/
theorem field : M.real.macField < ir.fields.length := by
  have h := M.twoTail
  exact h.field

/-- **The `x` operand has `chunks · width` coordinates.** -/
theorem lenX : ir.exprLen M.x = M.real.chunks * M.real.width := by
  have h := M.twoTail
  exact h.lenX

/-- **The cross-field `equal`'s `y` operand has `chunks · width` coordinates.** -/
theorem lenCy : ir.exprLen M.cy = M.real.chunks * M.real.width := by
  have h := M.twoTail
  exact h.lenY

/-- **The check's operand has `chunks · width` coordinates.** -/
theorem lenY : ir.exprLen M.y = M.real.chunks * M.real.width :=
  M.side_of (P := fun _ z => ir.exprLen z = M.real.chunks * M.real.width) M.lenX M.lenCy

/-- **The check's blind is one of the MAC's blinds.** -/
theorem blind_mem : M.sb ∈ M.real.blind.toList ++ M.real.blindX.toList := by
  rcases M.hside with ⟨b, hbx, -⟩ | ⟨bx, -, hbl, -⟩
  · exact List.mem_append_right _ (by rw [hbx]; simp)
  · exact List.mem_append_left _ (by rw [hbl]; simp)

/-- **No domain hosts the MAC**: it has a blind for `x`'s field. -/
theorem blindX_isSome : M.real.blindX.isSome = true := by
  rcases M.hside with ⟨b, hbx, -⟩ | ⟨bx, hbx, -⟩ <;> rw [hbx] <;> rfl

/-- **The `x` operand's domain has characteristic above `1`** (`MacChars`). -/
theorem one_lt_char_x : 1 < ir.charOf (ir.domainField M.dx) := M.chars.1

/-- **The `y` operand's domain has characteristic above `1`.** -/
theorem one_lt_char_cy : 1 < ir.charOf (ir.domainField M.cdy) := M.chars.2

/-- **The source facts the honest values of a MAC check over a field of characteristic `2` need**, at a reader `rd`: the cross-field `equal` holds and both operands read bits. -/
structure Source (rd : ir.Valuation I) : Prop where
  /-- The cross-field `equal` holds. -/
  cross : ir.HoldsWith rd (.cross M.dx M.x M.cdy M.cy M.k M.real)
  /-- The `x` operand reads bits. -/
  xbits : ∀ i < ir.exprLen M.x, ir.evalWith rd M.dx M.x i = 0 ∨ ir.evalWith rd M.dx M.x i = 1
  /-- The `y` operand reads bits. -/
  cybits : ∀ j < ir.exprLen M.cy, ir.evalWith rd M.cdy M.cy j = 0 ∨ ir.evalWith rd M.cdy M.cy j = 1

/-- **The source facts read only the operands.** -/
theorem Source.congr {rd rd' : ir.Valuation I}
    (h : ∀ v, v ∈ ir.exprNodes M.x ∨ v ∈ ir.exprNodes M.cy → rd v = rd' v)
    (hS : M.Source rd) : M.Source rd' := by
  have hx : ir.evalWith rd M.dx M.x = ir.evalWith rd' M.dx M.x :=
    funext fun i => congrFun (evalE_congr fun v hv => h v (Or.inl hv)) i
  have hy : ir.evalWith rd M.cdy M.cy = ir.evalWith rd' M.cdy M.cy :=
    funext fun i => congrFun (evalE_congr fun v hv => h v (Or.inr hv)) i
  refine ⟨(holdsWith_congr fun v hv => h v ?_).1 hS.cross, ?_, ?_⟩
  · simpa [predNodes, PredBody.exprs, tableCols] using hv
  · rw [← hx]
    exact hS.xbits
  · rw [← hy]
    exact hS.cybits

/-- **The check's operand reads bits** where the source facts hold. -/
theorem Source.ybits {rd : ir.Valuation I} (hS : M.Source rd) :
    ∀ j < ir.exprLen M.y, ir.evalWith rd M.dy M.y j = 0 ∨ ir.evalWith rd M.dy M.y j = 1 :=
  M.side_of (P := fun d z => ∀ j < ir.exprLen z, ir.evalWith rd d z j = 0 ∨ ir.evalWith rd d z j = 1)
    hS.xbits hS.cybits

/-- **The honest tag is the MAC of the chunks of the check's operand**:
where the tag is honest (`MacTagAt`: the `x` operand's chunks, no domain hosting the MAC) and the
source facts hold, the tag is the MAC of `x`'s chunks, which are the chunks of the check's operand
or agree with them (`evalWith_eq_one_iff_of_cross`). -/
theorem Source.sideTag {rd : ir.Valuation I} (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes)
    (hS : M.Source rd) {β : (I M.real.macField).K} (hT : ir.MacTagAt rd M.dx M.x M.real β) :
    (castElt (rd M.real.tag 0) : (I M.real.macField).K) =
      ∑ c : Fin M.real.chunks, β ^ ((c : ℕ) + 1) *
        ir.macChunkA rd M.real.macField M.dy M.y M.real.width c := by
  obtain ⟨bx, hbx⟩ := Option.isSome_iff_exists.1 M.blindX_isSome
  unfold MacTagAt at hT
  rw [hbx] at hT
  unfold MacTwoTagAt at hT
  rw [hT]
  rcases M.side_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [h1, h2]
    refine macChunkA_congr fun i => ?_
    have hidx : (c : ℕ) * M.real.width + i < ir.exprLen M.x := by
      rw [M.lenX]
      have := c.2
      have := i.2
      nlinarith
    rw [evalPad_of_lt hidx, evalPad_of_lt (by rw [M.lenCy, ← M.lenX]; exact hidx)]
    exact evalWith_eq_one_iff_of_cross hwf hL M.hpid M.hb M.width hS.cross hS.xbits M.one_lt_char_x
      M.one_lt_char_cy (fun j hj => hS.cybits j (by rw [M.lenCy, ← M.lenX]; exact hj)) hidx
  · rw [h1, h2]

variable {Inp : Type} (hgen : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I)
  (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)

set_option hygiene false in
local notation "HE" =>
  ir.reader (ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hgen stmtOf val SL y) c π)

/-- **The MAC's honest tag** (`MacTagAt`; `macTagC_honest`) at the honest environment of the
certificate. -/
theorem macTag_honest :
    ir.MacTagAt HE M.dx M.x M.real (castElt ((ir.honestEnv I (stmtOf y) (val y)
        (ir.genLateOf I hgen stmtOf val SL y) c π).chal M.real.key 0)) :=
  macTagC_honest hgen stmtOf val SL y c π M.hb M.tag M.tagGen M.tagNotSource M.tagLate M.xNoLate

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  (hM : I.MacModel ir)

include hwf hI hL hM in
/-- **The tail holds at the honest values** (`tailTwo_holds_of_honest`): the
honest tag (`macTagC_honest`) as the MAC of the chunks of the check's operand (`Source.sideTag`),
the blind the pad copy (`macBlinds_honestEnv`), the check's operand reading bits. -/
theorem tail_honest (hB : ir.BlindsArePadCopies) (hS : M.Source HE) :
    ir.HoldsWith HE (ir.predicate M.t).body := by
  have hpo := hwf.predicates _ (predicate_mem M.hpid)
  rw [M.hb] at hpo
  have hyok := hpo.1 (M.dy, M.y) M.side_mem
  exact tailTwo_holds_of_honest hwf hI hL hM _ hyok.1 M.lenY M.field M.tag M.sideOk.blindField
    M.sideOk.blindSize M.ht M.htB
    (hS.sideTag M hwf hL (M.macTag_honest hgen stmtOf val SL y c π))
    (macBlinds_honestEnv hB (stmtOf y) (val y) _ c π _ (predicate_mem M.hpid) _ _ _ _ _ _ M.hb M.sb
      M.blind_mem)
    (hS.ybits M)

end TwoMacC

/-- **`twoMacCB` is sound** (`TwoMacFactsC`). -/
theorem twoMacFactsC_of_B {G : Gens} {st : MacSite} (h : ir.twoMacCB primeNodes G st = true) :
    ir.TwoMacFactsC (primeNodes := primeNodes) G st :=
  of_decide_eq_true h

namespace TwoMacFactsC

variable {G : Gens} {st : MacSite} (F : ir.TwoMacFactsC (primeNodes := primeNodes) G st)
include F

/-- **The site's predicate is its cross-field `equal`** (`body_eq_macCross`). -/
theorem hb : (ir.predicate st.pid).body = .cross (ir.macCross st.pid).dx (ir.macCross st.pid).x
    (ir.macCross st.pid).dy (ir.macCross st.pid).y (ir.macCross st.pid).k (ir.macCross st.pid).real :=
  body_eq_macCross F.cross

/-- **The tail is a predicate of the program** (`macTailTwoB`). -/
theorem tail_lt : ir.twoTail st < ir.predicates.length := by
  have h := F.tail
  unfold macTailTwoB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

/-- **The site's MAC check over its field** (`MacFieldCheckTwo`): the MAC's
interval-free two-tail shape from the structural checks (`hreal`, `MacTwoCore`) and the site's check over
a field of characteristic `2`. -/
theorem side (hreal : ir.MacsRealizable primeNodes) :
    ir.MacFieldCheckTwo primeNodes st.pid (ir.macCross st.pid).dx (ir.macCross st.pid).x
      (ir.macCross st.pid).dy (ir.macCross st.pid).y (ir.macCross st.pid).k
      (ir.macCross st.pid).real (ir.siteDom st) (ir.siteOp st) (ir.macBlind st) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 F.blind
  obtain ⟨bx, hx⟩ := Option.isSome_iff_exists.1 F.blindX
  have hRz := hreal.macs _ F.lt _ _ _ _ _ _ F.hb
  simp only [macCoreOkB] at hRz
  rw [hx, hb] at hRz
  have hc := MacTwoCore.of_B hRz
  have hs := macTwoFieldOk_of_atB F.sideOk
  have hbs : ir.macBlind st = if st.xSide then bx else b := by simp [macBlind, hx, hb]
  cases hxs : st.xSide
  · simp only [hxs, Bool.false_eq_true, ite_false] at hbs
    simp only [siteDom, siteOp, hxs, Bool.false_eq_true, ite_false, hbs] at hs ⊢
    exact Or.inr ⟨bx, hx, hb, hc, F.chars, hs, rfl, rfl⟩
  · simp only [hxs, ite_true] at hbs
    simp only [siteDom, siteOp, hxs, ite_true, hbs] at hs ⊢
    exact Or.inl ⟨b, hx, hb, hc, F.chars, hs, rfl, rfl⟩

end TwoMacFactsC

variable (primeNodes) in
/-- **The MAC check over the field of characteristic `2` of site `st` with its tail, at the
certificate's generators** (`TwoMacC`), from the covered MAC realizations (`hreal`)
and the check `twoMacCB`. -/
def TwoMacC.ofB (hwf : ir.WellFormed) (hreal : ir.MacsRealizable primeNodes) {G : Gens}
    (st : MacSite) (h : ir.twoMacCB primeNodes G st = true) : ir.TwoMacC primeNodes G where
  pid := st.pid
  dx := (ir.macCross st.pid).dx
  x := (ir.macCross st.pid).x
  cdy := (ir.macCross st.pid).dy
  cy := (ir.macCross st.pid).y
  k := (ir.macCross st.pid).k
  real := (ir.macCross st.pid).real
  hpid := (twoMacFactsC_of_B h).lt
  hb := (twoMacFactsC_of_B h).hb
  dy := ir.siteDom st
  y := ir.siteOp st
  sb := ir.macBlind st
  hside := (twoMacFactsC_of_B h).side hreal
  t := ir.twoTail st
  ht := (twoMacFactsC_of_B h).tail_lt
  htB := (twoMacFactsC_of_B h).tail
  tagGen := (twoMacFactsC_of_B h).tagGen
  tagNotSource := (twoMacFactsC_of_B h).tagNotSource
  tagLate := (twoMacFactsC_of_B h).tagLate
  xNoLate := fun _ hv => noLateRead_of_B hwf ((twoMacFactsC_of_B h).xNoLate _ hv)
  cyNoLate := fun _ hv => noLateRead_of_B hwf ((twoMacFactsC_of_B h).yNoLate _ hv)
  blindCopy := kind_of_isPadCopyB (twoMacFactsC_of_B h).blindCopy

namespace TwoMacC

variable {G : Gens} (M : ir.TwoMacC primeNodes G) {Inp : Type} (hG : ir.CGenFacts I G)
  (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp)
  (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)
  (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  (R : ir.CommittedFacts I G) {s l : ir.Valuation I}

set_option hygiene false in
/-- The honest environment of the honest inputs `y`. -/
local notation "HE" => ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hG stmtOf val SL y) c π

include hwf hI hL R in
/-- **The source facts of a MAC check over a field of characteristic `2` hold at the certificate's
honest environment** where the execution accepts: at the source
environment of the honest committed values the cross-field `equal`, a source predicate (`hsrc`),
holds and reads bits (`SourceAcceptingAt.crossBits`), with the honest committed values
`genCommitted` (`hval`) and the source late values the execution's in their pad spaces (`hSL`); the
operands read no late value, so they read alike at the honest environment. -/
theorem source_honestC (hA : ir.SourceAcceptingAt I (ir.execEnv I (stmtOf y) s l c))
    (hval : val y = ir.genCommitted I G (stmtOf y) s) (hSL : SL.late y c = ir.padSpaceLate I l)
    (hsrc : ir.inSource (ir.predicate M.pid) = true) :
    M.Source (ir.reader HE) := by
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  have hcb : ir.CrossBitsAt I
      (ir.srcEnvL I (stmtOf y) (ir.genCommitted I G (stmtOf y) s) (ir.padSpaceLate I l) c π) :=
    (agreeOnSourceVals_srcEnvC hwf hI hL R hA π).symm.crossBitsAt R.sourceValid R.srcNoMessage
      hA.crossBits
  have hcr := hsat.preds _ (predicate_mem M.hpid) hsrc
  rw [M.hb] at hcr
  obtain ⟨hx, hy⟩ := hcb _ (predicate_mem M.hpid) hsrc _ _ _ _ _ _ M.hb
  have hS : M.Source (ir.reader
      (ir.srcEnvL I (stmtOf y) (ir.genCommitted I G (stmtOf y) s) (ir.padSpaceLate I l) c π)) :=
    ⟨hcr, hx, hy⟩
  rw [← hval, ← hSL] at hS
  refine hS.congr M fun v hv => ?_
  refine (reader_honestEnvC_srcEnvL_of_noGen hG stmtOf val SL y c π ?_).symm
  rcases hv with hv | hv
  · exact (M.xNoLate v hv).noGen
  · exact (M.cyNoLate v hv).noGen

end TwoMacC

end

end GordieHowe.RealizedProgram
