-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Digits
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the MAC of `MLDSA44.Emulated.QROMParams` with its digit tail

The program facts of the honest strategy from an execution (`GordieHowe.RealizedProgram.HonestStrategy.ofCompletion`) on the
realized program of `MLDSA44.Emulated.QROMParams` (export `c825eb05`): its one MAC `mac.equal` with the
ungrouped digit tail `mac` (`mac`, a `GordieHowe.RealizedProgram.DigitsMac`: the accumulator `mac.acc`, the lower
digit `mac.low`, the derived top digit, radix `116`), each fact by `decide +kernel`.
-/

namespace GordieHowe.MLDSA44.Emulated.QROMParams.Honest

open RealizedProgram

/-- **The realized program.** -/
noncomputable abbrev Pg : RealizedProgram := Generated.MLDSA44.Emulated.QROMParams.Program.program

/-- **The plan's prime-subfield nodes.** -/
noncomputable abbrev PN : ℕ → List String :=
  primeNodesOf Generated.MLDSA44.Emulated.QROMParams.Plan.plan Generated.MLDSA44.Emulated.QROMParams.Program.program

/-- **The MAC realization** of `mac.equal` (predicate `275`). -/
noncomputable def real : MacRealization :=
  match (Pg.predicate 275).body with
  | .cross _ _ _ _ _ r => r
  | _ => default
/-- **The realization of the MAC's tail** `mac` (predicate `273`). -/
noncomputable def realT : ModRealization :=
  match (Pg.predicate 273).body with
  | .mod _ _ _ _ r => r
  | _ => default
/-- **The left side of the MAC's tail.** -/
noncomputable def L : Expr :=
  match (Pg.predicate 273).body with
  | .mod _ _ l _ _ => l
  | _ => default
/-- **The units of the MAC's tail**: the blind, the powers and the A operand. -/
noncomputable def u : MacUnits := (macUnits? L).getD ⟨0, 0, 0, 0, [], default⟩
/-- **`mac.equal` is the cross-field `equal` of `ref 527` (domain `H`) and `ref 6` (domain `A`).** -/
theorem hb : (Pg.predicate 275).body = .cross 1 (.ref 527) 0 (.ref 6) {} real := rfl
/-- **The tail is a `mod_2` of domain `0` with right side the target's bits `574`.** -/
theorem hbt : (Pg.predicate 273).body = .mod 0 2 L (.leaf 574) realT := rfl
/-- **The blind `569` is the pad copy `polynomialBits` of the tag `572`.** -/
theorem kind569 : (Pg.value 569).kind = .padCopy real.tag "polynomialBits" :=
  RealizedProgram.kind_of_isPadCopyB (by decide +kernel)

set_option maxRecDepth 4096 in
/-- **The program's MAC with its tail** (`RealizedProgram.MacBase`), every fact by `decide +kernel`. -/
noncomputable def macBase : Pg.MacBase PN where
  pid := 275
  dx := 1
  x := .ref 527
  cdy := 0
  cy := .ref 6
  dy := 0
  y := .ref 6
  k := {}
  real := real
  hpid := by decide +kernel
  hb := hb
  sb := 569
  hside := Or.inl ⟨RealizedProgram.MacHostedCore.of_B (by decide +kernel),
    rfl, zeroPadB_self (by decide +kernel), rfl, by decide +kernel⟩
  dyLt := by decide +kernel
  yOk := by decide +kernel
  t := 273
  ht := by decide +kernel
  htB := by decide +kernel
  realT := realT
  L := L
  R := .leaf 574
  hbt := hbt
  u := u
  hu := rfl
  tagOwn := by decide +kernel
  tagHist := by decide +kernel
  tagLate := by decide +kernel
  xNoLate := fun v hv => noLateRead_of_B Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed
    (List.all_eq_true.1 (by decide +kernel : ((Pg.exprNodes (.ref 527)).all Pg.noLateReadB) = true) v hv)
  cyNoLate := fun v hv => noLateRead_of_B Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed
    (List.all_eq_true.1 (by decide +kernel : ((Pg.exprNodes (.ref 6)).all Pg.noLateReadB) = true) v hv)
  yNoLate := fun v hv => noLateRead_of_B Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed
    (List.all_eq_true.1 (by decide +kernel : ((Pg.exprNodes u.operand).all Pg.noLateReadB) = true) v hv)
  powNoLate := noLateRead_of_B Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed (by decide +kernel)
  blindCopy := kind569
  macChar := by decide +kernel

set_option maxRecDepth 4096 in
/-- **The program's MAC with a digit tail** (`RealizedProgram.DigitsMac`), every fact by `decide +kernel`
through the checkers of `GordieHowe/Language/Honest/Source.lean` and
`GordieHowe/Language/Honest/Digits.lean`. -/
noncomputable def mac : Pg.DigitsMac PN where
  toMacBase := macBase
  acc := 575
  low := 576
  top := .ref 12
  hdig := rfl
  hT := by decide +kernel
  hacc := by decide +kernel
  accRow := by decide +kernel
  derived := by decide +kernel
  accOwn := by decide +kernel
  accTag := by decide +kernel
  accGr := by decide +kernel
  accDig := by decide +kernel
  accHist := by decide +kernel
  accLt := by decide +kernel
  accLate := by decide +kernel
  accField := by decide +kernel
  lowOwn := by decide +kernel
  lowTag := by decide +kernel
  lowGr := by decide +kernel
  lowDig := by decide +kernel
  lowHist := by decide +kernel
  lowDAcc := by decide +kernel
  lowLt := by decide +kernel
  lowLate := by decide +kernel
  lowField := by decide +kernel
  lowSize := by decide +kernel
  accSize := by decide +kernel
  topLen := by decide +kernel
  lNoLate := fun v hv => noLateRead_of_B Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed
    (List.all_eq_true.1 (by decide +kernel : ((Pg.exprNodes L).all Pg.noLateReadB) = true) v hv)
  hw := by decide +kernel
  convFit := by decide +kernel
  accMax := by
    have hw : macBase.u.width = 256 := by decide +kernel
    have ht : macBase.u.taps.toFinset = GordieHowe.Conv.gf2_256Taps := by decide +kernel
    rw [hw, ht, GordieHowe.Conv.convMax_gf2_256]
    decide +kernel
  radixPos := by decide +kernel
  radixChar := by decide +kernel
  lowRoom := lowRoom_of_B (by decide +kernel)
  topRoom := by
    have hw : macBase.u.width = 256 := by decide +kernel
    have ht : macBase.u.taps.toFinset = GordieHowe.Conv.gf2_256Taps := by decide +kernel
    rw [hw, ht, GordieHowe.Conv.convMax_gf2_256]
    exact topRoom_of_B (by decide +kernel)
  wrapRoom := by
    have hw : macBase.u.width = 256 := by decide +kernel
    have ht : macBase.u.taps.toFinset = GordieHowe.Conv.gf2_256Taps := by decide +kernel
    rw [hw, ht, GordieHowe.Conv.convMax_gf2_256]
    exact wrapRoom_of_B (by decide +kernel)

end GordieHowe.MLDSA44.Emulated.QROMParams.Honest
