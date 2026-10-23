-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Source
public import GordieHowe.Generated.Falcon512.Native.QROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the honest prover's MAC of `Falcon512.Native.QROMParams`

The program facts of the honest strategy from an execution (`GordieHowe.RealizedProgram.HonestStrategy.ofCompletion`) on the
realized program of `Falcon512.Native.QROMParams` (export `c825eb05`): its one MAC `mac.equal` with the
grouped tail `mac` (`mac`, a `GordieHowe.RealizedProgram.GroupedMac`), each fact by `decide +kernel`.
-/

namespace GordieHowe.Falcon512.Native.QROMParams.Honest

open RealizedProgram

/-- **The realized program.** -/
noncomputable abbrev Pg : RealizedProgram := Generated.Falcon512.Native.QROMParams.Program.program

/-- **The plan's prime-subfield nodes.** -/
noncomputable abbrev PN : ℕ → List String :=
  primeNodesOf Generated.Falcon512.Native.QROMParams.Plan.plan Generated.Falcon512.Native.QROMParams.Program.program

/-- **The MAC realization** of `mac.equal` (predicate `285`). -/
noncomputable def real : MacRealization :=
  match (Pg.predicate 285).body with
  | .cross _ _ _ _ _ r => r
  | _ => default
/-- **The realization of the MAC's tail** `mac` (predicate `283`). -/
noncomputable def realT : ModRealization :=
  match (Pg.predicate 283).body with
  | .mod _ _ _ _ r => r
  | _ => default
/-- **The left side of the MAC's tail.** -/
noncomputable def L : Expr :=
  match (Pg.predicate 283).body with
  | .mod _ _ l _ _ => l
  | _ => default
/-- **The right side of the MAC's tail.** -/
noncomputable def R : Expr :=
  match (Pg.predicate 283).body with
  | .mod _ _ _ r _ => r
  | _ => default
/-- **The grouping of the MAC's tail.** -/
noncomputable def G : GroupedMod := realT.grouped.getD default
/-- **The units of the MAC's tail**: the blind, the powers and the A operand. -/
noncomputable def u : MacUnits := (macUnits? L).getD ⟨0, 0, 0, 0, [], default⟩
/-- **`mac.equal` is the cross-field `equal` of `x_H = 540` and `y_A = 545`.** -/
theorem hb : (Pg.predicate 285).body = .cross 0 (.leaf 540) 1 (.leaf 545) {} real := rfl
/-- **The tail is a `mod_2` of domain `1`.** -/
theorem hbt : (Pg.predicate 283).body = .mod 1 2 L R realT := rfl
/-- **The honest accumulators' quotients fit their two base-`64` digits**: a group of eight
chunks sums to at most `8 · 1017` (`Conv.convMax_gf2_256`). -/
theorem fit : ∀ fc ∈ G.groups, fc.2 * GordieHowe.Conv.convMax u.width u.taps.toFinset / 2 < G.base ^ G.digitCount := by
  have hw : u.width = 256 := by decide +kernel
  have ht : u.taps.toFinset = GordieHowe.Conv.gf2_256Taps := by decide +kernel
  rw [hw, ht, GordieHowe.Conv.convMax_gf2_256]
  decide +kernel
/-- **The blind `557` is the pad copy `polynomialBits` of the tag `560`.** -/
theorem kind557 : (Pg.value 557).kind = .padCopy real.tag "polynomialBits" :=
  RealizedProgram.kind_of_isPadCopyB (by decide +kernel)
/-- **The program's MAC with a grouped tail** (`RealizedProgram.GroupedMac`), every fact by
`decide +kernel` through the checkers of `GordieHowe/Language/Honest/Source.lean`. -/
noncomputable def mac : Pg.GroupedMac PN where
  pid := 285
  dx := 0
  x := .leaf 540
  cdy := 1
  cy := .leaf 545
  dy := 1
  y := .leaf 545
  k := {}
  real := real
  hpid := by decide +kernel
  hb := hb
  sb := 557
  hside := Or.inl ⟨RealizedProgram.MacHostedCore.of_B (by decide +kernel),
    rfl, zeroPadB_self (by decide +kernel), rfl, by decide +kernel⟩
  dyLt := by decide +kernel
  yOk := by decide +kernel
  t := 283
  ht := by decide +kernel
  htB := by decide +kernel
  realT := realT
  L := L
  R := R
  hbt := hbt
  hgf := by decide +kernel
  G := G
  hG := rfl
  u := u
  hu := rfl
  acc := 567
  hA := rfl
  gq := 568
  hD := rfl
  tagOwn := by decide +kernel
  tagHist := by decide +kernel
  tagLate := by decide +kernel
  accOwn := by decide +kernel
  accTag := by decide +kernel
  accHist := by decide +kernel
  accLt := by decide +kernel
  accLate := by decide +kernel
  accField := by decide +kernel
  gqOwn := by decide +kernel
  gqTag := by decide +kernel
  gqAcc := by decide +kernel
  gqHist := by decide +kernel
  gqLt := by decide +kernel
  gqLate := by decide +kernel
  gqField := by decide +kernel
  xNoLate := fun v hv => noLateRead_of_B Generated.Falcon512.Native.QROMParams.Valid.wellFormed
    (List.all_eq_true.1 (by decide +kernel : ((Pg.exprNodes (.leaf 540)).all Pg.noLateReadB) = true) v hv)
  cyNoLate := fun v hv => noLateRead_of_B Generated.Falcon512.Native.QROMParams.Valid.wellFormed
    (List.all_eq_true.1 (by decide +kernel : ((Pg.exprNodes (.leaf 545)).all Pg.noLateReadB) = true) v hv)
  yNoLate := fun v hv => noLateRead_of_B Generated.Falcon512.Native.QROMParams.Valid.wellFormed
    (List.all_eq_true.1 (by decide +kernel : ((Pg.exprNodes u.operand).all Pg.noLateReadB) = true) v hv)
  powNoLate := noLateRead_of_B Generated.Falcon512.Native.QROMParams.Valid.wellFormed (by decide +kernel)
  blindCopy := kind557
  fit := fit
  macChar := by decide +kernel
  digitsRoom := digitsRoom_of_B (by decide +kernel)
  finalRoom := finalRoom_of_B (by decide +kernel)
end GordieHowe.Falcon512.Native.QROMParams.Honest
