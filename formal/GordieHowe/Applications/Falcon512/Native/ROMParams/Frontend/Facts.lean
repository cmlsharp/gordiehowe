-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Basic
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Interp

@[expose] public section

/-!
# GordieHowe frontend: the program facts of `Falcon512.Native.ROMParams`

The program facts the native Falcon frontend reads (`FalconHBase`, decided on the tables of
`GordieHowe.Generated.Falcon512.Native.ROMParams.Program.program`, export `c825eb05`) and the selection's labels
in `GF(2^128)` (`FalconHConsts program gf128`: entry `j` of the constant `39` is `g^j`, checked in
the spread representation `gf2_128Exec`, `gpow_chain`, `gN_chain`).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program (program)
open GF2_128Exec

/-- The values the extractor reads read nothing from the run (`RealizedProgram.nodeReads`). -/
theorem srcReads_nil : ∀ v ∈ [45, 46, 47, 540, 545, 546],
    program.nodeReads program.fuel v = [] := by
  decide +kernel

/-- `statement.hhat` is a value of field `1`. -/
theorem hhatField : program.valueField 544 = 1 := (show 1 = program.valueField 544 by decide +kernel).symm

/-- The selection's predicates are `h2p.select.start`, `.step`, `.done` and `.route`, source predicates. -/
theorem selectPreds :
    program.predByName "h2p.select.start" = some 246 ∧
    program.predByName "h2p.select.step" = some 247 ∧
    program.predByName "h2p.select.done" = some 248 ∧
    program.predByName "h2p.select.route" = some 249 ∧
    (∀ p ∈ [246, 247, 248, 249], program.inSource (program.predicate p) = true) := by
  decide +kernel

/-- The selection has the first-`n` shape at `(S, n, w) = (639, 512, 16)`. -/
theorem selectShape_eq :
    program.selectShape? 639 512 16 246 247 248 249 = some selShape := by
  decide +kernel

/-- Domains `H` and `A` have fields `0` and `1`. -/
theorem domainField0 :
    program.domainField 0 = 0 := by
  decide +kernel

/-- Domain `A` has field `1`. -/
theorem domainField1 :
    program.domainField 1 = 1 := by
  decide +kernel

/-- The selection's constants are values of domain `H`. -/
theorem selConstField :
    ∀ v ∈ [26, 0, 35, 37, 33, 34, 36, 38, 39, 32], program.valueField v = 0 := by
  decide +kernel

/-- The entries of the selection's constants other than the labels. -/
theorem const_entries :
    (program.constEntries 39).getD 0 0 = 1 ∧ (program.constEntries 26).getD 0 0 = 1 ∧
    (program.constEntries 0).getD 0 0 = 0 ∧
    (∀ i < 638, (program.constEntries 35).getD i 0 = 0) ∧
    (∀ t < 127, (program.constEntries 37).getD t 0 = 0) ∧
    (∀ t < 127, (program.constEntries 33).getD t 0 = 1) ∧
    (program.constEntries 34).getD 0 0 = (program.constEntries 39).getD 1 0 ∧
    (∀ u < 16, (program.constEntries 38).getD u 0 = (program.constEntries 39).getD u 0) ∧
    (∀ u < 16, (program.constEntries 32).getD u 0 = 61445 / 2 ^ u % 2) := by
  decide +kernel

/-- `δ`'s field is its challenge's. -/
theorem deltaField :
    program.chalField 0 = program.valueField 543 := by
  decide +kernel

/-- The selection's committed values read nothing from the run. -/
theorem selReads_nil :
    ∀ v ∈ 541 :: 542 :: 540 :: program.exprNodes (.ref 489),
    program.nodeReads program.fuel v = [] := by
  decide +kernel

/-- Challenge `0` is full, of one coordinate, in field `0`. -/
theorem chal0 :
    (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧
    program.chalField 0 = 0 := by
  decide +kernel

/-- `select.raw` is a bit view; it and `c_A` have `8192` coordinates. -/
theorem raw_facts :
    program.isBitView 540 = true ∧ (program.value 540).size = 8192 ∧
    (program.value 545).size = 8192 := by
  decide +kernel

/-- The member check `falcon_key_canonical [12289]` of `hhat`. -/
theorem hhatCheck :
    RealizedProgram.MemberCheck.mk "hhat" 0 1024 "falcon_key_canonical" [12289] ∈
    program.statement.checks := by
  decide +kernel

/-- `hhat` is value `544`. -/
theorem hhatValue :
    program.memberValue? "hhat" = some 544 := by
  decide +kernel

/-- `hhat` has `512` coordinates. -/
theorem hhatSize :
    (program.value 544).size = 512 := by
  decide +kernel

/-- The program's shared expressions read only earlier entries. -/
theorem refsOrdered : program.RefsOrdered :=
  (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)

/-- The program of `Falcon512.Native.ROMParams` has the native Falcon frontend's program facts. -/
instance : FalconHBase program where
  selectPreds := selectPreds
  selectShape_eq := selectShape_eq
  refsOrdered := refsOrdered
  domainField0 := domainField0
  selConstField := selConstField
  const_entries := const_entries
  deltaKind := RealizedProgram.Kind.eq_of_challenge? (by decide +kernel)
  deltaField := deltaField
  selReads_nil := selReads_nil
  chal0 := chal0
  isSourceChal_iff j := by
    constructor
    · intro h
      have hj : j < 3 := h.1
      have key : ∀ j < 3, program.IsSourceChal j → j = 0 := by decide +kernel
      exact key j hj h
    · rintro rfl
      decide +kernel

/-- The native program has the Falcon frontend's program facts about domain `A`, at `c_A = 545`,
`s2 = 546`. -/
instance : FalconACore program where
  cA := 545
  s2 := 546
  domainField1 := domainField1
  macEqual := ⟨285, by decide +kernel, by decide +kernel, by decide +kernel⟩
  cABoolean := ⟨268, by decide +kernel, by decide +kernel, by decide +kernel⟩
  raw_facts := raw_facts
  hhatCheck := hhatCheck
  hhatValue := hhatValue
  hhatSize := hhatSize
  hhatField := hhatField
  srcReads_nil := srcReads_nil

/-- **The labels `g^j` as spread products**: entry `j + 1` of the constant `39` is entry `j` times
`g`, checked in the spread representation (`gf2_128Exec`). -/
theorem gpow_chain : ∀ j < 511, gf2_128Exec.mul
    (gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 39).getD j 0)).toNat)
    (gf2_128Exec.ofBits gf2_128SubfieldGenBV.toNat) =
    gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 39).getD (j + 1) 0)).toNat := by
  decide +kernel

/-- **`g^512` as a spread product**: the constant `36` is entry `511` of `39` times `g`. -/
theorem gN_chain : gf2_128Exec.mul
    (gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 39).getD 511 0)).toNat)
    (gf2_128Exec.ofBits gf2_128SubfieldGenBV.toNat) =
    gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 36).getD 0 0)).toNat := by
  decide +kernel

/-- **Entry `j` of the constant `39` is `g^j`** (`gpow_chain`, from entry `0 = 1`). -/
theorem gf2_128OfNat_gpow : ∀ j < 512,
    gf2_128OfNat ((program.constEntries 39).getD j 0) = gf2_128SubfieldGen ^ j
  | 0, _ => by rw [(FalconHBase.const_entries (program := program)).1, gf2_128OfNat_one, pow_zero]
  | j + 1, hj => by
    have hmul := gfMul_eq_of_spread (gpow_chain j (by omega))
    have := congrArg gf2_128OfBitVec hmul
    rw [gf2_128OfBitVec_gfMul, gf2_128OfBitVec_subfieldGenBV] at this
    change gf2_128OfNat _ * _ = gf2_128OfNat _ at this
    rw [← this, gf2_128OfNat_gpow j (by omega), pow_succ]

/-- The selection labels of the program of `Falcon512.Native.ROMParams` in `GF(2^128)`. -/
instance : FalconHConsts program RealizedProgram.gf128 where
  gpow := gf2_128OfNat_gpow
  gN := by
    have hmul := congrArg gf2_128OfBitVec (gfMul_eq_of_spread gN_chain)
    rw [gf2_128OfBitVec_gfMul, gf2_128OfBitVec_subfieldGenBV] at hmul
    change gf2_128OfNat _ * _ = gf2_128OfNat _ at hmul
    change gf2_128OfNat _ = gf2_128SubfieldGen ^ 512
    rw [← hmul, gf2_128OfNat_gpow 511 (by omega), ← pow_succ]
    rfl

set_option maxRecDepth 8192 in
/-- The selection field of the program of `Falcon512.Native.ROMParams` is `GF(2^128)`, with its labels. -/
instance : FalconSelField program RealizedProgram.gf128 RealizedProgram.fq9 where
  inst := inferInstanceAs (HField RealizedProgram.gf128)
  bits_eq := rfl
  gpow := gf2_128OfNat_gpow
  gN := FalconHConsts.gN (program := program) (FH := RealizedProgram.gf128)

end GordieHowe.Falcon512.Native.ROMParams
