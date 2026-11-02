-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Frontend.Basic
public import GordieHowe.Generated.Falcon512.Emulated.QROMParams.Structure
public import GordieHowe.Language.RealizedProgram.MemberValues
public import GordieHowe.Applications.FieldInterps.Odd
public import GordieHowe.Generated.Falcon512.Emulated.QROMParams.Plan
public import GordieHowe.Generated.Falcon512.Emulated.QROMParams.Interp
public import GordieHowe.Generated.Falcon512.Emulated.QROMParams.Facts.Model

@[expose] public section

/-!
# GordieHowe frontend: the program facts of `Falcon512.Emulated.QROMParams`

The program facts the Falcon frontend reads
(`FalconHBase`, `FalconACore`, decided on the tables of
`GordieHowe.Generated.Falcon512.Emulated.QROMParams.Program.program`, export `5d9fe0d5`) and the
selection's labels in `GF(2^256)` (`FalconHConsts program gf256`, `FalconSelField program gf256
gold4`: entry `j` of the constant `39` is `g^j`, checked in the spread representation
`gf2_256Exec`, `gpow_chain`, `gN_chain`, read in `GF(2^256)` by
`GordieHowe.gf2_256OfNat_mul_of_spread`). Domain `H` of the emulated program has the native
program's numbering, so these are the native program's facts at the emulated program; domain `A`
holds `c_A` and `s2` at `595` and `596`, one id later than the native program, after
`key.coefficients` (`594`).
-/

namespace GordieHowe.Falcon512.Emulated.QROMParams

open Generated.Falcon512.Emulated.QROMParams.Program (program)

/-- The values the extractor reads read nothing from the run (`RealizedProgram.nodeReads`). -/
theorem srcReads_nil : ∀ v ∈ [45, 46, 47, 589, 595, 596],
    program.nodeReads program.fuel v = [] := by
  decide +kernel

/-- `statement.hhat` is a value of field `1`. -/
theorem hhatField : program.valueField 593 = 1 := (show 1 = program.valueField 593 by decide +kernel).symm

/-- The selection's predicates are `h2p.select.start`, `.step`, `.done` and `.route`, source predicates. -/
theorem selectPreds :
    program.predNameB 270 "h2p.select.start" = true ∧
    program.predNameB 271 "h2p.select.step" = true ∧
    program.predNameB 272 "h2p.select.done" = true ∧
    program.predNameB 273 "h2p.select.route" = true ∧
    (∀ p ∈ [270, 271, 272, 273], program.inSource (program.predicate p) = true) := by
  decide +kernel

/-- The selection has the first-`n` shape at `(S, n, w) = (717, 512, 16)`. -/
theorem selectShape_eq :
    program.selectShape? 717 512 16 270 271 272 273 = some selShape := by
  decide +kernel

/-- Domain `H` has field `0`. -/
theorem domainField0 :
    program.domainField 0 = 0 := by
  decide +kernel

/-- Domain `A` has field `1`. -/
theorem domainField1 :
    program.domainField 1 = 1 := by
  decide +kernel

/-- The selection's constants are values of domain `H`. -/
theorem selConstField :
    ∀ v ∈ [25, 27, 35, 37, 33, 34, 36, 38, 39, 32], program.valueField v = 0 := by
  decide +kernel

/-- The entries of the selection's constants other than the labels. -/
theorem const_entries :
    (program.constEntries 39).getD 0 0 = 1 ∧ (program.constEntries 25).getD 0 0 = 1 ∧
    (program.constEntries 27).getD 0 0 = 0 ∧
    (∀ i < 716, (program.constEntries 35).getD i 0 = 0) ∧
    (∀ t < 205, (program.constEntries 37).getD t 0 = 0) ∧
    (∀ t < 205, (program.constEntries 33).getD t 0 = 1) ∧
    (program.constEntries 34).getD 0 0 = (program.constEntries 39).getD 1 0 ∧
    (∀ u < 16, (program.constEntries 38).getD u 0 = (program.constEntries 39).getD u 0) ∧
    (∀ u < 16, (program.constEntries 32).getD u 0 = 61445 / 2 ^ u % 2) := by
  decide +kernel

/-- `δ`'s field is its challenge's. -/
theorem deltaField :
    program.chalField 0 = program.valueField 592 := by
  decide +kernel

/-- The selection's committed values read nothing from the run. -/
theorem selReads_nil :
    ∀ v ∈ 590 :: 591 :: 589 :: program.exprNodes (.ref 537),
    program.nodeReads program.fuel v = [] := by
  decide +kernel

/-- Challenge `0` is full, of one coordinate, in field `0`. -/
theorem chal0 :
    (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧
    program.chalField 0 = 0 := by
  decide +kernel

/-- `select.raw` is a bit view; it and `c_A` have `8192` coordinates. -/
theorem raw_facts :
    program.isBitView 589 = true ∧ (program.value 589).size = 8192 ∧
    (program.value 595).size = 8192 := by
  decide +kernel

/-- The member check `falcon_key_canonical [12289]` of `hhat`. -/
theorem hhatCheck :
    RealizedProgram.MemberCheck.mk "hhat" 0 1024 "falcon_key_canonical" [12289] ∈
    program.statement.checks := by
  decide +kernel

/-- `hhat` is value `593`. -/
theorem hhatValue :
    program.memberValue? "hhat" = some 593 := by
  obtain ⟨m, -, v, hv, hp⟩ := RealizedProgram.exists_check_of_ptr (ir := program)
    (S := Generated.Falcon512.Emulated.QROMParams.Structure.records) (k := 0)
    (p := fun m v => m.member == "hhat" && v == 593) (by decide +kernel) (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rw [← hp.1, ← hp.2]
  exact hv

/-- `hhat` has `512` coordinates. -/
theorem hhatSize :
    (program.value 593).size = 512 := by
  decide +kernel

/-- The program's shared expressions read only earlier entries. -/
theorem refsOrdered : program.RefsOrdered :=
  (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)

/-- The program of `Falcon512.Emulated.QROMParams` has the Falcon frontend's program facts. -/
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

/-- The emulated program has the Falcon frontend's program facts about domain `A`, at
`c_A = 595`, `s2 = 596`. -/
instance : FalconACore program where
  cA := 595
  s2 := 596
  domainField1 := domainField1
  macEqual := ⟨299, by decide +kernel, by decide +kernel, by decide +kernel⟩
  cABoolean := ⟨284, by decide +kernel, by decide +kernel, by decide +kernel⟩
  raw_facts := raw_facts
  hhatCheck := hhatCheck
  hhatValue := hhatValue
  hhatSize := hhatSize
  hhatField := hhatField
  srcReads_nil := srcReads_nil

/-- **The labels `g^j` as spread products**: entry `j + 1` of the constant `39` is entry `j` times
`g`, checked in the spread representation (`gf2_256Exec`). -/
theorem gpow_chain : ∀ j < 511, gf2_256Exec.mul
    (gf2_256Exec.ofBits ((program.constEntries 39).getD j 0))
    (gf2_256Exec.ofBits gf2_256SubfieldGenN) =
    gf2_256Exec.ofBits ((program.constEntries 39).getD (j + 1) 0) := by
  decide +kernel

/-- **`g^512` as a spread product**: the constant `36` is entry `511` of `39` times `g`. -/
theorem gN_chain : gf2_256Exec.mul
    (gf2_256Exec.ofBits ((program.constEntries 39).getD 511 0))
    (gf2_256Exec.ofBits gf2_256SubfieldGenN) =
    gf2_256Exec.ofBits ((program.constEntries 36).getD 0 0) := by
  decide +kernel

/-- **Entry `j` of the constant `39` is `g^j`** (`gpow_chain`, from entry `0 = 1`). -/
theorem gf2_256OfNat_gpow : ∀ j < 512,
    gf2_256OfNat ((program.constEntries 39).getD j 0) = gf2_256SubfieldGen ^ j
  | 0, _ => by rw [(FalconHBase.const_entries (program := program)).1, gf2_256OfNat_one, pow_zero]
  | j + 1, hj => by
    have hmul := gf2_256OfNat_mul_of_spread (gpow_chain j (by omega))
    rw [show gf2_256OfNat gf2_256SubfieldGenN = gf2_256SubfieldGen from
      (gf2_256Val_ofBits _).symm.trans gf2_256Val_subfieldGen] at hmul
    rw [← hmul, gf2_256OfNat_gpow j (by omega), pow_succ]

/-- The selection labels of the program of `Falcon512.Emulated.QROMParams` in `GF(2^256)`. -/
instance : FalconHConsts program RealizedProgram.gf256 where
  gpow := gf2_256OfNat_gpow
  gN := by
    have hmul := gf2_256OfNat_mul_of_spread gN_chain
    rw [show gf2_256OfNat gf2_256SubfieldGenN = gf2_256SubfieldGen from
      (gf2_256Val_ofBits _).symm.trans gf2_256Val_subfieldGen] at hmul
    change gf2_256OfNat _ = gf2_256SubfieldGen ^ 512
    rw [← hmul, gf2_256OfNat_gpow 511 (by omega), ← pow_succ]
    rfl

/-- The selection field of the program of `Falcon512.Emulated.QROMParams` is `GF(2^256)`, with its
labels; domain `A`'s field is Goldilocks⁴. -/
instance : FalconSelField program RealizedProgram.gf256 RealizedProgram.gold4 where
  inst := inferInstanceAs (HField RealizedProgram.gf256)
  bits_eq := rfl
  gpow := gf2_256OfNat_gpow
  gN := FalconHConsts.gN (program := program) (FH := RealizedProgram.gf256)

end GordieHowe.Falcon512.Emulated.QROMParams
