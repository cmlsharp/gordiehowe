-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.HonestFull
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Honest
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.HashFacts
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.AlgebraFacts
public import GordieHowe.Applications.Falcon512.Native.QROMParams.ProofSystem

@[expose] public section

/-!
# GordieHowe: the honest prover's program facts of `Falcon512.Native.QROMParams`

The program facts the generic honest files read (`FalconHHonest`, `FalconHSelHonest`,
`FalconAHonest`), decided on the tables of `GordieHowe.Generated.Falcon512.Native.QROMParams.Program.program`
(export `c825eb05`).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open ROMParams

open Generated.Falcon512.Native.QROMParams.Program

set_option maxRecDepth 4096 in
/-- The honest hash facts of the program of `Falcon512.Native.QROMParams`. -/
instance : FalconHHonest program where
  words_checks := by decide +kernel
  state_checks := by decide +kernel
  buf_checks := by decide +kernel

/-- The selection values of the program of `Falcon512.Native.QROMParams`. -/
instance : FalconHSelHonest program where
  sel_checks := by decide +kernel

set_option maxRecDepth 8192 in
/-- The honest norm facts of the program of `Falcon512.Native.QROMParams` (`Norm.FalconNormHonest`): the norm's
values are private committed cells. -/
noncomputable instance : Norm.FalconNormHonest program where
  privCell := by decide +kernel

set_option maxRecDepth 8192 in
/-- The facts of honest domain A of the program of `Falcon512.Native.QROMParams`: the norm at domain and field `1`, the
field-form signature `265`, `c_A`'s check `268` and `mac.equal` `285`. -/
noncomputable instance : FalconAHonest program where
  toFalconAAlg := inferInstance
  norm_dA := rfl
  norm_fA := rfl
  norm_ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  pSigE := 265
  pCA := 268
  pMac := 285
  a_checks := by decide +kernel
  sizes_H := by decide +kernel
  const44 := by decide +kernel
  sigE_body := ⟨_, rfl⟩
  sigE_len := by decide +kernel
  ca_body := ⟨_, rfl⟩
  mac_body := ⟨_, _, rfl, by decide⟩
  cross_fields := by decide +kernel

/-! ## The honest strategy's program facts -/

namespace Facts

open RealizedProgram

/-- The blind's cells, decided. -/
theorem blind_cells : (program.value 557).kind = .padCopy 560 "polynomialBits" ∧
    (program.value 557).domain < program.domains.length ∧
    (∀ j < 256, CellKey.val 557 j ∈ program.cellKeys (program.value 557).domain) ∧
    program.valueField 557 = 1 ∧ (program.value 557).size = 256 :=
  ⟨kind_of_isPadCopyB (by decide +kernel), by decide +kernel,
    fun j hj => (program.mem_cellKeys_val).2 ⟨by decide +kernel, by decide +kernel,
      by have : (program.value 557).size = 256 := by decide +kernel
         omega⟩, by decide +kernel, by decide +kernel⟩

/-- **The MAC's predicates**: the H predicate, the accumulator rows, the residues' check, the
lookups on the digits and the final quotient, the tail. -/
def macRolePreds : List ℕ := [250, 261, 262, 263, 264, 272, 281, 282, 283]

open Honest in
/-- The only cross-field `equal` is `mac.equal` (predicate `285`), decided. -/
theorem cross_only : (List.range program.predicates.length).all (fun q => q == 285 ||
    match (program.predicate q).body with
    | .cross _ _ _ _ _ _ => false
    | _ => true) = true := by
  decide +kernel

end Facts

set_option maxRecDepth 4096 in
/-- The values of the program of `Falcon512.Native.QROMParams` are distinct where the honest valuation reads them. -/
instance : FalconHValues program where
  not_hash_sel := by decide +kernel
  not_hash_norm := by decide +kernel
  blind_not := by decide +kernel

/-- The program's one statement bound: the key's entries `hhat` below `q`. -/
theorem bounds : program.declaredRanges = [(544, 12289)] := by decide +kernel

open Facts RealizedProgram in
set_option maxRecDepth 4096 in
/-- **The honest-strategy facts of the program of `Falcon512.Native.QROMParams`**: the MAC `mac.equal` with its grouped
tail (`QROMParams.Honest.mac`), its role predicates. -/
noncomputable instance : FalconHonestFull program
    (RealizedProgram.primeNodesOf Generated.Falcon512.Native.QROMParams.Plan.plan program) where
  bounds := bounds
  mac := Honest.mac
  macRolePreds := Facts.macRolePreds
  bw := 256
  mac_shape := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  crossMac p hp dx x dy y k real hb := by
    obtain ⟨q, hq, rfl⟩ := RealizedProgram.exists_index_of_mem hp
    have := List.all_eq_true.1 Facts.cross_only q (List.mem_range.2 hq)
    rw [hb] at this
    simp only [beq_iff_eq, Bool.or_false] at this
    subst this
    rfl
  src_cover := by decide +kernel
  checks_list := by decide +kernel
  blind_cells := Facts.blind_cells
  cell_classes := by decide +kernel
  padCopy_only := by decide +kernel
  typed_classes := by decide +kernel

end GordieHowe.Falcon512.Native.QROMParams
