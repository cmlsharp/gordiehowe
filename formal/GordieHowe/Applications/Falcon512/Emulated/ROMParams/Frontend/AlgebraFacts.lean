-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Emulated.Frontend.Algebra
public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.Frontend.Facts
public import GordieHowe.Language.RealizedProgram.Kinds

@[expose] public section

/-!
# GordieHowe frontend: the domain `A` facts of `Falcon512.Emulated.ROMParams`

The program facts of domain `A` that the emulated Falcon frontend reads (`FalconEAlg`) for
`GordieHowe.Generated.Falcon512.Emulated.ROMParams.Program.program` read through its checked shape facts.
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open Generated.Falcon512.Emulated.ROMParams.Program (program)
open Generated.Falcon512.Emulated.ROMParams.ShapeFacts
open RealizedProgram

/-- `crossing.c_A`, `s2`, `signature.s1`, `magnitudes.mag2` and `encoding.low2` are committed. -/
theorem privKinds : (program.value 595).kind = .priv ∧ (program.value 596).kind = .priv ∧
    (program.value 597).kind = .priv ∧ (program.value 599).kind = .priv ∧
    (program.value 600).kind = .priv :=
  ⟨value_crossing_2ec_5fA_kind, value_s2_kind, value_signature_2es1_kind, value_magnitudes_2emag2_kind, value_encoding_2elow2_kind⟩

/-- `key.coefficients` is computed from `statement.hhat`. -/
theorem keyKind : (program.value 594).kind = .pub (.opaque "key.coefficients" [593]) :=
  value_key_2ecoefficients_kind

/-- `statement.hhat` is an opaque statement value of no argument. -/
theorem hhatKind : (program.value 593).kind = .pub (.opaque "statement.hhat" []) :=
  value_statement_2ehhat_kind

/-- The program of `Falcon512.Emulated.ROMParams` has the emulated Falcon frontend's program facts
about domain `A`. -/
instance : FalconEAlg program where
  cA_eq := rfl
  s2_eq := rfl
  sig := by
    obtain ⟨real, h, -⟩ := predicate_signature_2eequation_2esource_body
    exact ⟨real, h⟩
  magS1 := predicate_magnitudes_2es1_body
  magS2 := predicate_magnitudes_2es2_body
  normSum := predicate_norm_2esum_body
  rMag1 := predicate_magnitudes_2emag1_body
  rMag2 := predicate_magnitudes_2emag2_body
  rLow2 := predicate_encoding_2elow2_body
  rBudget := predicate_encoding_2ebudget_body
  rNorm := predicate_norm_2ebound_body
  high2 := by
    obtain ⟨real, h, -⟩ := predicate_encoding_2ehigh2_body
    exact ⟨real, h⟩
  inSource := by
    intro p hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨predicate_magnitudes_2es1_role.1, program.inSource_of_source predicate_magnitudes_2es1_role.2⟩
    · exact ⟨predicate_magnitudes_2es2_role.1, program.inSource_of_source predicate_magnitudes_2es2_role.2⟩
    · exact ⟨predicate_norm_2esum_role.1, program.inSource_of_source predicate_norm_2esum_role.2⟩
    · exact ⟨predicate_magnitudes_2emag1_role.1, program.inSource_of_source predicate_magnitudes_2emag1_role.2⟩
    · exact ⟨predicate_magnitudes_2emag2_role.1, program.inSource_of_source predicate_magnitudes_2emag2_role.2⟩
    · exact ⟨predicate_encoding_2elow2_role.1, program.inSource_of_source predicate_encoding_2elow2_role.2⟩
    · exact ⟨predicate_encoding_2ebudget_role.1, program.inSource_of_source predicate_encoding_2ebudget_role.2⟩
    · exact ⟨predicate_norm_2ebound_role.1, program.inSource_of_source predicate_norm_2ebound_role.2⟩
    · exact ⟨predicate_signature_2eequation_2esource_role.1, program.inSource_of_source predicate_signature_2eequation_2esource_role.2⟩
    · exact ⟨predicate_encoding_2ehigh2_role.1, program.inSource_of_source predicate_encoding_2ehigh2_role.2⟩
  consts := by
    refine ⟨isConstant_of_kind value_magnitudes_2eshift_kind, ?_, isConstant_of_kind value_magnitudes_2ezero_kind, ?_,
      isConstant_of_kind value_norm_2esum_2ezero_kind, ?_, isConstant_of_kind value_encoding_2ebudget_2eoffset_kind, ?_⟩
    · rw [constEntries_of_kind value_magnitudes_2eshift_kind]; rfl
    · rw [constEntries_of_kind value_magnitudes_2ezero_kind]; decide +kernel
    · rw [constEntries_of_kind value_norm_2esum_2ezero_kind]; rfl
    · rw [constEntries_of_kind value_encoding_2ebudget_2eoffset_kind]; rfl
  fields := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact valueShape_field value_magnitudes_2eshift_header.2
    · exact valueShape_field value_magnitudes_2ezero_header.2
    · exact valueShape_field value_norm_2esum_2ezero_header.2
    · exact valueShape_field value_statement_2ehhat_header.2
    · exact valueShape_field value_key_2ecoefficients_header.2
    · exact valueShape_field value_crossing_2ec_5fA_header.2
    · exact valueShape_field value_s2_header.2
    · exact valueShape_field value_signature_2es1_header.2
    · exact valueShape_field value_magnitudes_2emag1_header.2
    · exact valueShape_field value_magnitudes_2emag2_header.2
    · exact valueShape_field value_encoding_2elow2_header.2
    · exact valueShape_field value_encoding_2ebudget_2eoffset_header.2
    · exact valueShape_field value_norm_2esquares_header.2
  sizes := ⟨valueShape_size value_key_2ecoefficients_header.2, valueShape_size value_s2_header.2, valueShape_size value_signature_2es1_header.2, valueShape_size value_magnitudes_2emag1_header.2, valueShape_size value_magnitudes_2emag2_header.2, valueShape_size value_encoding_2elow2_header.2, valueShape_size value_norm_2esquares_header.2⟩
  privKinds := privKinds
  keyKind := keyKind
  hhatKind := hhatKind
  keyDeclared := by
    rw [statement_ranges]
    simp

/-- **Domain `A`'s obligation at `Falcon512.Emulated.ROMParams`** (`algebraSound`), at
`GF(2^128)` and Goldilocks². -/
theorem algebraSound :
    AlgebraSound (program := program) (FH := RealizedProgram.gf128) (FA := RealizedProgram.gold2) :=
  Emulated.algebraSound

end GordieHowe.Falcon512.Emulated.ROMParams
