-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Certified
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Relation

@[expose] public section

/-!
# GordieHowe: the signature relation's program facts of `MLDSA44.Ring.Carrier.QROMParams`

The program facts the ML-DSA ring carriers' signature relation reads
(`GordieHowe.MLDSA44.Ring.Carrier.MldsaCarrierRelation`), decided on the tables of
`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program.program` (export `5d775ae1`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open Generated.MLDSA44.Ring.Carrier.QROMParams.Program
open Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts RealizedProgram

set_option maxRecDepth 4096 in
/-- **`signature.relation`**: the spectral product form of `w′ ≡ Σ_j A_ij z_j − 2^d t1_i c (mod q)`. -/
theorem carrier_relation : ∃ real, (program.predicate 3).body = .mod 0 8380417 sigP sigN real ∧
    real.form = .spectralProduct :=
  by
    obtain ⟨r, h, hf, -⟩ := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.predicate_signature_2erelation_body
    exact ⟨r, h, hf⟩

set_option maxRecDepth 4096 in
/-- The signature relation's program facts. -/
instance : MldsaCarrierRelation program where
  refsOrdered := Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.wellFormed.refsOrdered
  exprsLen := expr_lt_of_ne_default (by
    rw [expr_signature_2erelation_2eshape_2eleft_2esecond_2esecond_2esecond_eq]
    decide)
  expr36 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2efirst_eq
  expr39 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2esecond_2efirst_eq
  expr40 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2esecond_2esecond_2efirst_eq
  expr41 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2esecond_2esecond_2esecond_eq
  expr37 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eright_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_eq
  expr38 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eright_2efirst_2esecond_2efirst_2efirst_2efirst_2esecond_2efirst_eq
  sig := carrier_relation
  cBool := by
    obtain ⟨t, ht⟩ := predicate_challenge_2ec_2eboolean_body
    rw [ht]
    rfl
  wRange := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.predicate_signature_2ew_body
  zRange := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.predicate_norm_2ez_body
  inSource := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨predicate_signature_2erelation_role.1, program.inSource_of_source predicate_signature_2erelation_role.2⟩
    · exact ⟨predicate_challenge_2ec_2eboolean_role.1,
        program.inSource_of_type predicate_challenge_2ec_2eboolean_role.2
          (valueShape_role value_challenge_2ec_header.2)⟩
    · exact ⟨predicate_signature_2ew_role.1, program.inSource_of_source predicate_signature_2ew_role.2⟩
    · exact ⟨predicate_norm_2ez_role.1, program.inSource_of_source predicate_norm_2ez_role.2⟩
  offset := ⟨isConstant_of_kind value_norm_2ez_2eoffset_kind,
    valueShape_field value_norm_2ez_2eoffset_header.2,
    (constEntries_of_kind value_norm_2ez_2eoffset_kind).trans (by decide +kernel)⟩
  size55 := valueShape_size value_member_2ea_5fhat_header.2
  size56 := valueShape_size value_member_2et1_header.2
  size60 := valueShape_size value_z_header.2
  size62 := valueShape_size value_challenge_2ec_header.2
  size63 := valueShape_size value_signature_2ew_header.2
  domainField0 := Generated.MLDSA44.Ring.Carrier.QROMParams.conditions.fieldTable.domainField_eq 0 (by decide)
  field60 := valueShape_field value_z_header.2
  field62 := valueShape_field value_challenge_2ec_header.2
  field63 := valueShape_field value_signature_2ew_header.2
  kind60 := by rw [value_z_kind]; rfl
  kind63 := by rw [value_signature_2ew_kind]; rfl
  kind62 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.value_challenge_2ec_kind

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
