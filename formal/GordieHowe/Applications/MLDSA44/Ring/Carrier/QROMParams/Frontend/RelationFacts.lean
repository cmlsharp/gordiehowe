-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program
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

set_option maxRecDepth 4096 in
/-- **`signature.relation`**: the spectral product form of `w′ ≡ Σ_j A_ij z_j − 2^d t1_i c (mod q)`. -/
theorem carrier_relation : ∃ real, (program.predicate 3).body = .mod 0 8380417 sigP sigN real ∧
    real.form = .spectralProduct :=
  ⟨_, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The signature relation's program facts. -/
instance : MldsaCarrierRelation program where
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  exprsLen := by decide +kernel
  expr36 := rfl
  expr39 := rfl
  expr40 := rfl
  expr41 := rfl
  expr37 := rfl
  expr38 := rfl
  sig := carrier_relation
  cBool := by decide +kernel
  wRange := ⟨_, rfl⟩
  zRange := ⟨_, rfl⟩
  inSource := by decide +kernel
  offset := by decide +kernel
  size55 := by decide +kernel
  size56 := by decide +kernel
  size60 := by decide +kernel
  size62 := by decide +kernel
  size63 := by decide +kernel
  domainField0 := by decide +kernel
  field60 := by decide +kernel
  field62 := by decide +kernel
  field63 := by decide +kernel
  kind60 := by decide +kernel
  kind63 := by decide +kernel
  kind62 := rfl

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
