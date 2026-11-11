-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Spec.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Basic

@[expose] public section

/-!
# Falcon-512 public keys as a finite type

A public key `PublicKey` (`GordieHowe/Applications/Falcon512/Spec/Basic.lean`) is its polynomial
`h`, a vector of `512` coefficients modulo `q` (`PublicKey.equiv`); hence a finite (VCVio's
`instFintypeVector`) and inhabited type.
-/

namespace GordieHowe.Falcon512

/-- A public key is its polynomial `h`, a vector of `512` coefficients modulo `q`. -/
def PublicKey.equiv : PublicKey ≃ Vector (ZMod 12289) 512 where
  toFun pk := pk.h
  invFun h := ⟨h⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype PublicKey := Fintype.ofEquiv _ PublicKey.equiv.symm

instance : Inhabited PublicKey := ⟨⟨Vector.replicate 512 0⟩⟩

end GordieHowe.Falcon512
