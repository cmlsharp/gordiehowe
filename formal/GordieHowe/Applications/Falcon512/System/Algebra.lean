-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Falcon512.System.Source
public import GordieHowe.Applications.Falcon512.Circuits.EmulatedAlgebra

@[expose] public section

/-!
# Falcon: the extracted samples and signature polynomial

The readings of domain A's cells that both Falcon configurations conclude on: the sample value of
the sample bits `c_A` (`sampleValue`), the raw samples (`cNat`), the signature polynomial read from
`s2` (`s2Nat`, `decodeS2`, `decodeS2Int`), and Falcon's algebraic verifier with the encoding bounds
on them (`AlgebraSpec`), with the bit view of a sample (`sampleBitOf`). Falcon emulated's
constraints and their soundness are in `GordieHowe/Applications/Falcon512/Emulated/System/Algebra.lean`; Falcon native's
in `GordieHowe/Applications/Falcon512/Native/System/Algebra.lean`.
-/

namespace GordieHowe.Falcon512.Emulated

open GordieHowe.Bits Range Params

variable {F : Type} [Field F]

/-- **Sample `i` of the sample bits** in `F`: `Σ_b 2^b c_A[i][b]` (`from_digits(c_A, 2)`). -/
def sampleValue (cA : Fin falcon512.n → BitWires F falconSampleBits) (i : Fin falcon512.n) : F :=
  ∑ b : Fin falconSampleBits, (2 : F) ^ (b : ℕ) * cA i b

variable [DecidableEq F]

/-- **The raw samples**: the natural of each sample's bits. -/
-- spec-side
def cNat (cA : Fin falcon512.n → BitWires F falconSampleBits) (i : Fin falcon512.n) : ℕ :=
  natOfBits (cA i)

/-- **The extracted coefficients of `s2`**: the representative in `[0, q]` of each value (zero if
there is none). -/
-- spec-side
def s2Nat (s2 : Fin falcon512.n → F) (i : Fin falcon512.n) : ℕ :=
  Range.natBelow (falcon512.q + 1) (s2 i)

/-- **The extracted signature polynomial**, reduced modulo `q`. -/
-- spec-side
def decodeS2 (s2 : Fin falcon512.n → F) : _root_.Falcon.Rq falcon512.n :=
  Falcon512.ofCoeff fun i => (s2Nat s2 i : _root_.Falcon.Coeff)

/-- **The extracted signature polynomial**, centered. -/
-- spec-side
def decodeS2Int (s2 : Fin falcon512.n → F) : _root_.Falcon.IntPoly falcon512.n :=
  Vector.ofFn fun i => LatticeCrypto.centeredRepr (Falcon512.coeff (decodeS2 s2) i)

theorem decodeS2Int_toRq (s2 : Fin falcon512.n → F) : (decodeS2Int s2).toRq = decodeS2 s2 := by
  apply LatticeCrypto.PolyBackend.ext_coeff (backend := _root_.Falcon.polyBackend falcon512.n)
  intro i
  change Falcon512.coeff (decodeS2Int s2).toRq i = Falcon512.coeff (decodeS2 s2) i
  rw [Falcon512.intPoly_toRq_coeff]
  change ((Vector.ofFn fun i =>
    LatticeCrypto.centeredRepr (Falcon512.coeff (decodeS2 s2) i)).get i :
      _root_.Falcon.Coeff) = Falcon512.coeff (decodeS2 s2) i
  rw [Vector.get_ofFn]
  exact (LatticeCrypto.centeredRepr_intCast _).symm

/-- **What the algebra constraints establish**: Falcon's algebraic verifier on the raw samples and
the extracted `s2` at the key `h`, and the encoding bounds of the centered `s2`. -/
structure AlgebraSpec (h : _root_.Falcon.Rq falcon512.n)
    (cA : Fin falcon512.n → BitWires F falconSampleBits) (s2 : Fin falcon512.n → F) : Prop where
  /-- Falcon's algebraic verifier. -/
  algebra : Falcon512.algebraOk falcon512 h (Falcon512.ofCoeff fun i => (cNat cA i : _root_.Falcon.Coeff))
    (decodeS2 s2)
  /-- The encoding bounds. -/
  encoding : Falcon512.EncodingBounds falcon512 (decodeS2Int s2)

/-- **What the algebra establishes at a challenge given as naturals** `c`: Falcon's algebraic
verifier on `c` and the extracted `s2` at the key `h`, and the encoding bounds of the centered
`s2`. -/
structure AlgebraSpecAt (h : _root_.Falcon.Rq falcon512.n) (c : Fin falcon512.n → ℕ)
    (s2 : Fin falcon512.n → F) : Prop where
  /-- Falcon's algebraic verifier. -/
  algebra : Falcon512.algebraOk falcon512 h (Falcon512.ofCoeff fun i => (c i : _root_.Falcon.Coeff))
    (decodeS2 s2)
  /-- The encoding bounds. -/
  encoding : Falcon512.EncodingBounds falcon512 (decodeS2Int s2)

/-- **The sample and bit of a flat sample-bit index** `16 i + b`. -/
def sampleBitOf (k : Fin (falconSampleBits * falcon512.n)) : Fin falcon512.n × Fin falconSampleBits :=
  (finProdFinEquiv (m := falcon512.n) (n := falconSampleBits)).symm
    (Fin.cast (Nat.mul_comm falconSampleBits falcon512.n) k)

/-- The flat index `16 i + b` is sample `i`, bit `b`. -/
theorem sampleBitOf_mk (i : Fin falcon512.n) (b : Fin falconSampleBits)
    (hk : falconSampleBits * (i : ℕ) + b < falconSampleBits * falcon512.n) :
    sampleBitOf ⟨falconSampleBits * i + b, hk⟩ = (i, b) := by
  rw [sampleBitOf, Equiv.symm_apply_eq]
  ext
  simp [finProdFinEquiv]
  ring

/-- Boolean sample bits cast their natural to the sample value. -/
theorem cNat_cast {cA : Fin falcon512.n → BitWires F falconSampleBits}
    (hbits : ∀ i b, cA i b = 0 ∨ cA i b = 1) (i : Fin falcon512.n) :
    (cNat cA i : F) = sampleValue cA i := by
  simp only [cNat, natOfBits, Nat.cast_sum, sampleValue, Nat.cast_ite, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro b _
  rcases hbits i b with hb | hb <;> simp [hb]

end GordieHowe.Falcon512.Emulated
