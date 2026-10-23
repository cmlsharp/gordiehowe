-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.PoP.Compose
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Foundations.Fields.GF2_128Conv
public import GordieHowe.Applications.MLDSA44.Fields.GF2_128

@[expose] public section

/-!
# Values extracted from the native ML-DSA-44 A circuit's wires

The native A circuit (`GordieHowe.MLDSA44.NativeAlgebraCircuit`, over `F_{q^6}`) commits the high bits `w1` as the `w1_tilde`
bits and the hints as field wires. `decodeW1` reads coefficient `(i, c)` of `w1` as the natural
number of its six `w1` bits (`w1Coeff`, bounded by `w1Coeff_lt`), and `decodeH` reads the hints as
the hint wires equal to `1`; `decodeW1_get` and `decodeH_get` read them coefficientwise.
-/

namespace GordieHowe.MLDSA44.PoP.Native
open NativeAlgebraCircuit

open Native.Rows

variable {K F : Type} [Field K] [Field F] [DecidableEq F]

/-! ### The extracted values -/

variable [DecidableEq K] {mw : ℕ} {taps : Finset ℕ} [mldsa44.MACWidth mw]
  {A : NativeArm mldsa44 mw taps}

/-- The extracted high bits: coefficient `(i, c)` is the natural number of its six `w1`
bits. -/
-- spec-side
def decodeW1 (w1 : BitWires F (8 * 768)) :
    Vector _root_.MLDSA.Concrete.High _root_.MLDSA.mldsa44.k :=
  Vector.ofFn fun i => MLDSA44.ofCoeff fun c => (w1Coeff w1 i c : _root_.MLDSA.Coeff)

theorem w1Coeff_lt (w1 : BitWires F (8 * 768)) (i : Fin nRows) (c : Fin deg) :
    w1Coeff w1 i c < 64 :=
  Bits.natOfBits_lt _

theorem decodeW1_get (w1 : BitWires F (8 * 768)) (i : Fin nRows) (c : Fin deg) :
    ((decodeW1 w1).get i).get c = (w1Coeff w1 i c : _root_.MLDSA.Coeff) := by
  rw [← MLDSA44.coeff_apply, decodeW1, Vector.get_ofFn, MLDSA44.coeff_ofCoeff]

/-- The extracted hints: the hint wires equal to `1`. -/
-- spec-side
def decodeH (hint : Fin nRows → Fin deg → F) :
    Vector _root_.MLDSA.Concrete.Hint _root_.MLDSA.mldsa44.k :=
  Vector.ofFn fun i => Vector.ofFn fun k => decodeHint hint i k

theorem decodeH_get (hint : Fin nRows → Fin deg → F) (i : Fin nRows) (k : Fin deg) :
    ((decodeH hint).get i).get k = decodeHint hint i k := by
  rw [decodeH, Vector.get_ofFn, Vector.get_ofFn]

end GordieHowe.MLDSA44.PoP.Native
