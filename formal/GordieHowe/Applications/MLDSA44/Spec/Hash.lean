-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Spec.Basic
public import GordieHowe.Applications.Keccak.Xof
public import GordieHowe.Foundations.ToMathlib.UInt8
import all LatticeCrypto.MLDSA.Concrete.Encoding

@[expose] public section

/-!
# The vendored ML-DSA hashes through `xofFin shake256`

The vendored `hashMessage` (`μ = H(tr ‖ M′, 64)`) and `hashCommitment`
(`c̃ = H(μ ‖ w1Encode(w₁), λ/4)`) of `Vendor/LatticeCrypto/MLDSA/ConcretePrimitives.lean`
call the vendored sponge on `UInt8` lists. The circuit specifications read hash outputs as
`xofFin shake256` on byte naturals. The lemmas here say the two readings agree byte for byte.
-/

namespace GordieHowe.MLDSA44

open _root_.MLDSA _root_.MLDSA.Concrete

/-- Byte `i` of the vendored `shake256List` output, as a natural, is `xofFin shake256` on the
same bytes read as naturals. -/
theorem shake256List_getElem!_toNat (l : List UInt8) (m : ℕ) (i : Fin m) :
    (shake256List l m)[i.1]!.toNat = xofFin shake256 (l.map UInt8.toNat) m i := by
  rw [xofFin_shake256_eq_getElem!, List.map_toUInt8_map_toNat]
  rfl

/-- Byte `i` of `byteArrayToVector (shake256List l m) 0 m` is `xofFin shake256` on `l`. -/
theorem byteArrayToVector_shake256List_get (l : List UInt8) (m : ℕ) (i : Fin m) :
    ((byteArrayToVector (shake256List l m) 0 m).get i).toNat =
      xofFin shake256 (l.map UInt8.toNat) m i := by
  have hsize : i.1 < (shake256List l m).size := by
    rw [shake256List, SLHDSA.Concrete.Keccak.shake256_size]
    exact i.2
  rw [← shake256List_getElem!_toNat, byteArrayToVector, Vector.get_ofFn, Nat.zero_add,
    getElem?_pos (shake256List l m) i.1 hsize, Option.getD_some,
    getElem!_pos (shake256List l m) i.1 hsize]

theorem byteArrayToList_vectorToByteArray {n : ℕ} (v : Bytes n) :
    byteArrayToList (vectorToByteArray v) = v.toList := by
  rw [byteArrayToList, vectorToByteArray]
  exact Vector.toList_toArray

/-- `μ = hashMessage tr M`, byte for byte, is `SHAKE256(tr ‖ M, 64)` on byte naturals. -/
theorem hashMessage_get (tr : Bytes 64) (M : List UInt8) (j : Fin 64) :
    ((hashMessage tr M).get j).toNat =
      xofFin shake256 (tr.toList.map UInt8.toNat ++ M.map UInt8.toNat) 64 j := by
  rw [hashMessage, byteArrayToVector_shake256List_get, byteArrayToList_vectorToByteArray,
    List.map_append]

/-- `c̃ = hashCommitment μ w`, byte for byte, is `SHAKE256(μ ‖ w, 32)` on byte naturals at
ML-DSA-44 (`λ / 4 = 32`). -/
theorem hashCommitment_get (mu : Bytes 64) (w : List UInt8) (i : Fin 32) :
    ((hashCommitment _root_.MLDSA.mldsa44 mu w).get i).toNat =
      xofFin shake256 (mu.toList.map UInt8.toNat ++ w.map UInt8.toNat) 32 i := by
  rw [hashCommitment]
  exact (byteArrayToVector_shake256List_get _ 32 i).trans (by
    rw [byteArrayToList_vectorToByteArray, List.map_append])

end GordieHowe.MLDSA44
