-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Xof

@[expose] public section

/-!
# The Keccak sponge, generic in rate and domain suffix (FIPS 202)

`keccakSponge rate suffix msg outLen` is FIPS 202's `KECCAK[c]` sponge over Keccak-f[1600]:
pad10*1 with the domain suffix, absorb `rate`-byte blocks, squeeze `outLen` bytes. It is
assembled from the vendored reference (`Vendor/HashSig/SLHDSA/Concrete/Keccak.lean`, VCVio
`HashSig/SLHDSA/Concrete/Keccak.lean` at `eb0f6e45`), whose `absorb input rate padByte` and
`squeezeXof state rate outLen` are already generic; no Keccak code is written here. The vendored
SHAKE128/SHAKE256/SHA3 functions are those two calls at fixed parameters, so each instance below
is equal to its vendored counterpart by `rfl` or a one-block squeeze.

The instances are the C++ `SpongeSpec`s (`lib/circuits/keccak/keccak_sponge.h:48-51` at
`e5daf0a`): SHAKE128 `{168, 0x1f}`, SHAKE256 `{136, 0x1f}`, SHA3-256 `{136, 0x06, 32}`,
SHA3-512 `{72, 0x06, 64}`. A fixed-length SHA3 digest is the sponge squeezed and truncated to
the digest length.

`spongeXof rate suffix` is the sponge as an `XOF` on byte values in `ℕ`, through the same
adapter as `GordieHowe.shake256`; `spongeXof_shake256` identifies the two.
-/

namespace GordieHowe

/-- **The Keccak sponge** (FIPS 202 §4, `SPONGE[Keccak-f[1600], pad10*1, 8·rate]` with the
domain suffix `suffix` prepended to the padding, as the vendored `absorb` does): `outLen` bytes
squeezed from `msg`. -/
def keccakSponge (rate : ℕ) (suffix : UInt8) (msg : List UInt8) (outLen : ℕ) : List UInt8 :=
  (SLHDSA.Concrete.Keccak.squeezeXof
    (SLHDSA.Concrete.Keccak.absorb (ByteArray.mk msg.toArray) rate suffix) rate outLen).data.toList

theorem keccakSponge_length {rate : ℕ} (hrate : 0 < rate) (suffix : UInt8) (msg : List UInt8)
    (outLen : ℕ) : (keccakSponge rate suffix msg outLen).length = outLen := by
  simp only [keccakSponge, Array.length_toList]
  exact SLHDSA.Concrete.Keccak.squeezeXof_size _ _ _ hrate

/-- **The generic sponge at SHAKE256's parameters is the vendored SHAKE256.** -/
theorem keccakSponge_shake256 :
    keccakSponge 136 0x1f =
      fun msg outLen => (SLHDSA.Concrete.Keccak.shake256 (ByteArray.mk msg.toArray) outLen).data.toList :=
  rfl

/-- SHAKE128 (FIPS 202 §6.2). -/
def shake128Bytes (msg : List UInt8) (outLen : ℕ) : List UInt8 := keccakSponge 168 0x1f msg outLen

theorem shake128Bytes_eq (msg : List UInt8) (outLen : ℕ) :
    shake128Bytes msg outLen =
      (SLHDSA.Concrete.Keccak.shake128 (ByteArray.mk msg.toArray) outLen).data.toList :=
  rfl

/-- SHAKE256 (FIPS 202 §6.2). -/
def shake256Bytes (msg : List UInt8) (outLen : ℕ) : List UInt8 := keccakSponge 136 0x1f msg outLen

/-- A squeeze of at most one block is one `squeeze` of the absorbed state. -/
theorem squeezeXof_of_lt (s : Array UInt64) {rate outLen : ℕ} (h : outLen < rate) :
    SLHDSA.Concrete.Keccak.squeezeXof s rate outLen = SLHDSA.Concrete.Keccak.squeeze s outLen := by
  apply ByteArray.ext
  simp [SLHDSA.Concrete.Keccak.squeezeXof, show rate ≠ 0 by omega, Nat.div_eq_of_lt h,
    Nat.mod_eq_of_lt h, SLHDSA.Concrete.Keccak.squeezeFullBlocks]

/-- SHA3-256 (FIPS 202 §6.1): the sponge truncated to a 32-byte digest. -/
def sha3_256Bytes (msg : List UInt8) : List UInt8 := keccakSponge 136 0x06 msg 32

theorem sha3_256Bytes_eq (msg : List UInt8) :
    sha3_256Bytes msg = (SLHDSA.Concrete.Keccak.sha3_256 (ByteArray.mk msg.toArray)).data.toList := by
  rw [sha3_256Bytes, keccakSponge, squeezeXof_of_lt _ (by decide)]
  rfl

/-- SHA3-512 (FIPS 202 §6.1): the sponge truncated to a 64-byte digest. -/
def sha3_512Bytes (msg : List UInt8) : List UInt8 := keccakSponge 72 0x06 msg 64

theorem sha3_512Bytes_eq (msg : List UInt8) :
    sha3_512Bytes msg = (SLHDSA.Concrete.Keccak.sha3_512 (ByteArray.mk msg.toArray)).data.toList := by
  rw [sha3_512Bytes, keccakSponge, squeezeXof_of_lt _ (by decide)]
  rfl

/-- The sponge as an `XOF` on byte values in `ℕ`, through `GordieHowe.shake256`'s adapter. -/
def spongeXof (rate : ℕ) (suffix : UInt8) : XOF := fun input m =>
  (keccakSponge rate suffix (input.map Nat.toUInt8) m).map UInt8.toNat

/-- **`spongeXof` at SHAKE256's parameters is `GordieHowe.shake256`.** -/
theorem spongeXof_shake256 : spongeXof 136 0x1f = shake256 :=
  rfl

theorem spongeXof_length {rate : ℕ} (hrate : 0 < rate) (suffix : UInt8) (input : List ℕ)
    (m : ℕ) : (spongeXof rate suffix input m).length = m := by
  rw [spongeXof, List.length_map, keccakSponge_length hrate]

/-- `xofFin (spongeXof rate suffix)` reads byte `i` of the vendored squeeze. -/
theorem xofFin_spongeXof_eq_getElem! {rate : ℕ} (hrate : 0 < rate) (suffix : UInt8)
    (input : List ℕ) (m : ℕ) (i : Fin m) :
    xofFin (spongeXof rate suffix) input m i =
      (SLHDSA.Concrete.Keccak.squeezeXof
        (SLHDSA.Concrete.Keccak.absorb (ByteArray.mk (input.map Nat.toUInt8).toArray) rate suffix)
        rate m)[i.1]!.toNat := by
  have hl := spongeXof_length hrate suffix input m
  have hs := SLHDSA.Concrete.Keccak.squeezeXof_size
    (SLHDSA.Concrete.Keccak.absorb (ByteArray.mk (input.map Nat.toUInt8).toArray) rate suffix)
    rate m hrate
  unfold xofFin
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact i.2), Option.getD_some]
  simp only [spongeXof, keccakSponge, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos _ i.1 (by rw [hs]; exact i.2)]
  rfl

end GordieHowe
