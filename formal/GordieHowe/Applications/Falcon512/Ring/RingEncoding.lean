-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.BaseSigners
public import GordieHowe.Applications.Ring.RingUnforgeability
public import GordieHowe.Applications.Ring.RingBytes

@[expose] public section

/-!
# Fixed-length encoding of a Falcon-512 ring and message

The base message `m ‖ encode R` of a ring-binding ring signature (BKM06 §5) for a ring of at most
`64` Falcon-512 keys and a `32`-byte message, as an injective fixed-length byte string.

- `ringMsgLen`, `ringMsgLen_le`: the encoded length `32 + (1 + 64 · 1024)`, at most `2 ^ 19`.
- `keyIdx`, `keyBytes`, `keyBytes_injective`: a key as `1024` bytes, each coefficient's value as two bytes
  (low, high).
- `ringBytes`, `ringBytes_injective`: a ring as one length byte and `64` slots of `1024` bytes,
  slot `a` the `a`-th key and zeros past the ring's length (`GordieHowe.Ring.ringBytes`,
  `GordieHowe/Applications/Ring/RingBytes.lean`).
- `encodeRingMsg`, `encodeRingMsg_inj`, `encodeRingMsg_injective`: the message followed by the
  ring's bytes, injective in both and in the message at each ring.
- `bindsRing_encodeRingMsg`: the Falcon-512 base signer at `encodeRingMsg` binds the ring.
-/

namespace GordieHowe.Falcon512.Ring

open GordieHowe.Falcon512.Ring.Native

/-- The length of an encoded ring message: `32` message bytes, one length byte, `64` key slots. -/
abbrev ringMsgLen : ℕ := 32 + (1 + 64 * 1024)

/-- **The encoded length is at most `2 ^ 19`.** -/
theorem ringMsgLen_le : ringMsgLen ≤ 2 ^ 19 := by decide

/-- The byte index `(i, b)` of a key: coefficient `i`, byte `b`. -/
abbrev keyIdx : Fin 512 × Fin 2 ≃ Fin 1024 := finProdFinEquiv

/-- A key as `1024` bytes: byte `(i, 0)` the low and `(i, 1)` the high byte of coefficient `i`'s
value. -/
def keyBytes (pk : PublicKey) : Fin 1024 → UInt8 := fun j =>
  let v := ((PublicKey.equiv pk)[(keyIdx.symm j).1]).val
  if (keyIdx.symm j).2 = (0 : Fin 2) then (v % 256).toUInt8 else (v / 256).toUInt8

/-- **`keyBytes` is injective.** -/
theorem keyBytes_injective : Function.Injective keyBytes := by
  intro pk pk' h
  apply PublicKey.equiv.injective
  apply Vector.ext
  intro i hi
  have h0 := congrFun h (keyIdx (⟨i, hi⟩, 0))
  have h1 := congrFun h (keyIdx (⟨i, hi⟩, 1))
  simp only [keyBytes, Equiv.symm_apply_apply] at h0 h1
  apply ZMod.val_injective
  have l0 := GordieHowe.Ring.toUInt8_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h0
  have b := ZMod.val_lt ((PublicKey.equiv pk)[(⟨i, hi⟩ : Fin 512)])
  have b' := ZMod.val_lt ((PublicKey.equiv pk')[(⟨i, hi⟩ : Fin 512)])
  have l1 := GordieHowe.Ring.toUInt8_inj (by omega) (by omega) h1
  have := Nat.div_add_mod ((PublicKey.equiv pk)[(⟨i, hi⟩ : Fin 512)]).val 256
  have := Nat.div_add_mod ((PublicKey.equiv pk')[(⟨i, hi⟩ : Fin 512)]).val 256
  simp only [Fin.getElem_fin] at *
  omega

/-- A ring as one length byte followed by `64` slots of `1024` bytes (`GordieHowe.Ring.ringBytes`
at `keyBytes`): slot `a` holds the bytes of the `a`-th key when `a` is below the ring's length,
and zeros otherwise. -/
abbrev ringBytes (R : RingSignature.KeyRing PublicKey 64) : Fin (1 + 64 * 1024) → UInt8 :=
  GordieHowe.Ring.ringBytes keyBytes R

/-- **`ringBytes` is injective.** -/
theorem ringBytes_injective : Function.Injective ringBytes :=
  GordieHowe.Ring.ringBytes_injective keyBytes_injective (by norm_num)

/-- The ring message `m ‖ encode R`: the `32` message bytes followed by `ringBytes R`
(`GordieHowe.Ring.encodeRingMsg` at `keyBytes`). -/
abbrev encodeRingMsg (R : RingSignature.KeyRing PublicKey 64) (m : Fin 32 → UInt8) :
    Fin ringMsgLen → UInt8 :=
  GordieHowe.Ring.encodeRingMsg keyBytes R m

/-- **`encodeRingMsg` is injective in the ring and the message.** -/
theorem encodeRingMsg_inj {R R' : RingSignature.KeyRing PublicKey 64} {m m' : Fin 32 → UInt8}
    (h : encodeRingMsg R m = encodeRingMsg R' m') : R = R' ∧ m = m' :=
  GordieHowe.Ring.encodeRingMsg_inj keyBytes_injective (by norm_num) h

/-- **`encodeRingMsg R` is injective in the message**, at every ring `R`. -/
theorem encodeRingMsg_injective (R : RingSignature.KeyRing PublicKey 64) :
    Function.Injective (encodeRingMsg R) :=
  fun _ _ h => (encodeRingMsg_inj h).2

/-- **The Falcon-512 base signer at `encodeRingMsg` binds the ring.** -/
theorem bindsRing_encodeRingMsg {X Y : Type} (G : Signer ringMsgLen) :
    (GordieHowe.Ring.falconBaseSigner (X := X) (Y := Y) (N := 64) G encodeRingMsg).BindsRing :=
  fun _ _ _ _ h => encodeRingMsg_inj h

end GordieHowe.Falcon512.Ring
