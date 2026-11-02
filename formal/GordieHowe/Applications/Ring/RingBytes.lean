-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Scheme

@[expose] public section

/-!
# Fixed-length encoding of a ring and a message

The base message `m ‖ encode R` of a ring-binding ring signature (BKM06 §5) as an injective
fixed-length byte string, for keys with an injective fixed-length byte encoding `kb : PK → Fin L →
UInt8` and rings of at most `N ≤ 255` keys.

- `fin_append_inj`, `toUInt8_inj`: `Fin.append` is injective in both parts, and `Nat.toUInt8` is
  injective below `256`.
- `ringBytes kb`, `ringBytes_injective`: a ring as one length byte and `N` slots of `L` bytes, slot
  `a` the bytes of the `a`-th key and zeros past the ring's length.
- `encodeRingMsg kb`, `encodeRingMsg_inj`, `encodeRingMsg_injective`: the message followed by the
  ring's bytes, injective in both and in the message at each ring.
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature

/-- **`Fin.append` is injective in both parts.** -/
theorem fin_append_inj {α : Type} {m n : ℕ} {a a' : Fin m → α} {b b' : Fin n → α}
    (h : Fin.append a b = Fin.append a' b') : a = a' ∧ b = b' := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · simpa using congrFun h (Fin.castAdd n i)
  · simpa using congrFun h (Fin.natAdd m i)

/-- **`Nat.toUInt8` is injective below `256`.** -/
theorem toUInt8_inj {x y : ℕ} (hx : x < 256) (hy : y < 256) (h : x.toUInt8 = y.toUInt8) :
    x = y := by
  have := congrArg UInt8.toNat h
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat'] at this
  omega

variable {PK : Type} {L N : ℕ} (kb : PK → Fin L → UInt8)

/-- **A ring as one length byte followed by `N` slots of `L` bytes**: slot `a` holds the bytes of
the `a`-th key when `a` is below the ring's length, and zeros otherwise. -/
def ringBytes (R : KeyRing PK N) : Fin (1 + N * L) → UInt8 :=
  Fin.append (fun _ : Fin 1 => R.1.length.toUInt8) fun j =>
    if h : (finProdFinEquiv.symm j).1.1 < R.1.length then
      kb (R.1[(finProdFinEquiv.symm j).1.1]) (finProdFinEquiv.symm j).2
    else 0

variable {kb}

/-- **`ringBytes kb` is injective** for an injective key encoding and rings of at most `255`
keys. -/
theorem ringBytes_injective (hkb : Function.Injective kb) (hN : N < 256) :
    Function.Injective (ringBytes (N := N) kb) := by
  rintro ⟨l, hl⟩ ⟨l', hl'⟩ h
  obtain ⟨hlen, hslots⟩ := fin_append_inj h
  have hlen' : l.length = l'.length :=
    toUInt8_inj (by omega) (by omega) (congrFun hlen 0)
  apply Subtype.ext
  apply List.ext_getElem hlen'
  intro a ha ha'
  apply hkb
  funext k
  have := congrFun hslots (finProdFinEquiv (⟨a, by omega⟩, k))
  simpa [Equiv.symm_apply_apply, ha, ha'] using this

variable (kb) in
/-- **The ring message `m ‖ encode R`**: the `mLen` message bytes followed by `ringBytes kb R`. -/
def encodeRingMsg {mLen : ℕ} (R : KeyRing PK N) (m : Fin mLen → UInt8) :
    Fin (mLen + (1 + N * L)) → UInt8 :=
  Fin.append m (ringBytes kb R)

/-- **`encodeRingMsg kb` is injective in the ring and the message.** -/
theorem encodeRingMsg_inj (hkb : Function.Injective kb) (hN : N < 256) {mLen : ℕ}
    {R R' : KeyRing PK N} {m m' : Fin mLen → UInt8}
    (h : encodeRingMsg kb R m = encodeRingMsg kb R' m') : R = R' ∧ m = m' := by
  obtain ⟨hm, hR⟩ := fin_append_inj h
  exact ⟨ringBytes_injective hkb hN hR, hm⟩

/-- **`encodeRingMsg kb R` is injective in the message**, at every ring `R`. -/
theorem encodeRingMsg_injective (hkb : Function.Injective kb) (hN : N < 256) {mLen : ℕ}
    (R : KeyRing PK N) : Function.Injective (encodeRingMsg (mLen := mLen) kb R) :=
  fun _ _ h => (encodeRingMsg_inj hkb hN h).2

end GordieHowe.Ring
