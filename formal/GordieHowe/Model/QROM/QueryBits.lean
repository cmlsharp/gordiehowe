-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Oracle
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.ZMod.Defs

@[expose] public section

/-!
# The oracle queries as bit strings

CMS19 (Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum Random Oracle Model",
ePrint 2019/834, section 4.2, p. 19) state their results for a random oracle
`h : {0,1}^m → {0,1}^n`. The quantum objects of this development (`GordieHowe/Model/QROM/Compressed.lean`,
`GordieHowe/Model/QROM/Lifting.lean`) are over that domain, `Bits m`, and the tagged queries of the chain
model (`Query k kN kS L`, `GordieHowe/Model/QROM/Oracle.lean`) enter it through the injective encoding
`Query.toBits : Query k kN kS L ↪ Bits (queryBits k kN kS L)`:

    tag byte ‖ payload ‖ zero padding

with tags `0` (`leaf`), `1` (`node`), `2` (`transcript`), `3` (`xof`), each byte as 8 bits,
a digest as its `k` bytes, a Merkle salt as its `kN` bytes, a Fiat–Shamir salt as its `kS` bytes, and a byte
string of at most `L` bytes (`Bytes L`) as its length in `Nat.size L` bits followed by its bytes,
zero-padded to `L` bytes. The payloads are: `leaf` a Merkle salt and a byte string
(`8kN + Nat.size L + 8L` bits), `node` two digests (`16k`), `transcript` a byte string
(`Nat.size L + 8L`), `xof` a key and a Fiat–Shamir salt (`8k + 8kS`). Each is zero-padded to the largest,
`payloadBits k kN kS L = max (8kN + 8L + Nat.size L) (max (16k) (8k + 8kS))` bits. In the C++
format (`kN = 2k`, `kS = k`, b90f5046) this is `16k + 8L + Nat.size L`.

The encoding is an idealization of the hash inputs, not a transcription of the C++ input formats:
the modelling claim is that SHA-384 / SHA-256 on the leaf (Merkle salt and column), node and
transcript inputs and cSHAKE256 with the customization string `"Longfellow-FS-XOF-v1"`
(`lib/random/transcript.h` lines 53, 72-131) on the `key ‖ seed` inputs, injectively padded to
`queryBits k kN kS L` bits, are independent uniformly random functions. The model's one oracle
`{0,1}^(queryBits k kN kS L) → {0,1}^(8(k + e))` simulates them, with the same number of queries:
- the hashes answer `k` bytes and the model's hash-role answers are the `k`-byte prefix
  (`Out.digest`); a real query with a `k`-byte answer register is a model query whose other
  `8e` answer qubits are in the uniform superposition, which XOR leaves unchanged;
- real queries outside the encoded domain are answered by an independent random function that
  the adversary simulates in its work register (a purified truth table, after a test of the
  input format), one model query per real query.

Only injectivity of the encoding is used.
-/

namespace GordieHowe.QROM

/-- An `m`-bit string, the paper's `{0,1}^m`. -/
abbrev Bits (m : ℕ) := Fin m → Bool

namespace Bits

variable {a b c : ℕ}

/-- `u ‖ v`. -/
def append (u : Bits a) (v : Bits b) : Bits (a + b) := Fin.append u v

theorem append_inj {u u' : Bits a} {v v' : Bits b} :
    append u v = append u' v' ↔ u = u' ∧ v = v' := by
  refine ⟨fun h => ⟨funext fun i => ?_, funext fun i => ?_⟩, fun ⟨hu, hv⟩ => hu ▸ hv ▸ rfl⟩
  · simpa [append] using congrFun h (Fin.castAdd b i)
  · simpa [append] using congrFun h (Fin.natAdd a i)

/-- `v` followed by zeros, to `c ≥ a` bits. -/
def pad (_h : a ≤ c) (v : Bits a) : Bits c := fun i => if hi : i.1 < a then v ⟨i, hi⟩ else false

theorem pad_injective (h : a ≤ c) : Function.Injective (pad h) := fun v v' e =>
  funext fun i => by simpa [pad] using congrFun e (Fin.castLE h i)

/-- The `w`-bit strings are the numbers below `2^w` (binary digits, through
`finFunctionFinEquiv`). -/
def equivFin (w : ℕ) : Bits w ≃ Fin (2 ^ w) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- A byte as 8 bits. -/
def byteEquiv : Byte ≃ Bits 8 := (finCongr (by norm_num)).trans (equivFin 8).symm

/-- A string of `n` bytes as `8n` bits, byte by byte. -/
def bytesEquiv (n : ℕ) : (Fin n → Byte) ≃ Bits (n * 8) :=
  (Equiv.arrowCongr (Equiv.refl _) byteEquiv).trans <|
    (Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _))

/-- A byte string of at most `L` bytes: its length in `Nat.size L` bits, then its bytes,
zero-padded to `L` bytes. -/
def ofByteString {L : ℕ} (s : Bytes L) : Bits (Nat.size L + L * 8) :=
  append ((equivFin _).symm (Fin.castLE (Nat.lt_size_self L) s.len))
    (pad (Nat.mul_le_mul_right 8 (Nat.le_of_lt_succ s.len.2)) (bytesEquiv s.len s.data))

theorem ofByteString_injective {L : ℕ} : Function.Injective (ofByteString (L := L)) := by
  rintro ⟨n, v⟩ ⟨n', v'⟩ h
  obtain ⟨hn, hv⟩ := append_inj.1 h
  obtain rfl : n = n' := Fin.castLE_injective _ ((equivFin _).symm.injective hn)
  obtain rfl := (bytesEquiv n).injective (pad_injective _ hv)
  rfl

/-- A tag byte followed by a payload zero-padded to `c` bits. -/
def frame (t : Byte) (h : a ≤ c) (v : Bits a) : Bits (8 + c) := append (byteEquiv t) (pad h v)

theorem tag_eq_of_frame_eq {t t' : Byte} {h : a ≤ c} {h' : b ≤ c} {v : Bits a} {v' : Bits b}
    (e : frame t h v = frame t' h' v') : t = t' :=
  byteEquiv.injective (append_inj.1 e).1

theorem frame_injective (t : Byte) (h : a ≤ c) : Function.Injective (frame t h) := fun _ _ e =>
  pad_injective h (append_inj.1 e).2

/-- The first `a` bits of an `(a + b)`-bit string, the left part of `u ‖ v`. -/
def takeLeft (w : Bits (a + b)) : Bits a := fun i => w (Fin.castAdd b i)

/-- The last `b` bits of an `(a + b)`-bit string, the right part of `u ‖ v`. -/
def takeRight (w : Bits (a + b)) : Bits b := fun i => w (Fin.natAdd a i)

@[simp] theorem takeLeft_append (u : Bits a) (v : Bits b) : takeLeft (append u v) = u :=
  funext fun i => by simp [takeLeft, append]

@[simp] theorem takeRight_append (u : Bits a) (v : Bits b) : takeRight (append u v) = v :=
  funext fun i => by simp [takeRight, append]

/-- The first `a` bits of a `c`-bit string, the left inverse of `pad`. -/
def unpad (h : a ≤ c) (w : Bits c) : Bits a := fun i => w (Fin.castLE h i)

@[simp] theorem unpad_pad (h : a ≤ c) (v : Bits a) : unpad h (pad h v) = v :=
  funext fun i => by simp [unpad, pad]

/-- **The decoding of a byte string** from its `Nat.size L` length bits and `L` padded bytes:
the length read from the first bits, `none` when it exceeds `L`, then that many bytes. A left
inverse of `ofByteString` (`toByteString_ofByteString`). -/
def toByteString {L : ℕ} (w : Bits (Nat.size L + L * 8)) : Option (Bytes L) :=
  let n := (equivFin _ (takeLeft w)).val
  if hn : n < L + 1 then
    some ⟨⟨n, hn⟩, (bytesEquiv n).symm
      (unpad (Nat.mul_le_mul_right 8 (Nat.le_of_lt_succ hn)) (takeRight w))⟩
  else none

theorem toByteString_of_len {L : ℕ} (w : Bits (Nat.size L + L * 8)) {n : ℕ} (hn : n < L + 1)
    (hlen : (equivFin _ (takeLeft w)).val = n) :
    toByteString w = some ⟨⟨n, hn⟩, (bytesEquiv n).symm
      (unpad (Nat.mul_le_mul_right 8 (Nat.le_of_lt_succ hn)) (takeRight w))⟩ := by
  subst hlen
  simp [toByteString, hn]

theorem toByteString_ofByteString {L : ℕ} (s : Bytes L) : toByteString (ofByteString s) = some s := by
  obtain ⟨⟨n, hn⟩, v⟩ := s
  rw [toByteString_of_len _ hn (by simp [ofByteString])]
  simp [ofByteString]

end Bits

variable {k kN kS L : ℕ}

/-- The payload width of an encoded query: the largest payload, a `kN`-byte Merkle salt and a byte
string of at most `L` bytes (`8kN + 8L + Nat.size L` bits), two digests (`16k`), or a key and a
Fiat–Shamir salt (`8k + 8kS`); a byte string alone is shorter than a leaf. -/
def payloadBits (k kN kS L : ℕ) : ℕ := max (8 * kN + 8 * L + Nat.size L) (max (16 * k) (8 * k + 8 * kS))

theorem leaf_le_payloadBits : kN * 8 + (Nat.size L + L * 8) ≤ payloadBits k kN kS L := by
  unfold payloadBits
  have := le_max_left (8 * kN + 8 * L + Nat.size L) (max (16 * k) (8 * k + 8 * kS))
  omega

theorem node_le_payloadBits : k * 8 + k * 8 ≤ payloadBits k kN kS L := by
  unfold payloadBits
  have := le_max_right (8 * kN + 8 * L + Nat.size L) (max (16 * k) (8 * k + 8 * kS))
  have := le_max_left (16 * k) (8 * k + 8 * kS)
  omega

theorem transcript_le_payloadBits : Nat.size L + L * 8 ≤ payloadBits k kN kS L := by
  unfold payloadBits
  have := le_max_left (8 * kN + 8 * L + Nat.size L) (max (16 * k) (8 * k + 8 * kS))
  omega

theorem xof_le_payloadBits : k * 8 + kS * 8 ≤ payloadBits k kN kS L := by
  unfold payloadBits
  have := le_max_right (8 * kN + 8 * L + Nat.size L) (max (16 * k) (8 * k + 8 * kS))
  have := le_max_right (16 * k) (8 * k + 8 * kS)
  omega

/-- The bit length `m` of an encoded query: a tag byte and the payload. -/
def queryBits (k kN kS L : ℕ) : ℕ := 8 + payloadBits k kN kS L

open Bits in
/-- The encoding of a query: tag byte (`0` leaf, `1` node, `2` transcript, `3` xof), payload,
zero padding. -/
def Query.bits : Query k kN kS L → Bits (queryBits k kN kS L)
  | .leaf nonce col => frame 0 leaf_le_payloadBits
      (append (bytesEquiv kN nonce) (ofByteString col))
  | .node l r => frame 1 node_le_payloadBits
      (append (bytesEquiv k l) (bytesEquiv k r))
  | .transcript pre => frame 2 transcript_le_payloadBits (ofByteString pre)
  | .xof key seed => frame 3 xof_le_payloadBits
      (append (bytesEquiv k key) (bytesEquiv kS seed))

open Bits in
theorem Query.bits_injective : Function.Injective (Query.bits (k := k) (kN := kN) (kS := kS) (L := L)) := by
  intro q q' h
  cases q <;> cases q' <;>
    first
    | exact absurd (tag_eq_of_frame_eq h) (by decide)
    | skip
  · obtain ⟨h1, h2⟩ := append_inj.1 (frame_injective _ _ h)
    rw [(bytesEquiv kN).injective h1, ofByteString_injective h2]
  · obtain ⟨h1, h2⟩ := append_inj.1 (frame_injective _ _ h)
    rw [(bytesEquiv k).injective h1, (bytesEquiv k).injective h2]
  · rw [ofByteString_injective (frame_injective _ _ h)]
  · obtain ⟨h1, h2⟩ := append_inj.1 (frame_injective _ _ h)
    rw [(bytesEquiv k).injective h1, (bytesEquiv kS).injective h2]

/-- **The oracle queries as bit strings**: the injective encoding of `Query k kN kS L` into the
paper's oracle domain `{0,1}^m`, `m = queryBits k kN kS L`. -/
def Query.toBits : Query k kN kS L ↪ Bits (queryBits k kN kS L) := ⟨Query.bits, Query.bits_injective⟩

open Bits in
/-- **The decoding of an encoded query**, by its tag byte: the payload's parts read back
(`takeLeft`, `takeRight`, `unpad`, `toByteString`), `none` at an unused tag or a byte-string length
above `L`. A left inverse of `Query.bits` (`decode_bits`); it does not check the zero padding,
which `Query.ofBits` does by re-encoding. -/
def Query.decode (w : Bits (queryBits k kN kS L)) : Option (Query k kN kS L) :=
  let p : Bits (payloadBits k kN kS L) := takeRight w
  match byteEquiv.symm (takeLeft w) with
  | 0 =>
    let v := unpad leaf_le_payloadBits p
    (toByteString (takeRight v)).map (.leaf ((bytesEquiv kN).symm (takeLeft v)))
  | 1 =>
    let v := unpad node_le_payloadBits p
    some (.node ((bytesEquiv k).symm (takeLeft v)) ((bytesEquiv k).symm (takeRight v)))
  | 2 => (toByteString (unpad transcript_le_payloadBits p)).map .transcript
  | 3 =>
    let v := unpad xof_le_payloadBits p
    some (.xof ((bytesEquiv k).symm (takeLeft v)) ((bytesEquiv kS).symm (takeRight v)))
  | _ => none

open Bits in
theorem Query.decode_bits (q : Query k kN kS L) : Query.decode q.bits = some q := by
  cases q <;>
    simp [Query.decode, Query.bits, frame, toByteString_ofByteString]

/-- **The decoding of an oracle input as a query**: `Query.decode`, kept when re-encoding gives the
input back. One pass over the `queryBits k kN kS L` bits and one re-encoding. -/
def Query.ofBits (w : Bits (queryBits k kN kS L)) : Option (Query k kN kS L) :=
  (Query.decode w).filter fun q => decide (q.bits = w)

/-- **`Query.ofBits` inverts `Query.toBits`**: it decodes `w` to `q` exactly when `w` encodes `q`. -/
theorem Query.ofBits_eq_some_iff {w : Bits (queryBits k kN kS L)} {q : Query k kN kS L} :
    Query.ofBits w = some q ↔ Query.toBits q = w := by
  constructor
  · intro h
    obtain ⟨-, hq⟩ := Option.filter_eq_some_iff.1 h
    exact of_decide_eq_true hq
  · rintro rfl
    exact Option.filter_eq_some_iff.2 ⟨decode_bits q, decide_eq_true rfl⟩

/-! ### The quantum oracle's range -/

/-- The range of the quantum oracle: `k + e` bytes of 8 bits each, added bitwise (XOR). -/
abbrev XOut (k e : ℕ) := Fin (k + e) → Fin 8 → ZMod 2

/-- A bit as an element of `ZMod 2`. -/
def boolZModTwo : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := z = 1
  left_inv b := by cases b <;> rfl
  right_inv z := by fin_cases z <;> rfl

/-- A byte as 8 bits in `ZMod 2` (`Bits.byteEquiv`). -/
def byteBitsEquiv : Byte ≃ (Fin 8 → ZMod 2) :=
  Bits.byteEquiv.trans (Equiv.piCongrRight fun _ => boolZModTwo)

/-- The answer of the quantum oracle read as the `k + e` bytes of the chain model's answer. -/
def outEquiv (k e : ℕ) : XOut k e ≃ Out k e :=
  ((Equiv.piCongrRight fun _ => byteBitsEquiv.symm).trans (Fin.appendEquiv k e).symm).trans
    Out.equivProd.symm

end GordieHowe.QROM
