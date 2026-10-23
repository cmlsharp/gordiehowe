-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.System.Scheme
public import GordieHowe.SPBCS.Format.ListCodec
public import GordieHowe.ProofSystem.Program.Transcript.Format

@[expose] public section

/-!
# Falcon ring, native arm: the statement writes and the label

* **The statement writes** (`stmtCodecN`): the ring as a list of keys (`GordieHowe.SPBCS.Codec.list` of the key
  codec, `falconKeyWrites`: `512` coefficients of `2` bytes in a length-framed array), the message
  bytes (`Codec.bstr`) and the salt (`Codec.bstr 40`), self-delimiting, so prefix-free
  (`Codec.prefixFree`). The C++ writes the ring dimension, the ring size, the keys and `c`
  (`falcon_ring_profile.h`, `falcon_ring_statement_parts`); the Lean writes the message and the
  salt from which the verifier computes `c` (exact byte identity is not a goal).
* **The label** (`label`): `gordiehowe:falcon-ring-native`.
-/

namespace GordieHowe.Falcon512.Ring.Native

open IOP GordieHowe.QROM GordieHowe.SPBCS SPBCS.Configurations GordieHowe.Ring
open scoped NNReal ENNReal

/-! ### The statement writes -/

/-- **The codec of a public key**: its `512` coefficients as an array of `2`-byte elements
(`falconKeyWrites`). -/
def keyCodec : Codec PublicKey :=
  (Codec.fieldArray falconCoeffBytes 512).mapEquiv (PublicKey.equiv.trans (Vector.equivFun _ _))

/-- A key's bytes are `falconKeyWrites`, `1033` bytes. -/
theorem length_ser_keyCodec (pk : PublicKey) : (keyCodec.ser pk).length = 1033 :=
  Codec.length_ser_fieldArray falconCoeffBytes 512 _

/-- **The codec of a ring of at most `N` keys**: the list of its keys. -/
def ringCodecN (N : ℕ) : Codec (RingOf PublicKey N) :=
  (Codec.list keyCodec).mapPartial Subtype.val
    (fun l => if h : l.length ≤ N then some ⟨l, h⟩ else none)
    (fun R => by simp [R.2]) (by
      intro l R h
      split_ifs at h with hl
      cases h
      rfl)

/-- Bytes as `UInt8`s. -/
def bytesEquiv (m : ℕ) : (Fin m → UInt8) ≃ (Fin m → Byte) := Equiv.arrowCongr (.refl _) UInt8.equivFin

variable {msgLen : ℕ} {G : Signer msgLen}

variable {msgLen : ℕ} {G : Signer msgLen}

variable (G) in
/-- A ring statement of rings of at most `N` keys is its ring, message and salt. -/
def stmtEquivN (N : ℕ) : RingStmt (scheme G) (Fin msgLen → UInt8) N ≃
    RingOf PublicKey N × ((Fin msgLen → UInt8) × Salt) where
  toFun x := (x.ring, x.msg, x.pub)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (G) in
/-- **The codec of a ring statement of rings of at most `N` keys**: the ring, the message bytes
(`bstr msgLen`) and the salt (`bstr 40`). -/
def stmtCodecN (N : ℕ) : Codec (RingStmt (scheme G) (Fin msgLen → UInt8) N) :=
  ((ringCodecN N).prod ((Codec.bstr msgLen).mapEquiv (bytesEquiv msgLen) |>.prod
    ((Codec.bstr 40).mapEquiv ((Vector.equivFun UInt8 40).trans (bytesEquiv 40))))).mapEquiv
    (stmtEquivN G N)

/-- **A ring statement's writes** have at most `N · 1034 + 1 + 9 + msgLen + 49` bytes. -/
theorem length_ser_stmtCodecN_le {N : ℕ} (x : RingStmt (scheme G) (Fin msgLen → UInt8) N) :
    ((stmtCodecN G N).ser x).length ≤ N * 1034 + 1 + (9 + msgLen) + (9 + 40) := by
  have hl := Codec.length_ser_list keyCodec length_ser_keyCodec x.ring.1
  have hr : x.ring.1.length ≤ N := x.ring.2
  have hser : (stmtCodecN G N).ser x = (Codec.list keyCodec).ser x.ring.1 ++
      ((Codec.bstr msgLen).ser (bytesEquiv msgLen x.msg) ++
        (Codec.bstr 40).ser (bytesEquiv 40 ((Vector.equivFun UInt8 40) x.pub))) := rfl
  rw [hser]
  simp only [List.length_append, hl, Codec.bstr, Codec.length_ser_framed, List.length_cons,
    Enc.length_le64]
  nlinarith

/-- **The label write of the native Falcon ring**: `gordiehowe:falcon-ring-native` (`system.h`,
`"gordiehowe:" + s.name()`). -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:falcon-ring-native")

end GordieHowe.Falcon512.Ring.Native
