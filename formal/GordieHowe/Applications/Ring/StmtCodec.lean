-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.SPBCS.Format.ListCodec
public import GordieHowe.ProofSystem.Program.Transcript.Format

@[expose] public section

/-!
# The statement writes of a ring program and the keys of a ring statement

The pieces of a compiled ring program's statement that do not depend on the base scheme, for a
ring statement `GordieHowe.Ring.RingStmt Sch M N` (`GordieHowe/Applications/Ring/Scheme.lean`):

- `RingStmt.keyAt`, `RingStmt.keyAt_eq`: the key at a position of the ring (the default key past
  its end), read by the program's statement map.
- `ringCodec kc N`: a ring of at most `N` keys written as the list of its keys
  (`GordieHowe.SPBCS.Codec.list`) of the key codec `kc`.
- `bytesEquiv`: bytes as `UInt8`s.
- `stmtCodec kc mc pc N`: a ring statement written as its ring, its message (the codec `mc`;
  `msgCodec msgLen`, `Codec.bstr msgLen`, for `msgLen` bytes) and its public value (the codec
  `pc`), self-delimiting, so prefix-free (`Codec.prefixFree`). `length_ser_stmtCodec_le`: with
  keys of `L` bytes, messages of at most `K` bytes and public values of at most `P` bytes, at most
  `N · (L + 1) + 1 + K + P` bytes.
-/

namespace GordieHowe.Ring

open GordieHowe.SPBCS GordieHowe.QROM

variable {Sch : SigScheme} {M : Type} {N : ℕ}

/-- **The key at a position of a ring statement's ring** (the default key past the end). -/
def RingStmt.keyAt [Inhabited Sch.PK] (x : RingStmt Sch M N) (j : ℕ) : Sch.PK :=
  x.ring.1.getD j default

theorem RingStmt.keyAt_eq [Inhabited Sch.PK] {x : RingStmt Sch M N} {j : ℕ}
    (hj : j < x.ring.1.length) : x.keyAt j = x.ring.1[j]'hj := by
  unfold RingStmt.keyAt
  simp [hj]

/-- **The codec of a ring of at most `N` keys**: the list of its keys. -/
def ringCodec {PK : Type} (kc : Codec PK) (N : ℕ) : Codec (RingOf PK N) :=
  (Codec.list kc).mapPartial Subtype.val
    (fun l => if h : l.length ≤ N then some ⟨l, h⟩ else none)
    (fun R => by simp [R.2]) (by
      intro l R h
      split_ifs at h with hl
      cases h
      rfl)

/-- Bytes as `UInt8`s. -/
def bytesEquiv (m : ℕ) : (Fin m → UInt8) ≃ (Fin m → Byte) :=
  Equiv.arrowCongr (.refl _) UInt8.equivFin

variable (Sch M N) in
/-- A ring statement is its ring, message and public value. -/
def stmtEquiv : RingStmt Sch M N ≃ RingOf Sch.PK N × (M × Sch.Pub) where
  toFun x := (x.ring, x.msg, x.pub)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The codec of a ring statement** of rings of at most `N` keys: the ring (`ringCodec kc N`),
the message (`mc`) and the public value (`pc`). -/
def stmtCodec (kc : Codec Sch.PK) (mc : Codec M) (pc : Codec Sch.Pub) (N : ℕ) :
    Codec (RingStmt Sch M N) :=
  ((ringCodec kc N).prod (mc.prod pc)).mapEquiv (stmtEquiv Sch M N)

/-- **A ring statement's writes** have at most `N · (L + 1) + 1 + K + P` bytes, for keys written
in `L` bytes (`hk`), messages in at most `K` bytes (`hm`) and public values in at most `P` bytes
(`hp`). -/
theorem length_ser_stmtCodec_le {kc : Codec Sch.PK} {mc : Codec M} {pc : Codec Sch.Pub}
    {L K P : ℕ} (hk : ∀ k, (kc.ser k).length = L) (hm : ∀ m, (mc.ser m).length ≤ K)
    (hp : ∀ y, (pc.ser y).length ≤ P) (x : RingStmt Sch M N) :
    ((stmtCodec kc mc pc N).ser x).length ≤ N * (L + 1) + 1 + K + P := by
  have hl := Codec.length_ser_list kc hk x.ring.1
  have hr : x.ring.1.length ≤ N := x.ring.2
  have hser : (stmtCodec kc mc pc N).ser x = (Codec.list kc).ser x.ring.1 ++
      (mc.ser x.msg ++ pc.ser x.pub) := rfl
  rw [hser]
  simp only [List.length_append, hl]
  have := hp x.pub
  have := hm x.msg
  nlinarith

/-- **The codec of `msgLen` message bytes**: `bstr msgLen`. -/
def msgCodec (msgLen : ℕ) : Codec (Fin msgLen → UInt8) :=
  (Codec.bstr msgLen).mapEquiv (bytesEquiv msgLen)

theorem length_ser_msgCodec (msgLen : ℕ) (m : Fin msgLen → UInt8) :
    ((msgCodec msgLen).ser m).length = 9 + msgLen := by
  change ((Codec.bstr msgLen).ser _).length = _
  simp only [Codec.bstr, Codec.length_ser_framed, List.length_cons, Enc.length_le64]

end GordieHowe.Ring
