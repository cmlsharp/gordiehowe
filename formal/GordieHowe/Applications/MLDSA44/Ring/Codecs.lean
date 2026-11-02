-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.RingEncoding
public import GordieHowe.ProofSystem.Program.Transcript.Format
public import GordieHowe.SPBCS.Format.SpecWrites

@[expose] public section

/-!
# The ML-DSA-44 rings: the statement writes and the labels

* **The statement writes** (`stmtCodecN`, the generic `GordieHowe.Ring.stmtCodec`): the ring as a
  list of keys (`keyCodec`: `ρ` as `bstr 32`, then the `1024` coefficients of `t₁` as one array of
  `3`-byte field elements of `ℤ_q`), the message representative (`bstr msgLen`) and no bytes for
  the public value `()`; self-delimiting, so prefix-free. The C++ writes the ring's encoded keys,
  the message and the context (`MLDSARingInputs::Statement`); the Lean writes the message
  representative from which the verifier computes every member's `µ` (exact byte identity is not
  a goal). `length_ser_stmtCodecN_le`: at most `N · 3123 + 1 + (9 + msgLen)` bytes.
* **The labels** (`labelNative`, `labelCarrier`): `gordiehowe:ml-dsa-44-private-ring` and
  `gordiehowe:ml-dsa-44-private-ring-carrier` (`system.h`, `"gordiehowe:" + s.name()`, the C++
  relations' names in `examples/rings/mldsa_ring_testing.h`).
-/

namespace GordieHowe.MLDSA44.Ring

open GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring

/-- The bytes of a coefficient of `ℤ_q`, `q = 8380417`: three little-endian bytes of its
representative in `[0, q)`. -/
def coeffBytes : Codec.FieldBytes _root_.MLDSA.Coeff 3 :=
  Codec.FieldBytes.ofEquiv (ZMod.finEquiv 8380417).symm.toEquiv (by norm_num)

/-- A key as its `ρ` bytes and the `1024` coefficients of `t₁` (`t1Coeff`). -/
def keyEquiv : PublicKey ≃ (Fin 32 → UInt8) × (Fin 1024 → _root_.MLDSA.Coeff) where
  toFun pk := (fun i => pk.rho.get i, t1Coeff pk)
  invFun x := ⟨Vector.ofFn x.1, Vector.ofFn fun i => LatticeCrypto.Poly.ofPi fun j =>
    x.2 (finProdFinEquiv (m := _root_.MLDSA.mldsa44.k) (n := _root_.MLDSA.ringDegree) (i, j))⟩
  left_inv pk := by
    obtain ⟨r, t⟩ := pk
    simp only [_root_.MLDSA.PublicKey.mk.injEq]
    refine ⟨Vector.ext fun i hi => by simp [Vector.get_eq_getElem], Vector.ext fun i hi => ?_⟩
    apply LatticeCrypto.Poly.ext_get_eq
    intro j
    simp only [t1Coeff]
    erw [Vector.getElem_ofFn, LatticeCrypto.Poly.get_ofPi]
    simp [Vector.get_eq_getElem]
  right_inv x := by
    obtain ⟨r, t⟩ := x
    refine Prod.ext (funext fun i => by simp [Vector.get_eq_getElem]) (funext fun c => ?_)
    simp only [t1Coeff]
    erw [Vector.get_ofFn, LatticeCrypto.Poly.get_ofPi]
    exact congrArg t ((finProdFinEquiv (m := _root_.MLDSA.mldsa44.k)
      (n := _root_.MLDSA.ringDegree)).apply_symm_apply c)

/-- **The codec of a public key**: `ρ` (`bstr 32`), then `t₁`'s coefficients as one array of
`1024` field elements of `ℤ_q` (`3` bytes each). -/
def keyCodec : Codec PublicKey :=
  (((Codec.bstr 32).mapEquiv (bytesEquiv 32)).prod (Codec.fieldArray coeffBytes 1024)).mapEquiv
    keyEquiv

/-- A key's bytes: `9 + 32` and `9 + 1024 · 3`, `3122` bytes. -/
theorem length_ser_keyCodec (pk : PublicKey) : (keyCodec.ser pk).length = 3122 := by
  change ((Codec.bstr 32).ser _ ++ (Codec.fieldArray coeffBytes 1024).ser _).length = 3122
  rw [List.length_append, Codec.length_ser_fieldArray]
  simp only [Codec.bstr, Codec.length_ser_framed, List.length_cons, Enc.length_le64]

/-- **The codec of the public value `()`**: no bytes. -/
def unitCodec : Codec Unit where
  ser _ := []
  parse s := some ((), s)
  parse_ser _ _ := rfl
  ser_parse {s a t} h := by
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl

/-- **The codec of a message representative**: `bstr msgLen` of its bytes. -/
def bytesCodec (msgLen : ℕ) : Codec (_root_.MLDSA.Bytes msgLen) :=
  (msgCodec msgLen).mapEquiv (Vector.equivFun UInt8 msgLen)

theorem length_ser_bytesCodec (msgLen : ℕ) (m : _root_.MLDSA.Bytes msgLen) :
    ((bytesCodec msgLen).ser m).length = 9 + msgLen :=
  length_ser_msgCodec msgLen _

variable {msgLen : ℕ}

variable (msgLen) in
/-- **The codec of a ring statement of rings of at most `N` keys**: the ring, the message
representative and no bytes for `()` (`GordieHowe.Ring.stmtCodec`). -/
abbrev stmtCodecN (N : ℕ) : Codec (GordieHowe.Ring.RingStmt (scheme msgLen) (_root_.MLDSA.Bytes msgLen) N) :=
  stmtCodec (Sch := scheme msgLen) keyCodec (bytesCodec msgLen) unitCodec N

/-- **A ring statement's writes** have at most `N · 3123 + 1 + (9 + msgLen)` bytes. -/
theorem length_ser_stmtCodecN_le {N : ℕ}
    (x : GordieHowe.Ring.RingStmt (scheme msgLen) (_root_.MLDSA.Bytes msgLen) N) :
    ((stmtCodecN msgLen N).ser x).length ≤ N * 3123 + 1 + (9 + msgLen) := by
  have := length_ser_stmtCodec_le (Sch := scheme msgLen) length_ser_keyCodec
    (fun m => (length_ser_bytesCodec msgLen m).le) (pc := unitCodec) (P := 0) (fun _ => le_refl _) x
  simpa using this

/-- **The label write of the native ML-DSA-44 ring**: `gordiehowe:ml-dsa-44-private-ring`. -/
def labelNative : List QROM.Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:ml-dsa-44-private-ring")

/-- **The label write of the ML-DSA-44 ring carrier**:
`gordiehowe:ml-dsa-44-private-ring-carrier`. -/
def labelCarrier : List QROM.Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:ml-dsa-44-private-ring-carrier")

end GordieHowe.MLDSA44.Ring
