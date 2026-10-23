-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.System.Hash
public import GordieHowe.Applications.MLDSA44.System.Params
public import GordieHowe.Applications.MLDSA44.Native.Rows

@[expose] public section

/-!
# ML-DSA: the source assignment

Used by both ML-DSA configurations: ML-DSA emulated uses ML-DSA native's domain H, MAC field
profile, layout and phases.

The assignment of ML-DSA native before the randomized lowerings
(`lib/gordiehowe/examples/mldsa/mldsa_native.h`, `mldsa_gadgets.h`, `mldsa_hash.h`): the
variables the application declares, by domain.

* Domain A: the hint `h` (`[K][N]` Bit private input), the challenge bits `challenge.c`
  (`[N][2]`, support and sign), `signature.w` (`w'`, `[K][N]`), the response `z` (`[L][N]`; the
  range lowering binds it to `norm.z`'s digits, so it has no cell), and UseHint's advice
  `hint.w1` (`[K][N][6]` bits), `hint.nonpositive` (`[K][N]` bits), `hint.offset` and
  `hint.slack` (`[K][N]`, bound to their digits).
* Domain H: the message bits `msg`, the Keccak trace (`h2c.*.states`, `Words`), H's copy `w1` of
  the UseHint output bits, the selected stream bytes `h2c.sample.select.j` (`[τ][8]` bits), and
  the decoded challenge `c_H` (`[N][2]`: circuit-only in the C++, the decoding of
  `h2c.sample.mem.c_enc`; the SampleInBall lowering's source reads it, and a storage binding
  replaces it by that decoding).

The crossing (`mldsa_gadgets.h:446-454`, one MAC for both equalities) is the `w1` bits then the
challenge bits, `2k` support and `2k + 1` sign (`GordieHowe.MLDSA44.HashCircuit.crossBits`, `cBits`), in `nch` chunks
of `w` bits: `xhOf` reads domain H's copy, `xaOf` domain A's.

`cBitsA` and `cBitsH` flatten the challenge blocks `[N][2]`; `sigWit` is the witness of the
signature rows.
-/

namespace GordieHowe.MLDSA44.Native

open GordieHowe.Bits Params

/-- **The source assignment of ML-DSA native**, for a `msgLen`-byte message, with domain H's
field `KH` and domain A's field `F`. -/
structure Source (KH F : Type) (msgLen : ℕ) where
  /-- The message bits (`msg`). -/
  msg : BitWires KH (8 * msgLen)
  /-- The Keccak trace words (`h2c.*.states`). -/
  states : Words KH msgLen
  /-- H's copy of the UseHint output bits (`w1`), bit `(i N + k) 6 + b`. -/
  w1H : BitWires KH (8 * 768)
  /-- The selected stream bytes (`h2c.sample.select.j`). -/
  j : Fin τ → BitWires KH 8
  /-- The decoded challenge (`c_H`): support and sign of coefficient `k`. -/
  chalH : Fin N → KH × KH
  /-- The hint (`h`). -/
  h : Fin nRows → Fin N → F
  /-- The challenge's support and sign bits (`challenge.c`), coefficient `k`, component `t`. -/
  cA : Fin N → Fin 2 → F
  /-- `w'` (`signature.w`). -/
  w : Fin nRows → Fin N → F
  /-- The response (`z`). -/
  z : Fin nCols → Fin N → F
  /-- The UseHint output bits (`hint.w1`), bit `(i N + k) 6 + b`. -/
  w1A : BitWires F (8 * 768)
  /-- The UseHint sign advice (`hint.nonpositive`). -/
  np : Fin nRows → Fin N → F
  /-- The UseHint offset advice (`hint.offset`). -/
  offset : Fin nRows → Fin N → F
  /-- The UseHint slack advice (`hint.slack`). -/
  slack : Fin nRows → Fin N → F

instance (P : Profile) : mldsa44.MACWidth P.macWidth :=
  ⟨Nat.mul_div_cancel' P.macWidth_dvd⟩

section SigWit

variable {KH F : Type} [Field F] [DecidableEq F] [CharP F _root_.MLDSA.modulus] {msgLen : ℕ}

/-- **The witness of the signature rows**: `w'`, `z`, and the challenge's support and sign bits. -/
def sigWit (a : Source KH F msgLen) : Rows.Wit F :=
  (a.w, a.z, fun k => a.cA k 0, fun k => a.cA k 1)

end SigWit

variable {KH F : Type} {msgLen : ℕ}

/-- The challenge bits of A as the flat `2 N` crossing bits. -/
def cBitsA (a : Source KH F msgLen) : BitWires F (2 * mldsa44.N) :=
  HashCircuit.cBits fun k => (a.cA k 0, a.cA k 1)

/-- The decoded challenge of H as the flat `2 N` crossing bits. -/
def cBitsH (a : Source KH F msgLen) : BitWires KH (2 * mldsa44.N) := HashCircuit.cBits a.chalH

variable (P : Profile)

/-- **H's crossing by MAC chunk**: bit `j` of chunk `c` is crossing bit `w c + j`. -/
def xhOf (a : Source KH F msgLen) (c : Fin P.nch) (j : Fin P.macWidth) : KH :=
  HashCircuit.crossBits (mw := P.macWidth) a.w1H (cBitsH a) ⟨P.macWidth * c + j,
    MAC.chunk_index_lt c.isLt j.isLt⟩

/-- **A's crossing by MAC chunk.** -/
def xaOf (a : Source KH F msgLen) (c : Fin P.nch) (j : Fin P.macWidth) : F :=
  HashCircuit.crossBits (mw := P.macWidth) a.w1A (cBitsA a) ⟨P.macWidth * c + j,
    MAC.chunk_index_lt c.isLt j.isLt⟩

/-- **Every crossing bit is a MAC bit**: bit `t` of the crossing is bit `t mod w` of chunk
`t / w`. -/
theorem exists_chunk (t : Fin (P.macWidth * P.nch)) :
    ∃ (c : Fin P.nch) (j : Fin P.macWidth), (⟨P.macWidth * c + j, MAC.chunk_index_lt c.isLt j.isLt⟩ :
      Fin (P.macWidth * P.nch)) = t := by
  obtain ⟨tv, ht⟩ := t
  have hw : 0 < P.macWidth := Nat.pos_of_ne_zero fun h => by
    simp [h] at ht
  refine ⟨⟨tv / P.macWidth, ?_⟩, ⟨tv % P.macWidth, Nat.mod_lt _ hw⟩, Fin.ext ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hw).mpr (by rwa [mul_comm] at ht)
  · exact Nat.div_add_mod tv P.macWidth

end GordieHowe.MLDSA44.Native
