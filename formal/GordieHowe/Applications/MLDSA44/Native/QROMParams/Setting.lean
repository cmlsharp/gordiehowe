-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Setting
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `MLDSA44.Native.QROMParams`

The data the series–parallel transcript of the BCS transformation is built from, for the protocol at the realized
program of the native ML-DSA-44 proof of possession at the QROM parameters (`GordieHowe.MLDSA44.Native.QROMParams.proofSystem`), with the
statement an encoded public key whose `ExpandA` finishes within the byte budget (`KeyStmt`), read through the
statement values it determines (`stmtOf`: `key.a_hat` the key's `Â`, `key.t1` its `t1`, `tr` the
bits of `H(pk)`; `iop`: the soundness IOP of the proof system at the frontend's round-by-round knowledge
soundness, `MultiCircuitIOP.comap stmtOf`). The transcript is in
`GordieHowe/Applications/MLDSA44/Native/QROMParams/Transcript.lean`, its statements in
`GordieHowe/Applications/MLDSA44/Native/QROMParams.lean`.

* **The statement** (`KeyStmt`, `keyStmtCodec`, `stmtOf`, `keyOf_stmtOf`): the program checks no
  statement (`StatementOk` holds everywhere). The verifier prepares `Â = ExpandA(ρ)` with every
  `RejNTTPoly` call within `1008` SHAKE128 bytes, as FIPS 204 Appendix C permits
  (`GordieHowe.MLDSA44.expandABounded`), so the statements are the keys at which `ExpandA`
  finishes within that budget (`GordieHowe.MLDSA44.ExpandAWithin`); at the others no signature
  verifies (`GordieHowe.MLDSA44.Verifies.expandA`).
* **The compiled circuits** (`Compiled`): the GKR sources with the trust bundle `CircuitsEnforce`.
* **The transcript data**: the label `gordiehowe:ml-dsa-44-possession`, the key-and-context
  writes, the phases' codecs (`GordieHowe.RealizedProgram.appWrites`: `32` bytes in `F_q^11`, `32` bytes in `GF(2^256)`), the C++ challenge readers of both
  fields and LogUp's `α` outside `[0, 512)`; the domains' codecs and readers are the generic
  per-field domain proofs' (`GordieHowe/Applications/MLDSA44/Native/QROMParams/Transcript.lean`).
-/

namespace GordieHowe.MLDSA44.Native.QROMParams
open ROMParams (VarWitness KeyOf rel aHatAt t1At trBits extractor proj)

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.MLDSA44.Native.QROMParams.Program (program)
open HashField (interp)
open scoped NNReal ENNReal

/-! ## The statement -/

/-- **The statements of the BCS transformation**: encoded ML-DSA-44 public keys whose `ExpandA`
finishes within the byte budget (`ROMParams.KeyStmt`, shared by the ML-DSA-44 configurations). -/
abbrev KeyStmt : Type := ROMParams.KeyStmt

/-- **The codec of a statement** (`ROMParams.keyStmtCodec`). -/
abbrev keyStmtCodec : Codec KeyStmt := ROMParams.keyStmtCodec

/-- The row of a coordinate of `key.a_hat`: `(4 i + j) · 256 + k` with `n < 4096`. -/
def aRow (n : ℕ) (hn : n < 4096) : Fin _root_.MLDSA.mldsa44.k :=
  ⟨n / 1024, by change n / 1024 < 4; omega⟩

/-- The column of a coordinate of `key.a_hat`. -/
def aCol (n : ℕ) : Fin _root_.MLDSA.mldsa44.l := ⟨n / 256 % 4, Nat.mod_lt _ (by decide)⟩

/-- The spectrum index of a coordinate of `key.a_hat`. -/
def aIdx (n : ℕ) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by norm_num)⟩

/-- **The statement values of a key and a matrix**: `key.a_hat` (value `56`) the entries of
`aHat` as naturals, `key.t1` (value `57`) the coefficients of `t1`, `tr` (value `67`) the bits of
`H(pk)` (`MLDSA44.PoP.Compose.trOf`), every other statement coordinate `0`. -/
def stmtOfKeyWith (pk : MLDSA44.PublicKey44)
    (aHat : _root_.MLDSA.TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) :
    program.Valuation interp := fun v i =>
  if h : v = 56 ∧ i < 4096 then
    RealizedProgram.castElt (a := 0) ((((aHat.get (aRow i h.2)).get (aCol i)).coeffs.get
      (aIdx i)).val : (interp 0).K)
  else if h : v = 57 ∧ i < 1024 then
    RealizedProgram.castElt (a := 0) (((pk.t1.get (⟨i / 256, by change i / 256 < 4; omega⟩ :
      Fin _root_.MLDSA.mldsa44.k)).get (aIdx i)).val : (interp 0).K)
  else if h : v = 67 ∧ i < 512 then
    RealizedProgram.castElt (a := 1) (Bits.constBit (K := (interp 1).K)
      (MLDSA44.PoP.Compose.trOf pk ⟨i / 8, by omega⟩).toNat (i % 8))
  else 0

/-- **The statement values of a key** (`stmtOfKeyWith` at `Â = ExpandA(ρ)`,
`Rows.aHat`). -/
noncomputable def stmtOfKey (pk : MLDSA44.PublicKey44) : program.Valuation interp :=
  stmtOfKeyWith pk (Rows.aHat pk)

/-- **The statement values of a statement**: the values of its decoded key, with
`Â = ExpandA(ρ)` computed within the byte budget by `MLDSA44.expandABounded`.

Running time: `MLDSA44.expandABounded`'s (`16 · 336` SHAKE128 candidates), then a table lookup
per coordinate. -/
def stmtOf (s : KeyStmt) : program.Valuation interp :=
  stmtOfKeyWith (MLDSA44.pkDecode44 s.1.key)
    (MLDSA44.expandABounded _root_.MLDSA.mldsa44 (MLDSA44.pkDecode44 s.1.key).rho)

/-- A statement's values are its decoded key's. -/
theorem stmtOf_eq (s : KeyStmt) : stmtOf s = stmtOfKey (MLDSA44.pkDecode44 s.1.key) := by
  rw [stmtOf, MLDSA44.expandABounded_eq_expandAFull s.2]
  rfl

/-- A value read in the field it was cast to and back is itself. -/
theorem castElt_castElt {a b : ℕ} (h : b = a) (x : (interp a).K) :
    RealizedProgram.castElt (b := a) (RealizedProgram.castElt (a := a) (b := b) x) = x := by
  subst h
  simp

/-- **A key's statement holds the key's preprocessing** (`KeyOf`). -/
theorem keyOf_stmtOfKey (pk : MLDSA44.PublicKey44) : KeyOf pk (stmtOfKey pk) where
  aHat i j k := by
    have hn : ((i : ℕ) * 4 + j) * 256 + k < 4096 := by omega
    unfold aHatAt
    rw [RealizedProgram.evalE_leaf]
    unfold stmtOfKey stmtOfKeyWith
    rw [dif_pos ⟨rfl, hn⟩, castElt_castElt (by decide +kernel)]
    have hr : aRow _ hn = i := Fin.ext (by simp only [aRow]; omega)
    have hc : aCol (((i : ℕ) * 4 + j) * 256 + k) = j := Fin.ext (by simp only [aCol]; omega)
    have hk : aIdx (((i : ℕ) * 4 + j) * 256 + k) = k := Fin.ext (by simp only [aIdx]; omega)
    rw [hr, hc, hk]
    exact ROMParams.toNat_fq6_natCast (ZMod.val_lt _)
  t1 i k := by
    have hn : (i : ℕ) * 256 + k < 1024 := by omega
    unfold t1At
    rw [RealizedProgram.evalE_leaf]
    unfold stmtOfKey stmtOfKeyWith
    rw [dif_neg (by omega), dif_pos ⟨rfl, hn⟩, castElt_castElt (by decide +kernel)]
    have hi : (⟨((i : ℕ) * 256 + k) / 256, by change _ < 4; omega⟩ :
        Fin _root_.MLDSA.mldsa44.k) = i := Fin.ext (by simp; omega)
    have hk : aIdx ((i : ℕ) * 256 + k) = k := Fin.ext (by simp only [aIdx]; omega)
    rw [hi, hk]
    exact ROMParams.toNat_fq6_natCast (ZMod.val_lt _)
  tr := by
    funext t
    have ht := t.isLt
    unfold trBits Falcon512.HashCircuit.wiresOfByteVec
    rw [RealizedProgram.evalE_leaf]
    unfold stmtOfKey stmtOfKeyWith
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨rfl, by omega⟩,
      castElt_castElt (by decide +kernel)]

/-- **A statement's values hold its decoded key's preprocessing** (`KeyOf`). -/
theorem keyOf_stmtOf (s : KeyStmt) : KeyOf (MLDSA44.pkDecode44 s.1.key) (stmtOf s) := by
  rw [stmtOf_eq]
  exact keyOf_stmtOfKey _

/-! ## The compiled circuits and the multi-circuit IOP -/

/-- **The compiled circuits of `MLDSA44.Native.QROMParams`** (`RealizedProgram.Compiled` at `QROMParams.proofSystem`): the GKR sources of
the program's circuits with the trust bundle `CircuitsEnforce`. -/
abbrev Compiled : Type := RealizedProgram.Compiled proofSystem

variable (C : Compiled)

/-- **The relation of the BCS transformation**: the realized program's relation `rel` at the statement
values of the key, on the witness read from those values. -/
abbrev keyRel : Set (KeyStmt × (program.Valuation interp → VarWitness)) :=
  {p | (stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf rel}

/-! ## The transcript -/

/-- **The bytes of the fields' elements**: `32` bytes for `F_q^11` (field `0`), `32` bytes for
`GF(2^256)` (every other field), the C++ layouts (`Codec.FieldBytes.mldsaNative11`,
`Codec.FieldBytes.gf2_256`). -/
def fieldBytes : RealizedProgram.FieldBytesOf interp where
  fb
    | 0 => 32
    | _ + 1 => 32
  bytes
    | 0 => Codec.FieldBytes.mldsaNative11
    | _ + 1 => Codec.FieldBytes.gf2_256

/-- **The phases' messages fit in `2^20` bytes.** -/
theorem msgB_le : ∀ k, program.msgB fieldBytes k ≤ 2 ^ 20 := by
  decide +kernel

/-- The program has four challenges. -/
theorem challenges_length : program.challenges.length = 4 := by decide

/-- **The C++ samplers of the fields' elements**: `CReader.mldsaNative11` for field `0`, `CReader.gf2_256` for every
other field. -/
def fieldReader : ∀ f, CReader (interp f).K
  | 0 => CReader.mldsaNative11
  | _ + 1 => CReader.gf2_256

/-- **The fields' sizes**: `8380417 ^ 11` for field `0`, `2 ^ 256` for every other field. -/
theorem fieldCard : ∀ f, Fintype.card (interp f).K = if f = 0 then 8380417 ^ 11 else 2 ^ 256
  | 0 => by convert mldsaNativeField11_card <;> rfl
  | _ + 1 => by convert gf2_256_card <;> rfl

/-- **The readers of the challenges' values** (`RealizedProgram.stdReaders`): every challenge's field's
sampler, repeated until its value is outside the table values for LogUp's `α` (decided). -/
def samplerReaders : RealizedProgram.SamplerReaders interp program :=
  RealizedProgram.stdReaders fieldReader fieldCard (by decide +kernel)

/-- The largest load of a challenge: the `13` draws of `RealizedProgram.stdReaders`, the `32` bytes of an element
of `GF(2^256)`. -/
def chalLoadMax : Load := ⟨13, 32⟩

/-- Every challenge's draws are within `chalLoadMax` (`RealizedProgram.chalLoad_stdReaders_le`, decided). -/
theorem chalLoad_le (k : Fin program.phases) (j : program.ChalAt k) :
    program.chalLoad samplerReaders j.1 ≤ chalLoadMax :=
  RealizedProgram.chalLoad_stdReaders_le fieldReader fieldCard _ (by decide +kernel) k j

/-- **The label write of `MLDSA44.Native.QROMParams`**: `gordiehowe:ml-dsa-44-possession` (`system.h`,
`"gordiehowe:" + s.name()`, the C++ system's name). -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:ml-dsa-44-possession")

end GordieHowe.MLDSA44.Native.QROMParams
