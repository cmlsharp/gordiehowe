-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweCerts.Applications.MLDSA44.Emulated.ROMParams.Theorem
public import GordieHoweCerts.Applications.MLDSA44.Native.ROMParams.Setting
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `MLDSA44.Emulated.ROMParams`

The data the series–parallel transcript of the BCS transformation is built from, for the protocol
at the realized program of the emulated ML-DSA-44 proof of possession at the ROM parameters (`GordieHowe.MLDSA44.Emulated.ROMParams.proofSystem`),
with the statement an encoded public key whose `ExpandA` finishes within the byte budget
(`KeyStmt`), read through the statement values it determines (`stmtOf`: `key.a` the key's `A` in coefficient form, `key.t1`
its `t1`, `tr` the bits of `H(pk)`; `iop`: the soundness IOP of the proof system at the frontend's
round-by-round knowledge soundness, `MultiCircuitIOP.comap stmtOf`). The transcript and the statements are in
`GordieHoweCerts/Applications/MLDSA44/Emulated/ROMParams.lean`.

* **The statement** (`KeyStmt`, `keyStmtCodec`, `stmtOf`, `keyOf_stmtOf`, `stmtBounded_stmtOf`):
  as native's; the statement values lie within the declared bounds `key.a < q`, `key.t1 < 2^10`
  (`stmtBounded_stmtOf`).
* **The proof systems** (`ProofSystems`, `ProofSystem.lean`): the definitions below are generic over
  them; the statements are at `proofSystem` (`GordieHoweCerts/Generated/MLDSA44/Emulated/ROMParams/Certified.lean`).
* **The transcript data**: the label `gordiehowe:ml-dsa-44-possession-emulated`, `32`-byte
  digests, the key-and-context writes, the codecs of domain `A`'s circuit proof (Goldilocks², `16`
  bytes) and domain `H`'s (`GF(2^128)`, `16` bytes), the C++ challenge readers and LogUp's `α`
  outside `[0, 645)`.
* **The facts the setting is built from**: the sum over the two domains (`sum_domains`) and the
  circuits' widths and layers.
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open Generated.MLDSA44.Emulated.ROMParams (interp ProofSystems)
open scoped NNReal ENNReal

/-! ## The statement -/

/-- **The statements of the BCS transformation**: those of the native program at the ROM parameters
(`Native.ROMParams.KeyStmt`), encoded ML-DSA-44 public keys whose `ExpandA` finishes within the byte
budget. One type, with its one decidable equality (`Native.ROMParams.instDecidableEqKeyStmt`), serves
every ML-DSA-44 configuration. -/
abbrev KeyStmt : Type := Native.ROMParams.KeyStmt

/-- **The codec of a statement**: the key-and-context codec (`keyContextCodec 0`), parsing only
keys whose `ExpandA` finishes within the byte budget (decided by `MLDSA44.ExpandAWithin`'s
instance); the writes (`Codec.ser`) are the key-and-context codec's. -/
def keyStmtCodec : Codec KeyStmt :=
  (MLDSA44.PoP.StatementWrites.keyContextCodec 0).mapPartial Subtype.val
    (fun s => if h : MLDSA44.ExpandAWithin _root_.MLDSA.mldsa44 (MLDSA44.pkDecode44 s.key).rho then
      some ⟨s, h⟩ else none)
    (fun b => by simp [b.2]) (fun {a b} h => by
      split_ifs at h with ha
      · cases h
        rfl)

/-- The row of a coordinate of `key.a`: `(4 i + j) · 256 + k` with `n < 4096`. -/
def aRow (n : ℕ) (hn : n < 4096) : Fin 4 := ⟨n / 1024, by omega⟩

/-- The column of a coordinate of `key.a`. -/
def aCol (n : ℕ) : Fin 4 := ⟨n / 256 % 4, Nat.mod_lt _ (by decide)⟩

/-- The coefficient index of a coordinate of `key.a`. -/
def aIdx (n : ℕ) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by norm_num)⟩

/-- **The statement values of a key and a matrix**: `key.a` (value `56`) the coefficients of
`A = NTT⁻¹(aHat)` below `q` (`KeyNTT.vals`), `key.t1` (value `57`) the coefficients of `t1`, `tr`
(value `67`) the bits of `H(pk)` (`MLDSA44.PoP.Compose.trOf`), every other statement coordinate
`0`. -/
def stmtOfKeyWith (pk : MLDSA44.PublicKey44)
    (aHat : _root_.MLDSA.TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) :
    program.Valuation interp := fun v i =>
  if h : v = 56 ∧ i < 4096 then
    RealizedProgram.castElt (a := 0) ((KeyNTT.vals (_root_.MLDSA.Concrete.invNTT
      ((aHat.get (aRow i h.2)).get (aCol i))) (aIdx i) : ℕ) : (interp 0).K)
  else if h : v = 57 ∧ i < 1024 then
    RealizedProgram.castElt (a := 0) ((((pk.t1.get (⟨i / 256, by change i / 256 < 4; omega⟩ :
      Fin _root_.MLDSA.mldsa44.k)).get (aIdx i)).val : ℕ) : (interp 0).K)
  else if h : v = 67 ∧ i < 512 then
    RealizedProgram.castElt (a := 1) (Bits.constBit (K := (interp 1).K)
      (MLDSA44.PoP.Compose.trOf pk ⟨i / 8, by omega⟩).toNat (i % 8))
  else 0

/-- **The statement values of a key** (`stmtOfKeyWith` at `Â = ExpandA(ρ)`,
`Native.Rows.aHat`): `key.a` holds `Rows.aKeyOf`. -/
noncomputable def stmtOfKey (pk : MLDSA44.PublicKey44) : program.Valuation interp :=
  stmtOfKeyWith pk (Native.Rows.aHat pk)

/-- **The statement values of a statement**: the values of its decoded key, with
`Â = ExpandA(ρ)` computed within the byte budget by `MLDSA44.expandABounded`.

Running time: `MLDSA44.expandABounded`'s (`16 · 336` SHAKE128 candidates), `16` inverse NTTs,
then a table lookup per coordinate. -/
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
  a i j k := by
    have hn : ((i : ℕ) * 4 + j) * 256 + k < 4096 := by omega
    rw [RealizedProgram.evalE_leaf]
    unfold stmtOfKey stmtOfKeyWith
    rw [dif_pos ⟨rfl, hn⟩, castElt_castElt (by shape_decide)]
    have hr : aRow _ hn = i := Fin.ext (by simp only [aRow]; omega)
    have hc : aCol (((i : ℕ) * 4 + j) * 256 + k) = j := Fin.ext (by simp only [aCol]; omega)
    have hk : aIdx (((i : ℕ) * 4 + j) * 256 + k) = k := Fin.ext (by simp only [aIdx]; omega)
    rw [hr, hc, hk]
    rfl
  t1 i k := by
    have hn : (i : ℕ) * 256 + k < 1024 := by omega
    rw [RealizedProgram.evalE_leaf]
    unfold stmtOfKey stmtOfKeyWith
    rw [dif_neg (by omega), dif_pos ⟨rfl, hn⟩, castElt_castElt (by shape_decide)]
    have hi : (⟨((i : ℕ) * 256 + k) / 256, by change _ < 4; omega⟩ :
        Fin _root_.MLDSA.mldsa44.k) = i := Fin.ext (by simp; omega)
    have hk : aIdx ((i : ℕ) * 256 + k) = k := Fin.ext (by simp only [aIdx]; omega)
    rw [hi, hk]
  tr := by
    funext t
    have ht := t.isLt
    simp only [Emulated.trBits]
    unfold Falcon512.HashCircuit.wiresOfByteVec
    rw [RealizedProgram.evalE_leaf]
    unfold stmtOfKey stmtOfKeyWith
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨rfl, by omega⟩,
      castElt_castElt (by shape_decide)]

/-- **A statement's values hold its decoded key's preprocessing** (`KeyOf`). -/
theorem keyOf_stmtOf (s : KeyStmt) : KeyOf (MLDSA44.pkDecode44 s.1.key) (stmtOf s) := by
  rw [stmtOf_eq]
  exact keyOf_stmtOfKey _

/-- The declared statement bounds: `key.a` (value `56`) below `q` and `key.t1` (value `57`) below
`2^10`, of `4096` and `1024` coordinates in field `0`. -/
theorem rangeValues : program.declaredRanges = [(56, 8380417), (57, 1024)] ∧
    True ∧ (program.value 56).size = 4096 ∧
    (program.value 57).size = 1024 ∧ program.valueField 56 = 0 ∧ program.valueField 57 = 0 := by
  refine ⟨Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.statement_ranges, trivial, ?_⟩
  shape_decide

/-- **A key's statement values lie within the declared bounds** (`RealizedProgram.StmtBounded`): `A`'s
coefficients are below `q`, a decoded key's `t1` coefficients below `2^10`
(`MLDSA44.pkDecode44_t1_lt`); the honest statements pass the verifier's check. -/
theorem stmtBounded_stmtOf (s : KeyStmt) : program.StmtBounded interp (stmtOf s) := by
  intro vN hvN
  simp only [rangeValues.1, List.mem_cons,
    List.not_mem_nil, or_false] at hvN
  rcases hvN with rfl | rfl
  · intro i hi
    rw [rangeValues.2.2.1] at hi
    refine ⟨_, KeyNTT.vals_lt (_root_.MLDSA.Concrete.invNTT
      (((MLDSA44.expandABounded _root_.MLDSA.mldsa44 (MLDSA44.pkDecode44 s.1.key).rho).get
        (aRow i hi)).get (aCol i))) (aIdx i), ?_⟩
    rw [RealizedProgram.stmtRead_of_isStmtLeaf _ (by shape_decide)]
    show stmtOfKeyWith _ (MLDSA44.expandABounded _ _) 56 i = _
    unfold stmtOfKeyWith
    rw [dif_pos ⟨rfl, hi⟩]
    have hf := rangeValues.2.2.2.2.1
    revert hf
    generalize program.valueField 56 = a
    rintro rfl
    rfl
  · intro i hi
    rw [rangeValues.2.2.2.1] at hi
    refine ⟨_, MLDSA44.pkDecode44_t1_lt s.1.key ⟨i / 256, by change i / 256 < 4; omega⟩ (aIdx i),
      ?_⟩
    rw [RealizedProgram.stmtRead_of_isStmtLeaf _ (by shape_decide)]
    show stmtOfKeyWith _ (MLDSA44.expandABounded _ _) 57 i = _
    unfold stmtOfKeyWith
    rw [dif_neg (show ¬ ((57 : ℕ) = 56 ∧ i < 4096) by omega), dif_pos ⟨rfl, hi⟩]
    have hf := rangeValues.2.2.2.2.2
    revert hf
    generalize program.valueField 57 = a
    rintro rfl
    rfl

/-! ## The compiled circuits and the multi-circuit IOP -/

variable (C : ProofSystems)

/-- **The relation of the BCS transformation**: the relation `rel` at the realized program, at the statement
values of the key, on the witness read from those values. -/
abbrev keyRel : Set (KeyStmt × (program.Valuation interp → MLDSA44.VarWitness)) :=
  {p | (stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf rel}

/-- **The label write of `MLDSA44.Emulated.ROMParams`**: `gordiehowe:ml-dsa-44-possession-emulated`
(`system.h`, `"gordiehowe:" + s.name()`, the plan's system name). -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:ml-dsa-44-possession-emulated")

end GordieHowe.MLDSA44.Emulated.ROMParams
