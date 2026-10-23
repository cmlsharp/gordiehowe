-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Transcript.FieldReaders
public import GordieHowe.SPBCS.Format.FieldCodecs
public import GordieHowe.Applications.Falcon512.PoP.Configuration
public import GordieHowe.ProofSystem.Ligero.AgreementThreshold
public import GordieHowe.Model.IOP.AppendView
public import GordieHowe.Foundations.Algebra.RelativePackingBijective
public import GordieHowe.ProofSystem.Ligero.MaskTest.PiecesHonest
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.GKR.SourceInput
public import GordieHowe.ProofSystem.Zerocheck.Round
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic
public import GordieHowe.ProofSystem.GKR.TranscriptRouting
public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.ProofSystem.GKR.CircuitBudget
public import GordieHowe.ProofSystem.GKR.OrdinaryCompleteness
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.ProofSystem.GKR.HonestTranscript
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.ProofSystem.Ligero.Routing
public import GordieHowe.Foundations.Algebra.AffineForm
public import GordieHowe.ProofSystem.Ligero.Preparation
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.Foundations.ReedSolomon.AffineProximity
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.Applications.Falcon512.Circuits.HashStep
public import GordieHowe.Applications.Keccak.HashCircuit.SkipCompleteness
public import GordieHowe.ProofSystem.Ligero.ShapeEncoding
public import GordieHowe.Foundations.ReedSolomon.SubfieldInterpolation
public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.ProofSystem.Ligero.HVZK
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import GordieHowe.ProofSystem.FieldProof.MaskedRowReduction
public import GordieHowe.Applications.Keccak.HashCircuit.SkipHVZK
public import GordieHowe.ProofSystem.Program.Basic
public import GordieHowe.Applications.MLDSA44.PoP.Configuration
public import GordieHowe.Foundations.ToMathlib.FintypeBytes
public import GordieHowe.SPBCS.Sampler.Avoid

@[expose] public section

/-!
# The transcript pieces of the proofs of possession

The data the configurations' settings share (for example
`GordieHowe/Applications/Falcon512/Native/ROMParams/Setting.lean`):

- the Falcon statement `FalconPublicKey` and the statement writes: Falcon writes the public key's
  `512` coefficients as one array of elements of `ℤ_q`, two little-endian bytes each
  (`falconKeyWrites`, `falconKeyCodec`); ML-DSA writes the encoded key as one byte string and the
  context as another (`GordieHowe.MLDSA44.PoP.StatementWrites.keyContext`, an instance of the C++ shape
  `StatementWrites`);
- the ASCII bytes of the C++ transcript labels (`GordieHowe.SPBCS.Configurations.asciiBytes`);
- the column codecs of a tableau (`colCodec`: the column's `nrep + R` entries as one array of
  field elements, then the two mask entries; `rowsColCodec`: the entries alone;
  `GordieHowe.Ligero.MaskRow.Setup.leafCodec` picks one by the masking) and their lengths
  (`length_ser_colCodec`, `length_ser_rowsColCodec`);
- the C++ challenge samplers' data (the stream budget `fsExtraBytes`, the values a lookup
  challenge avoids, `excludedListing`) and the Chernoff certificates of their overrun
  (`PassesChernoff`, `passesChernoff_of_nat_at`, `nat_mul_ofReal_pow`).

The field element bytes are the C++ layout (`GordieHowe/SPBCS/Format/FieldCodecs.lean`).
-/

namespace GordieHowe

open IOP SPBCS SPBCS.Configurations QROM RelativePacking
open scoped ENNReal

/-- A Falcon-512 public key: the statement of the Falcon proof of possession. -/
abbrev FalconPublicKey := _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512

/-- **The C++ statement writes of the ML-DSA-44 proof of possession**, the shape of the statement
writes `BCS.Format.stmt` at an ML-DSA setting (`absorb_statement`, `lib/zk/zk_common.h`, as the
ML-DSA-44 proofs of possession called it at `938eb888`): the two circuit-id writes `ids`, fixed by
the compiled circuits; the encoded key as one byte string (`Codec.bstr 1312`: tag `0x00`,
`u64le(1312)`, the bytes of `pkEncode(ρ, t₁)`); then the remaining writes `rest`, the H and A
public-input slots and the two constraint digests. `rest_length`: the remaining writes have one
length, since they are fixed-width field elements and digests (a property of the C++ writes).
`rest_ctx`: at a fixed key they determine the context, since the H slots carry the context bits as
the field elements `0` and `1`, whose byte encodings differ; at `ctxLen = 0`, the headlines'
fixture, it holds trivially. -/
structure MLDSA44.PoP.StatementWrites (ctxLen : ℕ) where
  /-- The two circuit-id writes. -/
  ids : List QROM.Byte
  /-- The writes after the key: the public-input slots and the constraint digests. -/
  rest : MLDSA44.PoP.Statement ctxLen → List QROM.Byte
  rest_length : ∀ x x', (rest x).length = (rest x').length
  rest_ctx : ∀ pk c c', rest ⟨pk, c⟩ = rest ⟨pk, c'⟩ → c = c'

namespace MLDSA44.PoP.StatementWrites

open SPBCS QROM

variable {ctxLen : ℕ} (W : StatementWrites ctxLen)

/-- The bytes of an encoded key as transcript bytes. -/
def keyBytes (pk : MLDSA44.EncodedKey44) : Fin 1312 → Byte := fun i => (pk i).toFin

/-- The statement writes at the statement `x`: the circuit ids, the encoded key, the rest. -/
def pre (x : MLDSA44.PoP.Statement ctxLen) : List Byte :=
  W.ids ++ (Codec.bstr 1312).ser (keyBytes x.key) ++ W.rest x

end MLDSA44.PoP.StatementWrites

namespace SPBCS.Configurations

/-- **The ASCII bytes of a string** (the C++ labels are ASCII). -/
def asciiBytes (s : String) : List Byte :=
  s.toList.map fun c => ⟨c.toNat % 256, Nat.mod_lt _ (by norm_num)⟩

end SPBCS.Configurations

/-! ### Statement writes -/

/-- The bytes of a coefficient of `ℤ_q`, `q = 12289`: two little-endian bytes of its
representative in `[0, q)`. -/
def falconCoeffBytes : Codec.FieldBytes (ZMod 12289) 2 :=
  Codec.FieldBytes.ofEquiv (ZMod.finEquiv 12289).symm.toEquiv (by norm_num)

/-- **The Falcon statement writes**: the public key's `512` coefficients `h`, one array of field
elements of `ℤ_q` (`TAG_ARRAY ‖ u64le(512) ‖ …`). -/
def falconKeyWrites (pk : FalconPublicKey) : List Byte :=
  (Codec.fieldArray falconCoeffBytes 512).ser fun i => (pk.h : Vector (ZMod 12289) 512).get i

theorem falconKeyWrites_length (pk : FalconPublicKey) : (falconKeyWrites pk).length = 1033 :=
  Codec.length_ser_fieldArray falconCoeffBytes 512 _

/-- A Falcon public key is its `512` coefficients. -/
def falconKeyEquiv : FalconPublicKey ≃ (Fin 512 → ZMod 12289) :=
  ({ toFun pk := pk.h
     invFun h := ⟨h⟩
     left_inv _ := rfl
     right_inv _ := rfl } : FalconPublicKey ≃ Vector (ZMod 12289) 512).trans (Vector.equivFun _ _)

/-- **The codec of the Falcon statement writes** (`falconKeyWrites`): its decoder reads the
array of `512` two-byte coefficients back.

Running time: `9 + 1024` byte comparisons and reads and `512` coefficient decodings (each a
comparison of a 16-bit value with `q`). This running time is argued here, not proved in Lean. -/
def falconKeyCodec : Codec FalconPublicKey :=
  (Codec.fieldArray falconCoeffBytes 512).mapEquiv falconKeyEquiv

namespace MLDSA44.PoP.StatementWrites

/-- **The ML-DSA statement writes of the format settings**: no circuit-id writes, the encoded key
as one byte string, then the context as one byte string. -/
def keyContext (ctxLen : ℕ) : StatementWrites ctxLen where
  ids := []
  rest x := (Codec.bstr ctxLen).ser fun i => (x.ctx i).toFin
  rest_length x x' := by simp [Codec.bstr, Codec.length_ser_framed]
  rest_ctx pk c c' h :=
    funext fun i => UInt8.toFin_inj.mp (congrFun ((Codec.bstr ctxLen).ser_injective h) i)

theorem keyContext_pre_length {ctxLen : ℕ} (x : MLDSA44.PoP.Statement ctxLen) :
    ((keyContext ctxLen).pre x).length = 9 + 1312 + (9 + ctxLen) := by
  simp [pre, keyContext, Codec.bstr, Codec.length_ser_framed]

/-- An ML-DSA statement is the bytes of its encoded key and of its context. -/
def keyContextEquiv (ctxLen : ℕ) :
    MLDSA44.PoP.Statement ctxLen ≃ (Fin 1312 → Byte) × (Fin ctxLen → Byte) where
  toFun x := (keyBytes x.key, fun i => (x.ctx i).toFin)
  invFun p := ⟨fun i => UInt8.ofFin (p.1 i), fun i => UInt8.ofFin (p.2 i)⟩
  left_inv x := by
    obtain ⟨key, ctx⟩ := x
    simp [keyBytes]
  right_inv _ := Prod.ext (funext fun _ => rfl) (funext fun _ => rfl)

/-- **The codec of the ML-DSA statement writes `keyContext`**: the encoded key and the context,
one byte string each; its decoder reads both back.

Running time: `9 + 1312 + 9 + ctxLen` byte comparisons and reads.
This running time is argued here, not proved in Lean. -/
def keyContextCodec (ctxLen : ℕ) : Codec (MLDSA44.PoP.Statement ctxLen) :=
  ((Codec.bstr 1312).prod (Codec.bstr ctxLen)).mapEquiv (keyContextEquiv ctxLen)

end MLDSA44.PoP.StatementWrites

/-! ### Column codecs -/

/-- **The leaf codec of a column of the encoded rows**: the column's `nrep + R` entries (the
`nrep` ILDT entries, then the data entries, `Ligero.Tableau.Column.equivFin`) as one array of field
elements, then the two mask entries. -/
def colCodec {K : Type} {fb : ℕ} (FB : Codec.FieldBytes K fb) (R nrep : ℕ) :
    Codec (Ligero.Tableau.Leaf K R nrep) :=
  ((Codec.fieldArray FB (nrep + R)).prod ((Codec.fieldElem FB).prod (Codec.fieldElem FB))).mapEquiv
    Ligero.Tableau.Leaf.equivProd

theorem length_ser_colCodec {K : Type} {fb : ℕ} (FB : Codec.FieldBytes K fb) (R nrep : ℕ)
    (c : Ligero.Tableau.Leaf K R nrep) :
    ((colCodec FB R nrep).ser c).length = (9 + (nrep + R) * fb) + ((1 + fb) + (1 + fb)) := by
  simp only [colCodec, Codec.mapEquiv, Codec.mapPartial, Codec.prod, List.length_append,
    Codec.length_ser_fieldArray, Codec.length_ser_fieldElem]

/-- **The leaf codec of a column of the encoded rows without masks**: the column's `nrep + R`
entries as one array of field elements (`Ligero.Tableau.Column.equivFin`). -/
def rowsColCodec {K : Type} {fb : ℕ} (FB : Codec.FieldBytes K fb) (R nrep : ℕ) :
    Codec (Ligero.Tableau.Column K R nrep) :=
  (Codec.fieldArray FB (nrep + R)).mapEquiv Ligero.Tableau.Column.equivFin

theorem length_ser_rowsColCodec {K : Type} {fb : ℕ} (FB : Codec.FieldBytes K fb) (R nrep : ℕ)
    (c : Ligero.Tableau.Column K R nrep) :
    ((rowsColCodec FB R nrep).ser c).length = 9 + (nrep + R) * fb := by
  simp only [rowsColCodec, Codec.mapEquiv, Codec.mapPartial, Codec.length_ser_fieldArray]

/-! ### The bounds -/

namespace SPBCS.Configurations

/-- **A computable listing of the values a lookup challenge avoids** (`Range.excluded`): the
casts of `0, …, T - 1` without repetitions, or nothing when `T` itself is one of them. -/
def excludedListing (F : Type) [Field F] [Fintype F] [DecidableEq F] (T : ℕ) :
    (Range.excluded F T).Listing where
  list := if (T : F) ∈ Range.tableValues T then [] else ((List.range T).map (Nat.cast : ℕ → F)).dedup
  nodup := by
    split_ifs
    · exact List.nodup_nil
    · exact List.nodup_dedup _
  mem_iff x := by
    unfold Range.excluded
    split_ifs with h
    · simp
    · simp only [List.mem_dedup, List.mem_map, List.mem_range, Range.mem_tableValues]
      exact ⟨fun ⟨j, hj, hx⟩ => ⟨⟨j, hj⟩, hx⟩, fun ⟨j, hx⟩ => ⟨j, j.2, hx⟩⟩

/-- **The C++ stream budget beyond the digest**: `kFSStreamExtraBytes = 206848`
(`lib/random/transcript.h` line 60). -/
def fsExtraBytes : ℕ := 206848

/-- **A load passes the Chernoff test** `ε` at `z` on streams of `N` bytes: the attempt
generating function is finite at `z` (`pow_lt`), and the per-round Chernoff bound on `N`-byte
streams with attempt bound `N` is at most `ε` (`bound_le`). -/
structure PassesChernoff (z ε : ℝ) (N : ℕ) (L : Load) : Prop where
  /-- `z ^ bytes < 2`, so the attempt generating function is finite at `z`. -/
  pow_lt : z ^ L.bytes < 2
  /-- The Chernoff bound is at most `ε`. -/
  bound_le : L.bound z N N ≤ ε

theorem PassesChernoff.of_le {z ε : ℝ} (hz : 1 ≤ z) {N : ℕ} {L L' : Load}
    (h : PassesChernoff z ε N L') (hL : L ≤ L') : PassesChernoff z ε N L :=
  ⟨(pow_le_pow_right₀ hz hL.bytes).trans_lt h.pow_lt, (Load.bound_mono hz hL h.pow_lt).trans h.bound_le⟩

theorem PassesChernoff.anti {z ε : ℝ} (hz : 1 ≤ z) {N N' : ℕ} {L : Load}
    (h : PassesChernoff z ε N L) (hN : N ≤ N') : PassesChernoff z ε N' L :=
  ⟨h.pow_lt, (Load.bound_anti hz h.pow_lt hN hN).trans h.bound_le⟩

theorem geomPgf_65_64 (b : ℕ) (hb : 65 ^ b < 2 * 64 ^ b) :
    geomPgf (65 / 64) b = (65 : ℝ) ^ b / ((2 * 64 ^ b - 65 ^ b : ℕ) : ℝ) := by
  have h64 : (0 : ℝ) < 64 ^ b := by positivity
  rw [geomPgf, Nat.cast_sub hb.le]
  push_cast
  rw [div_pow]
  field_simp

/-- **A numeric Chernoff certificate at `ε = 2^-E`**: `D` draws of at most `b` bytes pass the test
at `z = 65/64` on streams of `N` bytes when both terms are at most `2^-(E+1)`. -/
theorem passesChernoff_of_nat_at (E : ℕ) {b D N : ℕ} (hb : 65 ^ b < 2 * 64 ^ b)
    (h1 : 65 ^ (b * D) * 64 ^ (N + 1) * 2 ^ (E + 1) ≤ (2 * 64 ^ b - 65 ^ b) ^ D * 65 ^ (N + 1))
    (h2 : D * 2 ^ (E + 1) ≤ 2 ^ N) :
    PassesChernoff (65 / 64) ((1 / 2) ^ E) N ⟨D, b⟩ := by
  have hpos : (0 : ℝ) < ((2 * 64 ^ b - 65 ^ b : ℕ) : ℝ) := by
    have : 0 < 2 * 64 ^ b - 65 ^ b := by omega
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · show (65 / 64 : ℝ) ^ b < 2
    rw [div_pow, div_lt_iff₀ (by positivity)]
    exact_mod_cast hb
  · show geomPgf (65 / 64) b ^ D / (65 / 64) ^ (N + 1) + D * (1 / 2) ^ N ≤ (1 / 2) ^ E
    rw [geomPgf_65_64 b hb]
    have e1 : ((65 : ℝ) ^ b / ((2 * 64 ^ b - 65 ^ b : ℕ) : ℝ)) ^ D / (65 / 64) ^ (N + 1) ≤
        (1 / 2) ^ (E + 1) := by
      have hc : ((65 : ℝ) ^ (b * D) * 64 ^ (N + 1)) * 2 ^ (E + 1) ≤
          ((2 * 64 ^ b - 65 ^ b : ℕ) : ℝ) ^ D * 65 ^ (N + 1) := by exact_mod_cast h1
      have heq : ((65 : ℝ) ^ b / ((2 * 64 ^ b - 65 ^ b : ℕ) : ℝ)) ^ D / (65 / 64) ^ (N + 1) =
          ((65 : ℝ) ^ (b * D) * 64 ^ (N + 1)) /
            (((2 * 64 ^ b - 65 ^ b : ℕ) : ℝ) ^ D * 65 ^ (N + 1)) := by
        rw [div_pow, div_pow, pow_mul]
        field_simp
      rw [heq, div_le_iff₀ (by positivity), one_div_pow, div_mul_eq_mul_div, one_mul,
        le_div_iff₀ (by positivity)]
      exact hc
    have e2 : (D : ℝ) * (1 / 2) ^ N ≤ (1 / 2) ^ (E + 1) := by
      rw [one_div_pow, one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity),
        one_mul]
      exact_mod_cast h2
    calc _ ≤ (1 / 2 : ℝ) ^ (E + 1) + (1 / 2) ^ (E + 1) := add_le_add e1 e2
      _ = (1 / 2) ^ E := by rw [pow_succ]; ring

/-- `n` rounds of at most `2^-E` each: at most `n / 2^E`. -/
theorem nat_mul_ofReal_pow (n E : ℕ) :
    (n : ℝ≥0∞) * ENNReal.ofReal ((1 / 2) ^ E) = n / 2 ^ E := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat, one_div, ← ENNReal.inv_pow, div_eq_mul_inv]

end SPBCS.Configurations

end GordieHowe
