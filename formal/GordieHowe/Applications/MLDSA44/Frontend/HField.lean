-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Frontend.Shared
public import GordieHowe.Applications.FieldInterps.GF256
public import GordieHowe.Applications.MLDSA44.System.Fields

@[expose] public section

/-!
# GordieHowe frontend: the field facts of an ML-DSA program's domain `H`

The ML-DSA frontend's facts about domain `H` hold for any program with domain `H`'s shape
(`MldsaHBase` and its extensions, instantiated per program by `decide`) over any binary field
interpretation `FH` with the data and facts below (`GordieHowe.MLDSA44.HField`), discharged once per field: `GF(2^128)`
(`gf128`, the programs at the ROM parameters) and `GF(2^256)` (`gf256`, the programs at the QROM
parameters).
-/

namespace GordieHowe.RealizedProgram

/-- **The field data and facts of domain `H`'s field interpretation**: the selection field at
degree `264` (`sel`, its packing constant `X`), the memory check's `θ` in the selection subfield and
the record packing's injectivity, characteristic two, `|K| = 2^bits`, and the decodings the
programs' constants use: `0`, `1`, `2 = X`, `4 = X²`, and additivity on xors. -/
class _root_.GordieHowe.MLDSA44.HField (FH : FieldInterp) where
  /-- The selection field. -/
  sel : SelectionField FH.K 264
  /-- The memory check's `θ`. -/
  Θ : MemoryShuffle.Theta FH.K
  /-- `θ` lies in the selection subfield. -/
  θ_mem : Θ.θ ∈ sel.E
  /-- The record packing at `X` is injective on the subfield's triples. -/
  packing3 : ∀ a b : Fin 3 → FH.K, (∀ i, a i ∈ sel.E) → (∀ i, b i ∈ sel.E) →
    RecordPacking.pack sel.X a = RecordPacking.pack sel.X b → a = b
  /-- The field's bit length. -/
  bits : ℕ
  /-- The field has `2^bits` elements. -/
  card : Fintype.card FH.K = 2 ^ bits
  /-- The field has characteristic two. -/
  charTwo : CharP FH.K 2
  /-- The constant `0` decodes to `0`. -/
  decode_zero : FH.decode 0 = 0
  /-- The constant `1` decodes to `1`. -/
  decode_one : FH.decode 1 = 1
  /-- The constant `2` decodes to the packing constant `X`. -/
  decode_two : FH.decode 2 = sel.X
  /-- The constant `4` decodes to `X²`. -/
  decode_four : FH.decode 4 = sel.X ^ 2
  /-- Decoding is additive on xors. -/
  decode_xor : ∀ a b, FH.decode (a ^^^ b) = FH.decode a + FH.decode b
  /-- The packing basis of the trace words (`GF(2^16)` over `GF(2)`). -/
  packing : PackedClaim.PackedBasis FH.K 4
  /-- Bit `j` of a packed word at the node `GF(2^16)` is its bit `j mod 16`. -/
  coord_pack : ∀ (b : Fin (2 ^ 4) → Bool) (j : ℕ),
    FH.coord "GF(2^16)" (PackedClaim.pack packing b) j = b ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩
  /-- An element of the node `GF(2^16)` lies in the selection subfield. -/
  mem_sel_of_node : ∀ x : FH.K, x ∈ FH.node "GF(2^16)" → x ∈ sel.E
  /-- The integer reading is injective. -/
  toNat_injective : Function.Injective FH.toNat
  /-- `0` is read as `0`. -/
  toNat_zero : FH.toNat 0 = 0
  /-- `1` is read as `1`. -/
  toNat_one : FH.toNat 1 = 1

instance _root_.GordieHowe.MLDSA44.HField.instCharP (FH : FieldInterp) [h : MLDSA44.HField FH] : CharP FH.K 2 := h.charTwo

/-- `GF(2^128)` has domain `H`'s field data (`MLDSA44.Native.ROMParams.fieldData`). -/
instance : MLDSA44.HField gf128 where
  sel := MLDSA44.Native.ROMParams.fieldData.sel
  Θ := MLDSA44.Native.ROMParams.fieldData.Θ
  θ_mem := MLDSA44.Native.ROMParams.fieldData.θ_mem
  packing3 := MLDSA44.Native.ROMParams.fieldData.packing3
  bits := 128
  card := gf2_128_card
  charTwo := inferInstanceAs (CharP GF2_128 2)
  decode_zero := gf2_128OfNat_zero
  decode_one := gf2_128OfNat_one
  decode_two := rfl
  decode_four := gf2_128OfNat_two_pow (j := 2) (by norm_num)
  decode_xor := gf2_128OfNat_xor
  packing := gf2_128PackedBasis
  coord_pack := gf2Coord_pack
  mem_sel_of_node x h := mem_gf2_128Subfield.2 (RelativePacking.mem_fixedField_iff_pow.1
    (show x ∈ RelativePacking.fixedField GF2_128 2 16 from h))
  toNat_injective := gf128_toNat_injective
  toNat_zero := gf128_toNat_zero
  toNat_one := gf128_toNat_one

/-- `GF(2^256)` has domain `H`'s field data (`MLDSA44.Native.QROMParams.fieldData`). -/
instance : MLDSA44.HField gf256 where
  sel := MLDSA44.Native.QROMParams.fieldData.sel
  Θ := MLDSA44.Native.QROMParams.fieldData.Θ
  θ_mem := MLDSA44.Native.QROMParams.fieldData.θ_mem
  packing3 := MLDSA44.Native.QROMParams.fieldData.packing3
  bits := 256
  card := gf2_256_card
  charTwo := inferInstanceAs (CharP GF2_256 2)
  decode_zero := gf2_256OfNat_zero
  decode_one := gf2_256OfNat_one
  decode_two := rfl
  decode_four := gf2_256OfNat_four
  decode_xor := gf2_256OfNat_xor
  packing := gf2_256PackedBasis
  coord_pack := gf256Coord_pack
  mem_sel_of_node x h := mem_gf2_256Subfield.2 (RelativePacking.mem_fixedField_iff_pow.1
    (show x ∈ RelativePacking.fixedField GF2_256 2 16 from h))
  toNat_injective _ _ h := BitVec.eq_of_toNat_eq h
  toNat_zero := gf256_toNat_zero
  toNat_one := gf256_toNat_one

/-- **A natural below `2` decodes to its bit.** -/
theorem _root_.GordieHowe.MLDSA44.HField.decode_lt_two {FH : FieldInterp} [MLDSA44.HField FH] {b : ℕ} (hb : b < 2) :
    FH.decode b = if b = 1 then 1 else 0 := by
  interval_cases b
  · exact MLDSA44.HField.decode_zero
  · exact MLDSA44.HField.decode_one

/-- **An element read below `2` is that bit** (the integer reading is injective). -/
theorem _root_.GordieHowe.MLDSA44.HField.eq_of_toNat_lt_two {FH : FieldInterp} [MLDSA44.HField FH] {x : FH.K} {n : ℕ}
    (h : FH.toNat x = n) (hn : n < 2) : x = if n = 1 then 1 else 0 := by
  apply MLDSA44.HField.toNat_injective (FH := FH)
  rw [h]
  interval_cases n
  · rw [if_neg (by decide), MLDSA44.HField.toNat_zero]
  · rw [if_pos rfl, MLDSA44.HField.toNat_one]

/-- **The embedding of a byte value** `v < 256` in a selection field: the sum of the embedding basis
over its set bits `u < 8`. -/
theorem _root_.GordieHowe.SelectionField.embed_of_lt_256 {K : Type*} [Field K] {S : ℕ} (F : SelectionField K S)
    {v : ℕ} (hv : v < 256) :
    F.embed v = ∑ u : Fin 8, if v.testBit u then F.e ⟨u, by change (u : ℕ) < 16; omega⟩ else 0 := by
  unfold SelectionField.embed selectionEmbed
  change (∑ i : Fin (8 + 8), _) = _
  rw [Fin.sum_univ_add]
  have hz : ∀ k : Fin 8, v / 2 ^ ((Fin.natAdd 8 k : Fin (8 + 8)) : ℕ) % 2 = 0 := fun k => by
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hv (by
      simp only [Fin.natAdd, Fin.val_mk]
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ (8 + (k : ℕ)) := Nat.pow_le_pow_right (by norm_num) (by omega)))]
  simp only [hz, zero_ne_one, if_false, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [Fin.castAdd, Fin.castLE, decide_eq_true_eq]

/-- **The decoding of an `XOR` selection** is the sum of the selected decodings
(`MLDSA44.HField.decode_xor`). -/
theorem decode_xorSel (FH : FieldInterp) [MLDSA44.HField FH] (v : ℕ) (c : ℕ → ℕ) :
    FH.decode (xorSel v c) = ∑ u : Fin 8, if v.testBit u then FH.decode (c u) else 0 := by
  have hstep : ∀ (acc : ℕ) (u : ℕ), FH.decode (acc ^^^ (if v.testBit u then c u else 0)) =
      FH.decode acc + if v.testBit u then FH.decode (c u) else 0 := fun acc u => by
    rw [MLDSA44.HField.decode_xor]
    split_ifs
    · rfl
    · rw [MLDSA44.HField.decode_zero]
  simp only [xorSel, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, hstep, MLDSA44.HField.decode_zero, Fin.sum_univ_eight]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add]
  rfl

/-- **An equation evaluated in domain `d`** is the equation evaluated in field `f` when domain `d`'s
field is `f`. -/
theorem evalWith_eq_iff {ir : RealizedProgram} {I : Interp} {rd : ir.Valuation I} {d f : ℕ}
    (h : ir.domainField d = f) {a b : Expr} {i j : ℕ} :
    ir.evalWith rd d a i = ir.evalWith rd d b j ↔ ir.evalE rd f a i = ir.evalE rd f b j := by
  subst h
  rfl

end GordieHowe.RealizedProgram
