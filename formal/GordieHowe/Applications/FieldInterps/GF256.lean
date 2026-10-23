-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Interp
public import GordieHowe.Foundations.Fields.GF2_256Relative
public import GordieHowe.Foundations.Fields.GF2_256Dual
public import GordieHowe.Foundations.Fields.GF2_256Conv

@[expose] public section

/-!
# GordieHowe: `GF(2^256)` read in Lean, and the ML-DSA interpretation at the QROM parameters

* **`GF(2^256)`** (`gf256`): the registry entry `gf2_256Entry`, `GF2_256`; constants are the
  polynomial-basis bits (`gf2_256OfNat`), and so is the integer reading; the nodes `GF(2^16)` and
  `bit` are the fixed fields of `x ↦ x^(2^16)` and `x ↦ x^2` (`gf256Node`); bit `j` of a `GF(2^16)`
  value is its decoded bit in the packing basis `gf2_256PackedBasis`, read through the first
  coordinate of the relative basis `gf2_256RelativeBasis` (`gf256Coord`), additive on the field
  (`gf256_bitsAdditive`). This mirrors `gf128` (`GordieHowe/Applications/FieldInterps/Basic.lean`). Its model
  at the node `bit` (`gf256_model`); a binary MAC field of width `256` with the taps `{0, 2, 5, 10}`
  (`gf256_macFieldOk`).
* **The ML-DSA interpretation at the QROM parameters** (`GordieHowe.RealizedProgram.mldsaQROMInterp`): field `0` domain `A`'s, field `1`
  `GF(2^256)`.
-/

namespace GordieHowe.RealizedProgram

open Export RelativePacking

/-- **The bits' node is `{0, 1}`** in any field: the fixed field of `x ↦ x^2`. -/
theorem mem_fixedField_two_one_iff {K : Type} [Field K] [Fintype K] [CharP K 2] {x : K} :
    x ∈ fixedField K 2 1 ↔ x = 0 ∨ x = 1 := by
  rw [mem_fixedField_iff_pow, pow_one]
  constructor
  · intro h
    exact eq_zero_or_one_of_sq_eq_self h
  · rintro (rfl | rfl) <;> simp

/-- The relative basis of `GF(2^256)` over `GF(2^16)` starts at `1`. -/
theorem gf2_256RelativeBasis_zero : gf2_256RelativeBasis.β 0 = 1 := pow_zero _

/-- **The nodes of `GF(2^256)`**: `GF(2^16)` the fixed field of `x ↦ x^(2^16)`, `bit` the fixed
field of `x ↦ x^2` (`{0, 1}`), any other name the field. -/
def gf256Node (s : String) : AddSubgroup GF2_256 :=
  if s = "GF(2^16)" then (fixedField GF2_256 2 16).toSubring.toAddSubgroup
  else if s = "bit" then (fixedField GF2_256 2 1).toSubring.toAddSubgroup else ⊤

/-- Membership in a node of `GF(2^256)` is decidable (one exponentiation). -/
instance gf256NodeDec (s : String) : DecidablePred (· ∈ gf256Node s) := fun x => by
  unfold gf256Node
  split
  · exact decidableMemFixedField (p := 2) (m := 16) x
  · split
    · exact decidableMemFixedField (p := 2) (m := 1) x
    · exact isTrue (AddSubgroup.mem_top x)

/-- **Bit `j` of a `GF(2^256)` element at a node**: at `GF(2^16)`, decoded bit `j mod 16` in the
packing basis of the first relative coordinate; no bits at other nodes. -/
def gf256Coord (s : String) (x : GF2_256) (j : ℕ) : Bool :=
  if s = "GF(2^16)" then
    decide (PackedClaim.decode gf2_256PackedBasis (coord gf2_256RelativeBasis x 0)
      ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩ = 1)
  else false

/-- **`GF(2^256)` as a field of the program**: the registry entry, `GF2_256`, constants as
polynomial-basis bits (`gf2_256OfNat`), the integer reading the polynomial-basis bits, the nodes
`gf256Node`, the bit coordinates `gf256Coord`. -/
def gf256 : FieldInterp where
  spec := gf2_256Entry.spec
  K := GF2_256
  decode := gf2_256OfNat
  toNat x := BitVec.toNat (show BitVec 256 from x)
  node := gf256Node
  memDec := gf256NodeDec
  coord := gf256Coord

/-- The integer reading of `GF(2^256)` reads `0` as `0`. -/
theorem gf256_toNat_zero : gf256.toNat 0 = 0 := by decide

/-- The integer reading of `GF(2^256)` reads `1` as `1`. -/
theorem gf256_toNat_one : gf256.toNat 1 = 1 := by decide

/-- `0` decodes to `0`. -/
theorem gf2_256OfNat_zero : gf2_256OfNat 0 = 0 := rfl

/-- **`gf2_256OfNat` is additive on xors**: xoring the polynomial-basis bits adds the elements. -/
theorem gf2_256OfNat_xor (a b : ℕ) : gf2_256OfNat (a ^^^ b) = gf2_256OfNat a + gf2_256OfNat b := by
  unfold gf2_256OfNat
  rw [BitVec.ofNat_xor]
  rfl

open BinarySpread in
/-- **The constants `2^j`, `j < 256`, of `GF(2^256)` are the powers of `x`** (the polynomial-basis
map takes `2^j` to `root^j`, `bitsVal_two_pow`). -/
theorem _root_.GordieHowe.gf2_256OfNat_two_pow {j : ℕ} (hj : j < 256) :
    gf2_256OfNat (2 ^ j) = gf2_256OfNat 2 ^ j := by
  apply gf2_256ToSpec.injective
  have hs : ∀ v, gf2_256ToSpec (gf2_256OfNat v) = bitsVal gf2_256Poly 256 v := fun v =>
    toSpec_ofNat 256 v
  have h2 : bitsVal gf2_256Poly 256 2 = AdjoinRoot.root gf2_256Poly := by
    simpa using bitsVal_two_pow (f := gf2_256Poly) (n := 256) (j := 1) (by norm_num)
  rw [map_pow, hs, hs, bitsVal_two_pow hj, h2]

/-- `4` decodes to `x²`. -/
theorem gf2_256OfNat_four : gf2_256OfNat 4 = gf2_256OfNat 2 ^ 2 := by
  rw [sq]
  decide +kernel

/-- The reading of a bit in `GF(2^256)`: `1` or `0`. -/
def gf256BitVal (b : Bool) : GF2_256 := if b then 1 else 0

/-- An element of `{0, 1}` is the reading of its being `1`. -/
theorem gf256BitVal_decide_eq_one {x : GF2_256} (h : x = 0 ∨ x = 1) :
    gf256BitVal (decide (x = 1)) = x := by
  rcases h with rfl | rfl
  · simp [gf256BitVal]
  · simp [gf256BitVal]

/-- **The bit coordinates of `GF(2^256)` are additive** (`PackedClaim.decode_add`, `coord_add`,
`PackedClaim.decode_bool`). -/
theorem gf256Coord_add (E : String) (j : ℕ) (x y : GF2_256) :
    gf256BitVal (gf256Coord E (x + y) j) =
      gf256BitVal (gf256Coord E x j) + gf256BitVal (gf256Coord E y j) := by
  unfold gf256Coord
  split_ifs
  · have hb : ∀ z : GF2_256, PackedClaim.decode gf2_256PackedBasis (coord gf2_256RelativeBasis z 0)
        ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩ = 0 ∨
        PackedClaim.decode gf2_256PackedBasis (coord gf2_256RelativeBasis z 0)
          ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩ = 1 := fun z =>
      PackedClaim.decode_bool _ (coord_mem _ _ _) _
    rw [coord_add, PackedClaim.decode_add, gf256BitVal_decide_eq_one ((hb x).elim
      (fun h0 => (hb y).elim (fun h1 => .inl (by rw [h0, h1, add_zero]))
        fun h1 => .inr (by rw [h0, h1, zero_add]))
      fun h0 => (hb y).elim (fun h1 => .inr (by rw [h0, h1, add_zero]))
        fun h1 => .inl (by rw [h0, h1]; exact CharTwo.add_self_eq_zero 1)),
      gf256BitVal_decide_eq_one (hb x), gf256BitVal_decide_eq_one (hb y)]
  · simp [gf256BitVal]

/-- **The bit coordinates of `GF(2^256)` as a field of the program are additive**. -/
theorem gf256_bitsAdditive : gf256.BitsAdditive := fun E j x y => gf256Coord_add E j x y

/-- **The node `bit` of `GF(2^256)` is `{0, 1}`** (`mem_fixedField_two_one_iff`). -/
theorem gf256_mem_bit {x : GF2_256} : x ∈ gf256.node "bit" ↔ x = 0 ∨ x = 1 := by
  change x ∈ gf256Node "bit" ↔ _
  simp only [gf256Node, show ("bit" = "GF(2^16)") = False from by decide, if_false, if_true]
  exact mem_fixedField_two_one_iff

/-- **The model of `GF(2^256)`** at the node `bit`, its prime subfield and its bit node: the
registry entry `gf2_256Entry` (cardinality `2^256`, `gf2_256_card`); `0` and `1` read and decode as
themselves; the node `bit` is `{0, 1}` (`gf256_mem_bit`); additive bit coordinates
(`gf256_bitsAdditive`). -/
theorem gf256_model : gf256.Model ["bit"] ["bit"] where
  entry := ⟨gf2_256Entry, by simp [fieldRegistry], rfl⟩
  ringChar := ringChar.eq GF2_256 2
  card := gf2_256_card
  toNat_lt h := absurd h (by decide)
  toNat_natCast k hk := by
    change k < 2 at hk
    interval_cases k
    · rw [Nat.cast_zero]
      exact gf256_toNat_zero
    · rw [Nat.cast_one]
      exact gf256_toNat_one
  decode_natCast c hc := by
    change c < 2 at hc
    change gf2_256OfNat c = (c : GF2_256)
    interval_cases c
    · rw [Nat.cast_zero]
      exact gf2_256OfNat_zero
    · rw [Nat.cast_one]
      exact gf2_256OfNat_one
  natCast_toNat E hE x hx := by
    rw [List.mem_singleton] at hE
    subst hE
    change ((gf256.toNat x : ℕ) : GF2_256) = x
    rcases gf256_mem_bit.1 hx with rfl | rfl
    · exact (congrArg (fun n : ℕ => (n : GF2_256)) gf256_toNat_zero).trans Nat.cast_zero
    · exact (congrArg (fun n : ℕ => (n : GF2_256)) gf256_toNat_one).trans Nat.cast_one
  rootNode := by
    change gf256Node gf256.spec.name = ⊤
    rw [gf256Node, if_neg (by decide), if_neg (by decide)]
  bitNode E hE x hx := by
    rw [List.mem_singleton] at hE
    subst hE
    exact gf256_mem_bit.1 hx
  bitsAdditive := gf256_bitsAdditive

/-- **`GF(2^256)` is a binary MAC field of width `256` with the taps `{0, 2, 5, 10}`**
(`FieldInterp.MacFieldOk`): characteristic `2`, the polynomial basis `gf2_256ConvBasis` whose
coordinates are the bits of the integer reading (`BitVec.testBit_toNat`) and whose elements are the
powers of `x`, the decoding of `2`; the constants `2^j` decode to `x^j` (`gf2_256OfNat_two_pow`). -/
theorem gf256_macFieldOk : gf256.MacFieldOk 256 Conv.gf2_256Taps where
  charTwo := inferInstanceAs (CharP GF2_256 2)
  basis := ⟨gf2_256ConvBasis, fun x _ => (BitVec.testBit_toNat (x := (x : BitVec 256))).symm,
    fun _ => rfl⟩
  decodePow _ hj := gf2_256OfNat_two_pow hj

/-- **The bits of a packed word are its bits**: at `GF(2^16)`, bit `j` of the word packing `b` in
the packing basis is `b (j mod 16)` (`PackedClaim.decode_pack`, `coord_zero_of_mem`). -/
theorem gf256Coord_pack (b : Fin (2 ^ 4) → Bool) (j : ℕ) :
    gf256Coord "GF(2^16)" (PackedClaim.pack gf2_256PackedBasis b) j =
      b ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩ := by
  have hx : PackedClaim.pack gf2_256PackedBasis b ∈ fixedField GF2_256 2 16 :=
    (mem_fixedField_iff_pow).2 (mem_gf2_256Subfield.1 (PackedClaim.pack_mem gf2_256PackedBasis b))
  simp only [gf256Coord, ite_true,
    coord_zero_of_mem gf2_256RelativeBasis gf2_256RelativeBasis_zero hx, PackedClaim.decode_pack]
  cases b ⟨j % 16, _⟩ <;> simp

/-- **The interpretation of an ML-DSA program at the QROM parameters** with domain `A` over `F0`: field `0` is `F0`,
field `1` (and any other identifier) `GF(2^256)`; the opaque functions `targetBitsFn`. -/
abbrev mldsaQROMInterp (F0 : FieldInterp) : Interp := mldsaInterpOf F0 gf256

end GordieHowe.RealizedProgram
