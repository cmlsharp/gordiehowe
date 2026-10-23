-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldModel
public import GordieHowe.Foundations.Algebra.RelativePackingAdditive
public import GordieHowe.Foundations.Fields.GF2_128Relative
public import GordieHowe.Foundations.Fields.GF2_128Dual
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9Relative
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNativeCoords

@[expose] public section

/-!
# GordieHowe: the fields of the programs, read in Lean

The field interpretations (`FieldInterp`, `GordieHowe/Language/RealizedProgram/Semantics.lean`) that several
programs share:

* **`GF(2^128)`** (`gf128`): the registry entry `gf2_128Entry`, `GF2_128`; constants are the
  polynomial-basis bits (`gf2_128OfNat`), and so is the integer reading; the nodes `GF(2^16)` and
  `bit` are the fixed fields of `x ↦ x^(2^16)` and `x ↦ x^2` (`gf2Node`); bit `j` of a `GF(2^16)`
  value is its decoded bit in the packing basis `gf2_128PackedBasis`, read through the first
  coordinate of the relative basis (`gf2Coord`: on `GF(2^16)` the value itself,
  `coord_zero_of_mem`), which is additive on the field (`gf128_bitsAdditive`). The node `bit` is
  `{0, 1}` (`mem_fixedField_two_one`). Its model at the node `bit` (`gf128_model`); a binary MAC
  field of width `128` with the taps `{0, 1, 2, 7}` (`gf128_macFieldOk`).
* **`F_q^9`** (`fq9`, `q = 12289`): the registry entry `falconNative9Entry`,
  `FalconNativeField9`; constants are casts of naturals, the integer reading is the constant
  coefficient; the node `GF(p^1)` is the prime subfield `F_q` (`fq9Node`); no bit coordinates. Its
  model at `GF(p^1)` (`fq9_model`); its integer reading is linear (`fq9_readLinear`).
* **The MAC target's bits** (`targetBitsFn`): the opaque function `mac.target_bits` of the programs
  with a MAC.
-/

namespace GordieHowe.RealizedProgram

open Export RelativePacking

/-! ## `GF(2^128)` -/

/-- The relative basis of `GF(2^128)` over `GF(2^16)` starts at `1`. -/
theorem gf2_128RelativeBasis_zero : gf2_128RelativeBasis.β 0 = 1 := pow_zero _

/-- **The nodes of `GF(2^128)`**: `GF(2^16)` the fixed field of `x ↦ x^(2^16)`, `bit` the fixed
field of `x ↦ x^2` (`{0, 1}`), any other name the field. -/
def gf2Node (s : String) : AddSubgroup GF2_128 :=
  if s = "GF(2^16)" then (fixedField GF2_128 2 16).toSubring.toAddSubgroup
  else if s = "bit" then (fixedField GF2_128 2 1).toSubring.toAddSubgroup else ⊤

/-- Membership in a node of `GF(2^128)` is decidable (one exponentiation). -/
instance gf2NodeDec (s : String) : DecidablePred (· ∈ gf2Node s) := fun x => by
  unfold gf2Node
  split
  · exact decidableMemFixedField (p := 2) (m := 16) x
  · split
    · exact decidableMemFixedField (p := 2) (m := 1) x
    · exact isTrue (AddSubgroup.mem_top x)

/-- **Bit `j` of a `GF(2^128)` element at a node**: at `GF(2^16)`, decoded bit `j mod 16` in the
packing basis (`PackedClaim.decode gf2_128PackedBasis`) of the first relative coordinate (on
`GF(2^16)` the element itself, `coord_zero_of_mem`); no bits at other nodes. -/
def gf2Coord (s : String) (x : GF2_128) (j : ℕ) : Bool :=
  if s = "GF(2^16)" then
    decide (PackedClaim.decode gf2_128PackedBasis (coord gf2_128RelativeBasis x 0)
      ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩ = 1)
  else false

/-- **`GF(2^128)` as a field of the program**: the registry entry, `GF2_128`, constants as
polynomial-basis bits (`gf2_128OfNat`), the integer reading the polynomial-basis bits, the nodes
`gf2Node`, the bit coordinates `gf2Coord`. -/
def gf128 : FieldInterp where
  spec := gf2_128Entry.spec
  K := GF2_128
  decode := gf2_128OfNat
  toNat x := BitVec.toNat (show BitVec 128 from x)
  node := gf2Node
  memDec := gf2NodeDec
  coord := gf2Coord

/-- The integer reading of `GF(2^128)` reads `0` as `0`. -/
theorem gf128_toNat_zero : gf128.toNat 0 = 0 := by decide

/-- The integer reading of `GF(2^128)` reads `1` as `1`. -/
theorem gf128_toNat_one : gf128.toNat 1 = 1 := by decide

/-- **The bits' node is `{0, 1}`**: the fixed field of `x ↦ x^2`. -/
theorem mem_fixedField_two_one {x : GF2_128} : x ∈ fixedField GF2_128 2 1 ↔ x = 0 ∨ x = 1 := by
  rw [mem_fixedField_iff_pow, pow_one]
  constructor
  · intro h
    exact eq_zero_or_one_of_sq_eq_self h
  · rintro (rfl | rfl) <;> simp

/-- The reading of a bit in `GF(2^128)`: `1` or `0`. -/
def gf2BitVal (b : Bool) : GF2_128 := if b then 1 else 0

/-- An element of `{0, 1}` is the reading of its being `1`. -/
theorem gf2BitVal_decide_eq_one {x : GF2_128} (h : x = 0 ∨ x = 1) :
    gf2BitVal (decide (x = 1)) = x := by
  rcases h with rfl | rfl
  · simp [gf2BitVal]
  · simp [gf2BitVal]

/-- **The bit coordinates of `GF(2^128)` are additive**: decoding is additive
(`PackedClaim.decode_add`), the first relative coordinate is (`coord_add`), and the decoded bits are
`0` or `1` (`PackedClaim.decode_bool`). -/
theorem gf2Coord_add (E : String) (j : ℕ) (x y : GF2_128) :
    gf2BitVal (gf2Coord E (x + y) j) = gf2BitVal (gf2Coord E x j) + gf2BitVal (gf2Coord E y j) := by
  unfold gf2Coord
  split_ifs
  · have hb : ∀ z : GF2_128, PackedClaim.decode gf2_128PackedBasis (coord gf2_128RelativeBasis z 0)
        ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩ = 0 ∨
        PackedClaim.decode gf2_128PackedBasis (coord gf2_128RelativeBasis z 0)
          ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩ = 1 := fun z =>
      PackedClaim.decode_bool _ (coord_mem _ _ _) _
    rw [coord_add, PackedClaim.decode_add, gf2BitVal_decide_eq_one ((hb x).elim
      (fun h0 => (hb y).elim (fun h1 => .inl (by rw [h0, h1, add_zero]))
        fun h1 => .inr (by rw [h0, h1, zero_add]))
      fun h0 => (hb y).elim (fun h1 => .inr (by rw [h0, h1, add_zero]))
        fun h1 => .inl (by rw [h0, h1]; exact CharTwo.add_self_eq_zero 1)),
      gf2BitVal_decide_eq_one (hb x), gf2BitVal_decide_eq_one (hb y)]
  · simp [gf2BitVal]

/-- **The bit coordinates of `GF(2^128)` as a field of the program are additive**
(`gf2Coord_add`). -/
theorem gf128_bitsAdditive : gf128.BitsAdditive := fun E j x y => gf2Coord_add E j x y

/-- **The node `bit` of `GF(2^128)` is `{0, 1}`** (`mem_fixedField_two_one`). -/
theorem gf128_mem_bit {x : GF2_128} : x ∈ gf128.node "bit" ↔ x = 0 ∨ x = 1 := by
  change x ∈ gf2Node "bit" ↔ _
  simp only [gf2Node, show ("bit" = "GF(2^16)") = False from by decide, if_false, if_true]
  exact mem_fixedField_two_one

/-- **The model of `GF(2^128)`** at the node `bit`, its prime subfield and its bit node: the
registry entry `gf2_128Entry` (cardinality `2^128`, `gf2_128_card`); `0` and `1` read and decode as
themselves; the node `bit` is `{0, 1}` (`gf128_mem_bit`); additive bit coordinates
(`gf128_bitsAdditive`). -/
theorem gf128_model : gf128.Model ["bit"] ["bit"] where
  entry := ⟨gf2_128Entry, by simp [fieldRegistry], rfl⟩
  ringChar := ringChar.eq GF2_128 2
  card := gf2_128_card
  toNat_lt h := absurd h (by decide)
  toNat_natCast k hk := by
    change k < 2 at hk
    interval_cases k
    · rw [Nat.cast_zero]
      exact gf128_toNat_zero
    · rw [Nat.cast_one]
      exact gf128_toNat_one
  decode_natCast c hc := by
    change c < 2 at hc
    change gf2_128OfNat c = (c : GF2_128)
    interval_cases c
    · rw [Nat.cast_zero]
      decide
    · rw [Nat.cast_one]
      exact gf2_128OfNat_one
  natCast_toNat E hE x hx := by
    rw [List.mem_singleton] at hE
    subst hE
    change ((gf128.toNat x : ℕ) : GF2_128) = x
    rcases gf128_mem_bit.1 hx with rfl | rfl
    · decide
    · decide
  rootNode := by
    change gf2Node gf128.spec.name = ⊤
    rw [gf2Node, if_neg (by decide), if_neg (by decide)]
  bitNode E hE x hx := by
    rw [List.mem_singleton] at hE
    subst hE
    exact gf128_mem_bit.1 hx
  bitsAdditive := gf128_bitsAdditive

/-- **`GF(2^128)` is a binary MAC field of width `128` with the taps `{0, 1, 2, 7}`**
(`FieldInterp.MacFieldOk`): characteristic `2`, the polynomial basis `gf2_128ConvBasis` whose
coordinates are the bits of the integer reading and whose elements are the powers of `x`, the
decoding of `2`; the constants `2^j` decode to `x^j` (`gf2_128OfNat_two_pow`). -/
theorem gf128_macFieldOk : gf128.MacFieldOk 128 Conv.gf2_128Taps where
  charTwo := inferInstanceAs (CharP GF2_128 2)
  basis := ⟨gf2_128ConvBasis, fun _ _ => rfl, fun _ => rfl⟩
  decodePow _ hj := gf2_128OfNat_two_pow hj

/-- **The bits of a packed word are its bits**: at `GF(2^16)`, bit `j` of the word packing `b` in
the packing basis is `b (j mod 16)` (`PackedClaim.decode_pack`, `coord_zero_of_mem`). -/
theorem gf2Coord_pack (b : Fin (2 ^ 4) → Bool) (j : ℕ) :
    gf2Coord "GF(2^16)" (PackedClaim.pack gf2_128PackedBasis b) j =
      b ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩ := by
  have hx : PackedClaim.pack gf2_128PackedBasis b ∈ fixedField GF2_128 2 16 :=
    (mem_fixedField_iff_pow).2 (mem_gf2_128Subfield.1 (PackedClaim.pack_mem gf2_128PackedBasis b))
  simp only [gf2Coord, ite_true, coord_zero_of_mem gf2_128RelativeBasis gf2_128RelativeBasis_zero hx,
    PackedClaim.decode_pack]
  cases b ⟨j % 16, _⟩ <;> simp

/-! ## `F_q^9` -/

/-- **The nodes of `F_q^9`**: `GF(p^1)` is the prime subfield `F_q`, any other name the field. -/
def fq9Node (s : String) : AddSubgroup FalconNativeField9 :=
  if s = "GF(p^1)" then (fixedField FalconNativeField9 12289 1).toSubring.toAddSubgroup else ⊤

/-- Membership in a node of `F_q^9` is decidable (one exponentiation for `F_q`). -/
instance fq9NodeDec (s : String) : DecidablePred (· ∈ fq9Node s) := fun x => by
  unfold fq9Node
  split
  · exact decidableMemFixedField (p := 12289) (m := 1) x
  · exact isTrue (AddSubgroup.mem_top x)

/-- **`F_q^9` as a field of the program**: the registry entry, `FalconNativeField9`, constants as
casts of naturals, the integer reading the constant coefficient, the nodes `fq9Node`, no bit
coordinates (an odd field). -/
def fq9 : FieldInterp where
  spec := falconNative9Entry.spec
  K := FalconNativeField9
  decode n := (n : FalconNativeField9)
  toNat x := (falconNative9Coords x 0).val
  node := fq9Node
  memDec := fq9NodeDec
  coord _ _ _ := false

/-- The integer reading of `F_q^9` reads `0` as `0`. -/
theorem fq9_toNat_zero : fq9.toNat 0 = 0 := by
  change (falconNative9Coords (0 : FalconNativeField9) 0).val = 0
  rw [← Nat.cast_zero, falconNative9Coords_natCast, Nat.cast_zero, ZMod.val_zero]

/-- **The model of `F_q^9`** at its prime subfield `GF(p^1)` (`FieldInterp.model_of_primeCoord`):
the registry entry `falconNative9Entry` (cardinality `q^9`, `falconNativeField_card`), the integer
reading the constant coordinate (`falconNative9Coords_natCast`,
`falconNative9Coords_algebraMap`). -/
theorem fq9_model : fq9.Model ["GF(p^1)"] [] :=
  FieldInterp.model_of_primeCoord (spec := falconNative9Entry.spec) (p := 12289)
    (c := fun x => falconNative9Coords x 0) ⟨falconNative9Entry, by simp [fieldRegistry], rfl⟩ rfl
    falconNativeField_card falconNative9Coords_natCast falconNative9Coords_algebraMap
    (fun _ hx => by rwa [fq9Node, if_pos rfl] at hx)
    (by rw [fq9Node, if_neg (by decide)])

/-- **`F_q^9` reads linearly** (`FieldInterp.ReadLinear`): its integer reading is the constant
coordinate, additive (`falconNative9Coords_val_cast_add`). -/
theorem fq9_readLinear : fq9.ReadLinear :=
  .of_add falconNative9Coords_val_cast_add (by rw [fq9_toNat_zero, Nat.cast_zero])

/-! ## Opaque functions -/

/-- **The MAC target's bits** (`<mac>.target_bits`, the opaque function of the programs with a MAC):
`mac.target_bits` returns `1` at coordinate `i` when bit `i` of its argument's first coordinate is
set (the argument is the integer reading of the MAC tag's message, its polynomial-basis coefficients
in the binary MAC field), `0` otherwise; every other name `0` (the programs' other opaque values
take no arguments and are read from the statement). -/
def targetBitsFn (nm : String) (xs : List (ℕ → ℕ)) (i : ℕ) : ℕ :=
  if nm = "mac.target_bits" then (if ((xs.headD 0) 0).testBit i then 1 else 0) else 0

/-- **The MAC target's bits are bits.** -/
theorem targetBitsFn_lt_two (nm : String) (xs : List (ℕ → ℕ)) (i : ℕ) :
    targetBitsFn nm xs i < 2 := by
  unfold targetBitsFn
  split_ifs <;> omega

/-- **`mac.target_bits` returns the bits of its argument's first coordinate.** -/
theorem targetBitsFn_target (xs : List (ℕ → ℕ)) (i : ℕ) :
    targetBitsFn "mac.target_bits" xs i = if ((xs.headD 0) 0).testBit i then 1 else 0 :=
  if_pos rfl

end GordieHowe.RealizedProgram
