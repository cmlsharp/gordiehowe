-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Basic
public import GordieHowe.Applications.Falcon512.Spec.KeyNTT
public import GordieHowe.Applications.FieldInterps.Fq20
public import GordieHowe.Applications.FieldInterps.GF256
public import GordieHowe.Foundations.Fields.GF2_128Selection
public import GordieHowe.Foundations.Fields.GF2_256Selection
public import GordieHowe.Language.Realizations.MaskSubfield

@[expose] public section

/-!
# GordieHowe frontend: the fields of a native Falcon program

The native Falcon frontend reads a program with domain `H` over a binary field `FH` and domain `A`
over an extension `FA` of `F_q`, `q = 12289` (`falconInterpOf FH FA`); its facts about the fields
hold for any interpretations with the data and facts below, discharged once per field:

* **domain `H`'s field** (`GordieHowe.Falcon512.HField`): the selection field of the hash-to-point selection at
  `S = 639` samples (`sel`: the subfield `GF(2^16)`, `X`, the labels `g^j`, the embedding basis
  `e_u = g^u`, linearly independent over `GF(2)`), characteristic two, `|K| = 2^bits`, the decodings
  of `0`, `1`, `2 = X` and of xors, and the integer readings of `0` and `1`. Instances: `GF(2^128)`
  (`gf128`, `Falcon512.Native.ROMParams`) and `GF(2^256)` (`gf256`, `Falcon512.Native.QROMParams`).
* **domain `A`'s field** (`GordieHowe.Falcon512.AField`): characteristic `q`, the constant coordinate `coord0`, an
  additive map to `F_q` taking the cast of a natural to its cast, the integer reading the constant
  coordinate's value, constants decoded as casts, the node `GF(p^1)` the prime subfield. Instances:
  `F_q^9` (`fq9`) and `F_q^20` (`fq20`).
-/

namespace GordieHowe

open RealizedProgram.Export RelativePacking

/-- **The key's coefficients as the verifier computes them** (the opaque value `key.coefficients`
of the emulated programs, read by `signature.equation`'s `negacyclicConv` in coefficient form),
entry `i` as a natural: the statement's `hhat` (the first argument's `512` entries) decoded as the
verifier's preprocessing does (`FalconKeyNTT.falconDecode 512 12289`: every entry below `q`, then
the C++ inverse transform); `0` when `hhat` does not decode (a statement the member check
`falcon_key_canonical` rejects) and beyond the `512` coefficients. -/
def RealizedProgram.keyCoeffs (xs : List (ℕ → ℕ)) (i : ℕ) : ℕ :=
  match Falcon512.KeyNTT.falconDecode 512 12289 (fun j : Fin 512 => (xs.headD 0) j) with
  | some c => if h : i < 512 then c ⟨i, h⟩ else 0
  | none => 0

/-- **The opaque functions of a Falcon program**: `key.coefficients` the key's coefficients
(`keyCoeffs`, read by the emulated programs), every other name as `targetBitsFn`
(`mac.target_bits`). -/
def RealizedProgram.falconOps : String → List (ℕ → ℕ) → ℕ → ℕ := fun nm xs i =>
  open Classical in
  if nm = "key.coefficients" then keyCoeffs xs i else targetBitsFn nm xs i

theorem RealizedProgram.falconOps_target (xs : List (ℕ → ℕ)) (i : ℕ) :
    falconOps "mac.target_bits" xs i = targetBitsFn "mac.target_bits" xs i := by
  simp [falconOps]

/-- **Every opaque function of a Falcon program computing a bit returns one**: `mac.target_bits`. -/
theorem RealizedProgram.falconOps_lt_two_of_ne {nm : String} (h : nm ≠ "key.coefficients")
    (xs : List (ℕ → ℕ)) (i : ℕ) : falconOps nm xs i < 2 := by
  simp only [falconOps, h, if_false]
  exact targetBitsFn_lt_two nm xs i

/-- **The name of an opaque statement value computed from arguments** (`""` for any other kind). -/
def RealizedProgram.Kind.opaqueArgsName : Kind → String
  | .pub (.opaque name (_ :: _)) => name
  | _ => ""

/-- **The opaque `Bit` values of a Falcon program return bits** (`Interp.Lawful.opaqueBit` at
`falconOps`): given, decided per program, that no opaque `Bit` value computed from arguments is
`key.coefficients` (a field value). -/
theorem RealizedProgram.falconOps_opaqueBit {ir : RealizedProgram}
    (h : ∀ v < ir.values.length, (ir.value v).type = .bit →
      (ir.value v).kind.opaqueArgsName ≠ "key.coefficients") :
    ∀ v < ir.values.length, ∀ name args, (ir.value v).kind = .pub (.opaque name args) →
      args ≠ [] → (ir.value v).type = .bit → ∀ xs i, falconOps name xs i < 2 := by
  intro v hv name args hk hne hb xs i
  refine falconOps_lt_two_of_ne ?_ xs i
  have := h v hv hb
  rw [hk] at this
  cases args with
  | nil => exact absurd rfl hne
  | cons a as => exact this

/-- **The interpretation of a Falcon program**: field `0` (domain `H`) is `FH`, field `1` (domain
`A`, and any other identifier) `FA`; the opaque functions `falconOps`. -/
abbrev RealizedProgram.falconInterpOf (FH FA : FieldInterp) : Interp :=
  ⟨fun n => match n with | 0 => FH | _ => FA, falconOps⟩

/-- **The field models of a Falcon interpretation**: field `0` has `FH`'s model, every other field
`FA`'s. -/
theorem RealizedProgram.falconInterpOf_models {FH FA : FieldInterp} {pH bH pA bA : List String}
    (hH : FH.Model pH bH) (hA : FA.Model pA bA) :
    (falconInterpOf FH FA).Models (twoFieldNodes pH pA) (twoFieldNodes bH bA)
  | 0 => hH
  | _ + 1 => hA

/-- **`mac.target_bits` of a Falcon program returns the bits of its argument's first
coordinate.** -/
theorem RealizedProgram.falconOps_target_bits (xs : List (ℕ → ℕ)) (i : ℕ) :
    falconOps "mac.target_bits" xs i = if ((xs.headD 0) 0).testBit i then 1 else 0 := by
  rw [falconOps_target, targetBitsFn_target]

/-! ## Domain `H`'s field -/

/-- **The field data and facts of domain `H`'s field interpretation** (see the module docstring). -/
class Falcon512.HField (FH : RealizedProgram.FieldInterp) where
  /-- The field has characteristic two. -/
  charTwo : CharP FH.K 2
  /-- The selection field. -/
  sel : SelectionField FH.K falcon512.S
  /-- The embedding basis is the labels' first powers. -/
  e_eq : ∀ u, sel.e u = sel.g ^ (u : ℕ)
  /-- The embedding basis is linearly independent over `GF(2)`. -/
  e_li : letI : CharP FH.K 2 := charTwo
    letI : Algebra (ZMod 2) FH.K := ZMod.algebra FH.K 2
    LinearIndependent (ZMod 2) sel.e
  /-- The field's bit length. -/
  bits : ℕ
  /-- The field has `2^bits` elements. -/
  card : Fintype.card FH.K = 2 ^ bits
  /-- The constant `0` decodes to `0`. -/
  decode_zero : FH.decode 0 = 0
  /-- The constant `1` decodes to `1`. -/
  decode_one : FH.decode 1 = 1
  /-- The constant `2` decodes to the packing constant `X`. -/
  decode_two : FH.decode 2 = sel.X
  /-- Decoding is additive on xors. -/
  decode_xor : ∀ a b, FH.decode (a ^^^ b) = FH.decode a + FH.decode b
  /-- `0` is read as `0`. -/
  toNat_zero : FH.toNat 0 = 0
  /-- `1` is read as `1`. -/
  toNat_one : FH.toNat 1 = 1
  /-- The packing basis of the committed words (`GF(2^16)` over `GF(2)`). -/
  packing : PackedClaim.PackedBasis FH.K 4
  /-- Bit `j` of a packed word at the node `GF(2^16)` is its bit `j mod 16`. -/
  coord_pack : ∀ (b : Fin (2 ^ 4) → Bool) (j : ℕ),
    FH.coord "GF(2^16)" (PackedClaim.pack packing b) j = b ⟨j % 16, Nat.mod_lt _ (by norm_num)⟩
  /-- The node `GF(2^16)` is the fixed field of `x ↦ x^(2^16)`. -/
  node16 : ∀ x, x ∈ FH.node "GF(2^16)" ↔ x ∈ fixedField FH.K 2 16
  /-- The node `bit` is `{0, 1}`. -/
  nodeBit : ∀ x, x ∈ FH.node "bit" ↔ x = 0 ∨ x = 1
  /-- The packed words lie in `GF(2^16)`. -/
  pack_mem : ∀ b, PackedClaim.pack packing b ∈ fixedField FH.K 2 16
  /-- The selection's generator lies in `GF(2^16)`. -/
  g_mem : sel.g ∈ fixedField FH.K 2 16

instance Falcon512.HField.instCharP (FH : RealizedProgram.FieldInterp) [h : HField FH] : CharP FH.K 2 :=
  h.charTwo

/-- `GF(2^128)` has domain `H`'s field data (`gf2_128SelectionField`). -/
instance : Falcon512.HField RealizedProgram.gf128 where
  sel := gf2_128SelectionField
  e_eq _ := rfl
  e_li := linearIndependent_gf2_128SubfieldBasis
  bits := 128
  card := gf2_128_card
  charTwo := inferInstanceAs (CharP GF2_128 2)
  decode_zero := gf2_128OfNat_zero
  decode_one := gf2_128OfNat_one
  decode_two := rfl
  decode_xor := gf2_128OfNat_xor
  toNat_zero := RealizedProgram.gf128_toNat_zero
  toNat_one := RealizedProgram.gf128_toNat_one
  packing := gf2_128PackedBasis
  coord_pack := RealizedProgram.gf2Coord_pack
  node16 x := by
    change x ∈ RealizedProgram.gf2Node "GF(2^16)" ↔ _
    rw [RealizedProgram.gf2Node, if_pos rfl]
    rfl
  nodeBit x := by
    change x ∈ RealizedProgram.gf2Node "bit" ↔ _
    rw [RealizedProgram.gf2Node, if_neg (by decide), if_pos rfl]
    exact RealizedProgram.mem_fixedField_two_one
  pack_mem b := show PackedClaim.pack gf2_128PackedBasis b ∈ fixedField GF2_128 2 16 from
    (RelativePacking.mem_fixedField_iff_pow).2 (mem_gf2_128Subfield.1 (PackedClaim.pack_mem gf2_128PackedBasis b))
  g_mem := show gf2_128SelectionField.g ∈ fixedField GF2_128 2 16 from
    (RelativePacking.mem_fixedField_iff_pow).2 (mem_gf2_128Subfield.1 gf2_128SelectionField.g_mem)

/-- `GF(2^256)` has domain `H`'s field data (`gf2_256SelectionField`). -/
instance : Falcon512.HField RealizedProgram.gf256 where
  sel := gf2_256SelectionField
  e_eq _ := rfl
  e_li := linearIndependent_gf2_256SubfieldBasis
  bits := 256
  card := gf2_256_card
  charTwo := inferInstanceAs (CharP GF2_256 2)
  decode_zero := RealizedProgram.gf2_256OfNat_zero
  decode_one := gf2_256OfNat_one
  decode_two := rfl
  decode_xor := RealizedProgram.gf2_256OfNat_xor
  toNat_zero := RealizedProgram.gf256_toNat_zero
  toNat_one := RealizedProgram.gf256_toNat_one
  packing := gf2_256PackedBasis
  coord_pack := RealizedProgram.gf256Coord_pack
  node16 x := by
    change x ∈ RealizedProgram.gf256Node "GF(2^16)" ↔ _
    rw [RealizedProgram.gf256Node, if_pos rfl]
    rfl
  nodeBit x := by
    change x ∈ RealizedProgram.gf256Node "bit" ↔ _
    rw [RealizedProgram.gf256Node, if_neg (by decide), if_pos rfl]
    exact RealizedProgram.mem_fixedField_two_one_iff
  pack_mem b := show PackedClaim.pack gf2_256PackedBasis b ∈ fixedField GF2_256 2 16 from
    (RelativePacking.mem_fixedField_iff_pow).2 (mem_gf2_256Subfield.1 (PackedClaim.pack_mem gf2_256PackedBasis b))
  g_mem := show gf2_256SelectionField.g ∈ fixedField GF2_256 2 16 from
    (RelativePacking.mem_fixedField_iff_pow).2 (mem_gf2_256Subfield.1 gf2_256SelectionField.g_mem)

/-- **A natural below `2` decodes to its bit.** -/
theorem Falcon512.HField.decode_lt_two {FH : RealizedProgram.FieldInterp} [HField FH] {b : ℕ} (hb : b < 2) :
    FH.decode b = if b = 1 then 1 else 0 := by
  interval_cases b
  · exact HField.decode_zero
  · exact HField.decode_one

/-! ## Domain `A`'s field -/

/-- **The field data and facts of domain `A`'s field interpretation** (see the module docstring). -/
class Falcon512.AField (FA : RealizedProgram.FieldInterp) where
  /-- The field has characteristic `q`. -/
  charQ : CharP FA.K 12289
  /-- The registry's characteristic is `q`. -/
  spec_char : FA.spec.characteristic = 12289
  /-- The constant coordinate. -/
  coord0 : FA.K →+ ZMod 12289
  /-- The constant coordinate of a natural's cast is its cast. -/
  coord0_natCast : ∀ n : ℕ, coord0 (n : FA.K) = n
  /-- The integer reading is the constant coordinate's value. -/
  toNat_eq : ∀ x, FA.toNat x = (coord0 x).val
  /-- Constants decode to their casts. -/
  decode_eq : ∀ c, FA.decode c = (c : FA.K)
  /-- The node `GF(p^1)` is the prime subfield. -/
  node_prime : ∀ x, x ∈ FA.node "GF(p^1)" ↔ x ∈ fixedField FA.K 12289 1

instance Falcon512.AField.instCharP (FA : RealizedProgram.FieldInterp) [h : AField FA] : CharP FA.K 12289 :=
  h.charQ

/-- `F_q^9` has domain `A`'s field data: the constant coordinate `falconNative9Coords x 0`. -/
instance : Falcon512.AField RealizedProgram.fq9 where
  charQ := inferInstanceAs (CharP FalconNativeField9 12289)
  spec_char := rfl
  coord0 :=
    { toFun x := falconNative9Coords x 0
      map_zero' := falconNative9Coords_zero 0
      map_add' x y := falconNative9Coords_add x y 0 }
  coord0_natCast := falconNative9Coords_natCast
  toNat_eq _ := rfl
  decode_eq _ := rfl
  node_prime x := by
    change x ∈ RealizedProgram.fq9Node "GF(p^1)" ↔ _
    rw [RealizedProgram.fq9Node, if_pos rfl]
    rfl

/-- `F_q^20` has domain `A`'s field data: the constant coordinate
`falconQuarticCoords (falconNative20Coords x 0) 0`. -/
instance : Falcon512.AField RealizedProgram.fq20 where
  charQ := inferInstanceAs (CharP FalconNativeField20 12289)
  spec_char := rfl
  coord0 :=
    { toFun x := falconQuarticCoords (falconNative20Coords x 0) 0
      map_zero' := by
        have h := falconNative20Coords_natCast 0
        rwa [Nat.cast_zero, Nat.cast_zero] at h
      map_add' x y :=
        (congrArg (falconQuarticCoords · 0)
          (falconNative20Coords_add (x : FalconNativeField20) y 0)).trans
          (falconQuarticCoords_add _ _ 0) }
  coord0_natCast := falconNative20Coords_natCast
  toNat_eq _ := rfl
  decode_eq _ := rfl
  node_prime x := by
    change x ∈ RealizedProgram.fq20Node "GF(p^1)" ↔ _
    rw [RealizedProgram.fq20Node, if_pos rfl]
    rfl

namespace Falcon512.AField

variable {FA : RealizedProgram.FieldInterp} [AField FA]

/-- **The prime field `F_q` in `FA`.** -/
abbrev φq : ZMod 12289 →+* FA.K := ZMod.castHom (dvd_refl 12289) _

theorem φq_apply (z : ZMod 12289) : (φq z : FA.K) = ((z.val : ℕ) : FA.K) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

/-- The constant coordinate of an element of `F_q`. -/
theorem coord0_φq (z : ZMod 12289) : coord0 (φq z : FA.K) = z := by
  rw [φq_apply, coord0_natCast, ZMod.natCast_zmod_val]

/-- **The constant coordinate is `F_q`-linear.** -/
theorem coord0_φq_mul (z : ZMod 12289) (y : FA.K) : coord0 (φq z * y) = z * coord0 y := by
  rw [φq_apply, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

/-- **The integer reading is below `q`.** -/
theorem toNat_lt (x : FA.K) : FA.toNat x < 12289 := by
  rw [toNat_eq]
  exact ZMod.val_lt _

/-- **The integer reading inverts the cast of a natural below `q`.** -/
theorem toNat_natCast {k : ℕ} (hk : k < 12289) : FA.toNat (k : FA.K) = k := by
  rw [toNat_eq, coord0_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem toNat_zero : FA.toNat 0 = 0 := by
  have h := toNat_natCast (FA := FA) (k := 0) (by norm_num)
  rwa [Nat.cast_zero] at h

theorem toNat_one : FA.toNat 1 = 1 := by
  have h := toNat_natCast (FA := FA) (k := 1) (by norm_num)
  rwa [Nat.cast_one] at h

/-- **An element of the prime subfield is the cast of its integer reading.** -/
theorem natCast_toNat {x : FA.K} (hx : x ∈ FA.node "GF(p^1)") :
    ((FA.toNat x : ℕ) : FA.K) = x := by
  rw [node_prime] at hx
  let : Algebra (ZMod 12289) FA.K := ZMod.algebra FA.K 12289
  obtain ⟨z, rfl⟩ : x ∈ Set.range (algebraMap (ZMod 12289) FA.K) := by
    rw [GordieHowe.range_algebraMap_eq_fixedField]
    exact hx
  have h : algebraMap (ZMod 12289) FA.K z = φq z := rfl
  rw [h, toNat_eq, coord0_φq, ← φq_apply]

end Falcon512.AField

/-- **Domain `A`'s integer readings below `q`** (what the Falcon frontend's crossing and statement
read of domain `A`'s field): the integer reading inverts the cast of a natural below `q = 12289`. Every
field of characteristic `q` (`Falcon512.AField`) and every field of larger characteristic whose integer
reading inverts the casts below it (Goldilocks², Goldilocks⁴) has it. -/
class Falcon512.AReading (FA : RealizedProgram.FieldInterp) : Prop where
  /-- The integer reading inverts the cast of a natural below `q`. -/
  toNat_natCast : ∀ {k : ℕ}, k < 12289 → FA.toNat (k : FA.K) = k

instance (priority := 100) Falcon512.AField.toFalconAReading (FA : RealizedProgram.FieldInterp) [Falcon512.AField FA] :
    Falcon512.AReading FA :=
  ⟨Falcon512.AField.toNat_natCast⟩

namespace Falcon512.AReading

variable {FA : RealizedProgram.FieldInterp} [AReading FA]

theorem toNat_zero : FA.toNat 0 = 0 := by
  have h := toNat_natCast (FA := FA) (k := 0) (by norm_num)
  rwa [Nat.cast_zero] at h

theorem toNat_one : FA.toNat 1 = 1 := by
  have h := toNat_natCast (FA := FA) (k := 1) (by norm_num)
  rwa [Nat.cast_one] at h

end Falcon512.AReading

end GordieHowe
