-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_128Selection
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim

@[expose] public section

/-!
# The packing basis of `GF(2¹²⁸)` and its trace-dual basis

`gf2_128PackedBasis` is the `PackedClaim.PackedBasis GF2_128 4` of the proposed packed bit
witnesses: the sixteen-bit subfield `gf2_128Subfield`, the basis `β i = g ^ i` the flagship packs
with (`beta_[i] = g^i`, `lib/gf2k/gf2_128.h:125-129`), and the trace-dual basis `β*` of `β` for
`Tr x = ∑_{k < 16} x ^ 2^k`, which the packed-witness verifier needs for the decode
`bit_i(p) = Tr(β*_i · p)`.

The dual elements are the `BitVec 128` literals `gf2_128DualBV`, computed
offline by inverting the `16 × 16` trace matrix `Tr(β_i β_j)` over `GF(2)`:
`β*_i = ∑_k C_ik β_k` with `C` the inverse, whose rows are the bit masks
`gf2_128DualCoeff`. The certificate uses the linearity of the trace. Since
`β_k β_j = g ^ (k + j)`, the trace matrix is determined by the 31 traces
`Tr(g ^ m)`, `m < 31`, whose bits are `gf2_128TraceBits`. The `decide +kernel`
checks are the following; the first two evaluate `gfMul` and the trace in the spread
representation `gf2_128Exec` of `GordieHowe.Foundations.Fields.BinarySpread` (`gfMul_eq_of_spread`,
`traceBV_eq_of_spread`), where one multiplication is one `Nat.mul`:

* `gfMul_subfieldPowBV`: the table `gf2_128SubfieldPowBV` holds `g ^ m`;
* `traceBV_subfieldPowBV`: `Tr(g ^ m)` is bit `m` of `gf2_128TraceBits` (four checks of eight
  exponents each);
* `dualBV_eq_xorSum`: `β*_i = ∑_k C_ik β_k` on bits;
* `dualCoeff_trace`: `∑_k C_ik Tr(g ^ (k + j)) = δ_ij` over `GF(2)`.

Membership of `β*_i` in the subfield follows from `β*_i = ∑_k C_ik β_k`.
-/

namespace GordieHowe

open GF2_128Exec

/-- `GF2_128` has Frobenius order `128`: every element is fixed by the `2¹²⁸`-power map. -/
instance : FrobeniusOrder GF2_128 128 :=
  .of_card gf2_128_card (by norm_num)

theorem gf2_128OfBitVec_ite (c : Prop) [Decidable c] (a b : BitVec 128) :
    gf2_128OfBitVec (if c then a else b) = if c then gf2_128OfBitVec a else gf2_128OfBitVec b := by
  split_ifs <;> rfl

/-! ## Additivity of the trace

These are facts about `PackedClaim.trace` and belong in `GordieHowe/ProofSystem/RingSwitching/PackedClaim.lean`. -/

theorem packedTrace_add {F : Type*} [Field F] [CharP F 2] (a : ℕ) (x y : F) :
    PackedClaim.trace a (x + y) = PackedClaim.trace a x + PackedClaim.trace a y := by
  simp only [PackedClaim.trace, add_pow_char_pow, Finset.sum_add_distrib]

theorem packedTrace_zero {F : Type*} [Field F] (a : ℕ) : PackedClaim.trace a (0 : F) = 0 := by
  simp [PackedClaim.trace]

theorem packedTrace_sum {F : Type*} [Field F] [CharP F 2] (a : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → F) : PackedClaim.trace a (∑ i ∈ s, f i) = ∑ i ∈ s, PackedClaim.trace a (f i) :=
  map_sum (AddMonoidHom.mk' (PackedClaim.trace a) (packedTrace_add a)) f s

/-! ## Sums and the trace on bit vectors -/

/-- The exclusive or of `f 0, …, f (n - 1)`. -/
def xorSum : (n : ℕ) → (Fin n → BitVec 128) → BitVec 128
  | 0, _ => 0
  | n + 1, f => f 0 ^^^ xorSum n (fun k => f k.succ)

theorem gf2_128OfBitVec_xorSum (n : ℕ) (f : Fin n → BitVec 128) :
    gf2_128OfBitVec (xorSum n f) = ∑ k, gf2_128OfBitVec (f k) := by
  induction n with
  | zero =>
    rw [xorSum, Fin.sum_univ_zero]
    exact gf2_128OfBitVec_zero
  | succ n ih => rw [xorSum, gf2_128OfBitVec_xor, ih, Fin.sum_univ_succ]

/-- `traceAux n y = ∑_{k < n} y ^ 2^k`, by repeated squaring. -/
def traceAux : ℕ → BitVec 128 → BitVec 128
  | 0, _ => 0
  | n + 1, y => y ^^^ traceAux n (gfMul y y)

theorem gf2_128OfBitVec_traceAux (n : ℕ) (y : BitVec 128) :
    gf2_128OfBitVec (traceAux n y) = ∑ k : Fin n, gf2_128OfBitVec y ^ (2 ^ (k : ℕ)) := by
  induction n generalizing y with
  | zero =>
    rw [traceAux, Fin.sum_univ_zero]
    exact gf2_128OfBitVec_zero
  | succ n ih =>
    rw [traceAux, gf2_128OfBitVec_xor, ih, gf2_128OfBitVec_gfMul, Fin.sum_univ_succ]
    congr 1
    · rw [Fin.val_zero, pow_zero, pow_one]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fin.val_succ, pow_succ', pow_mul, sq]

/-- The trace `Tr x = ∑_{k < 16} x ^ 2^k` on bit vectors. -/
def traceBV (y : BitVec 128) : BitVec 128 := traceAux 16 y

theorem gf2_128OfBitVec_traceBV (y : BitVec 128) :
    gf2_128OfBitVec (traceBV y) = PackedClaim.trace 4 (gf2_128OfBitVec y) := by
  rw [traceBV, gf2_128OfBitVec_traceAux]
  rfl

/-- An identity `traceBV y = z`, checked in the spread representation `gf2_128Exec`. -/
theorem traceBV_eq_of_spread {y z : BitVec 128}
    (h : gf2_128Exec.trace 1 16 (gf2_128Exec.ofBits y.toNat) = gf2_128Exec.ofBits z.toNat) :
    traceBV y = z :=
  gf2_128OfBitVec_injective (by
    rw [traceBV, gf2_128OfBitVec_traceAux, gf2_128OfBitVec_eq_valVia y, gf2_128OfBitVec_eq_valVia z,
      ← h, gf2_128Rep.valVia_trace _ 1 (BinarySpread.Rep.canon_ofBits _)]
    simp only [one_mul])

/-! ## Powers of the generator and their traces -/

/-- `g ^ m` as bits for `m < 31`; `gfMul_subfieldPowBV` checks it. The first
sixteen entries are the basis `β`. -/
def gf2_128SubfieldPowBV : Fin 31 → BitVec 128 :=
  ![0x00000000000000000000000000000001#128, 0x5c5971877501d4b8f1871e01b64fda4c#128,
    0x8bb99658eaf2cae0a6e310fb6e176ea8#128, 0xb61e08da12f9665c3f8de8a2f9ff7eed#128,
    0xa76c2e634c6483ae9ba3282087a3f827#128, 0x54944ff4a5269cedf7af4e93629f689e#128,
    0x5439ecfd75a950d8d0765f1873309b88#128, 0x49ecdfbe06777b02e566f9fc3d9b58a2#128,
    0x97a401b733e66a9319af205497f8e2d0#128, 0x789fd7793ce7523860e4dbdce9777814#128,
    0xaa440b2d4b546256c0f157187adbc05b#128, 0x79f2cadb70b6115d222f207d0d8ad9f9#128,
    0xae72af7894ce037df6d1f84fb66c52b8#128, 0xd6f226d783d454db4af94ef056d28a30#128,
    0x057d918d494925fc0f37a0a4d91b4220#128, 0x18d4bbb6833c5ae8b683012350e55753#128,
    0x4c89902504a440f9d8a5f3261bf904fc#128, 0x28ff876abb2c70d3045e462781e8ed91#128,
    0xdee138126ca49b15e6dab3f6e05ebee6#128, 0x9a533a512a31a34350805f77e0f820ec#128,
    0xafd42d71324c347f4617ae3f3e14fd40#128, 0xeef189ae6da6419998937c848ccde0b2#128,
    0xce682d6097f50100eb721128d6ce8e40#128, 0xea420251cff25be64bb620f9fc062f66#128,
    0xa2b2b83ea261dab40a4d8ffc1395961e#128, 0x3c787eff4f28267220b07f106b73e223#128,
    0x2d037c5f061168cad3a66e7cbf1d0504#128, 0x6d52252a7f80effdc56b4097fe64db20#128,
    0x08a8c70303a6ad2f000e500004d806b0#128, 0x14c06d8d74bdf2d864deb62290503d7c#128,
    0xe3fd7f5678795548d399e6a9c5e29cc5#128]

theorem gfMul_subfieldPowBV :
    gf2_128SubfieldPowBV 0 = 1 ∧ ∀ m : Fin 30,
      gfMul (gf2_128SubfieldPowBV m.castSucc) gf2_128SubfieldGenBV = gf2_128SubfieldPowBV m.succ := by
  have h : ∀ m : Fin 30, gf2_128Exec.mul (gf2_128Exec.ofBits (gf2_128SubfieldPowBV m.castSucc).toNat)
      (gf2_128Exec.ofBits gf2_128SubfieldGenBV.toNat) =
        gf2_128Exec.ofBits (gf2_128SubfieldPowBV m.succ).toNat := by
    decide +kernel
  exact ⟨rfl, fun m => gfMul_eq_of_spread (h m)⟩

theorem gf2_128OfBitVec_subfieldPowBV (m : Fin 31) :
    gf2_128OfBitVec (gf2_128SubfieldPowBV m) = gf2_128SubfieldGen ^ (m : ℕ) := by
  induction m using Fin.induction with
  | zero => rw [gfMul_subfieldPowBV.1, gf2_128OfBitVec_one, Fin.val_zero, pow_zero]
  | succ m ih =>
    rw [← gfMul_subfieldPowBV.2, gf2_128OfBitVec_gfMul, ih, gf2_128OfBitVec_subfieldGenBV,
      Fin.val_succ, Fin.val_castSucc, pow_succ]

/-- Bit `m` is `Tr(g ^ m)`, for `m < 31`. -/
def gf2_128TraceBits : ℕ := 0x7e6deb96

/-- `traceBV_subfieldPowBV` for `m < 8`. The certificate is four kernel checks of eight exponents
each, in the spread representation `gf2_128Exec` (`traceBV_eq_of_spread`); the split bounds the
memory each check holds. -/
theorem traceBV_subfieldPowBV_lt_8 : ∀ m : Fin 31, (m : ℕ) < 8 →
    traceBV (gf2_128SubfieldPowBV m) = if gf2_128TraceBits.testBit m then 1 else 0 := by
  have h : ∀ m : Fin 31, (m : ℕ) < 8 →
      gf2_128Exec.trace 1 16 (gf2_128Exec.ofBits (gf2_128SubfieldPowBV m).toNat) =
        gf2_128Exec.ofBits (if gf2_128TraceBits.testBit m then (1 : BitVec 128) else 0).toNat := by
    decide +kernel
  exact fun m h0 => traceBV_eq_of_spread (h m h0)

/-- `traceBV_subfieldPowBV` for `8 ≤ m < 16`. -/
theorem traceBV_subfieldPowBV_lt_16 : ∀ m : Fin 31, 8 ≤ (m : ℕ) → (m : ℕ) < 16 →
    traceBV (gf2_128SubfieldPowBV m) = if gf2_128TraceBits.testBit m then 1 else 0 := by
  have h : ∀ m : Fin 31, 8 ≤ (m : ℕ) → (m : ℕ) < 16 →
      gf2_128Exec.trace 1 16 (gf2_128Exec.ofBits (gf2_128SubfieldPowBV m).toNat) =
        gf2_128Exec.ofBits (if gf2_128TraceBits.testBit m then (1 : BitVec 128) else 0).toNat := by
    decide +kernel
  exact fun m h0 h1 => traceBV_eq_of_spread (h m h0 h1)

/-- `traceBV_subfieldPowBV` for `16 ≤ m < 24`. -/
theorem traceBV_subfieldPowBV_lt_24 : ∀ m : Fin 31, 16 ≤ (m : ℕ) → (m : ℕ) < 24 →
    traceBV (gf2_128SubfieldPowBV m) = if gf2_128TraceBits.testBit m then 1 else 0 := by
  have h : ∀ m : Fin 31, 16 ≤ (m : ℕ) → (m : ℕ) < 24 →
      gf2_128Exec.trace 1 16 (gf2_128Exec.ofBits (gf2_128SubfieldPowBV m).toNat) =
        gf2_128Exec.ofBits (if gf2_128TraceBits.testBit m then (1 : BitVec 128) else 0).toNat := by
    decide +kernel
  exact fun m h0 h1 => traceBV_eq_of_spread (h m h0 h1)

/-- `traceBV_subfieldPowBV` for `24 ≤ m`. -/
theorem traceBV_subfieldPowBV_ge_24 : ∀ m : Fin 31, 24 ≤ (m : ℕ) →
    traceBV (gf2_128SubfieldPowBV m) = if gf2_128TraceBits.testBit m then 1 else 0 := by
  have h : ∀ m : Fin 31, 24 ≤ (m : ℕ) →
      gf2_128Exec.trace 1 16 (gf2_128Exec.ofBits (gf2_128SubfieldPowBV m).toNat) =
        gf2_128Exec.ofBits (if gf2_128TraceBits.testBit m then (1 : BitVec 128) else 0).toNat := by
    decide +kernel
  exact fun m h0 => traceBV_eq_of_spread (h m h0)

theorem traceBV_subfieldPowBV : ∀ m : Fin 31,
    traceBV (gf2_128SubfieldPowBV m) = if gf2_128TraceBits.testBit m then 1 else 0 := by
  intro m
  rcases Nat.lt_or_ge (m : ℕ) 8 with h8 | h8
  · exact traceBV_subfieldPowBV_lt_8 m h8
  rcases Nat.lt_or_ge (m : ℕ) 16 with h16 | h16
  · exact traceBV_subfieldPowBV_lt_16 m h8 h16
  rcases Nat.lt_or_ge (m : ℕ) 24 with h24 | h24
  · exact traceBV_subfieldPowBV_lt_24 m h16 h24
  · exact traceBV_subfieldPowBV_ge_24 m h24

/-! ## The dual basis -/

/-- Row `i` of the inverse of the trace matrix `Tr(β_i β_j)` over `GF(2)`,
bit `k` the coefficient of `β_k` in `β*_i`. -/
def gf2_128DualCoeff : Fin 16 → ℕ :=
  ![0x3a91, 0xc090, 0x6048, 0x3024, 0x2283, 0xf608, 0x7b04, 0x0713, 0xe4c0, 0x48f1, 0xf9a0,
    0x4641, 0xc469, 0x857d, 0x9f66, 0x7522]

/-- The trace-dual basis `β*` of `gf2_128SubfieldBasis`, as bits. -/
def gf2_128DualBV : Fin 16 → BitVec 128 :=
  ![0x976d65d01158ec6f80269cc2be7bd9e1#128, 0xf329dbe6806687b8c771705b33c6b5f6#128,
    0x31a8537dadcd47a3aa3559ee05062d75#128, 0xa7ad500358ce01abed64e8d7ec36debe#128,
    0xbbd85f97cc45a9593efc72d1347170cb#128, 0x01ec771ab8257e809a04735e03130b59#128,
    0x608d926fcb16914c4e98dd1524b7b73d#128, 0xbe4a82077d300debd39e9ab135b878f5#128,
    0x7cca3482712b624306ac1e8beb5c9c32#128, 0x92a20982a36300387404408e7f06c84b#128,
    0x9607f8b23d6eb4932cd5a07eac36c6ee#128, 0x839fa1244b53454a7f547378398761e6#128,
    0x015e8ac54357b72b61110fb61b7558d2#128, 0xbf52a2c49f6eb10a4ac9b79dbc226ead#128,
    0x5d6647206c6dc058ab7a6af026a0c17f#128, 0x48d02ccbf6c632ca6c6931c500560af1#128]

theorem dualBV_eq_xorSum : ∀ i : Fin 16, gf2_128DualBV i = xorSum 16 fun k =>
    if (gf2_128DualCoeff i).testBit k then gf2_128SubfieldPowBV (k.castLE (by omega)) else 0 := by
  decide +kernel

/-- `∑_k C_ik Tr(β_k β_j) = δ_ij`, with `Tr(β_k β_j) = Tr(g ^ (k + j))`. -/
theorem dualCoeff_trace : ∀ i j : Fin 16, (xorSum 16 fun k =>
    if (gf2_128DualCoeff i).testBit k && gf2_128TraceBits.testBit (k + j : ℕ) then 1 else 0) =
      if i = j then 1 else 0 := by
  decide +kernel

theorem gf2_128SubfieldBasis_eq_ofBitVec (k : Fin 16) :
    gf2_128SubfieldBasis k = gf2_128OfBitVec (gf2_128SubfieldPowBV (k.castLE (by omega))) := by
  rw [gf2_128OfBitVec_subfieldPowBV, Fin.val_castLE, gf2_128SubfieldBasis]

/-- The trace-dual basis `β*` of `gf2_128SubfieldBasis` in `GF2_128`. -/
def gf2_128DualBasis (i : Fin 16) : GF2_128 := gf2_128OfBitVec (gf2_128DualBV i)

theorem gf2_128DualBasis_eq_sum (i : Fin 16) :
    gf2_128DualBasis i =
      ∑ k : Fin 16, if (gf2_128DualCoeff i).testBit k then gf2_128SubfieldBasis k else 0 := by
  rw [gf2_128DualBasis, dualBV_eq_xorSum, gf2_128OfBitVec_xorSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gf2_128OfBitVec_ite, gf2_128OfBitVec_zero, gf2_128SubfieldBasis_eq_ofBitVec]

theorem gf2_128DualBasis_mem (i : Fin 16) : gf2_128DualBasis i ∈ gf2_128Subfield := by
  rw [gf2_128DualBasis_eq_sum]
  refine gf2_128Subfield.sum_mem fun k _ => ?_
  split_ifs
  · exact gf2_128Subfield.pow_mem gf2_128SubfieldGen_mem _
  · exact gf2_128Subfield.zero_mem

theorem trace_subfieldBasis_mul (k j : Fin 16) :
    PackedClaim.trace 4 (gf2_128SubfieldBasis k * gf2_128SubfieldBasis j) =
      if gf2_128TraceBits.testBit (k + j : ℕ) then 1 else 0 := by
  have h := traceBV_subfieldPowBV ⟨k + j, by omega⟩
  rw [← gf2_128OfBitVec_injective.eq_iff, gf2_128OfBitVec_traceBV, gf2_128OfBitVec_subfieldPowBV,
    gf2_128OfBitVec_ite, gf2_128OfBitVec_one, gf2_128OfBitVec_zero] at h
  rw [gf2_128SubfieldBasis, gf2_128SubfieldBasis, ← pow_add, h]

theorem trace_gf2_128DualBasis_mul (i j : Fin 16) :
    PackedClaim.trace 4 (gf2_128DualBasis i * gf2_128SubfieldBasis j) = if i = j then 1 else 0 := by
  have h := congrArg gf2_128OfBitVec (dualCoeff_trace i j)
  rw [gf2_128OfBitVec_xorSum, gf2_128OfBitVec_ite, gf2_128OfBitVec_one, gf2_128OfBitVec_zero] at h
  rw [← h, gf2_128DualBasis_eq_sum, Finset.sum_mul, packedTrace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gf2_128OfBitVec_ite, gf2_128OfBitVec_one, gf2_128OfBitVec_zero]
  by_cases hc : (gf2_128DualCoeff i).testBit k
  · simp only [hc, ite_true, Bool.true_and, trace_subfieldBasis_mul]
  · simp only [hc, Bool.false_eq_true, ite_false, zero_mul, Bool.false_and, packedTrace_zero]

/-- The packing data of the flagship `GF(2¹²⁸)`: the sixteen-bit subfield, the
basis `β i = g ^ i` (`beta_`, `lib/gf2k/gf2_128.h:125-129`) and its trace-dual
basis, which gives the decode `bit_i(p) = Tr(β*_i · p)`. -/
def gf2_128PackedBasis : PackedClaim.PackedBasis GF2_128 4 where
  E := gf2_128Subfield
  fixed _ hx := mem_gf2_128Subfield.mp hx
  β := gf2_128SubfieldBasis
  β_mem _ := gf2_128Subfield.pow_mem gf2_128SubfieldGen_mem _
  βdual := gf2_128DualBasis
  βdual_mem := gf2_128DualBasis_mem
  dual := trace_gf2_128DualBasis_mul

/-- The selection subfield is the packing subfield. -/
theorem gf2_128SelectionField_E_le : gf2_128SelectionField.E ≤ gf2_128PackedBasis.E :=
  le_rfl

end GordieHowe
