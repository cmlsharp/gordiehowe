-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldPacking
public import GordieHowe.ProofSystem.GKR.ConcreteNodes
public import GordieHowe.ProofSystem.Zerocheck.ZeroOneTwoNodes
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.AlgebraField
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.AlgebraField
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.Interp
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.Interp
public import GordieHowe.Applications.FieldInterps.Basic
public import GordieHowe.Applications.FieldInterps.GF256
public import GordieHowe.Applications.FieldInterps.Fq20
public import GordieHowe.Foundations.Algebra.RelativePackingBijective
public import GordieHowe.Foundations.Fields.GF2_128Tower
public import GordieHowe.Foundations.Fields.GF2_256Tower
public import GordieHowe.Applications.Shared.TableauFq20
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Params

@[expose] public section

/-!
# GordieHowe: the packing facts of the field interpretations

The packing facts (`FieldInterp.Packing`) of the field interpretations, each proved once for its
field by computation and registered as the field's instance of the class:

* **`F_q^6`** (`fq6Packing`, `q = 8380417`): the edge `F_q <6 F_q^6` with subfield masks over
  `S0 = F_q` in the basis `mldsaNativeRelativeBasis`; the node `GF(p^1)` of degree `1`, every other
  name the field; the casts of the naturals below `q` as evaluation points; the integer skip
  domains; no bit coordinates.
* **`GF(2^128)`** (`gf128Packing`): the bit edge `GF(2) <16 GF(2^16)` with squaring-chain masks in
  the packing basis `gf2_128PackedBasis`, the inner edge `GF(2^16) <4 GF(2^64)` in the basis
  `gf2_128InnerStageBasis` and the root edge `GF(2^64) <2 GF(2^128)` in the basis
  `gf2_128RootBasis`, both with subfield masks over `S0 = GF(2^16)` in the basis
  `gf2_128RelativeBasis`; the nodes `bit` (degree `1`) and `GF(2^16)` (degree `16`), no degree for
  `GF(2^64)` (the field interpretation's node of that name is the whole field, and no cell lives
  there), every other name the field; the `of_scalar` points of the packing basis; the C++ skip
  domain of width `16` at degree `2`; a word's bit coordinates its decoded bits.
* **`GF(2^256)`** (`gf256Packing`): the same tree `GF(2) <16 GF(2^16) <4 GF(2^64) <4 GF(2^256)` in
  the bases `gf2_256PackedBasis`, `gf2_256InnerStageBasis` and `gf2_256RootBasis`, masks over
  `S0 = GF(2^16)` in the basis `gf2_256RelativeBasis`, and the same nodes, points, skip domain and
  bit coordinates.
-/

namespace GordieHowe.RealizedProgram

open Export PackingStage RelativePacking PEdge

/-! ## `F_q^6` -/

section Fq6

open MLDSA44.Native.ROMParams.HashField

/-- `F_q^6` is `F_{q^6}`. -/
theorem fq6_top : fixedField MLDSANativeField6 8380417 6 = ⊤ := by
  ext x
  simp only [Subfield.mem_top, iff_true]
  rw [mem_fixedField_iff_pow]
  have := RelFrobeniusOrder.pow_eq (K := MLDSANativeField6) (p := 8380417) (m := 1) (D := 6) x
  simpa using this

instance : Fintype (fixedField MLDSANativeField6 8380417 1) :=
  @Subtype.fintype _ _ (fun x => decidableMemFixedField x) _

/-- **The edge `F_q <6 F_q^6`** with subfield masks over `F_q`. -/
def fq6Edge :
    EdgeKit MLDSANativeField6 8380417 (fixedField MLDSANativeField6 8380417 1) 1 6 where
  e := 6
  basis := mldsaNativeRelativeBasis.toStageBasis
  top_eq := by rw [one_mul, fq6_top]; rfl
  masks := MaskKit.subfield mldsaNativeRelativeBasis.β le_rfl (packSub_bijective _)

/-- **The edges of `F_q^6`**: `F_q <6 F_q^6` with subfield masks. -/
def fq6Edges (m d : ℕ) (mode : PackingMode) :
    Option (EdgeKit MLDSANativeField6 8380417 (fixedField MLDSANativeField6 8380417 1) m d) :=
  if h : m = 1 ∧ d = 6 ∧ mode = .subfieldMasks then
    some (cast (by rw [h.1, h.2.1]) fq6Edge)
  else none

/-- **The node degrees of `F_q^6`**: `GF(p^1)` is `F_q`, every other name the field. -/
def fq6NodeDeg (s : String) : Option ℕ := if s = "GF(p^1)" then some 1 else some 6

theorem fq6_node_eq (s : String) (m : ℕ) (h : fq6NodeDeg s = some m) :
    ((fq6Node s : AddSubgroup MLDSANativeField6) : Set MLDSANativeField6) =
      fixedField MLDSANativeField6 8380417 m := by
  unfold fq6Node
  unfold fq6NodeDeg at h
  split_ifs at h ⊢ with hs
  · cases h
    rfl
  · cases h
    rw [fq6_top]
    rfl

/-- **The skip domains of `F_q^6`**: the integers below `q`. -/
def fq6Skip (w D : ℕ) : Option (Sumcheck.FieldSkip.SkipPoints MLDSANativeField6 w D) :=
  if h : w + (D - 1) * (w - 1) ≤ 8380417 then
    some (Sumcheck.FieldSkip.SkipPoints.integers 8380417 h) else none

/-- **The packing facts of `F_q^6`** (see the module docstring). -/
def fq6Packing : fq6.Packing where
  p := 8380417
  expChar := inferInstanceAs (ExpChar MLDSANativeField6 8380417)
  n := 6
  top_eq := fq6_top
  s0 := 1
  decS0 := fun x => decidableMemFixedField (K := MLDSANativeField6) x
  edge := fq6Edges
  nodeDeg := fq6NodeDeg
  node_eq := fq6_node_eq
  q := 8380417
  points := Ligero.Relative.Shape.natPoints MLDSANativeField6 8380417
  points_mem _ := natCast_mem (fixedField MLDSANativeField6 8380417 1) _
  coord_eq _ m dd mode EB h _ hmode := by
    subst hmode
    change fq6Edges m dd .squaringChain = some EB at h
    simp [fq6Edges] at h
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl
  skip := fq6Skip
  nodes := some (Sumcheck.Nodes.zeroOneTwo (F := MLDSANativeField6) 8380417 (by norm_num))

end Fq6

/-! ## `GF(2^128)` -/

section GF128

/-- `GF(2^128)` is `F_{2^128}`. -/
theorem gf128_top : fixedField GF2_128 2 128 = ⊤ := by
  ext x
  simp only [Subfield.mem_top, iff_true]
  rw [mem_fixedField_iff_pow]
  exact FrobeniusOrder.pow_eq x

instance : Fintype (fixedField GF2_128 2 16) :=
  @Subtype.fintype _ _ (fun x => decidableMemFixedField x) _

/-- **The bit edge `GF(2) <16 GF(2^16)`** with squaring-chain masks. -/
def gf128BitEdge : EdgeKit GF2_128 2 (fixedField GF2_128 2 16) 1 16 where
  e := 128
  order := RelFrobeniusOrder.of_frobeniusOrder (by norm_num) (by norm_num)
  basis := gf2_128PackedBasis.toStageBasis
  top_eq := rfl
  masks := MaskKit.bitChain

/-- **The inner edge `GF(2^16) <4 GF(2^64)`** with subfield masks over `GF(2^16)`. -/
def gf128InnerEdge : EdgeKit GF2_128 2 (fixedField GF2_128 2 16) 16 4 where
  e := 8
  basis := gf2_128InnerStageBasis
  top_eq := gf2_128InnerStageBasis_top
  masks := MaskKit.subfield gf2_128RelativeBasis.β le_rfl (packSub_bijective _)

/-- **The root edge `GF(2^64) <2 GF(2^128)`** with subfield masks over `GF(2^16)`. -/
def gf128RootEdge : EdgeKit GF2_128 2 (fixedField GF2_128 2 16) 64 2 where
  e := 2
  basis := gf2_128RootBasis.toStageBasis
  top_eq := by rw [show 64 * 2 = 128 from rfl, gf128_top]; rfl
  masks := MaskKit.subfield gf2_128RelativeBasis.β (fixedField_le_mul 16 4) (packSub_bijective _)

/-- **The edges of `GF(2^128)`**: the bit edge, the inner edge and the root edge. -/
def gf128Edges (m d : ℕ) (mode : PackingMode) :
    Option (EdgeKit GF2_128 2 (fixedField GF2_128 2 16) m d) :=
  if h : m = 1 ∧ d = 16 ∧ mode = .squaringChain then
    some (cast (by rw [h.1, h.2.1]) gf128BitEdge)
  else if h : m = 16 ∧ d = 4 ∧ mode = .subfieldMasks then
    some (cast (by rw [h.1, h.2.1]) gf128InnerEdge)
  else if h : m = 64 ∧ d = 2 ∧ mode = .subfieldMasks then
    some (cast (by rw [h.1, h.2.1]) gf128RootEdge)
  else none

/-- **The node degrees of `GF(2^128)`**: `GF(2^16)`, `bit`, none for `GF(2^64)` (`gf2Node` reads
it as the whole field), every other name the field. -/
def gf128NodeDeg (s : String) : Option ℕ :=
  if s = "GF(2^16)" then some 16 else if s = "bit" then some 1
  else if s = "GF(2^64)" then none else some 128

theorem gf128_node_eq (s : String) (m : ℕ) (h : gf128NodeDeg s = some m) :
    ((gf2Node s : AddSubgroup GF2_128) : Set GF2_128) = fixedField GF2_128 2 m := by
  unfold gf2Node
  unfold gf128NodeDeg at h
  split_ifs at h ⊢ with h1 h2 h3
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rw [gf128_top]
    rfl

/-- **A word's bit coordinates are its coordinates in the bit stage** (`coord_zero_of_mem`,
`PackedClaim.decode_bool`). -/
theorem gf128_coord_eq (s : String) {m dd : ℕ} (mode : PackingMode)
    (EB : EdgeKit GF2_128 2 (fixedField GF2_128 2 16) m dd) (h : gf128Edges m dd mode = some EB)
    (hm : m = 1) (hmode : mode = .squaringChain) (hs : gf128NodeDeg s = some dd) (x : GF2_128)
    (hx : x ∈ fixedField GF2_128 2 dd) (j : Fin dd) :
    gf2BitVal (gf2Coord s x j) = EB.basis.coord x j := by
  subst hm hmode
  by_cases h16 : dd = 16
  · subst h16
    simp only [gf128Edges, and_self, ↓reduceDIte, Option.some.injEq] at h
    subst h
    have hs16 : s = "GF(2^16)" := by
      by_contra hne
      unfold gf128NodeDeg at hs
      rw [if_neg hne] at hs
      split_ifs at hs
      · cases hs
      · cases hs
    subst hs16
    rw [cast_eq]
    change gf2BitVal (gf2Coord "GF(2^16)" x j) =
      (gf2_128PackedBasis.toStageBasis : StageBasis GF2_128 2 1 (2 ^ 4)).coord x j
    rw [coord_toStageBasis]
    simp only [gf2Coord, ite_true,
      coord_zero_of_mem gf2_128RelativeBasis gf2_128RelativeBasis_zero hx, Nat.mod_eq_of_lt j.isLt]
    exact gf2BitVal_decide_eq_one (PackedClaim.decode_bool _ hx _)
  · simp [gf128Edges, h16] at h

/-- **The skip domain of `GF(2^128)`**: the C++ skip domain of width `16` at degree `2`. -/
def gf128Skip (w D : ℕ) : Option (Sumcheck.FieldSkip.SkipPoints GF2_128 w D) :=
  if h : w = 16 ∧ D = 2 then some (cast (by rw [h.1, h.2]) gf2_128SkipDomain.toPoints) else none

/-- **The evaluation points of `GF(2^128)`**: the `of_scalar` points of the packing basis. -/
def gf128Points : Ligero.Relative.Shape.Points GF2_128 (2 ^ 2 ^ 4) :=
  Ligero.Relative.Shape.scalarPoints gf2_128PackedBasis

theorem gf128_points_mem (a : ℕ) : gf128Points.pt a ∈ fixedField GF2_128 2 16 :=
  PackedClaim.ofScalar_mem gf2_128PackedBasis _

/-- **The packing facts of `GF(2^128)`** (see the module docstring). -/
def gf128Packing : gf128.Packing where
  p := 2
  expChar := inferInstanceAs (ExpChar GF2_128 2)
  n := 128
  top_eq := gf128_top
  s0 := 16
  decS0 := fun x => decidableMemFixedField (K := GF2_128) x
  edge := gf128Edges
  nodeDeg := gf128NodeDeg
  node_eq := gf128_node_eq
  q := 2 ^ 2 ^ 4
  points := gf128Points
  points_mem := gf128_points_mem
  coord_eq := gf128_coord_eq
  bitsAdditive := gf128_bitsAdditive
  skip := gf128Skip
  nodes := some GKR.ConcreteNodes.gf2_128Nodes

end GF128

/-! ## Odd fields with a prime node -/

section Odd

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} [ExpChar K p]

/-- **A field of relative Frobenius order `n` over `F_p` is `F_{p^n}`.** -/
theorem fixedField_top_of_rel {n : ℕ} [RelFrobeniusOrder K p 1 n] : fixedField K p n = ⊤ := by
  ext x
  simp only [Subfield.mem_top, iff_true]
  rw [mem_fixedField_iff_pow]
  have := RelFrobeniusOrder.pow_eq (K := K) (p := p) (m := 1) (D := n) x
  simpa using this

/-- `F_p` lies in every `F_{p^m}`. -/
theorem fixedField_one_le_of (m : ℕ) : fixedField K p 1 ≤ fixedField K p m := fun x hx => by
  rw [mem_fixedField_iff_pow]
  have := phi_of_mem hx m
  rwa [phi_def, one_mul] at this

/-- **The node degrees of a field with the prime node `GF(p^1)`**: `GF(p^1)` of degree `1`, every
other name the field. -/
def primeNodeDeg (n : ℕ) (s : String) : Option ℕ := if s = "GF(p^1)" then some 1 else some n

theorem primeNode_eq {n : ℕ} (htop : fixedField K p n = ⊤) (s : String) (m : ℕ)
    (h : primeNodeDeg n s = some m) :
    (((if s = "GF(p^1)" then (fixedField K p 1).toSubring.toAddSubgroup else ⊤ :
      AddSubgroup K)) : Set K) = fixedField K p m := by
  unfold primeNodeDeg at h
  split_ifs at h ⊢ with hs
  · cases h
    rfl
  · cases h
    rw [htop]
    rfl

/-- **The edge `F_p <n K`** with subfield masks over `F_p` in the basis `B`. -/
def primeEdge {n : ℕ} [RelFrobeniusOrder K p 1 n] [Fintype (fixedField K p 1)]
    (B : RelativeBasis K p 1 n) : EdgeKit K p (fixedField K p 1) 1 n where
  e := n
  basis := B.toStageBasis
  top_eq := by rw [one_mul, fixedField_top_of_rel]; rfl
  masks := MaskKit.subfield B.β le_rfl (packSub_bijective _)

/-- **The edges of a field with one edge `F_p <n K`.** -/
def primeEdges {n : ℕ} [RelFrobeniusOrder K p 1 n] [Fintype (fixedField K p 1)]
    (B : RelativeBasis K p 1 n) (m d : ℕ) (mode : PackingMode) :
    Option (EdgeKit K p (fixedField K p 1) m d) :=
  if h : m = 1 ∧ d = n ∧ mode = .subfieldMasks then some (cast (by rw [h.1, h.2.1]) (primeEdge B))
  else none

/-- **The integer skip domains** of a field of characteristic `q`. -/
def integerSkip (q : ℕ) [CharP K q] (w D : ℕ) : Option (Sumcheck.FieldSkip.SkipPoints K w D) :=
  if h : w + (D - 1) * (w - 1) ≤ q then some (Sumcheck.FieldSkip.SkipPoints.integers q h) else none

end Odd

/-! ## `F_q^9`, `F_q^11`, Goldilocks² and Goldilocks⁴ -/

instance : Fintype (fixedField FalconNativeField9 12289 1) :=
  @Subtype.fintype _ _ (fun x => decidableMemFixedField x) _

/-- **The packing facts of `F_q^9`** (`q = 12289`): the edge `F_q <9 F_q^9` in the basis
`falconNativeRelativeBasis`, the node `GF(p^1)`, the casts of the naturals as points, the integer
skip domains. -/
def fq9Packing : fq9.Packing where
  p := 12289
  expChar := inferInstanceAs (ExpChar FalconNativeField9 12289)
  n := 9
  top_eq := fixedField_top_of_rel (K := FalconNativeField9)
  s0 := 1
  decS0 := fun x => decidableMemFixedField (K := FalconNativeField9) x
  edge := primeEdges (K := FalconNativeField9) falconNativeRelativeBasis
  nodeDeg := primeNodeDeg 9
  node_eq s m h := primeNode_eq (K := FalconNativeField9) fixedField_top_of_rel s m h
  q := 12289
  points := Ligero.Relative.Shape.natPoints FalconNativeField9 12289
  points_mem _ := natCast_mem (fixedField FalconNativeField9 12289 1) _
  coord_eq _ m dd mode EB h _ hmode := by
    subst hmode
    change primeEdges (K := FalconNativeField9) falconNativeRelativeBasis m dd .squaringChain = some EB at h
    simp [primeEdges] at h
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl
  skip := integerSkip (K := FalconNativeField9) 12289
  nodes := some (Sumcheck.Nodes.zeroOneTwo (F := FalconNativeField9) 12289 (by norm_num))

instance : Fintype (fixedField MLDSANativeField11 8380417 1) :=
  @Subtype.fintype _ _ (fun x => decidableMemFixedField x) _

/-- **The packing facts of `F_q^11`** (`q = 8380417`): the edge `F_q <11 F_q^11` in the basis
`mldsa11RelativeBasis`, the node `GF(p^1)`, the casts of the naturals as points, the integer skip
domains. -/
def fq11Packing : RealizedProgram.fq11.Packing where
  p := 8380417
  expChar := inferInstanceAs (ExpChar MLDSANativeField11 8380417)
  n := 11
  top_eq := fixedField_top_of_rel (K := MLDSANativeField11)
  s0 := 1
  decS0 := fun x => decidableMemFixedField (K := MLDSANativeField11) x
  edge := primeEdges (K := MLDSANativeField11) mldsa11RelativeBasis
  nodeDeg := primeNodeDeg 11
  node_eq s m h := primeNode_eq (K := MLDSANativeField11) fixedField_top_of_rel s m h
  q := 8380417
  points := Ligero.Relative.Shape.natPoints MLDSANativeField11 8380417
  points_mem _ := natCast_mem (fixedField MLDSANativeField11 8380417 1) _
  coord_eq _ m dd mode EB h _ hmode := by
    subst hmode
    change primeEdges (K := MLDSANativeField11) mldsa11RelativeBasis m dd .squaringChain = some EB at h
    simp [primeEdges] at h
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl
  skip := integerSkip (K := MLDSANativeField11) 8380417
  nodes := some (Sumcheck.Nodes.zeroOneTwo (F := MLDSANativeField11) 8380417 (by norm_num))

instance : Fintype (fixedField GoldilocksExt2 pGold 1) :=
  @Subtype.fintype _ _ (fun x => decidableMemFixedField x) _

/-- **The packing facts of Goldilocks²**: the edge `F_p <2 F_p^2` in the basis
`goldilocksExt2RelativeBasis`, the node `GF(p^1)`, the normalized C++ Reed–Solomon points
(`goldPoints`), the integer skip domains. -/
def gold2Packing : RealizedProgram.gold2.Packing where
  p := pGold
  expChar := inferInstanceAs (ExpChar GoldilocksExt2 pGold)
  n := 2
  top_eq := fixedField_top_of_rel (K := GoldilocksExt2)
  s0 := 1
  decS0 := fun x => decidableMemFixedField (K := GoldilocksExt2) x
  edge := primeEdges (K := GoldilocksExt2) goldilocksExt2RelativeBasis
  nodeDeg := primeNodeDeg 2
  node_eq s m h := primeNode_eq (K := GoldilocksExt2) fixedField_top_of_rel s m h
  q := 2 ^ 32
  points := Ligero.Relative.Shape.goldPoints GoldilocksExt2
  points_mem := Ligero.Relative.Shape.goldPoints_mem (F := GoldilocksExt2)
  coord_eq _ m dd mode EB h _ hmode := by
    subst hmode
    change primeEdges (K := GoldilocksExt2) goldilocksExt2RelativeBasis m dd .squaringChain = some EB at h
    simp [primeEdges] at h
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl
  skip := integerSkip (K := GoldilocksExt2) pGold
  nodes := some (Sumcheck.Nodes.zeroOneTwo (F := GoldilocksExt2) pGold (by norm_num [pGold]))

instance : Fintype (fixedField GoldilocksExt4 pGold 1) :=
  @Subtype.fintype _ _ (fun x => decidableMemFixedField x) _

/-- **The packing facts of Goldilocks⁴**: the edge `F_p <4 F_p^4` in the basis
`goldilocksExt4RelativeBasis`, the node `GF(p^1)`, the normalized C++ Reed–Solomon points
(`goldPoints`), the integer skip domains. -/
def gold4Packing : RealizedProgram.gold4.Packing where
  p := pGold
  expChar := inferInstanceAs (ExpChar GoldilocksExt4 pGold)
  n := 4
  top_eq := fixedField_top_of_rel (K := GoldilocksExt4)
  s0 := 1
  decS0 := fun x => decidableMemFixedField (K := GoldilocksExt4) x
  edge := primeEdges (K := GoldilocksExt4) goldilocksExt4RelativeBasis
  nodeDeg := primeNodeDeg 4
  node_eq s m h := primeNode_eq (K := GoldilocksExt4) fixedField_top_of_rel s m h
  q := 2 ^ 32
  points := Ligero.Relative.Shape.goldPoints GoldilocksExt4
  points_mem := Ligero.Relative.Shape.goldPoints_mem (F := GoldilocksExt4)
  coord_eq _ m dd mode EB h _ hmode := by
    subst hmode
    change primeEdges (K := GoldilocksExt4) goldilocksExt4RelativeBasis m dd .squaringChain = some EB at h
    simp [primeEdges] at h
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl
  skip := integerSkip (K := GoldilocksExt4) pGold
  nodes := some (Sumcheck.Nodes.zeroOneTwo (F := GoldilocksExt4) pGold (by norm_num [pGold]))

/-! ## `F_q^20` -/

instance : Fintype (fixedField FalconNativeField20 12289 1) :=
  @Subtype.fintype _ _ (fun x => decidableMemFixedField x) _

/-- **The inner edge `F_q <4 F_q^4`** of `F_q^20` with subfield masks over `F_q` in the basis
`falcon20RelativeBasis`. -/
def fq20InnerEdge :
    EdgeKit FalconNativeField20 12289 (fixedField FalconNativeField20 12289 1) 1 4 where
  e := 20
  basis := falconInnerStageBasis
  top_eq := by rw [one_mul]; exact falconInnerStageBasis_top
  masks := MaskKit.subfield falcon20RelativeBasis.β le_rfl (packSub_bijective _)

/-- **The root edge `F_q^4 <5 F_q^20`** with subfield masks over `F_q`. -/
def fq20RootEdge :
    EdgeKit FalconNativeField20 12289 (fixedField FalconNativeField20 12289 1) 4 5 where
  e := 5
  basis := falconRootBasis.toStageBasis
  top_eq := by rw [show 4 * 5 = 20 from rfl, fixedField_top_of_rel (K := FalconNativeField20)]; rfl
  masks := MaskKit.subfield falcon20RelativeBasis.β (fixedField_one_le_of 4) (packSub_bijective _)

/-- **The edges of `F_q^20`**: the inner edge and the root edge. -/
def fq20Edges (m d : ℕ) (mode : PackingMode) :
    Option (EdgeKit FalconNativeField20 12289 (fixedField FalconNativeField20 12289 1) m d) :=
  if h : m = 1 ∧ d = 4 ∧ mode = .subfieldMasks then
    some (cast (by rw [h.1, h.2.1]) fq20InnerEdge)
  else if h : m = 4 ∧ d = 5 ∧ mode = .subfieldMasks then
    some (cast (by rw [h.1, h.2.1]) fq20RootEdge)
  else none

/-- **The packing facts of `F_q^20`** (`q = 12289`): the tower `F_q <4 F_q^4 <5 F_q^20`, the node
`GF(p^1)`, the casts of the naturals as points, the integer skip domains. -/
def fq20Packing : fq20.Packing where
  p := 12289
  expChar := inferInstanceAs (ExpChar FalconNativeField20 12289)
  n := 20
  top_eq := fixedField_top_of_rel (K := FalconNativeField20)
  s0 := 1
  decS0 := fun x => decidableMemFixedField (K := FalconNativeField20) x
  edge := fq20Edges
  nodeDeg := primeNodeDeg 20
  node_eq s m h := primeNode_eq (K := FalconNativeField20) fixedField_top_of_rel s m h
  q := 12289
  points := Ligero.Relative.Shape.natPoints FalconNativeField20 12289
  points_mem _ := natCast_mem (fixedField FalconNativeField20 12289 1) _
  coord_eq _ m dd mode EB h _ hmode := by
    subst hmode
    change fq20Edges m dd .squaringChain = some EB at h
    simp [fq20Edges] at h
  bitsAdditive := FieldInterp.bitsAdditive_of_noBits fun _ _ _ => rfl
  skip := integerSkip (K := FalconNativeField20) 12289
  nodes := some (Sumcheck.Nodes.zeroOneTwo (F := FalconNativeField20) 12289 (by norm_num))

/-! ## `GF(2^256)` -/

section GF256

/-- `GF(2^256)` is `F_{2^256}`. -/
theorem gf256_top : fixedField GF2_256 2 256 = ⊤ := by
  ext x
  simp only [Subfield.mem_top, iff_true]
  rw [mem_fixedField_iff_pow]
  exact FrobeniusOrder.pow_eq x

instance : Fintype (fixedField GF2_256 2 16) :=
  @Subtype.fintype _ _ (fun x => decidableMemFixedField x) _

/-- **The bit edge `GF(2) <16 GF(2^16)`** of `GF(2^256)` with squaring-chain masks. -/
def gf256BitEdge : EdgeKit GF2_256 2 (fixedField GF2_256 2 16) 1 16 where
  e := 256
  order := RelFrobeniusOrder.of_frobeniusOrder (by norm_num) (by norm_num)
  basis := gf2_256PackedBasis.toStageBasis
  top_eq := rfl
  masks := MaskKit.bitChain

/-- **The inner edge `GF(2^16) <4 GF(2^64)`** of `GF(2^256)` with subfield masks over
`GF(2^16)`. -/
def gf256InnerEdge : EdgeKit GF2_256 2 (fixedField GF2_256 2 16) 16 4 where
  e := 16
  basis := gf2_256InnerStageBasis
  top_eq := gf2_256InnerStageBasis_top
  masks := MaskKit.subfield gf2_256RelativeBasis.β le_rfl (packSub_bijective _)

/-- **The root edge `GF(2^64) <4 GF(2^256)`** with subfield masks over `GF(2^16)`. -/
def gf256RootEdge : EdgeKit GF2_256 2 (fixedField GF2_256 2 16) 64 4 where
  e := 4
  basis := gf2_256RootBasis.toStageBasis
  top_eq := by rw [show 64 * 4 = 256 from rfl, gf256_top]; rfl
  masks := MaskKit.subfield gf2_256RelativeBasis.β (fixedField_le_mul 16 4) (packSub_bijective _)

/-- **The edges of `GF(2^256)`**: the bit edge, the inner edge and the root edge. -/
def gf256Edges (m d : ℕ) (mode : PackingMode) :
    Option (EdgeKit GF2_256 2 (fixedField GF2_256 2 16) m d) :=
  if h : m = 1 ∧ d = 16 ∧ mode = .squaringChain then
    some (cast (by rw [h.1, h.2.1]) gf256BitEdge)
  else if h : m = 16 ∧ d = 4 ∧ mode = .subfieldMasks then
    some (cast (by rw [h.1, h.2.1]) gf256InnerEdge)
  else if h : m = 64 ∧ d = 4 ∧ mode = .subfieldMasks then
    some (cast (by rw [h.1, h.2.1]) gf256RootEdge)
  else none

/-- **The node degrees of `GF(2^256)`**: `GF(2^16)`, `bit`, none for `GF(2^64)` (`gf256Node`
reads it as the whole field), every other name the field. -/
def gf256NodeDeg (s : String) : Option ℕ :=
  if s = "GF(2^16)" then some 16 else if s = "bit" then some 1
  else if s = "GF(2^64)" then none else some 256

theorem gf256_node_eq (s : String) (m : ℕ) (h : gf256NodeDeg s = some m) :
    ((gf256Node s : AddSubgroup GF2_256) : Set GF2_256) = fixedField GF2_256 2 m := by
  unfold gf256Node
  unfold gf256NodeDeg at h
  split_ifs at h ⊢ with h1 h2 h3
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rw [gf256_top]
    rfl

/-- **A word's bit coordinates are its coordinates in the bit stage** (`coord_zero_of_mem`,
`PackedClaim.decode_bool`). -/
theorem gf256_coord_eq (s : String) {m dd : ℕ} (mode : PackingMode)
    (EB : EdgeKit GF2_256 2 (fixedField GF2_256 2 16) m dd) (h : gf256Edges m dd mode = some EB)
    (hm : m = 1) (hmode : mode = .squaringChain) (hs : gf256NodeDeg s = some dd) (x : GF2_256)
    (hx : x ∈ fixedField GF2_256 2 dd) (j : Fin dd) :
    gf256BitVal (gf256Coord s x j) = EB.basis.coord x j := by
  subst hm hmode
  by_cases h16 : dd = 16
  · subst h16
    simp only [gf256Edges, and_self, ↓reduceDIte, Option.some.injEq] at h
    subst h
    have hs16 : s = "GF(2^16)" := by
      by_contra hne
      unfold gf256NodeDeg at hs
      rw [if_neg hne] at hs
      split_ifs at hs
      · cases hs
      · cases hs
    subst hs16
    rw [cast_eq]
    change gf256BitVal (gf256Coord "GF(2^16)" x j) =
      (gf2_256PackedBasis.toStageBasis : StageBasis GF2_256 2 1 (2 ^ 4)).coord x j
    rw [coord_toStageBasis]
    simp only [gf256Coord, ite_true,
      coord_zero_of_mem gf2_256RelativeBasis gf2_256RelativeBasis_zero hx, Nat.mod_eq_of_lt j.isLt]
    exact gf256BitVal_decide_eq_one (PackedClaim.decode_bool _ hx _)
  · simp [gf256Edges, h16] at h

/-- **The skip domain of `GF(2^256)`**: the C++ skip domain of width `16` at degree `2`. -/
def gf256Skip (w D : ℕ) : Option (Sumcheck.FieldSkip.SkipPoints GF2_256 w D) :=
  if h : w = 16 ∧ D = 2 then some (cast (by rw [h.1, h.2]) gf2_256SkipDomain.toPoints) else none

/-- **The evaluation points of `GF(2^256)`**: the `of_scalar` points of the packing basis. -/
def gf256Points : Ligero.Relative.Shape.Points GF2_256 (2 ^ 2 ^ 4) :=
  Ligero.Relative.Shape.scalarPoints gf2_256PackedBasis

theorem gf256_points_mem (a : ℕ) : gf256Points.pt a ∈ fixedField GF2_256 2 16 :=
  PackedClaim.ofScalar_mem gf2_256PackedBasis _

/-- **The packing facts of `GF(2^256)`**: the bit edge `GF(2) <16 GF(2^16)` with squaring-chain
masks in `gf2_256PackedBasis`, the inner edge `GF(2^16) <4 GF(2^64)` in `gf2_256InnerStageBasis`
and the root edge `GF(2^64) <4 GF(2^256)` in `gf2_256RootBasis`, both with subfield masks in
`gf2_256RelativeBasis`, the nodes `bit` and `GF(2^16)`, the `of_scalar` points, the C++ skip
domain, a word's bit coordinates its decoded bits. -/
def gf256Packing : gf256.Packing where
  p := 2
  expChar := inferInstanceAs (ExpChar GF2_256 2)
  n := 256
  top_eq := gf256_top
  s0 := 16
  decS0 := fun x => decidableMemFixedField (K := GF2_256) x
  edge := gf256Edges
  nodeDeg := gf256NodeDeg
  node_eq := gf256_node_eq
  q := 2 ^ 2 ^ 4
  points := gf256Points
  points_mem := gf256_points_mem
  coord_eq := gf256_coord_eq
  bitsAdditive := gf256_bitsAdditive
  skip := gf256Skip
  nodes := some GKR.ConcreteNodes.gf2_256Nodes

end GF256

/-! ## The instances

Each field interpretation is a member of the class `FieldInterp.Packing` by its decided packing
facts. -/

instance : RealizedProgram.fq6.Packing := fq6Packing
instance : gf128.Packing := gf128Packing
instance : fq9.Packing := fq9Packing
instance : RealizedProgram.fq11.Packing := fq11Packing
instance : RealizedProgram.gold2.Packing := gold2Packing
instance : RealizedProgram.gold4.Packing := gold4Packing
instance : fq20.Packing := fq20Packing
instance : gf256.Packing := gf256Packing

/-! ## The Ligero certificates -/

/-- **The tableau of `MLDSA44.Native.ROMParams`'s domain `A`**: `(rate, t, block_enc) = (9, 74, 3376)`,
the mask test at `A = 975` with `17258473` exceptional challenges (`MLDSA44.Native.ROMParams.AlgebraField.aMaskTest`). -/
def mldsaNativeROMACert : LigeroCert where
  Sh := MLDSA44.Native.ROMParams.AlgebraField.aShape
  agree := MLDSA44.Native.ROMParams.AlgebraField.aAgree
  exceptions := MLDSA44.Native.ROMParams.AlgebraField.aExceptions
  line C hk := MLDSA44.Native.ROMParams.AlgebraField.aMaskTest C hk
  masking := .split

/-- **The tableau `(rate, t, block_enc) = (12, 63, 3955)` at two low-degree repetitions**, the
mask test at `A = 982` with `41166706213` exceptional challenges (`Tableau.gf128K282R2MaskTest`). -/
def gf128K282R2Cert : LigeroCert where
  Sh := Tableau.gf128K282R2Shape
  agree := Tableau.gf128K282R2Agree
  exceptions := Tableau.gf128K282R2Exceptions
  line C hk := Tableau.gf128K282R2MaskTest C hk
  masking := .split

/-- **The tableau of `Falcon512.Native.ROMParams`'s domain `A`** at two low-degree repetitions:
`(rate, t, block_enc) = (5, 91, 2369)`, the mask test at `A = 758` with `34023420758` exceptional
challenges (`Falcon512.Ring.Native.Params.aNativeROMMaskTest`). -/
def falconNativeROMACert : LigeroCert where
  Sh := Falcon512.Ring.Native.Params.aNativeROMShape
  agree := Falcon512.Ring.Native.Params.aNativeROMAgree
  exceptions := Falcon512.Ring.Native.Params.aNativeROMExceptions
  line C hk := Falcon512.Ring.Native.Params.aNativeROMMaskTest C hk
  masking := .split

/-- **The tableau of `Falcon512.Ring.Native.ROMParams`'s domain `A`** at two low-degree repetitions:
`(rate, t, block_enc) = (5, 90, 2105)`, the mask test at `A = 673` with `51456804230` exceptional
challenges (`Falcon512.Ring.Native.Params.aRingROMMaskTest`). -/
def falconRingNativeROMACert : LigeroCert where
  Sh := Falcon512.Ring.Native.Params.aRingROMShape
  agree := Falcon512.Ring.Native.Params.aRingROMAgree
  exceptions := Falcon512.Ring.Native.Params.aRingROMExceptions
  line C hk := Falcon512.Ring.Native.Params.aRingROMMaskTest C hk
  masking := .split

/-- **The `F_q^20` tableau at the QROM parameters** `(rate, t, block_enc) = (12, 127, 3799)` of
domain `A` of `Falcon512.Native.QROMParams` and `Falcon512.Ring.Native.QROMParams`, the mask test at `A = 944` with `23020764629`
exceptional challenges (`Tableau.fq20K271MaskTest`). -/
def fq20K271Cert : LigeroCert where
  Sh := Tableau.fq20K271Shape
  agree := Tableau.fq20K271Agree
  exceptions := Tableau.fq20K271Exceptions
  line C hk := Tableau.fq20K271MaskTest C hk
  masking := .split

/-- **The tableau of `MLDSA44.Native.QROMParams`'s domain `A`**: `(rate, t, block_enc) = (9, 144, 4274)`
at two low-degree repetitions, the mask test at `A = 1169` with `74189372805` exceptional challenges
(`MLDSA44.Native.QROMParams.AlgebraField.aMaskTest`). -/
def mldsaNativeQROMACert : LigeroCert where
  Sh := MLDSA44.Native.QROMParams.AlgebraField.aShape
  agree := MLDSA44.Native.QROMParams.AlgebraField.aAgree
  exceptions := MLDSA44.Native.QROMParams.AlgebraField.aExceptions
  line C hk := MLDSA44.Native.QROMParams.AlgebraField.aMaskTest C hk
  masking := .split

/-- **The Goldilocks⁴ tableau** `(6, 201, 4095)`. -/
def gold4K512Cert : LigeroCert where
  Sh := Tableau.gold4K512Shape
  agree := Tableau.gold4K512Agree
  exceptions := Tableau.gold4K512Exceptions
  line C hk := Tableau.gold4K512MaskTest C hk
  masking := .split

/-- **The Goldilocks² tableau** `(5, 97, 3583)` at two low-degree repetitions. -/
def gold2K512R2Cert : LigeroCert where
  Sh := Tableau.gold2K512R2Shape
  agree := Tableau.gold2K512R2Agree
  exceptions := Tableau.gold2K512R2Exceptions
  line C hk := Tableau.gold2K512R2MaskTest C hk
  masking := .split

/-- **The Goldilocks⁴ tableau** `(6, 175, 4095)` at two low-degree repetitions. -/
def gold4K512R2Cert : LigeroCert where
  Sh := Tableau.gold4K512R2Shape
  agree := Tableau.gold4K512R2Agree
  exceptions := Tableau.gold4K512R2Exceptions
  line C hk := Tableau.gold4K512R2MaskTest C hk
  masking := .split

/-- **The `GF(2^256)` tableau** `(12, 128, 4746)` at two low-degree repetitions. -/
def gf256K339R2Cert : LigeroCert where
  Sh := Tableau.gf256K339R2Shape
  agree := Tableau.gf256K339R2Agree
  exceptions := Tableau.gf256K339R2Exceptions
  line C hk := Tableau.gf256K339R2MaskTest C hk
  masking := .split

end GordieHowe.RealizedProgram
