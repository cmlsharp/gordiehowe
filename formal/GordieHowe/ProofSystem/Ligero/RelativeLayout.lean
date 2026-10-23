-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.Foundations.Algebra.BitReverse
public import GordieHowe.ProofSystem.Ligero.MaskTest.PiecesHonest

@[expose] public section

/-!
# The Ligero numbers of a C++ layout

The code, message nodes and tableau shape the C++ builds from the three Ligero numbers
`(rate, nreq, block_enc)` of a tableau (`Relative.Shape`, with the arithmetic facts
`Ligero.Relative.Shape.Valid`), which the tree layout (`GordieHowe.Ligero.MaskRow.TreeLayout`) is built on, and
the facts about `Ligero.Layout.Shape` it uses (the embedded placement, the piece rows of the
mask test):

* **Ligero** (`ligero_param.h` lines 154-258): `r` privacy positions, at least as many as the
  opened columns (the C++ takes `r = nreq`, the blinding width equal to the query count), then
  `w = block − r` witness positions per row (the paper's `ℓ` entries per row of `def:tableau`),
  `block = (block_enc + 1)/(2 + rate)`, the code of
  length `block_enc − dblock` at the points `pt (dblock + j)`, `dblock = 2·block − 1` (the opened
  columns `[dblock, block_enc)`), message nodes `pt 0, …, pt (block − 1)` (`code`, `nodes`). The
  point map `pt` is the C++ split-mask evaluation point `Y_i` (`split_points`, at which the mask
  test recombines its pieces), the image of the C++ encoder's point `P_i` under the affine map
  that sends `P_0` and `P_1` to `0` and `1`: the cast of a natural in a native prime field
  (`natPoints`) and the C++ `of_scalar` of a binary field with a subfield basis (`scalarPoints`),
  where `P_0 = 0`, `P_1 = 1` (`of_scalar(1) = beta_[0] = 1`) and `Y_i = P_i`; the normalization
  (`Points.normalize`) of the powers `g ^ bitrev_32(i)` of a primitive `2^32`-th root in a
  Goldilocks extension (`subgroupPoints`).
  An affine change of point with nonzero slope preserves the degree of a polynomial, so the code
  at the points `Y_i` has the codewords and the message encoding of the C++ code at the points
  `P_i`.
-/

namespace GordieHowe

open IOP

/-! ### Finiteness of the GKR pads -/

namespace GKR.LayeredCircuit

variable {F : Type} [Field F] {d : ℕ}

instance (SA : LayeredCircuit F d) : Fintype SA.PadIdx := by
  unfold LayeredCircuit.PadIdx CircuitFlatten.PadIndex
  infer_instance

instance (SA : LayeredCircuit F d) : DecidableEq SA.PadIdx := by
  unfold LayeredCircuit.PadIdx CircuitFlatten.PadIndex
  infer_instance

/-- The pads are encoded as the sigma type `CircuitFlatten.PadIndex`. -/
instance (SA : LayeredCircuit F d) : Encodable SA.PadIdx := by
  unfold LayeredCircuit.PadIdx CircuitFlatten.PadIndex
  infer_instance

end GKR.LayeredCircuit

/-! ### The piece rows of the mask test -/

namespace Ligero.Layout.Shape

variable (S : Shape)

/-- **The six piece rows of the mask test**: the last six data rows, the IDOT pieces `A`, `C`, `B`
then the IQUAD pieces `A`, `C`, `B`. They are free of the placement when the Shape's six extra
rows are its last rows (`pieceRows_free`). -/
def pieceRows : MaskTest.Pieces.PieceRows S.dataRows where
  dot := ⟨⟨S.dataRows - 5, by omega⟩, ⟨S.dataRows - 4, by omega⟩, ⟨S.dataRows - 3, by omega⟩⟩
  quad := ⟨⟨S.dataRows - 2, by omega⟩, ⟨S.dataRows - 1, by omega⟩, ⟨S.dataRows, by omega⟩⟩

/-- Every piece row is among the last six data rows. -/
theorem le_of_mem_pieceRows {row : Fin (S.dataRows + 1)} (h : row ∈ S.pieceRows.toList) :
    S.dataRows - 5 ≤ row.val := by
  simp only [MaskTest.Pieces.PieceRows.toList, pieceRows, List.mem_cons, List.not_mem_nil, or_false]
    at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- A product row precedes the extra rows. -/
theorem products_le (g : Fin S.productGroups) (s : Fin 3) :
    (S.products g s).val ≤ S.witnessRows + 3 * S.productGroups := by
  have hg := g.isLt
  have hs := s.isLt
  have hm : s.val * S.productGroups ≤ 2 * S.productGroups := Nat.mul_le_mul_right _ (by omega)
  change 1 + S.witnessRows + s.val * S.productGroups + g.val ≤ _
  omega

end Ligero.Layout.Shape

/-! ### The Shape placement at an embedding of the coordinates -/

namespace Ligero.Layout.Shape

variable (S : Shape) {F : Type} [Field F] {N : ℕ} (C : GordieHowe.RSCode F N)
  (hk : C.k = S.r + S.w) {ι Q : Type} (pos : ι ↪ Fin S.nw) (productIndex : Q ≃ Fin S.nq)
  (nodes : Fin C.k → F) (hnodes : Function.Injective nodes)

/-- **The Shape placement at an embedding** `pos` of the source coordinates into the Shape's
positions (unused positions stay unoccupied), and an enumeration of the products. -/
def embeddedPlacement :
    Preparation.Placement C (S.parameters C nodes hnodes) ι Q where
  source i := (S.placement C hk nodes hnodes).source (pos i)
  source_nonzero i := (S.placement C hk nodes hnodes).source_nonzero (pos i)
  source_witness i := (S.placement C hk nodes hnodes).source_witness (pos i)
  copyGroup q := (S.placement C hk nodes hnodes).copyGroup (productIndex q)
  copyCol q := (S.placement C hk nodes hnodes).copyCol (productIndex q)
  copy_witness q := (S.placement C hk nodes hnodes).copy_witness (productIndex q)
  product_nonzero q s := (S.placement C hk nodes hnodes).product_nonzero (productIndex q) s

/-- The embedded placement places each coordinate where the Shape placement places its
position. -/
theorem embeddedPlacement_location (z : Routing.Prepared ι Q) :
    (S.embeddedPlacement C hk pos productIndex nodes hnodes).location z =
      (S.placement C hk nodes hnodes).location
        (Sum.map pos (Prod.map productIndex id) z) := by
  cases z <;> rfl

/-- The embedded Shape placement has injective locations, so it has no aliases. -/
theorem embeddedPlacement_aliasesAgree (products : Routing.ProductLayout ι Q) :
    (S.embeddedPlacement C hk pos productIndex nodes hnodes).AliasesAgree products := by
  apply Preparation.Placement.aliasesAgree_of_injective
  intro z z' h
  rw [embeddedPlacement_location, embeddedPlacement_location] at h
  exact (Sum.map_injective.mpr ⟨pos.injective,
    productIndex.injective.prodMap Function.injective_id⟩)
    (ShapeEncoding.placement_location_injective S C hk nodes hnodes h)

/-- Every occupied product-row cell of the embedded Shape placement is in the column of a
copy of that group. -/
theorem embeddedPlacement_productsCovered :
    (S.embeddedPlacement C hk pos productIndex nodes hnodes).ProductsCovered := by
  intro g s j z hz
  rw [embeddedPlacement_location] at hz
  obtain ⟨q, hg, hc⟩ := S.placement_productsCovered C hk nodes hnodes g s j _ hz
  refine ⟨productIndex.symm q, ?_, ?_⟩
  · change (S.placement C hk nodes hnodes).copyGroup (productIndex (productIndex.symm q)) = g
    rw [Equiv.apply_symm_apply]
    exact hg
  · change (S.placement C hk nodes hnodes).copyCol (productIndex (productIndex.symm q)) = j
    rw [Equiv.apply_symm_apply]
    exact hc

/-- A source coordinate in the row of a position below `w` is at a position below `w`. -/
theorem source_row_lt {i j : Fin S.nw} (hj : j.val < S.w)
    (h : (S.source C hk i).1 = (S.source C hk j).1) : i.val < S.w := by
  have hv := congrArg Fin.val h
  change 1 + i.val / S.w = 1 + j.val / S.w at hv
  rw [Nat.div_eq_of_lt hj] at hv
  exact (Nat.div_eq_zero_iff_lt S.width_pos).mp (by omega)

/-- A source coordinate sits in a witness row. -/
theorem source_row_le (i : Fin S.nw) : (S.source C hk i).1.val ≤ S.witnessRows := by
  have h := S.block_lt i.isLt
  change 1 + i.val / S.w ≤ S.witnessRows
  change i.val / S.w < S.witnessRows at h
  omega

/-- **The piece rows are free in the embedded placement** when the Shape has six extra rows: they
are distinct, after row `0`, and after every source and product row. -/
theorem pieceRows_free (h : S.extra = 6) :
    S.pieceRows.Free (S.embeddedPlacement C hk pos productIndex nodes hnodes) := by
  have hd : S.dataRows = S.witnessRows + 3 * S.productGroups + 6 := by
    unfold Shape.dataRows
    rw [h]
  refine ⟨?_, fun h0 => ?_, fun i hi => ?_, fun g s hi => ?_⟩
  · simp only [MaskTest.Pieces.PieceRows.toList, pieceRows, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, Fin.ext_iff,
      not_false_eq_true]
    rw [hd]
    omega
  · have := S.le_of_mem_pieceRows h0
    simp at this
    omega
  · have h1 := S.le_of_mem_pieceRows hi
    have h2 := S.source_row_le C hk (pos i)
    change ((S.placement C hk nodes hnodes).source (pos i)).1.val ≤ _ at h2
    change S.dataRows - 5 ≤ ((S.placement C hk nodes hnodes).source (pos i)).1.val at h1
    omega
  · have h1 := S.le_of_mem_pieceRows hi
    have h2 := S.products_le g s
    change S.dataRows - 5 ≤ (S.products g s).val at h1
    omega

end Ligero.Layout.Shape

/-! ### Casts of naturals below the characteristic -/

/-- Casts of naturals below the characteristic are distinct. -/
theorem natCast_inj_of_lt {F : Type} [AddGroupWithOne F] {q : ℕ} [CharP F q] {a b : ℕ}
    (ha : a < q) (hb : b < q) (h : (a : F) = b) : a = b :=
  ((CharP.natCast_eq_natCast F q).mp h).eq_of_lt_of_lt ha hb

/-! ### The Ligero numbers -/

/-- **The Ligero numbers of a tableau** (`ligero_param.h` lines 154-258): the code rate
`rate`, the query count `nreq` (the number of opened columns), the encoded block length
`block_enc`, the number `nrep` of repetitions of the low-degree test (one unless a configuration
sets it) and the number `r` of privacy positions per row (the C++ blinding width, `nreq` in every
C++ layout). The code dimension `block` and length `N` depend on `rate` and `block_enc` only; `r`
sets the witness capacity `w = block − r` of a row, the paper's `ℓ` entries per row
(`def:tableau`, `r = k − ℓ`). -/
structure Ligero.Relative.Shape where
  rate : ℕ
  nreq : ℕ
  blockEnc : ℕ
  /-- The number of repetitions of the low-degree test. -/
  nrep : ℕ := 1
  /-- The number of privacy positions per row (`k − ℓ`). -/
  r : ℕ := nreq

namespace Ligero.Relative.Shape

variable (Sh : Shape)

/-- The message block: `(block_enc + 1)/(2 + rate)`. -/
def block : ℕ := (Sh.blockEnc + 1) / (2 + Sh.rate)

/-- The witness positions per row: `block − r`, the paper's `ℓ`. -/
def w : ℕ := Sh.block - Sh.r

/-- The first opened column: `2·block − 1`. -/
def dblock : ℕ := 2 * Sh.block - 1

/-- The code length: the opened columns `[dblock, block_enc)`. -/
def N : ℕ := Sh.blockEnc - Sh.dblock

/-- **The arithmetic facts of the layout** at the size `q` of the evaluation domain (the
naturals below `q` on which the points `Points F q` are injective: the characteristic of a prime
field, `2^16` for the binary fields, `2^32` for the Goldilocks subgroup points) and the relative
degree `D`, all parameter conditions discharged by `decide`: the encoded positions `[0, block_enc)`
lie in the domain, at least one query, at most as many queries as privacy positions (`nreq ≤ r`,
the paper's `q ≤ k − ℓ`), fewer privacy positions than `block` (`ℓ ≥ 1`), the masks fit one row
(`D² ≤ w`), the rate condition `2·block < N`, and at most `N` queries. -/
structure Valid (q D : ℕ) : Prop where
  /-- The encoded positions `[0, block_enc)` lie in the point domain. -/
  enc_le_domain : Sh.blockEnc ≤ q
  nreq_pos : 0 < Sh.nreq
  /-- At most as many queries as privacy positions (the paper's `q ≤ k − ℓ`). -/
  nreq_le_r : Sh.nreq ≤ Sh.r
  /-- At least one witness position per row (the paper's `ℓ ≥ 1`). -/
  r_lt_block : Sh.r < Sh.block
  masks_le : D * D ≤ Sh.w
  D_pos : 0 < D
  rate_lt : 2 * Sh.block < Sh.N
  nreq_le_N : Sh.nreq ≤ Sh.N
  /-- The low-degree test has at least one repetition. -/
  nrep_pos : 0 < Sh.nrep

variable {Sh} in
/-- The arithmetic facts from one conjunction, for `decide` at a concrete tableau. -/
theorem Valid.of_and {q D : ℕ}
    (h : Sh.blockEnc ≤ q ∧ 0 < Sh.nreq ∧ Sh.nreq ≤ Sh.r ∧ Sh.r < Sh.block ∧ D * D ≤ Sh.w ∧
      0 < D ∧ 2 * Sh.block < Sh.N ∧ Sh.nreq ≤ Sh.N ∧ 0 < Sh.nrep) : Sh.Valid q D :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

variable {Sh} {q D : ℕ} (hv : Sh.Valid q D)

include hv in
/-- At most `block` privacy positions. -/
theorem Valid.r_le : Sh.r ≤ Sh.block := hv.r_lt_block.le

include hv in
theorem Valid.w_pos : 0 < Sh.w := by
  have := hv.r_lt_block
  unfold w
  omega

include hv in
theorem Valid.block_pos : 0 < Sh.block := lt_of_le_of_lt (Nat.zero_le _) hv.r_lt_block

include hv in
theorem Valid.dblock_add_N : Sh.dblock + Sh.N = Sh.blockEnc := by
  have := hv.rate_lt
  unfold N at *
  omega

/-! ### Evaluation points -/

/-- **The evaluation points of a field**: a map from the naturals below `q` into the field,
injective there. The C++ Reed–Solomon encoder evaluates at `pt 0, pt 1, …`. -/
structure Points (F : Type) (q : ℕ) where
  pt : ℕ → F
  inj : ∀ {a b : ℕ}, a < q → b < q → pt a = pt b → a = b

/-- The points of a field of characteristic `q`: the casts of the naturals. -/
def natPoints (F : Type) [AddGroupWithOne F] (q : ℕ) [CharP F q] : Points F q where
  pt a := a
  inj ha hb h := natCast_inj_of_lt ha hb h

/-- The points of a binary field with a packing basis `P`: `PackedClaim.ofScalar`, the C++
`of_scalar` (`lib/gf2k/gf2_256.h:167-173`), injective below `2^(2^a)`. -/
def scalarPoints {F : Type} [Field F] [CharP F 2] {a : ℕ} (P : PackedClaim.PackedBasis F a) :
    Points F (2 ^ 2 ^ a) where
  pt := PackedClaim.ofScalar P
  inj ha hb h := PackedClaim.ofScalar_inj P ha hb h

/-- **The subgroup points** of a field with a primitive `2^K`-th root of unity `g`: position `i`
is `g ^ bitrev_K(i)`, the C++ `SubgroupReedSolomon` domain (`lib/algebra/subgroup_reed_solomon.h`
lines 28-50), injective below `2^K`. -/
def subgroupPoints {F : Type} [Field F] {g : F} {K : ℕ} (hg : IsPrimitiveRoot g (2 ^ K)) :
    Points F (2 ^ K) where
  pt a := g ^ bitRevNat K a
  inj ha hb h := bitRevNat_injOn ha hb (hg.pow_inj (bitRevNat_lt K _) (bitRevNat_lt K _) h)

/-- **The normalized points** of `P`: `(P.pt i − P.pt 0) / (P.pt 1 − P.pt 0)`, the image of `P`
under the affine map that sends the points of positions `0` and `1` to `0` and `1`. These are the
C++ split-mask evaluation points (`split_points`, `lib/ligero/ligero_param.h` lines 526-538), at
which the verifier recombines the mask pieces. The map is injective below `q` whenever `P` is,
for `1 < q`. -/
def Points.normalize {F : Type} [Field F] {q : ℕ} (P : Points F q) (hq : 1 < q) : Points F q where
  pt a := (P.pt a - P.pt 0) / (P.pt 1 - P.pt 0)
  inj ha hb h := by
    have hne : P.pt 1 - P.pt 0 ≠ 0 :=
      sub_ne_zero.mpr fun h10 => absurd (P.inj hq (by omega) h10) one_ne_zero
    exact P.inj ha hb (sub_left_injective ((div_left_inj' hne).mp h))

variable {F : Type} [Field F] (P : Points F q)

/-- **The code of the tableau**: length `block_enc − dblock` at the points `pt (dblock + j)`,
message length `block`, the unique-decoding radius. -/
def code : GordieHowe.RSCode F Sh.N where
  D j := P.pt (Sh.dblock + j)
  D_injective i j h := by
    have hi := i.isLt
    have hj := j.isLt
    have := hv.dblock_add_N
    have := hv.enc_le_domain
    exact Fin.ext (by
      have := P.inj (by omega) (by omega) h
      omega)
  k := Sh.block
  e := (Sh.N - Sh.block) / 2
  k_pos := hv.block_pos
  radius := by have := hv.rate_lt; omega

/-- The message nodes `pt 0, …, pt (block − 1)`. -/
def nodes : Fin (code hv P).k → F := fun j => P.pt j

theorem nodes_injective : Function.Injective (nodes hv P) := by
  intro i j h
  have hi : (i : ℕ) < Sh.block := i.isLt
  have hj : (j : ℕ) < Sh.block := j.isLt
  have := hv.dblock_add_N
  have := hv.enc_le_domain
  have := hv.rate_lt
  unfold dblock at *
  exact Fin.ext (P.inj (by omega) (by omega) h)

/-- The Shape of the tableau: `r` privacy positions and `w` witness positions per row,
`total` positions and `nq` products. -/
def shape (total nq extra : ℕ) : Layout.Shape := ⟨Sh.w, Sh.r, total, nq, extra, hv.w_pos⟩

theorem code_k (total nq extra : ℕ) :
    (code hv P).k = (shape hv total nq extra).r + (shape hv total nq extra).w := by
  change Sh.block = Sh.r + (Sh.block - Sh.r)
  have := hv.r_le
  omega

/-- No code point is a message node. -/
theorem code_ne_nodes (i : Fin Sh.N) (j : Fin (code hv P).k) : (code hv P).D i ≠ nodes hv P j := by
  intro h
  have hi := i.isLt
  have hj : (j : ℕ) < Sh.block := j.isLt
  have := hv.dblock_add_N
  have := hv.enc_le_domain
  have := hv.block_pos
  have hd : Sh.block ≤ Sh.dblock := by unfold dblock; omega
  have := P.inj (a := Sh.dblock + i) (b := j) (by omega) (by omega) h
  omega

end Ligero.Relative.Shape

end GordieHowe
