-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.MaskRow.Masked

@[expose] public section

/-!
# The C++ layout of a packing tree's commitment

The committed layout the C++ builds for a domain over a packing tree (`lib/gordiehowe/compiler/tree_zk.h`,
`TreeLayout`), from the three Ligero numbers `(rate, nreq, block_enc)` of its tableau
(`Ligero.Relative.Shape`, with the arithmetic facts `TreeLayout.Valid`), the number `np` of prefix
cells, the number `nw` of root children's words and the finite type `Full` of the root's own cells.
It is the layout of `Ligero.Relative.Shape` (`GordieHowe/ProofSystem/Ligero/RelativeLayout.lean`) with the one prefix
row of `D²` masks replaced by `⌈np / w⌉` prefix rows, and with the cells committed as they are (no
unpacking: a packing tree's root stages run in the masked row reduction).

* **The committed cells** (`Coord`, `tree_zk.h:350-351`): `[prefix | root children's words | root
  own]`. The prefix is `⌈np / w⌉` rows of `w` positions (`prefixRows`, `tree_zk.h:316`,
  `prefix_padded = ⌈prefix / w⌉ · w`), holding prefix cell `j` at position `j` and zeros after
  `np`; word `y` sits at `⌈np / w⌉ · w + y`; the root's own cells after the words, in the order of
  the encoding of `Full` (`Encodable.fintypeEquivFin`, `pos`).
* **Ligero**: the code, the message nodes and the Shape of `Ligero.Relative.Shape` (`code`,
  `nodes`, `shapeAt`), the rows of `Ligero.Layout.Shape`: the prefix rows, the word and own rows,
  then one copy of each product triple in the X/Y/Z product rows (`place`), then the extra rows of
  the masking (`Masking.extra`: the six piece rows of the mask test, none for untested masks).
* **The blinding fields** (`prefixFields`): `E` on the prefix rows (the C++ commits the first
  `prefix_padded` positions with subfield blinding, `tree_zk.h:1314`), `⊤` elsewhere. The prefix
  rows hold only prefix cells (`PrefixRowsPure`), so the honest cells are admissible whenever their
  prefix lies in `E` (`admissible_of_in`).

What a tree domain consumes (`TreeLayout.Numbers`, the Ligero numbers with their points in `E` and
the masking of the tableau with its code parameters, `TreeLayout.Masking`: untested masks or the
mask test):

* `Numbers.setup`: Ligero with the prefix-row test on the layout, with untested masks
  (`Numbers.untestedSetup`) or the mask test (`Numbers.splitSetup`), as a
  `GordieHowe.Ligero.MaskRow.Setup`, with the masking's round bounds at the Ligero numbers
  (`Masking.bounds`, `Numbers.bounds_setup`) and its proof-phase error (`Numbers.proofError`);
* `Numbers.hidingData`: its honest prover's data (`GordieHowe.Ligero.MaskRow.Setup.Hiding`), every field proved
  from the layout (`commitAllocation`, `pieceRows_free`, `hidingParams`, `query_le`), and
  `Numbers.admissible_hiding`: cells whose prefix lies in `E` are admissible.

The order of the root's own cells and of the products is not modelled from the C++; the proofs do
not depend on either.
-/

namespace GordieHowe.Ligero.Layout.Shape

variable (S : Shape) {F : Type} [Field F] {N : ℕ} (C : GordieHowe.RSCode F N) (hk : C.k = S.r + S.w)

/-- A source coordinate in the row of a position below `m · w` is at a position below `m · w`
(`m` whole rows; `Ligero.Layout.Shape.source_row_lt` is `m = 1`). -/
theorem source_row_lt_mul {m : ℕ} {i j : Fin S.nw} (hj : j.val < m * S.w)
    (h : (S.source C hk i).1 = (S.source C hk j).1) : i.val < m * S.w := by
  have hv := congrArg Fin.val h
  change 1 + i.val / S.w = 1 + j.val / S.w at hv
  have h1 : j.val / S.w < m := (Nat.div_lt_iff_lt_mul S.width_pos).mpr hj
  exact (Nat.div_lt_iff_lt_mul S.width_pos).mp (by omega)

end GordieHowe.Ligero.Layout.Shape

namespace GordieHowe.Ligero.MaskRow

open IOP
open scoped NNReal

/-! ### The prefix rows of a placement -/

section Fields

variable {K ι Q : Type} [Field K] {N R nQ np : ℕ} {C : GordieHowe.RSCode K N}
  {T : Tableau.Parameters (R := R) (nQ := nQ) C}

/-- A data row holding a prefix cell. The prefix-row test opens exactly these rows. -/
def IsPrefixRow (A : Preparation.Placement C T ι Q) (cell : Fin np → ι) (row : Fin R) : Prop :=
  ∃ j, (A.source (cell j)).1 = row.succ

instance (A : Preparation.Placement C T ι Q) (cell : Fin np → ι) (row : Fin R) :
    Decidable (IsPrefixRow A cell row) :=
  inferInstanceAs (Decidable (∃ j, (A.source (cell j)).1 = row.succ))

/-- **The blinding fields of a commitment with a prefix**: `E` on the prefix rows, `⊤` elsewhere
(the C++ commits the first `prefix_padded` positions with subfield blinding, `tree_zk.h:1314`),
membership decided by `E`'s. -/
def prefixFields (E : Subfield K) [DecidablePred (· ∈ E)] (A : Preparation.Placement C T ι Q)
    (cell : Fin np → ι) : HVZK.BlindingFields C T where
  field row := if IsPrefixRow A cell row then E else ⊤
  decMem row x :=
    if h : IsPrefixRow A cell row then decidable_of_iff (x ∈ E) (by simp [h])
    else isTrue (by simp [h])

variable {E : Subfield K} [DecidablePred (· ∈ E)] {A : Preparation.Placement C T ι Q}
  {cell : Fin np → ι}

theorem prefixFields_of_prefix {row : Fin R} (h : IsPrefixRow A cell row) :
    (prefixFields E A cell).field row = E := by
  simp [prefixFields, h]

theorem prefixFields_of_not_prefix {row : Fin R} (h : ¬ IsPrefixRow A cell row) :
    (prefixFields E A cell).field row = ⊤ := by
  simp [prefixFields, h]

/-- An element of `E` lies in every row's blinding field. -/
theorem prefixFields_mem {row : Fin R} {x : K} (hx : x ∈ E) :
    x ∈ (prefixFields E A cell).field row := by
  by_cases h : IsPrefixRow A cell row
  · rw [prefixFields_of_prefix h]
    exact hx
  · rw [prefixFields_of_not_prefix h]
    exact Subfield.mem_top _

variable (A cell) in
/-- **A prefix row holds only prefix cells**: a coordinate placed in a prefix row, under exact
routing, is a prefix cell. The C++ fills the prefix rows with the prefix cells and zeros
(`tree_zk.h:316`, `prefix_padded`). -/
def PrefixRowsPure (products : Routing.ProductLayout ι Q) : Prop :=
  ∀ z (row : Fin R), (A.location z).1 = row.succ → IsPrefixRow A cell row →
    Routing.routedSource products z ∈ Set.range cell

variable (A cell) in
/-- **The committed allocation of a commitment with a prefix**, a parameter condition on the fixed
layout and placement:
* `aliases`, `covered`: `Placement.AliasesAgree` and `Placement.ProductsCovered`;
* `prefixRows`: a prefix row holds only prefix cells (`PrefixRowsPure`);
* `products_ne_zero`: no product group reads row 0, the random ILDT row. -/
structure CommitAllocation (products : Routing.ProductLayout ι Q) : Prop where
  aliases : A.AliasesAgree products
  covered : A.ProductsCovered
  prefixRows : PrefixRowsPure A cell products
  products_ne_zero : ∀ g s, T.products g s ≠ 0

variable {products : Routing.ProductLayout ι Q}

variable (E A cell) in
/-- **The hiding layout of a commitment with a prefix**: `E` on the prefix rows and `⊤` elsewhere
(`prefixFields`). `hdomain` and `hnodes` are facts about the field: the code points and the message
nodes lie in `E`, hence in every row's blinding field. `hide` is a parameter condition: the hiding
thresholds of the tableau. The products never read row 0 (`CommitAllocation.products_ne_zero`). -/
def hidingLayout [DecidableEq K] (hdomain : ∀ j, C.D j ∈ E) (hnodes : ∀ j, T.nodes j ∈ E)
    (hide : HVZK.HidingParams C T) (hcom : CommitAllocation A cell products) :
    HVZK.HidingLayout C T where
  toBlindingFields := prefixFields E A cell
  toHidingParams := hide
  decEq := inferInstance
  nodes_mem _ j := prefixFields_mem (hnodes j)
  points_mem _ i := prefixFields_mem (hdomain i)
  products_ne_zero := hcom.products_ne_zero

/-- **Cells whose prefix lies in `E` are admissible**: every placed value lies in its row's blinding
field, since a prefix row holds only prefix cells (`PrefixRowsPure`). -/
theorem admissible_of_in (hcom : CommitAllocation A cell products) {x : ι → K}
    (hx : ∀ j, x (cell j) ∈ E) :
    ∀ z (row : Fin R), (A.location z).1 = row.succ →
      Routing.honestCopies products x z ∈ (prefixFields E A cell).field row := by
  intro z row hz
  by_cases hp : IsPrefixRow A cell row
  · rw [prefixFields_of_prefix hp]
    obtain ⟨j, hj⟩ := hcom.prefixRows z row hz hp
    have he : Routing.honestCopies products x z = x (Routing.routedSource products z) := by
      cases z <;> rfl
    rw [he, ← hj]
    exact hx j
  · rw [prefixFields_of_not_prefix hp]
    exact Subfield.mem_top _

end Fields

/-! ### The honest prover's data from the allocation -/

section Hiding

variable {K ι Q Lin : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [Fintype Q]
  [Fintype Lin] {N R nQ nL np : ℕ} {C : GordieHowe.RSCode K N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C} {products : Routing.ProductLayout ι Q}

/-- **The honest prover's data of Ligero with untested masks and the prefix-row test** from the
committed allocation (`CommitAllocation`): the hiding layout `hidingLayout` (`E` on the prefix
rows), so every prefix cell's row has blinding field `E`. `hnodes` is a fact about the field (the
message nodes lie in `E`); `hide`, `hcom` and `t_le_privacy` are parameter conditions. -/
def _root_.GordieHowe.Ligero.UntestedMask.hidingOf (S : UntestedMask.Setup C P products Lin nL np)
    (hnodes : ∀ j, P.nodes j ∈ S.pre.E) (hide : HVZK.HidingParams C P)
    (hcom : CommitAllocation S.placement S.pre.cell products)
    (t_le_privacy : S.t ≤ C.k - P.witness.card) : UntestedMask.Hiding S where
  inner :=
    { layout := hidingLayout S.pre.E S.placement S.pre.cell S.domain_mem hnodes hide hcom
      aliasesAgree := hcom.aliases
      productsCovered := hcom.covered
      t_le_privacy := t_le_privacy }
  prefix_field j _ h := le_of_eq (prefixFields_of_prefix ⟨j, h⟩)

/-- **The honest prover's data of Ligero with the mask test and the prefix-row test** from the committed
allocation (`CommitAllocation`): the hiding layout `hidingLayout` (`E` on the prefix rows), so every
prefix cell's row has blinding field `E`. `hnodes` is a fact about the field (the message nodes lie
in `E`); `hide`, `hcom`, `t_le_privacy`, `free` (the piece rows are free in the placement) and
`t_le_half` (`2t ≤ k`) are parameter conditions. -/
def _root_.GordieHowe.Ligero.MaskTest.hidingOf (S : MaskTest.Setup C P products Lin nL np)
    (hnodes : ∀ j, P.nodes j ∈ S.pre.E) (hide : HVZK.HidingParams C P)
    (hcom : CommitAllocation S.placement S.pre.cell products)
    (t_le_privacy : S.t ≤ C.k - P.witness.card) (free : S.pieces.Free S.placement)
    (t_le_half : 2 * S.t ≤ C.k) : MaskTest.Hiding S where
  inner :=
    { layout := hidingLayout S.pre.E S.placement S.pre.cell S.domain_mem hnodes hide hcom
      aliasesAgree := hcom.aliases
      productsCovered := hcom.covered
      t_le_privacy := t_le_privacy
      free := free
      t_le_half := t_le_half }
  prefix_field j _ h := le_of_eq (prefixFields_of_prefix ⟨j, h⟩)

end Hiding

/-! ### The C++ tree layout -/

namespace TreeLayout

open Ligero.Relative

/-- **The arithmetic facts of a tree layout's Ligero numbers** at the size `q` of the evaluation
domain, all parameter conditions discharged by `decide`: those of `Ligero.Relative.Shape.Valid`
without the mask row (the prefix spans as many rows as it needs): the encoded positions lie in the
domain, at least one query, at most as many queries as privacy positions (the paper's
`q ≤ k − ℓ`), at least one witness position per row (`ℓ ≥ 1`), the rate condition `2·block < N`,
and at most `N` queries. The covering condition `2·nreq ≤ block` of the mask test is the
masking's (`Masking.Covers`). -/
structure Valid (Sh : Relative.Shape) (q : ℕ) : Prop where
  /-- The encoded positions `[0, block_enc)` lie in the point domain. -/
  enc_le_domain : Sh.blockEnc ≤ q
  nreq_pos : 0 < Sh.nreq
  /-- At most as many queries as privacy positions (the paper's `q ≤ k − ℓ`). -/
  nreq_le_r : Sh.nreq ≤ Sh.r
  /-- At least one witness position per row (the paper's `ℓ ≥ 1`). -/
  r_lt_block : Sh.r < Sh.block
  rate_lt : 2 * Sh.block < Sh.N
  nreq_le_N : Sh.nreq ≤ Sh.N
  /-- The low-degree test has at least one repetition. -/
  nrep_pos : 0 < Sh.nrep

variable {Sh : Relative.Shape} {q : ℕ}

/-- The facts of the relative layout give those of the tree layout. -/
theorem Valid.of_relative {D : ℕ} (hv : Sh.Valid q D) : Valid Sh q :=
  ⟨hv.enc_le_domain, hv.nreq_pos, hv.nreq_le_r, hv.r_lt_block, hv.rate_lt, hv.nreq_le_N,
    hv.nrep_pos⟩

theorem Valid.w_pos (hv : Valid Sh q) : 0 < Sh.w := by
  have := hv.r_lt_block
  unfold Shape.w
  omega

/-- The facts of the tree layout are those of the relative layout at relative degree `1` (one
mask), which the shared code and Shape of `Ligero.Relative.Shape` take. -/
theorem Valid.toRelative (hv : Valid Sh q) : Sh.Valid q 1 :=
  ⟨hv.enc_le_domain, hv.nreq_pos, hv.nreq_le_r, hv.r_lt_block, by
    have := hv.w_pos
    omega, one_pos, hv.rate_lt, hv.nreq_le_N, hv.nrep_pos⟩

variable (hv : Valid Sh q) {F : Type} [Field F] (P : Shape.Points F q)

/-- **The code of the tableau** (`Ligero.Relative.Shape.code`): length `block_enc − dblock` at the
points `pt (dblock + j)`, message length `block`. -/
abbrev code : GordieHowe.RSCode F Sh.N := Shape.code hv.toRelative P

/-- The message nodes `pt 0, …, pt (block − 1)`. -/
abbrev nodes : Fin (code hv P).k → F := Shape.nodes hv.toRelative P

section Layout

variable (np nw : ℕ) (Full : Type) [Fintype Full] [Encodable Full] (nq extra : ℕ)

variable (Sh) in
/-- **The number of prefix rows**: `⌈np / w⌉` (`tree_zk.h:316`; `prefix_rows`, `tree_zk.h:1159`). -/
def prefixRows : ℕ := (np + Sh.w - 1) / Sh.w

variable {np} in
include hv in
/-- The prefix fits its rows: `np ≤ ⌈np / w⌉ · w`. -/
theorem le_prefixRows_mul : np ≤ prefixRows Sh np * Sh.w := by
  have hw := hv.w_pos
  have h1 := Nat.div_add_mod (np + Sh.w - 1) Sh.w
  have h2 := Nat.mod_lt (np + Sh.w - 1) hw
  unfold prefixRows
  rw [Nat.mul_comm]
  omega

/-- **The committed cells**: the prefix cells, the root children's words and the root's own
cells. -/
abbrev Coord := Fin np ⊕ (Fin nw ⊕ Full)

/-- **The prefix cells**: prefix cell `j` is the committed cell `.inl j`. -/
abbrev prefixCell (j : Fin np) : Coord np nw Full := .inl j

/-- **The prefix predicate**: a committed cell that is a prefix cell. -/
def IsPrefix (c : Coord np nw Full) : Prop := ∃ j, prefixCell np nw Full j = c

variable (Sh) in
/-- The number of positions: the prefix rows, the words and the root's own cells. -/
def total : ℕ := prefixRows Sh np * Sh.w + nw + Fintype.card Full

/-- **The position of a committed cell**: prefix cell `j` at `j`, word `y` at
`⌈np / w⌉ · w + y`, and the root's own cells after the words. -/
def pos : Coord np nw Full ↪ Fin (total Sh np nw Full) where
  toFun := Sum.elim
    (fun j => ⟨j, by
      have := j.isLt
      have := le_prefixRows_mul hv (np := np)
      unfold total
      omega⟩)
    (Sum.elim (fun y => ⟨prefixRows Sh np * Sh.w + y, by unfold total; omega⟩)
      (fun x => ⟨prefixRows Sh np * Sh.w + nw + Encodable.fintypeEquivFin (α := Full) x, by
        have := (Encodable.fintypeEquivFin (α := Full) x).isLt
        unfold total
        omega⟩))
  inj' := by
    have hm : ∀ j : Fin np, (j : ℕ) < prefixRows Sh np * Sh.w := fun j =>
      lt_of_lt_of_le j.isLt (le_prefixRows_mul hv)
    rintro (a | a | a) (b | b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
    · exact congrArg Sum.inl (Fin.ext h)
    · have := hm a; omega
    · have := hm a; omega
    · have := hm b; omega
    · exact congrArg (Sum.inr ∘ Sum.inl) (Fin.ext (by omega))
    · have := (Encodable.fintypeEquivFin (α := Full) b).isLt; omega
    · have := hm b; omega
    · have := b.isLt; omega
    · exact congrArg (Sum.inr ∘ Sum.inr) ((Encodable.fintypeEquivFin (α := Full)).injective
        (Fin.ext (by omega)))

variable {np nw Full} in
/-- The prefix cells are the cells at positions below `⌈np / w⌉ · w`. -/
theorem pos_lt_prefix {c : Coord np nw Full}
    (h : (pos hv np nw Full c).val < prefixRows Sh np * Sh.w) :
    c ∈ Set.range (prefixCell np nw Full) := by
  rcases c with j | y | x
  · exact ⟨j, rfl⟩
  · change prefixRows Sh np * Sh.w + y.val < prefixRows Sh np * Sh.w at h
    omega
  · change prefixRows Sh np * Sh.w + nw + (Encodable.fintypeEquivFin (α := Full) x).val <
      prefixRows Sh np * Sh.w at h
    omega

/-- The Shape of the tableau at the layout. -/
abbrev shapeAt : Layout.Shape := Sh.shape hv.toRelative (total Sh np nw Full) nq extra

/-- The tableau parameters. -/
abbrev tableau :=
  (shapeAt hv np nw Full nq extra).parameters (code hv P) (nodes hv P)
    (Shape.nodes_injective hv.toRelative P)

/-- **The placement** of the committed cells and the product copies, at an enumeration `qi` of the
products. -/
abbrev place {Q : Type} (qi : Q ≃ Fin nq) :
    Preparation.Placement (code hv P) (tableau hv P np nw Full nq extra) (Coord np nw Full) Q :=
  (shapeAt hv np nw Full nq extra).embeddedPlacement (code hv P)
    (Shape.code_k hv.toRelative P _ _ _) (pos hv np nw Full) qi (nodes hv P)
    (Shape.nodes_injective hv.toRelative P)

/-- **The hiding thresholds of the tableau**: no code point is a witness node, and the witness part
of a row is nonempty. -/
theorem hidingParams : HVZK.HidingParams (code hv P) (tableau hv P np nw Full nq extra) where
  off_witness i j _ := Shape.code_ne_nodes hv.toRelative P i j
  witness_nonempty := ⟨⟨Sh.r, hv.r_lt_block⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩⟩

/-- The query count `nreq` is at most the number `r` of privacy positions. -/
theorem query_le : Sh.nreq ≤ (code hv P).k - (tableau hv P np nw Full nq extra).witness.card :=
  hv.nreq_le_r.trans_eq ((shapeAt hv np nw Full nq extra).privacy_card (code hv P)
    (Shape.code_k hv.toRelative P _ _ _) (nodes hv P) (Shape.nodes_injective hv.toRelative P)).symm

variable {nq} {Q : Type} (qi : Q ≃ Fin nq) (products : Routing.ProductLayout (Coord np nw Full) Q)

/-- **A prefix row holds only prefix cells**: a cell in the row of a prefix cell is at a position
below `⌈np / w⌉ · w` (`Ligero.Layout.Shape.source_row_lt_mul`), so it is a prefix cell
(`pos_lt_prefix`); no product row is a source row. -/
theorem prefixRowsPure :
    PrefixRowsPure (place hv P np nw Full nq extra qi) (prefixCell np nw Full) products := by
  intro z row hz ⟨j, hj⟩
  have hjp : (pos hv np nw Full (.inl j)).val < prefixRows Sh np * Sh.w :=
    lt_of_lt_of_le j.isLt (le_prefixRows_mul hv)
  rcases z with c | ⟨g, s⟩
  · exact pos_lt_prefix hv ((shapeAt hv np nw Full nq extra).source_row_lt_mul (code hv P)
      (Shape.code_k hv.toRelative P _ _ _) hjp (hz.trans hj.symm))
  · exact absurd (hz.trans hj.symm) ((shapeAt hv np nw Full nq extra).products_ne_source
      (code hv P) (Shape.code_k hv.toRelative P _ _ _) _ s _)

/-- **The committed allocation of the layout**. -/
theorem commitAllocation :
    CommitAllocation (place hv P np nw Full nq extra qi) (prefixCell np nw Full) products where
  aliases := (shapeAt hv np nw Full nq extra).embeddedPlacement_aliasesAgree (code hv P) _
    (pos hv np nw Full) qi (nodes hv P) _ products
  covered := (shapeAt hv np nw Full nq extra).embeddedPlacement_productsCovered (code hv P) _
    (pos hv np nw Full) qi (nodes hv P) _
  prefixRows := prefixRowsPure hv P np nw Full extra qi products
  products_ne_zero := Layout.Shape.products_ne_zero _

/-- **The piece rows of the mask test are free in the placement** of a layout with six extra rows
(`Ligero.Layout.Shape.pieceRows_free`). -/
theorem pieceRows_free :
    (shapeAt hv np nw Full nq 6).pieceRows.Free (place hv P np nw Full nq 6 qi) :=
  (shapeAt hv np nw Full nq 6).pieceRows_free (code hv P) (Shape.code_k hv.toRelative P _ _ _)
    (pos hv np nw Full) qi (nodes hv P) (Shape.nodes_injective hv.toRelative P) rfl

end Layout

/-- **The masking of a tree layout's tableau** with the code parameters of its errors, on the code
`C`: untested masks (`untested`, `Ligero.AgreementThreshold` with the prefix-row test,
`GordieHowe.Ligero.UntestedMask`) at agreement threshold `agree`, exceptional count `exceptions`,
mask agreement threshold `a` and mask list size `l`; or the mask test (`split`,
`GordieHowe.Ligero.MaskTest`) at agreement threshold `agree` and exceptional count `exceptions`. -/
inductive Masking {K : Type} [Field K] {N : ℕ} (C : GordieHowe.RSCode K N) where
  /-- Untested masks, with the code parameters `Ligero.AgreementThreshold.Parameters`. -/
  | untested (agree exceptions a l : ℕ)
      (params : Ligero.AgreementThreshold.Parameters C agree exceptions a l)
  /-- The mask test, with the code parameters `MaskTest.Pieces.Parameters`. -/
  | split (agree exceptions : ℕ) (params : MaskTest.Pieces.Parameters C agree exceptions)

namespace Masking

variable {K : Type} [Field K] {N : ℕ} {C : GordieHowe.RSCode K N}

/-- **The extra data rows of the masking**: none for untested masks, the six piece rows of the
mask test. -/
def extra : Masking C → ℕ
  | .untested .. => 0
  | .split .. => 6

/-- The masking adds at most six data rows. -/
theorem extra_le_six : (M : Masking C) → M.extra ≤ 6
  | .untested .. => Nat.zero_le 6
  | .split .. => le_rfl

/-- **The covering condition of the masking** at `t` queried columns: none for untested masks,
`2t ≤ k` for the mask test (the paper's condition of `thm:backend` for a tableau with the mask
test). -/
def Covers (t : ℕ) : Masking C → Prop
  | .untested .. => True
  | .split .. => 2 * t ≤ C.k

/-- **The round bounds of the masking** at `nrep` repetitions of the low-degree test and `t`
queried columns: for untested masks those of `Ligero.AgreementThreshold.bounds` (commit
`(B/(|K| − 1)) ^ nrep`, test `l/|K|`, column `((A − 1)_t + a_t)/(N)_t`), for the mask test those of
`MaskTest.Pieces.bounds` (commit `(B/(|K| − 1)) ^ nrep`, test `1/|K|`, column
`((A − 1)_t + (2k − 1)_t)/(N)_t`). -/
noncomputable def bounds [Fintype K] (nrep t : ℕ) : Masking C → Ligero.AgreementThreshold.Bounds
  | .untested A B a l _ => Ligero.AgreementThreshold.bounds K N A B nrep t a l
  | .split A B _ => MaskTest.Pieces.bounds K N A B nrep C.k t

end Masking

/-- **The Ligero numbers of a tree layout** with what the commitment needs: the C++ numbers
`(rate, nreq, block_enc)` (`Sh`) with their arithmetic facts at the point domain `q` (`valid`), the
evaluation points of the C++ encoder (`points`), which lie in the prefix test's subfield `E`
(`points_mem`, a fact about the field), and the masking of the tableau with its code parameters
(`masking`: untested masks or the mask test) and its covering condition (`covers`). -/
structure Numbers (K : Type) [Field K] (E : Subfield K) where
  /-- The Ligero numbers `(rate, nreq, block_enc)`. -/
  Sh : Relative.Shape
  /-- The size of the point domain. -/
  q : ℕ
  /-- The arithmetic facts of the numbers. -/
  valid : Valid Sh q
  /-- The evaluation points. -/
  points : Shape.Points K q
  /-- The evaluation points lie in `E`. -/
  points_mem : ∀ a, points.pt a ∈ E
  /-- The masking of the tableau with its code parameters. -/
  masking : Masking (code valid points)
  /-- The covering condition of the masking at the `nreq` queried columns. -/
  covers : masking.Covers Sh.nreq

namespace Numbers

section Errors

variable {K : Type} [Field K] [Fintype K] {E : Subfield K} (L : Numbers K E)

/-- **The round bounds of the masking at the Ligero numbers** (`Masking.bounds` at `nrep`
repetitions and `t = nreq` queried columns). -/
noncomputable abbrev bounds : Ligero.AgreementThreshold.Bounds :=
  L.masking.bounds L.Sh.nrep L.Sh.nreq

/-- **The proof-phase error of the tree layout's commitment** with `np` prefix cells: the test and
column bounds and, when the prefix is nonempty, the joint subfield term `(k − 1)_t/(N)_t`. -/
noncomputable def proofError (np : ℕ) : ℝ≥0 :=
  L.bounds.test + L.bounds.column +
    if np = 0 then 0 else SubfieldTest.jointSubfieldError L.Sh.block L.Sh.N L.Sh.nreq

end Errors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {E : Subfield K} [DecidablePred (· ∈ E)]
  (L : Numbers K E) (np nw : ℕ) (Full : Type) [Fintype Full] [Encodable Full] {Q : Type} [Fintype Q]
  [Encodable Q] (products : Routing.ProductLayout (Coord np nw Full) Q) (Lin : Type) [Fintype Lin]
  [Encodable Lin]

variable (Q) in
/-- The tableau of the layout with the products `Q` and the extra rows of the masking
(`Masking.extra`: none for untested masks, the six piece rows of the mask test). -/
abbrev tableauOf (M : Masking (code L.valid L.points)) :=
  TreeLayout.tableau L.valid L.points np nw Full (Fintype.card Q) M.extra

variable (Q) in
/-- The tableau of the layout with the products `Q` and the extra rows of the masking. -/
abbrev tableau := L.tableauOf np nw Full Q L.masking

/-- The prefix cells of the layout, with the subfield `E` of the test. -/
def prefixCells : PrefixCells K (Coord np nw Full) np := ⟨prefixCell np nw Full, E⟩

/-- **Ligero with untested masks and the prefix-row test on the tree layout** (`tree_zk.h`, the
commitment of `TreeLayout` without the mask test): the placement `place` at an enumeration of the
products with no extra rows, the prepared rows in the order of their encoding
(`Encodable.fintypeEquivFin`), the agreement threshold, line certificate and mask list of `params`,
`nreq` queried columns, and the prefix cells in `E`, whose code points and message nodes lie in `E`
(`points_mem`). -/
def untestedSetup (A B a l : ℕ) (params : Ligero.AgreementThreshold.Parameters (code L.valid L.points) A B a l) :
    UntestedMask.Setup (code L.valid L.points)
      (L.tableauOf np nw Full Q (.untested A B a l params)) products Lin
      (Fintype.card (Routing.PreparedRow Lin Q)) np where
  placement := place L.valid L.points np nw Full (Fintype.card Q) 0
    (Encodable.fintypeEquivFin (α := Q))
  index := (Encodable.fintypeEquivFin (α := Routing.PreparedRow Lin Q)).symm
  A := A
  k_le_A := params.k_le_A
  B := B
  line := by
    rw [NNReal.coe_natCast]
    exact params.line
  t := L.Sh.nreq
  t_le := L.valid.nreq_le_N
  nrep := L.Sh.nrep
  nrep_pos := L.valid.nrep_pos
  a := a
  l := l
  list := params.list
  pre := prefixCells np nw Full
  domain_mem _ := L.points_mem _
  node_mem _ := L.points_mem _

/-- **Ligero with the mask test and the prefix-row test on the tree layout** (`tree_zk.h`, the
commitment of `TreeLayout`): the placement `place` at an enumeration of the products, the prepared
rows in the order of their encoding (`Encodable.fintypeEquivFin`), the agreement threshold and the
line certificate of `params`, `nreq` queried columns, the six piece rows after the product rows,
and the prefix cells in `E`, whose code points and message nodes lie in `E` (`points_mem`). -/
def splitSetup (A B : ℕ) (params : MaskTest.Pieces.Parameters (code L.valid L.points) A B) :
    MaskTest.Setup (code L.valid L.points) (L.tableauOf np nw Full Q (.split A B params)) products
      Lin (Fintype.card (Routing.PreparedRow Lin Q)) np where
  placement := place L.valid L.points np nw Full (Fintype.card Q) 6
    (Encodable.fintypeEquivFin (α := Q))
  index := (Encodable.fintypeEquivFin (α := Routing.PreparedRow Lin Q)).symm
  A := A
  k_le_A := params.k_le_A
  B := B
  line := by
    rw [NNReal.coe_natCast]
    exact params.line
  t := L.Sh.nreq
  t_le := L.valid.nreq_le_N
  nrep := L.Sh.nrep
  nrep_pos := L.valid.nrep_pos
  rate_le := (Nat.sub_le _ 1).trans L.valid.rate_lt.le
  pieces := (shapeAt L.valid np nw Full (Fintype.card Q) 6).pieceRows
  pre := prefixCells np nw Full
  domain_mem _ := L.points_mem _
  node_mem _ := L.points_mem _

/-- **The commitment of the tree layout at a masking** as a setup of Ligero with the prefix-row
test: `untestedSetup` for untested masks, `splitSetup` for the mask test. -/
def setupOf : (M : Masking (code L.valid L.points)) →
    Setup (code L.valid L.points) (L.tableauOf np nw Full Q M) products Lin
      (Fintype.card (Routing.PreparedRow Lin Q)) np
  | .untested A B a l params => .listRadius (L.untestedSetup np nw Full products Lin A B a l params)
  | .split A B params => .split (L.splitSetup np nw Full products Lin A B params)

/-- **The commitment of the tree layout** as a setup of Ligero with the prefix-row test, at the
masking of the numbers (`setupOf`). -/
abbrev setup :
    Setup (code L.valid L.points) (L.tableau np nw Full Q) products Lin
      (Fintype.card (Routing.PreparedRow Lin Q)) np :=
  L.setupOf np nw Full products Lin L.masking

/-- **The honest prover's data of the tree layout's commitment at a masking**
(`UntestedMask.hidingOf`, `MaskTest.hidingOf`): every field proved from the layout: the message
nodes in `E` (`points_mem`), the hiding thresholds (`hidingParams`), the committed allocation
(`commitAllocation`), the query count at most the privacy positions (`query_le`), and for the mask
test the piece rows free (`pieceRows_free`) and `2t ≤ k` (`Masking.Covers`). -/
def hidingDataOf : (M : Masking (code L.valid L.points)) → M.Covers L.Sh.nreq →
    (L.setupOf np nw Full products Lin M).Hiding
  | .untested A B a l params, _ =>
    UntestedMask.hidingOf (L.untestedSetup np nw Full products Lin A B a l params)
      (fun _ => L.points_mem _)
      (hidingParams L.valid L.points np nw Full _ 0)
      (commitAllocation L.valid L.points np nw Full 0 (Encodable.fintypeEquivFin (α := Q)) products)
      (query_le L.valid L.points np nw Full _ 0)
  | .split A B params, hcov =>
    MaskTest.hidingOf (L.splitSetup np nw Full products Lin A B params) (fun _ => L.points_mem _)
      (hidingParams L.valid L.points np nw Full _ 6)
      (commitAllocation L.valid L.points np nw Full 6 (Encodable.fintypeEquivFin (α := Q)) products)
      (query_le L.valid L.points np nw Full _ 6)
      (pieceRows_free L.valid L.points np nw Full (Encodable.fintypeEquivFin (α := Q)))
      hcov

/-- **The honest prover's data of the tree layout's commitment** (`hidingDataOf` at the masking of
the numbers). -/
def hidingData : (L.setup np nw Full products Lin).Hiding :=
  L.hidingDataOf np nw Full products Lin L.masking L.covers

omit [Fintype K] in
variable {np nw Full products Lin} in
/-- **Cells whose prefix lies in `E` are admissible** for the honest prover of the tree layout's
commitment at every masking (`admissible_of_in`). -/
theorem admissible_hidingOf (M : Masking (code L.valid L.points)) (hM : M.Covers L.Sh.nreq)
    {x : Coord np nw Full → K} (hx : ∀ j, x (prefixCell np nw Full j) ∈ E) :
    (L.setupOf np nw Full products Lin M).Admissible
      (L.hidingDataOf np nw Full products Lin M hM) x := by
  cases M
  · exact admissible_of_in
      (commitAllocation L.valid L.points np nw Full 0 (Encodable.fintypeEquivFin (α := Q)) products) hx
  · exact admissible_of_in
      (commitAllocation L.valid L.points np nw Full 6 (Encodable.fintypeEquivFin (α := Q)) products) hx

omit [Fintype K] in
variable {np nw Full products Lin} in
/-- **Cells whose prefix lies in `E` are admissible** for the honest prover of the tree layout's
commitment (`admissible_hidingOf`). -/
theorem admissible_hiding {x : Coord np nw Full → K} (hx : ∀ j, x (prefixCell np nw Full j) ∈ E) :
    (L.setup np nw Full products Lin).Admissible (L.hidingData np nw Full products Lin) x :=
  L.admissible_hidingOf L.masking L.covers hx

omit [DecidableEq K] in
/-- **The round bounds of the tree layout's commitment at a masking** are the masking's at the
Ligero numbers (`Masking.bounds`). -/
theorem bounds_setupOf (M : Masking (code L.valid L.points)) :
    (L.setupOf np nw Full products Lin M).bounds = M.bounds L.Sh.nrep L.Sh.nreq := by
  cases M <;> rfl

omit [DecidableEq K] in
/-- **The round bounds of the tree layout's commitment** are the masking's at the Ligero numbers
(`bounds`). -/
theorem bounds_setup : (L.setup np nw Full products Lin).bounds = L.bounds :=
  L.bounds_setupOf np nw Full products Lin L.masking

omit [Fintype K] [DecidableEq K] in
/-- The tree layout's commitment at a masking queries `nreq` columns. -/
theorem t_setupOf (M : Masking (code L.valid L.points)) :
    (L.setupOf np nw Full products Lin M).t = L.Sh.nreq := by
  cases M <;> rfl

omit [Fintype K] [DecidableEq K] in
/-- The tree layout's commitment queries `nreq` columns. -/
theorem t_setup : (L.setup np nw Full products Lin).t = L.Sh.nreq :=
  L.t_setupOf np nw Full products Lin L.masking

omit [Fintype K] [DecidableEq K] in
/-- The tree layout's commitment at a masking repeats the low-degree test `nrep` times. -/
theorem nrep_setupOf (M : Masking (code L.valid L.points)) :
    (L.setupOf np nw Full products Lin M).nrep = L.Sh.nrep := by
  cases M <;> rfl

omit [Fintype K] [DecidableEq K] in
/-- The tree layout's commitment repeats the low-degree test `nrep` times. -/
theorem nrep_setup : (L.setup np nw Full products Lin).nrep = L.Sh.nrep :=
  L.nrep_setupOf np nw Full products Lin L.masking

omit [Fintype K] [DecidableEq K] in
/-- The prefix cells of the tree layout's commitment at a masking, with their subfield. -/
theorem pre_setupOf (M : Masking (code L.valid L.points)) :
    (L.setupOf np nw Full products Lin M).pre = prefixCells (E := E) np nw Full := by
  cases M <;> rfl

omit [Fintype K] [DecidableEq K] in
/-- The tree layout's prefix cells and their subfield. -/
theorem pre_setup : (L.setup np nw Full products Lin).pre = prefixCells (E := E) np nw Full :=
  L.pre_setupOf np nw Full products Lin L.masking

end Numbers

end TreeLayout

end GordieHowe.Ligero.MaskRow
