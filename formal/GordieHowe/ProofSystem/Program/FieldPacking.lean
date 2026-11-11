-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PlanTree
public import GordieHowe.Language.RealizedProgram.Views
public import GordieHowe.ProofSystem.Zerocheck.AffineBatch
public import GordieHoweNative.Language.PackingDesc
public import GordieHoweNative.Language.TableauNums
public import GordieHowe.Foundations.Algebra.FiniteFieldStages

@[expose] public section

/-!
# GordieHowe: the packing facts of a field interpretation

The plan data names a domain's packing tree by node names, degrees and masking modes
(`GordieHowe.RealizedProgram.Export.PackingEdge`); the Lean proof of the tree needs field facts the plan does not carry: the
stage bases of the edges with their relative Frobenius orders, the masks' basis `γ` of `K` over the
masking subfield `S0`, the subfield of each node, the evaluation points of Ligero's code, and, in
characteristic two, that a node's bit coordinates (`FieldInterp.coord`) are the coordinates of the
bit stage. They are a property of the field interpretation, stated and proved once per field
(`FieldInterp.Packing`, a class), never per program. The class is no restriction on the field:
every finite field of `p^n` elements with an interpretation whose named nodes are subfields has a
member (`GordieHowe/ProofSystem/Program/FieldPackingGeneric.lean`), realizing every edge
`F_{p^m} <d F_{p^(m d)}` with
`1 < d` and `m d ∣ n` (subfield masks when `s0 ∣ m`; squaring-chain masks in characteristic two at
`m = 1` where the interpretation reads bits in a basis), `q ≤ p^s0` evaluation points and every skip
domain of at most `|K|` points.

* **The packing facts** (`FieldInterp.Packing`): the characteristic `p`, the degree `n` of `K` over
  `F_p` (`card_eq`: `|K| = p^n`, so `F_{p^n} = K`, `top_eq`), the masking subfield
  `S0 = F_{p^s0}` (`s0_dvd`: `s0 ∣ n`), the realized edges by
  child degree, relative degree and masking mode (`edge`, `EdgeKit`), the degree of every node
  name with its subgroup the subfield of that degree (`nodeDeg`, `node_eq`), the evaluation points
  in `S0`, and the bit coordinates of a node of any degree (`coord_eq`).
* **The Ligero certificates** (`LigeroCert`): a Ligero shape with the agreement threshold and the
  exceptional count of the low-degree test, its line certificate, and the masking of the responses
  (untested masks with their list hypotheses, or the mask test, `LigeroCert.Masking`); the
  certificates are facts about the code for every field, proved once per shape. With a field's points it gives the tree layout's numbers
  (`Packing.numbers`).
-/

namespace GordieHowe.RealizedProgram

open Export PackingStage RelativePacking Ligero.MaskRow

/-- **The packing facts of a field interpretation**, the class of the fields the proof system proves
over (see the module docstring). Every finite field whose named nodes are subfields and whose bit
coordinates at the bit edges are basis coordinates has a member realizing every edge, node, point
count and skip domain its size allows (`FieldInterp.genericPacking`, `genericPacking_realizes`);
the concrete fields register computable instances
(`GordieHowe/ProofSystem/Program/FieldPackings.lean`). -/
class FieldInterp.Packing (F : FieldInterp) where
  /-- The characteristic. -/
  p : ℕ
  [expChar : ExpChar F.K p]
  /-- The degree of `K` over `F_p`. -/
  n : ℕ
  /-- `K` has `p^n` elements. -/
  card_eq : Fintype.card F.K = p ^ n
  /-- The degree of the masking subfield `S0` over `F_p`. -/
  s0 : ℕ
  /-- The masking subfield is a subfield of `K`: `s0` divides `n`. -/
  s0_dvd : s0 ∣ n
  /-- Membership in `S0` is decidable. -/
  [decS0 : DecidablePred (· ∈ fixedField F.K p s0)]
  /-- The realized edges by child degree, relative degree and masking mode. -/
  edge : (m d : ℕ) → PackingMode → Option (EdgeKit F.K p (fixedField F.K p s0) m d)
  /-- The degree of each node name over `F_p`. -/
  nodeDeg : String → Option ℕ
  /-- A node's subgroup is the subfield of its degree. -/
  node_eq : ∀ s m, nodeDeg s = some m → ((F.node s : AddSubgroup F.K) : Set F.K) = fixedField F.K p m
  /-- The size of the evaluation domain. -/
  q : ℕ
  /-- The evaluation points. -/
  points : Ligero.Relative.Shape.Points F.K q
  /-- The evaluation points lie in `S0`. -/
  points_mem : ∀ a, points.pt a ∈ fixedField F.K p s0
  /-- The bit coordinates of a node are the coordinates of the node's bit stage
  (`F_2 <dd`, the edge of child degree `1`). -/
  coord_eq : ∀ (s : String) {m dd : ℕ} (mode : PackingMode)
    (EB : EdgeKit F.K p (fixedField F.K p s0) m dd), edge m dd mode = some EB → m = 1 →
      mode = .squaringChain →
      nodeDeg s = some dd → ∀ x ∈ fixedField F.K p dd, ∀ j : Fin dd,
        F.ofBool (F.coord s x j) = EB.basis.coord x j
  /-- The bit coordinates are additive. -/
  bitsAdditive : F.BitsAdditive
  /-- The skip domain of width `w` at degree `D` (`D(w − 1) + 1` distinct points). -/
  skip : (w D : ℕ) → Option (Sumcheck.FieldSkip.SkipPoints F.K w D)
  /-- The interpolation nodes `0, 1, g` of a degree-two sumcheck round
  (`Field::poly_evaluation_point`), used by the bit sumcheck of a batch on bits; `none` for a
  field with no three distinct points. -/
  nodes : Option (Sumcheck.Nodes F.K)

attribute [instance] FieldInterp.Packing.expChar FieldInterp.Packing.decS0

/-- **`F_{p^n}` is `K`** (`fixedField_eq_top` at `card_eq`). -/
theorem FieldInterp.Packing.top_eq {F : FieldInterp} (Pk : F.Packing) :
    fixedField F.K Pk.p Pk.n = ⊤ :=
  RelativePacking.fixedField_eq_top Pk.card_eq

/-- **The packing descriptor of `Pk` at the queries of `D`**: the part of a packing the field
checks read (`fieldOkB`, through `fieldOkBD`), as naturals and Booleans: the degree `n`, the
evaluation domain's size `q`, at each of `D`'s queried edges (child degree, relative degree,
masking mode) whether `Pk` realizes it, at each of `D`'s queried node names its degree, at each of
`D`'s queried widths and degrees whether `Pk` has the skip domain, and whether `Pk` has the bit
sumcheck's interpolation nodes, and at each of `D`'s queried edges its kit's mask cells (before the
rows and in them). It reads `Pk` only at `D`'s keys, so `Pk.desc D = D` is a finite
check (`fieldOkB_of_desc`). -/
def FieldInterp.Packing.desc {F : FieldInterp} (Pk : F.Packing) (D : PackingDesc) : PackingDesc where
  n := Pk.n
  q := Pk.q
  edges := D.edges.map fun x => (x.1, x.2.1, x.2.2.1, (Pk.edge x.1 x.2.1 x.2.2.1).isSome)
  nodeDegs := D.nodeDegs.map fun x => (x.1, Pk.nodeDeg x.1)
  skips := D.skips.map fun x => (x.1, x.2.1, (Pk.skip x.1 x.2.1).isSome)
  hasNodes := Pk.nodes.isSome
  masks := D.masks.map fun x => (x.1, x.2.1, x.2.2.1,
    ((Pk.edge x.1 x.2.1 x.2.2.1).map fun kit => (kit.masks.nPre, kit.masks.nOwn)).getD (0, 0))

/-- **The masking of a certified Ligero shape** at message length `block` and block length `N`:
untested masks (`untested`) with the mask agreement threshold `a`, the mask list size `l` and the
arbitrary-mask list hypotheses of the code at them (`list`, a fact about the code for every field
of evaluation), or the mask test (`split`). -/
inductive LigeroCert.Masking (block N : ℕ) where
  /-- Untested masks at the mask agreement threshold `a` and mask list size `l`. -/
  | untested (a l : ℕ)
      (list : ∀ {F : Type} [Field F] (C : GordieHowe.RSCode F N), C.k = block →
        Ligero.UntestedMaskRow.Parameters C a l)
  /-- The mask test. -/
  | split

/-- **The exported masking kind** of a certified masking: `.listRadius` for untested masks,
`.split` for the mask test. -/
def LigeroCert.Masking.kind {block N : ℕ} : LigeroCert.Masking block N → Export.MaskingKind
  | .untested .. => .listRadius
  | .split => .split

/-- **The covering condition of a certified masking** at `t` queried columns: none for untested
masks, `2t ≤ block` for the mask test. -/
def LigeroCert.Masking.Covers {block N : ℕ} (t : ℕ) : LigeroCert.Masking block N → Prop
  | .untested .. => True
  | .split => 2 * t ≤ block

instance {block N : ℕ} (t : ℕ) (M : LigeroCert.Masking block N) : Decidable (M.Covers t) := by
  cases M <;> unfold LigeroCert.Masking.Covers <;> infer_instance

/-- **A certified Ligero shape**: the Ligero numbers, the agreement threshold and the exceptional
count of the low-degree test, its line certificate (`line`, a fact about the code for every field
of evaluation, proved once per shape), and the masking of the responses with its code parameters
(`masking`). -/
structure LigeroCert where
  /-- The Ligero numbers. -/
  Sh : Ligero.Relative.Shape
  /-- The agreement threshold. -/
  agree : ℕ
  /-- The exceptional count of the line certificate. -/
  exceptions : ℕ
  /-- The code parameters of the low-degree test: `k ≤ agree` and the line certificate. -/
  line : ∀ {F : Type} [Field F] (C : GordieHowe.RSCode F Sh.N), C.k = Sh.block →
    Ligero.MaskTest.Pieces.Parameters C agree exceptions
  /-- The masking of the responses. -/
  masking : LigeroCert.Masking Sh.block Sh.N

/-- **The layout facts of a Ligero shape** at the size `q` of the point domain, with the covering
condition of its masking, as a test. -/
def LigeroCert.validB (c : LigeroCert) (q : ℕ) : Bool :=
  decide (c.Sh.blockEnc ≤ q) && decide (0 < c.Sh.nreq) && decide (c.Sh.nreq ≤ c.Sh.r) &&
    decide (c.Sh.r < c.Sh.block) && decide (2 * c.Sh.block < c.Sh.N) &&
    decide (c.Sh.nreq ≤ c.Sh.N) && decide (0 < c.Sh.nrep) && decide (c.masking.Covers c.Sh.nreq)

theorem LigeroCert.valid_of_validB {c : LigeroCert} {q : ℕ} (h : c.validB q = true) :
    TreeLayout.Valid c.Sh q := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem LigeroCert.covers_of_validB {c : LigeroCert} {q : ℕ} (h : c.validB q = true) :
    c.masking.Covers c.Sh.nreq := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- **The plan's Ligero numbers and masking are the certificate's** (`.listRadius` for untested
masks, `.split` for the mask test, `Masking.kind`). -/
def LigeroCert.matchesB (c : LigeroCert) (lg : Export.Ligero) : Bool :=
  lg.masking == c.masking.kind && lg.rate == c.Sh.rate && lg.blockEnc == c.Sh.blockEnc &&
    lg.t == c.Sh.nreq && lg.r == c.Sh.r && lg.N == c.Sh.N && lg.k == c.Sh.block &&
    lg.ldtReps == c.Sh.nrep

/-- **The numbers of a certified Ligero shape** (`TableauNums`): its Ligero numbers, whether its
masking is the mask test, its agreement threshold and exceptional count. -/
def LigeroCert.nums (c : LigeroCert) : TableauNums :=
  ⟨c.Sh.rate, c.Sh.nreq, c.Sh.blockEnc, c.Sh.nrep, c.Sh.r, c.masking.kind == .split, c.agree,
    c.exceptions⟩

/-- **`validB` reads the numbers only.** -/
theorem LigeroCert.validB_eq_nums (c : LigeroCert) (q : ℕ) : c.validB q = c.nums.validB q := by
  obtain ⟨Sh, agree, exceptions, line, masking⟩ := c
  cases masking <;> rfl

/-- **`matchesB` reads the numbers only.** -/
theorem LigeroCert.matchesB_eq_nums (c : LigeroCert) (lg : Export.Ligero) :
    c.matchesB lg = c.nums.matchesB lg := by
  obtain ⟨Sh, agree, exceptions, line, masking⟩ := c
  cases masking <;> rfl

/-- **The tree layout's masking** of a certified shape at a code of the shape: untested masks with
the line certificate and the list hypotheses, or the mask test with the line certificate. -/
def LigeroCert.treeMasking {K : Type} [Field K] (c : LigeroCert) (C : GordieHowe.RSCode K c.Sh.N)
    (hk : C.k = c.Sh.block) : TreeLayout.Masking C :=
  match c.masking with
  | .untested a l list => .untested c.agree c.exceptions a l
      ⟨(c.line C hk).k_le_A, (c.line C hk).line, list C hk⟩
  | .split => .split c.agree c.exceptions (c.line C hk)

/-- **The tree layout's masking covers** the queried columns when the certified masking does. -/
theorem LigeroCert.covers_treeMasking {K : Type} [Field K] (c : LigeroCert)
    (C : GordieHowe.RSCode K c.Sh.N) (hk : C.k = c.Sh.block) {t : ℕ} (h : c.masking.Covers t) :
    (c.treeMasking C hk).Covers t := by
  unfold treeMasking
  split
  · trivial
  · next heq =>
    rw [heq] at h
    change 2 * t ≤ C.k
    rw [hk]
    exact h

/-! ### The round bounds of a certified shape as fractions -/

/-- **The test numerator of a certified masking**: the mask list size `l` for untested masks, `1`
for the mask test (the test bound is this over the field's size). -/
def LigeroCert.testNum (c : LigeroCert) : ℕ :=
  match c.masking with
  | .untested _ l _ => l
  | .split => 1

/-- **The mask count of the column bound** at `t = nreq` queried columns: `a_t` for untested masks
at the mask agreement threshold `a`, `(2k − 1)_t` for the mask test. -/
def LigeroCert.maskCount (c : LigeroCert) : ℕ :=
  match c.masking with
  | .untested a _ _ => a.descFactorial c.Sh.nreq
  | .split => (2 * c.Sh.block - 1).descFactorial c.Sh.nreq

/-- **The numerator of the column bound**: `(A − 1)_t` and the mask count. -/
def LigeroCert.columnNum (c : LigeroCert) : ℕ :=
  (c.agree - 1).descFactorial c.Sh.nreq + c.maskCount

/-- **The numerator of the joint subfield term**: `(k − 1)_t`. -/
def LigeroCert.jointNum (c : LigeroCert) : ℕ :=
  (c.Sh.block - 1).descFactorial c.Sh.nreq

/-- **The denominator of the column bound and the joint subfield term**: `(N)_t`. -/
def LigeroCert.columnDen (c : LigeroCert) : ℕ :=
  c.Sh.N.descFactorial c.Sh.nreq

/-- **The round bounds of a certified shape's tree masking** at its repetitions and queried
columns: the commit bound `(B/(|K| − 1))^nrep`, the test bound `testNum/|K|` and the column bound
`columnNum/columnDen`. -/
theorem LigeroCert.bounds_treeMasking {K : Type} [Field K] [Fintype K] (c : LigeroCert)
    (C : GordieHowe.RSCode K c.Sh.N) (hk : C.k = c.Sh.block) :
    (c.treeMasking C hk).bounds c.Sh.nrep c.Sh.nreq =
      ⟨((c.exceptions : NNReal) / (Fintype.card K - 1)) ^ c.Sh.nrep,
        (c.testNum : NNReal) / Fintype.card K, (c.columnNum : NNReal) / c.columnDen⟩ := by
  unfold treeMasking testNum columnNum maskCount columnDen
  split
  · next heq =>
    simp only [heq, TreeLayout.Masking.bounds, Ligero.AgreementThreshold.bounds, Nat.cast_add]
  · next heq =>
    simp only [heq, TreeLayout.Masking.bounds, Ligero.MaskTest.Pieces.bounds, hk, Nat.cast_add,
      Nat.cast_one]

namespace FieldInterp.Packing

variable {F : FieldInterp} (Pk : F.Packing)

/-- The masking subfield `S0`. -/
abbrev S0 : Subfield F.K := fixedField F.K Pk.p Pk.s0

/-- **The tree layout's Ligero numbers** of a certified shape at the field's points
(`TreeLayout.Numbers`). -/
def numbers (c : LigeroCert) (hv : c.validB Pk.q = true) :
    TreeLayout.Numbers F.K Pk.S0 where
  Sh := c.Sh
  q := Pk.q
  valid := LigeroCert.valid_of_validB hv
  points := Pk.points
  points_mem := Pk.points_mem
  masking := c.treeMasking _ rfl
  covers := c.covers_treeMasking _ rfl (LigeroCert.covers_of_validB hv)

/-- **The round bounds of the tree layout's Ligero numbers** are the certificate's fractions
(`LigeroCert.bounds_treeMasking`). -/
theorem numbers_bounds (c : LigeroCert) (hv : c.validB Pk.q = true) :
    (Pk.numbers c hv).bounds =
      ⟨((c.exceptions : NNReal) / (Fintype.card F.K - 1)) ^ c.Sh.nrep,
        (c.testNum : NNReal) / Fintype.card F.K, (c.columnNum : NNReal) / c.columnDen⟩ :=
  c.bounds_treeMasking _ rfl

end FieldInterp.Packing

end GordieHowe.RealizedProgram
