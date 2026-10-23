-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.TreeLayoutDomain
public import GordieHowe.ProofSystem.RingSwitching.RouteSupport

@[expose] public section

/-!
# A packing tree from a list of planned edges

The planner's packing tree of a domain (`tree.h`, `GordieHowe.RealizedProgram.Export.Domain.packing`) is a list of edges in
processing order, deepest first, each edge `B < T` packing the slots of its child node `B` into
words of its parent `T`: the root `K` or the child of a later edge. This file builds the general
tree of `GordieHowe/Language/Export/PackingTree.lean` from such a list, for any number of edges and any
shape of tree:

* **the masks of an edge** (`MaskKit`, generic in the cells): the scheme on given prefix cells and
  own cells, its mode (`StageMode`), and its honest prover with the values its cells hold. The kits
  are subfield masks over `S0` with a basis `γ` of `K` over `S0` (`MaskKit.subfield`) and
  squaring-chain masks over `GF(2)` (`MaskKit.bitChain`) and over `GF(2^b)` (`MaskKit.chain`);
* **a realized edge** (`EdgeKit`): the stage basis of `F_{p^m} <d` with top `F_{p^(m d)}`, the
  relative Frobenius order of `K` over `F_{p^m}`, and the masks;
* **a planned edge** (`PEdge`): an edge kit, the number of groups `ng`, the parent (`none` for the
  root, `some j` for the edge at absolute position `j`), the parent's slot holding each group (a
  committed word for a root child), and the mask cells;
* **the logical coordinates** (`PEdge.Logical`): the cells, then each edge's child coordinates, each
  at its edge's node (`PEdge.nodeOf`);
* **the routed tree** (`PEdge.path`), for claims reading given nodes: every edge's stage, root
  children included, combines the claims whose nodes hold it, with no combination when at most one
  does, and passes the others (`GordieHowe.RingSwitching.Tree.route` at `PEdge.routeAt`); the claims after it read
  `PEdge.nextReads`, so the passing claims avoid the child when the claims read only their nodes
  (`PEdge.routes_path`); at most one combination per edge (`combinations_path_le`); nested and with
  a mode per stage under the decidable shape condition (`PEdge.Shaped`), so a member of the class
  (`PEdge.treeSpec`);
* **the logical assignment** (`GordieHowe.RingSwitching.Tree.level_mem`): decoded coordinates lie in their nodes'
  subfields on every committed vector; a consistent assignment (`PEdge.Consistent`: each child
  coordinate is the decoded coordinate of its word) is the logical assignment of its cells
  (`PEdge.level_view_of_consistent`).
-/

namespace GordieHowe

open IOP PackingStage RelativePacking
open scoped NNReal

/-! ### The decoded coordinates lie in their subfields -/

namespace RingSwitching.Tree

variable {K ι : Type} [Field K] [Fintype ι] {p : ℕ} [ExpChar K p]

/-- **Decoded coordinates lie in their nodes' subfields** on every committed vector, for a nested
path: a child coordinate is a decoded coordinate of a word in the stage's top
(`StageBasis.coord_mem_fixedField`). -/
theorem level_mem : {V : Type} → {nc : ℕ} → (P : Tree K p ι V nc) → P.Nested →
    ∀ (x : ι → K) (z : V), P.level.view x z ∈ P.field z
  | _, _, .nil, _, _, _ => Subfield.mem_top _
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), hN, x, .inl y =>
    level_mem rest hN.2 x y
  | _, _, (@Tree.cons _ _ _ _ _ _ _ _ _ _ _ _ S rest), hN, x, .inr c =>
    S.basis.coord_mem_fixedField (hN.1 c.group (level_mem rest hN.2 x (S.word c.group))) c.pos
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest), hN, x, .inl y =>
    level_mem rest hN.2 x y
  | _, _, (@Tree.route _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ rest), hN, x, .inr c =>
    S.basis.coord_mem_fixedField (hN.1 c.group (level_mem rest hN.2 x (S.word c.group))) c.pos

end RingSwitching.Tree

/-! ### The masks of an edge -/

/-- **The masks of an edge, generic in the cells**: the scheme on `nPre` prefix cells and `nOwn`
own cells, its mode over `S0` with the prefix predicate holding at the prefix cells, and its honest
prover: uniform masks from the pads (`sigmaOf`), and the values the prefix cells (in `S0`) and the
own cells hold, on which the mask forms are the masks, the products hold and `Valid` holds. -/
structure MaskKit (K : Type) [Field K] [Fintype K] (p m d : ℕ) [ExpChar K p] (S0 : Subfield K)
    where
  /-- The number of prefix cells. -/
  nPre : ℕ
  /-- The number of own cells. -/
  nOwn : ℕ
  /-- The scheme on the prefix cells and the own cells. -/
  scheme : {ι : Type} → (Fin nPre → ι) → (Fin nOwn → ι) → MaskScheme K ι p m d
  /-- The mode of the scheme. -/
  mode : ∀ {ι : Type} (pre : ι → Prop) (cp : Fin nPre → ι) (co : Fin nOwn → ι),
    (∀ j, pre (cp j)) → StageMode S0 pre (scheme cp co)
  /-- The pads. -/
  Pads : Type
  [fintype : Fintype Pads]
  [nonempty : Nonempty Pads]
  /-- The masks the pads give. -/
  sigmaOf : Pads → Fin d → K
  /-- The masks are uniform. -/
  uniform : Uniform sigmaOf
  /-- The values of the prefix cells. -/
  preVal : Pads → Fin nPre → K
  /-- The prefix values lie in `S0`. -/
  preVal_mem : ∀ π j, preVal π j ∈ S0
  /-- The values of the own cells. -/
  ownVal : Pads → Fin nOwn → K
  /-- The mask forms are the masks on cells holding the values. -/
  sigma_eval : ∀ {ι : Type} (cp : Fin nPre → ι) (co : Fin nOwn → ι) π (x : ι → K),
    (∀ j, x (cp j) = preVal π j) → (∀ o, x (co o) = ownVal π o) →
      ∀ k, ((scheme cp co).sigma k).eval x = sigmaOf π k
  /-- The products hold on cells holding the values. -/
  products : ∀ {ι : Type} (cp : Fin nPre → ι) (co : Fin nOwn → ι) π (x : ι → K),
    (∀ j, x (cp j) = preVal π j) → (∀ o, x (co o) = ownVal π o) →
      Ligero.Routing.SourceProducts (scheme cp co).products x
  /-- `Valid` holds on cells holding the values. -/
  valid : ∀ {ι : Type} (cp : Fin nPre → ι) (co : Fin nOwn → ι) π (x : ι → K),
    (∀ j, x (cp j) = preVal π j) → (∀ o, x (co o) = ownVal π o) → (scheme cp co).Valid x
  /-- The product triples are at most the own cells. -/
  card_Q_le : ∀ {ι : Type} (cp : Fin nPre → ι) (co : Fin nOwn → ι),
    Fintype.card (scheme cp co).Q ≤ nOwn

attribute [instance] MaskKit.fintype MaskKit.nonempty

namespace MaskKit

variable {K : Type} [Field K] [Fintype K] {p m d : ℕ} [ExpChar K p] {S0 : Subfield K}

/-- **The honest masks of a kit** on given cells: the kit's pads and masks, the cells holding the
kit's values. -/
def honest (M : MaskKit K p m d S0) {ι : Type} (cp : Fin M.nPre → ι) (co : Fin M.nOwn → ι) :
    (M.scheme cp co).Honest where
  Pads := M.Pads
  sigmaOf := M.sigmaOf
  uniform := M.uniform
  Commits π x := (∀ j, x (cp j) = M.preVal π j) ∧ ∀ o, x (co o) = M.ownVal π o
  sigma_eval π x h := M.sigma_eval cp co π x h.1 h.2
  products π x h := M.products cp co π x h.1 h.2
  valid π x h := M.valid cp co π x h.1 h.2

/-- **Subfield masks as a kit** (`MaskScheme.subfieldMasks`): `d · r` prefix cells `s_{k,i}` at
`k r + i` (`finProdFinEquiv`), no own cell, the basis `γ` of `K` over `S0 ⊆ F_{p^m}` (`hγ`, a
fact about the field data); the honest cells are uniform in `S0`. -/
def subfield {r : ℕ} (γ : Fin r → K) (hS0 : S0 ≤ fixedField K p m)
    [Fintype S0] (hγ : Function.Bijective fun s : Fin r → S0 => ∑ i, γ i * s i) :
    MaskKit K p m d S0 where
  nPre := d * r
  nOwn := 0
  scheme cp _ := MaskScheme.subfieldMasks
    { cell := fun k i => cp (finProdFinEquiv (k, i)), γ := γ, S0 := S0, S0_le := hS0 }
  mode pre cp _ h := .subfieldMasks _ rfl fun k i => h _
  Pads := Fin d → Fin r → S0
  sigmaOf π k := ∑ i, γ i * π k i
  uniform := IdentDistrib.of_equiv
    (Equiv.piCongrRight fun _ => Equiv.ofBijective _ hγ) fun _ => rfl
  preVal π j := π (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  preVal_mem π j := (π _ _).2
  ownVal _ o := o.elim0
  sigma_eval cp _ π x h _ k := by
    simp only [MaskScheme.subfieldMasks, AffineForm.eval_sumFin, AffineForm.eval_smul,
      AffineForm.eval_var, h, Equiv.symm_apply_apply, smul_eq_mul]
  products _a _b _c _d _e _f q := q.elim
  valid cp _ π x h _ k i := by
    change x (cp (finProdFinEquiv (k, i))) ∈ S0
    rw [h, Equiv.symm_apply_apply]
    exact (π k i).2
  card_Q_le _ _ := by
    change Fintype.card Empty ≤ 0
    simp

/-- **The own cells of a squaring chain on `d` masks**: `σ_k`, then the chain cells
(`SquaringCell.equivSigma`, `finSigmaFinEquiv`). -/
def chainCells {ι : Type} (co : Fin (d + ∑ k : Fin d, (k : ℕ)) → ι) : SquaringChainCells ι d where
  sigma k := co (Fin.castAdd _ k)
  chain c := co (Fin.natAdd d (finSigmaFinEquiv ((SquaringCell.equivSigma d) c)))

/-- **The values of a squaring chain's own cells** for the masks `σ`: `σ_k`, then the chain cell
`(k, j)` the power `σ_k ^ 2 ^ (j + 1)`. -/
def chainVal (σ : Fin d → K) (o : Fin (d + ∑ k : Fin d, (k : ℕ))) : K :=
  Fin.addCases (fun k => σ k)
    (fun j => σ ((SquaringCell.equivSigma d).symm (finSigmaFinEquiv.symm j)).k ^
      2 ^ ((((SquaringCell.equivSigma d).symm (finSigmaFinEquiv.symm j)).j : ℕ) + 1)) o

theorem chainVal_sigma (σ : Fin d → K) (k : Fin d) :
    chainVal σ (Fin.castAdd (∑ k : Fin d, (k : ℕ)) k) = σ k := by
  simp only [chainVal, Fin.addCases_left]

theorem chainVal_chain (σ : Fin d → K) (c : SquaringCell d) :
    chainVal σ (Fin.natAdd d (finSigmaFinEquiv ((SquaringCell.equivSigma d) c))) =
      σ c.k ^ 2 ^ ((c.j : ℕ) + 1) := by
  rw [chainVal, Fin.addCases_right, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- **Cells holding the chain values commit the honest squaring chain**
(`MaskScheme.squaringChainHonest`). -/
theorem commits_chainVal [ExpChar K 2] {ι : Type} (co : Fin (d + ∑ k : Fin d, (k : ℕ)) → ι)
    (σ : Fin d → K) (x : ι → K) (h : ∀ o, x (co o) = chainVal σ o) :
    (MaskScheme.squaringChainHonest (F := K) (chainCells co)).Commits σ x :=
  ⟨fun k => (h _).trans (chainVal_sigma σ k), fun c => (h _).trans (chainVal_chain σ c)⟩

/-- **Squaring-chain masks over `GF(2)` as a kit** (`MaskScheme.squaringChain`): no prefix cell,
`d + d(d − 1)/2` own cells (`chainCells`); the honest masks are uniform in `K^d`, the chain cells
their squarings (`MaskScheme.squaringChainHonest`). -/
def bitChain [ExpChar K 2] {S0 : Subfield K} : MaskKit K 2 1 d S0 where
  nPre := 0
  nOwn := d + ∑ k : Fin d, (k : ℕ)
  scheme _ co := MaskScheme.squaringChain (chainCells co)
  mode _ _ co _ := .squaringChainBit (chainCells co)
  Pads := Fin d → K
  sigmaOf σ := σ
  uniform := IdentDistrib.refl _
  preVal _ j := j.elim0
  preVal_mem _ j := j.elim0
  ownVal := chainVal
  sigma_eval _ co σ x _ h :=
    (MaskScheme.squaringChainHonest (F := K) (chainCells co)).sigma_eval σ x
      (commits_chainVal co σ x h)
  products _ co σ x _ h :=
    (MaskScheme.squaringChainHonest (F := K) (chainCells co)).products σ x
      (commits_chainVal co σ x h)
  valid := by intros; trivial
  card_Q_le _ _ := by
    change Fintype.card (SquaringCell d) ≤ _
    rw [Fintype.card_congr (SquaringCell.equivSigma d), Fintype.card_sigma]
    simp only [Fintype.card_fin]
    omega

/-- **The own cells of a squaring chain over `GF(2^b)` on `d` masks**: `σ_k`, then the chain cells
(`ChainCell.equivSigma`, `finSigmaFinEquiv`). -/
def chainOverCells {b : ℕ} {ι : Type} (co : Fin (d + ∑ k : Fin d, b * (k : ℕ)) → ι) :
    ChainCells ι b d where
  sigma k := co (Fin.castAdd _ k)
  chain c := co (Fin.natAdd d (finSigmaFinEquiv ((ChainCell.equivSigma b d) c)))

/-- **The values of the own cells of a squaring chain over `GF(2^b)`** for the masks `σ`: `σ_k`,
then the chain cell `(k, j)` the power `σ_k ^ 2 ^ (j + 1)`. -/
def chainOverVal (b : ℕ) (σ : Fin d → K) (o : Fin (d + ∑ k : Fin d, b * (k : ℕ))) : K :=
  Fin.addCases (fun k => σ k)
    (fun j => σ ((ChainCell.equivSigma b d).symm (finSigmaFinEquiv.symm j)).k ^
      2 ^ ((((ChainCell.equivSigma b d).symm (finSigmaFinEquiv.symm j)).j : ℕ) + 1)) o

theorem chainOverVal_sigma (b : ℕ) (σ : Fin d → K) (k : Fin d) :
    chainOverVal b σ (Fin.castAdd (∑ k : Fin d, b * (k : ℕ)) k) = σ k := by
  simp only [chainOverVal, Fin.addCases_left]

theorem chainOverVal_chain (b : ℕ) (σ : Fin d → K) (c : ChainCell b d) :
    chainOverVal b σ (Fin.natAdd d (finSigmaFinEquiv ((ChainCell.equivSigma b d) c))) =
      σ c.k ^ 2 ^ ((c.j : ℕ) + 1) := by
  rw [chainOverVal, Fin.addCases_right, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- **Cells holding the chain values commit the honest squaring chain over `GF(2^b)`**
(`MaskScheme.squaringChainOverHonest`). -/
theorem commits_chainOverVal [ExpChar K 2] {b : ℕ} {ι : Type}
    (co : Fin (d + ∑ k : Fin d, b * (k : ℕ)) → ι) (σ : Fin d → K) (x : ι → K)
    (h : ∀ o, x (co o) = chainOverVal b σ o) :
    (MaskScheme.squaringChainOverHonest (F := K) (chainOverCells co)).Commits σ x :=
  ⟨fun k => (h _).trans (chainOverVal_sigma b σ k),
    fun c => (h _).trans (chainOverVal_chain b σ c)⟩

/-- **Squaring-chain masks over `B = GF(2^b)` as a kit** (`MaskScheme.squaringChainOver`,
`lem:bits-sound`(2),(3) at every `b`): no prefix cell, `d + b d(d − 1)/2` own cells
(`chainOverCells`); the honest masks are uniform in `K^d`, the chain cells their squarings
(`MaskScheme.squaringChainOverHonest`). `bitChain` is the case `b = 1` with its own cell type. -/
def chain [ExpChar K 2] (b : ℕ) {S0 : Subfield K} : MaskKit K 2 b d S0 where
  nPre := 0
  nOwn := d + ∑ k : Fin d, b * (k : ℕ)
  scheme _ co := MaskScheme.squaringChainOver (chainOverCells co)
  mode _ _ co _ := .squaringChain (chainOverCells co)
  Pads := Fin d → K
  sigmaOf σ := σ
  uniform := IdentDistrib.refl _
  preVal _ j := j.elim0
  preVal_mem _ j := j.elim0
  ownVal := chainOverVal b
  sigma_eval _ co σ x _ h :=
    (MaskScheme.squaringChainOverHonest (F := K) (chainOverCells co)).sigma_eval σ x
      (commits_chainOverVal co σ x h)
  products _ co σ x _ h :=
    (MaskScheme.squaringChainOverHonest (F := K) (chainOverCells co)).products σ x
      (commits_chainOverVal co σ x h)
  valid := by intros; trivial
  card_Q_le _ _ := by
    change Fintype.card (ChainCell b d) ≤ _
    rw [Fintype.card_congr (ChainCell.equivSigma b d), Fintype.card_sigma]
    simp only [Fintype.card_fin]
    omega

end MaskKit

/-! ### Realized and planned edges -/

/-- **A realized edge** `F_{p^m} <d F_{p^(m d)}` of `K`: the stage basis, whose top is
`F_{p^(m d)}`, the relative Frobenius order `e` of `K` over `F_{p^m}`, and the masks. The fields
are field facts, certified once for the concrete field. -/
structure EdgeKit (K : Type) [Field K] [Fintype K] (p : ℕ) [ExpChar K p] (S0 : Subfield K)
    (m d : ℕ) where
  /-- The relative Frobenius order of `K` over `F_{p^m}`. -/
  e : ℕ
  /-- `K` has relative Frobenius order `e` over `F_{p^m}`. -/
  [order : RelFrobeniusOrder K p m e]
  /-- The stage basis. -/
  basis : StageBasis K p m d
  /-- The top is `F_{p^(m d)}`. -/
  top_eq : basis.top = fixedField K p (m * d)
  /-- The masks. -/
  masks : MaskKit K p m d S0

/-- **A planned edge** on the cells `ι`: a realized edge `F_{p^m} <d`, its `ng` groups, its parent
(`none`: the root; `some j`: the child of the edge at absolute position `j`), the parent's slot
holding each group, the committed word of each group (read for a root child), and the mask
cells. -/
structure PEdge (K ι : Type) [Field K] [Fintype K] (p : ℕ) [ExpChar K p] (S0 : Subfield K) where
  /-- The child's degree over `F_p`. -/
  m : ℕ
  /-- The relative degree. -/
  d : ℕ
  /-- The realized edge. -/
  kit : EdgeKit K p S0 m d
  /-- The number of groups. -/
  ng : ℕ
  /-- The parent: `none` for the root, `some j` for the child of the edge at position `j`. -/
  parent : Option ℕ
  /-- The parent's slot holding each group. -/
  slot : Fin ng → ℕ
  /-- The committed word of each group, for a root child. -/
  rootWord : Fin ng → ι
  /-- The prefix cells of the masks. -/
  maskPre : Fin kit.masks.nPre → ι
  /-- The own cells of the masks. -/
  maskOwn : Fin kit.masks.nOwn → ι

/-- `PackedCoord ng d` is finite: a group and a position. -/
instance PackedCoord.instFintypePlan (ng d : ℕ) : Fintype (PackedCoord ng d) :=
  Fintype.ofEquiv (Fin ng × Fin d)
    ⟨fun p => ⟨p.1, p.2⟩, fun c => (c.group, c.pos), fun _ => rfl, fun _ => rfl⟩

/-- `PackedCoord ng d` is encoded as the pair of its group and its position. -/
instance PackedCoord.instEncodablePlan (ng d : ℕ) : Encodable (PackedCoord ng d) :=
  Encodable.ofEquiv (Fin ng × Fin d)
    ⟨fun c => (c.group, c.pos), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

namespace PEdge

variable {K ι : Type} [Field K] [Fintype K] {p : ℕ} [ExpChar K p] {S0 : Subfield K}

/-- **The logical coordinates of a list of edges**: the cells, then each edge's child
coordinates, the first edge's outermost. -/
def Logical (ι : Type) : List (PEdge K ι p S0) → Type
  | [] => ι
  | e :: es => Logical ι es ⊕ PackedCoord e.ng e.d

instance : (es : List (PEdge K ι p S0)) → [Fintype ι] → Fintype (Logical ι es)
  | [], _ => inferInstanceAs (Fintype ι)
  | e :: es, _ => @instFintypeSum _ _ (instFintypeLogical es) _

instance : (es : List (PEdge K ι p S0)) → [DecidableEq ι] → DecidableEq (Logical ι es)
  | [], h => h
  | e :: es, _ => @instDecidableEqSum _ _ (instDecidableEqLogical es) _

/-- The logical coordinates are encoded as nested sums. -/
instance : (es : List (PEdge K ι p S0)) → [Encodable ι] → Encodable (Logical ι es)
  | [], h => h
  | e :: es, _ => @Sum.encodable _ _ (instEncodableLogical es) _

/-- **A cell as a logical coordinate.** -/
def cellIn : (es : List (PEdge K ι p S0)) → ι → Logical ι es
  | [], i => i
  | _ :: es, i => .inl (cellIn es i)

/-- **Slot `s` of the child of edge `j`** (relative to the list) as a logical coordinate:
coordinate `s mod d` of group `⌊s / d⌋`, the cell `fb` out of range. -/
def slotAt (fb : ι) : (es : List (PEdge K ι p S0)) → ℕ → ℕ → Logical ι es
  | [], _, _ => fb
  | e :: es, 0, s =>
    if h : s < e.ng * e.d then
      .inr ⟨⟨s / e.d, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)⟩,
        ⟨s % e.d, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)⟩⟩
    else .inl (cellIn es fb)
  | _ :: es, j + 1, s => .inl (slotAt fb es j s)

/-- **The words of an edge** at absolute position `pos` over the later edges `es`: a root child's
committed words, the parent's slots otherwise. -/
def word (fb : ι) (pos : ℕ) (e : PEdge K ι p S0) (es : List (PEdge K ι p S0)) :
    Fin e.ng → Logical ι es := fun g =>
  match e.parent with
  | none => cellIn es (e.rootWord g)
  | some j => slotAt fb es (j - (pos + 1)) (e.slot g)

/-- **The stage of an edge** over the later edges: the edge's basis, its words, its masks on its
mask cells. -/
def stage (fb : ι) (pos : ℕ) (e : PEdge K ι p S0) (es : List (PEdge K ι p S0)) :
    @Stage K ι _ p e.m e.d e.kit.e e.ng _ (Logical ι es) where
  basis := e.kit.basis
  word := word fb pos e es
  masks := e.kit.masks.scheme e.maskPre e.maskOwn

/-! ### The nodes the claims read -/

/-- **The node of a logical coordinate** from absolute position `pos` on: the position of the edge
whose child holds it, none for a cell. -/
def nodeOf : (pos : ℕ) → (es : List (PEdge K ι p S0)) → Logical ι es → Option ℕ
  | _, [], _ => none
  | pos, _ :: es, .inl y => nodeOf (pos + 1) es y
  | pos, _ :: _, .inr _ => some pos

/-- **A logical coordinate at a node of `N`**, or a cell. -/
def InNodes (pos : ℕ) (es : List (PEdge K ι p S0)) (N : Finset ℕ) (z : Logical ι es) : Prop :=
  ∀ n, nodeOf pos es z = some n → n ∈ N

/-- **A node is a position of the list.** -/
theorem nodeOf_lt : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (z : Logical ι es) → ∀ n,
    nodeOf pos es z = some n → n < pos + es.length
  | _, [], _, _, h => by cases h
  | pos, _ :: es, .inl y, n, h => by
    have := nodeOf_lt (pos + 1) es y n h
    simp only [List.length_cons]
    omega
  | pos, _ :: _, .inr _, n, h => by
    cases h
    simp

/-- **Every coordinate is at a node below `pos + |es|`**, or a cell. -/
theorem inNodes_range (pos : ℕ) (es : List (PEdge K ι p S0)) (z : Logical ι es) :
    InNodes pos es (Finset.range (pos + es.length)) z := fun n h =>
  Finset.mem_range.2 (nodeOf_lt pos es z n h)

/-- A cell is at no node. -/
theorem nodeOf_cellIn : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (i : ι) →
    nodeOf pos es (cellIn es i) = none
  | _, [], _ => rfl
  | pos, _ :: es, i => nodeOf_cellIn (pos + 1) es i

/-- A cell is in every set of nodes. -/
theorem inNodes_cellIn (pos : ℕ) (es : List (PEdge K ι p S0)) (N : Finset ℕ) (i : ι) :
    InNodes pos es N (cellIn es i) := fun n h => by
  rw [nodeOf_cellIn] at h
  cases h

/-- **Slot `s` of the child of edge `j`** is at node `pos + j`, or is the spare cell. -/
theorem nodeOf_slotAt (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (j s : ℕ) →
    ∀ n, nodeOf pos es (slotAt fb es j s) = some n → n = pos + j
  | _, [], _, _, _, h => by cases h
  | pos, e :: es, 0, s, n, h => by
    by_cases hs : s < e.ng * e.d
    · simp only [slotAt, hs, ↓reduceDIte, nodeOf, Option.some.injEq] at h
      omega
    · simp only [slotAt, hs, ↓reduceDIte, nodeOf, nodeOf_cellIn, reduceCtorEq] at h
  | pos, _ :: es, j + 1, s, n, h => by
    have := nodeOf_slotAt fb (pos + 1) es j s n h
    omega

/-- **The node of a slot**: the edge's when the slot is in range, none otherwise. -/
theorem nodeOf_slotAt_eq (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (j s : ℕ) →
    nodeOf pos es (slotAt fb es j s) =
      if h : j < es.length then (if s < es[j].ng * es[j].d then some (pos + j) else none) else none
  | pos, [], j, s => by simp [slotAt, nodeOf]
  | pos, e :: es, 0, s => by
    by_cases hs : s < e.ng * e.d
    · simp [slotAt, hs, nodeOf]
    · simp [slotAt, hs, nodeOf, nodeOf_cellIn]
  | pos, e :: es, j + 1, s => by
    rw [show slotAt fb (e :: es) (j + 1) s = .inl (slotAt fb es j s) from rfl, nodeOf,
      nodeOf_slotAt_eq fb (pos + 1) es j s]
    simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ]
    split_ifs <;> simp [Nat.add_right_comm, Nat.add_assoc, Nat.add_comm 1]

/-- **The nodes an edge's words lie at**: the parent's, none for a root child. -/
def parentNodes (pos : ℕ) (e : PEdge K ι p S0) : Finset ℕ :=
  match e.parent with
  | none => ∅
  | some j => {pos + 1 + (j - (pos + 1))}

/-- **An edge's words lie at its parent.** -/
theorem inNodes_word (fb : ι) (pos : ℕ) (e : PEdge K ι p S0) (es : List (PEdge K ι p S0))
    (g : Fin e.ng) : InNodes (pos + 1) es (parentNodes pos e) (word fb pos e es g) := by
  intro n hn
  unfold word at hn
  unfold parentNodes
  split at hn
  · rename_i h
    rw [nodeOf_cellIn] at hn
    cases hn
  · rename_i j h
    simp only [h, Finset.mem_singleton]
    exact nodeOf_slotAt fb (pos + 1) es _ _ n hn

/-! ### The routed tree -/

/-- **The routing at the edge at position `pos`**: the claims whose nodes hold `pos` touch
(`StageRouting.Routing.ofTouch`). -/
def routeAt {nc : ℕ} (pos : ℕ) (r : Fin nc → Finset ℕ) : StageRouting.Routing nc :=
  StageRouting.Routing.ofTouch fun c => decide (pos ∈ r c)

/-- **The nodes the claims after an edge's stage read**: the remainder those of the touching
claims, each measurement row the edge's parent, each passing claim its own. -/
def nextReads {nc : ℕ} (pos : ℕ) (e : PEdge K ι p S0) (r : Fin nc → Finset ℕ) :
    Fin (e.d + 1 + (routeAt pos r).np) → Finset ℕ :=
  Fin.append
    (Fin.cases (Finset.univ.biUnion fun i => r ((routeAt pos r).route.split.symm (.inl i)))
      fun _ => parentNodes pos e)
    fun i => r ((routeAt pos r).route.split.symm (.inr i))

variable [Fintype ι]

/-- **The tree in processing order** from the edge at absolute position `pos` on, for `nc` claims
reading the nodes `r` (`tree_zk.h`, `TreePlan::route`): every edge's stage combines the claims
whose nodes hold it, with no combination when at most one does, and passes the others
(`RingSwitching.Tree.route` at `routeAt`); the claims after it read `nextReads`. -/
def path (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (Fin nc → Finset ℕ) → RingSwitching.Tree K p ι (Logical ι es) nc
  | _, [], _, _ => .nil
  | pos, e :: es, _, r =>
    letI := e.kit.order
    RingSwitching.Tree.route (stage fb pos e es) (routeAt pos r).route
      (path fb (pos + 1) es (e.d + 1 + (routeAt pos r).np) (nextReads pos e r))

/-- **The tree combines at most once per edge.** -/
theorem combinations_path_le (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) → (path fb pos es nc r).combinations ≤ es.length
  | _, [], _, _ => le_rfl
  | pos, e :: es, _, r => by
    have h1 := combinations_path_le fb (pos + 1) es _ (nextReads pos e r)
    have h2 : (routeAt pos r).route.combinations ≤ 1 :=
      StageRouting.Routing.combinations_ofTouch_le _
    change _ + (routeAt pos r).route.combinations ≤ es.length + 1
    omega

/-- **The tree's level is that of its path at any claims.** -/
theorem path_level_eq (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc nc' : ℕ) →
    (r : Fin nc → Finset ℕ) → (r' : Fin nc' → Finset ℕ) →
    (path fb pos es nc r).level = (path fb pos es nc' r').level
  | _, [], _, _, _, _ => rfl
  | pos, e :: es, _, _, r, r' => by
    letI := e.kit.order
    change (stage fb pos e es).level (path fb (pos + 1) es _ (nextReads pos e r)).level =
      (stage fb pos e es).level (path fb (pos + 1) es _ (nextReads pos e r')).level
    rw [path_level_eq fb (pos + 1) es _ _ (nextReads pos e r) (nextReads pos e r')]

/-- A cell's coordinate in the tree's level is the cell. -/
theorem level_cell (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) → (i : ι) → (path fb pos es nc r).level.cell i = cellIn es i
  | _, [], _, _, _ => rfl
  | pos, e :: es, _, r, i => by
    letI := e.kit.order
    change Sum.inl ((path fb (pos + 1) es _ (nextReads pos e r)).level.cell i) = _
    rw [level_cell fb (pos + 1) es _ _ i]
    rfl

/-- **The tree's routing obligation from the claims' nodes**: when every claim reads only cells
and coordinates at its nodes `r`, every edge's passing claims read no coordinate of its child, at
every stage. -/
theorem routes_path [DecidableEq K] [DecidableEq ι] {Pub Wit : Type}
    {cells : Wit → ι → K} (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) →
    (M : FieldProof.MaskedReduction K ι Pub Wit cells (Logical ι es) nc) →
    M.ReadsOnly (fun c => InNodes pos es (r c)) → (path fb pos es nc r).Routes M
  | _, [], _, _, _, _ => trivial
  | pos, e :: es, nc, r, M, h => by
    letI := e.kit.order
    refine ⟨FieldProof.MaskedReduction.passingAvoid_of_readsOnly h _ fun i q hq => ?_,
      routes_path fb (pos + 1) es _ (nextReads pos e r) _
        ((h.routedStage _ (stage fb pos e es) _).mono fun c y hy => ?_)⟩
    · have hr := hq pos rfl
      have ht := StageRouting.Routing.ofTouch_inr (fun c => decide (pos ∈ r c)) i
      simp only [decide_eq_false_iff_not] at ht
      exact ht hr
    · refine Fin.addCases (fun c hy => ?_) (fun i hy => ?_) c hy
      · simp only [StageRouting.outSupport, Fin.append_left] at hy
        rw [nextReads, Fin.append_left]
        refine Fin.cases (fun hy => ?_) (fun k hy => ?_) c hy
        · simp only [Fin.cases_zero] at hy ⊢
          rcases hy with ⟨i, hi⟩ | ⟨i, rfl⟩
          · intro n hn
            exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi n hn⟩
          · rw [level_cell]
            exact inNodes_cellIn _ _ _ _
        · simp only [Fin.cases_succ] at hy ⊢
          rcases hy with ⟨g, rfl⟩ | ⟨i, rfl⟩
          · exact inNodes_word fb pos e es g
          · rw [level_cell]
            exact inNodes_cellIn _ _ _ _
      · simp only [StageRouting.outSupport, Fin.append_right] at hy
        rw [nextReads, Fin.append_right]
        exact hy

/-- The field of a cell is `K`. -/
theorem field_cellIn (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) → (i : ι) → (path fb pos es nc r).field (cellIn es i) = ⊤
  | _, [], _, _, _ => rfl
  | pos, e :: es, _, r, i => field_cellIn fb (pos + 1) es _ (nextReads pos e r) i

/-- **The field of a slot** of the child of edge `j`, in range: `F_{p^m}` of that edge. -/
theorem field_slotAt (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) → (j s : ℕ) → (hj : j < es.length) → s < es[j].ng * es[j].d →
    (path fb pos es nc r).field (slotAt fb es j s) = fixedField K p es[j].m
  | _, [], _, _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | pos, e :: es, _, _, 0, s, _, hs => by
    simp only [List.getElem_cons_zero] at hs ⊢
    simp only [slotAt, hs, ↓reduceDIte]
    rfl
  | pos, e :: es, _, r, j + 1, s, hj, hs =>
    field_slotAt fb (pos + 1) es _ (nextReads pos e r) j s (Nat.lt_of_succ_lt_succ hj) hs

/-- **The shape condition of a list of edges** from absolute position `pos` on, in a field of degree
`n` over `F_p`: a root child spans the field (`m d = n`); another edge's parent is a later edge
whose child has degree `m d`, whose slots hold the edge's groups; every edge has positive relative
degree. Decidable. -/
def Shaped (n : ℕ) : (pos : ℕ) → List (PEdge K ι p S0) → Prop
  | _, [] => True
  | pos, e :: es =>
    (match e.parent with
      | none => e.m * e.d = n
      | some j => pos < j ∧ ∃ h : j - (pos + 1) < es.length,
          es[j - (pos + 1)].m = e.m * e.d ∧
            ∀ g, e.slot g < es[j - (pos + 1)].ng * es[j - (pos + 1)].d) ∧
      Shaped n (pos + 1) es

/-- **The shape condition by position** (`Shaped` read at absolute positions): a root child spans
the field, another edge's parent is a later edge whose child has degree `m d` and whose slots hold
the edge's groups. -/
def ShapedAt (n : ℕ) (es0 : List (PEdge K ι p S0)) : Prop :=
  ∀ (b : ℕ) (hb : b < es0.length),
    match es0[b].parent with
    | none => es0[b].m * es0[b].d = n
    | some j => b < j ∧ ∃ hj : j < es0.length, es0[j].m = es0[b].m * es0[b].d ∧
        ∀ g : Fin es0[b].ng, es0[b].slot g < es0[j].ng * es0[j].d

theorem eq_getElem_of_drop {es0 es : List (PEdge K ι p S0)} {e : PEdge K ι p S0} {pos : ℕ}
    (hes : e :: es = es0.drop pos) : ∃ h : pos < es0.length, e = es0[pos] ∧
      es = es0.drop (pos + 1) := by
  have hlen : pos < es0.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at hes
    exact List.cons_ne_nil _ _ hes
  refine ⟨hlen, ?_, ?_⟩
  · have := congrArg (fun l => l[0]?) hes
    simp only [List.getElem?_cons_zero, List.getElem?_drop, Nat.add_zero,
      List.getElem?_eq_getElem hlen, Option.some.injEq] at this
    exact this
  · rw [← List.drop_drop, ← hes]
    rfl

/-- **The shape condition by position gives the shape condition** of every suffix. -/
theorem shaped_of_shapedAt {n : ℕ} {es0 : List (PEdge K ι p S0)} (h : ShapedAt n es0) :
    (pos : ℕ) → (es : List (PEdge K ι p S0)) → es = es0.drop pos → Shaped n pos es
  | _, [], _ => trivial
  | pos, e :: es, hes => by
    obtain ⟨hlen, he, hrest⟩ := eq_getElem_of_drop hes
    refine ⟨?_, shaped_of_shapedAt h (pos + 1) es hrest⟩
    have hb := h pos hlen
    rw [← he] at hb
    revert hb
    cases hp : e.parent with
    | none => exact id
    | some j =>
      rintro ⟨hpj, hj, hm, hslot⟩
      have hjr : j - (pos + 1) < es.length := by
        rw [hrest, List.length_drop]
        omega
      have hget : es[j - (pos + 1)] = es0[j] := by
        simp only [hrest, List.getElem_drop]
        congr 1
        omega
      exact ⟨hpj, hjr, by rw [hget, hm], fun g => by rw [hget]; exact hslot g⟩

/-- **The parent of an edge in a shaped list** is a later edge whose child has degree `m d`. -/
theorem ShapedAt.parent {n : ℕ} {es0 : List (PEdge K ι p S0)} (h : ShapedAt n es0) {b : ℕ}
    (hb : b < es0.length) {a : ℕ} (hpar : es0[b].parent = some a) :
    b < a ∧ ∃ ha : a < es0.length, es0[a].m = es0[b].m * es0[b].d := by
  have hb' := h b hb
  rw [hpar] at hb'
  exact ⟨hb'.1, hb'.2.1, hb'.2.2.1⟩

/-- **In a shaped list, a parent lies after its child**, in absolute positions. -/
theorem shaped_parent_lt {n : ℕ} : {pos : ℕ} → {es : List (PEdge K ι p S0)} → Shaped n pos es →
    ∀ (b : ℕ) (hb : b < es.length) {a : ℕ}, es[b].parent = some a → pos + b < a
  | _, [], _, _, hb, _, _ => absurd hb (Nat.not_lt_zero _)
  | pos, e :: es, ⟨he, _⟩, 0, _, a, hp => by
    simp only [List.getElem_cons_zero] at hp
    rw [hp] at he
    exact he.1
  | pos, e :: es, ⟨_, hs⟩, b + 1, hb, a, hp => by
    have := shaped_parent_lt hs b (Nat.lt_of_succ_lt_succ hb) hp
    omega

/-- **Every mask prefix cell satisfies `pre`.** -/
def MasksIn (pre : ι → Prop) (es : List (PEdge K ι p S0)) : Prop :=
  ∀ e ∈ es, ∀ j, pre (e.maskPre j)

/-- **A shaped list of edges is nested**, in a field whose degree-`n` subfield is `K`. -/
theorem nested_path (fb : ι) {n : ℕ} (htop : fixedField K p n = ⊤) :
    (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) → (r : Fin nc → Finset ℕ) →
      Shaped n pos es → (path fb pos es nc r).Nested
  | _, [], _, _, _ => trivial
  | pos, e :: es, _, r, ⟨he, hs⟩ => by
    refine ⟨fun g => ?_, nested_path fb htop (pos + 1) es _ (nextReads pos e r) hs⟩
    change (path fb (pos + 1) es _ (nextReads pos e r)).field (word fb pos e es g) ≤
      e.kit.basis.top
    rw [e.kit.top_eq]
    unfold word
    split
    · rename_i hp
      rw [hp] at he
      rw [field_cellIn, he, htop]
    · rename_i j hp
      rw [hp] at he
      obtain ⟨-, hj, hm, hslot⟩ := he
      rw [field_slotAt fb (pos + 1) es _ _ _ _ hj (hslot g), hm]

/-- **Every stage of a list of edges has its mode**, with the mask prefix cells satisfying
`pre`. -/
theorem modes_path (fb : ι) (pre : ι → Prop) :
    (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) → (r : Fin nc → Finset ℕ) →
      MasksIn pre es → (path fb pos es nc r).Modes S0 pre
  | _, [], _, _, _ => trivial
  | pos, e :: es, _, r, h =>
    ⟨e.kit.masks.mode pre e.maskPre e.maskOwn (h e (List.mem_cons_self ..)),
      modes_path fb pre (pos + 1) es _ (nextReads pos e r) fun e' he' =>
        h e' (List.mem_cons_of_mem _ he')⟩

/-- **A shaped list of edges is a member of the class** `𝒯(K, S0)` (`TreeSpec`). -/
def treeSpec (fb : ι) {n : ℕ} (htop : fixedField K p n = ⊤) (pre : ι → Prop)
    (es : List (PEdge K ι p S0)) (nc : ℕ) (r : Fin nc → Finset ℕ) (hs : ShapedAt n es)
    (hpre : MasksIn pre es) : TreeSpec K p ι S0 pre (Logical ι es) nc where
  path := path fb 0 es nc r
  nested := nested_path fb htop 0 es nc r (shaped_of_shapedAt hs 0 es rfl)
  modes := modes_path fb pre 0 es nc r hpre

/-! ### Consistent assignments -/

/-- **A consistent logical assignment** from absolute position `pos` on: each child coordinate is
the decoded coordinate of its word (`StageBasis.coord`). -/
def Consistent (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (Logical ι es → K) → Prop
  | _, [], _ => True
  | pos, e :: es, z =>
    Consistent fb (pos + 1) es (z ∘ Sum.inl) ∧
      ∀ c : PackedCoord e.ng e.d, z (.inr c) = e.kit.basis.coord (z (.inl (word fb pos e es c.group)))
        c.pos

/-- The cells of a logical assignment. -/
theorem comp_cellIn_cons (e : PEdge K ι p S0) (es : List (PEdge K ι p S0))
    (z : Logical ι (e :: es) → K) : z ∘ cellIn (e :: es) = (z ∘ Sum.inl) ∘ cellIn es :=
  rfl

/-- **A consistent assignment is the logical assignment of its cells.** -/
theorem level_view_of_consistent (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) → (z : Logical ι es → K) → Consistent fb pos es z →
      (path fb pos es nc r).level.view (z ∘ cellIn es) = z
  | _, [], _, _, _, _ => rfl
  | pos, e :: es, _, r, z, ⟨hz, hc⟩ => by
    have ih := level_view_of_consistent fb (pos + 1) es _ (nextReads pos e r) (z ∘ Sum.inl) hz
    funext y
    rcases y with y | c
    · change (path fb (pos + 1) es _ (nextReads pos e r)).level.view
        ((z ∘ Sum.inl) ∘ cellIn es) y = _
      rw [ih]
      rfl
    · change e.kit.basis.coord ((path fb (pos + 1) es _ (nextReads pos e r)).level.view
        ((z ∘ Sum.inl) ∘ cellIn es) (word fb pos e es c.group)) c.pos = _
      rw [ih, hc c]
      rfl

/-- **The word of group `g` of the edge at position `b`** of `es` (relative), from absolute
position `pos` on: a root child's committed word, the parent's slot otherwise. -/
def wordRel (fb : ι) (pos : ℕ) (es : List (PEdge K ι p S0)) (b : ℕ) (hb : b < es.length)
    (g : Fin es[b].ng) : Logical ι es :=
  match es[b].parent with
  | none => cellIn es (es[b].rootWord g)
  | some a => slotAt fb es (a - pos) (es[b].slot g)

/-- **A consistent assignment at a slot is the decoded coordinate of its word**: slot `g d + j` of
the child of edge `b` is coordinate `j` of group `g`'s word, on a shaped list. -/
theorem consistent_slotAt (fb : ι) {n : ℕ} : (pos : ℕ) → (es : List (PEdge K ι p S0)) →
    Shaped n pos es → (z : Logical ι es → K) → Consistent fb pos es z →
    ∀ (b : ℕ) (hb : b < es.length) (g : Fin es[b].ng) (j : Fin es[b].d),
      z (slotAt fb es b (g * es[b].d + j)) = es[b].kit.basis.coord (z (wordRel fb pos es b hb g)) j
  | _, [], _, _, _, _, hb, _, _ => absurd hb (Nat.not_lt_zero _)
  | pos, e :: es, ⟨he, hs⟩, z, ⟨hz, hc⟩, 0, h0, ⟨g, hg⟩, ⟨j, hj⟩ => by
    change g < e.ng at hg
    change j < e.d at hj
    have hlt : g * e.d + j < e.ng * e.d :=
      calc g * e.d + j < g * e.d + e.d := by omega
        _ = (g + 1) * e.d := by ring
        _ ≤ e.ng * e.d := Nat.mul_le_mul_right _ hg
    have hd : 0 < e.d := by omega
    have hdiv : (g * e.d + j) / e.d = g := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (g * e.d + j) % e.d = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    change z (slotAt fb (e :: es) 0 (g * e.d + j)) =
      e.kit.basis.coord (z (wordRel fb pos (e :: es) 0 h0 ⟨g, hg⟩)) ⟨j, hj⟩
    simp only [slotAt, hlt, ↓reduceDIte]
    have hcoord : ∀ h1 h2, (⟨⟨(g * e.d + j) / e.d, h1⟩, ⟨(g * e.d + j) % e.d, h2⟩⟩ :
        PackedCoord e.ng e.d) = ⟨⟨g, hg⟩, ⟨j, hj⟩⟩ := fun _ _ => by
      ext
      · exact hdiv
      · exact hmod
    rw [hcoord, hc ⟨⟨g, hg⟩, ⟨j, hj⟩⟩]
    congr 2
    change Sum.inl (word fb pos e es ⟨g, hg⟩) = wordRel fb pos (e :: es) 0 h0 ⟨g, hg⟩
    unfold word wordRel
    simp only [List.getElem_cons_zero]
    split
    · rfl
    · rename_i a hp
      rw [hp] at he
      obtain ⟨hpa, -⟩ := he
      obtain ⟨k, hk⟩ : ∃ k, a - pos = k + 1 := ⟨a - pos - 1, by omega⟩
      rw [hk, show a - (pos + 1) = k by omega]
      rfl
  | pos, e :: es, ⟨_, hs⟩, z, ⟨hz, _⟩, b + 1, hb, g, j => by
    have hb' : b < es.length := Nat.lt_of_succ_lt_succ hb
    have ih := consistent_slotAt fb (pos + 1) es hs (z ∘ Sum.inl) hz b hb' g j
    have hw : Sum.inl (wordRel fb (pos + 1) es b hb' g) = wordRel fb pos (e :: es) (b + 1) hb g := by
      unfold wordRel
      simp only [List.getElem_cons_succ]
      cases hp : es[b].parent with
      | none => rfl
      | some a =>
        have hpa : pos + 1 + b < a := shaped_parent_lt hs b hb' hp
        obtain ⟨k, hk⟩ : ∃ k, a - pos = k + 1 := ⟨a - pos - 1, by omega⟩
        simp only
        rw [hk, show a - (pos + 1) = k by omega]
        rfl
    refine ih.trans ?_
    rw [← hw]
    rfl

/-- **A consistent assignment at a slot of a non-root edge** given by an equation `es[b] = e`:
slot `g d + j` of `e`'s child is coordinate `j` of the parent's slot holding group `g`. -/
theorem consistent_slotAt_eq (fb : ι) {n pos : ℕ} {es : List (PEdge K ι p S0)}
    (hs : Shaped n pos es) {z : Logical ι es → K} (hz : Consistent fb pos es z) {b : ℕ}
    (hb : b < es.length) {e : PEdge K ι p S0} (he : es[b] = e) {a : ℕ} (hpa : e.parent = some a)
    (g : Fin e.ng) (j : Fin e.d) :
    z (slotAt fb es b (g * e.d + j)) = e.kit.basis.coord (z (slotAt fb es (a - pos) (e.slot g))) j := by
  subst he
  have := consistent_slotAt fb pos es hs z hz b hb g j
  unfold wordRel at this
  simp only [hpa] at this
  exact this

/-- **The logical assignment of any cells is consistent.** -/
theorem consistent_level_view (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) → (x : ι → K) → Consistent fb pos es ((path fb pos es nc r).level.view x)
  | _, [], _, _, _ => trivial
  | pos, e :: es, _, r, x =>
    ⟨consistent_level_view fb (pos + 1) es _ (nextReads pos e r) x, fun _ => rfl⟩

/-- The logical assignment reads the cells at their coordinates. -/
theorem level_view_cellIn (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) → (x : ι → K) → (i : ι) →
    (path fb pos es nc r).level.view x (cellIn es i) = x i
  | _, [], _, _, _, _ => rfl
  | pos, e :: es, _, r, x, i => level_view_cellIn fb (pos + 1) es _ (nextReads pos e r) x i

/-! ### The honest logical assignment -/

/-- **The parent's word of a group** in an assignment of the slots `vals` and the cells `cells`:
a root child's committed word, the parent's slot otherwise. -/
def wordVal (vals : ℕ → ℕ → K) (cells : ι → K) (e : PEdge K ι p S0) (g : Fin e.ng) : K :=
  match e.parent with
  | none => cells (e.rootWord g)
  | some j => vals j (e.slot g)

/-- **The logical assignment of the slot values `vals` and the cells `cells`** from absolute
position `pos` on: coordinate `(g, j)` of the edge at position `a` is slot `g d + j` of its child. -/
def fill (vals : ℕ → ℕ → K) (cells : ι → K) : (pos : ℕ) → (es : List (PEdge K ι p S0)) →
    Logical ι es → K
  | _, [] => cells
  | pos, e :: es => Sum.elim (fill vals cells (pos + 1) es) fun c => vals pos (c.group * e.d + c.pos)

theorem fill_cellIn (vals : ℕ → ℕ → K) (cells : ι → K) : (pos : ℕ) →
    (es : List (PEdge K ι p S0)) → (i : ι) → fill vals cells pos es (cellIn es i) = cells i
  | _, [], _ => rfl
  | pos, _ :: es, i => fill_cellIn vals cells (pos + 1) es i

theorem fill_slotAt (fb : ι) (vals : ℕ → ℕ → K) (cells : ι → K) : (pos : ℕ) →
    (es : List (PEdge K ι p S0)) → (j s : ℕ) → (hj : j < es.length) → s < es[j].ng * es[j].d →
    fill vals cells pos es (slotAt fb es j s) = vals (pos + j) s
  | _, [], _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | pos, e :: es, 0, s, _, hs => by
    simp only [List.getElem_cons_zero] at hs
    have hd : 0 < e.d := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hs
    simp only [slotAt, hs, ↓reduceDIte, fill, Sum.elim_inr, Nat.add_zero]
    rw [Nat.mul_comm, Nat.div_add_mod]
  | pos, e :: es, j + 1, s, hj, hs => by
    rw [show pos + (j + 1) = pos + 1 + j by omega]
    exact fill_slotAt fb vals cells (pos + 1) es j s (Nat.lt_of_succ_lt_succ hj) hs

/-- **The words decode to the slots** from absolute position `pos` on: slot `g d + j` of each
edge's child is coordinate `j` of the group's word (`wordVal`). -/
def WordsOk (vals : ℕ → ℕ → K) (cells : ι → K) : (pos : ℕ) → List (PEdge K ι p S0) → Prop
  | _, [] => True
  | pos, e :: es =>
    (∀ (g : Fin e.ng) (j : Fin e.d),
      vals pos (g * e.d + j) = e.kit.basis.coord (wordVal vals cells e g) j) ∧
      WordsOk vals cells (pos + 1) es

/-- **The assignment of slots whose words decode to them is consistent**, on a shaped list. -/
theorem consistent_fill (fb : ι) {n : ℕ} (vals : ℕ → ℕ → K) (cells : ι → K) : (pos : ℕ) →
    (es : List (PEdge K ι p S0)) → Shaped n pos es → WordsOk vals cells pos es →
      Consistent fb pos es (fill vals cells pos es)
  | _, [], _, _ => trivial
  | pos, e :: es, ⟨he, hs⟩, ⟨hw, hws⟩ => by
    refine ⟨consistent_fill fb vals cells (pos + 1) es hs hws, fun c => ?_⟩
    change vals pos (c.group * e.d + c.pos) = _
    rw [hw c.group c.pos]
    congr 1
    change wordVal vals cells e c.group = fill vals cells (pos + 1) es (word fb pos e es c.group)
    unfold wordVal word
    split
    · exact (fill_cellIn vals cells (pos + 1) es _).symm
    · rename_i j hp
      rw [hp] at he
      obtain ⟨hpj, hj, -, hslot⟩ := he
      rw [fill_slotAt fb vals cells (pos + 1) es _ _ hj (hslot c.group)]
      congr 1
      omega

/-- **The words decode to the slots, by position**: for the edge at every position `a` of `es0`,
slot `g d + j` of its child is coordinate `j` of the group's word. -/
def WordsAt (es0 : List (PEdge K ι p S0)) (vals : ℕ → ℕ → K) (cells : ι → K) : Prop :=
  ∀ (a : ℕ) (h : a < es0.length) (g : Fin es0[a].ng) (j : Fin es0[a].d),
    vals a (g * es0[a].d + j) = es0[a].kit.basis.coord (wordVal vals cells es0[a] g) j

theorem wordsOk_drop (es0 : List (PEdge K ι p S0)) (vals : ℕ → ℕ → K) (cells : ι → K)
    (h : WordsAt es0 vals cells) : (pos : ℕ) → (es : List (PEdge K ι p S0)) →
      es = es0.drop pos → WordsOk vals cells pos es
  | _, [], _ => trivial
  | pos, e :: es, hes => by
    obtain ⟨hlen, he, hrest⟩ := eq_getElem_of_drop hes
    refine ⟨fun g j => ?_, wordsOk_drop es0 vals cells h (pos + 1) es hrest⟩
    subst he
    exact h pos hlen g j

/-- **The assignment of slots whose words decode to them is the logical assignment of its
cells**, on a shaped list (`level_view_of_consistent`). -/
theorem level_view_fill (fb : ι) {n : ℕ} (es0 : List (PEdge K ι p S0)) (nc : ℕ)
    (r : Fin nc → Finset ℕ) (vals : ℕ → ℕ → K) (cells : ι → K) (hs : ShapedAt n es0)
    (hw : WordsAt es0 vals cells) :
    (path fb 0 es0 nc r).level.view (fill vals cells 0 es0 ∘ cellIn es0) = fill vals cells 0 es0 :=
  level_view_of_consistent fb 0 es0 nc r _
    (consistent_fill fb vals cells 0 es0 (shaped_of_shapedAt hs 0 es0 rfl) (wordsOk_drop es0 vals cells hw 0 es0 rfl))

/-! ### The honest slot values -/

/-- **The honest slot values** of the edges `es0`: slot `s` of the child of the edge at position
`a` holds its own value `own a s`, unless it holds group `g` of a deeper edge `b` (`groupAt`), a
packed word of `b`'s child slots (`StageBasis.pack`), or a given word (`given b g`: a word of the
parent's own, whose coordinates are the child's own values). -/
def slotVal (es0 : List (PEdge K ι p S0)) (own : ℕ → ℕ → K) (given : ℕ → ℕ → Bool)
    (groupAt : ℕ → ℕ → Option (ℕ × ℕ)) (a s : ℕ) : K :=
  match groupAt a s with
  | some (b, g) =>
    if h : b < a then
      match es0[b]? with
      | some eb =>
        if given b g then own a s
        else eb.kit.basis.pack fun j => slotVal es0 own given groupAt b (g * eb.d + j)
      | none => own a s
    else own a s
  | none => own a s
termination_by a

/-- **The honest cells**: each root child's committed word the packed word of its group
(`rootAt`), every other cell its own value `base`. -/
def cellVal (es0 : List (PEdge K ι p S0)) (own : ℕ → ℕ → K) (given : ℕ → ℕ → Bool)
    (groupAt : ℕ → ℕ → Option (ℕ × ℕ)) (rootAt : ι → Option (ℕ × ℕ)) (base : ι → K) (i : ι) : K :=
  match rootAt i with
  | some (b, g) =>
    match es0[b]? with
    | some eb => eb.kit.basis.pack fun j => slotVal es0 own given groupAt b (g * eb.d + j)
    | none => base i
  | none => base i

/-- **The layout of the honest slots** (facts about the placement): every group of a non-root
edge is found at its parent's slot, and every group of a root child at its committed word; the
groups found are groups of children of the slot's node; the own values lie in their nodes'
subfields; a given group's child slots hold the coordinates of the parent's own value and no
deeper group. -/
structure FillSpec (es0 : List (PEdge K ι p S0)) (own : ℕ → ℕ → K) (given : ℕ → ℕ → Bool)
    (groupAt : ℕ → ℕ → Option (ℕ × ℕ)) (rootAt : ι → Option (ℕ × ℕ)) : Prop where
  /-- Every group of a non-root edge is found at its parent's slot. -/
  find : ∀ (b : ℕ) (hb : b < es0.length) (j : ℕ), es0[b].parent = some j →
    ∀ g : Fin es0[b].ng, groupAt j (es0[b].slot g) = some (b, (g : ℕ))
  /-- Every group of a root child is found at its committed word. -/
  findRoot : ∀ (b : ℕ) (hb : b < es0.length), es0[b].parent = none →
    ∀ g : Fin es0[b].ng, rootAt (es0[b].rootWord g) = some (b, (g : ℕ)) ∧ given b g = false
  /-- A found group belongs to a child of the slot's node, below the parent. -/
  child : ∀ a s b g, groupAt a s = some (b, g) → ∃ hb : b < es0.length,
    es0[b].parent = some a ∧ g < es0[b].ng
  /-- The own values lie in their nodes' subfields. -/
  own_mem : ∀ (a : ℕ) (ha : a < es0.length) s, own a s ∈ fixedField K p es0[a].m
  /-- A given group's child slots hold the coordinates of the parent's own value. -/
  given_coord : ∀ (b : ℕ) (hb : b < es0.length) (j : ℕ), es0[b].parent = some j →
    ∀ g : Fin es0[b].ng, given b g = true → ∀ i : Fin es0[b].d,
      slotVal es0 own given groupAt b (g * es0[b].d + i) = es0[b].kit.basis.coord (own j (es0[b].slot g)) i

theorem slotVal_eq (es0 : List (PEdge K ι p S0)) (own : ℕ → ℕ → K) (given : ℕ → ℕ → Bool)
    (groupAt : ℕ → ℕ → Option (ℕ × ℕ)) (a s : ℕ) :
    slotVal es0 own given groupAt a s =
      match groupAt a s with
      | some (b, g) =>
        if h : b < a then
          match es0[b]? with
          | some eb =>
            if given b g then own a s
            else eb.kit.basis.pack fun j => slotVal es0 own given groupAt b (g * eb.d + j)
          | none => own a s
        else own a s
      | none => own a s := by
  rw [slotVal]

/-- **The honest slot values lie in their nodes' subfields**, on a shaped list. -/
theorem slotVal_mem {n : ℕ} {es0 : List (PEdge K ι p S0)} {own : ℕ → ℕ → K}
    {given : ℕ → ℕ → Bool} {groupAt : ℕ → ℕ → Option (ℕ × ℕ)} {rootAt : ι → Option (ℕ × ℕ)}
    (hs : ShapedAt n es0) (hf : FillSpec es0 own given groupAt rootAt) :
    ∀ (a : ℕ) (ha : a < es0.length) s, slotVal es0 own given groupAt a s ∈ fixedField K p es0[a].m
  := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha s
    rw [slotVal_eq]
    split
    · rename_i b g hg
      obtain ⟨hb, hpar, hgl⟩ := hf.child a s b g hg
      split
      · rename_i hba
        rw [List.getElem?_eq_getElem hb]
        simp only
        split
        · exact hf.own_mem a ha s
        · obtain ⟨-, ha', hm⟩ := hs.parent hb hpar
          rw [hm, ← es0[b].kit.top_eq]
          exact es0[b].kit.basis.pack_mem fun j => ih b hba hb _
      · exact hf.own_mem a ha s
    · exact hf.own_mem a ha s

/-- **The honest slot values decode from their words** (`WordsAt`), on a shaped list with the
honest layout: a packed word decodes to its coordinates in the child's subfield
(`StageBasis.coord_pack`, `slotVal_mem`); a given word's coordinates are the child's slots
(`FillSpec.given_coord`). -/
theorem wordsAt_slotVal {n : ℕ} {es0 : List (PEdge K ι p S0)} {own : ℕ → ℕ → K}
    {given : ℕ → ℕ → Bool} {groupAt : ℕ → ℕ → Option (ℕ × ℕ)} {rootAt : ι → Option (ℕ × ℕ)}
    (base : ι → K) (hs : ShapedAt n es0) (hf : FillSpec es0 own given groupAt rootAt) :
    WordsAt es0 (slotVal es0 own given groupAt) (cellVal es0 own given groupAt rootAt base) := by
  intro b hb g j
  have hmem : ∀ i : Fin es0[b].d,
      slotVal es0 own given groupAt b (g * es0[b].d + i) ∈ fixedField K p es0[b].m :=
    fun i => slotVal_mem hs hf b hb _
  unfold wordVal
  split
  · rename_i hp
    obtain ⟨hr, -⟩ := hf.findRoot b hb hp g
    simp only [cellVal, hr, List.getElem?_eq_getElem hb]
    exact (es0[b].kit.basis.coord_pack hmem j).symm
  · rename_i a hp
    obtain ⟨hba, -, -⟩ := hs.parent hb hp
    rw [slotVal_eq es0 own given groupAt a, hf.find b hb a hp g]
    simp only [hba, ↓reduceDIte, List.getElem?_eq_getElem hb]
    split
    · rename_i hg
      exact hf.given_coord b hb a hp g hg j
    · exact (es0[b].kit.basis.coord_pack hmem j).symm

end PEdge

end GordieHowe
