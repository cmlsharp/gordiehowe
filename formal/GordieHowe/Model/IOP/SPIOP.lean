-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.IOP
public import GordieHowe.Model.IOP.CausalHVZK

@[expose] public section

/-!
# Composite IOPs with oracles

A series–parallel composite of public-coin protocols whose prover messages each consist of a
non-oracle part, read in full, and Merkle-committed oracles read at query positions: the input of
the spBCS compiler (`GordieHowe.SPBCS`, `GordieHowe/SPBCS/Setting.lean`).

* `CompIOP P`: the message structure of one component (non-oracle parts, trees, leaves, the
  decomposition `parts` of each prover message).
* `SPIOP P t Stmt`: a message structure per component, the composite verifier `V`, the query
  positions `pos` (a leaf and a position of its component) as a function of the composite
  challenges, distinct, and query locality `reads`: the decision is a function of the view
  (`GordieHowe.IOP.SPIOP.views`: the challenges, every non-oracle part and the leaves at the query positions).
* `CompWrite I k j i`: the write of a prover message, its non-oracle part and the roots of its
  trees.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec GordieHowe.QROM IOP.SPTerm
open scoped NNReal ENNReal

/-! ### Components with oracles -/

/-- **The message structure of a component**: for each prover message its non-oracle part, its
trees with their leaf types and default leaves, and its decomposition into parts. -/
structure SPBCS.CompIOP {m : ℕ} (P : ProtocolSpec m) where
  /-- The non-oracle part of each prover message, read in full. -/
  NonOracle : P.MessageIdx → Type
  /-- The number of trees of each prover message. -/
  nTrees : P.MessageIdx → ℕ
  /-- The number of leaves of each tree. -/
  nLeaves : (i : P.MessageIdx) → Fin (nTrees i) → ℕ
  /-- The leaf type of each tree. -/
  Leaf : (i : P.MessageIdx) → Fin (nTrees i) → Type
  /-- The leaf read where a leaf is missing. -/
  leafDefault : ∀ i t, Leaf i t
  /-- A prover message is its non-oracle part and the leaves of its trees. -/
  parts : ∀ i : P.MessageIdx,
    P.Type i.1 ≃ MessageParts (NonOracle i) (nTrees i) (nLeaves i) (Leaf i)

/-- **A component from the shape of each prover message** (`MessageShape`). -/
def SPBCS.CompIOP.ofShape {m : ℕ} {P : ProtocolSpec m} (sh : ∀ i : P.MessageIdx, MessageShape (P.Type i.1)) :
    CompIOP P where
  NonOracle i := (sh i).NonOracle
  nTrees i := (sh i).nTrees
  nLeaves i := (sh i).nLeaves
  Leaf i := (sh i).Leaf
  leafDefault i := (sh i).leafDefault
  parts i := (sh i).parts

/-- **A component every prover message of which is read in full.** -/
abbrev SPBCS.CompIOP.plain {m : ℕ} (P : ProtocolSpec m) : CompIOP P :=
  CompIOP.ofShape fun i => MessageShape.plain (P.Type i.1)

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}

/-- **A query position of a composite**: a leaf and a position of its component. -/
structure SPBCS.CausalPos {t : SPTerm ι} (comp : (j : ι) → CompIOP (P j)) where
  /-- The leaf. -/
  leaf : t.Leaf
  /-- The position in the leaf's component. -/
  pos : Position (P leaf.label) (comp leaf.label).nTrees (comp leaf.label).nLeaves

/-- **A composite IOP with non-oracle messages** over statements in `Stmt` (module docstring). -/
structure IOP.SPIOP (P : (j : ι) → ProtocolSpec (n j)) (t : SPTerm ι) (Stmt : Type) where
  /-- The message structure of each component. -/
  comp : (j : ι) → SPBCS.CompIOP (P j)
  /-- The composite verifier. -/
  V : Stmt → FullTr P t → Bool
  /-- The query positions at the composite challenges. -/
  pos : Chs P t → List (SPBCS.CausalPos (t := t) comp)
  /-- The query positions are distinct. -/
  pos_nodup : ∀ ch, (pos ch).Nodup
  /-- **Query locality**: the decision is a function of the view. -/
  reads : ∀ x (f f' : FullTr P t),
    (∀ c : ChIdx P t, f.challenges c = f'.challenges c) →
    (∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
      ((comp p.label).parts i (f p i.1)).nonOracle = ((comp p.label).parts i (f' p i.1)).nonOracle) →
    (∀ q ∈ pos f.challenges,
      ((comp q.leaf.label).parts q.pos.msg (f q.leaf q.pos.msg.1)).leaves q.pos.tree q.pos.leaf =
        ((comp q.leaf.label).parts q.pos.msg (f' q.leaf q.pos.msg.1)).leaves q.pos.tree
          q.pos.leaf) →
    V x f = V x f'

/-- A query position of a composite is a dependent pair of a leaf and a position. -/
def SPBCS.CausalPos.equivSigma {t : SPTerm ι} {comp : (j : ι) → CompIOP (P j)} :
    CausalPos (t := t) comp ≃
      Σ p : t.Leaf, Position (P p.label) (comp p.label).nTrees (comp p.label).nLeaves where
  toFun q := ⟨q.leaf, q.pos⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {t : SPTerm ι} {comp : (j : ι) → SPBCS.CompIOP (P j)} : DecidableEq (SPBCS.CausalPos (t := t) comp) :=
  SPBCS.CausalPos.equivSigma.decidableEq

namespace IOP.SPIOP

variable {t : SPTerm ι} {Stmt : Type} (I : SPIOP P t Stmt)

/-- A query position of the composite. -/
abbrev Pos : Type := SPBCS.CausalPos (t := t) I.comp

/-- The largest number of trees of a prover message of a component. -/
def maxTrees [Fintype ι] [∀ j, Fintype (P j).MessageIdx] : ℕ :=
  Finset.univ.sup fun j => Finset.univ.sup (I.comp j).nTrees

end IOP.SPIOP

variable {t : SPTerm ι} {X : Type}

/-- The write of message `i` of component `j`: its non-oracle part and the roots of its trees. -/
abbrev SPBCS.CompWrite (I : SPIOP P t X) (k : ℕ) (j : ι) (i : (P j).MessageIdx) : Type :=
  Write ((I.comp j).NonOracle i) ((I.comp j).nTrees i) k

/-! ### The view of the composite verifier -/

namespace SPBCS.CausalIOPViews

variable (I : SPIOP P t X)

/-- The entries of message `i` of leaf `p`: its non-oracle part and its leaves. -/
abbrev Idx (p : t.Leaf) (i : (P p.label).MessageIdx) : Type :=
  Entry ((I.comp p.label).nTrees i) ((I.comp p.label).nLeaves i)

/-- The entry values of message `i` of leaf `p`. -/
abbrev Ans (p : t.Leaf) (i : (P p.label).MessageIdx) : Type :=
  EntryValue ((I.comp p.label).NonOracle i) ((I.comp p.label).nTrees i) ((I.comp p.label).Leaf i)

/-- Message `i` of leaf `p` read as the table of its entries. -/
def read (p : t.Leaf) (i : (P p.label).MessageIdx) (m : (P p.label).Type i.1) :
    Idx I p i → Ans I p i
  | .nonOracle => .nonOracle (((I.comp p.label).parts i) m).nonOracle
  | .leaf τ l => .leaf τ ((((I.comp p.label).parts i) m).leaves τ l)

theorem read_injective (p : t.Leaf) (i : (P p.label).MessageIdx) :
    Function.Injective (read I p i) := by
  intro m m' h
  refine ((I.comp p.label).parts i).injective (MessageParts.ext ?_ (funext fun τ => funext fun l => ?_))
  · simpa [read] using congrFun h .nonOracle
  · simpa [read] using congrFun h (.leaf τ l)

/-- The entries of message `i` of leaf `p` queried at the composite challenges `ch`: the
non-oracle part and the leaves at the query positions. -/
def queries (p : t.Leaf) (i : (P p.label).MessageIdx) (ch : Chs P t) :
    Finset (Idx I p i) :=
  Finset.univ.filter fun o => (match o with
    | .nonOracle => true
    | .leaf τ l => decide ((⟨p, ⟨i, τ, l⟩⟩ : I.Pos) ∈ I.pos ch)) = true

theorem nonOracle_mem_queries (p : t.Leaf) (i : (P p.label).MessageIdx) (ch : Chs P t) :
    .nonOracle ∈ queries I p i ch := by
  simp [queries]

theorem leaf_mem_queries {ch : Chs P t} {q : I.Pos} (hq : q ∈ I.pos ch) :
    .leaf q.pos.tree q.pos.leaf ∈ queries I q.leaf q.pos.msg ch := by
  simpa [queries] using hq

end SPBCS.CausalIOPViews

/-- **How the composite verifier reads every leaf's prover messages**: message `i` of leaf `p` as
the table of its non-oracle part, queried at every challenge vector, and its leaves, queried at the
query positions of the composite challenges. -/
def IOP.SPIOP.views (I : SPIOP P t X) : CausalViews P t where
  Idx := SPBCS.CausalIOPViews.Idx I
  Ans := SPBCS.CausalIOPViews.Ans I
  msg p i := ⟨SPBCS.CausalIOPViews.read I p i, SPBCS.CausalIOPViews.read_injective I p i,
    SPBCS.CausalIOPViews.queries I p i⟩

/-- **Two composite transcripts have the same view** when their challenges, their non-oracle
parts and their leaves at the query positions agree. -/
theorem IOP.SPIOP.view_eq {I : SPIOP P t X} {f f' : FullTr P t}
    (hc : ∀ c : ChIdx P t, f.challenges c = f'.challenges c)
    (hn : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
      ((I.comp p.label).parts i (f p i.1)).nonOracle = ((I.comp p.label).parts i (f' p i.1)).nonOracle)
    (hl : ∀ q ∈ I.pos f.challenges,
      ((I.comp q.leaf.label).parts q.pos.msg (f q.leaf q.pos.msg.1)).leaves q.pos.tree q.pos.leaf =
        ((I.comp q.leaf.label).parts q.pos.msg (f' q.leaf q.pos.msg.1)).leaves q.pos.tree
          q.pos.leaf) :
    I.views.view f = I.views.view f' := by
  have hch : f.challenges = f'.challenges := funext hc
  refine CausalView.ext hch (funext fun p => funext fun i => funext fun o => ?_)
  change (I.views.msg p i).see f.challenges (f p i.1) o = (I.views.msg p i).see f'.challenges (f' p i.1) o
  rw [← hch]
  by_cases ho : o ∈ (I.views.msg p i).queries f.challenges
  · rw [MessageView.see_of_mem _ ho, MessageView.see_of_mem _ ho]
    congr 1
    rcases o with _ | ⟨τ, l⟩
    · exact congrArg SPBCS.EntryValue.nonOracle (hn p i)
    · have hq : (⟨p, ⟨i, τ, l⟩⟩ : I.Pos) ∈ I.pos f.challenges := by
        have ho' := Finset.mem_filter.1 ho
        simpa using ho'.2
      exact congrArg (SPBCS.EntryValue.leaf τ) (hl _ hq)
  · simp only [MessageView.see, ho, ite_false]

end GordieHowe
