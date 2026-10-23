-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.RBR

@[expose] public section

/-!
# Query positions and trees of a protocol with Merkle-committed messages

- `SPBCS.TreeIdx P nTrees`: a tree of a protocol whose prover message `i` carries `nTrees i` trees
  (`msg`, `tree`).
- `SPBCS.Position P nTrees nLeaves`: a query position, a leaf of one of those trees (`msg`, `tree`,
  `leaf`); `Position.treeIdx` is its tree.

The compiled IOPs (`GordieHowe/Model/IOP/SPIOP.lean`) index their Merkle trees and leaves by these.
-/

namespace GordieHowe.SPBCS

open IOP IOP.ProtocolSpec

/-- **A tree** of a protocol `P` whose prover message `i` carries `nTrees i` trees: a prover message
and one of its trees. -/
@[ext]
structure TreeIdx {n : ℕ} (P : ProtocolSpec n) (nTrees : P.MessageIdx → ℕ) where
  /-- The prover message. -/
  msg : P.MessageIdx
  /-- The tree of the message. -/
  tree : Fin (nTrees msg)

namespace TreeIdx

variable {n : ℕ} {P : ProtocolSpec n} {nTrees : P.MessageIdx → ℕ}

/-- A tree is a dependent pair of a message and a tree. -/
def equivSigma : TreeIdx P nTrees ≃ Σ i : P.MessageIdx, Fin (nTrees i) where
  toFun τ := ⟨τ.msg, τ.tree⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq P.MessageIdx] : DecidableEq (TreeIdx P nTrees) :=
  equivSigma.decidableEq

instance [Fintype P.MessageIdx] : Fintype (TreeIdx P nTrees) :=
  Fintype.ofEquiv _ equivSigma.symm

/-- The prover rounds in round order. -/
def _root_.GordieHowe.IOP.ProtocolSpec.msgList (P : ProtocolSpec n) : List P.MessageIdx :=
  (List.finRange n).filterMap fun r => if hd : P.dir r = .P_to_V then some ⟨r, hd⟩ else none

theorem _root_.GordieHowe.IOP.ProtocolSpec.mem_msgList (i : P.MessageIdx) : i ∈ P.msgList :=
  List.mem_filterMap.2 ⟨i.1, List.mem_finRange _, by rw [dif_pos i.2]; rfl⟩

theorem _root_.GordieHowe.IOP.ProtocolSpec.nodup_msgList : P.msgList.Nodup := by
  refine (List.nodup_finRange n).filterMap fun r r' i h h' => ?_
  by_cases hd : P.dir r = .P_to_V <;> by_cases hd' : P.dir r' = .P_to_V <;>
    simp only [hd, hd', dite_true, dite_false, Option.mem_def, reduceCtorEq] at h h'
  rw [← h'] at h
  exact congrArg Subtype.val (Option.some.inj h)

variable (P nTrees) in
/-- **The trees in order**: the trees of each prover round in round order (computable). -/
def list : List (TreeIdx P nTrees) :=
  P.msgList.flatMap fun i => (List.finRange (nTrees i)).map fun t => ⟨i, t⟩

@[simp] theorem mem_list (τ : TreeIdx P nTrees) : τ ∈ list P nTrees :=
  List.mem_flatMap.2 ⟨τ.msg, P.mem_msgList _, List.mem_map.2 ⟨τ.tree, List.mem_finRange _, rfl⟩⟩

theorem nodup_list : (list P nTrees).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun i _ => (List.nodup_finRange _).map fun t t' h => by
    cases h; rfl, ?_⟩
  refine P.nodup_msgList.pairwise_of_forall_ne fun i _ j _ hij => ?_
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
  rintro _ ⟨t, rfl⟩ ⟨t', h⟩
  exact hij (congrArg TreeIdx.msg h).symm

/-- A sum over the list of trees is the sum over all trees. -/
theorem sum_map_list {M : Type*} [AddCommMonoid M] (f : TreeIdx P nTrees → M) :
    ((list P nTrees).map f).sum = ∑ τ, f τ := by
  rw [← List.sum_toFinset _ nodup_list]
  congr 1
  ext τ
  simp

end TreeIdx

/-- **A query position** of a protocol `P` whose prover message `i` carries `nTrees i` trees with
`nLeaves i t` leaves: a prover message, one of its trees, and a leaf of that tree. -/
structure Position {n : ℕ} (P : ProtocolSpec n) (nTrees : P.MessageIdx → ℕ)
    (nLeaves : (i : P.MessageIdx) → Fin (nTrees i) → ℕ) where
  /-- The prover message. -/
  msg : P.MessageIdx
  /-- The tree of the message. -/
  tree : Fin (nTrees msg)
  /-- The leaf of the tree. -/
  leaf : Fin (nLeaves msg tree)

namespace Position

variable {n : ℕ} {P : ProtocolSpec n} {nTrees : P.MessageIdx → ℕ}
  {nLeaves : (i : P.MessageIdx) → Fin (nTrees i) → ℕ}

/-- A query position is a nested dependent pair of a message, a tree and a leaf. -/
def equivSigma :
    Position P nTrees nLeaves ≃ Σ i : P.MessageIdx, Σ t : Fin (nTrees i), Fin (nLeaves i t) where
  toFun p := ⟨p.msg, p.tree, p.leaf⟩
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq P.MessageIdx] : DecidableEq (Position P nTrees nLeaves) :=
  equivSigma.decidableEq

instance [Fintype P.MessageIdx] : Fintype (Position P nTrees nLeaves) :=
  Fintype.ofEquiv _ equivSigma.symm

end Position

namespace Position

variable {n : ℕ} {P : ProtocolSpec n} {nTrees : P.MessageIdx → ℕ}
  {nLeaves : (i : P.MessageIdx) → Fin (nTrees i) → ℕ}

/-- The tree of a position. -/
def treeIdx (p : Position P nTrees nLeaves) : TreeIdx P nTrees := ⟨p.msg, p.tree⟩

@[simp] theorem msg_treeIdx (p : Position P nTrees nLeaves) : p.treeIdx.msg = p.msg := rfl

@[simp] theorem tree_treeIdx (p : Position P nTrees nLeaves) : p.treeIdx.tree = p.tree := rfl

end Position

end GordieHowe.SPBCS
