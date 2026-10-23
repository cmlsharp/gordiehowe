-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.SPBCS.Extraction.Position
public import GordieHowe.Model.QROM.Oracle

@[expose] public section

/-!
# Positions, message parts and writes of committed messages

The objects of a prover message that consists of a non-oracle message, which the verifier reads
in its entirety, and any number of oracles, each committed as one Merkle tree whose leaves the
verifier reads at query positions (CY24 p. 259: "a non-oracle message αi that the IOP verifier
reads in its entirety", compiled in CY24 Remarks 24.1.2 and 25.1.2):

- `SPBCS.LeafPos nTrees nLeaves`: a leaf of a table of trees (`tree`, `leaf`).
- `GordieHowe.SPBCS.MessageParts`: a prover message decomposed into its non-oracle part (`nonOracle`) and the
  leaves of its trees (`leaves`).
- `GordieHowe.SPBCS.Entry`, `GordieHowe.SPBCS.EntryValue`: an entry of a prover message (its non-oracle part, or a leaf of
  one of its trees) and the value of an entry.
- `MessageShape M`: how a message of type `M` is read (its non-oracle part and its trees); a message
  read in full (`MessageShape.plain`) and a table of trees (`MessageShape.trees`).
- `GordieHowe.SPBCS.Write`: the write of a prover message in a hash chain, its non-oracle part and the roots of
  its trees.
-/

namespace GordieHowe.SPBCS

open IOP IOP.ProtocolSpec
open scoped NNReal

/-! ### Positions and message parts -/

/-- **A leaf of a table of trees**: one of the `nTrees` trees and one of its leaves. -/
structure LeafPos (nTrees : ℕ) (nLeaves : Fin nTrees → ℕ) where
  /-- The tree. -/
  tree : Fin nTrees
  /-- The leaf of the tree. -/
  leaf : Fin (nLeaves tree)
  deriving DecidableEq

namespace LeafPos

variable {nTrees : ℕ} {nLeaves : Fin nTrees → ℕ}

/-- A leaf of a table of trees is a dependent pair of a tree and a leaf. -/
def equivSigma : LeafPos nTrees nLeaves ≃ Σ t : Fin nTrees, Fin (nLeaves t) where
  toFun p := ⟨p.tree, p.leaf⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (LeafPos nTrees nLeaves) := Fintype.ofEquiv _ equivSigma.symm

theorem mk_injective_right {t : Fin nTrees} :
    Function.Injective (LeafPos.mk (nLeaves := nLeaves) t) :=
  fun _ _ h => eq_of_heq (LeafPos.mk.inj h).2

end LeafPos

/-- **A prover message in parts**: its non-oracle part, read in full, and the leaves of its
`nTrees` trees. -/
@[ext]
structure MessageParts (NonOracle : Type) (nTrees : ℕ) (nLeaves : Fin nTrees → ℕ)
    (Leaf : Fin nTrees → Type) where
  /-- The non-oracle part. -/
  nonOracle : NonOracle
  /-- The leaves of each tree. -/
  leaves : (t : Fin nTrees) → Fin (nLeaves t) → Leaf t

/-! ### The entries of a message -/

/-- **An entry of a prover message** with `nTrees` trees: its non-oracle part, or a leaf of one of
its trees. -/
inductive Entry (nTrees : ℕ) (nLeaves : Fin nTrees → ℕ) where
  /-- The non-oracle part. -/
  | nonOracle
  /-- The leaf `leaf` of the tree `tree`. -/
  | leaf (tree : Fin nTrees) (leaf : Fin (nLeaves tree))
  deriving DecidableEq

namespace Entry

variable {nTrees : ℕ} {nLeaves : Fin nTrees → ℕ}

/-- An entry is the non-oracle part (`none`) or a leaf of a table of trees. -/
def equivOption : Entry nTrees nLeaves ≃ Option (LeafPos nTrees nLeaves) where
  toFun
    | nonOracle => none
    | leaf t j => some ⟨t, j⟩
  invFun
    | none => nonOracle
    | some p => leaf p.tree p.leaf
  left_inv o := by cases o <;> rfl
  right_inv o := by
    rcases o with _ | ⟨t, j⟩ <;> rfl

instance : Fintype (Entry nTrees nLeaves) := Fintype.ofEquiv _ equivOption.symm

end Entry

/-- **The value of an entry** of a prover message: the non-oracle part, or a leaf of one of its
trees with the tree it belongs to. -/
inductive EntryValue (NonOracle : Type) (nTrees : ℕ) (Leaf : Fin nTrees → Type) where
  /-- The non-oracle part. -/
  | nonOracle (value : NonOracle)
  /-- A leaf of the tree `tree`. -/
  | leaf (tree : Fin nTrees) (value : Leaf tree)

/-! ### The shape of a message -/

/-- **How the BCS transformation reads a message** of type `M`: its non-oracle part, read in
full, and its trees, each a table of leaves with a default leaf (the per-message fields of
`SPBCS.CompIOP`). -/
structure MessageShape (M : Type) : Type 1 where
  /-- The non-oracle part. -/
  NonOracle : Type
  /-- The number of trees. -/
  nTrees : ℕ
  /-- The number of leaves of each tree. -/
  nLeaves : Fin nTrees → ℕ
  /-- The leaf type of each tree. -/
  Leaf : Fin nTrees → Type
  /-- The leaf read where a leaf is missing. -/
  leafDefault : ∀ t, Leaf t
  /-- The message is its non-oracle part and the leaves of its trees. -/
  parts : M ≃ MessageParts NonOracle nTrees nLeaves Leaf

namespace MessageShape

/-- A message read in full: the whole message is the non-oracle part, and there are no trees. -/
def plain (M : Type) : MessageShape M where
  NonOracle := M
  nTrees := 0
  nLeaves := Fin.elim0
  Leaf := Fin.elim0
  leafDefault t := t.elim0
  parts :=
    { toFun := fun m => ⟨m, fun t => t.elim0⟩
      invFun := fun p => p.nonOracle
      left_inv := fun _ => rfl
      right_inv := fun _ => MessageParts.ext rfl (funext fun t => t.elim0) }

/-- A message that is a table of trees, with no non-oracle part. -/
def trees {M : Type} (nTrees : ℕ) (nLeaves : Fin nTrees → ℕ) (Leaf : Fin nTrees → Type)
    (leafDefault : ∀ t, Leaf t) (e : M ≃ ((t : Fin nTrees) → Fin (nLeaves t) → Leaf t)) :
    MessageShape M where
  NonOracle := Unit
  nTrees := nTrees
  nLeaves := nLeaves
  Leaf := Leaf
  leafDefault := leafDefault
  parts :=
    { toFun := fun m => ⟨(), e m⟩
      invFun := fun p => e.symm p.leaves
      left_inv := fun m => e.symm_apply_apply m
      right_inv := fun p => MessageParts.ext rfl (e.apply_symm_apply p.leaves) }

/-- A message without trees is determined by its non-oracle part. -/
theorem eq_of_nonOracle {M : Type} (s : MessageShape M) (h : s.nTrees = 0) {m m' : M}
    (e : (s.parts m).nonOracle = (s.parts m').nonOracle) : m = m' :=
  s.parts.injective (MessageParts.ext e (funext fun t => (Fin.cast h t).elim0))

end MessageShape

/-! ### Writes -/

/-- **The write of a prover message** in the hash chain of the compiled proof: its non-oracle part
and the roots of its `nTrees` trees. -/
@[ext]
structure Write (NonOracle : Type) (nTrees k : ℕ) where
  /-- The non-oracle part. -/
  nonOracle : NonOracle
  /-- The roots of the trees. -/
  roots : Fin nTrees → QROM.Digest k

/-- The writes of a message with no non-oracle part are its roots. -/
def Write.rootsEquiv (nTrees k : ℕ) : Write Unit nTrees k ≃ (Fin nTrees → QROM.Digest k) where
  toFun w := w.roots
  invFun r := ⟨(), r⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The writes of a message with no trees are its non-oracle parts. -/
def Write.nonOracleEquiv (NonOracle : Type) (k : ℕ) : Write NonOracle 0 k ≃ NonOracle where
  toFun w := w.nonOracle
  invFun a := ⟨a, Fin.elim0⟩
  left_inv w := Write.ext rfl (funext fun t => t.elim0)
  right_inv _ := rfl

end GordieHowe.SPBCS
