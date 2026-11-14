-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.Transcript
public import GordieHowe.Model.IOP.CausalLeaves
public import GordieHowe.SPBCS.Merkle.Opening

@[expose] public section

/-!
# The data of one component's hash chain

`ComponentModel P k kN L e`: the per-component data of one hash chain of the spBCS compiler
(`GordieHowe/SPBCS/Basic.lean`): the writes of the prover rounds, their Merkle trees, the message
read from a write and the views of its trees, and the sampler of each challenge round.

* `ComponentModel.chainWith`: the chain of a component for a key function (the digest of the
  chain input at each prefix), with its items (`itemWith`) and challenges (`chalWith`).
* `ComponentModel.writeAt`, `ComponentModel.views`: the write of a round held by an item, and the
  Merkle views of a round's trees read from a database at the roots of a write;
  `digest_mem_of_views_ne`: recording one new collision-free answer changes these views only at
  one of the write's roots or a digest of `S(D)`; `root_or_nodeKids_of_views_ne`: at one of the
  roots or a child of a recorded node; `views_extend_of_not_merkle`: an input that is neither a
  `node` nor a `leaf` changes none.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

/-! ### Component models -/

-- TODO(instance-hazard): `MessageWrite` and its `DecidableEq` instances are fields, so each
-- component model carries its own instance terms. A construction deriving one component model from
-- another and comparing them could give equal write types with unequal instances. If that arises,
-- take the write types as a parameter or type them through a named function with registered
-- instances.
/-- **The per-component data of one hash chain**: the write of each prover round, its Merkle
trees, the message read from a write and the views of its trees, and the sampler of each
challenge round. The fields carry correspondence obligations: the writes, roots and messages are
those of the C++ transcript, and each sampler is the C++ challenge reader of its round. -/
structure ComponentModel {m : ℕ} (P : ProtocolSpec m) (k kN L e : ℕ)
    [∀ i, Fintype (P.Challenge i)] [∀ i, DecidableEq (P.Challenge i)] where
  /-- The prover's write of each prover round. -/
  MessageWrite : P.MessageIdx → Type
  /-- Writes have decidable equality (compiled code for the proofs that carry them). -/
  [instDecEqMessageWrite : ∀ i, DecidableEq (MessageWrite i)]
  /-- The number of trees of each prover round. -/
  nTrees : P.MessageIdx → ℕ
  /-- The leaf count of each tree. -/
  nLeaves : (i : P.MessageIdx) → Fin (nTrees i) → ℕ
  /-- The root of each tree carried by a write. -/
  rootOf : (i : P.MessageIdx) → MessageWrite i → Fin (nTrees i) → Digest k
  /-- The message read from a write and the Merkle views of its trees. -/
  msg : (i : P.MessageIdx) → MessageWrite i →
    ((t : Fin (nTrees i)) → MerkleView k kN L (nLeaves i t)) → P.Type i.1
  /-- The sampler of each challenge round. -/
  sampler : (i : P.ChallengeIdx) → Sampler k e (P.Challenge i)

attribute [instance] ComponentModel.instDecEqMessageWrite

namespace ComponentModel

variable {m : ℕ} {P : ProtocolSpec m} [∀ i, Fintype (P.Challenge i)]
  [∀ i, DecidableEq (P.Challenge i)] (C : ComponentModel P k kN L e)

/-- A write of some round, tagged with its round. -/
abbrev W : Type := Σ i, C.MessageWrite i

/-- The roots a write carries. -/
def roots (w : C.W) : Finset (Digest k) := Finset.univ.image (C.rootOf w.1 w.2)

/-! #### A chain from a key function -/

variable {kS : ℕ} (wr : (i : P.MessageIdx) → C.MessageWrite i) (keyOf : List (Item k C.W) → Digest k)
  (salt : FiatShamirSalt kS) (h : Query k kN kS L → Out k e)

/-- **Item `r` of a chain after the items `l`**, for the keys `keyOf` and the Fiat–Shamir salt
`salt`: the write at a prover round, the digest of the stream at the key of `l` and the salt at a
challenge round (the write-back). -/
def itemWith (r : ℕ) (hr : r < m) (l : List (Item k C.W)) : Item k C.W :=
  if hd : P.dir ⟨r, hr⟩ = .P_to_V then .write ⟨⟨⟨r, hr⟩, hd⟩, wr ⟨⟨r, hr⟩, hd⟩⟩
  else .absorb (h (.xof (keyOf l) salt)).digest

/-- **The first `r` items of a chain** for the keys `keyOf` and the salt `salt`: the chain of a
compiler whose chain input at the items `l` has the key `keyOf l`. -/
def chainWith : (r : ℕ) → r ≤ m → List (Item k C.W)
  | 0, _ => []
  | r + 1, hr => chainWith r (by omega) ++ [C.itemWith wr keyOf salt h r (by omega) (chainWith r (by omega))]

theorem length_chainWith : ∀ r (hr : r ≤ m), (C.chainWith wr keyOf salt h r hr).length = r
  | 0, _ => rfl
  | r + 1, hr => by simp [chainWith, length_chainWith r]

theorem chainWith_getElem? : ∀ r (hr : r ≤ m) j (hj : j < r), (C.chainWith wr keyOf salt h r hr)[j]? =
    some (C.itemWith wr keyOf salt h j (by omega) (C.chainWith wr keyOf salt h j (by omega)))
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, hr, j, hj => by
    rw [chainWith]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem?_append_left (by rw [length_chainWith]; exact hj'),
        chainWith_getElem? r (by omega) j hj']
    · rw [List.getElem?_append_right (by rw [length_chainWith]), length_chainWith]
      simp

/-- **The first `r` items of a chain of `s` items are its chain of `r` items.** -/
theorem take_chainWith : ∀ s (hs : s ≤ m) r (hr : r ≤ s),
    (C.chainWith wr keyOf salt h s hs).take r = C.chainWith wr keyOf salt h r (hr.trans hs)
  | 0, _, r, hr => by
    obtain rfl : r = 0 := by omega
    rfl
  | s + 1, hs, r, hr => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hr) with hr' | rfl
    · rw [chainWith, List.take_append_of_le_length (by rw [length_chainWith]; omega),
        take_chainWith s (by omega) r (by omega)]
    · rw [List.take_of_length_le (by rw [length_chainWith])]

variable {wr keyOf salt h} in
/-- **Two chains agree** when their key functions, salts and oracles give the same items at the
chain's own prefixes. -/
theorem chainWith_congr {keyOf' : List (Item k C.W) → Digest k} {kS' : ℕ}
    {salt' : FiatShamirSalt kS'} {h' : Query k kN kS' L → Out k e} :
    ∀ r (hr : r ≤ m), (∀ j (hj : j < r),
      (h (.xof (keyOf (C.chainWith wr keyOf salt h j (by omega))) salt)).digest =
        (h' (.xof (keyOf' (C.chainWith wr keyOf salt h j (by omega))) salt')).digest) →
      C.chainWith wr keyOf salt h r hr = C.chainWith wr keyOf' salt' h' r hr
  | 0, _, _ => rfl
  | r + 1, hr, hag => by
    have ih := chainWith_congr r (by omega) fun j hj => hag j (by omega)
    rw [chainWith, chainWith, ← ih]
    congr 2
    unfold itemWith
    split_ifs
    · rfl
    · rw [hag r (Nat.lt_succ_self r)]

variable {keyOf salt h} in
/-- **Two chains agree when their writes agree at the prover rounds before `r`.** -/
theorem chainWith_congr_wr {wr' : (i : P.MessageIdx) → C.MessageWrite i} :
    ∀ r (hr : r ≤ m), (∀ i : P.MessageIdx, i.1.1 < r → wr i = wr' i) →
      C.chainWith wr keyOf salt h r hr = C.chainWith wr' keyOf salt h r hr
  | 0, _, _ => rfl
  | r + 1, hr, hw => by
    have ih := chainWith_congr_wr r (by omega) fun i hi => hw i (by omega)
    rw [chainWith, chainWith, ← ih]
    congr 2
    unfold itemWith
    split_ifs with hd
    · rw [hw ⟨⟨r, by omega⟩, hd⟩ (Nat.lt_succ_self r)]
    · rfl

/-- **A chain from a key function is well formed**: a write at each prover round, an absorbed
digest at each challenge round. -/
theorem chainWF_chainWith (r : ℕ) (hr : r ≤ m) : chainWF P (C.chainWith wr keyOf salt h r hr) := by
  intro j hj
  rw [length_chainWith] at hj
  have hget := C.chainWith_getElem? wr keyOf salt h r hr j hj
  rw [List.getElem?_eq_getElem (by rw [length_chainWith]; exact hj), Option.some_inj] at hget
  rw [hget]
  unfold itemWith
  split_ifs with hd
  · rfl
  · exact ⟨by omega, by cases h' : P.dir ⟨j, by omega⟩ <;> simp_all⟩

/-- **The challenge `i` of a chain**, sampled from the stream at the key of its prefix and the
salt, or `none` when the sampler rejects. -/
def chalWith (i : P.ChallengeIdx) : Option (P.Challenge i) :=
  (C.sampler i).sample (h (.xof (keyOf (C.chainWith wr keyOf salt h i.1 i.1.2.le)) salt)).stream

end ComponentModel

namespace ComponentModel

variable {m : ℕ} {P : ProtocolSpec m} [∀ i, Fintype (P.Challenge i)]
  [∀ i, DecidableEq (P.Challenge i)] (C : ComponentModel P k kN L e)

/-- The write of round `i` held by an item, if it is one. -/
def writeAt (i : P.MessageIdx) : Item k C.W → Option (C.MessageWrite i)
  | .write w => if h : w.1 = i then some (h ▸ w.2) else none
  | .absorb _ => none

theorem writeAt_write (i : P.MessageIdx) (w : C.MessageWrite i) :
    C.writeAt i (.write ⟨i, w⟩) = some w := by
  simp [writeAt]

theorem eq_write_of_writeAt {i : P.MessageIdx} {it : Item k C.W} {w : C.MessageWrite i}
    (h : C.writeAt i it = some w) : it = .write ⟨i, w⟩ := by
  cases it with
  | write w' =>
    obtain ⟨j, w'⟩ := w'
    simp only [writeAt] at h
    split_ifs at h with hj
    subst hj
    simp_all
  | absorb d => simp [writeAt] at h

/-- The Merkle views of round `i`'s trees read from `D`, at the roots of the write `w`. -/
def views (D : ODB k kN kS L e) (i : P.MessageIdx) (w : C.MessageWrite i) :
    (τ : Fin (C.nTrees i)) → MerkleView k kN L (C.nLeaves i τ) :=
  fun τ => view D (C.nLeaves i τ) (C.rootOf i w τ)

theorem rootOf_mem_roots (i : P.MessageIdx) (w : C.MessageWrite i) (τ : Fin (C.nTrees i)) :
    C.rootOf i w τ ∈ C.roots ⟨i, w⟩ :=
  Finset.mem_image_of_mem _ (Finset.mem_univ τ)

/-- A write item's roots are digests of the chain prefix that contains it. -/
theorem roots_subset_chainDigests {l : List (Item k C.W)} {r : ℕ} {i : P.MessageIdx}
    {w : C.MessageWrite i} {it : Item k C.W} (hit : l[r]? = some it) (hw : C.writeAt i it = some w) :
    C.roots ⟨i, w⟩ ⊆ chainDigests C.roots (l.take (r + 1)) := fun _ hu =>
  mem_chainDigests.2 ⟨it, SPBCS.mem_take_succ_of_getElem? hit, by
    rw [C.eq_write_of_writeAt hw]; exact hu⟩

/-- If recording `q ↦ y` (collision-free) changes the views of a round's trees at the roots of
`w`, the digest of `y` is one of those roots or lies in `S(D)`. -/
theorem digest_mem_of_views_ne {D : ODB k kN kS L e} {q : Query k kN kS L} {y : Out k e}
    (digestsOf : Bytes L → Finset (Digest k)) (hq : q ∉ D) (hcol : D.extend q y ∉ digestCollision)
    {i : P.MessageIdx} {w : C.MessageWrite i} (h : C.views (D.extend q y) i w ≠ C.views D i w) :
    y.digest ∈ C.roots ⟨i, w⟩ ∪ halfPre digestsOf D := by
  obtain ⟨τ, hτ⟩ : ∃ τ, C.views (D.extend q y) i w τ ≠ C.views D i w τ := by
    by_contra hne
    push Not at hne
    exact h (funext hne)
  have hmem := digest_mem_of_view_ne hq hcol digestsOf hτ
  rw [Finset.mem_insert] at hmem
  rcases hmem with hmem | hmem
  · exact Finset.mem_union_left _ (hmem ▸ C.rootOf_mem_roots i w τ)
  · exact Finset.mem_union_right _ hmem

/-- If recording `q ↦ y` changes the views of a round's trees at the roots of `w`, the digest of
`y` is one of those roots or a child of a node recorded before. -/
theorem root_or_nodeKids_of_views_ne {D : ODB k kN kS L e} {q : Query k kN kS L} {y : Out k e}
    (hq : q ∉ D) {i : P.MessageIdx} {w : C.MessageWrite i}
    (h : C.views (D.extend q y) i w ≠ C.views D i w) :
    (∃ τ, C.rootOf i w τ = y.digest) ∨ y.digest ∈ nodeKids D := by
  by_contra hc
  push Not at hc
  exact h (funext fun τ => view_extend_of_notMem_nodeKids hq (fun he => hc.1 τ he.symm) hc.2)

/-- **Recording a new input that is neither a `node` nor a `leaf` without a digest collision
changes no view of a round's trees.** -/
theorem views_extend_of_not_merkle {D : ODB k kN kS L e} {q : Query k kN kS L} {y : Out k e}
    (hq : q ∉ D) (hcol : D.extend q y ∉ digestCollision) (hqc : q.children = none)
    (hqo : q.opening = none) (i : P.MessageIdx) (w : C.MessageWrite i) :
    C.views (D.extend q y) i w = C.views D i w :=
  funext fun _ => view_extend_of_not_merkle hq hcol hqc hqo

end ComponentModel

end GordieHowe.SPBCS
