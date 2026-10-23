-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.Model
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CausalRun

@[expose] public section

/-!
# The honest prover of the series–parallel base model

The pieces of the honest prover of the compiled argument of a composition
(`GordieHowe.SPBCS.FullPast`, `GordieHowe/SPBCS/FullPast/Model.lean`), for every causal prover (`CausalProver`). The
namespace `GordieHowe.SPBCS` states completeness for the spBCS compiler with them (`GordieHowe.SPBCS.prob_not_accepts_prove_le`,
`GordieHowe/SPBCS/Complete.lean`).

* `ComponentModel.Encoder`: the honest encoding of a component's messages (the column bytes of
  each leaf and the write carrying given roots).
* `overrun`: the samplers' rejection probabilities summed over all challenges of all leaves.
* The rounds of all leaves are listed in term order (`SPTerm.slots`): round `r` of leaf `p` is
  global round `p.off + r`, and the prover's key and XOF queries form one adaptive strategy
  (`strategyW`, `strategyQ`, `strategyFullPast`) of `2 · t.size n` queries, query `2g` the `transcript`
  query of global round `g`'s chain input and query `2g + 1` the `xof` query at its key.
  `chOf`, `itemW`, `leafChainW`, `ctxW`: the challenges, chain items, chains and causal contexts
  derived from the answers; `answersFullPast`, `honestChainsFullPast`: the honest prover's answers and chains.
* `length_leafChainW`, `leafChainW_getElem?`: the chains' lengths and items;
  `honestWrite_congr_oracle`: the honest writes depend on the oracle only through its answers.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

/-! ### Encoders of components -/

namespace ComponentModel

variable {m : ℕ} {P : ProtocolSpec m} [∀ i, Fintype (P.Challenge i)]
  [∀ i, DecidableEq (P.Challenge i)] (C : ComponentModel P k kN L e)

/-- **The honest encoding of a component's messages**: the column bytes of
each leaf of each tree of a prover round, and the write carrying given roots, with the laws that
the write carries the roots and that the message read back from views holding the columns is the
message. -/
structure Encoder where
  /-- The column bytes of each leaf. -/
  cols : (i : P.MessageIdx) → P.Type i.1 → (τ : Fin (C.nTrees i)) → Fin (C.nLeaves i τ) → Bytes L
  /-- The write carrying the roots. -/
  write : (i : P.MessageIdx) → P.Type i.1 → (Fin (C.nTrees i) → Digest k) → C.MessageWrite i
  rootOf_write : ∀ i msg rts τ, C.rootOf i (write i msg rts) τ = rts τ
  msg_write : ∀ i msg rts (vw : (τ : Fin (C.nTrees i)) → MerkleView k kN L (C.nLeaves i τ)),
    (∀ τ j, ∃ ν, (vw τ).leaves j = some ⟨ν, cols i msg τ j⟩) → C.msg i (write i msg rts) vw = msg

end ComponentModel

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-- **The overrun term** of the composite: the samplers' rejection probabilities summed over all
challenges of all leaves. -/
noncomputable def overrun : ℝ≥0∞ :=
  ∑ c : ChIdx P t, ((M.comp c.leaf.label).sampler c.idx).rejectionProb

/-- The overrun is finite. -/
theorem overrun_ne_top : M.overrun ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun _ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (Sampler.rejectionProb_le_one _)

/-- A write function: the write of each prover round of each leaf as a function of its message. -/
abbrev WriteFn : Type := (p : t.Leaf) → (i : (P p.label).MessageIdx) → (P p.label).Type i.1 →
  (M.comp p.label).MessageWrite i

variable {M} (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS)

/-- Leaf `j` of tree `τ` of round `i` of leaf `p` with message `msg`: the Merkle salt of the
position and the column bytes; past the last leaf, a fixed value. -/
def leafFn (p : t.Leaf) (i : (P p.label).MessageIdx) (msg : (P p.label).Type i.1)
    (τ : Fin ((M.comp p.label).nTrees i)) (j : ℕ) : MerkleLeaf kN L :=
  if hj : j < (M.comp p.label).nLeaves i τ then
    ⟨ν ⟨p, ⟨i, τ, ⟨j, hj⟩⟩⟩, (E p.label).cols i msg τ ⟨j, hj⟩⟩
  else ⟨fun _ => 0, ⟨0, Fin.elim0⟩⟩

theorem leafFn_val (p : t.Leaf) (i : (P p.label).MessageIdx) (msg : (P p.label).Type i.1)
    (τ : Fin ((M.comp p.label).nTrees i)) (j : Fin ((M.comp p.label).nLeaves i τ)) :
    leafFn E ν p i msg τ j = ⟨ν ⟨p, ⟨i, τ, j⟩⟩, (E p.label).cols i msg τ j⟩ := by
  simp [leafFn]

/-- The honest write of round `i` of leaf `p` with message `msg`: the encoder's write at the
honest roots of its trees. -/
def honestWrite (h : Query k kN kS L → Out k e) : M.WriteFn := fun p i msg =>
  (E p.label).write i msg fun τ => MerkleTree.root h ((M.comp p.label).nLeaves i τ)
    (leafFn E ν p i msg τ)

variable [∀ j i, Nonempty ((P j).Challenge i)]

variable {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x)

variable (h : Query k kN kS L → Out k e)

/-! ### The probability bound -/

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The honest write function reads the oracle only at `leaf` and `node` queries. -/
theorem honestWrite_congr_oracle {h₁ h₂ : Query k kN kS L → Out k e}
    (hq : ∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) :
    honestWrite (M := M) E ν h₁ = honestWrite E ν h₂ := by
  funext p i msg
  unfold honestWrite
  congr 1
  funext τ
  exact MerkleTree.root_congr (fun a b => hq _ id) (fun l r => hq _ id) _ _

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : FullPast P t X k kN kS L e)

variable {M} (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS)

variable [∀ j i, Nonempty ((P j).Challenge i)]

variable (M) in
/-- The challenges derived from the strategy's answers `ws`: challenge `c` samples the answer to
its global round's `xof` query (an arbitrary value where the sampler rejects). -/
noncomputable def chOf (ws : List (Out k e)) : Chs P t := fun c =>
  ((ws[2 * (c.leaf.off n + c.idx.1.1) + 1]?).bind fun w =>
    ((M.comp c.leaf.label).sampler c.idx).sample w.stream).getD
      ((M.comp c.leaf.label).sampler c.idx).default

variable (M) in
/-- Round `r` of leaf `p`'s chain for the write function `wr` from the answers `ws`: the write of
the causal prover's message at the derived challenges, or the digest of the round's `xof`
answer. -/
noncomputable def itemW (wr : M.WriteFn) (ws : List (Out k e)) (p : t.Leaf) (r : ℕ) :
    Item k (M.comp p.label).W :=
  if hr : r < n p.label then
    if hd : (P p.label).dir ⟨r, hr⟩ = .P_to_V then
      .write ⟨⟨⟨r, hr⟩, hd⟩, wr p ⟨⟨r, hr⟩, hd⟩ (prv.run x (M.chOf ws) p ⟨r, hr⟩)⟩
    else .absorb ((ws[2 * (p.off n + r) + 1]?).getD SPBCS.defaultOut).digest
  else .absorb fun _ => 0

variable (M) in
/-- The first `r` items of leaf `p`'s chain for the write function `wr` from the answers `ws`. -/
noncomputable def leafChainW (wr : M.WriteFn) (ws : List (Out k e)) (p : t.Leaf) : ℕ → M.Items p
  | 0 => []
  | r + 1 => leafChainW wr ws p r ++ [itemW M prv x wr ws p r]

variable (M) in
/-- The causal context of leaf `p`: the full chains of the leaves before it. -/
noncomputable def ctxW (wr : M.WriteFn) (ws : List (Out k e)) (p : t.Leaf) : M.Ctx p :=
  fun q => leafChainW M prv x wr ws q.1 (n q.1.label)

variable (M) in
/-- **The key and XOF queries of a prover with write function `wr`** as an adaptive strategy:
query `2g` is the `transcript` query of global round `g`'s chain input (its leaf, the chains of
the leaves before it, its own items before it), query `2g + 1` the `xof` query at the digest of
answer `2g` and the salt. -/
noncomputable def strategyW (wr : M.WriteFn) (j : ℕ) (ws : List (Out k e)) : Query k kN kS L :=
  match (t.slots n)[j / 2]? with
  | some s =>
    if j % 2 = 0 then
      .transcript (M.enc.encode ⟨σ, x⟩ (M.content s.leaf (ctxW M prv x wr ws s.leaf)
        (leafChainW M prv x wr ws s.leaf s.round)))
    else .xof ((ws[j - 1]?).getD SPBCS.defaultOut).digest σ
  | none => .xof (SPBCS.defaultOut (k := k) (e := e)).digest σ

variable (M) in
/-- The strategy of a prover whose write function `wrOf h` depends on the oracle. -/
noncomputable def strategyQ (wrOf : (Query k kN kS L → Out k e) → M.WriteFn) (j : ℕ)
    (ws : List (Out k e)) (h : Query k kN kS L → Out k e) : Query k kN kS L :=
  strategyW M prv x σ (wrOf h) j ws

/-- **The honest prover's key and XOF queries** as an adaptive strategy. -/
noncomputable def strategyFullPast (j : ℕ) (ws : List (Out k e)) (h : Query k kN kS L → Out k e) :
    Query k kN kS L :=
  strategyQ M prv x σ (honestWrite E ν) j ws h

/-- The answers to the honest prover's key and XOF queries. -/
noncomputable def answersFullPast (h : Query k kN kS L → Out k e) : List (Out k e) :=
  ansList (strategyFullPast E prv x ν σ) h (2 * t.size n)

variable {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x)

/-- The honest prover's chains. -/
noncomputable def honestChainsFullPast (h : Query k kN kS L → Out k e) : (p : t.Leaf) → M.Items p :=
  fun p => leafChainW M prv x (honestWrite E ν h) (answersFullPast E prv x ν σ h) p (n p.label)

/-! ### Chains of a write function -/

section ChainW

variable (wr : M.WriteFn)

theorem length_leafChainW (ws : List (Out k e)) (p : t.Leaf) :
    ∀ r, (leafChainW M prv x wr ws p r).length = r
  | 0 => rfl
  | r + 1 => by simp [leafChainW, length_leafChainW ws p r]

theorem leafChainW_getElem? (ws : List (Out k e)) (p : t.Leaf) :
    ∀ r j, j < r → (leafChainW M prv x wr ws p r)[j]? = some (itemW M prv x wr ws p j)
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, j, hj => by
    rw [leafChainW]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem?_append_left (by rw [length_leafChainW]; exact hj'),
        leafChainW_getElem? ws p r j hj']
    · rw [List.getElem?_append_right (by rw [length_leafChainW]), length_leafChainW]
      simp

end ChainW

end FullPast

end GordieHowe.SPBCS
