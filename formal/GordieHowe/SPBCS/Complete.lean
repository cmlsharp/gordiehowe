-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Basic
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.CausalRun

@[expose] public section

/-!
# Completeness of the spBCS compiler

The honest prover of the spBCS compiler on a series–parallel term with merges
(`GordieHowe/SPBCS/Basic.lean`) and its completeness for a fixed statement (paper `thm:bcs-complete`
(1)), for every causal prover, every query phase and every composite verifier.

The prover's oracle queries form one adaptive strategy over *query slots* (`QSlot`): the chain
input of a challenge round (`key p r`), the stream point at its key (`xof p r`) and the final
input of a branch (`fin s`). The slots are listed by their *key* (`QSlot.key`): the step of their
observer in the prover's order (`Merges.Obs.rank`), then the round. A query reads only the
answers at slots of smaller key (`queryW_congr`), since a step reads only steps of smaller rank
(`Merges.Obs.rank_lt_of_reads`). So the prover's chains (`chsW`), final digests (`fsW`) and
challenges (`chOfW`) are functions of the answer list, read at the slots' positions (`pos`).

The verifier recomputes the prover's chains (`chains_eq_chsW`, by induction on the causal
order) and final digests (`finals_eq_fsW`, the unique solution of their equation,
`GordieHowe.SPBCS.eq_finalsWith`), so the honest proof is accepted when every sampler accepts and the
composite verifier accepts the causal run (`accepts_prove`).

`prob_not_accepts_prove_le`: over a uniform oracle the honest proof is rejected with probability
at most `ε + overrun + keyCollision (t.size n) k`. The transcript queries are distinct (their
contents are well formed and distinct, `eq_of_queryW_eq`), so a repeated query is a stream query
at the key of an earlier round, and only the `t.size n` rounds have a key; a final input has none.
-/

/-!
## The honest writes

The pieces of the honest prover of the spBCS compiler, for every causal prover (`CausalProver`),
with which completeness is stated below (`prob_not_accepts_prove_le`).

* `ComponentModel.Encoder`: the honest encoding of a component's messages (the column bytes of
  each leaf and the write carrying given roots).
* `WriteFn`, `honestWrite`, `leafFn`: the honest writes of every leaf as functions of the
  challenges and the oracle, and the honest leaves of every position;
  `honestWrite_congr_oracle`: the honest writes depend on the oracle only through its answers.
* `overrun`: the samplers' rejection probabilities summed over all challenges of all leaves.
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

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t}
  {X : Type} (M : SPBCS Mg P X k kN kS L e)

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

end

end GordieHowe.SPBCS

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

/-! ### Query slots -/

variable (Mg : Merges t) (n : ι → ℕ) in
/-- **A query slot of the honest prover**: the chain input of round `r` of leaf `p` (`key`), the
stream point at its key (`xof`), the final input of the branch of site `s` (`fin`). -/
inductive QSlot where
  /-- The chain input of round `r` of leaf `p`. -/
  | key (p : t.Leaf) (r : Fin (n p.label))
  /-- The stream point at the key of round `r` of leaf `p`. -/
  | xof (p : t.Leaf) (r : Fin (n p.label))
  /-- The final input of the branch of site `s`. -/
  | fin (s : Mg.Site)

namespace QSlot

variable {Mg : Merges t} {n : ι → ℕ}

/-- The query slots as a sum type. -/
def equivSum : QSlot Mg n ≃
    ((Σ p : t.Leaf, Fin (n p.label)) ⊕ (Σ p : t.Leaf, Fin (n p.label))) ⊕ Mg.Site where
  toFun
    | key p r => .inl (.inl ⟨p, r⟩)
    | xof p r => .inl (.inr ⟨p, r⟩)
    | fin s => .inr s
  invFun
    | .inl (.inl a) => key a.1 a.2
    | .inl (.inr a) => xof a.1 a.2
    | .inr s => fin s
  left_inv u := by cases u <;> rfl
  right_inv a := by rcases a with (_ | _) | _ <;> rfl

instance : DecidableEq (QSlot Mg n) := equivSum.decidableEq

instance : Fintype (QSlot Mg n) := Fintype.ofEquiv _ equivSum.symm

/-- The observer of a slot: its leaf, or the sink of its site. -/
def obs : QSlot Mg n → Mg.Obs
  | key p _ => .leaf p
  | xof p _ => .leaf p
  | fin s => .sink s

/-- The order of a slot within its observer's step: `2r` for a chain input, `2r + 1` for its
stream point. -/
def sub : QSlot Mg n → ℕ
  | key _ r => 2 * r.1
  | xof _ r => 2 * r.1 + 1
  | fin _ => 0

/-- **A slot with a transcript query**: a chain input or a final input. -/
def IsTranscript : QSlot Mg n → Prop
  | xof _ _ => False
  | _ => True

/-- **The key of a slot**: the step of its observer, then its order within the step. -/
def rank (u : QSlot Mg n) : ℕ ×ₗ ℕ := toLex (u.obs.rank, u.sub)

/-- A slot whose observer is read by the observer of another has smaller key. -/
theorem rank_lt_of_reads {u v : QSlot Mg n} (h : u.obs.Reads v.obs) : v.rank < u.rank :=
  Prod.Lex.toLex_lt_toLex.2 (.inl (Merges.Obs.rank_lt_of_reads h))

/-- Within one observer, a slot of smaller order has smaller key. -/
theorem rank_lt_of_sub_lt {u v : QSlot Mg n} (ho : v.obs = u.obs) (h : v.sub < u.sub) :
    v.rank < u.rank :=
  Prod.Lex.toLex_lt_toLex.2 (.inr ⟨by rw [ho], h⟩)

end QSlot

variable (Mg : Merges t) (n : ι → ℕ)

/-- **The query slots in the prover's order**: sorted by key. -/
noncomputable def slots : List (QSlot Mg n) :=
  (Finset.univ : Finset (QSlot Mg n)).toList.mergeSort fun u v => decide (u.rank ≤ v.rank)

/-- The number of queries of the honest prover. -/
noncomputable def totalQ : ℕ := (slots Mg n).length

variable {Mg n}

/-- The position of a slot among the queries. -/
noncomputable def pos (u : QSlot Mg n) : ℕ := (slots Mg n).idxOf u

theorem mem_slots (u : QSlot Mg n) : u ∈ slots Mg n :=
  (List.mergeSort_perm _ _).mem_iff.2 (Finset.mem_toList.2 (Finset.mem_univ u))

theorem nodup_slots : (slots Mg n).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _)

theorem sorted_slots : (slots Mg n).Pairwise fun u v => decide (u.rank ≤ v.rank) = true :=
  List.pairwise_mergeSort (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact hab.trans hbc)
    (fun a b => by
      rcases le_total a.rank b.rank with h | h <;> simp [h]) _

theorem pos_lt (u : QSlot Mg n) : pos u < totalQ Mg n := List.idxOf_lt_length_of_mem (mem_slots u)

theorem getElem_pos (u : QSlot Mg n) : (slots Mg n)[pos u]'(pos_lt u) = u :=
  List.getElem_idxOf (xs := slots Mg n) (pos_lt u)

theorem getElem?_pos (u : QSlot Mg n) : (slots Mg n)[pos u]? = some u := by
  rw [List.getElem?_eq_getElem (pos_lt u), getElem_pos]

theorem pos_getElem {j : ℕ} (hj : j < totalQ Mg n) : pos ((slots Mg n)[j]'hj) = j :=
  List.Nodup.idxOf_getElem nodup_slots j hj

theorem pos_injective : Function.Injective (pos (Mg := Mg) (n := n)) := fun u v h => by
  rw [← getElem_pos u, ← getElem_pos v]
  exact getElem_congr_idx h

/-- **A slot of smaller key comes earlier.** -/
theorem pos_lt_pos {u v : QSlot Mg n} (h : u.rank < v.rank) : pos u < pos v := by
  rcases lt_trichotomy (pos u) (pos v) with hlt | heq | hgt
  · exact hlt
  · exact absurd (pos_injective heq ▸ h) (lt_irrefl _)
  · have := List.pairwise_iff_getElem.1 sorted_slots (pos v) (pos u) (pos_lt v) (pos_lt u) hgt
    rw [getElem_pos, getElem_pos, decide_eq_true_eq] at this
    exact absurd (lt_of_lt_of_le h this) (lt_irrefl _)

/-- The answer at position `j` of an answer list, a default where it is missing. -/
def ansAt (ws : List (Out k e)) (j : ℕ) : Out k e := (ws[j]?).getD SPBCS.defaultOut

/-- The first `m ≤ m'` queries of a strategy are distinct when the first `m'` are. -/
theorem nodup_qryList_of_le {A B : Type*} {q : ℕ → List B → (A → B) → A} {h : A → B} {m m' : ℕ}
    (hm : m ≤ m') (hnd : (qryList q h m').Nodup) : (qryList q h m).Nodup := by
  have : qryList q h m = (qryList q h m').take m := by
    simp only [qryList, ← List.map_take, List.take_range, Nat.min_eq_left hm]
  rw [this]
  exact hnd.sublist (List.take_sublist _ _)

section

variable {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

/-- The position of the stream point of a challenge. -/
noncomputable def posX (c : ChIdx P t) : ℕ := pos (Mg := Mg) (.xof c.leaf c.idx.1)

/-! ### The prover's chains from an answer list -/

variable [∀ j i, Nonempty ((P j).Challenge i)]

/-- **The challenges from the answers `ws`**: challenge `c` samples the answer at its stream
point (an arbitrary value where the sampler rejects). -/
noncomputable def chOfW (ws : List (Out k e)) : Chs P t := fun c =>
  (((M.comp c.leaf.label).sampler c.idx).sample (ansAt ws (posX (Mg := Mg) c)).stream).getD
    ((M.comp c.leaf.label).sampler c.idx).default

variable (prv : CausalProver P t X) (x : X) (σ : FiatShamirSalt kS)

variable {M} in
/-- **Round `r` of leaf `p`'s chain from the answers `ws`**: the write of the causal prover's
message at the challenges from `ws`, or the digest of the answer at the round's stream point. -/
noncomputable def itemW (wr : M.WriteFn) (ws : List (Out k e)) (p : t.Leaf) (r : ℕ) :
    Item k (M.comp p.label).W :=
  if hr : r < n p.label then
    if hd : (P p.label).dir ⟨r, hr⟩ = .P_to_V then
      .write ⟨⟨⟨r, hr⟩, hd⟩, wr p ⟨⟨r, hr⟩, hd⟩ (prv.run x (M.chOfW ws) p ⟨r, hr⟩)⟩
    else .absorb (ansAt ws (pos (Mg := Mg) (.xof p ⟨r, hr⟩))).digest
  else .absorb fun _ => 0

variable {M} in
/-- The first `r` items of leaf `p`'s chain from the answers `ws`. -/
noncomputable def chainW (wr : M.WriteFn) (ws : List (Out k e)) (p : t.Leaf) : ℕ → M.Items p
  | 0 => []
  | r + 1 => chainW wr ws p r ++ [itemW prv x wr ws p r]

variable {M} in
/-- The full chains from the answers `ws`. -/
noncomputable def chsW (wr : M.WriteFn) (ws : List (Out k e)) : M.Chains := fun p =>
  chainW prv x wr ws p (n p.label)

variable {M} in
/-- The final digests from the answers `ws`: the digest of the answer at each final input. -/
noncomputable def fsW (ws : List (Out k e)) (s : Mg.Site) : Digest k := (ansAt ws (pos (n := n) (.fin s))).digest

variable {M} in
/-- **The query at a slot** from the answers `ws` of the slots before it. -/
noncomputable def queryW (wr : M.WriteFn) (ws : List (Out k e)) : QSlot Mg n → Query k kN kS L
  | .key p r => .transcript (M.senc.encode (roundContent ⟨σ, x⟩ (chsW prv x wr ws)
      (fsW (n := n) ws) p (chainW prv x wr ws p r)))
  | .xof p r => .xof (ansAt ws (pos (Mg := Mg) (.key p r))).digest σ
  | .fin s => .transcript (M.senc.encode (finalContent ⟨σ, x⟩ (chsW prv x wr ws)
      (fsW (n := n) ws) s))

/-- **The queries of a prover with write function `wrOf h`** as an adaptive strategy: query `j`
is the query at slot `j`. -/
noncomputable def strategy (wrOf : (Query k kN kS L → Out k e) → M.WriteFn) (j : ℕ)
    (ws : List (Out k e)) (h : Query k kN kS L → Out k e) : Query k kN kS L :=
  match (slots Mg n)[j]? with
  | some u => queryW prv x σ (wrOf h) ws u
  | none => .xof (SPBCS.defaultOut (k := k) (e := e)).digest σ

/-! ### What the queries read -/

section Congr

variable {M} (wr : M.WriteFn)

theorem length_chainW (ws : List (Out k e)) (p : t.Leaf) :
    ∀ r, (chainW prv x wr ws p r).length = r
  | 0 => rfl
  | r + 1 => by simp [chainW, length_chainW ws p r]

theorem chainW_getElem? (ws : List (Out k e)) (p : t.Leaf) :
    ∀ r j, j < r → (chainW prv x wr ws p r)[j]? = some (itemW prv x wr ws p j)
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, j, hj => by
    rw [chainW]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem?_append_left (by rw [length_chainW]; exact hj'),
        chainW_getElem? ws p r j hj']
    · rw [List.getElem?_append_right (by rw [length_chainW]), length_chainW]
      simp

/-- Chains from answers are well formed. -/
theorem chainWF_chainW (ws : List (Out k e)) (p : t.Leaf) {r : ℕ} (hr : r ≤ n p.label) :
    chainWF (P p.label) (chainW prv x wr ws p r) := by
  intro j hj
  rw [length_chainW] at hj
  have hget := chainW_getElem? prv x wr ws p r j hj
  rw [List.getElem?_eq_getElem (by rw [length_chainW]; exact hj)] at hget
  rw [Option.some_inj.1 hget]
  unfold itemW
  have hjn : j < n p.label := by omega
  rw [dite_eq_left hjn]
  by_cases hd : (P p.label).dir ⟨j, hjn⟩ = .P_to_V
  · rw [dite_eq_left hd]
    rfl
  · rw [dite_eq_right hd]
    exact ⟨hjn, by cases h' : (P p.label).dir ⟨j, hjn⟩ <;> simp_all⟩

/-- **Leaf `p`'s first `r` items read the answers only at the stream points of the challenges of
the leaves before `p` and of `p`'s challenges before round `r`.** -/
theorem chainW_congr {ws ws' : List (Out k e)} (p : t.Leaf)
    (hb : ∀ c : ChIdx P t, c.leaf.Before p → ansAt ws (posX (Mg := Mg) c) = ansAt ws' (posX (Mg := Mg) c)) :
    ∀ r, (∀ j : (P p.label).ChallengeIdx, j.1.1 < r →
      ansAt ws (posX (Mg := Mg) ⟨p, j⟩) = ansAt ws' (posX (Mg := Mg) ⟨p, j⟩)) →
      chainW prv x wr ws p r = chainW prv x wr ws' p r
  | 0, _ => rfl
  | r + 1, ho => by
    rw [chainW, chainW, chainW_congr p hb r fun j hj => ho j (by omega)]
    congr 2
    unfold itemW
    by_cases hr : r < n p.label
    · rw [dite_eq_left hr, dite_eq_left hr]
      by_cases hd : (P p.label).dir ⟨r, hr⟩ = .P_to_V
      · rw [dite_eq_left hd, dite_eq_left hd]
        congr 3
        refine CausalProver.run_message_congr prv x p ⟨⟨r, hr⟩, hd⟩
          (fun c hc => by simp only [chOfW]; rw [hb c hc]) fun j hj => ?_
        simp only [chOfW]
        rw [ho j (by have : j.1.1 < r := hj; omega)]
      · rw [dite_eq_right hd, dite_eq_right hd]
        have hc : (P p.label).dir ⟨r, hr⟩ = .V_to_P := by
          cases h' : (P p.label).dir ⟨r, hr⟩ <;> simp_all
        have := ho ⟨⟨r, hr⟩, hc⟩ (Nat.lt_succ_self r)
        simp only [posX] at this
        rw [this]
    · rw [dite_eq_right hr, dite_eq_right hr]

/-- **The query at a slot reads the answers only at the slots of smaller key.** -/
theorem queryW_congr {ws ws' : List (Out k e)} (u : QSlot Mg n)
    (hag : ∀ v : QSlot Mg n, v.rank < u.rank → ansAt ws (pos v) = ansAt ws' (pos v)) :
    queryW prv x σ wr ws u = queryW prv x σ wr ws' u := by
  -- the full chains of the leaves the observer of `u` reads
  have hchs : ∀ q : t.Leaf, u.obs.Sees q → chsW prv x wr ws q = chsW prv x wr ws' q := by
    intro q hq
    refine chainW_congr prv x wr q (fun c hc => hag _ (QSlot.rank_lt_of_reads ?_)) _ fun j _ =>
      hag _ (QSlot.rank_lt_of_reads hq)
    show u.obs.Sees c.leaf
    cases hu : u.obs with
    | leaf p =>
      rw [hu] at hq
      exact hc.trans hq
    | sink s =>
      rw [hu] at hq
      exact Merges.sees_sink_of_before hq hc
  have hfs : ∀ s, Mg.Hides s u.obs → fsW ws s = fsW (n := n) ws' s := fun s hs => by
    unfold fsW
    rw [hag _ (QSlot.rank_lt_of_reads (v := .fin s) hs)]
  cases u with
  | key p r =>
    simp only [queryW, roundContent]
    rw [Merges.Obs.viewChains_congr (Merges.Obs.leaf p) fun q hq => hchs q hq.1,
      Merges.Obs.viewDs_congr (Merges.Obs.leaf p) hfs,
      chainW_congr prv x wr p (fun c hc => hag _ (QSlot.rank_lt_of_reads (v := .xof c.leaf c.idx.1)
        (u := .key p r) hc)) r fun j hj => hag _ (QSlot.rank_lt_of_sub_lt rfl (by
          simp only [QSlot.sub]; omega))]
  | xof p r =>
    simp only [queryW]
    rw [hag (.key p r) (QSlot.rank_lt_of_sub_lt rfl (by simp [QSlot.sub]))]
  | fin s =>
    simp only [queryW, finalContent]
    rw [Merges.Obs.viewChains_congr (Merges.Obs.sink s) fun q hq => hchs q hq.1,
      Merges.Obs.viewDs_congr (Merges.Obs.sink s) hfs]

end Congr

/-! ### The answers -/

theorem ansAt_ansList_of_le {q : ℕ → List (Out k e) → (Query k kN kS L → Out k e) → Query k kN kS L}
    {h : Query k kN kS L → Out k e} {m m' j : ℕ} (hm : m ≤ m') (hj : j < m) :
    ansAt (ansList q h m) j = ansAt (ansList q h m') j := by
  unfold ansAt
  rw [← take_ansList q h hm, List.getElem?_take, ite_eq_left hj]

section Answers

variable {M} (wrOf : (Query k kN kS L → Out k e) → M.WriteFn) (h : Query k kN kS L → Out k e)

/-- **The answers of a prover with write function `wrOf h`** to its queries against `h`. -/
noncomputable def answersW : List (Out k e) := ansList (strategy M prv x σ wrOf) h (totalQ Mg n)

theorem strategy_pos (u : QSlot Mg n) (ws : List (Out k e)) :
    strategy M prv x σ wrOf (pos u) ws h = queryW prv x σ (wrOf h) ws u := by
  simp only [strategy, getElem?_pos]

/-- **The answer at a slot is the oracle at the slot's query**, computed from all answers. -/
theorem ansAt_answersW (u : QSlot Mg n) :
    ansAt (answersW prv x σ wrOf h) (pos u) =
      h (queryW prv x σ (wrOf h) (answersW prv x σ wrOf h) u) := by
  have hlt := pos_lt u
  have h1 : ansAt (answersW prv x σ wrOf h) (pos u) =
      h (strategy M prv x σ wrOf (pos u) (ansList (strategy M prv x σ wrOf) h (pos u)) h) := by
    unfold ansAt answersW
    rw [List.getElem?_eq_getElem (by simp; exact hlt), getElem_ansList _ _ hlt]
    rfl
  rw [h1, strategy_pos]
  congr 1
  exact queryW_congr prv x σ (wrOf h) u fun v hv => ansAt_ansList_of_le hlt.le (pos_lt_pos hv)

end Answers

/-! ### The verifier's chains -/

section Verifier

variable {M} (wrOf : (Query k kN kS L → Out k e) → M.WriteFn) (h : Query k kN kS L → Out k e)
  (wr : M.Writes)
  (hw : ∀ p i, wr p i = wrOf h p i (prv.run x (M.chOfW (answersW prv x σ wrOf h)) p i.1))

/-- **The final digests from the answers solve their equation**, so they are the final digests
at the chains from the answers. -/
theorem finalsWith_chsW :
    M.finalsWith h ⟨σ, x⟩ (chsW prv x (wrOf h) (answersW prv x σ wrOf h)) =
      fsW (n := n) (answersW prv x σ wrOf h) :=
  (eq_finalsWith (M := M) (h := h) (ss := ⟨σ, x⟩) fun s => by
    unfold fsW finalStep
    rw [ansAt_answersW prv x σ wrOf h (.fin s)]
    rfl).symm

include hw

/-- **The verifier's chain of a leaf at the chains and final digests from the answers** is the
prover's. -/
theorem chainWith_eq_chainW (p : t.Leaf) : ∀ r (hr : r ≤ n p.label),
    (M.comp p.label).chainWith (wr p) (M.key h ⟨σ, x⟩
      (chsW prv x (wrOf h) (answersW prv x σ wrOf h)) (fsW (n := n) (answersW prv x σ wrOf h)) p) σ h r hr =
      chainW prv x (wrOf h) (answersW prv x σ wrOf h) p r
  | 0, _ => rfl
  | r + 1, hr => by
    rw [ComponentModel.chainWith, chainW, chainWith_eq_chainW p r (by omega)]
    congr 2
    unfold ComponentModel.itemWith itemW
    rw [dite_eq_left (show r < n p.label by omega)]
    by_cases hd : (P p.label).dir ⟨r, by omega⟩ = .P_to_V
    · rw [dite_eq_left hd, dite_eq_left hd]
      exact congrArg (fun w => (Item.write ⟨⟨⟨r, by omega⟩, hd⟩, w⟩ : Item k (M.comp p.label).W))
        (hw p _)
    · rw [dite_eq_right hd, dite_eq_right hd, ansAt_answersW prv x σ wrOf h (.xof p ⟨r, by omega⟩)]
      simp only [queryW]
      rw [ansAt_answersW prv x σ wrOf h (.key p ⟨r, by omega⟩)]
      rfl

/-- **The verifier's chains on a proof carrying the writes of a prover** are the prover's, leaf by
leaf in causal order. -/
theorem chains_eq_chsW (p : t.Leaf) :
    M.chains h ⟨σ, x⟩ wr p = chsW prv x (wrOf h) (answersW prv x σ wrOf h) p := by
  induction p using (wellFounded_before t).induction with
  | _ p ih =>
    rw [chains_eq, leafChain_congr wr (chs' := chsW prv x (wrOf h) (answersW prv x σ wrOf h)) ih]
    unfold leafChain
    rw [finalsWith_chsW]
    exact chainWith_eq_chainW prv x σ wrOf h wr hw p _ le_rfl

theorem chains_eq_chsW' :
    M.chains h ⟨σ, x⟩ wr = chsW prv x (wrOf h) (answersW prv x σ wrOf h) :=
  funext (chains_eq_chsW prv x σ wrOf h wr hw)

/-- The verifier's final digests on such a proof are the prover's. -/
theorem finals_eq_fsW : M.finals h ⟨σ, x⟩ wr = fsW (n := n) (answersW prv x σ wrOf h) := by
  unfold finals
  rw [chains_eq_chsW' prv x σ wrOf h wr hw, finalsWith_chsW]

/-- **The verifier's challenges on such a proof** are sampled from the answers at their stream
points. -/
theorem chal_eq (c : ChIdx P t) : M.chal h ⟨σ, x⟩ wr c =
    ((M.comp c.leaf.label).sampler c.idx).sample
      (ansAt (answersW prv x σ wrOf h) (posX (Mg := Mg) c)).stream := by
  unfold chal ComponentModel.chalWith
  rw [chains_eq_chsW' prv x σ wrOf h wr hw, finals_eq_fsW prv x σ wrOf h wr hw,
    chainWith_eq_chainW prv x σ wrOf h wr hw, posX, ansAt_answersW prv x σ wrOf h (.xof _ _)]
  simp only [queryW]
  rw [ansAt_answersW prv x σ wrOf h (.key _ _)]
  rfl

theorem chV_eq : M.chV h ⟨σ, x⟩ wr = M.chOfW (answersW prv x σ wrOf h) := by
  funext c
  rw [chV, chal_eq prv x σ wrOf h wr hw c]
  rfl

end Verifier

/-! ### The honest proof -/

section HonestProof

variable {M} (E : (j : ι) → (M.comp j).Encoder) (ν : M.Pos → MerkleSalt kN)
  (h : Query k kN kS L → Out k e)

/-- The answers to the honest prover's queries. -/
noncomputable def answers : List (Out k e) :=
  answersW prv x σ (SPBCS.honestWrite (M := M) E ν) h

/-- The honest prover's chains. -/
noncomputable def honestChains : M.Chains :=
  chsW prv x (SPBCS.honestWrite E ν h) (answers prv x σ E ν h)

/-- The honest prover's challenges. -/
noncomputable def honestCh : Chs P t := M.chOfW (answers prv x σ E ν h)

variable {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x)

/-- The positions the honest prover opens. -/
noncomputable def honestPos : List M.Pos :=
  Q.pos (honestChains prv x σ E ν h) (honestCh prv x σ E ν h)

/-- The opened leaves of the honest prover, in the order of the positions. -/
noncomputable def honestLeaves : List (MerkleLeaf kN L) :=
  (honestPos prv x σ E ν h Q).map fun q =>
    SPBCS.leafFn E ν q.leaf q.pos.msg (prv.run x (honestCh prv x σ E ν h) q.leaf q.pos.msg.1)
      q.pos.tree q.pos.leaf

/-- **The honest non-interactive spBCS prover** for the query phase `Q`: the causal prover
`prv` compiled against `h` with the Merkle salts `ν` and the Fiat–Shamir salt `σ`: the salt, the
honest write of every prover round of every leaf at the challenges from the honest answers, the
opened leaves and the honest opening of every tree (`MerkleFormat.path`). -/
noncomputable def prove : M.NIProof where
  salt := σ
  writes p i := SPBCS.honestWrite E ν h p i (prv.run x (honestCh prv x σ E ν h) p i.1)
  leaves := honestLeaves prv x σ E ν h Q
  paths τ := M.opening.path h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
    ((M.openedIn τ (honestPos prv x σ E ν h Q) (honestLeaves prv x σ E ν h Q)).map Prod.fst)
    (SPBCS.leafFn E ν τ.leaf τ.tree.msg
      (prv.run x (honestCh prv x σ E ν h) τ.leaf τ.tree.msg.1) τ.tree.tree)

theorem chains_prove :
    M.chains h ⟨σ, x⟩ (prove prv x σ E ν h Q).writes = honestChains prv x σ E ν h :=
  chains_eq_chsW' prv x σ _ h _ fun _ _ => rfl

theorem chV_prove :
    M.chV h ⟨σ, x⟩ (prove prv x σ E ν h Q).writes = honestCh prv x σ E ν h :=
  chV_eq prv x σ _ h _ fun _ _ => rfl

theorem chal_prove (c : ChIdx P t) :
    M.chal h ⟨σ, x⟩ (prove prv x σ E ν h Q).writes c =
      ((M.comp c.leaf.label).sampler c.idx).sample
        (ansAt (answers prv x σ E ν h) (posX (Mg := Mg) c)).stream :=
  chal_eq (M := M) prv x σ (SPBCS.honestWrite E ν) h _ (fun _ _ => rfl) c

/-- **The honest proof is accepted** when every challenge's sampler accepts its stream and the
composite verifier accepts the causal prover's run at the challenges from the honest answers. -/
theorem accepts_prove
    (hs : ∀ c : ChIdx P t, (((M.comp c.leaf.label).sampler c.idx).sample
      (ansAt (answers prv x σ E ν h) (posX (Mg := Mg) c)).stream).isSome)
    (hV : V x (prv.run x (honestCh prv x σ E ν h)) = true) :
    M.Accepts h x (prove prv x σ E ν h Q) Q := by
  classical
  set π := prove prv x σ E ν h Q with hπ
  have hl : M.chains h ⟨π.salt, x⟩ π.writes = honestChains prv x σ E ν h :=
    chains_prove prv x σ E ν h Q
  have hc : M.chV h ⟨π.salt, x⟩ π.writes = honestCh prv x σ E ν h := chV_prove prv x σ E ν h Q
  have hpos : Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes) =
      honestPos prv x σ E ν h Q := by
    rw [hl, hc]
    rfl
  let f : M.Pos → MerkleLeaf kN L := fun q =>
    SPBCS.leafFn E ν q.leaf q.pos.msg (prv.run x (honestCh prv x σ E ν h) q.leaf q.pos.msg.1)
      q.pos.tree q.pos.leaf
  have hleaves : π.leaves = (honestPos prv x σ E ν h Q).map f := rfl
  refine ⟨fun c => by
    rw [show M.chal h ⟨π.salt, x⟩ π.writes c = _ from chal_prove prv x σ E ν h Q c]
    exact hs c, ?_, ?_, ?_⟩
  · rw [hpos, hleaves, List.length_map]
  · intro τ hτ
    rw [hpos] at hτ ⊢
    obtain ⟨p, ⟨i, τ₀⟩⟩ := τ
    set ps := honestPos prv x σ E ν h Q
    have hop := M.openedIn_map f ⟨p, ⟨i, τ₀⟩⟩ ps
    have hsel : ∀ q ∈ ps.filter (fun q => decide (q.treeOf = (⟨p, ⟨i, τ₀⟩⟩ : M.Tree))),
        q.treeOf = ⟨p, ⟨i, τ₀⟩⟩ := fun q hq => by simpa using (List.mem_filter.1 hq).2
    have hroot : (M.comp p.label).rootOf i (π.writes p i) τ₀ =
        MerkleTree.root h ((M.comp p.label).nLeaves i τ₀)
          (SPBCS.leafFn E ν p i (prv.run x (honestCh prv x σ E ν h) p i.1) τ₀) :=
      (E p.label).rootOf_write _ _ _ _
    have hpath : π.paths ⟨p, ⟨i, τ₀⟩⟩ = M.opening.path h ((M.comp p.label).nLeaves i τ₀)
        ((M.openedIn ⟨p, ⟨i, τ₀⟩⟩ ps (ps.map f)).map Prod.fst)
        (SPBCS.leafFn E ν p i (prv.run x (honestCh prv x σ E ν h) p i.1) τ₀) := rfl
    unfold SPBCS.checkTree
    rw [hroot, hpath, hleaves, hop]
    simp only [List.map_map]
    refine M.opening.check_path h ?_ ?_ ?_ ?_
    · refine List.Nodup.map_on (fun q hq q' hq' he =>
        SPBCS.Pos.eq_of_treeOf_eq M (hsel q hq) (hsel q' hq') he)
        ((Q.pos_nodup _ _).filter _)
    · intro j hj
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
      obtain ⟨p', ⟨i', τ', j'⟩⟩ := q
      obtain ⟨rfl, he⟩ := SPBCS.Tree.mk.inj (hsel _ hq)
      obtain ⟨rfl, he⟩ := TreeIdx.mk.inj (eq_of_heq he)
      obtain rfl := eq_of_heq he
      exact j'.2
    · obtain ⟨q, hq, hqτ⟩ := List.mem_map.1 (List.mem_dedup.1 hτ)
      exact List.ne_nil_of_mem (List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by simpa using hqτ⟩, rfl⟩)
    · refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (List.forall₂_same.2 ?_))
      intro q hq
      obtain ⟨p', ⟨i', τ', j'⟩⟩ := q
      obtain ⟨rfl, he⟩ := SPBCS.Tree.mk.inj (hsel _ hq)
      obtain ⟨rfl, he⟩ := TreeIdx.mk.inj (eq_of_heq he)
      obtain rfl := eq_of_heq he
      rfl
  · let vw : M.Views := fun p i τ₀ =>
      ⟨fun _ => none, fun j =>
        some (SPBCS.leafFn E ν p i (prv.run x (honestCh prv x σ E ν h) p i.1) τ₀ j)⟩
    rw [hleaves, ← hpos]
    refine Q.verdict_of_accept _ _ vw (prv.run x (M.chV h ⟨π.salt, x⟩ π.writes)) _
      (fun p i => ⟨_, chains_getElem?_message (M := M) (h := h) (ss := ⟨π.salt, x⟩) π.writes p i⟩) ?_
      (CausalProver.challenges_run prv x _) ?_ (by rw [hc]; exact hV)
    · intro p i w hw
      have h2 := chains_getElem?_message (M := M) (h := h) (ss := ⟨π.salt, x⟩) π.writes p i
      rw [hw] at h2
      have hw' : w = π.writes p i :=
        eq_of_heq (Sigma.mk.inj (Item.write.inj (Option.some_inj.1 h2))).2
      subst hw'
      rw [hc]
      exact ((E p.label).msg_write _ _ _ _ fun τ₀ j =>
        ⟨ν ⟨p, ⟨i, τ₀, j⟩⟩, by simp [vw, SPBCS.leafFn_val]⟩).symm
    · rw [hpos]
      exact List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun q _ => rfl)

end HonestProof

/-! ### Distinct transcript queries -/

section Distinct

variable {M} (wr : M.WriteFn)

/-- **The content of a round's chain input from answers is well formed.** -/
theorem wf_roundContent (ws : List (Out k e)) (p : t.Leaf) (r : Fin (n p.label)) :
    (roundContent (M := M) ⟨σ, x⟩ (chsW prv x wr ws) (fsW (n := n) ws) p
      (chainW prv x wr ws p r)).WF n fun j => chainWF (P j) := by
  unfold roundContent
  exact .round (Content.viewWF_view _ (fun q _ => chainWF_chainW prv x wr ws q le_rfl)
    (fun q _ => length_chainW prv x wr ws q _) _) (chainWF_chainW prv x wr ws p r.2.le)
    (by rw [length_chainW]; exact r.2)

/-- **The content of a final input from answers is well formed.** -/
theorem wf_finalContent (ws : List (Out k e)) (s : Mg.Site) :
    (finalContent (M := M) ⟨σ, x⟩ (chsW prv x wr ws) (fsW (n := n) ws) s).WF n
      fun j => chainWF (P j) := by
  unfold finalContent
  exact .final (Content.viewWF_view _ (fun q _ => chainWF_chainW prv x wr ws q le_rfl)
    (fun q _ => length_chainW prv x wr ws q _) _)

/-- **Distinct transcript slots have distinct queries**, whatever answers they read: their
contents are well formed and differ in their kind, leaf, site or number of own items. -/
theorem eq_of_queryW_eq {ws ws' : List (Out k e)} {u v : QSlot Mg n} (hu : u.IsTranscript)
    (hv : v.IsTranscript) (he : queryW prv x σ wr ws u = queryW prv x σ wr ws' v) : u = v := by
  cases u with
  | xof => exact hu.elim
  | key p r =>
    cases v with
    | xof => exact hv.elim
    | key p' r' =>
      have hc := M.senc.encode_injective (wf_roundContent prv x σ wr ws p r)
        (wf_roundContent prv x σ wr ws' p' r') (Query.transcript.inj he)
      unfold roundContent at hc
      obtain ⟨-, rfl, -, -, hown⟩ := Content.round.inj hc
      have hl := congrArg List.length (eq_of_heq hown)
      rw [length_chainW, length_chainW] at hl
      rw [Fin.ext hl]
    | fin s' =>
      have hc := M.senc.encode_injective (wf_roundContent prv x σ wr ws p r)
        (wf_finalContent prv x σ wr ws' s') (Query.transcript.inj he)
      unfold roundContent finalContent at hc
      cases hc
  | fin s =>
    cases v with
    | xof => exact hv.elim
    | key p' r' =>
      have hc := M.senc.encode_injective (wf_finalContent prv x σ wr ws s)
        (wf_roundContent prv x σ wr ws' p' r') (Query.transcript.inj he)
      unfold roundContent finalContent at hc
      cases hc
    | fin s' =>
      have hc := M.senc.encode_injective (wf_finalContent prv x σ wr ws s)
        (wf_finalContent prv x σ wr ws' s') (Query.transcript.inj he)
      unfold finalContent at hc
      obtain ⟨-, rfl, -, -⟩ := Content.final.inj hc
      rfl

end Distinct

/-! ### The probability bound -/

section Bound

variable {M} (wrOf : (Query k kN kS L → Out k e) → M.WriteFn)

theorem isChainQuery_strategy (j : ℕ) (ws : List (Out k e)) (h : Query k kN kS L → Out k e) :
    SPBCS.IsChainQuery (strategy M prv x σ wrOf j ws h) := by
  unfold strategy
  split
  · rename_i u _
    cases u <;> trivial
  · trivial

theorem strategy_congr_oracle
    (hwr : ∀ h₁ h₂ : Query k kN kS L → Out k e,
      (∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) → wrOf h₁ = wrOf h₂)
    (j : ℕ) (ws : List (Out k e)) (h₁ h₂ : Query k kN kS L → Out k e)
    (hq : ∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) :
    strategy M prv x σ wrOf j ws h₁ = strategy M prv x σ wrOf j ws h₂ := by
  simp only [strategy]
  rw [hwr _ _ hq]

/-- The position of a round's chain input. -/
noncomputable def posK (a : Σ p : t.Leaf, Fin (n p.label)) : ℕ := pos (Mg := Mg) (.key a.1 a.2)

/-- **A key collision between the rounds `a` and `b`**: `a`'s chain input comes first, the
queries through `b`'s chain input are distinct, and the answers to the two chain inputs have the
same digest. -/
def KeyColl (h : Query k kN kS L → Out k e) (a b : Σ p : t.Leaf, Fin (n p.label)) : Prop :=
  posK (Mg := Mg) a < posK (Mg := Mg) b ∧
    (qryList (strategy M prv x σ wrOf) h (posK (Mg := Mg) b + 1)).Nodup ∧
    (ansAt (ansList (strategy M prv x σ wrOf) h (posK (Mg := Mg) b + 1)) (posK (Mg := Mg) b)).digest =
      (ansAt (ansList (strategy M prv x σ wrOf) h (posK (Mg := Mg) b + 1)) (posK (Mg := Mg) a)).digest

/-- **If a prover's queries repeat, two rounds collide**: transcript queries never repeat
(`eq_of_queryW_eq`), so the first repeat is a stream query at the digest of an earlier chain
input's answer. -/
theorem exists_keyColl_of (h : Query k kN kS L → Out k e)
    (hnd : ¬ (qryList (strategy M prv x σ wrOf) h (totalQ Mg n)).Nodup) :
    ∃ a b, KeyColl prv x σ wrOf h a b := by
  set q := strategy M prv x σ wrOf
  obtain ⟨j, hj, hnd', hmem⟩ := exists_first_dup h (totalQ Mg n) hnd
  obtain ⟨i, hi, hqi⟩ := List.mem_map.1 hmem
  rw [List.mem_range] at hi
  obtain ⟨u, rfl⟩ : ∃ u : QSlot Mg n, pos u = j := ⟨_, pos_getElem hj⟩
  obtain ⟨v, rfl⟩ : ∃ v : QSlot Mg n, pos v = i := ⟨_, pos_getElem (lt_trans hi hj)⟩
  change q (pos v) _ h = q (pos u) _ h at hqi
  simp only [q, strategy_pos] at hqi
  have hne : v ≠ u := fun he => by
    rw [he] at hi
    exact lt_irrefl _ hi
  cases u with
  | key p r =>
    cases v with
    | xof => cases hqi
    | _ => exact absurd (eq_of_queryW_eq prv x σ _ (by trivial) (by trivial) hqi) hne
  | fin s =>
    cases v with
    | xof => cases hqi
    | _ => exact absurd (eq_of_queryW_eq prv x σ _ (by trivial) (by trivial) hqi) hne
  | xof p r =>
    cases v with
    | key => cases hqi
    | fin => cases hqi
    | xof p' r' =>
      obtain ⟨hd, -⟩ := Query.xof.inj hqi
      have hku : pos (Mg := Mg) (.key p r) < pos (Mg := Mg) (.xof p r) :=
        pos_lt_pos (QSlot.rank_lt_of_sub_lt rfl (by simp [QSlot.sub]))
      have hkv : pos (Mg := Mg) (.key p' r') < pos (Mg := Mg) (.xof p' r') :=
        pos_lt_pos (QSlot.rank_lt_of_sub_lt rfl (by simp [QSlot.sub]))
      rw [ansAt_ansList_of_le hi.le hkv] at hd
      have hab : (⟨p, r⟩ : Σ p : t.Leaf, Fin (n p.label)) ≠ ⟨p', r'⟩ := fun he => by
        obtain ⟨rfl, hr⟩ := Sigma.mk.inj he
        obtain rfl := eq_of_heq hr
        exact hne rfl
      have hpk : posK (Mg := Mg) ⟨p, r⟩ ≠ posK (Mg := Mg) ⟨p', r'⟩ := fun he => by
        have := pos_injective he
        simp only [QSlot.key.injEq] at this
        obtain ⟨rfl, hr⟩ := this
        exact hab (by rw [eq_of_heq hr])
      rcases lt_or_gt_of_ne hpk with hlt | hlt
      · refine ⟨⟨p, r⟩, ⟨p', r'⟩, hlt, ?_⟩
        simp only [posK] at hlt ⊢
        refine ⟨nodup_qryList_of_le (by omega) hnd', ?_⟩
        rw [ansAt_ansList_of_le (j := pos (Mg := Mg) (.key p' r'))
            (m' := pos (Mg := Mg) (.xof p r)) (by omega) (Nat.lt_succ_self _),
          ansAt_ansList_of_le (j := pos (Mg := Mg) (.key p r))
            (m' := pos (Mg := Mg) (.xof p r)) (by omega) (by omega)]
        exact hd
      · refine ⟨⟨p', r'⟩, ⟨p, r⟩, hlt, ?_⟩
        simp only [posK] at hlt ⊢
        refine ⟨nodup_qryList_of_le (by omega) hnd', ?_⟩
        rw [ansAt_ansList_of_le (j := pos (Mg := Mg) (.key p r))
            (m' := pos (Mg := Mg) (.xof p r)) (by omega) (Nat.lt_succ_self _),
          ansAt_ansList_of_le (j := pos (Mg := Mg) (.key p' r'))
            (m' := pos (Mg := Mg) (.xof p r)) (by omega) (by omega)]
        exact hd.symm

/-- A key collision of two given rounds has probability at most `2^(-8k)`. -/
theorem prob_keyColl_le
    (hwr : ∀ h₁ h₂ : Query k kN kS L → Out k e,
      (∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) → wrOf h₁ = wrOf h₂)
    (a b : Σ p : t.Leaf, Fin (n p.label)) :
    Pr[h ← (Query k kN kS L → Out k e) : KeyColl prv x σ wrOf h a b] ≤ 1 / 2 ^ (8 * k) := by
  classical
  by_cases hlt : posK (Mg := Mg) a < posK (Mg := Mg) b
  · let G : (Fin (posK (Mg := Mg) b + 1) → Out k e) → Prop := fun v =>
      (v ⟨posK (Mg := Mg) b, by omega⟩).digest = (v ⟨posK (Mg := Mg) a, by omega⟩).digest
    calc _ ≤ Pr[h ← (Query k kN kS L → Out k e) :
          (qryList (strategy M prv x σ wrOf) h (posK (Mg := Mg) b + 1)).Nodup ∧
          G fun j => (ansList (strategy M prv x σ wrOf) h
            (posK (Mg := Mg) b + 1))[j.1]'(by rw [length_ansList]; exact j.2)] :=
          QROM.probUniform_mono fun h ⟨_, hnd, he⟩ => by
            refine ⟨hnd, ?_⟩
            unfold ansAt at he
            rw [List.getElem?_eq_getElem (by simp), List.getElem?_eq_getElem (by simp; omega)] at he
            simpa [G] using he
      _ ≤ Pr[v ← (Fin (posK (Mg := Mg) b + 1) → Out k e) : G v] :=
          prob_nodup_ansList_le (fun j ws h => isChainQuery_strategy prv x σ wrOf j ws h)
            (strategy_congr_oracle prv x σ wrOf hwr) _ G
      _ ≤ _ := SPBCS.prob_digest_eq_le (by simp [Fin.ext_iff]; omega)
  · rw [probUniform_eq_zero fun h hk => hlt hk.1]
    simp

/-- **A prover's queries repeat with probability at most `keyCollision (t.size n) k`**, for a
write function that reads only `leaf` and `node` queries (`hwr`): a repeat is a key collision of
two of the `t.size n` rounds (`exists_keyColl_of`). -/
theorem prob_not_nodup_le
    (hwr : ∀ h₁ h₂ : Query k kN kS L → Out k e,
      (∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) → wrOf h₁ = wrOf h₂) :
    Pr[h ← (Query k kN kS L → Out k e) :
        ¬ (qryList (strategy M prv x σ wrOf) h (totalQ Mg n)).Nodup] ≤
      SPBCS.keyCollision (t.size n) k := by
  classical
  set T : Finset (Σ p : t.Leaf, Fin (n p.label)) := Finset.univ
  have hT : T.card = t.size n := by
    rw [Finset.card_univ, Fintype.card_sigma, size_eq_sum]
    simp
  calc _ ≤ Pr[h ← (Query k kN kS L → Out k e) : ∃ s : ↥(T.powersetCard 2), ∃ a ∈ s.1, ∃ b ∈ s.1,
        KeyColl prv x σ wrOf h a b] :=
        QROM.probUniform_mono fun h hh => by
          obtain ⟨a, b, hk⟩ := exists_keyColl_of prv x σ wrOf h hh
          have hab : a ≠ b := fun he => by
            subst he
            exact lt_irrefl _ hk.1
          exact ⟨⟨{a, b}, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, Finset.card_pair hab⟩⟩,
            a, by simp, b, by simp, hk⟩
    _ ≤ ∑ s : ↥(T.powersetCard 2), Pr[h ← (Query k kN kS L → Out k e) : ∃ a ∈ s.1, ∃ b ∈ s.1,
        KeyColl prv x σ wrOf h a b] := probUniform_exists_le _
    _ ≤ ∑ s : ↥(T.powersetCard 2), (1 : ℝ≥0∞) / 2 ^ (8 * k) := Finset.sum_le_sum fun s _ => by
        obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 s.2).2
        rw [hs]
        by_cases hlt : posK (Mg := Mg) a < posK (Mg := Mg) b
        · refine (QROM.probUniform_mono fun h hh => ?_).trans (prob_keyColl_le prv x σ wrOf hwr a b)
          obtain ⟨c, hc, d, hd, hk⟩ := hh
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
          rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
          · exact absurd hk.1 (lt_irrefl _)
          · exact hk
          · exact absurd hk.1 (lt_asymm hlt)
          · exact absurd hk.1 (lt_irrefl _)
        · refine (QROM.probUniform_mono fun h hh => ?_).trans (prob_keyColl_le prv x σ wrOf hwr b a)
          obtain ⟨c, hc, d, hd, hk⟩ := hh
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
          rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
          · exact absurd hk.1 (lt_irrefl _)
          · exact absurd hk.1 hlt
          · exact hk
          · exact absurd hk.1 (lt_irrefl _)
    _ = SPBCS.keyCollision (t.size n) k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard, hT,
          SPBCS.keyCollision, nsmul_eq_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          mul_one, mul_comm]

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] in
/-- Distinct challenges have distinct stream points. -/
theorem posX_injective : Function.Injective (posX (Mg := Mg) (P := P)) := fun c c' he => by
  have := pos_injective he
  obtain ⟨p, i⟩ := c
  obtain ⟨p', i'⟩ := c'
  simp only [QSlot.xof.injEq] at this
  obtain ⟨rfl, hi⟩ := this
  rw [Subtype.ext (eq_of_heq hi)]

open Classical in
/-- **Fiat–Shamir challenges with merges are dominated by uniform challenges**: for a prover whose
write function reads the oracle only off the chain queries, over a uniform oracle the probability
that some sampler rejects or that the challenges from the answers lie in `B` is at most
`Pr[B] + overrun + keyCollision (t.size n) k` under uniform challenges. -/
theorem prob_sample_none_or_chOfW_mem_le
    (hwr : ∀ h₁ h₂ : Query k kN kS L → Out k e,
      (∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) → wrOf h₁ = wrOf h₂)
    (B : Chs P t → Prop) :
    Pr[h ← (Query k kN kS L → Out k e) : (∃ c : ChIdx P t,
        ((M.comp c.leaf.label).sampler c.idx).sample
          (ansAt (answersW prv x σ wrOf h) (posX (Mg := Mg) c)).stream = none) ∨
        B (M.chOfW (answersW prv x σ wrOf h))] ≤
      Pr[ch ← Chs P t : B ch] + M.overrun + SPBCS.keyCollision (t.size n) k := by
  classical
  set N := totalQ Mg n
  set q := strategy M prv x σ wrOf
  have hdom : ∀ j ws h, SPBCS.IsChainQuery (q j ws h) := fun j ws h =>
    isChainQuery_strategy prv x σ wrOf j ws h
  have hloc : ∀ j ws (h₁ h₂ : Query k kN kS L → Out k e),
      (∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) → q j ws h₁ = q j ws h₂ :=
    strategy_congr_oracle prv x σ wrOf hwr
  let φ : ChIdx P t ↪ Fin N := ⟨fun c => ⟨posX (Mg := Mg) c, pos_lt _⟩, fun c c' he =>
    posX_injective (congrArg Fin.val he)⟩
  let vec : (Query k kN kS L → Out k e) → Fin N → Out k e := fun h j =>
    (ansList q h N)[j.1]'(by simp)
  have hws : ∀ h (c : ChIdx P t), ansAt (answersW prv x σ wrOf h) (posX (Mg := Mg) c) =
      vec h (φ c) := fun h c => by
    simp only [vec, φ, ansAt, answersW]
    rw [List.getElem?_eq_getElem (by simp; exact pos_lt _)]
    rfl
  have hch : ∀ h, M.chOfW (answersW prv x σ wrOf h) = fun c =>
      (((M.comp c.leaf.label).sampler c.idx).sample (vec h (φ c)).stream).getD
        ((M.comp c.leaf.label).sampler c.idx).default := by
    intro h
    funext c
    rw [chOfW, hws h c]
  let G2 : (Fin N → Out k e) → Prop := fun a =>
    ∃ c : ChIdx P t, ((M.comp c.leaf.label).sampler c.idx).sample (a (φ c)).stream = none
  let G3 : (Fin N → Out k e) → Prop := fun a =>
    (∀ c : ChIdx P t, (((M.comp c.leaf.label).sampler c.idx).sample (a (φ c)).stream).isSome) ∧
      B fun c => (((M.comp c.leaf.label).sampler c.idx).sample (a (φ c)).stream).getD
        ((M.comp c.leaf.label).sampler c.idx).default
  have hcover : ∀ h, ((∃ c : ChIdx P t, ((M.comp c.leaf.label).sampler c.idx).sample
        (ansAt (answersW prv x σ wrOf h) (posX (Mg := Mg) c)).stream = none) ∨
        B (M.chOfW (answersW prv x σ wrOf h))) →
      ¬ (qryList q h N).Nodup ∨ ((qryList q h N).Nodup ∧ G2 (vec h)) ∨
        ((qryList q h N).Nodup ∧ G3 (vec h)) := by
    intro h hv
    by_cases hnd : (qryList q h N).Nodup
    · right
      by_cases hs : ∀ c : ChIdx P t,
          (((M.comp c.leaf.label).sampler c.idx).sample (vec h (φ c)).stream).isSome
      · right
        refine ⟨hnd, hs, ?_⟩
        rcases hv with ⟨c, hc⟩ | hB
        · rw [hws] at hc
          exact absurd (hs c) (by simp [hc])
        · rwa [hch] at hB
      · left
        push Not at hs
        obtain ⟨c, hc⟩ := hs
        exact ⟨hnd, c, by simpa using hc⟩
    · exact Or.inl hnd
  have hT3 : Pr[h ← (Query k kN kS L → Out k e) : (qryList q h N).Nodup ∧ G3 (vec h)] ≤
      Pr[ch ← Chs P t : B ch] := by
    refine (prob_nodup_ansList_le hdom hloc N G3).trans ?_
    have h1 : Pr[a ← (Fin N → Out k e) : G3 a] =
        Pr[g ← (ChIdx P t → Out k e) : (∀ c : ChIdx P t,
          (((M.comp c.leaf.label).sampler c.idx).sample (g c).stream).isSome) ∧ B fun c =>
            (((M.comp c.leaf.label).sampler c.idx).sample (g c).stream).getD
              ((M.comp c.leaf.label).sampler c.idx).default] :=
      probUniform_comp_embedding φ (fun g : ChIdx P t → Out k e => (∀ c : ChIdx P t,
        (((M.comp c.leaf.label).sampler c.idx).sample (g c).stream).isSome) ∧ B fun c =>
          (((M.comp c.leaf.label).sampler c.idx).sample (g c).stream).getD
            ((M.comp c.leaf.label).sampler c.idx).default)
    rw [h1]
    exact Sampler.prob_forall_sample_le (fun c : ChIdx P t => (M.comp c.leaf.label).sampler c.idx) B
  have hT2 : Pr[h ← (Query k kN kS L → Out k e) : (qryList q h N).Nodup ∧ G2 (vec h)] ≤
      M.overrun := by
    calc _ ≤ Pr[h ← (Query k kN kS L → Out k e) : ∃ c : ChIdx P t, (qryList q h N).Nodup ∧
          ((M.comp c.leaf.label).sampler c.idx).sample (vec h (φ c)).stream = none] :=
          QROM.probUniform_mono fun h ⟨hnd, c, hc⟩ => ⟨c, hnd, hc⟩
      _ ≤ ∑ c : ChIdx P t, Pr[h ← (Query k kN kS L → Out k e) : (qryList q h N).Nodup ∧
          ((M.comp c.leaf.label).sampler c.idx).sample (vec h (φ c)).stream = none] :=
          probUniform_exists_le _
      _ ≤ _ := Finset.sum_le_sum fun c _ => by
          refine (prob_nodup_ansList_le hdom hloc N
            (fun a => ((M.comp c.leaf.label).sampler c.idx).sample (a (φ c)).stream = none)).trans ?_
          let φ1 : Unit ↪ Fin N := ⟨fun _ => φ c, fun _ _ _ => rfl⟩
          have h1 : Pr[a ← (Fin N → Out k e) :
              ((M.comp c.leaf.label).sampler c.idx).sample (a (φ c)).stream = none] =
              Pr[g ← (Unit → Out k e) :
                ((M.comp c.leaf.label).sampler c.idx).sample (g ()).stream = none] :=
            probUniform_comp_embedding (Y := Out k e) φ1
              fun g => ((M.comp c.leaf.label).sampler c.idx).sample (g ()).stream = none
          rw [h1]
          calc Pr[g ← (Unit → Out k e) :
                ((M.comp c.leaf.label).sampler c.idx).sample (g ()).stream = none]
              = Pr[y ← Out k e : ((M.comp c.leaf.label).sampler c.idx).sample y.stream = none] :=
                (QROM.probUniform_equiv (Equiv.funUnique Unit (Out k e)).symm
                  (fun g => ((M.comp c.leaf.label).sampler c.idx).sample (g ()).stream = none)).symm
            _ = Pr[s ← (Fin (k + e) → Byte) : ((M.comp c.leaf.label).sampler c.idx).sample s = none] :=
                QROM.probUniform_equiv Out.streamEquiv
                  (fun s => ((M.comp c.leaf.label).sampler c.idx).sample s = none)
            _ ≤ _ := ((M.comp c.leaf.label).sampler c.idx).prob_none_le
  have hT1 := prob_not_nodup_le prv x σ wrOf hwr
  calc _ ≤ Pr[h ← (Query k kN kS L → Out k e) : ¬ (qryList q h N).Nodup ∨
        ((qryList q h N).Nodup ∧ G2 (vec h)) ∨ ((qryList q h N).Nodup ∧ G3 (vec h))] :=
        QROM.probUniform_mono hcover
    _ ≤ SPBCS.keyCollision (t.size n) k + (M.overrun + Pr[ch ← Chs P t : B ch]) :=
        (probUniform_or_le _ _).trans (add_le_add hT1 ((probUniform_or_le _ _).trans
          (add_le_add hT2 hT3)))
    _ = _ := by ring

end Bound

open Classical in
/-- **Completeness of the spBCS compiler for a fixed statement** (paper `thm:bcs-complete`
(1)): over a uniform oracle, the honest proof of the causal prover `prv`, with any Merkle salts `ν`
and Fiat–Shamir salt `σ`, is rejected with probability at most
`ε + overrun + keyCollision (t.size n) k`, where `ε` bounds the probability that the composite
verifier rejects the run of `prv` over uniform challenges. -/
theorem prob_not_accepts_prove_le {M : SPBCS Mg P X k kN kS L e}
    (E : (j : ι) → (M.comp j).Encoder) (ν : M.Pos → MerkleSalt kN) {V : X → FullTr P t → Bool}
    (Q : M.IOPQueries V x) {ε : ℝ≥0∞} (hε : Pr[ch ← Chs P t : V x (prv.run x ch) ≠ true] ≤ ε) :
    Pr[h ← (Query k kN kS L → Out k e) : ¬ M.Accepts h x (prove prv x σ E ν h Q) Q] ≤
      ε + M.overrun + SPBCS.keyCollision (t.size n) k := by
  refine le_trans (QROM.probUniform_mono fun h hv => ?_)
    ((prob_sample_none_or_chOfW_mem_le prv x σ (SPBCS.honestWrite E ν)
      (fun _ _ hq => SPBCS.honestWrite_congr_oracle E ν hq)
      fun ch => V x (prv.run x ch) ≠ true).trans (by gcongr))
  by_contra hc
  push Not at hc
  obtain ⟨hs, hV⟩ := hc
  exact hv (accepts_prove prv x σ E ν h Q (fun c => Option.isSome_iff_ne_none.2 (hs c)) hV)

end

end GordieHowe.SPBCS
