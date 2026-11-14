-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Stability

@[expose] public section

/-!
# The flip of the bad set by the class of the new entry

The flip into and out of `bad` (`GordieHowe/SPBCS/Stability.lean`) at one database `D` without a
digest collision and one fresh query, with the digests the new answer must hit counted by the
class of the query. A fresh answer changes the extraction only where its query is read:

* **A stream point `xof α σ`** is read only as the stream at the key `α`. Its digest must be the
  absorbed item of a chain at the position the unique recorded preimage of `α` fixes
  (`keyPos`), one slot per recorded input (`slotAbsorb`, `card_slotAbsorb_le`), or it completes a
  challenge (`nextBad`): `flip_into_bad_xof`. The chain holding the item is carried by a recorded
  chain input or by the final input of a hidden branch (`mem_slotAbsorb_of_hit`).
* **A chain input** is read only as a key. Its digest must be the key of a recorded stream point
  or the final digest a recorded input holds at the site the input fixes (`sitePos`), one target
  per recorded entry (`transcriptTargets`): `flip_into_bad_transcript`. None of the input's own
  digests is a target.
* **A `node` or a `leaf`** is read only by the Merkle views. Its digest must be a root carried by
  a recorded chain input, at most one per tree of the composite (`TreeSig`, `contentRoots`), or a
  child of a recorded node (`merkleTargets`): `flip_into_bad_merkle`. Only such an entry flips out
  of `bad` (`flip_out_of_bad_merkle`).

The dispatch over the classes gives `β + max 2 T · tq / 2^(8k)` for a bound `β` of `nextBad`
(`flip_bad_le_slot`, `slotCollisionBound`), `max 2 T · tq / 2^(8k)` out of `bad`
(`flip_compl_bad_le_slot`), the conditional flips `condFlip_bad_le_slot`,
`condFlip_compl_bad_le_slot`, and the conditional instability `condInstab_bad_le_slot`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X Wit : Type}

/-! ### The target sets -/

section Targets

variable (M : SPBCS Mg P X k kN kS L e)

/-- The absorbed digest at index `r` of leaf `q`'s chain in a content (at most two places:
the view's chain of `q`, and the own items when `q` is the observer). -/
def contentSlot (c : M.MContent) (q : t.Leaf) (r : ℕ) : Finset (Digest k) :=
  match c with
  | .round _ p chs _ own => ((chs q)[r]?.bind Item.getAbsorb).toFinset ∪
      (if p = q then ((own[r]?).bind Item.getAbsorb).toFinset else ∅)
  | .final _ _ chs _ => ((chs q)[r]?.bind Item.getAbsorb).toFinset

/-- The absorbed digest at index `r` of leaf `q`'s chain in a recorded input. -/
def inputSlot : Query k kN kS L → t.Leaf → ℕ → Finset (Digest k)
  | .transcript b, q, r => ((M.senc.decode b).map fun c => M.contentSlot c q r).getD ∅
  | _, _, _ => ∅

/-- The position a chain input fixes: its leaf and the number of its own items. -/
def keyPos : Query k kN kS L → Option (t.Leaf × ℕ)
  | .transcript b => (M.senc.decode b).bind fun c => match c with
    | .round _ q _ _ own => some (q, own.length)
    | .final _ _ _ _ => none
  | _ => none

/-- The slots of the recorded inputs at the position the input `x` fixes. -/
def keySlots (D : ODB k kN kS L e) (x : Query k kN kS L) : Finset (Digest k) :=
  match M.keyPos x with
  | some qr => D.keys.biUnion fun z => M.inputSlot z qr.1 qr.2
  | none => ∅

/-- **The digests a fresh stream answer at key `α` is compared with**: at the position fixed by
each recorded preimage of `α`, one slot per recorded input. -/
def slotAbsorb (D : ODB k kN kS L e) (α : Digest k) : Finset (Digest k) :=
  (preimages D α).biUnion (M.keySlots D)

/-- An `Option` has at most one element. -/
theorem card_toFinset_le_one {α : Type*} (o : Option α) : o.toFinset.card ≤ 1 := by
  cases o <;> simp

/-- **A well-formed content has at most one slot at a position**: the observer's own chain
is empty. -/
theorem card_contentSlot_le {c : M.MContent} (hwf : c.WF n fun j => chainWF (P j))
    (q : t.Leaf) (r : ℕ) : (M.contentSlot c q r).card ≤ 1 := by
  cases hwf with
  | @round ss p chs ds own hv _ _ =>
    simp only [contentSlot]
    by_cases hpq : p = q
    · subst hpq
      rw [hv.chains_nil p fun hv' => Leaf.not_before_self p hv'.1]
      simp only [List.getElem?_nil, Option.bind_none, Option.toFinset_none, Finset.empty_union,
        if_pos rfl]
      exact card_toFinset_le_one _
    · rw [if_neg hpq, Finset.union_empty]
      exact card_toFinset_le_one _
  | final _ => exact card_toFinset_le_one _

/-- A recorded input has at most one slot at a position. -/
theorem card_inputSlot_le (z : Query k kN kS L) (q : t.Leaf) (r : ℕ) :
    (M.inputSlot z q r).card ≤ 1 := by
  cases z with
  | transcript b =>
    cases hd : M.senc.decode b with
    | none => simp [inputSlot, hd]
    | some c =>
      simp only [inputSlot, hd, Option.map_some, Option.getD_some]
      exact M.card_contentSlot_le (M.senc.wf_of_decode b c hd) q r
  | _ => simp [inputSlot]

/-- The slots at the position an input fixes are at most one per recorded entry. -/
theorem card_keySlots_le (D : ODB k kN kS L e) (x : Query k kN kS L) :
    (M.keySlots D x).card ≤ D.size := by
  unfold keySlots
  split
  · refine Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ 1
      fun z _ => M.card_inputSlot_le z _ _).trans ?_)
    simp [DB.size]
  · simp

/-- **A fresh stream answer is compared with at most `|D|` digests** in a collision-free
database. -/
theorem card_slotAbsorb_le {D : ODB k kN kS L e} (hcol : D ∉ digestCollision) (α : Digest k) :
    (M.slotAbsorb D α).card ≤ D.size := by
  refine Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ D.size
    fun x _ => M.card_keySlots_le D x).trans ?_)
  rw [smul_eq_mul]
  exact (Nat.mul_le_mul_right _ (card_preimages_le_one hcol α)).trans_eq (one_mul _)

/-- The final digest at site `s` held by a recorded input. -/
def dsAt : Query k kN kS L → Mg.Site → Finset (Digest k)
  | .transcript b, s => ((M.senc.decode b).map fun c => ({c.ds s} : Finset (Digest k))).getD ∅
  | _, _ => ∅

/-- The site an input fixes: the site of its final content. -/
def sitePos : Query k kN kS L → Option Mg.Site
  | .transcript b => (M.senc.decode b).bind fun c => match c with
    | .final _ s _ _ => some s
    | .round _ _ _ _ _ => none
  | _ => none

/-- The target a recorded entry `z` offers a fresh chain input `x`: its key if `z` is a stream
point, its final digest at the site `x` fixes otherwise. -/
def tTarget (x z : Query k kN kS L) : Finset (Digest k) :=
  match z with
  | .xof κ _ => {κ}
  | _ => match M.sitePos x with
    | some s => M.dsAt z s
    | none => ∅

/-- **The digests a fresh chain input `x` must avoid**: one per recorded entry. -/
def transcriptTargets (D : ODB k kN kS L e) (x : Query k kN kS L) : Finset (Digest k) :=
  D.keys.biUnion (M.tTarget x)

/-- A recorded input holds at most one final digest at a site. -/
theorem card_dsAt_le (z : Query k kN kS L) (s : Mg.Site) : (M.dsAt z s).card ≤ 1 := by
  cases z with
  | transcript b => cases hd : M.senc.decode b <;> simp [dsAt, hd]
  | _ => simp [dsAt]

/-- A recorded entry offers a fresh chain input at most one target. -/
theorem card_tTarget_le (x z : Query k kN kS L) : (M.tTarget x z).card ≤ 1 := by
  unfold tTarget
  split
  · simp
  · split
    · exact M.card_dsAt_le _ _
    · simp

/-- **A fresh chain input has at most `|D|` targets.** -/
theorem card_transcriptTargets_le (D : ODB k kN kS L e) (x : Query k kN kS L) :
    (M.transcriptTargets D x).card ≤ D.size :=
  Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ 1
    fun z _ => M.card_tTarget_le x z).trans (by simp [DB.size]))

/-- The chains of a content with the own items at the observer. -/
def fullChains : M.MContent → M.Chains
  | .round _ p chs _ own => Function.update chs p own
  | .final _ _ chs _ => chs

/-- The root of tree `x` read at its round of a chain. -/
def rootOfChain {p : t.Leaf} (l : M.Items p) (x : TreeIdx (P p.label) (M.comp p.label).nTrees) :
    Option (Digest k) :=
  (l[x.msg.1.1]?.bind ((M.comp p.label).writeAt x.msg)).map fun w =>
    (M.comp p.label).rootOf x.msg w x.tree

/-- The trees of the composite as a dependent pair. -/
abbrev TreeSig : Type := Σ p : t.Leaf, TreeIdx (P p.label) (M.comp p.label).nTrees

/-- The roots a content carries: one per tree of the composite. -/
def contentRoots (c : M.MContent) : Finset (Digest k) :=
  (Finset.univ : Finset M.TreeSig).biUnion fun x =>
    (M.rootOfChain (M.fullChains c x.1) x.2).toFinset

/-- The Merkle targets a recorded entry offers: the roots of a chain input, the children of a
node. -/
def merkleAt : Query k kN kS L → Finset (Digest k)
  | .transcript b => ((M.senc.decode b).map M.contentRoots).getD ∅
  | .node l r => {l, r}
  | _ => ∅

/-- **The digests a fresh Merkle answer must avoid.** -/
def merkleTargets (D : ODB k kN kS L e) : Finset (Digest k) := D.keys.biUnion M.merkleAt

/-- **A content carries at most one root per tree of the composite.** -/
theorem card_contentRoots_le (c : M.MContent) :
    (M.contentRoots c).card ≤ Fintype.card M.TreeSig :=
  Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ 1
    fun x _ => card_toFinset_le_one _).trans (by simp))

/-- A recorded entry offers at most `max 2 T` Merkle targets. -/
theorem card_merkleAt_le (z : Query k kN kS L) :
    (M.merkleAt z).card ≤ max 2 (Fintype.card M.TreeSig) := by
  cases z with
  | transcript b =>
    cases hd : M.senc.decode b with
    | none => simp [merkleAt, hd]
    | some c =>
      simp only [merkleAt, hd, Option.map_some, Option.getD_some]
      exact (M.card_contentRoots_le c).trans (le_max_right _ _)
  | node l r => exact (Finset.card_le_two).trans (le_max_left _ _)
  | _ => simp [merkleAt]

/-- **A fresh Merkle answer has at most `max 2 T · |D|` targets.** -/
theorem card_merkleTargets_le (D : ODB k kN kS L e) :
    (M.merkleTargets D).card ≤ max 2 (Fintype.card M.TreeSig) * D.size :=
  Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ _
    fun z _ => M.card_merkleAt_le z).trans (by simp [DB.size, mul_comm]))

/-- The dependent pairs `TreeSig` count the trees of the composite. -/
theorem card_treeSig_eq [Fintype M.Tree] : Fintype.card M.TreeSig = Fintype.card M.Tree :=
  (Fintype.card_congr (Tree.equivSigma M)).symm

/-- The children of the recorded nodes are Merkle targets. -/
theorem nodeKids_subset (D : ODB k kN kS L e) : nodeKids D ⊆ M.merkleTargets D := by
  intro u hu
  obtain ⟨z, hz, hu⟩ := Finset.mem_biUnion.1 hu
  refine Finset.mem_biUnion.2 ⟨z, hz, ?_⟩
  cases z with
  | node l r => simpa [merkleAt] using hu
  | _ => simp at hu

/-- **The collision bound of one fresh entry by its class** at a database of fewer than `tq`
entries: `max 2 T · tq / 2^(8k)`, with `T` the number of trees of the composite. -/
noncomputable abbrev slotCollisionBound (tq : ℕ) : ℝ≥0∞ :=
  ((max 2 (Fintype.card M.TreeSig) * tq : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)

end Targets

/-! ### A fresh stream point -/

section Stream

variable (M : SPBCS Mg P X k kN kS L e) {D : ODB k kN kS L e} (ss : SaltedStatement kS X)
  (chs : M.Chains) {α : Digest k} {σ : FiatShamirSalt kS} {y : Out k e}

/-- Leaf `q`'s chain `l` holds `d` absorbed at some index `j` whose prefix's chain input is
recorded in `D` with an answer of digest `α`. -/
def AbsorbHit (D : ODB k kN kS L e) (α : Digest k) (q : t.Leaf) (l : M.Items q) (d : Digest k) :
    Prop :=
  ∃ j, (l[j]?.bind Item.getAbsorb) = some d ∧
    ∃ a, M.keyD D ss chs q (l.take j) = some a ∧ a.digest = α

/-- A key read after recording a fresh stream point was read before. -/
theorem keyD_of_extend_xof (hq : Query.xof α σ ∉ D) {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) {a : Out k e}
    (h' : M.keyD (D.extend (.xof α σ) y) ss chs p l = some a) : M.keyD D ss chs p l = some a := by
  by_contra h
  rcases M.keyD_extend ss chs hq hwf hl hlen h' h with ⟨h1, -⟩ | h1
  · simp [inputD] at h1
  · simp [pend] at h1

/-- If a fresh stream answer makes a challenge readable, its digest is the absorbed item and the
challenge's key is recorded in `D` with digest `α`. -/
theorem extChal_xof (hq : Query.xof α σ ∉ D) {q : t.Leaf}
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l₀ : M.Items q} (hl : chainWF (P q.label) l₀) (hlen : l₀.length < n q.label) {d : Digest k}
    {i : (P q.label).ChallengeIdx} {v : (P q.label).Challenge i}
    (h' : M.extChal (D.extend (.xof α σ) y) ss chs q l₀ d i = some v)
    (h : M.extChal D ss chs q l₀ d i ≠ some v) :
    y.digest = d ∧ ∃ a, M.keyD D ss chs q l₀ = some a ∧ a.digest = α := by
  simp only [extChal, Option.bind_eq_some_iff] at h'
  obtain ⟨a', ha', s', hs', hv⟩ := h'
  split_ifs at hv with hsd
  have ha := M.keyD_of_extend_xof ss chs hq hwf hl hlen ha'
  cases hs : D.lookup (.xof a'.digest ss.salt) with
  | none =>
    obtain ⟨h1, rfl⟩ := eq_of_lookup_extend hs hs'
    exact ⟨hsd, a', ha, (Query.xof.inj h1).1⟩
  | some s =>
    obtain rfl : s' = s :=
      Option.some_inj.1 ((lookup_extend_of_lookup hq hs).symm.trans hs').symm
    exact absurd (by simp [extChal, ha, hs, hsd, hv]) h

/-- If a fresh stream answer changes round `r` read from a chain, the chain absorbs its digest at
`r` and the key of the chain's first `r` items is recorded in `D` with digest `α`. -/
theorem extStep_xof (hq : Query.xof α σ ∉ D)
    (hcol : D.extend (.xof α σ) y ∉ digestCollision) {q : t.Leaf}
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items q} {r : ℕ} {hr : r < n q.label} (hpre : chainWF (P q.label) (l.take r))
    {v : (P q.label).Type ⟨r, hr⟩}
    (h' : M.extStep (D.extend (.xof α σ) y) ss chs q l r hr = some v)
    (h : M.extStep D ss chs q l r hr ≠ some v) :
    (l[r]?.bind Item.getAbsorb) = some y.digest ∧
      ∃ a, M.keyD D ss chs q (l.take r) = some a ∧ a.digest = α := by
  unfold extStep at h h'
  split_ifs at h h' with hd
  · exfalso
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h'
    rw [hw, Option.map_some] at h
    have hv : (M.comp q.label).views (D.extend (.xof α σ) y) ⟨⟨r, hr⟩, hd⟩ w =
        (M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w :=
      funext fun τ => view_extend_of_not_merkle hq hcol rfl rfl
    exact h (by rw [hv])
  · obtain ⟨d, hdl, hc⟩ := Option.bind_eq_some_iff.1 h'
    rw [hdl] at h
    have h2 : M.extChal D ss chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd) ≠ some v := h
    obtain ⟨hy, ha⟩ := M.extChal_xof ss chs hq hwf hpre
      ((List.length_take_le r l).trans_lt hr) hc h2
    rw [hy]
    exact ⟨hdl, ha⟩

/-- If a fresh stream answer changes a transcript read from a chain, the chain holds its
digest as an `AbsorbHit`. -/
theorem extLeaf_xof (hq : Query.xof α σ ∉ D)
    (hcol : D.extend (.xof α σ) y ∉ digestCollision) (q : t.Leaf)
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf (D.extend (.xof α σ) y) ss chs q l r hr = some tr →
      M.extLeaf D ss chs q l r hr ≠ some tr → M.AbsorbHit ss chs D α q l y.digest
  | 0, _, _, h', h => absurd h' (by rw [extLeaf] at h ⊢; exact h)
  | r + 1, hr, tr, h', h => by
    rw [extLeaf_succ] at h' h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    by_cases hD : M.extLeaf D ss chs q l r (by omega) = some tr₀
    · rw [hD, Option.bind_some] at h
      obtain ⟨hj, ha⟩ := M.extStep_xof ss chs hq hcol hwf
        (M.chainWF_take_of_extLeaf (D.extend (.xof α σ) y) ss chs h₀) hsv
        fun hs => h (by rw [hs, Option.map_some])
      exact ⟨r, hj, ha⟩
    · exact extLeaf_xof hq hcol q hwf l r (by omega) h₀ hD

/-- If a fresh stream answer changes an extracted causal past, its own items or the chain of a
leaf before it hold the answer's digest as an `AbsorbHit`. -/
theorem extPast_xof (hq : Query.xof α σ ∉ D)
    (hcol : D.extend (.xof α σ) y ∉ digestCollision) (c : ChIdx P t)
    (hfull : M.ChainsFull chs c.leaf) (l : M.Items c.leaf) {past : CausalPast P c}
    (h' : M.extPast (D.extend (.xof α σ) y) ss chs c l = some past)
    (h : M.extPast D ss chs c l ≠ some past) :
    M.AbsorbHit ss chs D α c.leaf l y.digest ∨
      ∃ r : t.Leaf, r.Before c.leaf ∧ M.AbsorbHit ss chs D α r (chs r) y.digest := by
  obtain ⟨ctx', hctx', hown'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨own', hown'', rfl⟩ := Option.map_eq_some_iff.1 hown'
  have hwf : ∀ r, r.Before c.leaf → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label :=
    fun r hr => ⟨M.chainWF_of_extLeaf (D.extend (.xof α σ) y) ss chs
      ((optAll_eq_some.1 hctx') ⟨r, hr⟩) (hfull r hr), hfull r hr⟩
  by_cases hctx : M.extCtx D ss chs c.leaf = some ctx'
  · rw [extPast, hctx, Option.bind_some] at h
    have hne : M.extLeaf D ss chs c.leaf l c.idx.1 c.idx.1.2.le ≠ some own' := fun he =>
      h (by rw [he]; rfl)
    exact Or.inl (M.extLeaf_xof ss chs hq hcol c.leaf hwf l _ _ hown'' hne)
  · obtain ⟨r, hr⟩ : ∃ r : {q : t.Leaf // q.Before c.leaf},
        M.extLeaf D ss chs r.1 (chs r.1) (n r.1.label) le_rfl ≠ some (ctx' r) := by
      by_contra hne
      push Not at hne
      exact hctx (optAll_eq_some.2 hne)
    have h1 := optAll_eq_some.1 hctx' r
    exact Or.inr ⟨r.1, r.2, M.extLeaf_xof ss chs hq hcol r.1
      (fun r' hr' => hwf r' (hr'.trans r.2)) (chs r.1) _ _ h1 hr⟩

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] in
/-- A prefix of a well-formed chain is well formed. -/
theorem chainWF_take {m : ℕ} {Q : ProtocolSpec m} {Wr : Q.MessageIdx → Type}
    {l : List (Item k (Σ i : Q.MessageIdx, Wr i))} (h : chainWF Q l) (j : ℕ) :
    chainWF Q (l.take j) := fun r hr => by
  have hr' : r < l.length := lt_of_lt_of_le hr (List.length_take_le' j l)
  simpa [List.getElem_take] using h r hr'

/-- The position of a recorded chain input whose own items are a prefix of length `j`. -/
theorem keyPos_inputD {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) :
    M.keyPos (M.inputD D ss chs p l) = some (p, l.length) := by
  have hwfc := wf_roundContent_of_before ss (M.finalsD D ss chs) hwf hl hlen
  simp only [keyPos, inputD, M.senc.decode_encode _ hwfc, Option.bind_some]
  simp only [roundContent]

/-- **The hit's prefix input is a recorded preimage of `α` whose position is the hit's.** -/
theorem keySlots_mem_of_hit {q : t.Leaf}
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items q} (hl : chainWF (P q.label) l) (hlen : l.length ≤ n q.label) {d : Digest k}
    (hhit : M.AbsorbHit ss chs D α q l d) :
    ∃ x ∈ preimages D α, ∃ j, (l[j]?.bind Item.getAbsorb) = some d ∧
      M.keyPos x = some (q, j) := by
  obtain ⟨j, hj, a, ha, hα⟩ := hhit
  have hjl : j < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    simp at hj
  unfold keyD at ha
  split_ifs at ha with hrec
  refine ⟨_, mem_preimages.2 ⟨DB.mem_iff_lookup.2 ⟨a, ha⟩, by simp [ha, hα]⟩, j, hj, ?_⟩
  have hlt : (l.take j).length < n q.label := by
    rw [List.length_take]
    omega
  rw [M.keyPos_inputD ss chs hwf (chainWF_take hl j) hlt, List.length_take, Nat.min_eq_left hjl.le]

/-- **The carrier step**: a hit in the chains read at a recorded chain input of leaf `p` lies in
the slot, at the hit's position, of that input or of the final input of the hidden branch
holding the hit's leaf. -/
theorem mem_slotAbsorb_of_hit {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) {a : Out k e}
    (ha : M.keyD D ss chs p l = some a) {d : Digest k}
    (hhit : M.AbsorbHit ss chs D α p l d ∨
      ∃ r : t.Leaf, r.Before p ∧ M.AbsorbHit ss chs D α r (chs r) d) :
    d ∈ M.slotAbsorb D α := by
  unfold keyD at ha
  split_ifs at ha with hrec
  have hin : M.inputD D ss chs p l ∈ D := DB.mem_iff_lookup.2 ⟨a, ha⟩
  have hwfc := wf_roundContent_of_before ss (M.finalsD D ss chs) hwf hl hlen
  -- the slot of a carrier `z ∈ D` at the position of a preimage gives membership
  have hmem : ∀ {q : t.Leaf} {x : Query k kN kS L} {j : ℕ} (z : Query k kN kS L),
      x ∈ preimages D α → M.keyPos x = some (q, j) → z ∈ D → d ∈ M.inputSlot z q j →
      d ∈ M.slotAbsorb D α := fun z hx hpos hz hd =>
    Finset.mem_biUnion.2 ⟨_, hx, by
      simp only [keySlots, hpos]
      exact Finset.mem_biUnion.2 ⟨z, Finmap.mem_keys.2 hz, hd⟩⟩
  rcases hhit with hhit | ⟨r, hr, hhit⟩
  · obtain ⟨x, hx, j, hj, hpos⟩ := M.keySlots_mem_of_hit ss chs hwf hl hlen.le hhit
    refine hmem _ hx hpos hin ?_
    simp only [inputSlot, inputD, M.senc.decode_encode _ hwfc, Option.map_some, Option.getD_some]
    simp only [roundContent, contentSlot]
    simp [hj]
  · have hwfr : ∀ r', r'.Before r → chainWF (P r'.label) (chs r') ∧
        (chs r').length = n r'.label := fun r' hr' => hwf r' (hr'.trans hr)
    obtain ⟨x, hx, j, hj, hpos⟩ :=
      M.keySlots_mem_of_hit ss chs hwfr (hwf r hr).1 (hwf r hr).2.le hhit
    by_cases hv : (Merges.Obs.leaf p : Mg.Obs).Visible r
    · refine hmem _ hx hpos hin ?_
      simp only [inputSlot, inputD, M.senc.decode_encode _ hwfc, Option.map_some,
        Option.getD_some]
      simp only [roundContent, contentSlot, Merges.Obs.viewChains_of_visible _ _ hv]
      simp [hj]
    · obtain ⟨s, hs, hm⟩ := Merges.Obs.exists_hides_of_sees (o := .leaf p) hr hv
      have hwff := wf_finalContent_of_sees ss (M.finalsD D ss chs) (s := s) fun r' hr' =>
        hwf r' (Merges.sees_of_sees_sink hs hr')
      refine hmem _ hx hpos (hrec s hs) ?_
      simp only [inputSlot, finalInputD, M.senc.decode_encode _ hwff, Option.map_some,
        Option.getD_some]
      simp only [finalContent, contentSlot,
        Merges.Obs.viewChains_of_visible _ _ (Merges.visible_sink_of_mem hm)]
      simp [hj]

end Stream

/-! ### A fresh chain input -/

section Transcript

variable (M : SPBCS Mg P X k kN kS L e) {D : ODB k kN kS L e} (ss : SaltedStatement kS X)
  (chs : M.Chains) {q₀ : Query k kN kS L} {y : Out k e}

/-- A key read after recording a new input that is not a chain input was read before. -/
theorem keyD_of_extend_not_transcript (hq : q₀ ∉ D) (hqt : ∀ b, q₀ ≠ .transcript b) {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) {a : Out k e}
    (h' : M.keyD (D.extend q₀ y) ss chs p l = some a) : M.keyD D ss chs p l = some a := by
  by_contra h
  rcases M.keyD_extend ss chs hq hwf hl hlen h' h with ⟨h1, -⟩ | h1
  · exact hqt _ h1
  · cases q₀ with
    | transcript b => exact absurd rfl (hqt b)
    | _ => simp [pend] at h1

end Transcript

section TranscriptChain

variable (M : SPBCS Mg P X k kN kS L e) {D : ODB k kN kS L e} (ss : SaltedStatement kS X)
  (chs : M.Chains) {b : Bytes L} {y : Out k e}

/-- **A key read only after recording a fresh chain input**: the input is the chain input
itself, or a recorded input holds the answer's digest as its final digest at the site the input
fixes. -/
theorem keyD_extend_transcript (hq : Query.transcript b ∉ D) {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) {a : Out k e}
    (h' : M.keyD (D.extend (.transcript b) y) ss chs p l = some a)
    (h : M.keyD D ss chs p l ≠ some a) :
    (Query.transcript b = M.inputD (D.extend (.transcript b) y) ss chs p l ∧ a = y) ∨
      ∃ z ∈ D, ∃ s, M.sitePos (.transcript b) = some s ∧ y.digest ∈ M.dsAt z s := by
  unfold keyD at h' h
  split_ifs at h' with hrec'
  by_cases hrec : M.FinalsRecorded D ss chs (.leaf p)
  · rw [ite_eq_left hrec] at h
    have he := M.inputD_extend (y := y) ss chs hq hrec l
    rw [he] at h'
    rcases (lookup_extend_eq_some_iff hq).1 h' with h1 | ⟨h1, h2⟩
    · exact absurd h1 h
    · exact Or.inl ⟨by rw [he]; exact h1.symm, h2⟩
  · have hne : (Finset.univ.filter fun s =>
        Mg.Hides s (.leaf p) ∧ M.finalInputD D ss chs s ∉ D).Nonempty := by
      by_contra hc
      refine hrec fun s hs => ?_
      by_contra hm
      exact hc ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, hm⟩⟩
    obtain ⟨s, hsf, hmin⟩ :=
      Finset.exists_min_image _ (fun s => (Merges.hiders (M := Mg) (.sink s)).card) hne
    obtain ⟨-, hs, hnot⟩ := Finset.mem_filter.1 hsf
    have hrecs : M.FinalsRecorded D ss chs (.sink s) := fun s' hs' => by
      by_contra hm
      have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
      exact absurd (hmin s' (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        Merges.hides_of_hides_sink hs hs', hm⟩)) (not_le.2 hlt)
    have hfin : M.finalInputD (D.extend (.transcript b) y) ss chs s = M.finalInputD D ss chs s := by
      unfold finalInputD
      rw [finalContent_congr (fun _ _ => rfl) fun s' hs' => M.finalsD_extend ss chs hq hrecs s' hs']
    have hq₀ : Query.transcript b = M.finalInputD D ss chs s := by
      have := hrec' s hs
      rw [hfin] at this
      rcases DB.mem_extend.1 this with h1 | h1
      · exact h1.symm
      · exact absurd h1 hnot
    have hds : M.finalsD (D.extend (.transcript b) y) ss chs s = y.digest := by
      refine M.finalsD_eq_of_lookup (D.extend (.transcript b) y) ss chs ?_
      rw [hfin, ← hq₀, DB.lookup_extend_self]
    by_cases hqr : Query.transcript b = M.inputD (D.extend (.transcript b) y) ss chs p l
    · refine Or.inl ⟨hqr, ?_⟩
      rw [← hqr, DB.lookup_extend_self] at h'
      exact (Option.some_inj.1 h').symm
    · right
      have hrD : M.inputD (D.extend (.transcript b) y) ss chs p l ∈ D := by
        rcases DB.mem_extend.1 (DB.mem_iff_lookup.2 ⟨a, h'⟩) with h1 | h1
        · exact absurd h1.symm hqr
        · exact h1
      have hwfc := wf_roundContent_of_before ss (M.finalsD (D.extend (.transcript b) y) ss chs)
        hwf hl hlen
      have hwff := wf_finalContent_of_sees ss (M.finalsD D ss chs) (s := s) fun r hr =>
        hwf r (Merges.sees_of_sees_sink hs hr)
      refine ⟨_, hrD, s, ?_, ?_⟩
      · rw [hq₀]
        simp only [sitePos, finalInputD, M.senc.decode_encode _ hwff, Option.bind_some]
        simp only [finalContent]
      · simp only [dsAt, inputD, M.senc.decode_encode _ hwfc, Option.map_some, Option.getD_some]
        simp only [roundContent, Content.ds, Merges.Obs.viewDs_of_hides _ _ hs, hds,
          Finset.mem_singleton]

/-- **A key read only after a fresh chain input, with its stream recorded**: the answer's digest
is a target. -/
theorem target_of_keyD_change (hq : Query.transcript b ∉ D) {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) {a s' : Out k e}
    {σ' : FiatShamirSalt kS}
    (h' : M.keyD (D.extend (.transcript b) y) ss chs p l = some a)
    (h : M.keyD D ss chs p l ≠ some a)
    (hs : (D.extend (.transcript b) y).lookup (.xof a.digest σ') = some s') :
    y.digest ∈ M.transcriptTargets D (.transcript b) := by
  rcases M.keyD_extend_transcript ss chs hq hwf hl hlen h' h with ⟨-, hay⟩ | ⟨z, hz, s, hs1, hz2⟩
  · have hne : (Query.xof a.digest σ' : Query k kN kS L) ≠ .transcript b := by simp
    rw [DB.lookup_extend_of_ne hne] at hs
    exact Finset.mem_biUnion.2 ⟨_, Finmap.mem_keys.2 (DB.mem_iff_lookup.2 ⟨_, hs⟩),
      by simp [tTarget, hay]⟩
  · refine Finset.mem_biUnion.2 ⟨z, Finmap.mem_keys.2 hz, ?_⟩
    cases z with
    | transcript b' => simpa only [tTarget, hs1] using hz2
    | _ => simp [dsAt] at hz2

/-- A fresh chain input changes a challenge read from `D` only when its answer's digest is a
target. -/
theorem extChal_transcript (hq : Query.transcript b ∉ D) {q : t.Leaf}
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l₀ : M.Items q} (hl : chainWF (P q.label) l₀) (hlen : l₀.length < n q.label) {d : Digest k}
    {i : (P q.label).ChallengeIdx} {v : (P q.label).Challenge i}
    (h' : M.extChal (D.extend (.transcript b) y) ss chs q l₀ d i = some v)
    (h : M.extChal D ss chs q l₀ d i ≠ some v) :
    y.digest ∈ M.transcriptTargets D (.transcript b) := by
  simp only [extChal, Option.bind_eq_some_iff] at h'
  obtain ⟨a', ha', s', hs', hv⟩ := h'
  by_cases ha : M.keyD D ss chs q l₀ = some a'
  · exfalso
    have hne : (Query.xof a'.digest ss.salt : Query k kN kS L) ≠ .transcript b := by simp
    rw [DB.lookup_extend_of_ne hne] at hs'
    exact h (by simp only [extChal, Option.bind_eq_some_iff]; exact ⟨a', ha, s', hs', hv⟩)
  · exact M.target_of_keyD_change ss chs hq hwf hl hlen ha' ha hs'

/-- A fresh chain input changes a round read from a chain only when its answer's digest is a
target. -/
theorem extStep_transcript (hq : Query.transcript b ∉ D)
    (hcol : D.extend (.transcript b) y ∉ digestCollision) {q : t.Leaf}
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items q} {r : ℕ} {hr : r < n q.label} (hpre : chainWF (P q.label) (l.take r))
    {v : (P q.label).Type ⟨r, hr⟩}
    (h' : M.extStep (D.extend (.transcript b) y) ss chs q l r hr = some v)
    (h : M.extStep D ss chs q l r hr ≠ some v) :
    y.digest ∈ M.transcriptTargets D (.transcript b) := by
  unfold extStep at h h'
  split_ifs at h h' with hd
  · exfalso
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h'
    rw [hw, Option.map_some] at h
    have hv : (M.comp q.label).views (D.extend (.transcript b) y) ⟨⟨r, hr⟩, hd⟩ w =
        (M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w :=
      funext fun τ => view_extend_of_not_merkle hq hcol rfl rfl
    exact h (by rw [hv])
  · obtain ⟨d, hdl, hc⟩ := Option.bind_eq_some_iff.1 h'
    rw [hdl] at h
    have h2 : M.extChal D ss chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd) ≠ some v := h
    exact M.extChal_transcript ss chs hq hwf hpre ((List.length_take_le r l).trans_lt hr) hc h2

/-- A fresh chain input changes a transcript read from a chain only when its answer's digest is
a target. -/
theorem extLeaf_transcript (hq : Query.transcript b ∉ D)
    (hcol : D.extend (.transcript b) y ∉ digestCollision) (q : t.Leaf)
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr},
      M.extLeaf (D.extend (.transcript b) y) ss chs q l r hr = some tr →
      M.extLeaf D ss chs q l r hr ≠ some tr → y.digest ∈ M.transcriptTargets D (.transcript b)
  | 0, _, _, h', h => absurd h' (by rw [extLeaf] at h ⊢; exact h)
  | r + 1, hr, tr, h', h => by
    rw [extLeaf_succ] at h' h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    by_cases hD : M.extLeaf D ss chs q l r (by omega) = some tr₀
    · rw [hD, Option.bind_some] at h
      exact M.extStep_transcript ss chs hq hcol hwf
        (M.chainWF_take_of_extLeaf (D.extend (.transcript b) y) ss chs h₀) hsv
        fun hs => h (by rw [hs, Option.map_some])
    · exact extLeaf_transcript hq hcol q hwf l r (by omega) h₀ hD

/-- A fresh chain input changes an extracted causal past only when its answer's digest is a
target. -/
theorem extPast_transcript (hq : Query.transcript b ∉ D)
    (hcol : D.extend (.transcript b) y ∉ digestCollision) (c : ChIdx P t)
    (hfull : M.ChainsFull chs c.leaf) (l : M.Items c.leaf) {past : CausalPast P c}
    (h' : M.extPast (D.extend (.transcript b) y) ss chs c l = some past)
    (h : M.extPast D ss chs c l ≠ some past) :
    y.digest ∈ M.transcriptTargets D (.transcript b) := by
  obtain ⟨ctx', hctx', hown'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨own', hown'', rfl⟩ := Option.map_eq_some_iff.1 hown'
  have hwf : ∀ r, r.Before c.leaf → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label :=
    fun r hr => ⟨M.chainWF_of_extLeaf (D.extend (.transcript b) y) ss chs
      ((optAll_eq_some.1 hctx') ⟨r, hr⟩) (hfull r hr), hfull r hr⟩
  by_cases hctx : M.extCtx D ss chs c.leaf = some ctx'
  · rw [extPast, hctx, Option.bind_some] at h
    have hne : M.extLeaf D ss chs c.leaf l c.idx.1 c.idx.1.2.le ≠ some own' := fun he =>
      h (by rw [he]; rfl)
    exact M.extLeaf_transcript ss chs hq hcol c.leaf hwf l _ _ hown'' hne
  · obtain ⟨r, hr⟩ : ∃ r : {q : t.Leaf // q.Before c.leaf},
        M.extLeaf D ss chs r.1 (chs r.1) (n r.1.label) le_rfl ≠ some (ctx' r) := by
      by_contra hne
      push Not at hne
      exact hctx (optAll_eq_some.2 hne)
    exact M.extLeaf_transcript ss chs hq hcol r.1 (fun r' hr' => hwf r' (hr'.trans r.2)) (chs r.1)
      _ _ (optAll_eq_some.1 hctx' r) hr

end TranscriptChain

/-! ### A fresh `node` or `leaf` -/

section MerkleChain

variable (M : SPBCS Mg P X k kN kS L e) {D : ODB k kN kS L e} (ss : SaltedStatement kS X)
  (chs : M.Chains) {q₀ : Query k kN kS L} {y : Out k e}

/-- Leaf `q`'s chain `l` carries `d` as a root of the write at a prover round. -/
def RootHit (q : t.Leaf) (l : M.Items q) (d : Digest k) : Prop :=
  ∃ (i : (P q.label).MessageIdx) (w : (M.comp q.label).MessageWrite i)
    (τ : Fin ((M.comp q.label).nTrees i)),
    (l[i.1.1]?.bind ((M.comp q.label).writeAt i)) = some w ∧ (M.comp q.label).rootOf i w τ = d

/-- A fresh Merkle entry changes a round read from a chain only at a root the chain carries or
a child of a recorded node. -/
theorem extStep_merkle (hq : q₀ ∉ D) (hqt : ∀ b, q₀ ≠ .transcript b)
    (hqx : ∀ κ σ, q₀ ≠ .xof κ σ) {q : t.Leaf}
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items q} {r : ℕ} {hr : r < n q.label} (hpre : chainWF (P q.label) (l.take r))
    {v : (P q.label).Type ⟨r, hr⟩}
    (h' : M.extStep (D.extend q₀ y) ss chs q l r hr = some v)
    (h : M.extStep D ss chs q l r hr ≠ some v) :
    M.RootHit q l y.digest ∨ y.digest ∈ nodeKids D := by
  unfold extStep at h h'
  split_ifs at h h' with hd
  · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h'
    rw [hw, Option.map_some] at h
    have hv : (M.comp q.label).views (D.extend q₀ y) ⟨⟨r, hr⟩, hd⟩ w ≠
        (M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w := fun he => h (by rw [he])
    rcases (M.comp q.label).root_or_nodeKids_of_views_ne hq hv with ⟨τ, hτ⟩ | hk
    · exact Or.inl ⟨⟨⟨r, hr⟩, hd⟩, w, τ, hw, hτ⟩
    · exact Or.inr hk
  · exfalso
    obtain ⟨d, hdl, hc⟩ := Option.bind_eq_some_iff.1 h'
    rw [hdl] at h
    have h2 : M.extChal D ss chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd) ≠ some v := h
    have hc' : M.extChal (D.extend q₀ y) ss chs q (l.take r) d
        ((P q.label).chIdx ⟨r, hr⟩ hd) = some v := hc
    unfold extChal at hc'
    obtain ⟨a', ha', hc2⟩ := Option.bind_eq_some_iff.1 hc'
    obtain ⟨s', hs', hv⟩ := Option.bind_eq_some_iff.1 hc2
    have ha := M.keyD_of_extend_not_transcript ss chs hq hqt hwf hpre
      ((List.length_take_le r l).trans_lt hr) ha'
    rw [DB.lookup_extend_of_ne fun he => hqx _ _ he.symm] at hs'
    exact h2 (by
      unfold extChal
      exact Option.bind_eq_some_iff.2 ⟨a', ha, Option.bind_eq_some_iff.2 ⟨s', hs', hv⟩⟩)

/-- A fresh Merkle entry changes a transcript read from a chain only at a root the chain
carries or a child of a recorded node. -/
theorem extLeaf_merkle (hq : q₀ ∉ D) (hqt : ∀ b, q₀ ≠ .transcript b)
    (hqx : ∀ κ σ, q₀ ≠ .xof κ σ) (q : t.Leaf)
    (hwf : ∀ r, r.Before q → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf (D.extend q₀ y) ss chs q l r hr = some tr →
      M.extLeaf D ss chs q l r hr ≠ some tr → M.RootHit q l y.digest ∨ y.digest ∈ nodeKids D
  | 0, _, _, h', h => absurd h' (by rw [extLeaf] at h ⊢; exact h)
  | r + 1, hr, tr, h', h => by
    rw [extLeaf_succ] at h' h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    by_cases hD : M.extLeaf D ss chs q l r (by omega) = some tr₀
    · rw [hD, Option.bind_some] at h
      exact M.extStep_merkle ss chs hq hqt hqx hwf
        (M.chainWF_take_of_extLeaf (D.extend q₀ y) ss chs h₀) hsv
        fun hs => h (by rw [hs, Option.map_some])
    · exact extLeaf_merkle hq hqt hqx q hwf l r (by omega) h₀ hD

/-- A fresh Merkle entry changes an extracted causal past only at a root carried by its own
items or the chain of a leaf before it, or at a child of a recorded node. -/
theorem extPast_merkle (hq : q₀ ∉ D) (hqt : ∀ b, q₀ ≠ .transcript b)
    (hqx : ∀ κ σ, q₀ ≠ .xof κ σ) (c : ChIdx P t)
    (hfull : M.ChainsFull chs c.leaf) (l : M.Items c.leaf) {past : CausalPast P c}
    (h' : M.extPast (D.extend q₀ y) ss chs c l = some past)
    (h : M.extPast D ss chs c l ≠ some past) :
    (M.RootHit c.leaf l y.digest ∨ ∃ r : t.Leaf, r.Before c.leaf ∧ M.RootHit r (chs r) y.digest) ∨
      y.digest ∈ nodeKids D := by
  obtain ⟨ctx', hctx', hown'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨own', hown'', rfl⟩ := Option.map_eq_some_iff.1 hown'
  have hwf : ∀ r, r.Before c.leaf → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label :=
    fun r hr => ⟨M.chainWF_of_extLeaf (D.extend q₀ y) ss chs
      ((optAll_eq_some.1 hctx') ⟨r, hr⟩) (hfull r hr), hfull r hr⟩
  by_cases hctx : M.extCtx D ss chs c.leaf = some ctx'
  · rw [extPast, hctx, Option.bind_some] at h
    have hne : M.extLeaf D ss chs c.leaf l c.idx.1 c.idx.1.2.le ≠ some own' := fun he =>
      h (by rw [he]; rfl)
    rcases M.extLeaf_merkle ss chs hq hqt hqx c.leaf hwf l _ _ hown'' hne with h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inr h1
  · obtain ⟨r, hr⟩ : ∃ r : {q : t.Leaf // q.Before c.leaf},
        M.extLeaf D ss chs r.1 (chs r.1) (n r.1.label) le_rfl ≠ some (ctx' r) := by
      by_contra hne
      push Not at hne
      exact hctx (optAll_eq_some.2 hne)
    rcases M.extLeaf_merkle ss chs hq hqt hqx r.1 (fun r' hr' => hwf r' (hr'.trans r.2))
      (chs r.1) _ _ (optAll_eq_some.1 hctx' r) hr with h1 | h1
    · exact Or.inl (Or.inr ⟨r.1, r.2, h1⟩)
    · exact Or.inr h1

/-- `extStep` in the converse direction: only a Merkle entry, at a root or a node child. -/
theorem extStep_ne_merkle (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision) {q : t.Leaf}
    {l : M.Items q} {r : ℕ} {hr : r < n q.label} {v : (P q.label).Type ⟨r, hr⟩}
    (h : M.extStep D ss chs q l r hr = some v)
    (h' : M.extStep (D.extend q₀ y) ss chs q l r hr ≠ some v) :
    (M.RootHit q l y.digest ∨ y.digest ∈ nodeKids D) ∧
      ¬ (q₀.children = none ∧ q₀.opening = none) := by
  unfold extStep at h h'
  split_ifs at h h' with hd
  · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [hw, Option.map_some] at h'
    have hv : (M.comp q.label).views (D.extend q₀ y) ⟨⟨r, hr⟩, hd⟩ w ≠
        (M.comp q.label).views D ⟨⟨r, hr⟩, hd⟩ w := fun he => h' (by rw [he])
    refine ⟨?_, fun hc => hv (funext fun τ => view_extend_of_not_merkle hq hcol hc.1 hc.2)⟩
    rcases (M.comp q.label).root_or_nodeKids_of_views_ne hq hv with ⟨τ, hτ⟩ | hk
    · exact Or.inl ⟨⟨⟨r, hr⟩, hd⟩, w, τ, hw, hτ⟩
    · exact Or.inr hk
  · exfalso
    obtain ⟨d, hdl, hc⟩ := Option.bind_eq_some_iff.1 h
    rw [hdl] at h'
    have h2 : M.extChal (D.extend q₀ y) ss chs q (l.take r) d ((P q.label).chIdx ⟨r, hr⟩ hd) ≠
        some v := h'
    exact h2 (M.extChal_extend_of_eq_some ss chs hq hc)

/-- `extLeaf_merkle` in the converse direction, for any fresh entry: only a Merkle entry. -/
theorem extLeaf_ne_merkle (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision) (q : t.Leaf)
    (l : M.Items q) :
    ∀ r (hr : r ≤ n q.label) {tr}, M.extLeaf D ss chs q l r hr = some tr →
      M.extLeaf (D.extend q₀ y) ss chs q l r hr ≠ some tr →
      (M.RootHit q l y.digest ∨ y.digest ∈ nodeKids D) ∧
        ¬ (q₀.children = none ∧ q₀.opening = none)
  | 0, _, _, h, h' => absurd h (by rw [extLeaf] at h' ⊢; exact h')
  | r + 1, hr, tr, h, h' => by
    rw [extLeaf_succ] at h' h
    obtain ⟨tr₀, h₀, hv⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, hsv, rfl⟩ := Option.map_eq_some_iff.1 hv
    by_cases hD : M.extLeaf (D.extend q₀ y) ss chs q l r (by omega) = some tr₀
    · rw [hD, Option.bind_some] at h'
      exact M.extStep_ne_merkle ss chs hq hcol hsv fun hs => h' (by rw [hs, Option.map_some])
    · exact extLeaf_ne_merkle hq hcol q l r (by omega) h₀ hD

/-- `extPast_merkle` in the converse direction, for any fresh entry: only a Merkle entry. -/
theorem extPast_ne_merkle (hq : q₀ ∉ D) (hcol : D.extend q₀ y ∉ digestCollision)
    (c : ChIdx P t) (l : M.Items c.leaf) {past : CausalPast P c}
    (h : M.extPast D ss chs c l = some past)
    (h' : M.extPast (D.extend q₀ y) ss chs c l ≠ some past) :
    ((M.RootHit c.leaf l y.digest ∨ ∃ r : t.Leaf, r.Before c.leaf ∧ M.RootHit r (chs r) y.digest) ∨
      y.digest ∈ nodeKids D) ∧ ¬ (q₀.children = none ∧ q₀.opening = none) := by
  obtain ⟨ctx, hctx, hown⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨own, hown', rfl⟩ := Option.map_eq_some_iff.1 hown
  by_cases hctx' : M.extCtx (D.extend q₀ y) ss chs c.leaf = some ctx
  · rw [extPast, hctx', Option.bind_some] at h'
    have hne : M.extLeaf (D.extend q₀ y) ss chs c.leaf l c.idx.1 c.idx.1.2.le ≠ some own :=
      fun he => h' (by rw [he]; rfl)
    obtain ⟨h1 | h1, hm⟩ := M.extLeaf_ne_merkle ss chs hq hcol c.leaf l _ _ hown' hne
    · exact ⟨Or.inl (Or.inl h1), hm⟩
    · exact ⟨Or.inr h1, hm⟩
  · obtain ⟨r, hr⟩ : ∃ r : {q : t.Leaf // q.Before c.leaf},
        M.extLeaf (D.extend q₀ y) ss chs r.1 (chs r.1) (n r.1.label) le_rfl ≠ some (ctx r) := by
      by_contra hne
      push Not at hne
      exact hctx' (optAll_eq_some.2 hne)
    obtain ⟨h1 | h1, hm⟩ := M.extLeaf_ne_merkle ss chs hq hcol r.1 (chs r.1) _ _
      (optAll_eq_some.1 hctx r) hr
    · exact ⟨Or.inl (Or.inr ⟨r.1, r.2, h1⟩), hm⟩
    · exact ⟨Or.inr h1, hm⟩

/-- **The carrier step for roots**: a root hit in the chains read at a recorded chain input of
leaf `p` is among the roots of that input or of the final input of the hidden branch. -/
theorem mem_merkleTargets_of_rootHit {p : t.Leaf}
    (hwf : ∀ r, r.Before p → chainWF (P r.label) (chs r) ∧ (chs r).length = n r.label)
    {l : M.Items p} (hl : chainWF (P p.label) l) (hlen : l.length < n p.label) {a : Out k e}
    (ha : M.keyD D ss chs p l = some a) {d : Digest k}
    (hhit : M.RootHit p l d ∨ ∃ r : t.Leaf, r.Before p ∧ M.RootHit r (chs r) d) :
    d ∈ M.merkleTargets D := by
  unfold keyD at ha
  split_ifs at ha with hrec
  have hin : M.inputD D ss chs p l ∈ D := DB.mem_iff_lookup.2 ⟨a, ha⟩
  have hwfc := wf_roundContent_of_before ss (M.finalsD D ss chs) hwf hl hlen
  have hmem : ∀ z : Query k kN kS L, z ∈ D → d ∈ M.merkleAt z → d ∈ M.merkleTargets D :=
    fun z hz hd => Finset.mem_biUnion.2 ⟨z, Finmap.mem_keys.2 hz, hd⟩
  rcases hhit with ⟨i, w, τ, hw, rfl⟩ | ⟨r, hr, i, w, τ, hw, rfl⟩
  · refine hmem _ hin ?_
    simp only [merkleAt, inputD, M.senc.decode_encode _ hwfc, Option.map_some, Option.getD_some]
    simp only [roundContent, contentRoots, fullChains]
    refine Finset.mem_biUnion.2 ⟨⟨p, ⟨i, τ⟩⟩, Finset.mem_univ _, ?_⟩
    simp [rootOfChain, hw]
  · have hrp : r ≠ p := fun he => Leaf.not_before_self p (he ▸ hr)
    by_cases hv : (Merges.Obs.leaf p : Mg.Obs).Visible r
    · refine hmem _ hin ?_
      simp only [merkleAt, inputD, M.senc.decode_encode _ hwfc, Option.map_some,
        Option.getD_some]
      simp only [roundContent, contentRoots, fullChains]
      refine Finset.mem_biUnion.2 ⟨⟨r, ⟨i, τ⟩⟩, Finset.mem_univ _, ?_⟩
      simp [rootOfChain, Function.update_of_ne hrp, Merges.Obs.viewChains_of_visible _ _ hv, hw]
    · obtain ⟨s, hs, hm⟩ := Merges.Obs.exists_hides_of_sees (o := .leaf p) hr hv
      have hwff := wf_finalContent_of_sees ss (M.finalsD D ss chs) (s := s) fun r' hr' =>
        hwf r' (Merges.sees_of_sees_sink hs hr')
      refine hmem _ (hrec s hs) ?_
      simp only [merkleAt, finalInputD, M.senc.decode_encode _ hwff, Option.map_some,
        Option.getD_some]
      simp only [finalContent, contentRoots, fullChains]
      refine Finset.mem_biUnion.2 ⟨⟨r, ⟨i, τ⟩⟩, Finset.mem_univ _, ?_⟩
      simp [rootOfChain, Merges.Obs.viewChains_of_visible _ _ (Merges.visible_sink_of_mem hm), hw]

end MerkleChain

/-! ### The flips by class -/

section Flip

variable {M : SPBCS Mg P X k kN kS L e} {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit}
  {S : CausalStateFn P t X} {D : ODB k kN kS L e} {α : Digest k} {σ : FiatShamirSalt kS}
  {b : Bytes L} {q₀ : Query k kN kS L} {y : Out k e}

/-- **Flipping into `bad` at a fresh stream point**: the answer's digest is the slot of a
recorded input at the position its key fixes, or the answer completes a challenge (`nextBad`). -/
theorem flip_into_bad_xof (hD : D ∉ M.bad rel E S) (hq : Query.xof α σ ∉ D)
    (hcol : D.extend (.xof α σ) y ∉ digestCollision)
    (h : D.extend (.xof α σ) y ∈ M.bad rel E S) :
    y.digest ∈ M.slotAbsorb D α ∨ M.nextBad rel E S D (.xof α σ) y := by
  obtain ⟨ss, c, chs, l, past, a', s', ch, hfull, hl, hpast', ha', hs', hc, hflip⟩ := h
  obtain ⟨hwf, hlwf, hlen⟩ := M.wf_of_extPast (D.extend (.xof α σ) y) ss chs hfull hl hpast'
  have ha := M.keyD_of_extend_xof ss chs hq hwf hlwf hlen ha'
  by_cases hpast : M.extPast D ss chs c l = some past
  · cases hs : D.lookup (.xof a'.digest ss.salt) with
    | none =>
      obtain ⟨h1, rfl⟩ := eq_of_lookup_extend hs hs'
      exact Or.inr ⟨ss, c, chs, l, past, a', ch, hfull, hl, hpast, ha, h1.symm, hc, hflip⟩
    | some s =>
      obtain rfl : s' = s :=
        (Option.some_inj.1 ((lookup_extend_of_lookup hq hs).symm.trans hs')).symm
      exact absurd ⟨ss, c, chs, l, past, a', s', ch, hfull, hl, hpast, ha, hs, hc, hflip⟩ hD
  · exact Or.inl (M.mem_slotAbsorb_of_hit ss chs hwf hlwf hlen ha
      (M.extPast_xof ss chs hq hcol c hfull l hpast' hpast))

/-- **The per-step bound at a fresh stream point**: at most `β` plus `|D| / 2^(8k)`. -/
theorem flip_bad_le_xof (hDb : D ∉ M.bad rel E S) (hDc : D ∉ digestCollision)
    (hq : Query.xof α σ ∉ D) {β : ℝ≥0∞}
    (hβ : Pr[y ← Out k e : M.nextBad rel E S D (.xof α σ) y] ≤ β) :
    Pr[y ← Out k e : D.extend (.xof α σ) y ∈ M.bad rel E S ∩ digestCollisionᶜ] ≤
      β + (D.size : ℝ≥0∞) / 2 ^ (8 * k) := by
  calc Pr[y ← Out k e : D.extend (.xof α σ) y ∈ M.bad rel E S ∩ digestCollisionᶜ]
      ≤ Pr[y ← Out k e : y.digest ∈ M.slotAbsorb D α ∨ M.nextBad rel E S D (.xof α σ) y] :=
        QROM.probUniform_mono fun y hy => flip_into_bad_xof hDb hq hy.2 hy.1
    _ ≤ Pr[y ← Out k e : y.digest ∈ M.slotAbsorb D α] +
          Pr[y ← Out k e : M.nextBad rel E S D (.xof α σ) y] := probUniform_or_le _ _
    _ ≤ (D.size : ℝ≥0∞) / 2 ^ (8 * k) + β := by
        refine add_le_add ?_ hβ
        rw [Out.probUniform_digest_mem]
        gcongr
        exact_mod_cast M.card_slotAbsorb_le hDc α
    _ = _ := add_comm _ _

/-- **Flipping into `bad` at a fresh chain input**: the answer's digest is a recorded stream key
or the final digest a recorded input holds at the site the input fixes. No `nextBad` and none of
the input's own digests. -/
theorem flip_into_bad_transcript (hD : D ∉ M.bad rel E S) (hq : Query.transcript b ∉ D)
    (hcol : D.extend (.transcript b) y ∉ digestCollision)
    (h : D.extend (.transcript b) y ∈ M.bad rel E S) :
    y.digest ∈ M.transcriptTargets D (.transcript b) := by
  obtain ⟨ss, c, chs, l, past, a', s', ch, hfull, hl, hpast', ha', hs', hc, hflip⟩ := h
  obtain ⟨hwf, hlwf, hlen⟩ :=
    M.wf_of_extPast (D.extend (.transcript b) y) ss chs hfull hl hpast'
  by_cases hpast : M.extPast D ss chs c l = some past
  · by_cases ha : M.keyD D ss chs c.leaf l = some a'
    · exfalso
      have hne : (Query.xof a'.digest ss.salt : Query k kN kS L) ≠ .transcript b := by simp
      rw [DB.lookup_extend_of_ne hne] at hs'
      exact hD ⟨ss, c, chs, l, past, a', s', ch, hfull, hl, hpast, ha, hs', hc, hflip⟩
    · exact M.target_of_keyD_change ss chs hq hwf hlwf hlen ha' ha hs'
  · exact M.extPast_transcript ss chs hq hcol c hfull l hpast' hpast

/-- **Flipping into `bad` at a fresh Merkle entry**: the answer's digest is a root carried by a
recorded chain input or a child of a recorded node. -/
theorem flip_into_bad_merkle (hD : D ∉ M.bad rel E S) (hq : q₀ ∉ D)
    (hqt : ∀ b, q₀ ≠ .transcript b) (hqx : ∀ κ σ, q₀ ≠ .xof κ σ)
    (h : D.extend q₀ y ∈ M.bad rel E S) : y.digest ∈ M.merkleTargets D := by
  obtain ⟨ss, c, chs, l, past, a', s', ch, hfull, hl, hpast', ha', hs', hc, hflip⟩ := h
  obtain ⟨hwf, hlwf, hlen⟩ := M.wf_of_extPast (D.extend q₀ y) ss chs hfull hl hpast'
  have ha := M.keyD_of_extend_not_transcript ss chs hq hqt hwf hlwf hlen ha'
  by_cases hpast : M.extPast D ss chs c l = some past
  · exfalso
    rw [DB.lookup_extend_of_ne fun he => hqx _ _ he.symm] at hs'
    exact hD ⟨ss, c, chs, l, past, a', s', ch, hfull, hl, hpast, ha, hs', hc, hflip⟩
  · rcases M.extPast_merkle ss chs hq hqt hqx c hfull l hpast' hpast with h1 | h1
    · exact M.mem_merkleTargets_of_rootHit ss chs hwf hlwf hlen ha h1
    · exact M.nodeKids_subset D h1

/-- **Flipping out of `bad`**: only a fresh Merkle entry, whose digest is a root carried by a
recorded chain input or a child of a recorded node. -/
theorem flip_out_of_bad_merkle (hD : D ∈ M.bad rel E S) (hq : q₀ ∉ D)
    (hcol : D.extend q₀ y ∉ digestCollision) (h : D.extend q₀ y ∉ M.bad rel E S) :
    y.digest ∈ M.merkleTargets D ∧ ¬ (q₀.children = none ∧ q₀.opening = none) := by
  obtain ⟨ss, c, chs, l, past, a, s, ch, hfull, hl, hpast, ha, hs, hc, hflip⟩ := hD
  by_cases hpast' : M.extPast (D.extend q₀ y) ss chs c l = some past
  · exact absurd ⟨ss, c, chs, l, past, a, s, ch, hfull, hl, hpast',
      M.keyD_extend_of_eq_some ss chs hq ha, lookup_extend_of_lookup hq hs, hc, hflip⟩ h
  · obtain ⟨hwf, hlwf, hlen⟩ := M.wf_of_extPast D ss chs hfull hl hpast
    obtain ⟨h1 | h1, hm⟩ := M.extPast_ne_merkle ss chs hq hcol c l hpast hpast'
    · exact ⟨M.mem_merkleTargets_of_rootHit ss chs hwf hlwf hlen ha h1, hm⟩
    · exact ⟨M.nodeKids_subset D h1, hm⟩

end Flip

/-! ### The dispatch over the classes -/

section Dispatch

variable {M : SPBCS Mg P X k kN kS L e} {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit}
  {S : CausalStateFn P t X} {D : ODB k kN kS L e} {q : Query k kN kS L}

/-- A property of a uniform answer that puts its digest in `A` has probability at most
`|A| / 2^(8k)`. -/
theorem prob_le_of_target {A : Finset (Digest k)} {Q : Out k e → Prop}
    (h : ∀ y, Q y → y.digest ∈ A) :
    Pr[y ← Out k e : Q y] ≤ (A.card : ℝ≥0∞) / 2 ^ (8 * k) :=
  (QROM.probUniform_mono h).trans_eq (Out.probUniform_digest_mem A)

/-- **The flip into `bad` at one database and one fresh query, by class**:
`β + max 2 T · tq / 2^(8k)`, `T` the number of trees of the composite. -/
theorem flip_bad_le_slot (hDb : D ∉ M.bad rel E S) (hDc : D ∉ digestCollision) {tq : ℕ}
    (hs : D.size < tq) (hq : q ∉ D) {β : ℝ≥0∞}
    (hβ : Pr[y ← Out k e : M.nextBad rel E S D q y] ≤ β) :
    Pr[y ← Out k e : D.extend q y ∈ M.bad rel E S ∩ digestCollisionᶜ] ≤
      β + M.slotCollisionBound tq := by
  unfold slotCollisionBound
  have hsz : D.size ≤ max 2 (Fintype.card M.TreeSig) * tq :=
    calc D.size ≤ 1 * tq := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ ((by norm_num : 1 ≤ 2).trans (le_max_left _ _))
  have hsz' : max 2 (Fintype.card M.TreeSig) * D.size ≤ max 2 (Fintype.card M.TreeSig) * tq :=
    Nat.mul_le_mul_left _ hs.le
  cases q with
  | xof α σ =>
    refine (flip_bad_le_xof hDb hDc hq hβ).trans (add_le_add le_rfl ?_)
    gcongr
  | transcript b =>
    refine le_add_left ((prob_le_of_target fun y hy =>
      flip_into_bad_transcript hDb hq hy.2 hy.1).trans ?_)
    gcongr
    exact_mod_cast (M.card_transcriptTargets_le D _).trans hsz
  | leaf ν c =>
    refine le_add_left ((prob_le_of_target fun y hy =>
      flip_into_bad_merkle (y := y) hDb hq (by simp) (by simp) hy.1).trans ?_)
    gcongr
    exact_mod_cast (M.card_merkleTargets_le D).trans hsz'
  | node l r =>
    refine le_add_left ((prob_le_of_target fun y hy =>
      flip_into_bad_merkle (y := y) hDb hq (by simp) (by simp) hy.1).trans ?_)
    gcongr
    exact_mod_cast (M.card_merkleTargets_le D).trans hsz'

/-- **The flip out of `bad` at one database and one fresh query**: `max 2 T · tq / 2^(8k)`. -/
theorem flip_compl_bad_le_slot (hDb : D ∈ M.bad rel E S) {tq : ℕ} (hs : D.size < tq)
    (hq : q ∉ D) :
    Pr[y ← Out k e : D.extend q y ∈ (M.bad rel E S)ᶜ ∩ digestCollisionᶜ] ≤
      M.slotCollisionBound tq := by
  unfold slotCollisionBound
  refine (prob_le_of_target fun y hy => (flip_out_of_bad_merkle hDb hq hy.2 hy.1).1).trans ?_
  gcongr
  exact_mod_cast (M.card_merkleTargets_le D).trans (Nat.mul_le_mul_left _ hs.le)

variable [∀ j i, Nonempty ((P j).Challenge i)] {ε : ChIdx P t → ℝ≥0}
  {claim : X → Prop} {claimOut : X → FullTr P t → Prop}

variable (M rel E S)

/-- `flip(bad | P̄_col, t) ≤ maxError ε + max 2 T · t / 2^(8k)`. -/
theorem condFlip_bad_le_slot (hrbr : CausalRBR rel E S ε claim claimOut) {tq : ℕ} :
    condFlip (M.bad rel E S) digestCollisionᶜ tq ≤
      maxError ε + M.slotCollisionBound tq :=
  flipProb_le fun D hD hs q hq =>
    flip_bad_le_slot hD.1 hD.2 hs hq (prob_nextBad_le hD.2 hrbr)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- `flip(complement of bad | P̄_col, t) ≤ max 2 T · t / 2^(8k)`. -/
theorem condFlip_compl_bad_le_slot {tq : ℕ} :
    condFlip (M.bad rel E S)ᶜ digestCollisionᶜ tq ≤
      M.slotCollisionBound tq :=
  flipProb_le fun D hD hs q hq => by
    rw [compl_compl] at hD
    exact flip_compl_bad_le_slot hD.1 hs hq

/-- **The conditional instability of `bad` at the slot constant**:
`I(bad | P̄_col, t) ≤ maxError ε + max 2 T · t / 2^(8k)` (`condFlip_bad_le_slot`,
`condFlip_compl_bad_le_slot`). -/
theorem condInstab_bad_le_slot (hrbr : CausalRBR rel E S ε claim claimOut) {tq : ℕ} :
    condInstab (M.bad rel E S) digestCollisionᶜ tq ≤ maxError ε + M.slotCollisionBound tq :=
  max_le (M.condFlip_bad_le_slot rel E S hrbr)
    ((M.condFlip_compl_bad_le_slot rel E S).trans le_add_self)

/-- `condFlip_bad_le_slot` at the collision bound `collisionBound`, when
`max 2 T ≤ max 2 c + nJ`. -/
theorem condFlip_bad_le_of_card_le (hrbr : CausalRBR rel E S ε claim claimOut) {tq : ℕ}
    (hT : max 2 (Fintype.card M.TreeSig) ≤ max 2 M.senc.digestsPerInput + Mg.nJ) :
    condFlip (M.bad rel E S) digestCollisionᶜ tq ≤ maxError ε + M.collisionBound tq := by
  refine (M.condFlip_bad_le_slot rel E S hrbr).trans (add_le_add le_rfl ?_)
  rw [collisionBound, slotCollisionBound]
  gcongr

end Dispatch

end GordieHowe.SPBCS
