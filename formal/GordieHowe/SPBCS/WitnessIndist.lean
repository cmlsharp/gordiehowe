-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.WitnessIndist
public import GordieHowe.SPBCS.CompleteAdaptive
public import GordieHowe.SPBCS.Merkle.LeafHidingCausal

@[expose] public section

/-!
# Unconditional witness indistinguishability of the spBCS compiler

Adaptive, multi-theorem, everlasting (statistical) witness indistinguishability (CY24 Definition
33.1.1, p. 426, at unbounded queries) of the spBCS compiler (`GordieHowe/SPBCS/Basic.lean`)
against a distinguisher that receives the whole random oracle. The argument is the one for the
compiler over the term (`GordieHowe/SPBCS/FullPast/WitnessIndist.lean`) with the merge chains, challenges
and verifier, per proof query at a fixed oracle:

1. *Leaf equivocation* (`close_realLaw_idealLaw`): the honest proof is a function of its leaf
   (Merkle salt, digest) pairs (`prove_eq_proofTr`); replacing them by uniform digests with Merkle
   salts drawn from their preimages costs at most `|Pos| · leafDist h`. A column is that of a
   message at the challenges derived from the digests, which read only the digests of earlier
   global rounds (`rankCausal_colD`), so the replacement goes tree by tree in global round order
   (`tvDist_leafPairs_causal_le`).
2. *The fixed-point laws* (`close_idealLaw`): in the ideal law the proof is a kernel applied to
   the composite view, the digests and the Fiat–Shamir challenges, which are the unique
   self-consistent challenges of the spBCS verifier (`fsD_eq_iff`, from
   `chOfW_answersW_eq_iff`; uniqueness is `eq_of_chV_skeletonW_of_le`, by induction along the
   global round order).
3. *The salt bound* (`expect_sup'_fpDist_le`): the salt slices of the oracle are independent given
   its salt-free part; on each slice the challenges are dominated by uniform ones up to
   `overrun + keyCollision (t.size n) k` (`prob_sample_none_or_chOfW_mem_le`).
4. *The leaf term* and *the hybrid* over the `Q` proof queries (`GordieHowe.SPBCS.Base.wiAdvantageWith_le_of`).

The theorem (`wiAdvantage_le`): `wiAdvantage ≤ Q · wiError δ |choices|`, with the error of the
compiler over the term (`GordieHowe.SPBCS.Base.wiError`), from the views of two witnesses being at average
distance at most `2δ` (`GordieHowe.SPBCS.Base.ObsClose`), which honest-verifier zero knowledge of the
composite at error `δ` gives (`GordieHowe.SPBCS.Base.obsClose_of_causalHVZK`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open GordieHowe.QROM (replaceSlice)
open scoped ENNReal NNReal BigOperators

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

open Base (obsLaw ObsClose)
open FullPast (skeletonW skeletonTr writeD leafTr merkleSaltLaw obsD)

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {X W : Type} {M : SPBCS Mg P X k kN kS L e}

/-! ### The prover's answers for write functions that agree on its messages -/

section WriteCongr

variable (prv : CausalProver P t X) (x : X) (σ : FiatShamirSalt kS)

/-- **The prover's chains read a write function only at the causal prover's messages.** -/
theorem chainW_congr_wr {wr wr' : M.WriteFn}
    (hwr : ∀ (ch : Chs P t) (p : t.Leaf) (i : (P p.label).MessageIdx),
      wr p i (prv.run x ch p i.1) = wr' p i (prv.run x ch p i.1))
    (ws : List (Out k e)) (p : t.Leaf) : ∀ r, chainW prv x wr ws p r = chainW prv x wr' ws p r
  | 0 => rfl
  | r + 1 => by
    rw [chainW, chainW, chainW_congr_wr hwr ws p r]
    congr 2
    unfold itemW
    split_ifs with hr hd
    · exact congrArg (fun w => (Item.write ⟨⟨⟨r, hr⟩, hd⟩, w⟩ : Item k (M.comp p.label).W))
        (hwr _ p ⟨⟨r, hr⟩, hd⟩)
    · rfl
    · rfl

theorem chsW_congr_wr {wr wr' : M.WriteFn}
    (hwr : ∀ (ch : Chs P t) (p : t.Leaf) (i : (P p.label).MessageIdx),
      wr p i (prv.run x ch p i.1) = wr' p i (prv.run x ch p i.1)) (ws : List (Out k e)) :
    chsW prv x wr ws = chsW prv x wr' ws :=
  funext fun p => chainW_congr_wr prv x hwr ws p _

/-- **The queries read a write function only at the causal prover's messages.** -/
theorem queryW_congr_wr {wr wr' : M.WriteFn}
    (hwr : ∀ (ch : Chs P t) (p : t.Leaf) (i : (P p.label).MessageIdx),
      wr p i (prv.run x ch p i.1) = wr' p i (prv.run x ch p i.1)) (ws : List (Out k e))
    (u : QSlot Mg n) : queryW prv x σ wr ws u = queryW prv x σ wr' ws u := by
  cases u <;> simp only [queryW, chsW_congr_wr prv x hwr, chainW_congr_wr prv x hwr]

/-- **The prover's answers read the write functions only at the causal prover's messages.** -/
theorem answersW_congr_wr {wrOf wrOf' : (Query k kN kS L → Out k e) → M.WriteFn}
    (h : Query k kN kS L → Out k e)
    (hwr : ∀ (ch : Chs P t) (p : t.Leaf) (i : (P p.label).MessageIdx),
      wrOf h p i (prv.run x ch p i.1) = wrOf' h p i (prv.run x ch p i.1)) :
    answersW prv x σ wrOf h = answersW prv x σ wrOf' h := by
  unfold answersW
  refine ansList_congr_fun _ _ (fun j ws => ?_) _
  unfold strategy
  split
  · exact queryW_congr_wr prv x σ hwr ws _
  · rfl

/-- **The prover's answers read the oracle only on its salt's slice**, for write functions that
read only salt-free queries. -/
theorem answersW_congr_slice (wrOf : (Query k kN kS L → Out k e) → M.WriteFn)
    (hwrOf : ∀ h₁ h₂ : Query k kN kS L → Out k e,
      (∀ a, ¬ SPBCS.IsChainQuery a → h₁ a = h₂ a) → wrOf h₁ = wrOf h₂)
    {h h' : Query k kN kS L → Out k e}
    (hh : ∀ q, M.querySalt q = some σ ∨ M.querySalt q = none → h q = h' q) :
    answersW prv x σ wrOf h = answersW prv x σ wrOf h' := by
  have hwr : wrOf h = wrOf h' :=
    hwrOf _ _ fun a ha => hh a (Or.inr (M.querySalt_of_not_isChainQuery ha))
  unfold answersW
  exact ansList_congr_oracle _ _ (Dom := fun a => M.querySalt a = some σ)
    (fun i _ l => querySalt_strategy prv x σ _ i l _) (fun i l => by simp only [strategy, hwr])
    fun a ha => hh a (Or.inl ha)

/-- **The prover's answers on a fresh slice**: against `f` with the slice of `σ` answered by `g`,
the answers of a prover whose writes read only salt-free queries are those of the prover with the
fixed writes of `f` against `g`. -/
theorem answersW_replaceSlice_of (wrOf : (Query k kN kS L → Out k e) → M.WriteFn)
    (f g : Query k kN kS L → Out k e) (hw : wrOf (replaceSlice M.querySalt σ f g) = wrOf f) :
    answersW prv x σ wrOf (replaceSlice M.querySalt σ f g) =
      answersW prv x σ (fun _ => wrOf f) g := by
  unfold answersW
  rw [ansList_congr_fun _ _ (q' := strategy M prv x σ fun _ => wrOf f)
    (fun i l => by simp only [strategy, hw]) _]
  exact ansList_congr_oracle _ _ (Dom := fun a => M.querySalt a = some σ)
    (fun i _ l => querySalt_strategy prv x σ _ i l _) (fun _ _ => rfl)
    (fun a ha => by simp [replaceSlice, ha])

end WriteCongr

/-! ### The fixed point of the Fiat–Shamir transformation -/

section FixedPoint

variable (prv : CausalProver P t X) (x : X) (σ : FiatShamirSalt kS)
  (h : Query k kN kS L → Out k e)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **A challenge reads only the writes of its leaf's earlier prover rounds and of the leaves
before its leaf**: the chains it reads are those of leaves before it, and the final digests of
the branches hidden from it read only the leaves in their sinks' pasts. -/
theorem chal_congr (ss : SaltedStatement kS X) {wr wr' : M.Writes} (c : ChIdx P t)
    (hown : ∀ i : (P c.leaf.label).MessageIdx, i.1.1 < c.idx.1.1 → wr c.leaf i = wr' c.leaf i)
    (hbefore : ∀ q : t.Leaf, q.Before c.leaf → wr q = wr' q) :
    M.chal h ss wr c = M.chal h ss wr' c := by
  have hch : ∀ q, q.Before c.leaf → M.chains h ss wr q = M.chains h ss wr' q := fun q hq =>
    M.chains_congr q fun r hr => hbefore r (hr.elim (·.trans hq) (· ▸ hq))
  have hkey : M.key h ss (M.chains h ss wr) (M.finals h ss wr) c.leaf =
      M.key h ss (M.chains h ss wr') (M.finals h ss wr') c.leaf :=
    key_congr (fun q hq => hch q hq.1) fun s hs =>
      M.finals_congr fun q hq => hbefore q (Merges.sees_of_sees_sink hs hq)
  unfold chal ComponentModel.chalWith
  rw [hkey, (M.comp c.leaf.label).chainWith_congr_wr (wr c.leaf) _ _ hown]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The Fiat–Shamir fixed point with merges reads the writes in global round order**: for
write functions `wr` and `wr'` that agree at every prover round before global round `m`, a vector
`ρ` of challenges that the verifier derives from the writes of `wr` at the causal prover's messages
at `ρ`, and a vector `ρ'` derived in the same way from `wr'`, agree at every challenge up to global
round `m`. A challenge reads only the writes of its leaf's earlier prover rounds and of the leaves
before its leaf (`chal_congr`), and those messages read only the challenges before it in global
round order (`CausalProver.run_message_congr`). -/
theorem eq_of_chV_skeletonW_of_le {wr wr' : M.WriteFn} {m : ℕ}
    (hwr : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx), p.off n + i.1.1 < m → wr p i = wr' p i)
    {ρ ρ' : Chs P t} (hρ : M.chV h ⟨σ, x⟩ (skeletonW prv x wr ρ) = ρ)
    (hρ' : M.chV h ⟨σ, x⟩ (skeletonW prv x wr' ρ') = ρ') (c : ChIdx P t)
    (hc : FullPast.gIdx c ≤ m) : ρ c = ρ' c := by
  suffices H : ∀ m', m' ≤ m + 1 → ∀ c : ChIdx P t, FullPast.gIdx c < m' → ρ c = ρ' c from
    H _ le_rfl c (Nat.lt_succ_of_le hc)
  intro m'
  induction m' with
  | zero => exact fun _ c hc => absurd hc (Nat.not_lt_zero _)
  | succ m' ih =>
    intro hm c hc
    have hrun : ∀ (p : t.Leaf) (i : (P p.label).MessageIdx),
        (∀ c' : ChIdx P t, c'.leaf.Before p → FullPast.gIdx c' < m') →
        (∀ j : (P p.label).ChallengeIdx, j.1 < i.1 →
          FullPast.gIdx (⟨p, j⟩ : ChIdx P t) < m') →
        prv.run x ρ p i.1 = prv.run x ρ' p i.1 := fun p i hb ho =>
      CausalProver.run_message_congr prv x p i (fun c' hc' => ih (by omega) c' (hb c' hc'))
        fun j hj => ih (by omega) _ (ho j hj)
    have hch : M.chal h ⟨σ, x⟩ (skeletonW prv x wr ρ) c =
        M.chal h ⟨σ, x⟩ (skeletonW prv x wr' ρ') c := by
      refine chal_congr h _ c (fun i hi => ?_) (fun q hq => funext fun i => ?_)
      · simp only [skeletonW]
        rw [hwr c.leaf i (by unfold FullPast.gIdx at hc; omega)]
        rw [hrun c.leaf i (fun c' hc' => ?_) (fun j hj => ?_)]
        · have h1 := Leaf.Before.off_add_le n hc'
          have h2 := c'.idx.1.2
          unfold FullPast.gIdx at hc ⊢
          omega
        · unfold FullPast.gIdx at hc ⊢
          simp only
          omega
      · simp only [skeletonW]
        have h3 := Leaf.Before.off_add_le n hq
        have h4 := i.1.2
        rw [hwr q i (by unfold FullPast.gIdx at hc; omega)]
        rw [hrun q i (fun c' hc' => ?_) (fun j hj => ?_)]
        · have h1 := Leaf.Before.off_add_le n hc'
          have h2 := c'.idx.1.2
          unfold FullPast.gIdx at hc ⊢
          omega
        · have h4 := j.1.2
          unfold FullPast.gIdx at hc ⊢
          simp only
          omega
    calc ρ c = M.chV h ⟨σ, x⟩ (skeletonW prv x wr ρ) c := (congrFun hρ c).symm
      _ = M.chV h ⟨σ, x⟩ (skeletonW prv x wr' ρ') c := by simp only [chV, hch]
      _ = ρ' c := congrFun hρ' c

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The Fiat–Shamir fixed point with merges is unique**: for a write function `wr`, two
challenge vectors that the verifier derives from the writes of `wr` at the causal prover's
messages at those challenges are equal (`eq_of_chV_skeletonW_of_le`). -/
theorem eq_of_chV_skeletonW (wr : M.WriteFn) {ρ ρ' : Chs P t}
    (hρ : M.chV h ⟨σ, x⟩ (skeletonW prv x wr ρ) = ρ)
    (hρ' : M.chV h ⟨σ, x⟩ (skeletonW prv x wr ρ') = ρ') : ρ = ρ' :=
  funext fun c => eq_of_chV_skeletonW_of_le prv x σ h (m := t.size n) (fun _ _ _ => rfl) hρ hρ' c
    (FullPast.gIdx_lt_size c).le

/-- **The derived challenges are the unique self-consistent challenges**: the challenges derived
by the prover with write functions `wrOf` against `h` are `ρ` exactly when the verifier,
recomputing the chains from the writes at the prover's messages at `ρ`, derives `ρ`. -/
theorem chOfW_answersW_eq_iff (wrOf : (Query k kN kS L → Out k e) → M.WriteFn) (ρ : Chs P t) :
    M.chOfW (answersW prv x σ wrOf h) = ρ ↔
      M.chV h ⟨σ, x⟩ (skeletonW prv x (wrOf h) ρ) = ρ := by
  have hfix : M.chV h ⟨σ, x⟩ (skeletonW prv x (wrOf h) (M.chOfW (answersW prv x σ wrOf h))) =
      M.chOfW (answersW prv x σ wrOf h) := chV_eq prv x σ wrOf h _ fun _ _ => rfl
  constructor
  · rintro rfl
    exact hfix
  · exact fun hρ => eq_of_chV_skeletonW prv x σ h (wrOf h) hfix hρ

end FixedPoint

/-! ### The prover at given leaf digests -/

section Digests

variable (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (σ : FiatShamirSalt kS) (h : Query k kN kS L → Out k e)

/-- The answers of the prover at the leaf digests `d`. -/
noncomputable def ansD (d : M.Pos → Digest k) : List (Out k e) :=
  answersW prv x σ (fun h' => writeD E h' d) h

/-- The challenges of the prover at the leaf digests `d`. -/
noncomputable def chD (d : M.Pos → Digest k) : Chs P t :=
  M.chOfW (ansD E prv x σ h d)

/-- The column of position `q` at the leaf digests `d`: the column of its message at the
challenges `chD d`. -/
noncomputable def colD (d : M.Pos → Digest k) (q : M.Pos) : Bytes L :=
  (E q.leaf.label).cols q.pos.msg (prv.run x (chD E prv x σ h d) q.leaf q.pos.msg.1) q.pos.tree
    q.pos.leaf

/-- **The challenges at given leaf digests read the digests in global round order**: digest
vectors that agree at the positions before global round `m` give the same challenges up to global
round `m` (`eq_of_chV_skeletonW_of_le`). -/
theorem chD_congr {d d' : M.Pos → Digest k} {m : ℕ} (hd : ∀ q : M.Pos, q.gIdx < m → d q = d' q)
    (c : ChIdx P t) (hc : FullPast.gIdx c ≤ m) : chD E prv x σ h d c = chD E prv x σ h d' c :=
  eq_of_chV_skeletonW_of_le prv x σ h (fun p i hi => FullPast.writeD_congr_digests E h hd p i hi)
    ((chOfW_answersW_eq_iff prv x σ h (fun h' => writeD E h' d) _).1 rfl)
    ((chOfW_answersW_eq_iff prv x σ h (fun h' => writeD E h' d') _).1 rfl) c hc

/-- **A column reads only the digests of earlier global rounds**: the column of position `q` at
the leaf digests `d` depends only on the digests of positions whose global round is below that of
`q`. Its message reads only the challenges before it (`CausalProver.run_message_congr`), and those
read only the digests of earlier rounds (`chD_congr`). -/
theorem rankCausal_colD : PMF.RankCausal Base.Pos.gIdx (colD E prv x σ h) := fun d d' q hd => by
  unfold colD
  rw [CausalProver.run_message_congr prv x q.leaf q.pos.msg (fun c hc => ?_) fun j hj => ?_]
  · refine chD_congr E prv x σ h hd c ?_
    have h1 := Leaf.Before.off_add_le n hc
    have h2 := c.idx.1.2
    unfold FullPast.gIdx Base.Pos.gIdx
    omega
  · refine chD_congr E prv x σ h hd _ ?_
    have : j.1.1 < q.pos.msg.1.1 := hj
    unfold FullPast.gIdx Base.Pos.gIdx
    simp only
    omega

end Digests

/-! ### The honest prover factors through its leaf digests -/

section Factor

variable (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS) (h : Query k kN kS L → Out k e)

/-- **The honest leaf digests**: the digest of the Merkle salt `ν q` and the column of position `q`
at the honest challenges. -/
noncomputable def honestD (q : M.Pos) : Digest k :=
  MerkleTree.leafDigest h ⟨ν q, (E q.leaf.label).cols q.pos.msg
    (prv.run x (honestCh prv x σ E ν h) q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- At the honest challenges, the digests of the honest leaves are the honest leaf digests. -/
theorem leafDigest_leafFn_honest (p : t.Leaf) (i : (P p.label).MessageIdx)
    (τ : Fin ((M.comp p.label).nTrees i)) (j : ℕ) :
    MerkleTree.leafDigest h (Base.leafFn E ν p i (prv.run x (honestCh prv x σ E ν h) p i.1) τ j) =
      M.toFullPast.leafDigestsOf h (honestD E prv x ν σ h) p i τ j := by
  unfold Base.leafFn FullPast.leafDigestsOf honestD
  split_ifs <;> rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- At the honest challenges, the honest write is the write at the honest leaf digests. -/
theorem honestWrite_eq_writeD (p : t.Leaf) (i : (P p.label).MessageIdx) :
    Base.honestWrite E ν h p i (prv.run x (honestCh prv x σ E ν h) p i.1) =
      writeD E h (honestD E prv x ν σ h) p i (prv.run x (honestCh prv x σ E ν h) p i.1) := by
  unfold Base.honestWrite writeD FullPast.rootsOf
  congr 1
  funext τ
  unfold MerkleTree.root MerkleTree.treeDigest
  congr 1
  funext j
  exact leafDigest_leafFn_honest E prv x ν σ h p i τ j

/-- **The challenges at the honest leaf digests are the honest challenges**: both are the fixed
point of the writes at the causal prover's messages at the honest challenges
(`chOfW_answersW_eq_iff`). -/
theorem chD_honestD : chD E prv x σ h (honestD E prv x ν σ h) = honestCh prv x σ E ν h := by
  have hfix : M.chV h ⟨σ, x⟩ (skeletonW prv x (Base.honestWrite E ν h) (honestCh prv x σ E ν h)) =
      honestCh prv x σ E ν h := (chOfW_answersW_eq_iff prv x σ h (Base.honestWrite E ν) _).1 rfl
  have hsk : skeletonW prv x (Base.honestWrite E ν h) (honestCh prv x σ E ν h) =
      skeletonW prv x (writeD E h (honestD E prv x ν σ h)) (honestCh prv x σ E ν h) :=
    funext fun p => funext fun i => honestWrite_eq_writeD E prv x ν σ h p i
  rw [hsk] at hfix
  exact (chOfW_answersW_eq_iff prv x σ h (fun h' => writeD E h' (honestD E prv x ν σ h)) _).2 hfix

/-- **The honest leaf digests solve the leaf equations**: the digest of position `q` is that of
its Merkle salt and its column at the honest leaf digests (`chD_honestD`). -/
theorem honestD_eq (q : M.Pos) :
    honestD E prv x ν σ h q = SPBCS.digestOf h
      (SPBCS.leafEnc (colD E prv x σ h (honestD E prv x ν σ h) q) (ν q)) := by
  rw [colD, chD_honestD]
  rfl

end Factor

/-! ### The proof read from what it reveals -/

section Observation

variable {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x}

variable (E Qs) (h : Query k kN kS L → Out k e) (x : X) (σ : FiatShamirSalt kS)

/-- The positions the spBCS verifier opens on the writes of `tr` at the challenges `ρ`. -/
def posTr (d : M.Pos → Digest k) (ρ : Chs P t) (tr : FullTr P t) : List M.Pos :=
  (Qs x).pos (M.chains h ⟨σ, x⟩ (skeletonTr E h d tr)) ρ

/-- **The merge proof read from a transcript**: at the challenges `ρ`, the leaf digests `d` and
the Merkle salts `ν`, the writes of the messages of `tr`, the opened leaves (Merkle salt and column
of `tr`) at the positions the spBCS verifier recomputes, and the multiproofs over `d`. -/
def proofTr (d : M.Pos → Digest k) (ρ : Chs P t) (tr : FullTr P t)
    (ν : M.Pos → MerkleSalt kN) : M.NIProof where
  salt := σ
  writes := skeletonTr E h d tr
  leaves := (posTr E Qs h x σ d ρ tr).map (leafTr E tr ν)
  paths τ := (M.opening.sibs ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
    ((M.openedIn τ (posTr E Qs h x σ d ρ tr)
      ((posTr E Qs h x σ d ρ tr).map (leafTr E tr ν))).map Prod.fst)).map
        (MerkleTree.nodeDigest h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
          (M.toFullPast.leafDigestsOf h d τ.leaf τ.tree.msg τ.tree.tree))

/-- **The challenges at given leaf digests are the self-consistent ones**: they are `ρ` exactly
when the spBCS verifier, recomputing the chains from the writes of the prover's run at `ρ`,
derives `ρ` (`chOfW_answersW_eq_iff`). -/
theorem chD_eq_iff (prv : CausalProver P t X) (d : M.Pos → Digest k) (ρ : Chs P t) :
    chD E prv x σ h d = ρ ↔ M.chV h ⟨σ, x⟩ (skeletonTr E h d (prv.run x ρ)) = ρ :=
  chOfW_answersW_eq_iff prv x σ h (fun h' => writeD E h' d) ρ

/-- **The honest spBCS prover is read from its run**: the honest proof is `proofTr` of the run at
the honest challenges, at the honest leaf digests (`honestD`) and the Merkle salts `ν`. -/
theorem prove_eq_proofTr (prv : CausalProver P t X) (ν : M.Pos → MerkleSalt kN) :
    prove prv x σ E ν h (Qs x) =
      proofTr E Qs h x σ (honestD E prv x ν σ h) (honestCh prv x σ E ν h)
        (prv.run x (honestCh prv x σ E ν h)) ν := by
  set ρ := honestCh prv x σ E ν h with hρ
  have hwrites : (prove prv x σ E ν h (Qs x)).writes =
      skeletonTr E h (honestD E prv x ν σ h) (prv.run x ρ) :=
    funext fun p => funext fun i => honestWrite_eq_writeD E prv x ν σ h p i
  have hpos : honestPos prv x σ E ν h (Qs x) =
      posTr E Qs h x σ (honestD E prv x ν σ h) ρ (prv.run x ρ) := by
    unfold honestPos posTr
    rw [← chains_prove prv x σ E ν h (Qs x), hwrites]
  have hleaves : honestLeaves prv x σ E ν h (Qs x) =
      (posTr E Qs h x σ (honestD E prv x ν σ h) ρ (prv.run x ρ)).map (leafTr E (prv.run x ρ) ν) := by
    unfold honestLeaves
    rw [hpos]
    exact List.map_congr_left fun q _ => by rw [Base.leafFn_val, leafTr]
  unfold prove proofTr
  congr 1
  funext τ
  unfold MerkleFormat.path MerkleTree.treeDigest
  rw [hleaves, hpos]
  congr 1
  funext j
  congr 1
  funext j'
  exact leafDigest_leafFn_honest E prv x ν σ h _ τ.tree.msg τ.tree.tree j'

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The proof read from a transcript reads the Merkle salts only at the opened positions. -/
theorem proofTr_congr_merkleSalt (d : M.Pos → Digest k) (ρ : Chs P t) (tr : FullTr P t)
    {ν ν' : M.Pos → MerkleSalt kN} (hν : ∀ q ∈ posTr E Qs h x σ d ρ tr, ν q = ν' q) :
    proofTr E Qs h x σ d ρ tr ν = proofTr E Qs h x σ d ρ tr ν' := by
  unfold proofTr
  congr 1
  · exact List.map_congr_left fun q hq => by rw [leafTr, leafTr, hν q hq]
  · funext τ
    rw [Base.map_fst_openedIn _ (leafTr E tr ν')]

variable {E Qs} (Rv : M.Reveal E Qs)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
include Rv in
/-- **Transcripts with the same view give the same merge proof**, at their challenges. -/
theorem proofTr_congr (d : M.Pos → Digest k) {ρ : Chs P t} {tr tr' : FullTr P t}
    (hρ : tr.challenges = ρ) (ho : Rv.MV.view tr = Rv.MV.view tr') (ν : M.Pos → MerkleSalt kN) :
    proofTr E Qs h x σ d ρ tr ν = proofTr E Qs h x σ d ρ tr' ν := by
  have hsk := FullPast.skeletonTr_congr h x Rv d ho
  have hpos : posTr E Qs h x σ d ρ tr = posTr E Qs h x σ d ρ tr' := by
    unfold posTr
    rw [hsk]
  have hleaves : (posTr E Qs h x σ d ρ tr).map (leafTr E tr ν) =
      (posTr E Qs h x σ d ρ tr').map (leafTr E tr' ν) := by
    rw [hpos]
    exact List.map_congr_left fun q hq => by
      rw [leafTr, leafTr, Rv.col_congr x _ ρ hρ ho q hq]
  unfold proofTr
  congr 1
  · funext τ
    rw [hleaves, hpos, Base.map_fst_openedIn _ (leafTr E tr' ν)]

end Observation

/-! ### One proof query at a fixed oracle and salt -/

section OneProof

variable {V : X → FullTr P t → Bool}
variable (E : (j : ι) → (M.comp j).Encoder)
  (Qs : ∀ x, M.IOPQueries V x) (h : Query k kN kS L → Out k e) (x : X) (σ : FiatShamirSalt kS)
  {R : Type} [Fintype R] [Nonempty R]

/-- The real law of the merge proof at the salt `σ`: causal prover coins and Merkle salts
uniform. -/
noncomputable def realLaw (prv : R → CausalProver P t X) : PMF M.NIProof :=
  (PMF.uniformOfFintype R).bind fun r =>
    (PMF.uniformOfFintype (M.Pos → MerkleSalt kN)).map fun ν => prove (prv r) x σ E ν h (Qs x)

/-- The ideal law of the merge proof at the salt `σ`: causal prover coins and leaf digests
uniform, Merkle salts drawn from the preimages of the digests at the columns of the run at the
challenges derived from them (`colD`), and the proof read from that run (`proofTr`). -/
noncomputable def idealLaw (prv : R → CausalProver P t X) : PMF M.NIProof :=
  (PMF.uniformOfFintype (R × (M.Pos → Digest k))).bind fun c =>
    (merkleSaltLaw h (colD E (prv c.1) x σ h c.2) c.2).map
      (proofTr E Qs h x σ c.2 (chD E (prv c.1) x σ h c.2)
        ((prv c.1).run x (chD E (prv c.1) x σ h c.2)))

/-- **Leaf equivocation for the merge proof**: the real and the ideal law are within
`|Pos| · leafDist h` in total variation. The honest proof is a function of its (Merkle salt,
digest) pairs (`prove_eq_proofTr`), and the pairs are replaced tree by tree in global round order
(`tvDist_leafPairs_causal_le`, with `rankCausal_colD`). -/
theorem close_realLaw_idealLaw (prv : R → CausalProver P t X) :
    realLaw E Qs h x σ prv ≈[Fintype.card M.Pos * SPBCS.leafDist h]
      idealLaw E Qs h x σ prv := by
  classical
  let Ψ : R → (M.Pos → MerkleSalt kN) × (M.Pos → Digest k) → M.NIProof := fun r a =>
    proofTr E Qs h x σ a.2 (chD E (prv r) x σ h a.2) ((prv r).run x (chD E (prv r) x σ h a.2)) a.1
  let realPair : R → PMF ((M.Pos → MerkleSalt kN) × (M.Pos → Digest k)) := fun r =>
    (PMF.uniformOfFintype (M.Pos → MerkleSalt kN)).map fun ν =>
      (ν, honestD E (prv r) x ν σ h)
  let idealPair : R → PMF ((M.Pos → MerkleSalt kN) × (M.Pos → Digest k)) := fun r =>
    (PMF.uniformOfFintype (M.Pos → Digest k)).bind fun d =>
      (merkleSaltLaw h (colD E (prv r) x σ h d) d).map fun ν => (ν, d)
  have hreal : realLaw E Qs h x σ prv =
      (PMF.uniformOfFintype R).bind fun r => (realPair r).map (Ψ r) := by
    unfold realLaw
    congr 1
    funext r
    rw [PMF.map_comp]
    congr 1
    funext ν
    simp only [Function.comp_apply, Ψ]
    rw [chD_honestD]
    exact prove_eq_proofTr E Qs h x σ (prv r) ν
  have hideal : idealLaw E Qs h x σ prv =
      (PMF.uniformOfFintype R).bind fun r => (idealPair r).map (Ψ r) := by
    unfold idealLaw
    rw [PMF.uniformOfFintype_prod_eq_bind, PMF.bind_bind]
    congr 1
    funext r
    rw [PMF.bind_map, PMF.map_bind]
    congr 1
    funext d
    rw [PMF.map_comp]
    rfl
  have hdist : ∀ r, PMF.tvDist (realPair r) (idealPair r) ≤
      Fintype.card M.Pos * SPBCS.leafDist h := fun r =>
    tvDist_leafPairs_causal_le (SPBCS.digestOf h) SPBCS.leafEnc Base.Pos.gIdx
      (rankCausal_colD E (prv r) x σ h) (fun ν q => honestD_eq E (prv r) x ν σ h q) fun c =>
        Finset.le_sup' (fun c : Bytes L =>
          PMF.tvDist (digestLaw (SPBCS.digestOf h) (SPBCS.leafEnc c))
            (PMF.uniformOfFintype (Digest k))) (Finset.mem_univ c)
  rw [hreal, hideal]
  refine (PMF.tvDist_bind_left_le _ _ _).trans ?_
  calc ∑ r, (PMF.uniformOfFintype R r).toReal *
        PMF.tvDist ((realPair r).map (Ψ r)) ((idealPair r).map (Ψ r))
      ≤ ∑ r, (PMF.uniformOfFintype R r).toReal * (Fintype.card M.Pos * SPBCS.leafDist h) :=
        Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
          ((PMF.tvDist_map_le _ _ _).trans (hdist r)) ENNReal.toReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

end OneProof

/-! ### Two witnesses in the ideal law: the fixed-point laws -/

section Coupling

variable {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x}
variable (Rv : M.Reveal E Qs) (h : Query k kN kS L → Out k e) (x : X)
  (σ : FiatShamirSalt kS) {R : Type} [Fintype R] [Nonempty R]

variable (E) in
/-- The Fiat–Shamir challenges of the spBCS prover `prv r` at the leaf digests `d`. -/
noncomputable def fsD (prv : R → CausalProver P t X) (c : R × (M.Pos → Digest k)) :
    Chs P t :=
  chD E (prv c.1) x σ h c.2

/-- **The challenges `ρ` are self-consistent for the revealed data `od`** at the oracle `h`: some
transcript with the view `od.1` has writes, at the leaf digests `od.2`, from which the spBCS
verifier derives `ρ`. -/
def Consistent (ρ : Chs P t) (od : CausalView Rv.MV × (M.Pos → Digest k)) : Prop :=
  ∃ tr, Rv.MV.view tr = od.1 ∧ M.chV h ⟨σ, x⟩ (skeletonTr E h od.2 tr) = ρ

omit [Fintype R] [Nonempty R] in
/-- **The Fiat–Shamir challenges are the self-consistent ones**: they are `ρ` exactly when `ρ` is
self-consistent for what the ideal proof reveals at `ρ` (`chD_eq_iff`). -/
theorem fsD_eq_iff (prv : R → CausalProver P t X) (c : R × (M.Pos → Digest k))
    (ρ : Chs P t) :
    fsD E h x σ prv c = ρ ↔ Consistent Rv h x σ ρ (obsD Rv x prv c ρ) := by
  rw [fsD, chD_eq_iff]
  constructor
  · exact fun hc => ⟨_, rfl, hc⟩
  · rintro ⟨tr, ho, hc⟩
    change M.chV h ⟨σ, x⟩ (skeletonTr E h c.2 tr) = ρ at hc
    rwa [FullPast.skeletonTr_congr h x Rv c.2 ho] at hc

/-- **The fixed-point law** of the ideal merge proof at the salt `σ`: causal prover coins and
leaf digests uniform, what the proof reveals at its Fiat–Shamir challenges, with the
challenges. -/
noncomputable def fpLaw (prv : R → CausalProver P t X) :
    PMF ((CausalView Rv.MV × (M.Pos → Digest k)) × Chs P t) :=
  (PMF.uniformOfFintype (R × (M.Pos → Digest k))).map fun c =>
    (obsD Rv x prv c (fsD E h x σ prv c), fsD E h x σ prv c)

open Classical in
/-- The merge proof given what it reveals and the challenges: for a transcript with that view
at those challenges, Merkle salts from the preimages of the digests at its columns, then
`proofTr` (the fallback `π₀` is never reached on revealed data). -/
noncomputable def proofKernel (π₀ : M.NIProof)
    (a : (CausalView Rv.MV × (M.Pos → Digest k)) × Chs P t) : PMF M.NIProof :=
  if hex : ∃ tr, Rv.MV.view tr = a.1.1 ∧ tr.challenges = a.2 then
    (merkleSaltLaw h (fun q => (E q.leaf.label).cols q.pos.msg
      ((Classical.choose hex) q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf) a.1.2).map
      (proofTr E Qs h x σ a.1.2 a.2 (Classical.choose hex))
  else PMF.pure π₀

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The ideal law through what the proof reveals**: the fixed-point law of the revealed data
and the challenges, followed by `proofKernel`. The opened Merkle salts are drawn at the columns of
the opened positions, which the view determines (`Reveal.col_congr`), and the proof reads the
Merkle salts only there (`proofTr_congr_merkleSalt`). -/
theorem idealLaw_eq_bind (prv : R → CausalProver P t X) (π₀ : M.NIProof) :
    idealLaw E Qs h x σ prv =
      ((PMF.uniformOfFintype (R × (M.Pos → Digest k))).map fun c =>
        (obsD Rv x prv c (fsD E h x σ prv c), fsD E h x σ prv c)).bind
          (proofKernel Rv h x σ π₀) := by
  classical
  rw [PMF.bind_map, idealLaw]
  refine congrArg (PMF.bind _) (funext fun c => ?_)
  change _ = proofKernel Rv h x σ π₀ (obsD Rv x prv c (fsD E h x σ prv c), fsD E h x σ prv c)
  set ρ := fsD E h x σ prv c with hρ
  set tr := (prv c.1).run x ρ
  have hex : ∃ tr', Rv.MV.view tr' = Rv.MV.view tr ∧ tr'.challenges = ρ :=
    ⟨tr, rfl, CausalProver.challenges_run _ _ _⟩
  have hch : Rv.MV.view (Classical.choose hex) = Rv.MV.view tr := (Classical.choose_spec hex).1
  have hchρ : (Classical.choose hex).challenges = ρ := (Classical.choose_spec hex).2
  unfold proofKernel obsD
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  change (merkleSaltLaw h (colD E (prv c.1) x σ h c.2) c.2).map (proofTr E Qs h x σ c.2 ρ tr) = _
  rw [show proofTr E Qs h x σ c.2 ρ tr = proofTr E Qs h x σ c.2 ρ (Classical.choose hex) from
    funext fun ν => proofTr_congr h x σ Rv c.2 (CausalProver.challenges_run _ _ _) hch.symm ν]
  refine PMF.pi_map_eq_of_eqOn _ _ (posTr E Qs h x σ c.2 ρ (Classical.choose hex)).toFinset
    (fun q hq => ?_) _ fun ν ν' hν => proofTr_congr_merkleSalt E Qs h x σ _ _ _ fun q hq =>
      hν q (List.mem_toFinset.2 hq)
  have hcol : colD E (prv c.1) x σ h c.2 q =
      (E q.leaf.label).cols q.pos.msg ((Classical.choose hex) q.leaf q.pos.msg.1) q.pos.tree
        q.pos.leaf :=
    (Rv.col_congr x (M.chains h ⟨σ, x⟩ (skeletonTr E h c.2 (Classical.choose hex))) ρ hchρ
      hch q (List.mem_toFinset.1 hq)).symm
  show invert (SPBCS.digestOf h) (SPBCS.leafEnc (colD E (prv c.1) x σ h c.2 q)) (c.2 q) =
    invert (SPBCS.digestOf h) (SPBCS.leafEnc ((E q.leaf.label).cols q.pos.msg
      ((Classical.choose hex) q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf)) (c.2 q)
  rw [hcol]

/-- **The ideal laws are as close as their fixed-point laws**: the proof is a kernel applied to
what it reveals and its challenges (`idealLaw_eq_bind`). -/
theorem close_idealLaw (prv prv' : R → CausalProver P t X) :
    idealLaw E Qs h x σ prv ≈[PMF.tvDist (fpLaw Rv h x σ prv) (fpLaw Rv h x σ prv')]
      idealLaw E Qs h x σ prv' := by
  classical
  let π₀ : M.NIProof := ⟨σ, fun p i => (E p.label).write i
    (((prv (Classical.arbitrary R)).run x (fun _ => Classical.arbitrary _)) p i.1) fun _ => 0, [],
    fun _ => []⟩
  rw [idealLaw_eq_bind Rv h x σ prv π₀, idealLaw_eq_bind Rv h x σ prv' π₀]
  exact PMF.tvDist_bind_right_le _ _ _

end Coupling

/-! ### One proof query at a fixed oracle -/

section Request

variable {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x}
variable (Rv : M.Reveal E Qs) (h : Query k kN kS L → Out k e) (x : X)
  {R : Type} [Fintype R] [Nonempty R]

/-- **The fixed-point distance** of two prover families at the oracle `h`: the average over
uniform salts of the distance between their merge fixed-point laws (`fpLaw`). -/
noncomputable def fpDist (prv prv' : R → CausalProver P t X) : ℝ :=
  𝔼 σ : FiatShamirSalt kS, PMF.tvDist (fpLaw Rv h x σ prv) (fpLaw Rv h x σ prv')

theorem fpDist_nonneg (prv prv' : R → CausalProver P t X) : 0 ≤ fpDist Rv h x prv prv' :=
  Finset.expect_nonneg fun _ _ => PMF.tvDist_nonneg _ _

variable (E Qs) in
/-- The law of the merge proof at the oracle `h` for the prover family `prv` (coins uniform):
salt, causal prover coins and Merkle salts uniform. -/
noncomputable def proofLaw (prv : R → CausalProver P t X) : PMF M.NIProof :=
  (PMF.uniformOfFintype (FiatShamirSalt kS × R × (M.Pos → MerkleSalt kN))).map fun c =>
    prove (prv c.2.1) x c.1 E c.2.2 h (Qs x)

theorem proofLaw_eq_bind (prv : R → CausalProver P t X) :
    proofLaw E Qs h x prv =
      (PMF.uniformOfFintype (FiatShamirSalt kS)).bind fun σ => realLaw E Qs h x σ prv := by
  unfold proofLaw realLaw
  rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun σ => ?_)
  rw [PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun r => ?_)
  rw [PMF.map_comp]
  rfl

/-- **One spBCS proof query at a fixed oracle**: the laws of the proofs of two prover
families are within `2 · |Pos| · leafDist h` plus their fixed-point distance (`fpDist`). -/
theorem close_proofLaw (prv prv' : R → CausalProver P t X) :
    proofLaw E Qs h x prv ≈[2 * (Fintype.card M.Pos * SPBCS.leafDist h) +
      fpDist Rv h x prv prv'] proofLaw E Qs h x prv' := by
  rw [proofLaw_eq_bind, proofLaw_eq_bind]
  set a := Fintype.card M.Pos * SPBCS.leafDist h
  set β : FiatShamirSalt kS → ℝ := fun σ =>
    PMF.tvDist (fpLaw Rv h x σ prv) (fpLaw Rv h x σ prv')
  have hstep : ∀ σ, PMF.tvDist (realLaw E Qs h x σ prv) (realLaw E Qs h x σ prv') ≤
      2 * a + β σ := fun σ => by
    have h₁ := close_realLaw_idealLaw E Qs h x σ prv
    have h₂ := close_idealLaw Rv h x σ prv prv'
    have h₃ := close_realLaw_idealLaw E Qs h x σ prv'
    rw [PMF.tvDist_comm] at h₃
    linarith [PMF.tvDist_triangle (realLaw E Qs h x σ prv) (idealLaw E Qs h x σ prv)
      (realLaw E Qs h x σ prv'), PMF.tvDist_triangle (idealLaw E Qs h x σ prv)
      (idealLaw E Qs h x σ prv') (realLaw E Qs h x σ prv')]
  refine (PMF.tvDist_bind_left_le _ _ _).trans ?_
  calc ∑ σ, (PMF.uniformOfFintype (FiatShamirSalt kS) σ).toReal *
        PMF.tvDist (realLaw E Qs h x σ prv) (realLaw E Qs h x σ prv')
      ≤ ∑ σ, (PMF.uniformOfFintype (FiatShamirSalt kS) σ).toReal * (2 * a + β σ) :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hstep σ) ENNReal.toReal_nonneg
    _ = 2 * a + 𝔼 σ : FiatShamirSalt kS, β σ := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul,
          PMF.toReal_uniformOfFintype_apply, Fintype.expect_eq_sum_div_card, Finset.sum_div]
        congr 1
        exact Finset.sum_congr rfl fun σ _ => by rw [inv_mul_eq_div]

end Request

/-! ### The salt bound -/

section Salt

variable {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x}
variable (x : X) (σ : FiatShamirSalt kS) {R : Type} [Fintype R] [Nonempty R]

omit [Fintype R] [Nonempty R] in
/-- **Locality of the ideal challenges**: the merge Fiat–Shamir challenges at the salt `σ` read
the oracle only at the queries labeled `σ` and at the salt-free ones. -/
theorem fsD_congr (prv : R → CausalProver P t X) {h h' : Query k kN kS L → Out k e}
    (hh : ∀ q, M.querySalt q = some σ ∨ M.querySalt q = none → h q = h' q)
    (c : R × (M.Pos → Digest k)) : fsD E h x σ prv c = fsD E h' x σ prv c := by
  unfold fsD chD ansD
  rw [answersW_congr_slice (prv c.1) x σ (fun h' => writeD E h' c.2)
    (fun h₁ h₂ hoff => FullPast.writeD_congr_leaf_node E (fun a b => hoff _ id)
      (fun l r => hoff _ id) c.2) hh]

/-- **The mean over one salt's slice**: for any values `f` off the slice of `σ`, the probability
over the slice that the ideal merge challenges at `σ` fall in `B` is at most
`Pr[B] + overrun + keyCollision (t.size n) k` (`prob_sample_none_or_chOfW_mem_le`; the roots read
only salt-free queries, so they are fixed). -/
theorem prob_chD_mem_le (prv : CausalProver P t X) (B : Set (Chs P t))
    (f : Query k kN kS L → Out k e) (d : M.Pos → Digest k) :
    Pr[g ← (Query k kN kS L → Out k e) :
        chD E prv x σ (fun q => if M.querySalt q = some σ then g q else f q) d ∈ B] ≤
      Pr[ρ ← Chs P t : ρ ∈ B] + M.overrun + SPBCS.keyCollision (t.size n) k := by
  classical
  have hwr : ∀ g : Query k kN kS L → Out k e,
      writeD E (replaceSlice M.querySalt σ f g) d = writeD E f d := fun g =>
    FullPast.writeD_congr_leaf_node (h := replaceSlice M.querySalt σ f g) (h' := f) E
      (fun a b => rfl) (fun l r => rfl) d
  have heq : ∀ g : Query k kN kS L → Out k e,
      chD E prv x σ (fun q => if M.querySalt q = some σ then g q else f q) d =
        M.chOfW (answersW prv x σ (fun _ => writeD E f d) g) := fun g => by
    unfold chD ansD
    rw [show (fun q => if M.querySalt q = some σ then g q else f q) =
      replaceSlice M.querySalt σ f g from rfl,
      answersW_replaceSlice_of prv x σ (fun h' => writeD E h' d) f g (hwr g)]
  simp_rw [heq]
  exact (QROM.probUniform_mono fun g hg => Or.inr hg).trans
    (prob_sample_none_or_chOfW_mem_le prv x σ (fun _ => writeD E f d) (fun _ _ _ => rfl) (· ∈ B))

/-- **The mean over one salt's slice of the merge fixed-point distance**: for any values `f`
off the slice of `σ`, the average over the slice of the distance between the fixed-point laws of
two prover families at `σ` is at most the average over uniform challenges of the distance between
their view laws, plus `overrun + keyCollision (t.size n) k` (`expect_tvDist_map_fixedPoint_le`,
`prob_chD_mem_le`). -/
theorem expect_tvDist_fpLaw_le (Rv : M.Reveal E Qs) (prv prv' : R → CausalProver P t X)
    (f : Query k kN kS L → Out k e) :
    𝔼 g : Query k kN kS L → Out k e,
        PMF.tvDist (fpLaw Rv (fun q => if M.querySalt q = some σ then g q else f q) x σ prv)
          (fpLaw Rv (fun q => if M.querySalt q = some σ then g q else f q) x σ prv') ≤
      𝔼 ρ : Chs P t, PMF.tvDist (obsLaw Rv x prv ρ) (obsLaw Rv x prv' ρ) +
        M.overrun.toReal + (SPBCS.keyCollision (t.size n) k).toReal := by
  have hη : M.overrun + SPBCS.keyCollision (t.size n) k ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨M.overrun_ne_top, SPBCS.keyCollision_ne_top _ k⟩
  have hdom : ∀ (c : R × (M.Pos → Digest k)) (B : Set (Chs P t)),
      Pr[g ← (Query k kN kS L → Out k e) :
        fsD E (fun q => if M.querySalt q = some σ then g q else f q) x σ prv c ∈ B] ≤
        Pr[ρ ← Chs P t : ρ ∈ B] + (M.overrun + SPBCS.keyCollision (t.size n) k) :=
    fun c B => by
      rw [← add_assoc]
      exact prob_chD_mem_le x σ (prv c.1) B f c.2
  have h := expect_tvDist_map_fixedPoint_le (G := Query k kN kS L → Out k e)
    (Cn := R × (M.Pos → Digest k)) (C := Chs P t)
    (O := CausalView Rv.MV × (M.Pos → Digest k))
    (obsD Rv x prv) (obsD Rv x prv')
    (fun g => fsD E (fun q => if M.querySalt q = some σ then g q else f q) x σ prv)
    (fun g => fsD E (fun q => if M.querySalt q = some σ then g q else f q) x σ prv')
    (fun g => Consistent Rv (fun q => if M.querySalt q = some σ then g q else f q) x σ)
    (fun g c ρ => fsD_eq_iff Rv _ x σ prv c ρ) (fun g c ρ => fsD_eq_iff Rv _ x σ prv' c ρ) hη
    hdom
  refine h.trans ?_
  rw [ENNReal.toReal_add M.overrun_ne_top (SPBCS.keyCollision_ne_top _ k), ← add_assoc]
  exact add_le_add (add_le_add
    (Finset.expect_le_expect fun ρ _ => FullPast.tvDist_obsD_le x Rv prv prv' ρ) le_rfl) le_rfl

/-- **The salt bound of the spBCS compiler** (step 3). For finitely many choices `m` of a
statement and two prover families whose view laws are at average distance at most `β` over
uniform challenges, the expected maximum over the choices of the fixed-point distance is at most
`min 1 (β + overrun + keyCollision (t.size n) k) + √(log |C| / (2 · 2^(8k)))`: the salt slices of
the oracle are independent given its salt-free part (`expect_sup'_le_of_fibers`), and on each slice
the mean is bounded by `expect_tvDist_fpLaw_le`. -/
theorem expect_sup'_fpDist_le (Rv : M.Reveal E Qs) {C : Type} [Fintype C] [Nonempty C]
    (xc : C → X) (pc pc' : C → R → CausalProver P t X) {β : ℝ}
    (hβ : ∀ m, 𝔼 ρ : Chs P t, PMF.tvDist (obsLaw Rv (xc m) (pc m) ρ)
      (obsLaw Rv (xc m) (pc' m) ρ) ≤ β) :
    𝔼[h ← (Query k kN kS L → Out k e) : Finset.univ.sup' Finset.univ_nonempty
        (fun m => fpDist Rv h (xc m) (pc m) (pc' m))] ≤
      min 1 (β + M.overrun.toReal + (SPBCS.keyCollision (t.size n) k).toReal) +
        SPBCS.saltTerm kS (Fintype.card C) := by
  classical
  have hcard : (Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    ring
  have h := expect_sup'_le_of_fibers M.querySalt
    (fun m σ h => PMF.tvDist (fpLaw Rv h (xc m) σ (pc m)) (fpLaw Rv h (xc m) σ (pc' m)))
    (fun m σ h => ⟨PMF.tvDist_nonneg _ _, PMF.tvDist_le_one _ _⟩)
    (fun m σ h h' hh => by
      unfold fpLaw
      simp_rw [fsD_congr (xc m) σ (pc m) hh, fsD_congr (xc m) σ (pc' m) hh])
    (p := min 1 (β + M.overrun.toReal + (SPBCS.keyCollision (t.size n) k).toReal))
    fun m σ f =>
      le_min ((Finset.expect_le_expect fun g _ => PMF.tvDist_le_one _ _).trans_eq
        (Fintype.expect_const _))
        ((expect_tvDist_fpLaw_le (xc m) σ Rv (pc m) (pc' m) f).trans (by linarith [hβ m]))
  rwa [hcard] at h

end Salt

/-! ### Unconditional witness indistinguishability -/

variable (M) in
/-- **A distinguisher of the witness-indistinguishability game**: a predicate of the whole oracle
and the `Q` proofs. -/
abbrev WIDistinguisher (Q : ℕ) : Type := (Query k kN kS L → Out k e) → (Fin Q → M.NIProof) → Prop

section Game

variable {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x}

variable (E Qs) {R : Type} [Fintype R] [Nonempty R] (prv : W → R → CausalProver P t X)
  {rel : Set (X × W)} {Q : ℕ} (A : M.WIAdversary rel Q)

/-- **The witness-indistinguishability experiment of the spBCS compiler** `D_b`
(`Base.wiGameWith` at the merge proof laws `proofLaw`). -/
noncomputable def wiGame (b : Bool) :
    PMF ((Query k kN kS L → Out k e) × (Fin Q → M.NIProof)) :=
  Base.wiGameWith (fun h x w => proofLaw E Qs h x (prv w)) A b

/-- **The advantage of a distinguisher** `D` against the spBCS compiler, given the whole oracle
and the proofs (`Base.wiAdvantageWith` at the merge proof laws `proofLaw`). -/
noncomputable def wiAdvantage (D : (Query k kN kS L → Out k e) → (Fin Q → M.NIProof) → Prop) : ℝ :=
  Base.wiAdvantageWith (fun h x w => proofLaw E Qs h x (prv w)) A D

end Game

/-- **Unconditional witness indistinguishability of the spBCS compiler** (CY24 Definition
33.1.1, p. 426, at query bound `t = ∞`, for `Q` adaptively chosen proof queries): for every
adversary `A` choosing, in each of `Q` rounds, a statement and two valid witnesses from its finite
choice set as a function of the whole oracle and the earlier proofs, and every distinguisher `D`
given the whole oracle and the proofs, the advantage of `D` between answering every proof query with
the first witness and answering with the second is at most `Q · wiError δ |choices|`.

Hypotheses: `Rv` (what the compiled proof writes and opens is determined by the composite view); `hz` (the views of
two witnesses of a statement are at average distance at most `2δ`, `Base.ObsClose`;
honest-verifier zero knowledge of the composite at error `δ` gives it,
`Base.obsClose_of_causalHVZK`). -/
theorem wiAdvantage_le {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (Rv : M.Reveal E Qs) {rel : Set (X × W)}
    {R : Type} [Fintype R] [Nonempty R] {prv : W → R → CausalProver P t X} {δ : ℝ≥0}
    (hz : ObsClose Rv rel prv δ) {Q : ℕ} (A : M.WIAdversary rel Q)
    (D : (Query k kN kS L → Out k e) → (Fin Q → M.NIProof) → Prop) :
    wiAdvantage E Qs prv A D ≤ Q * M.wiError δ A.choices.card := by
  have hlaw : ∀ h, ∀ c ∈ A.choices, proofLaw E Qs h c.stmt (prv c.wit₀) ≈[2 *
      (Fintype.card M.Pos * SPBCS.leafDist h) + fpDist Rv h c.stmt (prv c.wit₀) (prv c.wit₁)]
      proofLaw E Qs h c.stmt (prv c.wit₁) :=
    fun h c _ => close_proofLaw Rv h c.stmt (prv c.wit₀) (prv c.wit₁)
  have hF : ∀ hne : A.choices.Nonempty, 𝔼 h : Query k kN kS L → Out k e,
      A.choices.sup' hne (fun c => fpDist Rv h c.stmt (prv c.wit₀) (prv c.wit₁)) ≤
        min 1 (2 * δ + M.overrun.toReal + (SPBCS.keyCollision (t.size n) k).toReal) +
          SPBCS.saltTerm kS A.choices.card := fun hne => by
    have : Nonempty A.choices := hne.to_subtype
    have hbound := expect_sup'_fpDist_le Rv (fun m : A.choices => m.1.stmt)
      (fun m => prv m.1.wit₀) (fun m => prv m.1.wit₁) (β := 2 * δ) fun m =>
        hz m.1.stmt m.1.wit₀ m.1.wit₁ (A.admissible m.1 m.2).1 (A.admissible m.1 m.2).2
    rw [Fintype.card_coe] at hbound
    have hsup : ∀ h : Query k kN kS L → Out k e,
        A.choices.sup' hne (fun c => fpDist Rv h c.stmt (prv c.wit₀) (prv c.wit₁)) ≤
          Finset.univ.sup' Finset.univ_nonempty
            (fun m : A.choices => fpDist Rv h m.1.stmt (prv m.1.wit₀) (prv m.1.wit₁)) :=
      fun h => Finset.sup'_le _ _ fun c hc => by
        have := Finset.le_sup' (fun m : A.choices => fpDist Rv h m.1.stmt (prv m.1.wit₀)
          (prv m.1.wit₁)) (Finset.mem_univ ⟨c, hc⟩)
        exact this
    exact (Finset.expect_le_expect fun h _ => hsup h).trans hbound
  exact Base.wiAdvantageWith_le_of (law := fun h x w => proofLaw E Qs h x (prv w)) A
    (fun h c => fpDist Rv h c.stmt (prv c.wit₀) (prv c.wit₁))
    (fun h c => fpDist_nonneg Rv h c.stmt _ _) hlaw hF D

variable (M) in
/-- **Unconditional witness indistinguishability of the spBCS compiler** (CY24 Definition 33.1.1,
p. 426, at unbounded queries) with `Q` proof queries and at most `C` choices, at advantage `ε`: against
every adversary making `Q` proof queries with at most `C` choices of a statement and two
witnesses of `rel`, each chosen as a function of the whole oracle and the earlier proofs, every
distinguisher of the oracle and the proofs has advantage at most `ε` against the honest prover
family `prv` (`wiAdvantage`). -/
def WitnessIndistinguishable (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    (Qs : ∀ x, M.IOPQueries V x) (rel : Set (X × W)) {R : Type} [Fintype R] [Nonempty R]
    (prv : W → R → CausalProver P t X) (Q C : ℕ) (ε : ℝ) : Prop :=
  ∀ A : M.WIAdversary rel Q, A.choices.card ≤ C →
    ∀ D : (Query k kN kS L → Out k e) → (Fin Q → M.NIProof) → Prop, wiAdvantage E Qs prv A D ≤ ε

/-- **Unconditional witness indistinguishability of the spBCS compiler** at `Q · wiError δ C`
(`wiAdvantage_le`, `Base.wiError_mono`). -/
theorem witnessIndistinguishable {E : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (Rv : M.Reveal E Qs) {rel : Set (X × W)} {R : Type} [Fintype R] [Nonempty R]
    {prv : W → R → CausalProver P t X} {δ : ℝ≥0} (hz : ObsClose Rv rel prv δ) (Q C : ℕ) :
    M.WitnessIndistinguishable E Qs rel prv Q C (Q * M.wiError δ C) := fun A hA D =>
  (wiAdvantage_le Rv hz A D).trans
    (mul_le_mul_of_nonneg_left (Base.wiError_mono δ hA) (Nat.cast_nonneg _))

end

end GordieHowe.SPBCS
