-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Salt
public import GordieHowe.SPBCS.Complete
public import GordieHowe.SPBCS.FullPast.ZeroKnowledge
public import GordieHowe.Model.QROM.SaltedZKProofQuery

@[expose] public section

/-!
# Zero knowledge of the spBCS compiler

Everlasting zero knowledge of the compiler on a series–parallel term with merges
(`GordieHowe/SPBCS/Basic.lean`, paper `thm:bcs-zk`) in the quantum random-oracle model, from
honest-verifier zero knowledge of the composite's observation (`GordieHowe.IOP.CausalHVZK`, CY24
Definition 23.1.8). The argument is the one for the compiler over the term
(`GordieHowe/SPBCS/FullPast/ZeroKnowledge.lean`), whose built chains, proofs and leaf hiding it reuses; what
changes is the chain inputs:

* the slice of the salt `σ` (`saltOfBits`): the `transcript` inputs whose content carries `σ`,
  and the `xof` inputs of `σ`. Every query of the honest prover and every point the simulator
  reads lies in it or is salt-free;
* the built chains (`buildChains`) read no key; the final digests of the built chains are the
  solution of their equation (`buildFinals`, `GordieHowe.SPBCS.finalsWith`), and a challenge's key is
  the digest of its chain input on the built chains and final digests (`buildKey`);
* the honest proof (`honestProof`) is the built proof at the honest streams `honestStreams`,
  the solution of `ρ c = h (xof (key of c at ρ) σ)`: a key reads only the streams of earlier
  challenges in global round order (`buildKey_honest_congr`), so iterating the equation once per
  round reaches its only solution (`honestStreams_eq`, `eq_honestStreams`);
* lazy sampling: the final digests are answers of the slice at encodings of well-formed final
  contents, a set fixed in advance that contains no chain input of a challenge (a chain input is a
  round content), so given the slice there the keys are digests of the slice at distinct further
  inputs, and two keys collide with probability at most `keyCollision (t.size n) k`
  (`prob_lazyKey_not_injective_le`);
* the simulator (`niJointSimulator`) runs a joint simulator of the composite's observation, draws
  each challenge's stream by preimage, builds every leaf's chain, reads the final digests and the
  keys from the oracle and programs each challenge's stream at the `xof` input of its key and the
  salt.

The bound per proof query is the compiler's `oneProofBound δ`: `keyCollision (t.size n) k + overrun +
δ + |Pos| · leafMax`; the error of the game is the compiler's `zkError δ`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

/-! ### Iterates of a causal map -/

section Iterate

variable {C β : Type*} (F : (C → β) → C → β) (rk : C → ℕ)

/-- **A map of functions on `C` is causal for the rank `rk`**: its value at `c` reads its argument
only at points of smaller rank. -/
def RankCausal : Prop :=
  ∀ ρ ρ' c, (∀ j, rk j < rk c → ρ j = ρ' j) → F ρ c = F ρ' c

variable {F rk}

/-- **The iterates of a causal map agree at a point after more steps than its rank.** -/
theorem RankCausal.iterate_apply_eq (hF : RankCausal F rk) (ρ₀ : C → β) (c : C) :
    ∀ m m', rk c < m → rk c < m' → F^[m] ρ₀ c = F^[m'] ρ₀ c := by
  induction hc : rk c using Nat.strong_induction_on generalizing c with
  | _ r ih =>
    intro m m' hm hm'
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', m' = a' + 1 := ⟨m' - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hF _ _ c fun j hj => ih (rk j) (by omega) j rfl a a' (by omega) (by omega)

/-- **A causal map's iterate past every rank is a fixed point.** -/
theorem RankCausal.iterate_fixed (hF : RankCausal F rk) (ρ₀ : C → β) {N : ℕ}
    (hN : ∀ c, rk c < N) : F^[N] ρ₀ = F (F^[N] ρ₀) := by
  funext c
  rw [← Function.iterate_succ_apply' F N ρ₀]
  exact hF.iterate_apply_eq ρ₀ c N (N + 1) (hN c) (by have := hN c; omega)

/-- **A causal map has only one fixed point**: its iterate past every rank. -/
theorem RankCausal.eq_iterate (hF : RankCausal F rk) (ρ₀ : C → β) {N : ℕ} (hN : ∀ c, rk c < N)
    {ρ : C → β} (hρ : ∀ c, ρ c = F ρ c) : ρ = F^[N] ρ₀ := by
  funext c
  induction hc : rk c using Nat.strong_induction_on generalizing c with
  | _ r ih =>
    rw [hρ c, congrFun (hF.iterate_fixed ρ₀ hN) c]
    exact hF _ _ c fun j hj => ih (rk j) (by omega) j rfl

end Iterate

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

/-! ### Well-formed chain inputs -/

section WF

variable {M}

/-- **The chain input of a round on full well-formed chains is well formed.** -/
theorem wf_roundContent_of {ss : SaltedStatement kS X} {chs : M.Chains} (fs : Mg.Site → Digest k)
    (hwf : ∀ q, chainWF (P q.label) (chs q)) (hlen : ∀ q, (chs q).length = n q.label)
    {p : t.Leaf} {l : M.Items p} (hl : chainWF (P p.label) l) (hll : l.length < n p.label) :
    (roundContent ss chs fs p l).WF n fun j => chainWF (P j) :=
  .round (Content.viewWF_view _ (fun q _ => hwf q) (fun q _ => hlen q) fs) hl hll

/-- **The final input of a branch on full well-formed chains is well formed.** -/
theorem wf_finalContent_of {ss : SaltedStatement kS X} {chs : M.Chains} (fs : Mg.Site → Digest k)
    (hwf : ∀ q, chainWF (P q.label) (chs q)) (hlen : ∀ q, (chs q).length = n q.label)
    (s : Mg.Site) : (finalContent ss chs fs s).WF n fun j => chainWF (P j) :=
  .final (Content.viewWF_view _ (fun q _ => hwf q) (fun q _ => hlen q) fs)

/-- **The final digests read the oracle only at final inputs.** -/
theorem finalsWith_congr_oracle {h₁ h₂ : Query k kN kS L → Out k e} {ss : SaltedStatement kS X}
    {chs : M.Chains}
    (htr : ∀ fs s, h₁ (.transcript (M.senc.encode (finalContent ss chs fs s))) =
      h₂ (.transcript (M.senc.encode (finalContent ss chs fs s)))) :
    M.finalsWith h₁ ss chs = M.finalsWith h₂ ss chs :=
  (eq_finalsWith fun s =>
    (finalsWith_eq (h := h₂) chs s).trans (congrArg Out.digest (htr _ s).symm)).symm

end WF

/-! ### The keys of the built chains -/

section Build

variable (h : Query k kN kS L → Out k e) (ss : SaltedStatement kS X)
  (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)

/-- **The built chains** of all leaves (`FullPast.buildLeaf`, full length). -/
def buildChains : M.Chains := fun q => M.toFullPast.buildLeaf h ρ wr ld q (n q.label)

/-- **The final digests of the built chains**: the solution of their equation. -/
def buildFinals : Mg.Site → Digest k := M.finalsWith h ss (M.buildChains h ρ wr ld)

/-- **The key of challenge `c` on the built chains**: the digest of its chain input, with the
built chains and the built final digests. -/
def buildKey (c : ChIdx P t) : Digest k :=
  M.key h ss (M.buildChains h ρ wr ld) (M.buildFinals h ss ρ wr ld) c.leaf
    (M.toFullPast.buildLeaf h ρ wr ld c.leaf c.idx.1)

/-- **The built assignment list**: each challenge's stream at the `xof` input of its key on the
built chains and the salt, in global round order. -/
def buildAssign : List (Assignment (Query k kN kS L) (Out k e)) :=
  (Base.chList P t).map fun c => ⟨.xof (M.buildKey h ss ρ wr ld c) ss.salt, ρ c⟩

theorem chainWF_buildChains (q : t.Leaf) : chainWF (P q.label) (M.buildChains h ρ wr ld q) :=
  M.toFullPast.chainWF_buildLeaf h ρ wr ld q le_rfl

theorem length_buildChains (q : t.Leaf) : (M.buildChains h ρ wr ld q).length = n q.label :=
  M.toFullPast.length_buildLeaf h ρ wr ld q _

/-- **The built chains have a write at every prover round.** -/
theorem writesAll_buildChains : M.WritesAll (M.buildChains h ρ wr ld) := by
  intro p i
  rw [buildChains, M.toFullPast.buildLeaf_getElem? h ρ wr ld p _ i.1.1 i.1.2]
  unfold FullPast.buildItem
  rw [dite_eq_left i.1.2, dite_eq_left i.2]
  exact ⟨_, rfl⟩

/-- **The chain input of a challenge on the built chains is well formed.** -/
theorem wf_buildRound (fs : Mg.Site → Digest k) (c : ChIdx P t) :
    (roundContent ss (M.buildChains h ρ wr ld) fs c.leaf (M.toFullPast.buildLeaf h ρ wr ld c.leaf c.idx.1)).WF n
      fun j => chainWF (P j) :=
  wf_roundContent_of fs (M.chainWF_buildChains h ρ wr ld) (M.length_buildChains h ρ wr ld)
    (M.toFullPast.chainWF_buildLeaf h ρ wr ld _ c.idx.1.2.le) (by rw [FullPast.length_buildLeaf]; exact c.idx.1.2)

/-- **A final input on the built chains is well formed.** -/
theorem wf_buildFinal (fs : Mg.Site → Digest k) (s : Mg.Site) :
    (finalContent ss (M.buildChains h ρ wr ld) fs s).WF n fun j => chainWF (P j) :=
  wf_finalContent_of fs (M.chainWF_buildChains h ρ wr ld) (M.length_buildChains h ρ wr ld) s

variable {h₁ h₂ : Query k kN kS L → Out k e}

/-- The built chains read the oracle only at `leaf` and `node` queries. -/
theorem buildChains_congr (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b))
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r)) :
    M.buildChains h₁ ρ wr ld = M.buildChains h₂ ρ wr ld :=
  funext fun q => M.toFullPast.buildLeaf_congr hleaf hnode ρ wr ld q _

/-- **A built key reads the oracle only at `leaf` and `node` queries and at `transcript` queries
of its salt.** -/
theorem buildKey_congr (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b))
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r))
    (htr : ∀ b, M.querySalt (.transcript b) = some ss.salt → h₁ (.transcript b) = h₂ (.transcript b))
    (c : ChIdx P t) :
    M.buildKey h₁ ss ρ wr ld c = M.buildKey h₂ ss ρ wr ld c := by
  have hch := M.buildChains_congr ρ wr ld hleaf hnode
  have hfin : M.buildFinals h₁ ss ρ wr ld = M.buildFinals h₂ ss ρ wr ld := by
    unfold buildFinals
    rw [hch]
    exact finalsWith_congr_oracle fun fs s => htr _ (by
      rw [M.querySalt_transcript_encode (M.wf_buildFinal h₂ ss ρ wr ld fs s)]
      rfl)
  unfold buildKey key
  rw [hch, hfin, M.toFullPast.buildLeaf_congr hleaf hnode, htr _ (by
    rw [M.querySalt_transcript_encode (M.wf_buildRound h₂ ss ρ wr ld _ c)]
    rfl)]

end Build

/-! ### The honest proof -/

section Honest

variable [∀ j i, Nonempty ((P j).Challenge i)]
variable {M} (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS) (h : Query k kN kS L → Out k e)

/-- **A built key of the honest prover is causal in the streams**: the key of challenge `c` reads
only the streams of the challenges before it in global round order. -/
theorem buildKey_honest_congr (ss : SaltedStatement kS X) {ρ ρ' : ChIdx P t → Out k e}
    (c : ChIdx P t) (hρ : ∀ j : ChIdx P t, FullPast.gIdx j < FullPast.gIdx c → ρ j = ρ' j) :
    M.buildKey h ss ρ (Base.honestWrite' E prv x ρ)
        (FullPast.honestDigest E prv x ν h ρ) c =
      M.buildKey h ss ρ' (Base.honestWrite' E prv x ρ')
        (FullPast.honestDigest E prv x ν h ρ') c := by
  have hbefore : ∀ q : t.Leaf, q.Before c.leaf →
      M.buildChains h ρ (Base.honestWrite' E prv x ρ)
          (FullPast.honestDigest E prv x ν h ρ) q =
        M.buildChains h ρ' (Base.honestWrite' E prv x ρ')
          (FullPast.honestDigest E prv x ν h ρ') q := fun q hq =>
    FullPast.buildLeaf_honest_congr E prv x ν h q _ fun j hj => hρ j (by
      have := Leaf.Before.off_add_le n hq
      unfold FullPast.gIdx at hj ⊢
      omega)
  unfold buildKey
  rw [FullPast.buildLeaf_honest_congr E prv x ν h c.leaf c.idx.1 fun j hj => hρ j hj]
  refine congrFun (key_congr (fun q hq => hbefore q hq.1) fun s hs => ?_) _
  exact finalsWith_congr_of_hides hbefore hs

/-- **The key equation of the honest streams**: the stream of challenge `c` is the oracle at the
`xof` input of its built key at the streams `ρ` and the salt. -/
noncomputable def keyStep (ρ : ChIdx P t → Out k e) : ChIdx P t → Out k e := fun c =>
  h (.xof (M.buildKey h ⟨σ, x⟩ ρ (Base.honestWrite' E prv x ρ)
    (FullPast.honestDigest E prv x ν h ρ) c) σ)

theorem rankCausal_keyStep : RankCausal (keyStep E prv x ν σ h) FullPast.gIdx :=
  fun ρ ρ' c hρ => by
    unfold keyStep
    rw [buildKey_honest_congr E prv x ν h _ c hρ]

/-- **The honest streams**: the solution of the key equation, the equation iterated once per
round. -/
noncomputable def honestStreams : ChIdx P t → Out k e :=
  (keyStep E prv x ν σ h)^[t.size n] fun _ => SPBCS.defaultOut

/-- **The honest stream of challenge `c` is the oracle at the `xof` input of its built key.** -/
theorem honestStreams_eq (c : ChIdx P t) :
    honestStreams E prv x ν σ h c = keyStep E prv x ν σ h (honestStreams E prv x ν σ h) c :=
  congrFun ((rankCausal_keyStep E prv x ν σ h).iterate_fixed _ FullPast.gIdx_lt_size) c

/-- **The honest streams are the only solution of the key equation.** -/
theorem eq_honestStreams {ρ : ChIdx P t → Out k e} (hρ : ∀ c, ρ c = keyStep E prv x ν σ h ρ c) :
    ρ = honestStreams E prv x ν σ h :=
  (rankCausal_keyStep E prv x ν σ h).eq_iterate _ FullPast.gIdx_lt_size hρ

/-- **The honest chains**: the built chains at the honest streams, writes and leaf digests. -/
noncomputable def honestBuiltChains : M.Chains :=
  M.buildChains h (honestStreams E prv x ν σ h)
    (Base.honestWrite' E prv x (honestStreams E prv x ν σ h))
    (FullPast.honestDigest E prv x ν h (honestStreams E prv x ν σ h))

/-- The honest queried positions: the query phase's positions on the honest chains at the
challenges read from the honest streams. -/
noncomputable def honestBuiltPos {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x) : List M.Pos :=
  Q.pos (honestBuiltChains E prv x ν σ h) (M.chOfStreams (honestStreams E prv x ν σ h))

/-- **The honest proof of the spBCS compiler** (paper `prot:generalized-bcs`): the built
proof at the honest streams, writes and leaf digests, with the honest leaves opened at the queried
positions. -/
noncomputable def honestProof {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x) : M.NIProof :=
  M.toFullPast.buildProof h σ (Base.honestWrite' E prv x (honestStreams E prv x ν σ h))
    (FullPast.honestDigest E prv x ν h (honestStreams E prv x ν σ h))
    (Base.honestOpened E prv x ν (honestStreams E prv x ν σ h) (honestBuiltPos E prv x ν σ h Q))
    (honestBuiltPos E prv x ν σ h Q)

variable {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x}

/-- **The honest proof at the positions of the view law.** -/
theorem honestProof_eq_buildProof (VE : M.ViewEncoder E Qs) :
    honestProof E prv x ν σ h (Qs x) =
      M.toFullPast.buildProof h σ (Base.honestWrite' E prv x (honestStreams E prv x ν σ h))
        (FullPast.honestDigest E prv x ν h (honestStreams E prv x ν σ h))
        (Base.honestOpened E prv x ν (honestStreams E prv x ν σ h)
          (VE.posC x (M.chOfStreams (honestStreams E prv x ν σ h))))
        (VE.posC x (M.chOfStreams (honestStreams E prv x ν σ h))) := by
  rw [honestProof, honestBuiltPos, honestBuiltChains, VE.pos_eq x _ _ (M.writesAll_buildChains _ _ _ _)]

/-! #### Locality in the salt -/

variable {h} in
/-- **The key equation reads the oracle only on the salt's slice and on salt-free queries.** -/
theorem keyStep_congr_slice {h' : Query k kN kS L → Out k e}
    (hh : AgreeOnSlice M.querySalt σ h h') : keyStep E prv x ν σ h = keyStep E prv x ν σ h' := by
  have hleaf : ∀ a b, h (.leaf a b) = h' (.leaf a b) := fun a b => hh _ (Or.inl rfl)
  have hnode : ∀ l r, h (.node l r) = h' (.node l r) := fun l r => hh _ (Or.inl rfl)
  have hd : ∀ ρ, FullPast.honestDigest E prv x ν h ρ = FullPast.honestDigest E prv x ν h' ρ :=
    fun ρ => by
      funext q
      simp only [FullPast.honestDigest, MerkleTree.leafDigest, hleaf]
  funext ρ c
  simp only [keyStep, hd]
  rw [M.buildKey_congr _ _ _ _ hleaf hnode (fun b hb => hh _ (Or.inr hb)) c]
  exact hh _ (Or.inr rfl)

variable {h} in
/-- **The honest proof reads the oracle only on its salt's slice and on salt-free queries.** -/
theorem honestProof_congr_salt {h' : Query k kN kS L → Out k e} (Q : M.IOPQueries V x)
    (hh : AgreeOnSlice M.querySalt σ h h') :
    honestProof E prv x ν σ h Q = honestProof E prv x ν σ h' Q := by
  have hleaf : ∀ a b, h (.leaf a b) = h' (.leaf a b) := fun a b => hh _ (Or.inl rfl)
  have hnode : ∀ l r, h (.node l r) = h' (.node l r) := fun l r => hh _ (Or.inl rfl)
  have hd : ∀ ρ, FullPast.honestDigest E prv x ν h ρ = FullPast.honestDigest E prv x ν h' ρ :=
    fun ρ => by
      funext q
      simp only [FullPast.honestDigest, MerkleTree.leafDigest, hleaf]
  have hs : honestStreams E prv x ν σ h = honestStreams E prv x ν σ h' := by
    unfold honestStreams
    rw [keyStep_congr_slice E prv x ν σ hh]
  have hch : ∀ ρ wr ld, M.buildChains h ρ wr ld = M.buildChains h' ρ wr ld := fun ρ wr ld =>
    M.buildChains_congr ρ wr ld hleaf hnode
  simp only [honestProof, honestBuiltPos, honestBuiltChains, hs, hd, hch, M.toFullPast.buildProof_congr hleaf hnode]

end Honest

/-! ### The honest spBCS prover is the built proof

The honest prover `prove` (`GordieHowe/SPBCS/Complete.lean`), whose oracle queries form one adaptive
strategy over the query slots, is the built honest proof `honestProof`: the answers at the
stream points of its run solve the key equation (`runStreams_eq`), so they are the honest
streams (`runStreams_eq_honestStreams`). -/

section Bridge

variable [∀ j i, Nonempty ((P j).Challenge i)] {M} (E : (j : ι) → (M.comp j).Encoder)
  (prv : CausalProver P t X) (x : X) (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS)
  (h : Query k kN kS L → Out k e)

/-- **The streams of the honest prover's run**: the answers at the stream points of its
challenges. -/
noncomputable def runStreams : ChIdx P t → Out k e := fun c =>
  ansAt (answers prv x σ E ν h) (posX (Mg := Mg) c)

theorem chOfW_answers :
    M.chOfW (answers prv x σ E ν h) = M.chOfStreams (runStreams E prv x ν σ h) := rfl

/-- **The honest prover's chains are the built chains** at the streams of its run. -/
theorem chainW_honest_eq (p : t.Leaf) : ∀ r,
    chainW prv x (Base.honestWrite E ν h) (answers prv x σ E ν h) p r =
      M.toFullPast.buildLeaf h (runStreams E prv x ν σ h)
        (Base.honestWrite' E prv x (runStreams E prv x ν σ h))
        (FullPast.honestDigest E prv x ν h (runStreams E prv x ν σ h)) p r
  | 0 => rfl
  | r + 1 => by
    rw [chainW, FullPast.buildLeaf, chainW_honest_eq p r]
    congr 2
    unfold itemW FullPast.buildItem
    split_ifs with hr hd
    · rw [chOfW_answers]
      exact congrArg (fun w => (Item.write ⟨⟨⟨r, hr⟩, hd⟩, w⟩ : Item k (M.comp p.label).W))
        (FullPast.honestWrite_eq E prv x ν h _ p ⟨⟨r, hr⟩, hd⟩)
    · rfl
    · rfl

theorem chsW_honest_eq :
    chsW prv x (Base.honestWrite E ν h) (answers prv x σ E ν h) =
      M.buildChains h (runStreams E prv x ν σ h)
        (Base.honestWrite' E prv x (runStreams E prv x ν σ h))
        (FullPast.honestDigest E prv x ν h (runStreams E prv x ν σ h)) :=
  funext fun p => chainW_honest_eq E prv x ν σ h p _

/-- **The streams of the honest prover's run solve the key equation.** -/
theorem runStreams_eq (c : ChIdx P t) :
    runStreams E prv x ν σ h c = keyStep E prv x ν σ h (runStreams E prv x ν σ h) c := by
  have hfs := finalsWith_chsW (M := M) prv x σ (Base.honestWrite E ν) h
  unfold runStreams posX
  rw [answers, ansAt_answersW prv x σ _ h (.xof c.leaf c.idx.1)]
  simp only [queryW]
  rw [ansAt_answersW prv x σ _ h (.key c.leaf c.idx.1)]
  simp only [queryW]
  rw [← hfs, ← answers, chsW_honest_eq, chainW_honest_eq]
  rfl

/-- **The streams of the honest prover's run are the honest streams.** -/
theorem runStreams_eq_honestStreams :
    runStreams E prv x ν σ h = honestStreams E prv x ν σ h :=
  eq_honestStreams E prv x ν σ h (runStreams_eq E prv x ν σ h)

/-- **The honest spBCS prover is the built honest proof** (`honestProof`). -/
theorem prove_eq_honestProof {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x) :
    prove prv x σ E ν h Q = honestProof E prv x ν σ h Q := by
  have hρ := runStreams_eq_honestStreams E prv x ν σ h
  have hch : honestCh prv x σ E ν h = M.chOfStreams (honestStreams E prv x ν σ h) := by
    rw [← hρ]
    rfl
  have hchains : honestChains prv x σ E ν h = honestBuiltChains E prv x ν σ h := by
    unfold honestChains honestBuiltChains
    rw [chsW_honest_eq, hρ]
  have hpos : honestPos prv x σ E ν h Q = honestBuiltPos E prv x ν σ h Q := by
    unfold honestPos honestBuiltPos
    rw [hchains, hch]
  have hleaves : honestLeaves prv x σ E ν h Q =
      Base.honestOpened E prv x ν (honestStreams E prv x ν σ h)
        (honestBuiltPos E prv x ν σ h Q) := by
    rw [honestLeaves, hpos, Base.honestOpened, hch]
    exact List.map_congr_left fun q _ => Base.leafFn_val E ν _ _ _ _ _
  simp only [prove, honestProof, FullPast.buildProof, hleaves, hpos]
  congr 1
  · funext p i
    rw [hch, FullPast.honestWrite_eq E prv x ν h]
  · funext τ
    simp only [MerkleFormat.path, MerkleTree.treeDigest, hch]
    rw [FullPast.root_leafFn E prv x ν h]

end Bridge

/-! ### The prover of the game -/

section Prover

variable [∀ j i, Nonempty ((P j).Challenge i)] {M}

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- A built proof whose opened leaves number at most `B` is bounded by `B` when every tree has at
most `B` leaves. -/
theorem bounded_buildProof (h : Query k kN kS L → Out k e) (σ : FiatShamirSalt kS) (wr : M.RootWriteFn)
    (ld : M.Pos → Digest k) (ops : List (MerkleLeaf kN L)) (ps : List M.Pos) {B : ℕ}
    (hops : ops.length ≤ B) (hleaves : ∀ (p : t.Leaf) i τ, (M.comp p.label).nLeaves i τ ≤ B) :
    M.Bounded B (M.toFullPast.buildProof h σ wr ld ops ps) := by
  refine ⟨hops, fun τ => ?_⟩
  simp only [FullPast.buildProof, List.length_map]
  refine M.opening.length_sibs_le (fun j hj => ?_) ?_ (hleaves _ _ _)
  · obtain ⟨⟨j', a⟩, hm, rfl⟩ := List.mem_map.1 hj
    exact M.lt_of_mem_openedIn hm
  · rw [List.length_map]
    exact (M.length_openedIn_le τ ps ops).trans hops

theorem bounded_honestProof (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
    (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS) {V : X → FullTr P t → Bool}
    (Q : M.IOPQueries V x) (h : Query k kN kS L → Out k e) {B : ℕ}
    (hpos : ∀ chs ch, (Q.pos chs ch).length ≤ B)
    (hleaves : ∀ (p : t.Leaf) i τ, (M.comp p.label).nLeaves i τ ≤ B) :
    M.Bounded B (honestProof E prv x ν σ h Q) :=
  bounded_buildProof _ _ _ _ _ _ (by rw [Base.honestOpened, List.length_map]; exact hpos _ _)
    hleaves

variable (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)] {Wit R : Type} [Fintype R]
  [Nonempty R] (honest : Wit → R → CausalProver P t X)

variable (M) in
/-- **The prover of the zero-knowledge games, as a function of the quantum oracle**: `prove` at the
causal prover `honest w ρ`, the Merkle salts `ν` and the salt `σ`, against the oracle seen through
`H`, serialized into the response register; the coins are uniform. It is the classical semantics of
the honest prover `niProver` serialized and run through `queryEncoding` (`toFn_encode_niProver`);
the game lemmas of this file are stated for it. -/
noncomputable def niProverZKM (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    (Qs : ∀ x, M.IOPQueries V x) :
    GordieHowe.NARG.ProverFn (Bits (queryBits k kN kS L)) (XOut k e) X Wit (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) where
  prove H x w a :=
    FullPast.Internal.encodeTotal M.toFullPast B (prove (honest w a.coins.iop) x a.salt E a.coins.merkleSalts (chainOracle H) (Qs x))
  coins := PMF.uniformOfFintype _

end Prover

/-! ### One proof on a fresh slice -/

section OneProof

variable [∀ j i, Nonempty ((P j).Challenge i)]
variable {M} {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) (B : ℕ)
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  (H : Bits (queryBits k kN kS L) → XOut k e) (x : X)

/-- The reply for a built proof on `H` with the slice of `σ` answered by `F`: the built proof
(bounded) and that oracle reprogrammed by the built assignment list. -/
noncomputable def outB (σ : FiatShamirSalt kS) (F : Bits (queryBits k kN kS L) → XOut k e)
    (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)
    (ops : List (MerkleLeaf kN L)) (ps : List M.Pos) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  let H' := replaceSlice M.saltOfBits σ H F
  ⟨some (FullPast.Internal.encodeTotal M.toFullPast B (M.toFullPast.buildProof (chainOracle H') σ wr ld ops ps)),
    H'.reprogram ((M.buildAssign (chainOracle H') ⟨σ, x⟩ ρ wr ld).map fun qa =>
      ⟨Query.toBits qa.input, (outEquiv k e).symm qa.output⟩)⟩

/-- The honest reply on the slice `F` of `σ`. -/
noncomputable def realOut (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) (F : Bits (queryBits k kN kS L) → XOut k e) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  let H' := replaceSlice M.saltOfBits σ H F
  ⟨some (FullPast.Internal.encodeTotal M.toFullPast B (prove prv₀ x σ E ν (chainOracle H') (Qs x))), H'⟩

/-- The lazily sampled reply: the honest proof built from the streams of the draw `d`, and the
slice of `d` reprogrammed at the keys with those streams. -/
noncomputable def lazyOut (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) (d : FullPast.StreamDraw k kN kS L e P t) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  outB B H x σ d.slice d.streams (Base.honestWrite' E prv₀ x d.streams)
    (FullPast.honestDigest E prv₀ x ν (chainOracle H) d.streams)
    (Base.honestOpened E prv₀ x ν d.streams (VE.posC x (M.chOfStreams d.streams)))
    (VE.posC x (M.chOfStreams d.streams))

variable {R : Type} [Fintype R] [Nonempty R] (prv : R → CausalProver P t X)

/-- `innerR`: the honest proof on `H` with the slice of `σ` answered by a uniform `F`. -/
noncomputable def innerR (σ : FiatShamirSalt kS) :
    PMF (EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e)) :=
  (PMF.uniformOfFintype (FreshSlice (Bits (queryBits k kN kS L)) (XOut k e) (M.ProverCoins R))).map
    fun a => realOut (E := E) (Qs := Qs) B H x σ (prv a.coins.iop) a.coins.merkleSalts a.slice

/-- `innerL`: the honest proof built from fresh uniform streams. -/
noncomputable def innerL (σ : FiatShamirSalt kS) :
    PMF (EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e)) :=
  (PMF.uniformOfFintype (M.ProverCoins R × FullPast.StreamDraw k kN kS L e P t)).map
    fun a => lazyOut VE B H x σ (prv a.1.iop) a.1.merkleSalts a.2

/-- The reply of `innerD` at a draw. -/
noncomputable def mixOut (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (d : FullPast.StreamDraw k kN kS L e P t) (z : M.Pos → MerkleSalt kN × Digest k) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  outB B H x σ d.slice d.streams (Base.honestWrite' E prv₀ x d.streams)
    (FullPast.mixDigest VE H x prv₀ (fun q => (z q).1) (fun q => (z q).2) d.streams)
    (Base.honestOpened E prv₀ x (fun q => (z q).1) d.streams
      (VE.posC x (M.chOfStreams d.streams)))
    (VE.posC x (M.chOfStreams d.streams))

/-- `innerD`: as `innerL`, with the digests of the unopened leaves uniform. -/
noncomputable def innerD (σ : FiatShamirSalt kS) :
    PMF (EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e)) :=
  (PMF.uniformOfFintype (M.toFullPast.LeafDraw R)).map fun a => mixOut VE B H x σ (prv a.iop) a.draw a.leaves

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
open Classical in
/-- The real slice law is the average over the salt of `innerR`. -/
theorem realSlice_eq_bind {Wit : Type} (honest : Wit → R → CausalProver P t X) (w : Wit) :
    realSlice M.saltOfBits (M.niProverZKM B honest E Qs) H x w =
      (PMF.uniformOfFintype (FiatShamirSalt kS)).bind fun σ =>
        innerR (E := E) (Qs := Qs) B H x (honest w) σ := by
  rw [realSlice, FreshSlice.map_uniformOfFintype_salted]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem leafDigest_replaceSlice (σ : FiatShamirSalt kS) (F : Bits (queryBits k kN kS L) → XOut k e)
    (a : MerkleLeaf kN L) :
    MerkleTree.leafDigest (chainOracle (replaceSlice M.saltOfBits σ H F)) a =
      MerkleTree.leafDigest (chainOracle H) a := by
  simp only [MerkleTree.leafDigest, chainOracle, replaceSlice, M.saltOfBits_toBits]
  rfl

/-- The reply built from an observation `o` at the challenges `ch`: its writes and opened columns
read off it, honest leaf digests at the opened positions and the drawn digests elsewhere; the
`unparsed` response if no writes can be read off `o`. -/
noncomputable def outViewAt (σ : FiatShamirSalt kS) (F : Bits (queryBits k kN kS L) → XOut k e)
    (ch : Chs P t) (ρ : ChIdx P t → Out k e) (ν : M.Pos → MerkleSalt kN)
    (d : M.Pos → Digest k) (o : CausalView VE.MV) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  (VE.writesOf x ch o).elim
    ⟨some none, (replaceSlice M.saltOfBits σ H F).reprogram []⟩ fun wr =>
    outB B H x σ F ρ wr
      (fun q => if q ∈ VE.posC x ch then
        MerkleTree.leafDigest (chainOracle H) ⟨ν q, VE.colOf x ch o q⟩ else d q)
      ((VE.posC x ch).map fun q => ⟨ν q, VE.colOf x ch o q⟩)
      (VE.posC x ch)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem innerD_out_eq (prv₀ : CausalProver P t X) (σ : FiatShamirSalt kS)
    (F : Bits (queryBits k kN kS L) → XOut k e) (ρ : ChIdx P t → Out k e)
    (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k) :
    outB B H x σ F ρ (Base.honestWrite' E prv₀ x ρ) (FullPast.mixDigest VE H x prv₀ ν d ρ)
      (Base.honestOpened E prv₀ x ν ρ (VE.posC x (M.chOfStreams ρ)))
      (VE.posC x (M.chOfStreams ρ)) =
      outViewAt VE B H x σ F (M.chOfStreams ρ) ρ ν d
        (VE.MV.view (prv₀.run x (M.chOfStreams ρ))) := by
  set ch := M.chOfStreams ρ
  set tr := prv₀.run x ch
  obtain ⟨chs, hl⟩ : ∃ chs : (p : t.Leaf) → M.Items p, (Qs x).pos chs ch = VE.posC x ch :=
    ⟨_, VE.pos_eq x _ ch
      (FullPast.writesAll_honestChainsFullPast E prv₀ x ν (fun _ => 0) (chainOracle H))⟩
  have hcol : ∀ q ∈ VE.posC x ch, VE.colOf x ch (VE.MV.view tr) q =
      (E q.leaf.label).cols q.pos.msg (tr q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf := fun q hq =>
    VE.colOf_obs x chs ch tr (CausalProver.challenges_run prv₀ x ch) q (hl ▸ hq)
  have hld : FullPast.mixDigest VE H x prv₀ ν d ρ = fun q => if q ∈ VE.posC x ch then
      MerkleTree.leafDigest (chainOracle H) ⟨ν q, VE.colOf x ch (VE.MV.view tr) q⟩ else d q := by
    funext q
    simp only [FullPast.mixDigest, FullPast.honestDigest]
    split_ifs with hq
    · rw [hcol q hq]
    · rfl
  have hops : Base.honestOpened E prv₀ x ν ρ (VE.posC x ch) =
      (VE.posC x ch).map fun q => ⟨ν q, VE.colOf x ch (VE.MV.view tr) q⟩ :=
    List.map_congr_left fun q hq => by rw [hcol q hq]
  rw [outViewAt, VE.writesOf_obs, Option.elim_some, hld, hops]
  rfl

/-- The slice oracle glued from its part off the `xof` inputs of `σ` and its `xof` part. -/
noncomputable def sliceGlue (σ : FiatShamirSalt kS)
    (Fo : {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} → XOut k e)
    (FX : Digest k → XOut k e) : Bits (queryBits k kN kS L) → XOut k e :=
  replaceSlice M.saltOfBits σ H ((splitAlong (SPBCS.xofEmb σ)).symm (Fo, FX))

section Lazy

variable (σ : FiatShamirSalt kS)
  (Fo : {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} → XOut k e)

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem sliceGlue_leaf (FX : Digest k → XOut k e) (a : MerkleSalt kN) (c : Bytes L) :
    chainOracle (sliceGlue (M := M) H σ Fo FX) (.leaf a c) = chainOracle H (.leaf a c) := by
  simp only [chainOracle, sliceGlue, replaceSlice, M.saltOfBits_toBits]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem sliceGlue_node (FX : Digest k → XOut k e) (l r : Digest k) :
    chainOracle (sliceGlue (M := M) H σ Fo FX) (.node l r) = chainOracle H (.node l r) := by
  simp only [chainOracle, sliceGlue, replaceSlice, M.saltOfBits_toBits]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem sliceGlue_xof (FX : Digest k → XOut k e) (κ : Digest k) :
    chainOracle (sliceGlue (M := M) H σ Fo FX) (.xof κ σ) = outEquiv k e (FX κ) := by
  have hs : M.saltOfBits (Query.toBits (.xof κ σ : Query k kN kS L)) = some σ := by
    rw [M.saltOfBits_toBits]
    rfl
  simp only [chainOracle, sliceGlue, replaceSlice, hs, ite_true]
  exact congrArg _ (splitAlong_symm_apply_embed (SPBCS.xofEmb σ) Fo FX κ)

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem transcript_notMem_xofEmb (b : Bytes L) :
    Query.toBits (.transcript b : Query k kN kS L) ∉
      Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ) := by
  rintro ⟨κ, hκ⟩
  have := Query.toBits.injective
    (show Query.toBits (.xof κ σ : Query k kN kS L) = Query.toBits (.transcript b) from hκ)
  cases this

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The glued slice answers a `transcript` query of the salt from its part off the `xof`
inputs.** -/
theorem sliceGlue_transcript_eq (FX : Digest k → XOut k e) {b : Bytes L}
    (hb : M.querySalt (.transcript b) = some σ) :
    chainOracle (sliceGlue (M := M) H σ Fo FX) (.transcript b) =
      outEquiv k e (Fo ⟨_, transcript_notMem_xofEmb σ b⟩) := by
  have hs : M.saltOfBits (Query.toBits (.transcript b : Query k kN kS L)) = some σ := by
    rw [M.saltOfBits_toBits, hb]
  simp only [chainOracle, sliceGlue, replaceSlice, hs, ite_true,
    splitAlong_symm_apply_of_notMem (SPBCS.xofEmb σ) _ _ (transcript_notMem_xofEmb σ b)]

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- Reprogramming the glued slice at `xof` inputs of `σ` is reprogramming its `xof` part. -/
theorem reprogram_sliceGlue (FX : Digest k → XOut k e)
    (ass : List (Assignment (Digest k) (XOut k e))) :
    (sliceGlue (M := M) H σ Fo FX).reprogram (ass.map (Assignment.mapInput (SPBCS.xofEmb σ))) =
      sliceGlue (M := M) H σ Fo (FX.reprogram ass) := by
  funext b
  by_cases hb : b ∈ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)
  · obtain ⟨κ, rfl⟩ := hb
    have hX : ∀ FX' : Digest k → XOut k e,
        (sliceGlue (M := M) H σ Fo FX') ∘ SPBCS.xofEmb σ = FX' := fun FX' => by
      funext κ'
      have hs : M.saltOfBits (Query.toBits (.xof κ' σ : Query k kN kS L)) = some σ := by
        rw [M.saltOfBits_toBits]
        rfl
      simp only [Function.comp_apply, sliceGlue, replaceSlice]
      rw [show (SPBCS.xofEmb σ) κ' = Query.toBits (.xof κ' σ : Query k kN kS L) from rfl, hs,
        ite_eq_left rfl]
      exact splitAlong_symm_apply_embed (SPBCS.xofEmb σ) Fo FX' κ'
    rw [reprogram_map_apply (SPBCS.xofEmb σ).injective, hX]
    exact (congrFun (hX (FX.reprogram ass)) κ).symm
  · rw [reprogram_map_apply_of_notMem _ _ hb]
    simp only [sliceGlue, replaceSlice,
      splitAlong_symm_apply_of_notMem (SPBCS.xofEmb σ) _ _ hb]

variable (prv₀ : CausalProver P t X) (ν : M.Pos → MerkleSalt kN)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem honestDigest_sliceGlue (FX : Digest k → XOut k e) (ρ : ChIdx P t → Out k e) :
    FullPast.honestDigest E prv₀ x ν (chainOracle (sliceGlue (M := M) H σ Fo FX)) ρ =
      FullPast.honestDigest E prv₀ x ν (chainOracle H) ρ := by
  funext q
  simp only [FullPast.honestDigest, MerkleTree.leafDigest, sliceGlue_leaf]

/-- The built chains at the streams `ρX` (quantum-oracle answers). -/
noncomputable def lazyChains (ρX : ChIdx P t → XOut k e) : M.Chains :=
  M.buildChains (chainOracle H) (FullPast.outs ρX)
    (Base.honestWrite' E prv₀ x (FullPast.outs ρX))
    (FullPast.honestDigest E prv₀ x ν (chainOracle H) (FullPast.outs ρX))

/-- The built chain of leaf `p` at the streams `ρX`. -/
noncomputable def lazyLeaf (ρX : ChIdx P t → XOut k e) (p : t.Leaf) (r : ℕ) : M.Items p :=
  M.toFullPast.buildLeaf (chainOracle H) (FullPast.outs ρX)
    (Base.honestWrite' E prv₀ x (FullPast.outs ρX))
    (FullPast.honestDigest E prv₀ x ν (chainOracle H) (FullPast.outs ρX)) p r

/-- **The final digests** at the streams `ρX`: those of the built chains, with the final inputs
answered by the slice part `Fo`. -/
noncomputable def lazyFinals (ρX : ChIdx P t → XOut k e) : Mg.Site → Digest k :=
  M.finalsWith (chainOracle (sliceGlue (M := M) H σ Fo 0)) ⟨σ, x⟩
    (lazyChains (E := E) H x prv₀ ν ρX)

/-- **The chain input of challenge `c`** at the streams `ρX`, with the final digests read from
`Fo`, as a point off the `xof` inputs. -/
noncomputable def lazyInput (ρX : ChIdx P t → XOut k e) (c : ChIdx P t) :
    {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} :=
  ⟨_, transcript_notMem_xofEmb σ (M.senc.encode (roundContent ⟨σ, x⟩
    (lazyChains (E := E) H x prv₀ ν ρX) (lazyFinals (E := E) H x σ Fo prv₀ ν ρX) c.leaf
    (lazyLeaf (E := E) H x prv₀ ν ρX c.leaf c.idx.1)))⟩

/-- **The key of challenge `c`** at the streams `ρX`: the digest of the slice part `Fo` at its
chain input. -/
noncomputable def lazyKey (c : ChIdx P t) (ρX : ChIdx P t → XOut k e) : Digest k :=
  (outEquiv k e (Fo (lazyInput (E := E) H x σ Fo prv₀ ν ρX c))).digest

/-- The honest streams on the glued slice, as quantum-oracle answers. -/
noncomputable def lazySol (FX : Digest k → XOut k e) (c : ChIdx P t) : XOut k e :=
  (outEquiv k e).symm
    (honestStreams E prv₀ x ν σ (chainOracle (sliceGlue (M := M) H σ Fo FX)) c)

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The glued slice answers `transcript` queries independently of its `xof` part.** -/
theorem sliceGlue_transcript (FX FX' : Digest k → XOut k e) (b : Bytes L) :
    chainOracle (sliceGlue (M := M) H σ Fo FX) (.transcript b) =
      chainOracle (sliceGlue (M := M) H σ Fo FX') (.transcript b) := by
  simp only [chainOracle, sliceGlue, replaceSlice,
    splitAlong_symm_apply_of_notMem (SPBCS.xofEmb σ) _ _ (transcript_notMem_xofEmb σ b)]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The built key on the glued slice is the lazy key.** -/
theorem buildKey_sliceGlue (FX : Digest k → XOut k e) (ρX : ChIdx P t → XOut k e)
    (c : ChIdx P t) :
    M.buildKey (chainOracle (sliceGlue (M := M) H σ Fo FX)) ⟨σ, x⟩ (FullPast.outs ρX)
        (Base.honestWrite' E prv₀ x (FullPast.outs ρX))
        (FullPast.honestDigest E prv₀ x ν (chainOracle H) (FullPast.outs ρX)) c =
      lazyKey (E := E) H x σ Fo prv₀ ν c ρX := by
  have hleaf := sliceGlue_leaf (M := M) H σ Fo FX
  have hnode := sliceGlue_node (M := M) H σ Fo FX
  unfold buildKey buildFinals lazyKey lazyInput lazyFinals lazyChains lazyLeaf key
  rw [M.buildChains_congr _ _ _ hleaf hnode, M.toFullPast.buildLeaf_congr hleaf hnode,
    finalsWith_congr_oracle (h₂ := chainOracle (sliceGlue (M := M) H σ Fo 0))
      fun fs s => sliceGlue_transcript H σ Fo FX 0 _,
    sliceGlue_transcript_eq H σ Fo FX (by
      rw [M.querySalt_transcript_encode (M.wf_buildRound _ _ _ _ _ _ c)]
      rfl)]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem lazySol_eq (FX : Digest k → XOut k e) (c : ChIdx P t) :
    lazySol (E := E) H x σ Fo prv₀ ν FX c =
      FX (lazyKey (E := E) H x σ Fo prv₀ ν c (lazySol (E := E) H x σ Fo prv₀ ν FX)) := by
  have hρ : FullPast.outs (lazySol (E := E) H x σ Fo prv₀ ν FX) =
      honestStreams E prv₀ x ν σ (chainOracle (sliceGlue (M := M) H σ Fo FX)) := by
    funext j
    simp [lazySol, FullPast.outs]
  rw [lazySol, honestStreams_eq E prv₀ x ν σ _ c, keyStep, honestDigest_sliceGlue, ← hρ,
    buildKey_sliceGlue, sliceGlue_xof, Equiv.symm_apply_apply]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem lazyKey_causal (c : ChIdx P t) (ρX ρX' : ChIdx P t → XOut k e)
    (h : ∀ j, (FullPast.chOrder P t).lt j c → ρX j = ρX' j) :
    lazyKey (E := E) H x σ Fo prv₀ ν c ρX = lazyKey (E := E) H x σ Fo prv₀ ν c ρX' := by
  rw [← buildKey_sliceGlue H x σ Fo prv₀ ν 0, ← buildKey_sliceGlue H x σ Fo prv₀ ν 0,
    ← honestDigest_sliceGlue H x σ Fo prv₀ ν 0, ← honestDigest_sliceGlue H x σ Fo prv₀ ν 0]
  exact buildKey_honest_congr E prv₀ x ν _ _ c fun j hj => by
    simp only [FullPast.outs, h j hj]

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (M) in
/-- **A point off the `xof` inputs is a final input**: the `transcript` input of a well-formed
final content. -/
def IsFinalPt (b : {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)}) : Prop :=
  ∃ c : M.MContent, c.WF n (fun j => chainWF (P j)) ∧ (∃ s, c.obs = .sink s) ∧
    b.1 = Query.toBits (.transcript (M.senc.encode c))

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **A chain input of a challenge is not a final input**: it is a round content. -/
theorem not_isFinalPt_lazyInput (ρX : ChIdx P t → XOut k e) (c : ChIdx P t) :
    ¬ M.IsFinalPt σ (lazyInput (E := E) H x σ Fo prv₀ ν ρX c) := by
  rintro ⟨d, hd, hs, he⟩
  have hc := M.senc.encode_injective (M.wf_buildRound _ _ _ _ _ _ c) hd
    (Query.transcript.inj (Query.toBits.injective he))
  rw [← hc] at hs
  obtain ⟨s, hs⟩ := hs
  simp [roundContent] at hs

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **Distinct challenges read distinct chain inputs**: their contents differ in the leaf or in
the number of own items. -/
theorem lazyInput_injective (ρX : ChIdx P t → XOut k e) :
    Function.Injective (lazyInput (E := E) H x σ Fo prv₀ ν ρX) := fun c c' hcc => by
  have h2 := Query.transcript.inj (Query.toBits.injective (congrArg Subtype.val hcc))
  have hc := M.senc.encode_injective (M.wf_buildRound _ _ _ _ _ _ c)
    (M.wf_buildRound _ _ _ _ _ _ c') h2
  have hl := congrArg Content.obs hc
  have ho := congrArg Content.ownLength hc
  simp only [roundContent, Content.obs_round, Merges.Obs.leaf.injEq] at hl
  simp only [roundContent, Content.ownLength, FullPast.length_buildLeaf] at ho
  obtain ⟨p, i⟩ := c
  obtain ⟨p', i'⟩ := c'
  dsimp only at hl ho
  subst hl
  have : i = i' := Subtype.ext (Fin.ext ho)
  rw [this]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The chain inputs read the slice part only at the final inputs.** -/
theorem lazyInput_congr {Fo' : {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} →
    XOut k e} (ρX : ChIdx P t → XOut k e) (hF : ∀ b, M.IsFinalPt σ b → Fo b = Fo' b)
    (c : ChIdx P t) :
    lazyInput (E := E) H x σ Fo prv₀ ν ρX c = lazyInput (E := E) H x σ Fo' prv₀ ν ρX c := by
  have hw := M.wf_finalContent_of (ss := ⟨σ, x⟩) (chs := lazyChains (E := E) H x prv₀ ν ρX)
  have : lazyFinals (E := E) H x σ Fo prv₀ ν ρX = lazyFinals (E := E) H x σ Fo' prv₀ ν ρX :=
    finalsWith_congr_oracle fun fs s => by
      have hwf := hw fs (M.chainWF_buildChains _ _ _ _) (M.length_buildChains _ _ _ _) s
      have hq : M.querySalt (.transcript (M.senc.encode (finalContent ⟨σ, x⟩
          (lazyChains (E := E) H x prv₀ ν ρX) fs s))) = some σ := by
        rw [M.querySalt_transcript_encode hwf]
        rfl
      rw [sliceGlue_transcript_eq H σ Fo 0 hq, sliceGlue_transcript_eq H σ Fo' 0 hq,
        hF _ ⟨_, hwf, ⟨s, rfl⟩, rfl⟩]
  simp only [lazyInput, this]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The key collision of the lazy keys**: for fixed streams, over a uniform slice part, two
challenges have equal keys with probability at most `keyCollision (t.size n) k`. The final digests
are read from the slice part at the final inputs, which are not chain inputs of a challenge. -/
theorem prob_lazyKey_not_injective_le (ρX : ChIdx P t → XOut k e) :
    ((PMF.uniformOfFintype ({b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} →
      XOut k e)).toOuterMeasure
      {Fo | ¬ Function.Injective fun c => lazyKey (E := E) H x σ Fo prv₀ ν c ρX}).toReal ≤
        (SPBCS.keyCollision (t.size n) k).toReal := by
  classical
  set NX := {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)}
  set a : (NX → XOut k e) → ChIdx P t → NX := fun Fo =>
    lazyInput (E := E) H x σ Fo prv₀ ν ρX
  set g : XOut k e → Digest k := fun y => (outEquiv k e y).digest
  have hg : (PMF.uniformOfFintype (XOut k e)).map g = PMF.uniformOfFintype (Digest k) := by
    rw [show g = Prod.fst ∘ Out.equivProd ∘ outEquiv k e from rfl, ← PMF.map_comp, ← PMF.map_comp,
      PMF.map_uniformOfFintype_equiv, PMF.map_uniformOfFintype_equiv, PMF.map_fst_uniformOfFintype]
  have hpair : ∀ c c' : ChIdx P t, c ≠ c' →
      ((PMF.uniformOfFintype (NX → XOut k e)).toOuterMeasure
        {Fo | g (Fo (a Fo c)) = g (Fo (a Fo c'))}).toReal = ((2 : ℝ) ^ (8 * k))⁻¹ := fun c c' hcc => by
    rw [prob_comp_eq_comp_of_local g hg (M.IsFinalPt σ) (a := fun Fo => a Fo c)
      (b := fun Fo => a Fo c')
      (fun Fo Fo' hag => ⟨lazyInput_congr H x σ Fo prv₀ ν ρX hag c,
        lazyInput_congr H x σ Fo prv₀ ν ρX hag c'⟩)
      (fun Fo => not_isFinalPt_lazyInput H x σ Fo prv₀ ν ρX c)
      (fun Fo => not_isFinalPt_lazyInput H x σ Fo prv₀ ν ρX c')
      (fun Fo => (lazyInput_injective H x σ Fo prv₀ ν ρX).ne hcc), Out.card_digest]
    push_cast
    rfl
  have hset : {Fo : NX → XOut k e | ¬ Function.Injective fun c =>
      lazyKey (E := E) H x σ Fo prv₀ ν c ρX} ⊆
      ⋃ c' : ChIdx P t, ⋃ c : ChIdx P t,
        {Fo | FullPast.gIdx c < FullPast.gIdx c' ∧ g (Fo (a Fo c)) = g (Fo (a Fo c'))} := by
    intro Fo hFo
    simp only [Set.mem_ofPred_eq, Function.Injective, not_forall] at hFo
    obtain ⟨c, c', heq, hne⟩ := hFo
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    rcases lt_or_gt_of_ne (fun he : FullPast.gIdx c = FullPast.gIdx c' =>
      hne (FullPast.gIdx_injective he)) with h | h
    · exact ⟨c', c, h, heq⟩
    · exact ⟨c, c', h, heq.symm⟩
  calc ((PMF.uniformOfFintype (NX → XOut k e)).toOuterMeasure
        {Fo | ¬ Function.Injective fun c => lazyKey (E := E) H x σ Fo prv₀ ν c ρX}).toReal
      ≤ ((PMF.uniformOfFintype (NX → XOut k e)).toOuterMeasure (⋃ c' : ChIdx P t,
          ⋃ c : ChIdx P t, {Fo | FullPast.gIdx c < FullPast.gIdx c' ∧
            g (Fo (a Fo c)) = g (Fo (a Fo c'))})).toReal :=
        ENNReal.toReal_mono (by rw [PMF.toOuterMeasure_apply]; exact PMF.tsum_coe_indicator_ne_top _ _)
          (MeasureTheory.measure_mono hset)
    _ ≤ ∑ c' : ChIdx P t, ∑ c : ChIdx P t,
          ((PMF.uniformOfFintype (NX → XOut k e)).toOuterMeasure
            {Fo | FullPast.gIdx c < FullPast.gIdx c' ∧
              g (Fo (a Fo c)) = g (Fo (a Fo c'))}).toReal :=
        (PMF.toReal_toOuterMeasure_iUnion_le _ _).trans
          (Finset.sum_le_sum fun c' _ => PMF.toReal_toOuterMeasure_iUnion_le _ _)
    _ ≤ ∑ c' : ChIdx P t, ∑ c : ChIdx P t,
          (if FullPast.gIdx c < FullPast.gIdx c' then ((2 : ℝ) ^ (8 * k))⁻¹ else 0) :=
        Finset.sum_le_sum fun c' _ => Finset.sum_le_sum fun c _ => by
          split_ifs with h
          · rw [← hpair c c' (fun he => by subst he; omega)]
            exact ENNReal.toReal_mono
              (by rw [PMF.toOuterMeasure_apply]; exact PMF.tsum_coe_indicator_ne_top _ _)
              (MeasureTheory.measure_mono fun Fo hFo => hFo.2)
          · simp [h]
    _ = (∑ c' : ChIdx P t, ((Finset.univ.filter fun c : ChIdx P t =>
          FullPast.gIdx c < FullPast.gIdx c').card : ℝ)) * ((2 : ℝ) ^ (8 * k))⁻¹ := by
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_mul]
    _ ≤ ((t.size n).choose 2 : ℝ) * ((2 : ℝ) ^ (8 * k))⁻¹ :=
        mul_le_mul_of_nonneg_right (FullPast.sum_card_earlier_le P t) (by positivity)
    _ = (SPBCS.keyCollision (t.size n) k).toReal := by
        rw [SPBCS.keyCollision, ENNReal.toReal_div, ← div_eq_mul_inv]
        simp

end Lazy

/-- The reply on the glued slice: the built proof of `prv₀` at the streams `q.2`, bounded, and
the glued slice with `xof` part `q.1`. -/
noncomputable def glueOut (σ : FiatShamirSalt kS)
    (Fo : {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} → XOut k e)
    (prv₀ : CausalProver P t X) (ν : M.Pos → MerkleSalt kN)
    (q : (Digest k → XOut k e) × (ChIdx P t → XOut k e)) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  ⟨some (FullPast.Internal.encodeTotal M.toFullPast B (M.toFullPast.buildProof (chainOracle H) σ
      (Base.honestWrite' E prv₀ x (FullPast.outs q.2))
      (FullPast.honestDigest E prv₀ x ν (chainOracle H) (FullPast.outs q.2))
      (Base.honestOpened E prv₀ x ν (FullPast.outs q.2)
        (VE.posC x (M.chOfStreams (FullPast.outs q.2))))
      (VE.posC x (M.chOfStreams (FullPast.outs q.2))))),
    sliceGlue (M := M) H σ Fo q.1⟩

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The real reply on the glued slice** is `glueOut` at the honest streams, a function of the
`xof` part (`lazySol`). -/
theorem map_realOut_eq_glue (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) :
    (PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e)).map
        (realOut (E := E) (Qs := Qs) B H x σ prv₀ ν) =
      (PMF.uniformOfFintype ({b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} →
        XOut k e)).bind fun Fo =>
        ((PMF.uniformOfFintype (Digest k → XOut k e)).map fun FX =>
          (FX, lazySol (E := E) H x σ Fo prv₀ ν FX)).map (glueOut VE B H x σ Fo prv₀ ν) := by
  rw [← PMF.map_uniformOfFintype_equiv (splitAlong (Y' := XOut k e) (SPBCS.xofEmb σ)).symm,
    PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext Fo
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext FX
  simp only [Function.comp_apply, realOut, glueOut]
  have hH : replaceSlice M.saltOfBits σ H ((splitAlong (SPBCS.xofEmb σ)).symm (Fo, FX)) =
      sliceGlue (M := M) H σ Fo FX := rfl
  rw [hH, prove_eq_honestProof, honestProof_eq_buildProof E prv₀ x ν σ _ VE,
    M.toFullPast.buildProof_congr (sliceGlue_leaf H σ Fo FX) (sliceGlue_node H σ Fo FX),
    honestDigest_sliceGlue (E := E) H x σ Fo prv₀ ν FX]
  have hρ : honestStreams E prv₀ x ν σ (chainOracle (sliceGlue (M := M) H σ Fo FX)) =
      FullPast.outs (lazySol (E := E) H x σ Fo prv₀ ν FX) := by
    funext j
    simp [lazySol, FullPast.outs]
  rw [hρ]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The lazily sampled reply on the glued slice** is `glueOut` with the `xof` part
reprogrammed at the lazy keys. -/
theorem map_lazyOut_eq_glue (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) :
    (PMF.uniformOfFintype (FullPast.StreamDraw k kN kS L e P t)).map
        (lazyOut VE B H x σ prv₀ ν) =
      (PMF.uniformOfFintype ({b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} →
        XOut k e)).bind fun Fo =>
        ((PMF.uniformOfFintype ((Digest k → XOut k e) × (ChIdx P t → XOut k e))).map fun q =>
          (q.1.reprogram ((Base.chList P t).map fun c =>
            ⟨lazyKey (E := E) H x σ Fo prv₀ ν c q.2, q.2 c⟩), q.2)).map
          (glueOut VE B H x σ Fo prv₀ ν) := by
  set es := splitAlong (Y' := XOut k e) (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)
  let eI : ({b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} → XOut k e) ×
      ((Digest k → XOut k e) × (ChIdx P t → XOut k e)) ≃
        FullPast.StreamDraw k kN kS L e P t :=
    { toFun := fun a => ⟨es.symm (a.1, a.2.1), fun j => outEquiv k e (a.2.2 j)⟩
      invFun := fun b => ((es b.slice).1, ((es b.slice).2,
        fun j => (outEquiv k e).symm (b.streams j)))
      left_inv := fun a => by simp
      right_inv := fun b => by simp }
  rw [← PMF.map_uniformOfFintype_equiv eI, PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind,
    PMF.map_bind]
  congr 1
  funext Fo
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext q
  obtain ⟨FX, ρX⟩ := q
  simp only [Function.comp_apply, glueOut, eI, Equiv.coe_fn_mk, lazyOut, outB]
  have hH : replaceSlice M.saltOfBits σ H (es.symm (Fo, FX)) = sliceGlue (M := M) H σ Fo FX := rfl
  rw [hH, M.toFullPast.buildProof_congr (sliceGlue_leaf H σ Fo FX) (sliceGlue_node H σ Fo FX)]
  congr 2
  rw [buildAssign, List.map_map, ← reprogram_sliceGlue H σ Fo FX, List.map_map]
  refine congrArg (Function.reprogram _) (List.map_congr_left fun c _ => ?_)
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [show (fun j => outEquiv k e (ρX j)) = FullPast.outs ρX from rfl, buildKey_sliceGlue]
  rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The average key collision** over a uniform slice part and uniform streams. -/
theorem expect_prob_lazyKey_le (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) :
    𝔼 Fo : {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} → XOut k e,
      ((PMF.uniformOfFintype (ChIdx P t → XOut k e)).toOuterMeasure
        {ρX | ¬ Function.Injective fun c => lazyKey (E := E) H x σ Fo prv₀ ν c ρX}).toReal ≤
      (SPBCS.keyCollision (t.size n) k).toReal := by
  classical
  have hswap : (𝔼 Fo : {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} →
      XOut k e, ((PMF.uniformOfFintype (ChIdx P t → XOut k e)).toOuterMeasure
        {ρX | ¬ Function.Injective fun c => lazyKey (E := E) H x σ Fo prv₀ ν c ρX}).toReal) =
      𝔼 ρX : ChIdx P t → XOut k e,
        ((PMF.uniformOfFintype ({b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} →
          XOut k e)).toOuterMeasure
          {Fo | ¬ Function.Injective fun c => lazyKey (E := E) H x σ Fo prv₀ ν c ρX}).toReal := by
    simp only [PMF.toReal_toOuterMeasure_apply, PMF.toReal_uniformOfFintype_apply,
      Finset.expect_eq_sum_div_card, Set.mem_ofPred_eq]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div]
    refine Finset.sum_congr rfl fun ρX _ => Finset.sum_congr rfl fun Fo _ => ?_
    split_ifs <;> simp only [Finset.card_univ] <;> ring
  rw [hswap]
  refine (Finset.expect_le_expect fun ρX _ =>
    prob_lazyKey_not_injective_le (E := E) H x σ prv₀ ν ρX).trans ?_
  rw [Finset.expect_const Finset.univ_nonempty]

/-- **Lazy sampling at fixed prover coins**: within the key collision. -/
theorem tvDist_realOut_lazyOut_le (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) :
    (PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e)).map
        (realOut (E := E) (Qs := Qs) B H x σ prv₀ ν)
      ≈[(SPBCS.keyCollision (t.size n) k).toReal]
      (PMF.uniformOfFintype (FullPast.StreamDraw k kN kS L e P t)).map
        (lazyOut VE B H x σ prv₀ ν) := by
  rw [map_realOut_eq_glue VE B H x σ prv₀ ν, map_lazyOut_eq_glue VE B H x σ prv₀ ν]
  refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
  refine (Finset.expect_le_expect fun Fo _ => (PMF.tvDist_map_le _ _ _).trans
    (@tvDist_lazy_le (Digest k) (XOut k e) _ _ _ _ (ChIdx P t) _ _
      (FullPast.chOrder P t) _ (Base.chList P t) Base.nodup_chList
      Base.mem_chList
      (fun c ρX => lazyKey (E := E) H x σ Fo prv₀ ν c ρX)
      (fun c ρX ρX' h => lazyKey_causal (E := E) H x σ Fo prv₀ ν c ρX ρX' h)
      (lazySol (E := E) H x σ Fo prv₀ ν) (lazySol_eq (E := E) H x σ Fo prv₀ ν))).trans ?_
  exact expect_prob_lazyKey_le (E := E) H x σ prv₀ ν

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- `innerR` averages over the prover's coins. -/
theorem innerR_eq_bind (σ : FiatShamirSalt kS) :
    innerR (E := E) (Qs := Qs) B H x prv σ = (PMF.uniformOfFintype (M.ProverCoins R)).bind fun c =>
      (PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e)).map
        (realOut (E := E) (Qs := Qs) B H x σ (prv c.iop) c.merkleSalts) := by
  rw [innerR, ← PMF.map_uniformOfFintype_equiv (FreshSlice.equivProd _ _ (M.ProverCoins R)).symm,
    PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext c
  rw [PMF.map_comp]
  rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- `innerL` averages over the prover's coins. -/
theorem innerL_eq_bind (σ : FiatShamirSalt kS) :
    innerL VE B H x prv σ = (PMF.uniformOfFintype (M.ProverCoins R)).bind fun c =>
      (PMF.uniformOfFintype (FullPast.StreamDraw k kN kS L e P t)).map
        (lazyOut VE B H x σ (prv c.iop) c.merkleSalts) := by
  rw [innerL, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext c
  rw [PMF.map_comp]
  rfl

/-- **Lazy sampling on the `xof` slice of the salt**: within the key collision over all rounds. -/
theorem tvDist_innerR_innerL_le (σ : FiatShamirSalt kS) :
    innerR (E := E) (Qs := Qs) B H x prv σ ≈[(SPBCS.keyCollision (t.size n) k).toReal]
      innerL VE B H x prv σ := by
  rw [innerR_eq_bind B H x prv σ, innerL_eq_bind VE B H x prv σ]
  refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
  refine (Finset.expect_le_expect fun c _ => ?_).trans (Finset.expect_const Finset.univ_nonempty _).le
  exact tvDist_realOut_lazyOut_le VE B H x σ (prv c.iop) c.merkleSalts

/-- The reply with the leaf digests and the Merkle salts of the opened positions given per
position by `z`. -/
noncomputable def leafOut (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (d : FullPast.StreamDraw k kN kS L e P t) (z : M.Pos → MerkleSalt kN × Digest k) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  outB B H x σ d.slice d.streams (Base.honestWrite' E prv₀ x d.streams) (fun q => (z q).2)
    ((VE.posC x (M.chOfStreams d.streams)).map fun q =>
      MerkleLeaf.mk (z q).1 (FullPast.honestCol (E := E) x prv₀ d q))
    (VE.posC x (M.chOfStreams d.streams))

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- `innerL` as independent per-position laws given the prover's coins and the draw. -/
theorem innerL_eq_pi (σ : FiatShamirSalt kS) :
    innerL VE B H x prv σ =
      (PMF.uniformOfFintype (R × FullPast.StreamDraw k kN kS L e P t)).bind fun o =>
        (PMF.pi fun q => (PMF.uniformOfFintype (MerkleSalt kN)).map
          (FullPast.lazyLeafLaw VE H x (prv o.1) o.2 q)).map (leafOut VE B H x σ (prv o.1) o.2) := by
  let eq : M.ProverCoins R × FullPast.StreamDraw k kN kS L e P t ≃
      (R × FullPast.StreamDraw k kN kS L e P t) × (M.Pos → MerkleSalt kN) :=
    { toFun := fun a => ((a.1.iop, a.2), a.1.merkleSalts)
      invFun := fun b => (⟨b.1.1, b.2⟩, b.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [innerL, ← PMF.map_uniformOfFintype_equiv eq.symm, PMF.map_comp,
    PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext o
  rw [← PMF.pi_map, ← PMF.pi_uniformOfFintype, PMF.map_comp, PMF.map_comp]
  congr 1
  funext ν
  simp only [Function.comp_apply, eq, Equiv.coe_fn_symm_mk, lazyOut, leafOut]
  congr 1
  · funext q
    by_cases hq : q ∈ VE.posC x (M.chOfStreams o.2.streams) <;>
      simp [FullPast.lazyLeafLaw, hq, FullPast.honestDigest, FullPast.honestCol]
  · exact List.map_congr_left fun q hq => by
      simp [FullPast.lazyLeafLaw, hq, FullPast.honestCol]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- `innerD` as independent per-position laws given the prover's coins and the draw. -/
theorem innerD_eq_pi (σ : FiatShamirSalt kS) :
    innerD VE B H x prv σ =
      (PMF.uniformOfFintype (R × FullPast.StreamDraw k kN kS L e P t)).bind fun o =>
        (PMF.pi fun q => (PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map
          (FullPast.mixLeaf VE H x (prv o.1) o.2 q)).map (leafOut VE B H x σ (prv o.1) o.2) := by
  let eq : M.toFullPast.LeafDraw R ≃ (R × FullPast.StreamDraw k kN kS L e P t) ×
      (M.Pos → MerkleSalt kN × Digest k) :=
    { toFun := fun a => ((a.iop, a.draw), a.leaves)
      invFun := fun b => ⟨b.1.1, b.1.2, b.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [innerD, ← PMF.map_uniformOfFintype_equiv eq.symm, PMF.map_comp,
    PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext o
  rw [← PMF.pi_map, ← PMF.pi_uniformOfFintype, PMF.map_comp, PMF.map_comp]
  congr 1
  funext z
  simp only [Function.comp_apply, eq, Equiv.coe_fn_symm_mk, mixOut, leafOut]
  congr 1
  · funext q
    by_cases hq : q ∈ VE.posC x (M.chOfStreams o.2.streams) <;>
      simp [FullPast.mixLeaf, hq, FullPast.mixDigest, FullPast.honestDigest,
        FullPast.honestCol]
  · exact List.map_congr_left fun q hq => by simp [FullPast.mixLeaf, hq, FullPast.honestCol]

/-- **The unopened leaves**: one leaf distance per position. -/
theorem tvDist_innerL_innerD_le (σ : FiatShamirSalt kS) :
    innerL VE B H x prv σ ≈[Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b))]
      (innerD VE B H x prv σ) := by
  classical
  rw [innerL_eq_pi VE B H x prv σ, innerD_eq_pi VE B H x prv σ]
  refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
  have hpos : ∀ o : R × FullPast.StreamDraw k kN kS L e P t, PMF.tvDist
      (PMF.pi fun q => (PMF.uniformOfFintype (MerkleSalt kN)).map
        (FullPast.lazyLeafLaw VE H x (prv o.1) o.2 q))
      (PMF.pi fun q => (PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map
        (FullPast.mixLeaf VE H x (prv o.1) o.2 q)) ≤
        Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b)) := fun o => by
    refine (PMF.tvDist_pi_le _ _).trans ?_
    calc ∑ q, PMF.tvDist ((PMF.uniformOfFintype (MerkleSalt kN)).map
            (FullPast.lazyLeafLaw VE H x (prv o.1) o.2 q))
          ((PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map
            (FullPast.mixLeaf VE H x (prv o.1) o.2 q))
        ≤ ∑ _q : M.Pos, SPBCS.leafMax (fun b => outEquiv k e (H b)) :=
          Finset.sum_le_sum fun q _ =>
            FullPast.tvDist_lazyLeafLaw_mixLeaf_le VE H x (prv o.1) o.2 q
      _ = Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc 𝔼 o : R × FullPast.StreamDraw k kN kS L e P t, PMF.tvDist _ _ ≤
        𝔼 _o : R × FullPast.StreamDraw k kN kS L e P t,
          (Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b))) :=
        Finset.expect_le_expect fun o _ => (PMF.tvDist_map_le _ _ _).trans (hpos o)
    _ = _ := Finset.expect_const Finset.univ_nonempty _

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- `innerD` as a draw of the leaves and the slice, then of the streams, then of the prover's
coins. -/
theorem innerD_eq_bind_streams (σ : FiatShamirSalt kS) :
    innerD VE B H x prv σ =
      (PMF.uniformOfFintype M.toFullPast.LeafSlice).bind fun q =>
        (PMF.uniformOfFintype (ChIdx P t → Out k e)).bind fun ρ =>
          (PMF.uniformOfFintype R).map fun r => outViewAt VE B H x σ q.2 (M.chOfStreams ρ) ρ
            (fun p => (q.1 p).1) (fun p => (q.1 p).2)
            (VE.MV.view ((prv r).run x (M.chOfStreams ρ))) := by
  let eq : M.toFullPast.LeafDraw R ≃ (M.toFullPast.LeafSlice × (ChIdx P t → Out k e)) × R :=
    { toFun := fun a => (((a.leaves, a.draw.slice), a.draw.streams), a.iop)
      invFun := fun b => ⟨b.2, ⟨b.1.1.2, b.1.2⟩, b.1.1.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [innerD, ← PMF.map_uniformOfFintype_equiv eq.symm, PMF.map_comp,
    PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind,
    PMF.uniformOfFintype_prod_eq_bind (β := M.toFullPast.LeafSlice), PMF.bind_bind]
  congr 1
  funext q
  rw [PMF.bind_map]
  congr 1
  funext ρ
  rw [Function.comp_apply, PMF.map_comp]
  congr 1
  funext r
  exact innerD_out_eq VE B H x (prv r) σ _ _ _ _

end OneProof

/-! ### The simulator -/

section Simulator

variable [∀ j i, Nonempty ((P j).Challenge i)] (VR : M.ViewRead) {Pub : Type} (B : ℕ)
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-- **The reply built from challenges, streams and a view**: the writes and opened columns read
off the view, the opened positions with their Merkle salts, the drawn digests elsewhere, the proof
built with the oracle seen through `H` (bounded), and each challenge's stream at the `xof` input
of its key on the built chains, the final digests read from the oracle; the empty response if no
writes can be read off the view. -/
def jointRun (H : Bits (queryBits k kN kS L) → XOut k e) (x : X) (σ : FiatShamirSalt kS)
    (ch : Chs P t) (ρ : ChIdx P t → Out k e) (ν : M.Pos → MerkleSalt kN)
    (d : M.Pos → Digest k) (o : CausalView VR.MV) :
    NARG.SimOutput (Bits (queryBits k kN kS L)) (XOut k e) (M.Response B) :=
  (VR.writesOf x ch o).elim ⟨none, []⟩ fun wr =>
    ⟨FullPast.Internal.encodeTotal M.toFullPast B (M.toFullPast.buildProof (chainOracle H) σ wr (M.toFullPast.jointLeaf VR (chainOracle H) x ch ν d o)
        ((VR.posC x ch).map fun q => ⟨ν q, VR.colOf x ch o q⟩) (VR.posC x ch)),
      (M.buildAssign (chainOracle H) ⟨σ, x⟩ ρ wr (M.toFullPast.jointLeaf VR (chainOracle H) x ch ν d o)).map
        fun qa => ⟨Query.toBits qa.input, (outEquiv k e).symm qa.output⟩⟩

/-- **The simulator of the spBCS compiler at a joint simulator of the composite view**: from
the salt, the joint simulator's coins, the preimage samplers' coins, the Merkle salts and the
digests: the joint simulator's view at the public statement `pub x` (its challenges included),
one stream per challenge drawn by its preimage sampler at the challenge, and the reply
`jointRun`.

Running time: polynomial in the proof size. One run of the joint simulator `Sim` (polynomial by
its own Running time paragraph); one run of each challenge's preimage sampler (polynomial by its
own cost statement); reading the writes and opened columns off the view with the read-off
functions of the view laws. Oracle points: one `leaf` query per opened position, at most
`nLeaves - 1` `node` queries per tree, one `transcript` query per site (its final input, holding
the chains its sink reads in full and at most `nJ` final digests, the sites taken in the order of
the numbers of branches hidden from their sinks) and one `transcript` query per challenge (its
chain input, holding the chains its leaf reads in full, at most `nJ` final digests and its leaf's
items); in all at most `2|Pos| + t.size n + |sites|` points, as the counted program
`niJointSimulatorProg` (`GordieHowe/SPBCS/SimProg.lean`) makes them. The assignment list has one
entry per challenge. This running time is argued here, not proved in Lean. -/
def niJointSimulator (pub : X → Pub) (Sim : CausalJointSimulator VR.MV Pub) (T : M.Preimages) :
    NARG.SimulatorFn (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VR Sim T)) where
  run H x a := M.jointRun VR B H x a.salt (Sim.sim (pub x) a.coins.sim).challenges
    (Sampler.preStreams T (Sim.sim (pub x) a.coins.sim).challenges a.coins.pre) a.coins.merkleSalts
    a.coins.digests (Sim.sim (pub x) a.coins.sim)
  coins_nonempty := inferInstance

section Joint

variable {M VR B} {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {Wit R : Type} [Fintype R] [Nonempty R]
  (honest : Wit → R → CausalProver P t X) (pub : X → Pub)
  (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (B) in
open Classical in
/-- **The spBCS compiler is local in its salt at the joint simulator.** -/
theorem saltedLocal :
    SaltedLocal M.saltOfBits (M.niProverZKM B honest E Qs)
      (M.niJointSimulator VE.toViewRead B pub Sim T) where
  prove_congr H H' x w c hH := by
    simp only [niProverZKM]
    rw [prove_eq_honestProof, prove_eq_honestProof,
      honestProof_congr_salt E (honest w c.coins.iop) x c.coins.merkleSalts c.salt (Qs x)
      fun q hq => by
      simp only [chainOracle]
      rw [hH _ (by rw [M.saltOfBits_toBits]; exact hq)]]
    rfl
  run_congr H H' x s hH := by
    have hh : ∀ q, M.querySalt q = none ∨ M.querySalt q = some s.salt →
        chainOracle H q = chainOracle H' q := fun q hq => by
      simp only [chainOracle]
      rw [hH _ (by rw [M.saltOfBits_toBits]; exact hq)]
    have hleaf : ∀ a b, chainOracle H (.leaf a b) = chainOracle H' (.leaf a b) := fun a b =>
      hh _ (Or.inl rfl)
    have hnode : ∀ l r, chainOracle H (.node l r) = chainOracle H' (.node l r) := fun l r =>
      hh _ (Or.inl rfl)
    simp only [niJointSimulator, jointRun, Base.ViewEncoder.toViewRead]
    rcases VE.writesOf x (Sim.sim (pub x) s.coins.sim).challenges (Sim.sim (pub x) s.coins.sim) with
      _ | wr
    · simp only [Option.elim_none]
    simp only [Option.elim_some, buildAssign, M.toFullPast.jointLeaf_congr _ hleaf,
      M.toFullPast.buildProof_congr hleaf hnode]
    congr 3
    funext c
    rw [M.buildKey_congr _ _ _ _ hleaf hnode (fun b hb => hh _ (Or.inr hb))]
  run_salt H x s a ha := by
    simp only [niJointSimulator, jointRun, Base.ViewEncoder.toViewRead] at ha
    obtain ⟨wr, hs⟩ : ∃ wr, VE.writesOf x (Sim.sim (pub x) s.coins.sim).challenges
        (Sim.sim (pub x) s.coins.sim) = some wr := by
      cases hs : VE.writesOf x (Sim.sim (pub x) s.coins.sim).challenges (Sim.sim (pub x) s.coins.sim)
        with
      | none => simp [hs] at ha
      | some wr => exact ⟨wr, rfl⟩
    simp only [hs, Option.elim_some, List.mem_map] at ha
    obtain ⟨qa, hqa, rfl⟩ := ha
    simp only [buildAssign, List.mem_map] at hqa
    obtain ⟨c, -, rfl⟩ := hqa
    rw [M.saltOfBits_toBits]
    rfl
  coins_eq := rfl

variable (H : Bits (queryBits k kN kS L) → XOut k e) (x : X)

variable (B) in
/-- The simulated reply on the slice `F` of `σ` at the coins `c`. -/
noncomputable def simOutJ (σ : FiatShamirSalt kS) (c : M.JointSimCoins VE.toViewRead Sim T)
    (F : Bits (queryBits k kN kS L) → XOut k e) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  let H' := replaceSlice M.saltOfBits σ H F
  let r := (M.niJointSimulator VE.toViewRead B pub Sim T).run H' x ⟨σ, c⟩
  ⟨some r.proof, H'.reprogram r.assignments⟩

variable (B) in
/-- `innerSJ`: the slice of the simulator at the salt `σ`. -/
noncomputable def innerSJ (σ : FiatShamirSalt kS) :
    PMF (EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e)) :=
  (PMF.uniformOfFintype
    (FreshSlice (Bits (queryBits k kN kS L)) (XOut k e) (M.JointSimCoins VE.toViewRead Sim T))).map
    fun a => simOutJ B VE pub Sim T H x σ a.coins a.slice

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (B) in
open Classical in
theorem simSlice_joint_eq_bind :
    simSlice M.saltOfBits (M.niJointSimulator VE.toViewRead B pub Sim T) H x =
      (PMF.uniformOfFintype (FiatShamirSalt kS)).bind fun σ => innerSJ B VE pub Sim T H x σ := by
  rw [simSlice, FreshSlice.map_uniformOfFintype_salted]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (B) in
theorem simOutJ_eq (σ : FiatShamirSalt kS) (c : M.JointSimCoins VE.toViewRead Sim T)
    (F : Bits (queryBits k kN kS L) → XOut k e) :
    simOutJ B VE pub Sim T H x σ c F =
      outViewAt VE B H x σ F (Sim.sim (pub x) c.sim).challenges
        (Sampler.preStreams T (Sim.sim (pub x) c.sim).challenges c.pre) c.merkleSalts c.digests
        (Sim.sim (pub x) c.sim) := by
  simp only [simOutJ, niJointSimulator, jointRun, outViewAt]
  rcases VE.writesOf x (Sim.sim (pub x) c.sim).challenges (Sim.sim (pub x) c.sim) with _ | wr
  · rfl
  simp only [Option.elim_some, FullPast.jointLeaf_eq, leafDigest_replaceSlice]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (B) in
/-- `innerSJ` as a draw of the leaves and the slice, then of the joint simulator's view, then of
the streams by preimage. -/
theorem innerSJ_eq_bind (σ : FiatShamirSalt kS) :
    innerSJ B VE pub Sim T H x σ =
      (PMF.uniformOfFintype M.toFullPast.LeafSlice).bind fun q =>
        (Sim.law (pub x)).bind fun v => (Sampler.preLaw T v.challenges).map fun ρ =>
          outViewAt VE B H x σ q.2 v.challenges ρ (fun p => (q.1 p).1) (fun p => (q.1 p).2) v := by
  let eq : M.toFullPast.LeafSlice × (Sim.Coins × ∀ c, (T c).Coins) ≃
      FreshSlice (Bits (queryBits k kN kS L)) (XOut k e) (M.JointSimCoins VE.toViewRead Sim T) :=
    { toFun := fun a => ⟨⟨a.2.1, a.2.2, fun p => (a.1.1 p).1, fun p => (a.1.1 p).2⟩, a.1.2⟩
      invFun := fun b => ((fun p => (b.coins.merkleSalts p, b.coins.digests p), b.slice),
        (b.coins.sim, b.coins.pre))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [innerSJ, ← PMF.map_uniformOfFintype_equiv eq, PMF.map_comp,
    PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  congr 1
  funext q
  rw [PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind, CausalJointSimulator.law,
    PMF.bind_map]
  congr 1
  funext c
  simp only [Function.comp_apply]
  rw [Sampler.preLaw, PMF.map_comp, PMF.map_comp]
  congr 1
  funext r
  exact simOutJ_eq B VE pub Sim T H x σ _ _

variable {rel : Set (X × Wit)} {δ : ℝ≥0}

variable (B) in
/-- **The view**: replacing the honest view at the challenges read from the streams by the joint
simulator's costs at most the samplers' rejection and the HVZK error. -/
theorem tvDist_innerD_innerSJ_le (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) {w : Wit}
    (hw : (x, w) ∈ rel) (σ : FiatShamirSalt kS) :
    (innerD VE B H x (honest w) σ) ≈[M.overrun.toReal + δ] innerSJ B VE pub Sim T H x σ := by
  rw [innerD_eq_bind_streams VE B H x (honest w) σ, innerSJ_eq_bind B VE pub Sim T H x σ]
  refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
  refine (Finset.expect_le_expect fun q _ => ?_).trans_eq
    (Finset.expect_const Finset.univ_nonempty _)
  have h := Base.tvDist_obs_joint_le VE honest pub Sim T x hvzk hw fun ch ρ o =>
    PMF.pure (outViewAt VE B H x σ q.2 ch ρ (fun p => (q.1 p).1) (fun p => (q.1 p).2) o)
  simp only [← PMF.bind_pure_comp]
  exact h

variable (B) in
/-- **One merge proof on a fresh slice, at one salt**: the honest reply and the simulated
reply are within `oneProofBound δ H`. -/
theorem tvDist_innerR_innerSJ_le (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) {w : Wit}
    (hw : (x, w) ∈ rel) (σ : FiatShamirSalt kS) :
    (innerR (E := E) (Qs := Qs) B H x (honest w) σ) ≈[M.toFullPast.oneProofBound δ H]
      (innerSJ B VE pub Sim T H x σ) := by
  have h1 := tvDist_innerR_innerL_le VE B H x (honest w) σ
  have h2 := tvDist_innerL_innerD_le VE B H x (honest w) σ
  have h3 := tvDist_innerD_innerSJ_le B VE honest pub Sim T H x hvzk hw σ
  have t1 := PMF.tvDist_triangle (innerR (E := E) (Qs := Qs) B H x (honest w) σ)
    (innerL VE B H x (honest w) σ) (innerSJ B VE pub Sim T H x σ)
  have t2 := PMF.tvDist_triangle (innerL VE B H x (honest w) σ)
    (innerD VE B H x (honest w) σ) (innerSJ B VE pub Sim T H x σ)
  simp only [FullPast.oneProofBound]
  linarith

variable (B) in
open Classical in
/-- **One merge proof is simulated on a fresh slice** at the bound `oneProofBound δ` of the
compiler over the term.

Hypothesis: `hvzk`, honest-verifier zero knowledge of the composite (`CausalHVZK`, CY24
Definition 23.1.8) at the joint simulator `Sim`. -/
theorem sliceClose (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    SliceClose M.saltOfBits (fun x w => (x, w) ∈ rel) (M.niProverZKM B honest E Qs)
      (M.niJointSimulator VE.toViewRead B pub Sim T) (M.toFullPast.oneProofBound δ) where
  close H x w hw := by
    rw [realSlice_eq_bind B H x honest w, simSlice_joint_eq_bind B VE pub Sim T H x]
    refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
    calc 𝔼 σ, PMF.tvDist (innerR (E := E) (Qs := Qs) B H x (honest w) σ)
          (innerSJ B VE pub Sim T H x σ)
        ≤ 𝔼 _σ : FiatShamirSalt kS, M.toFullPast.oneProofBound δ H := Finset.expect_le_expect fun σ _ =>
          tvDist_innerR_innerSJ_le B VE honest pub Sim T H x hvzk hw σ
      _ = M.toFullPast.oneProofBound δ H := Finset.expect_const Finset.univ_nonempty _
  nonneg H := by
    have h1 := SPBCS.leafMax_nonneg (kN := kN) (L := L) H
    simp only [FullPast.oneProofBound]
    positivity
  congr H H' hH := by
    have hcomp : ∀ col : Bytes L, (Out.digest ∘ fun b => outEquiv k e (H b)) ∘
        (fun ν : MerkleSalt kN => Query.toBits (.leaf ν col)) =
        (Out.digest ∘ fun b => outEquiv k e (H' b)) ∘
          (fun ν : MerkleSalt kN => Query.toBits (.leaf ν col)) :=
      fun col => funext fun ν => by
        simp only [Function.comp_apply]
        rw [hH _ (by rw [M.saltOfBits_toBits]; rfl)]
    have : SPBCS.leafMax (fun b => outEquiv k e (H b)) =
        SPBCS.leafMax (fun b => outEquiv k e (H' b)) := by
      simp only [SPBCS.leafMax, digestLaw, hcomp]
    simp only [FullPast.oneProofBound, this]

end Joint

end Simulator

/-! ### Zero knowledge -/

variable {M} in
open Classical in
/-- **Everlasting zero knowledge of the spBCS compiler** (QROM). For every spBCS compiler datum `M` with view laws `VE`, every causal honest prover
`honest` with honest-verifier zero knowledge of the composite (`CausalHVZK`, CY24
Definition 23.1.8) at the joint simulator `Sim` on public statements `pub x` with error `δ`,
preimage samplers `T`, every bound `B` on the proof format, and all finite statement and witness
types read in through `fx` and `fw`: every distinguisher with a request budget of `tq` queries
(`EverlastingZeroKnowledgePure`; unbounded after its last proof query), against environments
answering `Q` proof queries, distinguishes the honest prover `niProverZKM` from the simulator
`niJointSimulator` with advantage at most `zkError δ tq Q`, the error of the compiler over the
term: `4Qt/2^(4kS) + Q(Q - 1)/2^(8kS) + Q · (keyCollision (t.size n) k + overrun + δ +
|Pos| · leafBound k kN L)`. -/
theorem everlastingZeroKnowledge [∀ j i, Nonempty ((P j).Challenge i)]
    [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs)
    (B : ℕ) {Wit R : Type} [Fintype R] [Nonempty R] {honest : Wit → R → CausalProver P t X}
    {Pub : Type} {pub : X → Pub} {Sim : CausalJointSimulator VE.MV Pub} (T : M.Preimages)
    {rel : Set (X × Wit)} {δ : ℝ≥0} {X' W' : Type} [Fintype X'] [DecidableEq X'] [Fintype W']
    [DecidableEq W'] (fx : X' → X) (fw : W' → Wit) (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    EverlastingZeroKnowledgePure (fun x w => (fx x, fw w) ∈ rel)
      ((M.niProverZKM B honest E Qs).comap fx fw)
      ((M.niJointSimulator VE.toViewRead B pub Sim T).comap fx) (M.zkError δ) := by
  have hzk := everlastingZeroKnowledgePure_of_sliceClose _ _ _ _
    ((saltedLocal B VE honest pub Sim T).comap fx fw)
    ((sliceClose B VE honest pub Sim T hvzk).comap fx fw)
  refine EverlastingZeroKnowledgePure.mono hzk fun tq Q => ?_
  unfold Base.zkError
  have hsalt : (Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    ring
  have hsqrt : √(Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (4 * kS) := by
    rw [hsalt, show 8 * kS = 4 * kS * 2 by ring, pow_mul, Real.sqrt_sq (by positivity)]
  have hE := M.toFullPast.expect_oneProofBound_le δ
  rw [hsqrt, hsalt]
  gcongr

end

end GordieHowe.SPBCS
