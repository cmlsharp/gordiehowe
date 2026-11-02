-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Salt
public import GordieHowe.SPBCS.Complete
public import GordieHowe.Model.QROM.SaltedZKProofQuery
public import Mathlib.Data.Set.Finite.List
public import GordieHowe.Foundations.ToMathlib.ListLength
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.SPBCS.Merkle.LeafHidingAdaptive
public import GordieHowe.SPBCS.Extraction.LazySampling
public import GordieHowe.Model.QROM.SaltedZK
public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.SPBCS.Sampler.Preimage
public import GordieHowe.SPBCS.Merkle.TreeProg
public import GordieHowe.Model.IOP.CausalHVZK

@[expose] public section

/-!
# Zero knowledge of the spBCS compiler

Everlasting zero knowledge of the compiler on a series–parallel term with merges
(`GordieHowe/SPBCS/Basic.lean`, paper `thm:bcs-zk`) in the quantum random-oracle model, from
honest-verifier zero knowledge of the composite's observation (`GordieHowe.IOP.CausalHVZK`, CY24
Definition 23.1.8). The argument uses the built chains, proofs and leaf hiding (below), with the chain inputs with
merges:

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

/-!
## Zero knowledge: the pieces that do not read the chain inputs

The pieces of everlasting zero knowledge in the quantum random-oracle model that do not read the
chain inputs, from
honest-verifier zero knowledge of the composite's observation in the form of CY24 Definition
23.1.8, over the challenges of all leaves: bounded proofs, the view laws, the chains and proofs
built from streams (`buildLeaf`, `buildProof`), the honest digests (`honestDigest`), the stream
and leaf draws, and the one-proof bound. The theorem is `everlastingZeroKnowledge` (below). The argument:

* the challenges are ordered by their global round (`chOrder`: round `r` of leaf `p` is global
  round `p.off + r`); a challenge's chain input reads only the streams of earlier challenges in
  this order, since every leaf in its causal past is earlier in term order
  (`buildLeaf_honest_congr`), so lazy sampling applies (`tvDist_lazy_le`);
* distinct challenges have distinct chain inputs (`GordieHowe.SPBCS.lazyInput_injective`: the contents differ in the
  leaf or in the number of own items), so the keys collide with probability at most
  `keyCollision (t.size n) k`;
* the simulator (`GordieHowe.SPBCS.niJointSimulator`) runs a joint simulator of the composite's observation, draws
  each challenge's stream by preimage, builds every leaf's chain and programs each challenge's
  stream at the `xof` input of the key of its chain input and the salt.

The bound per proof query is `keyCollision (t.size n) k + overrun + δ + |Pos| · leafMax`, and the
game's bound `zkError` adds the two O2H steps and the salt collisions.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

variable {k kN kS L e : ℕ}

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t}
  {X : Type} (M : SPBCS Mg P X k kN kS L e)

/-! ### Finiteness of trees and positions -/

instance : Fintype M.Tree := Fintype.ofEquiv _ (Tree.equivSigma M).symm

instance : Fintype M.Pos := Fintype.ofEquiv _ (Pos.equivSigma M).symm

/-! ### Bounded proofs -/

/-- A proof has at most `B` opened leaves and at most `pathCap B` path digests per tree
(`MerkleFormat.pathCap`: `B` for multiproofs, `B · ⌊log₂ 2B⌋` for authentication paths). -/
structure Bounded (B : ℕ) (π : M.NIProof) : Prop where
  leaves_le : π.leaves.length ≤ B
  paths_le : ∀ τ, (π.paths τ).length ≤ M.opening.pathCap B

/-- The proofs with at most `B` opened leaves and at most `pathCap B` path digests per tree: a
finite type. -/
def BProof (B : ℕ) : Type :=
  {π : M.NIProof // M.Bounded B π}

/-- **A bounded proof is its salt, its writes, its opened leaves and its path digests per tree**,
each list of bounded length (`Bounded` bounds exactly these lengths). -/
def BProof.equivProd (B : ℕ) :
    M.BProof B ≃ FiatShamirSalt kS × M.Writes × {l : List (MerkleLeaf kN L) // l.length ≤ B} ×
      ((τ : M.Tree) → {l : List (Digest k) // l.length ≤ M.opening.pathCap B}) where
  toFun π := (π.1.salt, π.1.writes, ⟨π.1.leaves, π.2.leaves_le⟩,
    fun τ => ⟨π.1.paths τ, π.2.paths_le τ⟩)
  invFun x := ⟨⟨x.1, x.2.1, x.2.2.1.1, fun τ => (x.2.2.2 τ).1⟩,
    ⟨x.2.2.1.2, fun τ => (x.2.2.2 τ).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bounded proofs are a finite type (`BProof.equivProd`), with compiled code. -/
instance (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)] : Fintype (M.BProof B) :=
  letI : Fintype {l : List (MerkleLeaf kN L) // l.length ≤ B} := List.fintypeLengthLe _ _
  letI : Fintype {l : List (Digest k) // l.length ≤ M.opening.pathCap B} :=
    List.fintypeLengthLe _ _
  Fintype.ofEquiv _ (BProof.equivProd M B).symm

/-- **Bounded proofs have decidable equality** (`BProof.equivProd`, the writes' decidable
equality `ComponentModel.instDecEqMessageWrite`), with compiled code. -/
instance (B : ℕ) : DecidableEq (M.BProof B) :=
  letI : DecidableEq (FiatShamirSalt kS) := inferInstance
  letI : DecidableEq M.Writes := inferInstance
  letI : DecidableEq {l : List (MerkleLeaf kN L) // l.length ≤ B} := inferInstance
  letI : DecidableEq (M.Tree → {l : List (Digest k) // l.length ≤ M.opening.pathCap B}) :=
    inferInstance
  (BProof.equivProd M B).decidableEq

/-- **A response in the proof-query register of the zero-knowledge games**: a proof in the format
`B`, or none (a simulator that fails). The prover's proofs are in the format by its format bounds
(`FormatBounds`), the simulator's by those of its views. -/
abbrev Response (B : ℕ) : Type := Option (M.BProof B)

namespace Internal

end Internal

/-! ### The view laws -/

/-- A write function of the roots: the write of each prover round of each leaf as a function of
the roots of its trees. -/
abbrev RootWriteFn : Type := (p : t.Leaf) → (i : (P p.label).MessageIdx) →
  (Fin ((M.comp p.label).nTrees i) → Digest k) → (M.comp p.label).MessageWrite i

variable {M} in
/-- **The verifier's view of the composite determines every write and every opened column**
(with the observation the composite view `CausalView` of the
message views `MV`, the observation of `CausalHVZK`): read-off functions agreeing with the
transcript's writes and opened columns. Correspondence obligations of the instance. -/
structure Reveal (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    (Qs : ∀ x, M.IOPQueries V x) where
  /-- How the verifier reads every leaf's prover messages. -/
  MV : CausalViews P t
  /-- The writes read off a view, as functions of the roots. -/
  writesOf : X → Chs P t → CausalView MV → Option M.RootWriteFn
  /-- The column bytes of a position read off a view. -/
  colOf : X → Chs P t → CausalView MV → M.Pos → Bytes L
  writesOf_obs : ∀ x ρ (tr : FullTr P t),
    writesOf x ρ (MV.view tr) = some fun p i rts => (E p.label).write i (tr p i.1) rts
  colOf_obs : ∀ x chs ρ (tr : FullTr P t), tr.challenges = ρ → ∀ q ∈ (Qs x).pos chs ρ,
    colOf x ρ (MV.view tr) q = (E q.leaf.label).cols q.pos.msg (tr q.leaf q.pos.msg.1) q.pos.tree
      q.pos.leaf

variable {M} in
/-- **The view laws**: the observation, and the opened positions as a function of the challenges on
chains with a write at every prover round. -/
structure ViewEncoder (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    (Qs : ∀ x, M.IOPQueries V x) extends Reveal E Qs where
  /-- The opened positions as a function of the statement and the challenges. -/
  posC : X → Chs P t → List M.Pos
  /-- On chains with a write at every prover round, the queried positions are `posC`. -/
  pos_eq : ∀ x (chs : (p : t.Leaf) → M.Items p) ch, M.WritesAll chs → (Qs x).pos chs ch = posC x ch

/-- **The format bounds of the query phases**: every query phase opens at most `NQ` positions and
every tree of every component has at most `N` leaves. A property of the model and the query
phases. -/
structure FormatBounds {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) (NQ N : ℕ) : Prop where
  /-- At most `NQ` opened positions. -/
  pos_le : ∀ x chs ch, ((Qs x).pos chs ch).length ≤ NQ
  /-- At most `N` leaves per tree. -/
  nLeaves_le : ∀ (p : t.Leaf) i τ, (M.comp p.label).nLeaves i τ ≤ N

/-! ### Streams -/

variable [∀ j i, Nonempty ((P j).Challenge i)]

/-- The challenges read from the streams `ρ`: the sampler on each challenge's stream, an
arbitrary challenge where it rejects. -/
def chOfStreams (ρ : ChIdx P t → Out k e) : Chs P t := fun c =>
  (((M.comp c.leaf.label).sampler c.idx).sample (ρ c).stream).getD
    ((M.comp c.leaf.label).sampler c.idx).default

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **Some challenge rejects its uniform stream with probability at most the overrun.** -/
theorem prob_reject_le :
    Pr[ρ ← (ChIdx P t → Out k e) : ∃ c : ChIdx P t,
      ((M.comp c.leaf.label).sampler c.idx).sample (ρ c).stream = none] ≤ M.overrun := by
  refine (probUniform_exists_le _).trans (Finset.sum_le_sum fun c _ => ?_)
  let φ1 : Unit ↪ ChIdx P t := ⟨fun _ => c, fun _ _ _ => rfl⟩
  have h1 : Pr[a ← (ChIdx P t → Out k e) :
      ((M.comp c.leaf.label).sampler c.idx).sample (a c).stream = none] =
      Pr[g ← (Unit → Out k e) : ((M.comp c.leaf.label).sampler c.idx).sample (g ()).stream = none] :=
    probUniform_comp_embedding (Y := Out k e) φ1
      fun g => ((M.comp c.leaf.label).sampler c.idx).sample (g ()).stream = none
  rw [h1]
  calc Pr[g ← (Unit → Out k e) : ((M.comp c.leaf.label).sampler c.idx).sample (g ()).stream = none]
      = Pr[y ← Out k e : ((M.comp c.leaf.label).sampler c.idx).sample y.stream = none] :=
        (QROM.probUniform_equiv (Equiv.funUnique Unit (Out k e)).symm
          (fun g => ((M.comp c.leaf.label).sampler c.idx).sample (g ()).stream = none)).symm
    _ = Pr[s ← (Fin (k + e) → Byte) : ((M.comp c.leaf.label).sampler c.idx).sample s = none] :=
        QROM.probUniform_equiv Out.streamEquiv
          (fun s => ((M.comp c.leaf.label).sampler c.idx).sample s = none)
    _ ≤ _ := ((M.comp c.leaf.label).sampler c.idx).prob_none_le

/-! ### The honest proof as a built proof -/

section Honest

variable {M}
variable (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS) (h : Query k kN kS L → Out k e)

/-- The honest writes at the challenges read from the streams `ρ`. -/
noncomputable def honestWrite' (ρ : ChIdx P t → Out k e) : M.RootWriteFn := fun p i rts =>
  (E p.label).write i (prv.run x (M.chOfStreams ρ) p i.1) rts

/-- The honest opened leaves at the positions `ps`, at the challenges read from `ρ`. -/
noncomputable def honestOpened (ρ : ChIdx P t → Out k e) (ps : List M.Pos) :
    List (MerkleLeaf kN L) :=
  ps.map fun q => ⟨ν q, (E q.leaf.label).cols q.pos.msg
    (prv.run x (M.chOfStreams ρ) q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf⟩

end Honest

/-! ### The prover of the game -/

section Prover

variable {M}

variable (M) in
/-- **The honest prover's coins after the salt**: the causal prover's coins and a Merkle salt per
position. -/
@[ext]
structure ProverCoins (R : Type) where
  /-- The causal prover's coins. -/
  iop : R
  /-- The Merkle salt of each position. -/
  merkleSalts : M.Pos → MerkleSalt kN

variable (M) in
/-- The honest prover's coins as their two parts. -/
def ProverCoins.equivProd (R : Type) : M.ProverCoins R ≃ R × (M.Pos → MerkleSalt kN) where
  toFun c := (c.iop, c.merkleSalts)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (R : Type) [Fintype R] : Fintype (M.ProverCoins R) :=
  Fintype.ofEquiv _ (ProverCoins.equivProd M R).symm

/-- The honest prover's coins have decidable equality when the causal prover's coins do. -/
instance (R : Type) [DecidableEq R] : DecidableEq (M.ProverCoins R) :=
  (ProverCoins.equivProd M R).decidableEq

instance (R : Type) [Nonempty R] : Nonempty (M.ProverCoins R) :=
  ⟨⟨Classical.arbitrary _, fun _ => Classical.arbitrary _⟩⟩

end Prover

/-! ### The simulator -/

/-- **What a simulator reads off a composite view**: the message views, the writes and opened
columns read off a view, and the opened positions of the challenges. The view laws without their
laws and without the query phases. -/
structure ViewRead where
  /-- How the verifier reads every leaf's prover messages. -/
  MV : CausalViews P t
  /-- The writes read off a view, as functions of the roots. -/
  writesOf : X → Chs P t → CausalView MV → Option M.RootWriteFn
  /-- The column bytes of a position read off a view. -/
  colOf : X → Chs P t → CausalView MV → M.Pos → Bytes L
  /-- The opened positions of the challenges. -/
  posC : X → Chs P t → List M.Pos

variable {M} in
/-- **The format bounds of the simulated views**: wherever writes can be read off a view, the
opened positions number at most `B`; and every tree has at most `B` leaves. A property of the
variable {M} in
read-off functions, discharged from the format bounds of the query phases
(`ViewEncoder.formatBounds`). -/
structure ViewRead.FormatBounds (VR : M.ViewRead) (B : ℕ) : Prop where
  /-- At most `B` opened positions where the view decodes. -/
  posC_le : ∀ x ch o wr, VR.writesOf x ch o = some wr → (VR.posC x ch).length ≤ B
  /-- At most `B` leaves per tree. -/
  nLeaves_le : ∀ (p : t.Leaf) i τ, (M.comp p.label).nLeaves i τ ≤ B

/-- **What a simulator reads off the view of the view laws `VE`.** -/
abbrev ViewEncoder.toViewRead {M : SPBCS Mg P X k kN kS L e} {E : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : ViewEncoder E Qs) :
    M.ViewRead where
  MV := VE.MV
  writesOf := VE.writesOf
  colOf := VE.colOf
  posC := VE.posC

/-- **The preimage samplers of the composite**: one per challenge, for its sampler. -/
abbrev Preimages : Type 1 := ∀ c : ChIdx P t, ((M.comp c.leaf.label).sampler c.idx).Preimage

variable (VR : M.ViewRead) {Pub : Type}

/-- **The coins of the simulator after the salt**: the joint simulator's coins, the preimage
samplers' coins of each challenge, a Merkle salt and a digest per position. -/
@[ext]
structure JointSimCoins (S : CausalJointSimulator VR.MV Pub) (T : M.Preimages) : Type where
  /-- The joint simulator's coins. -/
  sim : S.Coins
  /-- The preimage sampler's coins of each challenge. -/
  pre : ∀ c, (T c).Coins
  /-- The Merkle salt of each position. -/
  merkleSalts : M.Pos → MerkleSalt kN
  /-- The digest of each position. -/
  digests : M.Pos → Digest k

variable {VR} in
/-- The simulator's coins as their four parts. -/
def JointSimCoins.equivProd (S : CausalJointSimulator VR.MV Pub) (T : M.Preimages) :
    M.JointSimCoins VR S T ≃
      S.Coins × (∀ c, (T c).Coins) × (M.Pos → MerkleSalt kN) × (M.Pos → Digest k) where
  toFun c := (c.sim, c.pre, c.merkleSalts, c.digests)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (S : CausalJointSimulator VR.MV Pub) (T : M.Preimages) :
    Fintype (M.JointSimCoins VR S T) :=
  Fintype.ofEquiv _ (JointSimCoins.equivProd M S T).symm

instance (S : CausalJointSimulator VR.MV Pub) (T : M.Preimages) :
    Nonempty (M.JointSimCoins VR S T) :=
  ⟨⟨Classical.arbitrary _, fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _,
    fun _ => Classical.arbitrary _⟩⟩

variable (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

section Joint

variable {M VR B} {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {Wit R : Type} [Fintype R] [Nonempty R]
  (honest : Wit → R → CausalProver P t X) (pub : X → Pub)
  (S : CausalJointSimulator VE.MV Pub) (T : M.Preimages)

variable (H : Bits (queryBits k kN kS L) → XOut k e) (x : X)

variable {rel : Set (X × Wit)} {δ : ℝ≥0}

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The view at the joint simulator**: for every function `G` of the challenges, the streams and
the view, the law of `G` at the honest view at the challenges read from uniform streams and the
law of `G` at the joint simulator with streams drawn by preimage are within `overrun + δ`. -/
theorem tvDist_obs_joint_le {β : Type} (hvzk : CausalHVZK VE.MV rel honest pub S δ) {w : Wit}
    (hw : (x, w) ∈ rel) (G : Chs P t → (ChIdx P t → Out k e) → CausalView VE.MV → PMF β) :
    PMF.tvDist
      ((PMF.uniformOfFintype (ChIdx P t → Out k e)).bind fun ρ =>
        (PMF.uniformOfFintype R).bind fun r =>
          G (M.chOfStreams ρ) ρ (VE.MV.view ((honest w r).run x (M.chOfStreams ρ))))
      ((S.law (pub x)).bind fun v => (Sampler.preLaw T v.challenges).bind fun ρ =>
        G v.challenges ρ v) ≤
      M.overrun.toReal + δ := by
  classical
  set K : (ChIdx P t → Out k e) → PMF β := fun ρ => (PMF.uniformOfFintype R).bind fun r =>
    G (M.chOfStreams ρ) ρ (VE.MV.view ((honest w r).run x (M.chOfStreams ρ)))
  set κ : CausalView VE.MV → PMF β := fun v =>
    (Sampler.preLaw T v.challenges).bind fun ρ => G v.challenges ρ v
  by_cases hne : ∀ c : ChIdx P t, ∃ s, (((M.comp c.leaf.label).sampler c.idx).sample s).isSome
  · set Bm : PMF β := (PMF.uniformOfFintype (Chs P t)).bind fun ch =>
      (Sampler.preLaw T ch).bind fun ρ => (PMF.uniformOfFintype R).bind fun r =>
        G ch ρ (VE.MV.view ((honest w r).run x ch)) with hBm
    have hB1 : Bm = ((PMF.uniformOfFintype (Chs P t)).bind (Sampler.preLaw T)).bind K := by
      rw [hBm, PMF.bind_bind]
      congr 1
      funext ch
      rw [Sampler.preLaw, PMF.bind_map, PMF.bind_map]
      congr 1
      funext r
      have hch : M.chOfStreams (Sampler.preStreams T ch r) = ch := funext fun c => by
        simp [chOfStreams, Sampler.sample_preStreams T hne ch r c]
      simp only [Function.comp_apply, K, hch]
    have hB2 : Bm = (VE.MV.honestView honest x w).bind κ := by
      rw [hBm, CausalViews.honestView, PMF.bind_bind]
      congr 1
      funext ch
      rw [PMF.bind_map]
      have hv : ∀ r, (VE.MV.view ((honest w r).run x ch)).challenges = ch := fun r =>
        CausalProver.challenges_run _ x ch
      have hf : (κ ∘ fun r => VE.MV.view ((honest w r).run x ch)) = fun r =>
          (Sampler.preLaw T ch).bind fun ρ => G ch ρ (VE.MV.view ((honest w r).run x ch)) :=
        funext fun r => by simp only [Function.comp_apply, κ, hv]
      rw [hf]
      exact PMF.bind_comm _ _ _
    have h1 : PMF.tvDist ((PMF.uniformOfFintype (ChIdx P t → Out k e)).bind K) Bm ≤
        M.overrun.toReal := by
      rw [hB1]
      refine (PMF.tvDist_bind_right_le _ _ _).trans ((Sampler.tvDist_preLaw_le T).trans ?_)
      exact ENNReal.toReal_mono M.overrun_ne_top M.prob_reject_le
    have h2 : PMF.tvDist Bm ((S.law (pub x)).bind κ) ≤ δ := by
      rw [hB2]
      exact (PMF.tvDist_bind_right_le _ _ _).trans (hvzk x w hw)
    have tr := PMF.tvDist_triangle ((PMF.uniformOfFintype (ChIdx P t → Out k e)).bind K) Bm
      ((S.law (pub x)).bind κ)
    exact tr.trans (add_le_add h1 h2)
  · push Not at hne
    obtain ⟨c, hc⟩ := hne
    have hone : Pr[ρ ← (ChIdx P t → Out k e) : ∃ c : ChIdx P t,
        ((M.comp c.leaf.label).sampler c.idx).sample (ρ c).stream = none] = 1 := by
      rw [probUniform_eq_card_div, Finset.filter_true_of_mem fun ρ _ =>
        ⟨c, by simpa using hc (ρ c).stream⟩, Finset.card_univ]
      exact ENNReal.div_self (by simp) (ENNReal.natCast_ne_top _)
    have hov : 1 ≤ M.overrun.toReal := by
      have := ENNReal.toReal_mono M.overrun_ne_top (hone ▸ M.prob_reject_le)
      simpa using this
    have hδ : (0 : ℝ) ≤ δ := δ.2
    exact (PMF.tvDist_le_one _ _).trans (by linarith)

end Joint

/-- **The zero-knowledge error of the composite** at the HVZK error `δ`, `t` queries and `Q`
proof queries: `4Qt/2^(4kS) + Q(Q - 1)/2^(8kS) + Q · (keyCollision (t.size n) k + overrun + δ +
|Pos| · BCS.leafBound k kN L)`. -/
noncomputable def zkError (δ : ℝ≥0) (tq Q : ℕ) : ℝ :=
  4 * Q * tq / 2 ^ (4 * kS) + Q * (Q - 1) / 2 ^ (8 * kS) +
    Q * ((SPBCS.keyCollision (t.size n) k).toReal + M.overrun.toReal + δ +
      Fintype.card M.Pos * SPBCS.leafBound k kN L)

end

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t}
  {X : Type} (M : SPBCS Mg P X k kN kS L e)

/-- Boundedness of a proof is decidable. -/
instance (B : ℕ) (π : M.NIProof) : Decidable (M.Bounded B π) :=
  decidable_of_iff (π.leaves.length ≤ B ∧ ∀ τ, (π.paths τ).length ≤ M.opening.pathCap B)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.leaves_le, h.paths_le⟩⟩

namespace Internal

/-- **A proof device of the hybrid argument; never in a statement reachable from a headline**: a
proof as a response, the proof itself when it is in the format `B`, none otherwise. The hybrid
games of this file (below) and of `GordieHowe/SPBCS/ZeroKnowledgeROMQuery.lean` build their
replies with it; within the format bounds it is the constructor of a bounded proof
(`encodeTotal_of_bounded`), which is how the theorems about the prover `niProver` and the simulator
`niSimulator` are reached. -/
def encodeTotal (B : ℕ) (π : M.NIProof) : M.Response B :=
  if h : M.Bounded B π then some ⟨π, h⟩ else none

/-- **The device is the constructor on proofs in the format.** -/
theorem encodeTotal_of_bounded {B : ℕ} {π : M.NIProof} (h : M.Bounded B π) :
    encodeTotal M B π = some ⟨π, h⟩ :=
  dite_eq_left h

end Internal

/-! ### Streams -/

variable [∀ j i, Nonempty ((P j).Challenge i)]

/-! ### The proof built from streams, writes and leaf digests -/

section Build

variable (h : Query k kN kS L → Out k e)

/-- The digest of the default leaf, read past the last leaf of a tree. -/
def defaultLeafDigest : Digest k :=
  MerkleTree.leafDigest h (⟨fun _ => 0, ⟨0, Fin.elim0⟩⟩ : MerkleLeaf kN L)

/-- The leaf digests of tree `τ` of round `i` of leaf `p` read from a digest per position. -/
def leafDigestsOf (d : M.Pos → Digest k) (p : t.Leaf) (i : (P p.label).MessageIdx)
    (τ : Fin ((M.comp p.label).nTrees i)) (j : ℕ) : Digest k :=
  if hj : j < (M.comp p.label).nLeaves i τ then d ⟨p, ⟨i, τ, ⟨j, hj⟩⟩⟩ else defaultLeafDigest h

/-- The roots of the trees of round `i` of leaf `p` over the leaf digests `d`. -/
def rootsOf (d : M.Pos → Digest k) (p : t.Leaf) (i : (P p.label).MessageIdx) :
    Fin ((M.comp p.label).nTrees i) → Digest k :=
  fun τ => MerkleTree.nodeDigest h ((M.comp p.label).nLeaves i τ) (M.leafDigestsOf h d p i τ) 1

/-- Round `r` of leaf `p`'s built chain: the write at the roots of the leaf digests, or the
first `k` bytes of the challenge's stream. -/
def buildItem (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k) (p : t.Leaf)
    (r : ℕ) : Item k (M.comp p.label).W :=
  if hr : r < n p.label then
    if hd : (P p.label).dir ⟨r, hr⟩ = .P_to_V then
      .write ⟨⟨⟨r, hr⟩, hd⟩, wr p _ (M.rootsOf h ld p _)⟩
    else .absorb (ρ ⟨p, (P p.label).chIdx ⟨r, hr⟩ hd⟩).digest
  else .absorb fun _ => 0

/-- The first `r` items of leaf `p`'s built chain. -/
def buildLeaf (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k) (p : t.Leaf) :
    ℕ → M.Items p
  | 0 => []
  | r + 1 => buildLeaf ρ wr ld p r ++ [M.buildItem h ρ wr ld p r]

/-- **The built proof**: the salt, the writes at the roots of the leaf digests, the opened leaves
`ops` at the positions `ps`, and each tree's opening from its heap. -/
def buildProof (σ : FiatShamirSalt kS) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)
    (ops : List (MerkleLeaf kN L)) (ps : List M.Pos) : M.NIProof where
  salt := σ
  writes p i := wr p i (M.rootsOf h ld p i)
  leaves := ops
  paths τ := (M.opening.sibs ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
      ((M.openedIn τ ps ops).map Prod.fst)).map
    (MerkleTree.nodeDigest h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
      (M.leafDigestsOf h ld τ.leaf τ.tree.msg τ.tree.tree))

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem length_buildLeaf (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)
    (p : t.Leaf) : ∀ r, (M.buildLeaf h ρ wr ld p r).length = r
  | 0 => rfl
  | r + 1 => by simp [buildLeaf, length_buildLeaf ρ wr ld p r]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem buildLeaf_getElem? (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)
    (p : t.Leaf) : ∀ r j, j < r → (M.buildLeaf h ρ wr ld p r)[j]? = some (M.buildItem h ρ wr ld p j)
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, j, hj => by
    rw [buildLeaf]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem?_append_left (by rw [length_buildLeaf]; exact hj'),
        buildLeaf_getElem? ρ wr ld p r j hj']
    · rw [List.getElem?_append_right (by rw [length_buildLeaf]), length_buildLeaf]
      simp

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem chainWF_buildLeaf (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)
    (p : t.Leaf) {r : ℕ} (hr : r ≤ n p.label) : chainWF (P p.label) (M.buildLeaf h ρ wr ld p r) := by
  intro j hj
  rw [length_buildLeaf] at hj
  have hget := M.buildLeaf_getElem? h ρ wr ld p r j hj
  rw [List.getElem?_eq_getElem (by rw [length_buildLeaf]; exact hj)] at hget
  rw [Option.some_inj.1 hget]
  unfold buildItem
  have hjn : j < n p.label := by omega
  rw [dite_eq_left hjn]
  by_cases hd : (P p.label).dir ⟨j, hjn⟩ = .P_to_V
  · rw [dite_eq_left hd]
    rfl
  · rw [dite_eq_right hd]
    exact ⟨hjn, by cases h' : (P p.label).dir ⟨j, hjn⟩ <;> simp_all⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem leafDigestsOf_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b)) (ld : M.Pos → Digest k) (p : t.Leaf)
    (i : (P p.label).MessageIdx) (τ : Fin ((M.comp p.label).nTrees i)) :
    M.leafDigestsOf h₁ ld p i τ = M.leafDigestsOf h₂ ld p i τ := by
  funext j
  simp [leafDigestsOf, defaultLeafDigest, MerkleTree.leafDigest, hleaf]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem nodeDigest_leafDigestsOf_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b)) (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r))
    (ld : M.Pos → Digest k) (p : t.Leaf) (i : (P p.label).MessageIdx)
    (τ : Fin ((M.comp p.label).nTrees i)) :
    MerkleTree.nodeDigest h₁ ((M.comp p.label).nLeaves i τ) (M.leafDigestsOf h₁ ld p i τ) =
      MerkleTree.nodeDigest h₂ ((M.comp p.label).nLeaves i τ) (M.leafDigestsOf h₂ ld p i τ) := by
  funext j
  rw [M.leafDigestsOf_congr hleaf, MerkleTree.nodeDigest_congr hnode]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem rootsOf_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b)) (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r))
    (ld : M.Pos → Digest k) (p : t.Leaf) (i : (P p.label).MessageIdx) :
    M.rootsOf h₁ ld p i = M.rootsOf h₂ ld p i := by
  funext τ
  simp only [rootsOf, M.nodeDigest_leafDigestsOf_congr hleaf hnode]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The built proof reads the oracle only at `leaf` and `node` queries. -/
theorem buildProof_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b)) (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r))
    (σ : FiatShamirSalt kS) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)
    (ops : List (MerkleLeaf kN L)) (ps : List M.Pos) :
    M.buildProof h₁ σ wr ld ops ps = M.buildProof h₂ σ wr ld ops ps := by
  simp only [buildProof, M.nodeDigest_leafDigestsOf_congr hleaf hnode, M.rootsOf_congr hleaf hnode]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The built chains read the oracle only at `leaf` and `node` queries. -/
theorem buildLeaf_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b)) (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r))
    (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k) (p : t.Leaf) (r : ℕ) :
    M.buildLeaf h₁ ρ wr ld p r = M.buildLeaf h₂ ρ wr ld p r := by
  have hroots : M.rootsOf h₁ ld = M.rootsOf h₂ ld :=
    funext fun p => funext (M.rootsOf_congr hleaf hnode ld p)
  have hitem : M.buildItem h₁ ρ wr ld = M.buildItem h₂ ρ wr ld := by
    funext p r
    unfold buildItem
    rw [hroots]
  induction r with
  | zero => rfl
  | succ r ih => rw [buildLeaf, buildLeaf, ih, hitem]

end Build

/-! ### The honest proof as a built proof -/

section Honest

variable {M}
variable (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS) (h : Query k kN kS L → Out k e)

/-- The honest leaf digests at the challenges read from the streams `ρ`. -/
noncomputable def honestDigest (ρ : ChIdx P t → Out k e) (q : M.Pos) : Digest k :=
  MerkleTree.leafDigest h ⟨ν q, (E q.leaf.label).cols q.pos.msg
    (prv.run x (M.chOfStreams ρ) q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf⟩

/-- The honest heap of a tree is the heap of the honest leaf digests. -/
theorem root_leafFn (ρ : ChIdx P t → Out k e) (p : t.Leaf) (i : (P p.label).MessageIdx)
    (τ : Fin ((M.comp p.label).nTrees i)) :
    (fun j => MerkleTree.leafDigest h (leafFn E ν p i (prv.run x (M.chOfStreams ρ) p i.1) τ j)) =
      M.leafDigestsOf h (honestDigest E prv x ν h ρ) p i τ := by
  funext j
  by_cases hj : j < (M.comp p.label).nLeaves i τ
  · simp [leafDigestsOf, honestDigest, hj, leafFn]
  · simp [leafDigestsOf, defaultLeafDigest, hj, leafFn]

/-- The honest write is the built write at the honest leaf digests. -/
theorem honestWrite_eq (ρ : ChIdx P t → Out k e) (p : t.Leaf) (i : (P p.label).MessageIdx) :
    honestWrite E ν h p i (prv.run x (M.chOfStreams ρ) p i.1) =
      honestWrite' E prv x ρ p i (M.rootsOf h (honestDigest E prv x ν h ρ) p i) := by
  have h1 : (fun τ => MerkleTree.root h ((M.comp p.label).nLeaves i τ)
      (leafFn E ν p i (prv.run x (M.chOfStreams ρ) p i.1) τ)) =
      M.rootsOf h (honestDigest E prv x ν h ρ) p i := by
    funext τ
    simp only [MerkleTree.root, MerkleTree.treeDigest, rootsOf]
    rw [root_leafFn]
  simp only [honestWrite, honestWrite', h1]

end Honest

/-- **The one-proof bound** `η H` of the composite: key collision over all rounds, overrun, the
HVZK error `δ`, and one leaf distance per position. -/
noncomputable def oneProofBound (δ : ℝ≥0) (H : Bits (queryBits k kN kS L) → XOut k e) : ℝ :=
  (SPBCS.keyCollision (t.size n) k).toReal + M.overrun.toReal + δ +
    Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b))

/-! ### The built chains in the streams -/

section Streams

variable {M}

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The roots of round `i` of leaf `p` depend only on the leaf digests of its trees. -/
theorem rootsOf_congr_ld (h : Query k kN kS L → Out k e) {ld ld' : M.Pos → Digest k} (p : t.Leaf)
    (i : (P p.label).MessageIdx) (hld : ∀ τ j, ld ⟨p, ⟨i, τ, j⟩⟩ = ld' ⟨p, ⟨i, τ, j⟩⟩) :
    M.rootsOf h ld p i = M.rootsOf h ld' p i := by
  funext τ
  have : M.leafDigestsOf h ld p i τ = M.leafDigestsOf h ld' p i τ := by
    funext j
    simp only [leafDigestsOf]
    split_ifs with hj
    · exact hld τ ⟨j, hj⟩
    · rfl
  simp only [rootsOf, this]

variable (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X) (x : X)
  (ν : M.Pos → MerkleSalt kN)

/-- The derived challenges of the leaves before `p` read only the streams of earlier global
rounds. -/
theorem chOfStreams_congr_before {ρ ρ' : ChIdx P t → Out k e} {p : t.Leaf}
    (hρ : ∀ j : ChIdx P t, gIdx j < p.off n → ρ j = ρ' j) (c : ChIdx P t) (hc : c.leaf.Before p) :
    M.chOfStreams ρ c = M.chOfStreams ρ' c := by
  have := Leaf.Before.off_add_le n hc
  have := c.idx.1.2
  simp only [chOfStreams]
  rw [hρ c (by unfold gIdx; omega)]

/-- **The honest built chain of a leaf is causal in the streams**: its first `r` items read only
the streams of the challenges before global round `p.off + r`. -/
theorem buildLeaf_honest_congr (h : Query k kN kS L → Out k e) {ρ ρ' : ChIdx P t → Out k e}
    (p : t.Leaf) : ∀ r, (∀ j : ChIdx P t, gIdx j < p.off n + r → ρ j = ρ' j) →
      M.buildLeaf h ρ (honestWrite' E prv x ρ) (honestDigest E prv x ν h ρ) p r =
        M.buildLeaf h ρ' (honestWrite' E prv x ρ') (honestDigest E prv x ν h ρ') p r
  | 0, _ => rfl
  | r + 1, hρ => by
    rw [buildLeaf, buildLeaf, buildLeaf_honest_congr h p r fun j hj => hρ j (by omega)]
    congr 2
    have hmsg : ∀ i : (P p.label).MessageIdx, i.1.1 ≤ r →
        prv.run x (M.chOfStreams ρ) p i.1 = prv.run x (M.chOfStreams ρ') p i.1 := fun i hi =>
      CausalProver.run_message_congr prv x p i
        (chOfStreams_congr_before fun j hj => hρ j (by omega)) fun j hj => by
          simp only [chOfStreams]
          rw [hρ ⟨p, j⟩ (by have : j.1.1 < i.1.1 := hj; show p.off n + j.1.1 < p.off n + (r + 1); omega)]
    unfold buildItem
    by_cases hr : r < n p.label
    · rw [dite_eq_left hr, dite_eq_left hr]
      by_cases hd : (P p.label).dir ⟨r, hr⟩ = .P_to_V
      · rw [dite_eq_left hd, dite_eq_left hd]
        have hm := hmsg ⟨⟨r, hr⟩, hd⟩ le_rfl
        have hroots := rootsOf_congr_ld h (ld := honestDigest E prv x ν h ρ)
          (ld' := honestDigest E prv x ν h ρ') p ⟨⟨r, hr⟩, hd⟩ fun τ j => by
            simp only [honestDigest]
            rw [show prv.run x (M.chOfStreams ρ) p (⟨⟨r, hr⟩, hd⟩ : (P p.label).MessageIdx).1 =
              prv.run x (M.chOfStreams ρ') p (⟨⟨r, hr⟩, hd⟩ : (P p.label).MessageIdx).1 from hm]
        simp only [honestWrite', hroots]
        rw [show prv.run x (M.chOfStreams ρ) p (⟨⟨r, hr⟩, hd⟩ : (P p.label).MessageIdx).1 =
          prv.run x (M.chOfStreams ρ') p (⟨⟨r, hr⟩, hd⟩ : (P p.label).MessageIdx).1 from hm]
      · rw [dite_eq_right hd, dite_eq_right hd,
          hρ ⟨p, (P p.label).chIdx ⟨r, hr⟩ hd⟩ (by unfold gIdx; simp [ProtocolSpec.chIdx])]
    · rw [dite_eq_right hr, dite_eq_right hr]

end Streams

/-! ### One proof on a fresh slice -/

variable (P t k kN kS L e) in
/-- **The stream draw** of the one-proof argument: a fresh slice and one stream per
challenge. -/
@[ext]
structure StreamDraw where
  /-- The fresh answers on the slice of the salt. -/
  slice : Bits (queryBits k kN kS L) → XOut k e
  /-- The stream of each challenge. -/
  streams : ChIdx P t → Out k e

variable (P t k kN kS L e) in
/-- A stream draw as its slice and its streams. -/
def StreamDraw.equivProd : StreamDraw k kN kS L e P t ≃
    (Bits (queryBits k kN kS L) → XOut k e) × (ChIdx P t → Out k e) where
  toFun d := (d.slice, d.streams)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (StreamDraw k kN kS L e P t) :=
  Fintype.ofEquiv _ (StreamDraw.equivProd k kN kS L e P t).symm

instance : Nonempty (StreamDraw k kN kS L e P t) :=
  ⟨⟨fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _⟩⟩

/-- **The draw of `innerD`**: the causal prover's coins, the stream draw, and a Merkle
salt and a digest per position. -/
@[ext]
structure LeafDraw (R : Type) where
  /-- The causal prover's coins. -/
  iop : R
  /-- The stream draw. -/
  draw : StreamDraw k kN kS L e P t
  /-- The Merkle salt and the digest of each position. -/
  leaves : M.Pos → MerkleSalt kN × Digest k

/-- The draw of `innerD` as its three parts. -/
def LeafDraw.equivProd (R : Type) : M.LeafDraw R ≃
    R × StreamDraw k kN kS L e P t × (M.Pos → MerkleSalt kN × Digest k) where
  toFun d := (d.iop, d.draw, d.leaves)
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (R : Type) [Fintype R] : Fintype (M.LeafDraw R) :=
  Fintype.ofEquiv _ (LeafDraw.equivProd M R).symm

instance (R : Type) [Nonempty R] : Nonempty (M.LeafDraw R) :=
  ⟨⟨Classical.arbitrary _, Classical.arbitrary _, fun _ => Classical.arbitrary _⟩⟩

section OneProof

variable {M} {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) (B : ℕ)
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  (H : Bits (queryBits k kN kS L) → XOut k e) (x : X)

variable {R : Type} [Fintype R] [Nonempty R] (prv : R → CausalProver P t X)

/-- The leaf digests of `innerD`: honest at the opened positions, the drawn digest elsewhere. -/
noncomputable def mixDigest (prv₀ : CausalProver P t X) (ν : M.Pos → MerkleSalt kN)
    (d : M.Pos → Digest k) (ρ : ChIdx P t → Out k e) (q : M.Pos) : Digest k :=
  if q ∈ VE.posC x (M.chOfStreams ρ) then honestDigest E prv₀ x ν (chainOracle H) ρ q else d q

section Lazy

variable (σ : FiatShamirSalt kS)
  (Fo : {b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} → XOut k e)

variable (prv₀ : CausalProver P t X) (ν : M.Pos → MerkleSalt kN)

/-- The streams `ρX` (quantum-oracle answers) as byte answers. -/
abbrev outs (ρX : ChIdx P t → XOut k e) : ChIdx P t → Out k e := fun j => outEquiv k e (ρX j)

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] in
variable (P t) in
/-- **The ordered pairs of challenges** number at most `t.size n choose 2`. -/
theorem sum_card_earlier_le :
    ∑ c' : ChIdx P t, ((Finset.univ.filter fun c : ChIdx P t => gIdx c < gIdx c').card : ℝ) ≤
      (t.size n).choose 2 := by
  calc ∑ c' : ChIdx P t, ((Finset.univ.filter fun c : ChIdx P t => gIdx c < gIdx c').card : ℝ)
      ≤ ∑ c' : ChIdx P t, (gIdx c' : ℝ) := Finset.sum_le_sum fun c' _ => by
        have : (Finset.univ.filter fun c : ChIdx P t => gIdx c < gIdx c').card ≤ gIdx c' := by
          calc (Finset.univ.filter fun c : ChIdx P t => gIdx c < gIdx c').card
              ≤ (Finset.range (gIdx c')).card := Finset.card_le_card_of_injOn gIdx
                (fun c hc => by simpa using hc) (fun c _ c' _ he => gIdx_injective he)
            _ = gIdx c' := Finset.card_range _
        exact_mod_cast this
    _ = ∑ r ∈ Finset.univ.map ⟨fun c : ChIdx P t => (⟨gIdx c, gIdx_lt_size c⟩ : Fin (t.size n)),
          fun c c' he => gIdx_injective (congrArg Fin.val he)⟩, (r : ℝ) := by
        rw [Finset.sum_map]
        rfl
    _ ≤ ∑ r : Fin (t.size n), (r : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = (t.size n).choose 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun r => (r : ℝ)) (t.size n), ← Nat.cast_sum,
          Finset.sum_range_id, Nat.choose_two_right]

end Lazy

/-- The honest column of position `q` at the challenges read from the streams of `d`. -/
noncomputable def honestCol (prv₀ : CausalProver P t X) (d : StreamDraw k kN kS L e P t)
    (q : M.Pos) : Bytes L :=
  (E q.leaf.label).cols q.pos.msg (prv₀.run x (M.chOfStreams d.streams) q.leaf q.pos.msg.1)
    q.pos.tree q.pos.leaf

/-- The per-position law of `innerL` from a uniform Merkle salt. -/
noncomputable def lazyLeafLaw (prv₀ : CausalProver P t X) (d : StreamDraw k kN kS L e P t)
    (q : M.Pos) (ν : MerkleSalt kN) : MerkleSalt kN × Digest k :=
  if q ∈ VE.posC x (M.chOfStreams d.streams) then
    (ν, MerkleTree.leafDigest (chainOracle H) ⟨ν, honestCol (E := E) x prv₀ d q⟩)
  else (fun _ => 0, MerkleTree.leafDigest (chainOracle H) ⟨ν, honestCol (E := E) x prv₀ d q⟩)

/-- The per-position law of `innerD` from a uniform Merkle salt and digest. -/
noncomputable def mixLeaf (prv₀ : CausalProver P t X) (d : StreamDraw k kN kS L e P t)
    (q : M.Pos) (a : MerkleSalt kN × Digest k) : MerkleSalt kN × Digest k :=
  if q ∈ VE.posC x (M.chOfStreams d.streams) then
    (a.1, MerkleTree.leafDigest (chainOracle H) ⟨a.1, honestCol (E := E) x prv₀ d q⟩)
  else (fun _ => 0, a.2)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **One position**: the per-position laws of `innerL` and `innerD` are within one leaf
distance. -/
theorem tvDist_lazyLeafLaw_mixLeaf_le (prv₀ : CausalProver P t X) (d : StreamDraw k kN kS L e P t)
    (q : M.Pos) :
    PMF.tvDist ((PMF.uniformOfFintype (MerkleSalt kN)).map (lazyLeafLaw VE H x prv₀ d q))
      ((PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map (mixLeaf VE H x prv₀ d q)) ≤
        SPBCS.leafMax (fun b => outEquiv k e (H b)) := by
  by_cases hq : q ∈ VE.posC x (M.chOfStreams d.streams)
  · have : (PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map (mixLeaf VE H x prv₀ d q) =
        (PMF.uniformOfFintype (MerkleSalt kN)).map (lazyLeafLaw VE H x prv₀ d q) := by
      have h1 : (PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map (mixLeaf VE H x prv₀ d q) =
          ((PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map Prod.fst).map
            (lazyLeafLaw VE H x prv₀ d q) := by
        rw [PMF.map_comp]
        congr 1
        funext a
        simp [mixLeaf, lazyLeafLaw, hq]
      rw [h1, PMF.map_fst_uniformOfFintype]
    rw [this, PMF.tvDist_self]
    exact SPBCS.leafMax_nonneg H
  · have hR : (PMF.uniformOfFintype (MerkleSalt kN)).map (lazyLeafLaw VE H x prv₀ d q) =
        (digestLaw (Out.digest ∘ fun b => outEquiv k e (H b))
          fun ν : MerkleSalt kN => Query.toBits (.leaf ν (honestCol (E := E) x prv₀ d q))).map
            (Prod.mk fun _ => 0) := by
      rw [digestLaw, PMF.map_comp]
      congr 1
      funext ν
      simp [lazyLeafLaw, hq, MerkleTree.leafDigest, chainOracle]
    have hI : (PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map (mixLeaf VE H x prv₀ d q) =
        (PMF.uniformOfFintype (Digest k)).map (Prod.mk fun _ => 0) := by
      have h1 : (PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map (mixLeaf VE H x prv₀ d q) =
          ((PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map Prod.snd).map
            (Prod.mk fun _ => 0) := by
        rw [PMF.map_comp]
        congr 1
        funext a
        simp [mixLeaf, hq]
      rw [h1, PMF.map_snd_uniformOfFintype]
    rw [hR, hI]
    exact (PMF.tvDist_map_le _ _ _).trans (SPBCS.tvDist_digestLaw_le_leafMax H _)

/-- The leaves and the slice of the one-proof draw. -/
abbrev LeafSlice : Type :=
  (M.Pos → MerkleSalt kN × Digest k) × (Bits (queryBits k kN kS L) → XOut k e)

end OneProof

variable (VR : M.ViewRead) {Pub : Type}

variable (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-- **The leaf digests of the simulated proof**: at an opened position, the leaf hash of its
Merkle salt and the column read off the view; the drawn digest elsewhere. -/
def jointLeaf (h : Query k kN kS L → Out k e) (x : X) (ch : Chs P t) (ν : M.Pos → MerkleSalt kN)
    (d : M.Pos → Digest k) (o : CausalView VR.MV) (q : M.Pos) : Digest k :=
  if q ∈ VR.posC x ch then MerkleTree.leafDigest h ⟨ν q, VR.colOf x ch o q⟩ else d q

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem jointLeaf_eq (h : Query k kN kS L → Out k e) (x : X) (ch : Chs P t)
    (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k) (o : CausalView VR.MV) :
    M.jointLeaf VR h x ch ν d o = fun q =>
      if q ∈ VR.posC x ch then MerkleTree.leafDigest h ⟨ν q, VR.colOf x ch o q⟩ else d q :=
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- The leaf digests read the oracle only at `leaf` queries. -/
theorem jointLeaf_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b)) (x : X) (ch : Chs P t)
    (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k) (o : CausalView VR.MV) :
    M.jointLeaf VR h₁ x ch ν d o = M.jointLeaf VR h₂ x ch ν d o := by
  funext q
  simp only [jointLeaf, MerkleTree.leafDigest, hleaf]

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The average one-proof bound**: at most
`keyCollision (t.size n) k + overrun + δ + |Pos| · leafBound k kN L`. -/
theorem expect_oneProofBound_le (δ : ℝ≥0) :
    𝔼 H : Bits (queryBits k kN kS L) → XOut k e, M.oneProofBound δ H ≤
      (SPBCS.keyCollision (t.size n) k).toReal + M.overrun.toReal + δ +
        Fintype.card M.Pos * SPBCS.leafBound k kN L := by
  have hleaf : 𝔼 H : Bits (queryBits k kN kS L) → XOut k e,
      SPBCS.leafMax (fun b => outEquiv k e (H b)) ≤ SPBCS.leafBound k kN L := by
    rw [show (𝔼 H : Bits (queryBits k kN kS L) → XOut k e,
          SPBCS.leafMax (fun b => outEquiv k e (H b))) =
        𝔼 h : Bits (queryBits k kN kS L) → Digest k × (Fin e → Byte),
          Finset.univ.sup' Finset.univ_nonempty fun col : Bytes L =>
            PMF.tvDist (digestLaw (Prod.fst ∘ h) fun ν : MerkleSalt kN => Query.toBits (.leaf ν col))
              (PMF.uniformOfFintype (Digest k)) from
      Fintype.expect_equiv (Equiv.arrowCongr (Equiv.refl _) ((outEquiv k e).trans Out.equivProd))
        (fun H => SPBCS.leafMax (fun b => outEquiv k e (H b))) _ fun H => rfl]
    have hN : (Fintype.card (MerkleSalt kN) : ℝ) = 2 ^ (8 * kN) := by
      rw [show Fintype.card (MerkleSalt kN) = 2 ^ (8 * kN) from Out.card_digest]
      push_cast
      ring
    have hY : (Fintype.card (Digest k) : ℝ) = 2 ^ (8 * k) := by
      rw [Out.card_digest]
      push_cast
      ring
    have h := expect_sup'_tvDist_digestLaw_fst_le (X := Bits (queryBits k kN kS L)) (Y := Digest k)
      (Z := Fin e → Byte) (N := MerkleSalt kN) (C := Bytes L)
      (e := fun (col : Bytes L) (ν : MerkleSalt kN) => Query.toBits (Query.leaf ν col : Query k kN kS L))
      (fun c => fun a b hab => by simpa using Query.toBits.injective hab)
    rw [hN, hY] at h
    exact h
  simp only [oneProofBound, Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty,
    ← Finset.mul_expect]
  gcongr

end

end GordieHowe.SPBCS

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

end WF

/-! ### The keys of the built chains -/

section Build

variable (h : Query k kN kS L → Out k e) (ss : SaltedStatement kS X)
  (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)

/-- **The built chains** of all leaves (`SPBCS.buildLeaf`, full length). -/
def buildChains : M.Chains := fun q => M.buildLeaf h ρ wr ld q (n q.label)

/-- **The final digests of the built chains**: the solution of their equation. -/
def buildFinals : Mg.Site → Digest k := M.finalsWith h ss (M.buildChains h ρ wr ld)

/-- **The key of challenge `c` on the built chains**: the digest of its chain input, with the
built chains and the built final digests. -/
def buildKey (c : ChIdx P t) : Digest k :=
  M.key h ss (M.buildChains h ρ wr ld) (M.buildFinals h ss ρ wr ld) c.leaf
    (M.buildLeaf h ρ wr ld c.leaf c.idx.1)

/-- **The built assignment list**: each challenge's stream at the `xof` input of its key on the
built chains and the salt, in global round order. -/
def buildAssign : List (Assignment (Query k kN kS L) (Out k e)) :=
  (SPBCS.chList P t).map fun c => ⟨.xof (M.buildKey h ss ρ wr ld c) ss.salt, ρ c⟩

theorem chainWF_buildChains (q : t.Leaf) : chainWF (P q.label) (M.buildChains h ρ wr ld q) :=
  M.chainWF_buildLeaf h ρ wr ld q le_rfl

theorem length_buildChains (q : t.Leaf) : (M.buildChains h ρ wr ld q).length = n q.label :=
  M.length_buildLeaf h ρ wr ld q _

/-- **The built chains have a write at every prover round.** -/
theorem writesAll_buildChains : M.WritesAll (M.buildChains h ρ wr ld) := by
  intro p i
  rw [buildChains, M.buildLeaf_getElem? h ρ wr ld p _ i.1.1 i.1.2]
  unfold SPBCS.buildItem
  rw [dite_eq_left i.1.2, dite_eq_left i.2]
  exact ⟨_, rfl⟩

/-- **The chain input of a challenge on the built chains is well formed.** -/
theorem wf_buildRound (fs : Mg.Site → Digest k) (c : ChIdx P t) :
    (roundContent ss (M.buildChains h ρ wr ld) fs c.leaf (M.buildLeaf h ρ wr ld c.leaf c.idx.1)).WF n
      fun j => chainWF (P j) :=
  wf_roundContent_of fs (M.chainWF_buildChains h ρ wr ld) (M.length_buildChains h ρ wr ld)
    (M.chainWF_buildLeaf h ρ wr ld _ c.idx.1.2.le) (by rw [SPBCS.length_buildLeaf]; exact c.idx.1.2)

/-- **A final input on the built chains is well formed.** -/
theorem wf_buildFinal (fs : Mg.Site → Digest k) (s : Mg.Site) :
    (finalContent ss (M.buildChains h ρ wr ld) fs s).WF n fun j => chainWF (P j) :=
  wf_finalContent_of fs (M.chainWF_buildChains h ρ wr ld) (M.length_buildChains h ρ wr ld) s

variable {h₁ h₂ : Query k kN kS L → Out k e}

/-- The built chains read the oracle only at `leaf` and `node` queries. -/
theorem buildChains_congr (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b))
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r)) :
    M.buildChains h₁ ρ wr ld = M.buildChains h₂ ρ wr ld :=
  funext fun q => M.buildLeaf_congr hleaf hnode ρ wr ld q _

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
  rw [hch, hfin, M.buildLeaf_congr hleaf hnode, htr _ (by
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
    (c : ChIdx P t) (hρ : ∀ j : ChIdx P t, SPBCS.gIdx j < SPBCS.gIdx c → ρ j = ρ' j) :
    M.buildKey h ss ρ (SPBCS.honestWrite' E prv x ρ)
        (SPBCS.honestDigest E prv x ν h ρ) c =
      M.buildKey h ss ρ' (SPBCS.honestWrite' E prv x ρ')
        (SPBCS.honestDigest E prv x ν h ρ') c := by
  have hbefore : ∀ q : t.Leaf, q.Before c.leaf →
      M.buildChains h ρ (SPBCS.honestWrite' E prv x ρ)
          (SPBCS.honestDigest E prv x ν h ρ) q =
        M.buildChains h ρ' (SPBCS.honestWrite' E prv x ρ')
          (SPBCS.honestDigest E prv x ν h ρ') q := fun q hq =>
    SPBCS.buildLeaf_honest_congr E prv x ν h q _ fun j hj => hρ j (by
      have := Leaf.Before.off_add_le n hq
      unfold SPBCS.gIdx at hj ⊢
      omega)
  unfold buildKey
  rw [SPBCS.buildLeaf_honest_congr E prv x ν h c.leaf c.idx.1 fun j hj => hρ j hj]
  refine congrFun (key_congr (fun q hq => hbefore q hq.1) fun s hs => ?_) _
  exact finalsWith_congr_of_hides hbefore hs

/-- **The key equation of the honest streams**: the stream of challenge `c` is the oracle at the
`xof` input of its built key at the streams `ρ` and the salt. -/
noncomputable def keyStep (ρ : ChIdx P t → Out k e) : ChIdx P t → Out k e := fun c =>
  h (.xof (M.buildKey h ⟨σ, x⟩ ρ (SPBCS.honestWrite' E prv x ρ)
    (SPBCS.honestDigest E prv x ν h ρ) c) σ)

theorem rankCausal_keyStep : RankCausal (keyStep E prv x ν σ h) SPBCS.gIdx :=
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
  congrFun ((rankCausal_keyStep E prv x ν σ h).iterate_fixed _ SPBCS.gIdx_lt_size) c

/-- **The honest streams are the only solution of the key equation.** -/
theorem eq_honestStreams {ρ : ChIdx P t → Out k e} (hρ : ∀ c, ρ c = keyStep E prv x ν σ h ρ c) :
    ρ = honestStreams E prv x ν σ h :=
  (rankCausal_keyStep E prv x ν σ h).eq_iterate _ SPBCS.gIdx_lt_size hρ

/-- **The honest chains**: the built chains at the honest streams, writes and leaf digests. -/
noncomputable def honestBuiltChains : M.Chains :=
  M.buildChains h (honestStreams E prv x ν σ h)
    (SPBCS.honestWrite' E prv x (honestStreams E prv x ν σ h))
    (SPBCS.honestDigest E prv x ν h (honestStreams E prv x ν σ h))

/-- The honest queried positions: the query phase's positions on the honest chains at the
challenges read from the honest streams. -/
noncomputable def honestBuiltPos {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x) : List M.Pos :=
  Q.pos (honestBuiltChains E prv x ν σ h) (M.chOfStreams (honestStreams E prv x ν σ h))

/-- **The honest proof of the spBCS compiler** (paper `prot:generalized-bcs`): the built
proof at the honest streams, writes and leaf digests, with the honest leaves opened at the queried
positions. -/
noncomputable def honestProof {V : X → FullTr P t → Bool} (Q : M.IOPQueries V x) : M.NIProof :=
  M.buildProof h σ (SPBCS.honestWrite' E prv x (honestStreams E prv x ν σ h))
    (SPBCS.honestDigest E prv x ν h (honestStreams E prv x ν σ h))
    (SPBCS.honestOpened E prv x ν (honestStreams E prv x ν σ h) (honestBuiltPos E prv x ν σ h Q))
    (honestBuiltPos E prv x ν σ h Q)

variable {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x}

/-- **The honest proof at the positions of the view law.** -/
theorem honestProof_eq_buildProof (VE : M.ViewEncoder E Qs) :
    honestProof E prv x ν σ h (Qs x) =
      M.buildProof h σ (SPBCS.honestWrite' E prv x (honestStreams E prv x ν σ h))
        (SPBCS.honestDigest E prv x ν h (honestStreams E prv x ν σ h))
        (SPBCS.honestOpened E prv x ν (honestStreams E prv x ν σ h)
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
  have hd : ∀ ρ, SPBCS.honestDigest E prv x ν h ρ = SPBCS.honestDigest E prv x ν h' ρ :=
    fun ρ => by
      funext q
      simp only [SPBCS.honestDigest, MerkleTree.leafDigest, hleaf]
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
  have hd : ∀ ρ, SPBCS.honestDigest E prv x ν h ρ = SPBCS.honestDigest E prv x ν h' ρ :=
    fun ρ => by
      funext q
      simp only [SPBCS.honestDigest, MerkleTree.leafDigest, hleaf]
  have hs : honestStreams E prv x ν σ h = honestStreams E prv x ν σ h' := by
    unfold honestStreams
    rw [keyStep_congr_slice E prv x ν σ hh]
  have hch : ∀ ρ wr ld, M.buildChains h ρ wr ld = M.buildChains h' ρ wr ld := fun ρ wr ld =>
    M.buildChains_congr ρ wr ld hleaf hnode
  simp only [honestProof, honestBuiltPos, honestBuiltChains, hs, hd, hch, M.buildProof_congr hleaf hnode]

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
    chainW prv x (SPBCS.honestWrite E ν h) (answers prv x σ E ν h) p r =
      M.buildLeaf h (runStreams E prv x ν σ h)
        (SPBCS.honestWrite' E prv x (runStreams E prv x ν σ h))
        (SPBCS.honestDigest E prv x ν h (runStreams E prv x ν σ h)) p r
  | 0 => rfl
  | r + 1 => by
    rw [chainW, SPBCS.buildLeaf, chainW_honest_eq p r]
    congr 2
    unfold itemW SPBCS.buildItem
    split_ifs with hr hd
    · rw [chOfW_answers]
      exact congrArg (fun w => (Item.write ⟨⟨⟨r, hr⟩, hd⟩, w⟩ : Item k (M.comp p.label).W))
        (SPBCS.honestWrite_eq E prv x ν h _ p ⟨⟨r, hr⟩, hd⟩)
    · rfl
    · rfl

theorem chsW_honest_eq :
    chsW prv x (SPBCS.honestWrite E ν h) (answers prv x σ E ν h) =
      M.buildChains h (runStreams E prv x ν σ h)
        (SPBCS.honestWrite' E prv x (runStreams E prv x ν σ h))
        (SPBCS.honestDigest E prv x ν h (runStreams E prv x ν σ h)) :=
  funext fun p => chainW_honest_eq E prv x ν σ h p _

/-- **The streams of the honest prover's run solve the key equation.** -/
theorem runStreams_eq (c : ChIdx P t) :
    runStreams E prv x ν σ h c = keyStep E prv x ν σ h (runStreams E prv x ν σ h) c := by
  have hfs := finalsWith_chsW (M := M) prv x σ (SPBCS.honestWrite E ν) h
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
      SPBCS.honestOpened E prv x ν (honestStreams E prv x ν σ h)
        (honestBuiltPos E prv x ν σ h Q) := by
    rw [honestLeaves, hpos, SPBCS.honestOpened, hch]
    exact List.map_congr_left fun q _ => SPBCS.leafFn_val E ν _ _ _ _ _
  simp only [prove, honestProof, SPBCS.buildProof, hleaves, hpos]
  congr 1
  · funext p i
    rw [hch, SPBCS.honestWrite_eq E prv x ν h]
  · funext τ
    simp only [MerkleFormat.path, MerkleTree.treeDigest, hch]
    rw [SPBCS.root_leafFn E prv x ν h]

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
    M.Bounded B (M.buildProof h σ wr ld ops ps) := by
  refine ⟨hops, fun τ => ?_⟩
  simp only [SPBCS.buildProof, List.length_map]
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
  bounded_buildProof _ _ _ _ _ _ (by rw [SPBCS.honestOpened, List.length_map]; exact hpos _ _)
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
    SPBCS.Internal.encodeTotal M B (prove (honest w a.coins.iop) x a.salt E a.coins.merkleSalts (chainOracle H) (Qs x))
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
  ⟨some (SPBCS.Internal.encodeTotal M B (M.buildProof (chainOracle H') σ wr ld ops ps)),
    H'.reprogram ((M.buildAssign (chainOracle H') ⟨σ, x⟩ ρ wr ld).map fun qa =>
      ⟨Query.toBits qa.input, (outEquiv k e).symm qa.output⟩)⟩

/-- The honest reply on the slice `F` of `σ`. -/
noncomputable def realOut (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) (F : Bits (queryBits k kN kS L) → XOut k e) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  let H' := replaceSlice M.saltOfBits σ H F
  ⟨some (SPBCS.Internal.encodeTotal M B (prove prv₀ x σ E ν (chainOracle H') (Qs x))), H'⟩

/-- The lazily sampled reply: the honest proof built from the streams of the draw `d`, and the
slice of `d` reprogrammed at the keys with those streams. -/
noncomputable def lazyOut (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) (d : SPBCS.StreamDraw k kN kS L e P t) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  outB B H x σ d.slice d.streams (SPBCS.honestWrite' E prv₀ x d.streams)
    (SPBCS.honestDigest E prv₀ x ν (chainOracle H) d.streams)
    (SPBCS.honestOpened E prv₀ x ν d.streams (VE.posC x (M.chOfStreams d.streams)))
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
  (PMF.uniformOfFintype (M.ProverCoins R × SPBCS.StreamDraw k kN kS L e P t)).map
    fun a => lazyOut VE B H x σ (prv a.1.iop) a.1.merkleSalts a.2

/-- The reply of `innerD` at a draw. -/
noncomputable def mixOut (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (d : SPBCS.StreamDraw k kN kS L e P t) (z : M.Pos → MerkleSalt kN × Digest k) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  outB B H x σ d.slice d.streams (SPBCS.honestWrite' E prv₀ x d.streams)
    (SPBCS.mixDigest VE H x prv₀ (fun q => (z q).1) (fun q => (z q).2) d.streams)
    (SPBCS.honestOpened E prv₀ x (fun q => (z q).1) d.streams
      (VE.posC x (M.chOfStreams d.streams)))
    (VE.posC x (M.chOfStreams d.streams))

/-- `innerD`: as `innerL`, with the digests of the unopened leaves uniform. -/
noncomputable def innerD (σ : FiatShamirSalt kS) :
    PMF (EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e)) :=
  (PMF.uniformOfFintype (M.LeafDraw R)).map fun a => mixOut VE B H x σ (prv a.iop) a.draw a.leaves

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
    outB B H x σ F ρ (SPBCS.honestWrite' E prv₀ x ρ) (SPBCS.mixDigest VE H x prv₀ ν d ρ)
      (SPBCS.honestOpened E prv₀ x ν ρ (VE.posC x (M.chOfStreams ρ)))
      (VE.posC x (M.chOfStreams ρ)) =
      outViewAt VE B H x σ F (M.chOfStreams ρ) ρ ν d
        (VE.MV.view (prv₀.run x (M.chOfStreams ρ))) := by
  set ch := M.chOfStreams ρ
  set tr := prv₀.run x ch
  obtain ⟨chs, hl⟩ : ∃ chs : (p : t.Leaf) → M.Items p, (Qs x).pos chs ch = VE.posC x ch :=
    ⟨_, VE.pos_eq x _ ch
      (M.writesAll_buildChains (chainOracle H) ρ (SPBCS.honestWrite' E prv₀ x ρ) d)⟩
  have hcol : ∀ q ∈ VE.posC x ch, VE.colOf x ch (VE.MV.view tr) q =
      (E q.leaf.label).cols q.pos.msg (tr q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf := fun q hq =>
    VE.colOf_obs x chs ch tr (CausalProver.challenges_run prv₀ x ch) q (hl ▸ hq)
  have hld : SPBCS.mixDigest VE H x prv₀ ν d ρ = fun q => if q ∈ VE.posC x ch then
      MerkleTree.leafDigest (chainOracle H) ⟨ν q, VE.colOf x ch (VE.MV.view tr) q⟩ else d q := by
    funext q
    simp only [SPBCS.mixDigest, SPBCS.honestDigest]
    split_ifs with hq
    · rw [hcol q hq]
    · rfl
  have hops : SPBCS.honestOpened E prv₀ x ν ρ (VE.posC x ch) =
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
    SPBCS.honestDigest E prv₀ x ν (chainOracle (sliceGlue (M := M) H σ Fo FX)) ρ =
      SPBCS.honestDigest E prv₀ x ν (chainOracle H) ρ := by
  funext q
  simp only [SPBCS.honestDigest, MerkleTree.leafDigest, sliceGlue_leaf]

/-- The built chains at the streams `ρX` (quantum-oracle answers). -/
noncomputable def lazyChains (ρX : ChIdx P t → XOut k e) : M.Chains :=
  M.buildChains (chainOracle H) (SPBCS.outs ρX)
    (SPBCS.honestWrite' E prv₀ x (SPBCS.outs ρX))
    (SPBCS.honestDigest E prv₀ x ν (chainOracle H) (SPBCS.outs ρX))

/-- The built chain of leaf `p` at the streams `ρX`. -/
noncomputable def lazyLeaf (ρX : ChIdx P t → XOut k e) (p : t.Leaf) (r : ℕ) : M.Items p :=
  M.buildLeaf (chainOracle H) (SPBCS.outs ρX)
    (SPBCS.honestWrite' E prv₀ x (SPBCS.outs ρX))
    (SPBCS.honestDigest E prv₀ x ν (chainOracle H) (SPBCS.outs ρX)) p r

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
    M.buildKey (chainOracle (sliceGlue (M := M) H σ Fo FX)) ⟨σ, x⟩ (SPBCS.outs ρX)
        (SPBCS.honestWrite' E prv₀ x (SPBCS.outs ρX))
        (SPBCS.honestDigest E prv₀ x ν (chainOracle H) (SPBCS.outs ρX)) c =
      lazyKey (E := E) H x σ Fo prv₀ ν c ρX := by
  have hleaf := sliceGlue_leaf (M := M) H σ Fo FX
  have hnode := sliceGlue_node (M := M) H σ Fo FX
  unfold buildKey buildFinals lazyKey lazyInput lazyFinals lazyChains lazyLeaf key
  rw [M.buildChains_congr _ _ _ hleaf hnode, M.buildLeaf_congr hleaf hnode,
    finalsWith_congr_oracle (h₂ := chainOracle (sliceGlue (M := M) H σ Fo 0))
      fun fs s => sliceGlue_transcript H σ Fo FX 0 _,
    sliceGlue_transcript_eq H σ Fo FX (by
      rw [M.querySalt_transcript_encode (M.wf_buildRound _ _ _ _ _ _ c)]
      rfl)]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem lazySol_eq (FX : Digest k → XOut k e) (c : ChIdx P t) :
    lazySol (E := E) H x σ Fo prv₀ ν FX c =
      FX (lazyKey (E := E) H x σ Fo prv₀ ν c (lazySol (E := E) H x σ Fo prv₀ ν FX)) := by
  have hρ : SPBCS.outs (lazySol (E := E) H x σ Fo prv₀ ν FX) =
      honestStreams E prv₀ x ν σ (chainOracle (sliceGlue (M := M) H σ Fo FX)) := by
    funext j
    simp [lazySol, SPBCS.outs]
  rw [lazySol, honestStreams_eq E prv₀ x ν σ _ c, keyStep, honestDigest_sliceGlue, ← hρ,
    buildKey_sliceGlue, sliceGlue_xof, Equiv.symm_apply_apply]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem lazyKey_causal (c : ChIdx P t) (ρX ρX' : ChIdx P t → XOut k e)
    (h : ∀ j, (SPBCS.chOrder P t).lt j c → ρX j = ρX' j) :
    lazyKey (E := E) H x σ Fo prv₀ ν c ρX = lazyKey (E := E) H x σ Fo prv₀ ν c ρX' := by
  rw [← buildKey_sliceGlue H x σ Fo prv₀ ν 0, ← buildKey_sliceGlue H x σ Fo prv₀ ν 0,
    ← honestDigest_sliceGlue H x σ Fo prv₀ ν 0, ← honestDigest_sliceGlue H x σ Fo prv₀ ν 0]
  exact buildKey_honest_congr E prv₀ x ν _ _ c fun j hj => by
    simp only [SPBCS.outs, h j hj]

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
  simp only [roundContent, Content.ownLength, SPBCS.length_buildLeaf] at ho
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
        {Fo | SPBCS.gIdx c < SPBCS.gIdx c' ∧ g (Fo (a Fo c)) = g (Fo (a Fo c'))} := by
    intro Fo hFo
    simp only [Set.mem_ofPred_eq, Function.Injective, not_forall] at hFo
    obtain ⟨c, c', heq, hne⟩ := hFo
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    rcases lt_or_gt_of_ne (fun he : SPBCS.gIdx c = SPBCS.gIdx c' =>
      hne (SPBCS.gIdx_injective he)) with h | h
    · exact ⟨c', c, h, heq⟩
    · exact ⟨c, c', h, heq.symm⟩
  calc ((PMF.uniformOfFintype (NX → XOut k e)).toOuterMeasure
        {Fo | ¬ Function.Injective fun c => lazyKey (E := E) H x σ Fo prv₀ ν c ρX}).toReal
      ≤ ((PMF.uniformOfFintype (NX → XOut k e)).toOuterMeasure (⋃ c' : ChIdx P t,
          ⋃ c : ChIdx P t, {Fo | SPBCS.gIdx c < SPBCS.gIdx c' ∧
            g (Fo (a Fo c)) = g (Fo (a Fo c'))})).toReal :=
        ENNReal.toReal_mono (by rw [PMF.toOuterMeasure_apply]; exact PMF.tsum_coe_indicator_ne_top _ _)
          (MeasureTheory.measure_mono hset)
    _ ≤ ∑ c' : ChIdx P t, ∑ c : ChIdx P t,
          ((PMF.uniformOfFintype (NX → XOut k e)).toOuterMeasure
            {Fo | SPBCS.gIdx c < SPBCS.gIdx c' ∧
              g (Fo (a Fo c)) = g (Fo (a Fo c'))}).toReal :=
        (PMF.toReal_toOuterMeasure_iUnion_le _ _).trans
          (Finset.sum_le_sum fun c' _ => PMF.toReal_toOuterMeasure_iUnion_le _ _)
    _ ≤ ∑ c' : ChIdx P t, ∑ c : ChIdx P t,
          (if SPBCS.gIdx c < SPBCS.gIdx c' then ((2 : ℝ) ^ (8 * k))⁻¹ else 0) :=
        Finset.sum_le_sum fun c' _ => Finset.sum_le_sum fun c _ => by
          split_ifs with h
          · rw [← hpair c c' (fun he => by subst he; omega)]
            exact ENNReal.toReal_mono
              (by rw [PMF.toOuterMeasure_apply]; exact PMF.tsum_coe_indicator_ne_top _ _)
              (MeasureTheory.measure_mono fun Fo hFo => hFo.2)
          · simp [h]
    _ = (∑ c' : ChIdx P t, ((Finset.univ.filter fun c : ChIdx P t =>
          SPBCS.gIdx c < SPBCS.gIdx c').card : ℝ)) * ((2 : ℝ) ^ (8 * k))⁻¹ := by
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_mul]
    _ ≤ ((t.size n).choose 2 : ℝ) * ((2 : ℝ) ^ (8 * k))⁻¹ :=
        mul_le_mul_of_nonneg_right (SPBCS.sum_card_earlier_le P t) (by positivity)
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
  ⟨some (SPBCS.Internal.encodeTotal M B (M.buildProof (chainOracle H) σ
      (SPBCS.honestWrite' E prv₀ x (SPBCS.outs q.2))
      (SPBCS.honestDigest E prv₀ x ν (chainOracle H) (SPBCS.outs q.2))
      (SPBCS.honestOpened E prv₀ x ν (SPBCS.outs q.2)
        (VE.posC x (M.chOfStreams (SPBCS.outs q.2))))
      (VE.posC x (M.chOfStreams (SPBCS.outs q.2))))),
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
    M.buildProof_congr (sliceGlue_leaf H σ Fo FX) (sliceGlue_node H σ Fo FX),
    honestDigest_sliceGlue (E := E) H x σ Fo prv₀ ν FX]
  have hρ : honestStreams E prv₀ x ν σ (chainOracle (sliceGlue (M := M) H σ Fo FX)) =
      SPBCS.outs (lazySol (E := E) H x σ Fo prv₀ ν FX) := by
    funext j
    simp [lazySol, SPBCS.outs]
  rw [hρ]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The lazily sampled reply on the glued slice** is `glueOut` with the `xof` part
reprogrammed at the lazy keys. -/
theorem map_lazyOut_eq_glue (σ : FiatShamirSalt kS) (prv₀ : CausalProver P t X)
    (ν : M.Pos → MerkleSalt kN) :
    (PMF.uniformOfFintype (SPBCS.StreamDraw k kN kS L e P t)).map
        (lazyOut VE B H x σ prv₀ ν) =
      (PMF.uniformOfFintype ({b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} →
        XOut k e)).bind fun Fo =>
        ((PMF.uniformOfFintype ((Digest k → XOut k e) × (ChIdx P t → XOut k e))).map fun q =>
          (q.1.reprogram ((SPBCS.chList P t).map fun c =>
            ⟨lazyKey (E := E) H x σ Fo prv₀ ν c q.2, q.2 c⟩), q.2)).map
          (glueOut VE B H x σ Fo prv₀ ν) := by
  set es := splitAlong (Y' := XOut k e) (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)
  let eI : ({b // b ∉ Set.range (SPBCS.xofEmb (k := k) (kN := kN) (L := L) σ)} → XOut k e) ×
      ((Digest k → XOut k e) × (ChIdx P t → XOut k e)) ≃
        SPBCS.StreamDraw k kN kS L e P t :=
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
  rw [hH, M.buildProof_congr (sliceGlue_leaf H σ Fo FX) (sliceGlue_node H σ Fo FX)]
  congr 2
  rw [buildAssign, List.map_map, ← reprogram_sliceGlue H σ Fo FX, List.map_map]
  refine congrArg (Function.reprogram _) (List.map_congr_left fun c _ => ?_)
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [show (fun j => outEquiv k e (ρX j)) = SPBCS.outs ρX from rfl, buildKey_sliceGlue]
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
      (PMF.uniformOfFintype (SPBCS.StreamDraw k kN kS L e P t)).map
        (lazyOut VE B H x σ prv₀ ν) := by
  rw [map_realOut_eq_glue VE B H x σ prv₀ ν, map_lazyOut_eq_glue VE B H x σ prv₀ ν]
  refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
  refine (Finset.expect_le_expect fun Fo _ => (PMF.tvDist_map_le _ _ _).trans
    (@tvDist_lazy_le (Digest k) (XOut k e) _ _ _ _ (ChIdx P t) _ _
      (SPBCS.chOrder P t) _ (SPBCS.chList P t) SPBCS.nodup_chList
      SPBCS.mem_chList
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
      (PMF.uniformOfFintype (SPBCS.StreamDraw k kN kS L e P t)).map
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
    (d : SPBCS.StreamDraw k kN kS L e P t) (z : M.Pos → MerkleSalt kN × Digest k) :
    EnvReply (M.Response B) (Bits (queryBits k kN kS L) → XOut k e) :=
  outB B H x σ d.slice d.streams (SPBCS.honestWrite' E prv₀ x d.streams) (fun q => (z q).2)
    ((VE.posC x (M.chOfStreams d.streams)).map fun q =>
      MerkleLeaf.mk (z q).1 (SPBCS.honestCol (E := E) x prv₀ d q))
    (VE.posC x (M.chOfStreams d.streams))

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- `innerL` as independent per-position laws given the prover's coins and the draw. -/
theorem innerL_eq_pi (σ : FiatShamirSalt kS) :
    innerL VE B H x prv σ =
      (PMF.uniformOfFintype (R × SPBCS.StreamDraw k kN kS L e P t)).bind fun o =>
        (PMF.pi fun q => (PMF.uniformOfFintype (MerkleSalt kN)).map
          (SPBCS.lazyLeafLaw VE H x (prv o.1) o.2 q)).map (leafOut VE B H x σ (prv o.1) o.2) := by
  let eq : M.ProverCoins R × SPBCS.StreamDraw k kN kS L e P t ≃
      (R × SPBCS.StreamDraw k kN kS L e P t) × (M.Pos → MerkleSalt kN) :=
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
      simp [SPBCS.lazyLeafLaw, hq, SPBCS.honestDigest, SPBCS.honestCol]
  · exact List.map_congr_left fun q hq => by
      simp [SPBCS.lazyLeafLaw, hq, SPBCS.honestCol]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- `innerD` as independent per-position laws given the prover's coins and the draw. -/
theorem innerD_eq_pi (σ : FiatShamirSalt kS) :
    innerD VE B H x prv σ =
      (PMF.uniformOfFintype (R × SPBCS.StreamDraw k kN kS L e P t)).bind fun o =>
        (PMF.pi fun q => (PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map
          (SPBCS.mixLeaf VE H x (prv o.1) o.2 q)).map (leafOut VE B H x σ (prv o.1) o.2) := by
  let eq : M.LeafDraw R ≃ (R × SPBCS.StreamDraw k kN kS L e P t) ×
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
      simp [SPBCS.mixLeaf, hq, SPBCS.mixDigest, SPBCS.honestDigest,
        SPBCS.honestCol]
  · exact List.map_congr_left fun q hq => by simp [SPBCS.mixLeaf, hq, SPBCS.honestCol]

/-- **The unopened leaves**: one leaf distance per position. -/
theorem tvDist_innerL_innerD_le (σ : FiatShamirSalt kS) :
    innerL VE B H x prv σ ≈[Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b))]
      (innerD VE B H x prv σ) := by
  classical
  rw [innerL_eq_pi VE B H x prv σ, innerD_eq_pi VE B H x prv σ]
  refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
  have hpos : ∀ o : R × SPBCS.StreamDraw k kN kS L e P t, PMF.tvDist
      (PMF.pi fun q => (PMF.uniformOfFintype (MerkleSalt kN)).map
        (SPBCS.lazyLeafLaw VE H x (prv o.1) o.2 q))
      (PMF.pi fun q => (PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map
        (SPBCS.mixLeaf VE H x (prv o.1) o.2 q)) ≤
        Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b)) := fun o => by
    refine (PMF.tvDist_pi_le _ _).trans ?_
    calc ∑ q, PMF.tvDist ((PMF.uniformOfFintype (MerkleSalt kN)).map
            (SPBCS.lazyLeafLaw VE H x (prv o.1) o.2 q))
          ((PMF.uniformOfFintype (MerkleSalt kN × Digest k)).map
            (SPBCS.mixLeaf VE H x (prv o.1) o.2 q))
        ≤ ∑ _q : M.Pos, SPBCS.leafMax (fun b => outEquiv k e (H b)) :=
          Finset.sum_le_sum fun q _ =>
            SPBCS.tvDist_lazyLeafLaw_mixLeaf_le VE H x (prv o.1) o.2 q
      _ = Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc 𝔼 o : R × SPBCS.StreamDraw k kN kS L e P t, PMF.tvDist _ _ ≤
        𝔼 _o : R × SPBCS.StreamDraw k kN kS L e P t,
          (Fintype.card M.Pos * SPBCS.leafMax (fun b => outEquiv k e (H b))) :=
        Finset.expect_le_expect fun o _ => (PMF.tvDist_map_le _ _ _).trans (hpos o)
    _ = _ := Finset.expect_const Finset.univ_nonempty _

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- `innerD` as a draw of the leaves and the slice, then of the streams, then of the prover's
coins. -/
theorem innerD_eq_bind_streams (σ : FiatShamirSalt kS) :
    innerD VE B H x prv σ =
      (PMF.uniformOfFintype M.LeafSlice).bind fun q =>
        (PMF.uniformOfFintype (ChIdx P t → Out k e)).bind fun ρ =>
          (PMF.uniformOfFintype R).map fun r => outViewAt VE B H x σ q.2 (M.chOfStreams ρ) ρ
            (fun p => (q.1 p).1) (fun p => (q.1 p).2)
            (VE.MV.view ((prv r).run x (M.chOfStreams ρ))) := by
  let eq : M.LeafDraw R ≃ (M.LeafSlice × (ChIdx P t → Out k e)) × R :=
    { toFun := fun a => (((a.leaves, a.draw.slice), a.draw.streams), a.iop)
      invFun := fun b => ⟨b.2, ⟨b.1.1.2, b.1.2⟩, b.1.1.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [innerD, ← PMF.map_uniformOfFintype_equiv eq.symm, PMF.map_comp,
    PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind,
    PMF.uniformOfFintype_prod_eq_bind (β := M.LeafSlice), PMF.bind_bind]
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
    ⟨SPBCS.Internal.encodeTotal M B (M.buildProof (chainOracle H) σ wr (M.jointLeaf VR (chainOracle H) x ch ν d o)
        ((VR.posC x ch).map fun q => ⟨ν q, VR.colOf x ch o q⟩) (VR.posC x ch)),
      (M.buildAssign (chainOracle H) ⟨σ, x⟩ ρ wr (M.jointLeaf VR (chainOracle H) x ch ν d o)).map
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
    simp only [niJointSimulator, jointRun, SPBCS.ViewEncoder.toViewRead]
    rcases VE.writesOf x (Sim.sim (pub x) s.coins.sim).challenges (Sim.sim (pub x) s.coins.sim) with
      _ | wr
    · simp only [Option.elim_none]
    simp only [Option.elim_some, buildAssign, M.jointLeaf_congr _ hleaf,
      M.buildProof_congr hleaf hnode]
    congr 3
    funext c
    rw [M.buildKey_congr _ _ _ _ hleaf hnode (fun b hb => hh _ (Or.inr hb))]
  run_salt H x s a ha := by
    simp only [niJointSimulator, jointRun, SPBCS.ViewEncoder.toViewRead] at ha
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
  simp only [Option.elim_some, SPBCS.jointLeaf_eq, leafDigest_replaceSlice]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (B) in
/-- `innerSJ` as a draw of the leaves and the slice, then of the joint simulator's view, then of
the streams by preimage. -/
theorem innerSJ_eq_bind (σ : FiatShamirSalt kS) :
    innerSJ B VE pub Sim T H x σ =
      (PMF.uniformOfFintype M.LeafSlice).bind fun q =>
        (Sim.law (pub x)).bind fun v => (Sampler.preLaw T v.challenges).map fun ρ =>
          outViewAt VE B H x σ q.2 v.challenges ρ (fun p => (q.1 p).1) (fun p => (q.1 p).2) v := by
  let eq : M.LeafSlice × (Sim.Coins × ∀ c, (T c).Coins) ≃
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
  have h := SPBCS.tvDist_obs_joint_le VE honest pub Sim T x hvzk hw fun ch ρ o =>
    PMF.pure (outViewAt VE B H x σ q.2 ch ρ (fun p => (q.1 p).1) (fun p => (q.1 p).2) o)
  simp only [← PMF.bind_pure_comp]
  exact h

variable (B) in
/-- **One merge proof on a fresh slice, at one salt**: the honest reply and the simulated
reply are within `oneProofBound δ H`. -/
theorem tvDist_innerR_innerSJ_le (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) {w : Wit}
    (hw : (x, w) ∈ rel) (σ : FiatShamirSalt kS) :
    (innerR (E := E) (Qs := Qs) B H x (honest w) σ) ≈[M.oneProofBound δ H]
      (innerSJ B VE pub Sim T H x σ) := by
  have h1 := tvDist_innerR_innerL_le VE B H x (honest w) σ
  have h2 := tvDist_innerL_innerD_le VE B H x (honest w) σ
  have h3 := tvDist_innerD_innerSJ_le B VE honest pub Sim T H x hvzk hw σ
  have t1 := PMF.tvDist_triangle (innerR (E := E) (Qs := Qs) B H x (honest w) σ)
    (innerL VE B H x (honest w) σ) (innerSJ B VE pub Sim T H x σ)
  have t2 := PMF.tvDist_triangle (innerL VE B H x (honest w) σ)
    (innerD VE B H x (honest w) σ) (innerSJ B VE pub Sim T H x σ)
  simp only [SPBCS.oneProofBound]
  linarith

variable (B) in
open Classical in
/-- **One merge proof is simulated on a fresh slice** at the bound `oneProofBound δ`.

Hypothesis: `hvzk`, honest-verifier zero knowledge of the composite (`CausalHVZK`, CY24
Definition 23.1.8) at the joint simulator `Sim`. -/
theorem sliceClose (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    SliceClose M.saltOfBits (fun x w => (x, w) ∈ rel) (M.niProverZKM B honest E Qs)
      (M.niJointSimulator VE.toViewRead B pub Sim T) (M.oneProofBound δ) where
  close H x w hw := by
    rw [realSlice_eq_bind B H x honest w, simSlice_joint_eq_bind B VE pub Sim T H x]
    refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
    calc 𝔼 σ, PMF.tvDist (innerR (E := E) (Qs := Qs) B H x (honest w) σ)
          (innerSJ B VE pub Sim T H x σ)
        ≤ 𝔼 _σ : FiatShamirSalt kS, M.oneProofBound δ H := Finset.expect_le_expect fun σ _ =>
          tvDist_innerR_innerSJ_le B VE honest pub Sim T H x hvzk hw σ
      _ = M.oneProofBound δ H := Finset.expect_const Finset.univ_nonempty _
  nonneg H := by
    have h1 := SPBCS.leafMax_nonneg (kN := kN) (L := L) H
    simp only [SPBCS.oneProofBound]
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
    simp only [SPBCS.oneProofBound, this]

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
  unfold SPBCS.zkError
  have hsalt : (Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    ring
  have hsqrt : √(Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (4 * kS) := by
    rw [hsalt, show 8 * kS = 4 * kS * 2 by ring, pow_mul, Real.sqrt_sq (by positivity)]
  have hE := M.expect_oneProofBound_le δ
  rw [hsqrt, hsalt]
  gcongr

end

end GordieHowe.SPBCS
