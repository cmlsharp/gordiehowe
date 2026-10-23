-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.Completeness
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.SPBCS.Merkle.LeafHidingAdaptive
public import GordieHowe.SPBCS.Extraction.LazySampling
public import GordieHowe.Model.QROM.SaltedZK
public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.SPBCS.Sampler.Preimage
public import GordieHowe.SPBCS.Merkle.TreeProg
public import GordieHowe.Model.IOP.CausalHVZK
public import GordieHowe.Model.QROM.SaltedZKProofQuery

@[expose] public section

/-!
# Zero knowledge: the series–parallel base model

Everlasting zero knowledge of the compiled argument of a composition
(`GordieHowe/SPBCS/FullPast/Model.lean`), in the quantum random-oracle model, from honest-verifier zero
knowledge of the composite's observation in the form of CY24 Definition 23.1.8, over the
challenges of all leaves. This file holds the pieces at the series–parallel base model
(`GordieHowe.SPBCS.FullPast`); the theorem for the spBCS compiler is `GordieHowe.SPBCS.everlastingZeroKnowledge`
(`GordieHowe/SPBCS/ZeroKnowledge.lean`). The argument:

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

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

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

noncomputable instance (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)] :
    Fintype (M.BProof B) := by
  classical
  haveI : ∀ (α : Type) [Fintype α] (m : ℕ), Fintype {l : List α // l.length ≤ m} := fun α _ m =>
    (List.finite_length_le α m).fintype
  refine Fintype.ofInjective (fun π : M.BProof B => (π.1.salt, π.1.writes,
    (⟨π.1.leaves, π.2.leaves_le⟩ : {l : List (MerkleLeaf kN L) // l.length ≤ B}),
    fun τ => (⟨π.1.paths τ, π.2.paths_le τ⟩ :
      {l : List (Digest k) // l.length ≤ M.opening.pathCap B}))) ?_
  rintro ⟨⟨s, w, l, p⟩, hπ⟩ ⟨⟨s', w', l', p'⟩, hπ'⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, hp⟩ := h
  have : p = p' := funext fun τ => congrArg Subtype.val (congrFun hp τ)
  subst this
  rfl

noncomputable instance (B : ℕ) : DecidableEq (M.BProof B) :=
  Classical.decEq _

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
abbrev ViewEncoder.toViewRead {M : Base P t X k kN kS L e} {E : (j : ι) → (M.comp j).Encoder}
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

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : FullPast P t X k kN kS L e)

/-- Boundedness of a proof is decidable. -/
instance (B : ℕ) (π : M.NIProof) : Decidable (M.Bounded B π) :=
  decidable_of_iff (π.leaves.length ≤ B ∧ ∀ τ, (π.paths τ).length ≤ M.opening.pathCap B)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.leaves_le, h.paths_le⟩⟩

namespace Internal

/-- **A proof device of the hybrid argument; never in a statement reachable from a headline**: a
proof as a response, the proof itself when it is in the format `B`, none otherwise. The hybrid
games of `GordieHowe/SPBCS/ZeroKnowledge.lean` and `GordieHowe/SPBCS/ZeroKnowledgeROMQuery.lean`
build their replies with it; within the format bounds it is the constructor of a bounded proof
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

/-- The honest chains have a write at every prover round. -/
theorem writesAll_honestChainsFullPast : M.WritesAll (honestChainsFullPast E prv x ν σ h) := by
  intro p i
  rw [honestChainsFullPast, leafChainW_getElem? prv x _ _ p _ i.1.1 i.1.2]
  unfold itemW
  rw [dite_eq_left i.1.2, dite_eq_left i.2]
  exact ⟨_, rfl⟩

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

end FullPast

end GordieHowe.SPBCS
