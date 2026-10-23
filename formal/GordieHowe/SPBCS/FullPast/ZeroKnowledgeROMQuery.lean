-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.ZeroKnowledgeROM
public import GordieHowe.Model.ROM.LeafZK
public import GordieHowe.Model.ROM.SaltedZK

@[expose] public section

/-!
# Query-counted zero knowledge of the compiler over a composition in the classical ROM

Zero knowledge of the compiled argument of a composition (`GordieHowe/SPBCS/FullPast/Model.lean`) against
classical adversaries all of whose queries are counted (`ROM.NIZK.ZeroKnowledgeQueryBounded`, Unruh
2017 Definition 6, p. 14, with classical adversaries): the honest prover `GordieHowe.SPBCS.niProverZKM`
and simulator `GordieHowe.SPBCS.niJointSimulator` of `GordieHowe.SPBCS.zeroKnowledgeROM`, with the leaf term
charged per query, over the challenges of all leaves. The error (`GordieHowe.SPBCS.Base.zkErrorROMQuery`) is

    Q t / 2^(8kS) + Q (Q - 1) / (2 · 2^(8kS))          (Fiat–Shamir salts)
    + Q · keyCollision (t.size n) k                     (lazy sampling of the streams)
    + Q (4 t U + 4 (Q U² + U)) / 2^(8kN)                (hidden leaf digests, `U = |Pos|`)
    + Q · (overrun + δ)                                 (the observation).

**The leaf kernel** (`leafKernel`): the honest reply built from fresh streams, with the digests of
the positions not opened at the challenges read from a value per position. The salt slot is the
Merkle salt of a `leaf` query (`leafSaltOfBits`); the only public salt is the default leaf's
(`defaultSalt`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

variable {M} [∀ j i, Nonempty ((P j).Challenge i)] {E : (j : ι) → (M.comp j).Encoder}
  {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) (B : ℕ)
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {Wit R : Type} [Fintype R] [Nonempty R]
  (honest : Wit → R → CausalProver P t X)

/-! ### Step 3: the uniform-digest kernel against the simulator -/

section Observation

variable {Pub : Type} (pub : X → Pub) {S : CausalJointSimulator VE.MV Pub} (T : M.Preimages)
  {rel : Set (X × Wit)} {δ : ℝ≥0}

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (M) in
/-- The digests of uniform values are uniform, with the further coins. -/
theorem map_digests_uniform :
    (PMF.uniformOfFintype (FiatShamirSalt kS × (M.Pos → MerkleSalt kN) × (M.Pos → XOut k e))).map
        (fun a => (a.1, a.2.1, fun p => (outEquiv k e (a.2.2 p)).digest)) =
      PMF.uniformOfFintype (FiatShamirSalt kS × (M.Pos → MerkleSalt kN) × (M.Pos → Digest k)) := by
  let eY : (M.Pos → XOut k e) ≃ (M.Pos → Digest k) × (M.Pos → Fin e → Byte) :=
    (Equiv.arrowCongr (Equiv.refl _) ((outEquiv k e).trans Out.equivProd)).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  let eA : FiatShamirSalt kS × (M.Pos → MerkleSalt kN) × (M.Pos → XOut k e) ≃
      (FiatShamirSalt kS × (M.Pos → MerkleSalt kN) × (M.Pos → Digest k)) ×
        (M.Pos → Fin e → Byte) :=
    { toFun := fun a => ((a.1, a.2.1, (eY a.2.2).1), (eY a.2.2).2)
      invFun := fun b => (b.1.1, b.1.2.1, eY.symm (b.1.2.2, b.2))
      left_inv := fun a => by simp
      right_inv := fun b => by simp }
  conv_rhs => rw [← PMF.map_fst_uniformOfFintype (β := M.Pos → Fin e → Byte),
    ← PMF.map_uniformOfFintype_equiv eA, PMF.map_comp]
  rfl

end Observation

/-! ### The theorem -/

variable (M) in
/-- **The query-counted zero-knowledge error of the composite in the classical random-oracle
model** at the HVZK error `δ`, `t` queries and `Q` proof queries:
`Q t / 2^(8kS) + Q (Q - 1) / (2 · 2^(8kS)) + Q · keyCollision (t.size n) k +
Q (4 t U + 4 (Q U² + U)) / 2^(8kN) + Q · (overrun + δ)` with `U = |Pos|`
(`zeroKnowledgeROMQuery`). -/
noncomputable def zkErrorROMQuery (δ : ℝ≥0) (tq Q : ℕ) : ℝ :=
  Q * tq / 2 ^ (8 * kS) + Q * (Q - 1) / (2 * 2 ^ (8 * kS)) +
    Q * (SPBCS.keyCollision (t.size n) k).toReal +
    Q * ((4 * tq * Fintype.card M.Pos + 4 * (Q * Fintype.card M.Pos ^ 2 + Fintype.card M.Pos)) /
      2 ^ (8 * kN)) + Q * (M.overrun.toReal + δ)

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : FullPast P t X k kN kS L e)

/-! ### Reading the oracle off the leaves -/

section Build

variable {h₁ h₂ : Query k kN kS L → Out k e}

/-- The leaf digests of a tree read the oracle only at the default leaf. -/
theorem leafDigestsOf_congr_default (hdef : ∀ c, h₁ (.leaf defaultSalt c) = h₂ (.leaf defaultSalt c))
    (ld : M.Pos → Digest k) (p : t.Leaf) (i : (P p.label).MessageIdx)
    (τ : Fin ((M.comp p.label).nTrees i)) :
    M.leafDigestsOf h₁ ld p i τ = M.leafDigestsOf h₂ ld p i τ := by
  funext j
  simp only [leafDigestsOf, defaultLeafDigest, MerkleTree.leafDigest]
  split_ifs
  · rfl
  · rw [show (fun _ : Fin kN => (0 : Byte)) = defaultSalt from rfl, hdef]

theorem nodeDigest_leafDigestsOf_congr_default
    (hdef : ∀ c, h₁ (.leaf defaultSalt c) = h₂ (.leaf defaultSalt c))
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r)) (ld : M.Pos → Digest k) (p : t.Leaf)
    (i : (P p.label).MessageIdx) (τ : Fin ((M.comp p.label).nTrees i)) :
    MerkleTree.nodeDigest h₁ ((M.comp p.label).nLeaves i τ) (M.leafDigestsOf h₁ ld p i τ) =
      MerkleTree.nodeDigest h₂ ((M.comp p.label).nLeaves i τ) (M.leafDigestsOf h₂ ld p i τ) := by
  funext j
  rw [M.leafDigestsOf_congr_default hdef, MerkleTree.nodeDigest_congr hnode]

theorem rootsOf_congr_default (hdef : ∀ c, h₁ (.leaf defaultSalt c) = h₂ (.leaf defaultSalt c))
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r)) (ld : M.Pos → Digest k) (p : t.Leaf)
    (i : (P p.label).MessageIdx) :
    M.rootsOf h₁ ld p i = M.rootsOf h₂ ld p i := by
  funext τ
  simp only [rootsOf, M.nodeDigest_leafDigestsOf_congr_default hdef hnode]

/-- **The built proof reads the oracle only at `node` queries and the default leaf**, the leaf
digests being given. -/
theorem buildProof_congr_default (hdef : ∀ c, h₁ (.leaf defaultSalt c) = h₂ (.leaf defaultSalt c))
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r)) (σ : FiatShamirSalt kS) (wr : M.RootWriteFn)
    (ld : M.Pos → Digest k) (ops : List (MerkleLeaf kN L)) (ps : List M.Pos) :
    M.buildProof h₁ σ wr ld ops ps = M.buildProof h₂ σ wr ld ops ps := by
  simp only [buildProof, M.nodeDigest_leafDigestsOf_congr_default hdef hnode,
    M.rootsOf_congr_default hdef hnode]

/-- The built chains read the oracle only at `node` queries and the default leaf. -/
theorem buildLeaf_congr_default (hdef : ∀ c, h₁ (.leaf defaultSalt c) = h₂ (.leaf defaultSalt c))
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r)) (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn)
    (ld : M.Pos → Digest k) (p : t.Leaf) (r : ℕ) :
    M.buildLeaf h₁ ρ wr ld p r = M.buildLeaf h₂ ρ wr ld p r := by
  have hroots : M.rootsOf h₁ ld = M.rootsOf h₂ ld :=
    funext fun p => funext (M.rootsOf_congr_default hdef hnode ld p)
  have hitem : M.buildItem h₁ ρ wr ld = M.buildItem h₂ ρ wr ld := by
    funext p r
    unfold buildItem
    rw [hroots]
  induction r with
  | zero => rfl
  | succ r ih => rw [buildLeaf, buildLeaf, ih, hitem]

end Build

/-! ### The leaf kernel -/

variable (P t k e kS) in
/-- **The further coins of the leaf kernel**: the Fiat–Shamir salt, the causal
prover's coins and one stream per challenge. -/
@[ext]
structure LeafMain (R : Type) where
  /-- The Fiat–Shamir salt. -/
  salt : FiatShamirSalt kS
  /-- The causal prover's coins. -/
  iop : R
  /-- The stream of each challenge. -/
  streams : ChIdx P t → Out k e

variable (P t k e kS) in
/-- The further coins as their three parts. -/
def LeafMain.equivProd (R : Type) :
    LeafMain k kS e P t R ≃ FiatShamirSalt kS × R × (ChIdx P t → Out k e) where
  toFun c := (c.salt, c.iop, c.streams)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (R : Type) [Fintype R] : Fintype (LeafMain k kS e P t R) :=
  Fintype.ofEquiv _ (LeafMain.equivProd k kS e P t R).symm

instance (R : Type) [Nonempty R] : Nonempty (LeafMain k kS e P t R) :=
  ⟨⟨Classical.arbitrary _, Classical.arbitrary _, fun _ => Classical.arbitrary _⟩⟩

variable {M} [∀ j i, Nonempty ((P j).Challenge i)] {E : (j : ι) → (M.comp j).Encoder}
  {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) (B : ℕ)
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {Wit R : Type} [Fintype R] [Nonempty R]
  (honest : Wit → R → CausalProver P t X)

/-! ### Step 1: the honest prover against the honest-digest kernel -/

variable (M) in
/-- **The coins of the lazily sampled honest reply after the Fiat–Shamir salt**: the
causal prover's coins, a stream per challenge, a Merkle salt per position and a value per position
(unused by the honest-digest kernel). -/
@[ext]
structure LazyCoins (R : Type) where
  /-- The causal prover's coins. -/
  iop : R
  /-- The stream of each challenge. -/
  streams : ChIdx P t → Out k e
  /-- The Merkle salt of each position. -/
  merkleSalts : M.Pos → MerkleSalt kN
  /-- The value of each position. -/
  digests : M.Pos → XOut k e

variable (M) in
/-- The lazy coins as their four parts. -/
def LazyCoins.equivProd (R : Type) : M.LazyCoins R ≃
    R × (ChIdx P t → Out k e) × (M.Pos → MerkleSalt kN) × (M.Pos → XOut k e) where
  toFun c := (c.iop, c.streams, c.merkleSalts, c.digests)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (R : Type) [Fintype R] : Fintype (M.LazyCoins R) :=
  Fintype.ofEquiv _ (LazyCoins.equivProd M R).symm

instance (R : Type) [Nonempty R] : Nonempty (M.LazyCoins R) :=
  ⟨⟨Classical.arbitrary _, fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _,
    fun _ => Classical.arbitrary _⟩⟩

variable (M) in
/-- The salted lazy coins as the leaf kernel's coins. -/
def lazyEquiv (R : Type) : SaltedCoins (FiatShamirSalt kS) (M.LazyCoins R) ≃
    ROM.NIZK.LeafCoins (LeafMain k kS e P t R) M.Pos (MerkleSalt kN) (XOut k e) where
  toFun c := ⟨⟨c.salt, c.coins.iop, c.coins.streams⟩, c.coins.merkleSalts, c.coins.digests⟩
  invFun c := ⟨c.main.salt, ⟨c.main.iop, c.main.streams, c.salts, c.digests⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- The value of a position at its honest leaf is the honest digest, so the mixed digests of the
honest-digest kernel are the honest digests. -/
theorem mixDigest_honestLeaf (O : Bits (queryBits k kN kS L) → XOut k e) (x : X)
    (prv : CausalProver P t X) (ν : M.Pos → MerkleSalt kN) (ρ : ChIdx P t → Out k e) :
    mixDigest VE O x prv ν (fun p => (outEquiv k e (O (Query.toBits (.leaf (ν p)
      ((E p.leaf.label).cols p.pos.msg (prv.run x (M.chOfStreams ρ) p.leaf p.pos.msg.1)
        p.pos.tree p.pos.leaf))))).digest) ρ =
      honestDigest E prv x ν (chainOracle O) ρ := by
  funext p
  simp only [mixDigest]
  split_ifs <;> rfl

end FullPast

end GordieHowe.SPBCS
