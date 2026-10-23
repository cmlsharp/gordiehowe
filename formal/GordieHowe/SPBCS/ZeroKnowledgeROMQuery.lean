-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.ZeroKnowledgeROM
public import GordieHowe.SPBCS.FullPast.ZeroKnowledgeROMQuery

@[expose] public section

/-!
# Query-counted zero knowledge of the spBCS compiler in the classical ROM

Zero knowledge of the spBCS compiler against classical adversaries all of whose queries are
counted (`ROM.NIZK.ZeroKnowledgeQueryBounded`, Unruh 2017 Definition 6, p. 14, with classical
adversaries): the prover `niProverZKM` and simulator `niJointSimulator` of
`GordieHowe.SPBCS.zeroKnowledgeROM`, with the leaf term charged per query. The argument is the compiler's
over the term (`GordieHowe/SPBCS/FullPast/ZeroKnowledgeROMQuery.lean`) with the merge chain inputs
(`buildAssign`, `saltOfBits`): the leaf kernel `leafKernel` replies with the honest proof built
from fresh streams, the digests of the positions not opened at the challenges read from a value
per position. The error is the compiler's `Base.zkErrorROMQuery δ`:

    Q t / 2^(8k) + Q (Q - 1) / (2 · 2^(8k)) + Q · keyCollision (t.size n) k
    + Q (4 t U + 4 (Q U² + U)) / 2^(8kN) + Q · (overrun + δ)          (`U = |Pos|`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

/-! ### Reading the oracle off the leaves -/

section Build

variable (ss : SaltedStatement kS X) (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn)
  (ld : M.Pos → Digest k) {h₁ h₂ : Query k kN kS L → Out k e}

/-- **A built key reads the oracle only at `node` and `transcript` queries and the default leaf**,
the leaf digests being given. -/
theorem buildKey_congr_default (hdef : ∀ c, h₁ (.leaf defaultSalt c) = h₂ (.leaf defaultSalt c))
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r)) (htr : ∀ b, h₁ (.transcript b) = h₂ (.transcript b))
    (c : ChIdx P t) :
    M.buildKey h₁ ss ρ wr ld c = M.buildKey h₂ ss ρ wr ld c := by
  have hch : M.buildChains h₁ ρ wr ld = M.buildChains h₂ ρ wr ld :=
    funext fun q => M.toFullPast.buildLeaf_congr_default hdef hnode ρ wr ld q _
  have hfin : M.buildFinals h₁ ss ρ wr ld = M.buildFinals h₂ ss ρ wr ld := by
    unfold buildFinals
    rw [hch]
    exact finalsWith_congr_oracle fun _ _ => htr _
  simp only [buildKey, key, hch, hfin, M.toFullPast.buildLeaf_congr_default hdef hnode, htr]

variable {ss ρ wr ld} in
/-- **The built assignment list reads the oracle only at queries other than `leaf` queries and the
default leaf.** -/
theorem buildAssign_congr_default (hdef : ∀ c, h₁ (.leaf defaultSalt c) = h₂ (.leaf defaultSalt c))
    (hnl : ∀ q : Query k kN kS L, q.leafSalt = none → h₁ q = h₂ q) :
    M.buildAssign h₁ ss ρ wr ld = M.buildAssign h₂ ss ρ wr ld := by
  simp only [buildAssign, M.buildKey_congr_default ss ρ wr ld hdef (fun l r => hnl _ rfl)
    (fun b => hnl _ rfl)]

variable {ss ρ wr ld} in
/-- The built assignment list programs only `xof` inputs at the salt of `ss`. -/
theorem exists_xof_of_mem_buildAssign {h : Query k kN kS L → Out k e}
    {qa : Assignment (Query k kN kS L) (Out k e)} (hqa : qa ∈ M.buildAssign h ss ρ wr ld) :
    ∃ κ, qa.input = .xof κ ss.salt := by
  simp only [buildAssign, List.mem_map] at hqa
  obtain ⟨c, -, rfl⟩ := hqa
  exact ⟨_, rfl⟩

end Build

/-! ### The leaf kernel -/

variable {M} [∀ j i, Nonempty ((P j).Challenge i)] {E : (j : ι) → (M.comp j).Encoder}
  {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) (B : ℕ)
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {Wit R : Type} [Fintype R] [Nonempty R]
  (honest : Wit → R → CausalProver P t X)

/-- **The merge reply built from fresh streams**: the honest proof of the causal prover `prv`
with the Merkle salts `ν`, built from the streams `ρ` on the oracle `O`, with the digest of each
position not opened at the challenges of `ρ` read from the value `dY` of the position, and each
stream at the `xof` input of its merge key. -/
noncomputable def leafRun (O : Bits (queryBits k kN kS L) → XOut k e) (x : X)
    (prv : CausalProver P t X) (σ : FiatShamirSalt kS) (ρ : ChIdx P t → Out k e)
    (ν : M.Pos → MerkleSalt kN) (dY : M.Pos → XOut k e) :
    NARG.SimOutput (Bits (queryBits k kN kS L)) (XOut k e) (M.Response B) :=
  ⟨FullPast.Internal.encodeTotal M.toFullPast B (M.toFullPast.buildProof (chainOracle O) σ (Base.honestWrite' E prv x ρ)
      (FullPast.mixDigest VE O x prv ν (fun p => (outEquiv k e (dY p)).digest) ρ)
      (Base.honestOpened E prv x ν ρ (VE.posC x (M.chOfStreams ρ)))
      (VE.posC x (M.chOfStreams ρ))),
    (M.buildAssign (chainOracle O) ⟨σ, x⟩ ρ (Base.honestWrite' E prv x ρ)
      (FullPast.mixDigest VE O x prv ν (fun p => (outEquiv k e (dY p)).digest) ρ)).map fun qa =>
        ⟨Query.toBits qa.input, (outEquiv k e).symm qa.output⟩⟩

/-- **The leaf kernel of the spBCS compiler** (module docstring): the reply `leafRun` at the
proof query's statement and the causal prover `honest` at the proof query's witness; the hidden positions
are those not opened at the challenges of the streams; the leaf input of a position with a salt is
the `leaf` query of that salt and the position's honest column. -/
noncomputable def leafKernel :
    ROM.NIZK.LeafKernel (Bits (queryBits k kN kS L)) (XOut k e) X Wit (M.Response B)
      (FullPast.LeafMain k kS e P t R) M.Pos (MerkleSalt kN) where
  run req O m ν dY := leafRun VE B O req.stmt (honest req.wit m.iop) m.salt m.streams ν dY
  hidden req m p := decide (p ∉ VE.posC req.stmt (M.chOfStreams m.streams))
  point req m p a := Query.toBits (.leaf a ((E p.leaf.label).cols p.pos.msg
    ((honest req.wit m.iop).run req.stmt (M.chOfStreams m.streams) p.leaf p.pos.msg.1)
    p.pos.tree p.pos.leaf))

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [Nonempty R] in
/-- **The laws of the merge leaf kernel**, for the Merkle salt slot and the default leaf's
salt. -/
theorem leafKernel_laws :
    (leafKernel VE B honest).Laws leafSaltOfBits {defaultSalt} where
  point_salt req m p a := by
    simp only [leafKernel, leafSaltOfBits_toBits]
    rfl
  run_digests req O m ν d d' h := by
    simp only [leafKernel, leafRun]
    have : FullPast.mixDigest VE O req.stmt (honest req.wit m.iop) ν
        (fun p => (outEquiv k e (d p)).digest) m.streams =
        FullPast.mixDigest VE O req.stmt (honest req.wit m.iop) ν
          (fun p => (outEquiv k e (d' p)).digest) m.streams := by
      funext p
      simp only [FullPast.mixDigest]
      split_ifs with hp
      · rfl
      · rw [h p (by simp [leafKernel, hp])]
    rw [this]
  run_salts req O m ν ν' d h := by
    have hν : ∀ p ∈ VE.posC req.stmt (M.chOfStreams m.streams), ν p = ν' p := fun p hp =>
      h p (by simp [leafKernel, hp])
    simp only [leafKernel, leafRun]
    have hmix : FullPast.mixDigest VE O req.stmt (honest req.wit m.iop) ν
        (fun p => (outEquiv k e (d p)).digest) m.streams =
        FullPast.mixDigest VE O req.stmt (honest req.wit m.iop) ν'
          (fun p => (outEquiv k e (d p)).digest) m.streams := by
      funext p
      simp only [FullPast.mixDigest, FullPast.honestDigest]
      split_ifs with hp
      · rw [hν p hp]
      · rfl
    have hop : Base.honestOpened E (honest req.wit m.iop) req.stmt ν m.streams
        (VE.posC req.stmt (M.chOfStreams m.streams)) =
        Base.honestOpened E (honest req.wit m.iop) req.stmt ν' m.streams
          (VE.posC req.stmt (M.chOfStreams m.streams)) :=
      List.map_congr_left fun p hp => by rw [hν p hp]
    rw [hmix, hop]
  run_oracle req O O' m ν d h := by
    have hq : ∀ q : Query k kN kS L, (q.leafSalt = none ∨
        (∃ a ∈ ({defaultSalt} : Finset (MerkleSalt kN)), q.leafSalt = some a) ∨
        ∃ p, (leafKernel VE B honest).hidden req m p = false ∧ q.leafSalt = some (ν p)) →
        chainOracle O q = chainOracle O' q := fun q hq' => by
      simp only [chainOracle]
      rw [h _ (by simpa only [leafSaltOfBits_toBits] using hq')]
    have hnl : ∀ q : Query k kN kS L, q.leafSalt = none → chainOracle O q = chainOracle O' q :=
      fun q hq' => hq q (Or.inl hq')
    have hdef : ∀ c, chainOracle O (.leaf defaultSalt c) = chainOracle O' (.leaf defaultSalt c) :=
      fun c => hq _ (Or.inr (Or.inl ⟨defaultSalt, Finset.mem_singleton_self _, rfl⟩))
    have hnode : ∀ l r, chainOracle O (.node l r) = chainOracle O' (.node l r) := fun l r =>
      hnl _ rfl
    have hmix : FullPast.mixDigest VE O req.stmt (honest req.wit m.iop) ν
        (fun p => (outEquiv k e (d p)).digest) m.streams =
        FullPast.mixDigest VE O' req.stmt (honest req.wit m.iop) ν
          (fun p => (outEquiv k e (d p)).digest) m.streams := by
      funext p
      simp only [FullPast.mixDigest, FullPast.honestDigest, MerkleTree.leafDigest]
      split_ifs with hp
      · rw [hq _ (Or.inr (Or.inr ⟨p, by simp [leafKernel, hp], rfl⟩))]
      · rfl
    simp only [leafKernel, leafRun]
    rw [hmix, M.toFullPast.buildProof_congr_default hdef hnode, M.buildAssign_congr_default hdef hnl]
  assignment_salt req O m ν d a ha := by
    simp only [leafKernel, leafRun, List.mem_map] at ha
    obtain ⟨qa, hqa, rfl⟩ := ha
    obtain ⟨κ, hκ⟩ := M.exists_xof_of_mem_buildAssign hqa
    rw [leafSaltOfBits_toBits, hκ]
    rfl

/-! ### Step 1: the honest prover against the honest-digest kernel -/

/-- **The lazily sampled merge reply** as a kernel on salted coins: the honest-digest kernel of
`leafKernel` through `lazyEquiv`. -/
noncomputable def lazyKernel :
    ROM.NIZK.Kernel (Bits (queryBits k kN kS L)) (XOut k e) X Wit (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) (M.toFullPast.LazyCoins R)) :=
  fun req O c => (leafKernel VE B honest).kL req O (M.toFullPast.lazyEquiv R c)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
open Classical in
/-- **The lazily sampled merge reply is local in its salt**, with the honest prover. -/
theorem saltedLocal_lazy :
    SaltedLocal M.saltOfBits (M.niProverZKM B honest E Qs).liftReq
      (lazyKernel VE B honest).toSimulator where
  prove_congr H H' r _ c hH := by
    simp only [NARG.ProverFn.liftReq, niProverZKM]
    rw [prove_eq_honestProof, prove_eq_honestProof,
      honestProof_congr_salt E (honest r.wit c.coins.iop) r.stmt c.coins.merkleSalts c.salt
      (Qs r.stmt) fun q hq => by
        simp only [chainOracle]
        rw [hH _ (by rw [M.saltOfBits_toBits]; exact hq)]]
    rfl
  run_congr H H' r s hH := by
    have hh : ∀ q, M.querySalt q = none ∨ M.querySalt q = some s.salt →
        chainOracle H q = chainOracle H' q := fun q hq => by
      simp only [chainOracle]
      rw [hH _ (by rw [M.saltOfBits_toBits]; exact hq)]
    have hleaf : ∀ a b, chainOracle H (.leaf a b) = chainOracle H' (.leaf a b) := fun a b =>
      hh _ (Or.inl rfl)
    have hnode : ∀ l r, chainOracle H (.node l r) = chainOracle H' (.node l r) := fun l r =>
      hh _ (Or.inl rfl)
    have hleafB : ∀ a b, H (Query.toBits (.leaf a b)) = H' (Query.toBits (.leaf a b)) :=
      fun a b => hH _ (Or.inl (by rw [M.saltOfBits_toBits]; rfl))
    simp only [ROM.NIZK.Kernel.toSimulator, lazyKernel, ROM.NIZK.LeafKernel.kL, leafKernel,
      leafRun, FullPast.lazyEquiv, Equiv.coe_fn_mk, hleafB]
    have hmix : ∀ d : M.Pos → Digest k, FullPast.mixDigest VE H r.stmt
        (honest r.wit s.coins.iop) s.coins.merkleSalts d s.coins.streams =
        FullPast.mixDigest VE H' r.stmt (honest r.wit s.coins.iop) s.coins.merkleSalts d
          s.coins.streams := fun d => by
      funext p
      simp only [FullPast.mixDigest, FullPast.honestDigest, MerkleTree.leafDigest, hleaf]
    rw [hmix, M.toFullPast.buildProof_congr hleaf hnode]
    congr 2
    simp only [buildAssign]
    congr 1
    funext c
    rw [M.buildKey_congr _ _ _ _ hleaf hnode (fun b hb => hh _ (Or.inr hb))]
  run_salt H r s a ha := by
    simp only [ROM.NIZK.Kernel.toSimulator, lazyKernel, ROM.NIZK.LeafKernel.kL, leafKernel,
      leafRun, List.mem_map] at ha
    obtain ⟨qa, hqa, rfl⟩ := ha
    obtain ⟨κ, hκ⟩ := M.exists_xof_of_mem_buildAssign hqa
    rw [M.saltOfBits_toBits, hκ]
    rfl
  coins_eq := rfl

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The simulated slice law of the lazily sampled merge reply is `innerL`.** -/
theorem simSliceAt_lazy (σ : FiatShamirSalt kS) (H : Bits (queryBits k kN kS L) → XOut k e)
    (x : X) (w : Wit) :
    ROM.NIZK.simSliceAt M.saltOfBits (lazyKernel VE B honest).toSimulator σ H ⟨x, w⟩ =
      innerL VE B H x (honest w) σ := by
  let eq : FreshSlice (Bits (queryBits k kN kS L)) (XOut k e) (M.toFullPast.LazyCoins R) ≃
      (M.ProverCoins R × FullPast.StreamDraw k kN kS L e P t) × (M.Pos → XOut k e) :=
    { toFun := fun a => ((⟨a.coins.iop, a.coins.merkleSalts⟩, ⟨a.slice, a.coins.streams⟩),
        a.coins.digests)
      invFun := fun b => ⟨⟨b.1.1.iop, b.1.2.streams, b.1.1.merkleSalts, b.2⟩, b.1.2.slice⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [ROM.NIZK.simSliceAt, ← PMF.map_uniformOfFintype_equiv eq.symm, PMF.map_comp, innerL]
  conv_rhs => rw [← PMF.map_fst_uniformOfFintype
    (α := M.ProverCoins R × FullPast.StreamDraw k kN kS L e P t)
    (β := M.Pos → XOut k e), PMF.map_comp]
  congr 1
  funext b
  simp only [Function.comp_apply, eq, Equiv.coe_fn_symm_mk, ROM.NIZK.Kernel.toSimulator,
    lazyKernel, ROM.NIZK.LeafKernel.kL, leafKernel, leafRun, FullPast.lazyEquiv,
    Equiv.coe_fn_mk, lazyOut, outB]
  rw [FullPast.mixDigest_honestLeaf VE]
  have hd : FullPast.honestDigest E (honest w b.1.1.iop) x b.1.1.merkleSalts
      (chainOracle (replaceSlice M.saltOfBits σ H b.1.2.slice)) b.1.2.streams =
      FullPast.honestDigest E (honest w b.1.1.iop) x b.1.1.merkleSalts (chainOracle H)
        b.1.2.streams := by
    funext p
    simp only [FullPast.honestDigest]
    exact leafDigest_replaceSlice H σ b.1.2.slice _
  rw [hd]

open Classical in
/-- **The honest prover against the lazily sampled merge reply**: at every salt the real slice
law (`innerR`) and the lazily sampled one (`innerL`) are within `keyCollision (t.size n) k`. -/
theorem sliceCloseAt_lazy {rel : Set (X × Wit)} :
    ROM.NIZK.SliceCloseAt M.saltOfBits (ROM.NIZK.liftRel fun x w => (x, w) ∈ rel)
      (M.niProverZKM B honest E Qs).liftReq (lazyKernel VE B honest).toSimulator
      fun _ => (SPBCS.keyCollision (t.size n) k).toReal where
  close σ H r _ _ := by
    rw [simSliceAt_lazy VE B honest σ H r.stmt r.wit]
    exact tvDist_innerR_innerL_le VE B H r.stmt (honest r.wit) σ
  nonneg _ := ENNReal.toReal_nonneg
  congr _ _ _ := rfl

/-! ### Step 3: the uniform-digest kernel against the simulator -/

section Observation

variable {Pub : Type} (pub : X → Pub) {Sim : CausalJointSimulator VE.MV Pub} (T : M.Preimages)
  {rel : Set (X × Wit)} {δ : ℝ≥0}

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [Nonempty R] in
open Classical in
/-- **The reply of the uniform-digest kernel is built from the honest observation**
(`outViewAt`). -/
theorem kernelReply_kD {x : X} {w : Wit} (hw : (x, w) ∈ rel)
    (O : Bits (queryBits k kN kS L) → XOut k e)
    (c : ROM.NIZK.LeafCoins (FullPast.LeafMain k kS e P t R) M.Pos (MerkleSalt kN)
      (XOut k e)) :
    ROM.NIZK.kernelReply (fun x w => (x, w) ∈ rel) (leafKernel VE B honest).kD c ⟨x, w⟩ O =
      outViewAt VE B O x c.main.salt O (M.chOfStreams c.main.streams) c.main.streams c.salts
        (fun p => (outEquiv k e (c.digests p)).digest)
        (VE.MV.view ((honest w c.main.iop).run x (M.chOfStreams c.main.streams))) := by
  rw [← innerD_out_eq VE B O x]
  simp only [ROM.NIZK.kernelReply, hw, ↓reduceIte, ROM.NIZK.LeafKernel.kD, leafKernel, leafRun,
    outB, replaceSlice_self]

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
open Classical in
/-- **The reply of the simulator is built from the joint simulator's view** (`outViewAt`). -/
theorem kernelReply_joint {x : X} {w : Wit} (hw : (x, w) ∈ rel)
    (O : Bits (queryBits k kN kS L) → XOut k e)
    (c : SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead Sim T)) :
    ROM.NIZK.kernelReply (fun x w => (x, w) ∈ rel)
        ((M.niJointSimulator VE.toViewRead B pub Sim T).toKernel (Wit := Wit)) c ⟨x, w⟩ O =
      outViewAt VE B O x c.salt O (Sim.sim (pub x) c.coins.sim).challenges
        (Sampler.preStreams T (Sim.sim (pub x) c.coins.sim).challenges c.coins.pre)
        c.coins.merkleSalts c.coins.digests (Sim.sim (pub x) c.coins.sim) := by
  rw [← simOutJ_eq B VE pub Sim T O x c.salt c.coins O]
  simp only [ROM.NIZK.kernelReply, hw, ↓reduceIte, NARG.SimulatorFn.toKernel, simOutJ, replaceSlice_self]

open Classical in
/-- **The uniform-digest kernel against the simulator**: at a valid proof query and any oracle, their
reply laws are within `overrun + δ` (`Base.tvDist_obs_joint_le`). -/
theorem tvDist_kD_joint_le (hvzk : CausalHVZK VE.MV rel honest pub Sim δ)
    (req : ProofQuery X Wit) (O : Bits (queryBits k kN kS L) → XOut k e)
    (hr : (req.stmt, req.wit) ∈ rel) :
    PMF.tvDist ((PMF.uniformOfFintype (ROM.NIZK.LeafCoins (FullPast.LeafMain k kS e P t R)
        M.Pos (MerkleSalt kN) (XOut k e))).map fun c =>
          ROM.NIZK.kernelReply (fun x w => (x, w) ∈ rel) (leafKernel VE B honest).kD c req O)
      ((PMF.uniformOfFintype (SaltedCoins (FiatShamirSalt kS)
        (M.JointSimCoins VE.toViewRead Sim T))).map
        fun c => ROM.NIZK.kernelReply (fun x w => (x, w) ∈ rel)
          ((M.niJointSimulator VE.toViewRead B pub Sim T).toKernel (Wit := Wit)) c req O) ≤
      M.overrun.toReal + δ := by
  obtain ⟨x, w⟩ := req
  let e₁ : ROM.NIZK.LeafCoins (FullPast.LeafMain k kS e P t R) M.Pos (MerkleSalt kN)
      (XOut k e) ≃
      (FiatShamirSalt kS × (M.Pos → MerkleSalt kN) × (M.Pos → XOut k e)) ×
        ((ChIdx P t → Out k e) × R) :=
    { toFun := fun c => ((c.main.salt, c.salts, c.digests), (c.main.streams, c.main.iop))
      invFun := fun b => ⟨⟨b.1.1, b.2.2, b.2.1⟩, b.1.2.1, b.1.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hL : (PMF.uniformOfFintype (ROM.NIZK.LeafCoins (FullPast.LeafMain k kS e P t R) M.Pos
        (MerkleSalt kN) (XOut k e))).map (fun c => ROM.NIZK.kernelReply (fun x w => (x, w) ∈ rel)
          (leafKernel VE B honest).kD c ⟨x, w⟩ O) =
      (PMF.uniformOfFintype (FiatShamirSalt kS × (M.Pos → MerkleSalt kN) × (M.Pos → Digest k))).bind
        fun q => (PMF.uniformOfFintype (ChIdx P t → Out k e)).bind fun ρ =>
          (PMF.uniformOfFintype R).map fun r => outViewAt VE B O x q.1 O (M.chOfStreams ρ) ρ
            q.2.1 q.2.2 (VE.MV.view ((honest w r).run x (M.chOfStreams ρ))) := by
    simp_rw [kernelReply_kD VE B honest hr O]
    rw [← PMF.map_uniformOfFintype_equiv e₁.symm, PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind,
      PMF.map_bind, ← Base.map_digests_uniform M.toBase, PMF.bind_map]
    congr 1
    funext a
    rw [PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind]
    congr 1
    funext ρ
    rw [PMF.map_comp]
    rfl
  let e₂ : SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead Sim T) ≃
      (FiatShamirSalt kS × (M.Pos → MerkleSalt kN) × (M.Pos → Digest k)) ×
        (Sim.Coins × ∀ c, (T c).Coins) :=
    { toFun := fun c => ((c.salt, c.coins.merkleSalts, c.coins.digests), (c.coins.sim, c.coins.pre))
      invFun := fun b => ⟨b.1.1, ⟨b.2.1, b.2.2, b.1.2.1, b.1.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hR : (PMF.uniformOfFintype (SaltedCoins (FiatShamirSalt kS)
        (M.JointSimCoins VE.toViewRead Sim T))).map
        (fun c => ROM.NIZK.kernelReply (fun x w => (x, w) ∈ rel)
          ((M.niJointSimulator VE.toViewRead B pub Sim T).toKernel (Wit := Wit)) c ⟨x, w⟩ O) =
      (PMF.uniformOfFintype (FiatShamirSalt kS × (M.Pos → MerkleSalt kN) × (M.Pos → Digest k))).bind
        fun q => (Sim.law (pub x)).bind fun v => (Sampler.preLaw T v.challenges).map fun ρ =>
          outViewAt VE B O x q.1 O v.challenges ρ q.2.1 q.2.2 v := by
    simp_rw [kernelReply_joint VE B pub T hr O]
    rw [← PMF.map_uniformOfFintype_equiv e₂.symm, PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind,
      PMF.map_bind]
    congr 1
    funext q
    rw [PMF.map_comp, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind, CausalJointSimulator.law,
      PMF.bind_map]
    congr 1
    funext c
    simp only [Function.comp_apply]
    rw [Sampler.preLaw, PMF.map_comp, PMF.map_comp]
    rfl
  rw [hL, hR]
  refine (PMF.tvDist_uniformOfFintype_bind_le _ _).trans ?_
  refine (Finset.expect_le_expect fun q _ => ?_).trans_eq (Finset.expect_const Finset.univ_nonempty _)
  have h := Base.tvDist_obs_joint_le VE honest pub Sim T x hvzk hr fun ch ρ o =>
    PMF.pure (outViewAt VE B O x q.1 O ch ρ q.2.1 q.2.2 o)
  simp only [← PMF.bind_pure_comp]
  exact h

end Observation

/-! ### The theorem -/

variable {Pub : Type} (pub : X → Pub) {Sim : CausalJointSimulator VE.MV Pub} (T : M.Preimages)
  {rel : Set (X × Wit)} {δ : ℝ≥0}

open Classical in
/-- **Query-counted zero knowledge of the spBCS compiler in the classical random-oracle
model** (module docstring; Unruh 2017 Definition 6, p. 14, with classical adversaries all of whose
queries are counted): at honest-verifier zero knowledge of the composite in the form of CY24
Definition 23.1.8 (`hvzk`), every classical adversary with a budget of `t` queries whose output does
not read the final oracle distinguishes the prover `niProverZKM` from the simulator
`niJointSimulator` with `Q` proof queries answered with advantage at most `zkErrorROMQuery δ t Q`, the
query-counted error of the compiler over the term. -/
theorem zeroKnowledgeROMQuery (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    ROM.NIZK.ZeroKnowledgeQueryBounded (fun x w => (x, w) ∈ rel) (M.niProverZKM B honest E Qs)
      (M.niJointSimulator VE.toViewRead B pub Sim T) (M.zkErrorROMQuery δ) := by
  have h1 := ROM.NIZK.zeroKnowledge_of_sliceCloseAt (saltedLocal_lazy VE B honest)
    (sliceCloseAt_lazy VE B honest (rel := rel))
  have hε₃ : (0 : ℝ) ≤ M.overrun.toReal + δ := add_nonneg ENNReal.toReal_nonneg δ.2
  refine (ROM.NIZK.zeroKnowledgeQueryBounded_of_leafKernel (leafKernel_laws VE B honest)
    (M.toFullPast.lazyEquiv R) (fun _ _ _ => rfl) h1 hε₃
    fun req O hr => tvDist_kD_joint_le VE B honest pub T hvzk req O hr).mono fun tq Q => ?_
  have hsalt : (Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    ring
  have hN : (Fintype.card (MerkleSalt kN) : ℝ) = 2 ^ (8 * kN) := by
    rw [show Fintype.card (MerkleSalt kN) = 2 ^ (8 * kN) from Out.card_digest]
    push_cast
    ring
  have hE : 𝔼 _H : Bits (queryBits k kN kS L) → XOut k e,
      (SPBCS.keyCollision (t.size n) k).toReal =
      (SPBCS.keyCollision (t.size n) k).toReal :=
    Finset.expect_const Finset.univ_nonempty _
  rw [hsalt, hN, hE, Finset.card_singleton, Base.zkErrorROMQuery]
  apply le_of_eq
  push_cast
  ring

open Classical in
/-- **Query-counted zero knowledge of the spBCS compiler in the classical random-oracle model
over query-bounded adversaries** (`GordieHowe.ROM.ZeroKnowledge`, Unruh 2017
Definition 6, p. 14, with classical adversaries all of whose queries are counted), from
`zeroKnowledgeROMQuery`. -/
theorem zeroKnowledgeROMQuery_games (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    GordieHowe.ROM.ZeroKnowledge (fun x w => (x, w) ∈ rel) (M.niProverZKM B honest E Qs)
      (M.niJointSimulator VE.toViewRead B pub Sim T) (M.zkErrorROMQuery δ) :=
  ROM.QueryBoundedAdversary.zeroKnowledge_of_queryBounded
    (zeroKnowledgeROMQuery VE B honest pub T hvzk)

end

end GordieHowe.SPBCS
