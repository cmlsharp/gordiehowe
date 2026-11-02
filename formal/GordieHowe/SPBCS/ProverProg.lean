-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimProg
public import GordieHowe.SPBCS.Extractor
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.SPBCS.Extraction.OnlineExtract
public import GordieHowe.SPBCS.Extraction.OnlineExtractROM
public import GordieHowe.Model.ROM.Model
public import GordieHowe.Model.Quantum.Interactive.QueryBoundedLastProofQuery

@[expose] public section

/-!
# The honest prover of the spBCS compiler

The honest prover `niProver`: the generic prover program (`niProverProgOf`, below) at the key
program with merges `mergeKeyProg`, which, for a challenge, queries the final inputs of all sites in
the order `siteOrder` (`finalsProg`) and then its chain input (`keyProg`). The key law holds at the
honest streams `honestStreams` (`keyLaw_mergeKeyProg`, from `honestStreams_eq`), so the program's
classical semantics is the compiled proof `prove` (`toFn_niProver`), in the format `B` of the
format bounds of the query phases. Run through `queryEncoding` it is the prover of the
zero-knowledge games `niProverZKM` (`toFn_encode_niProver`, the bridge from the hybrid argument).
At most `2 |Pos| + (|sites| + 2) · t.size n` queries.
-/

/-!
## The honest prover of the composite as a counted oracle program

The honest prover (built from the pieces of `GordieHowe/SPBCS/ZeroKnowledge.lean`) written as a
counted classical oracle program
(`GordieHowe.NARG.Prover`), over the global rounds in term order (`SPTerm.slots`). The program is
generic in how a challenge's key is queried (`KeyProg`); the spBCS compiler queries its chain input
after the merged branches' final inputs (`mergeKeyProg`, below). The program's classical semantics
is the built honest proof (`run_proverProg`) whenever the key program reads only the chains of the
challenge's causal past and its own earlier items, and the honest streams are the oracle at the keys
it computes on the built chains (`KeyLaw`).

- `proverStep`, `proverProg`: round `g` at its slot. At a prover round, the default leaf if a tree
  of the round is empty, then each tree's `leaf` queries and heap (`MerkleTree.treeHeapProg`); at a
  challenge round, the key program on the chains so far and the `xof` query at the key and the
  salt. Then, without queries, the proof from the writes, the opened leaves and the heaps.
- `length_trace_proverProg_le`: at most `2 |Pos| + (K + 1) · t.size n` queries for a key program
  of at most `K` queries.
- `ProverInv`, `run_proverProg`: the invariant over the rounds and the run.
- `niProverProgOf`, `toFn_niProverProgOf`: the counted program at a key program, whose classical
  semantics is the built honest proof; the spBCS compiler's prover `GordieHowe.SPBCS.niProver` is its
  instance at the key program with merges.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped BigOperators

variable {k kN kS L e : ℕ}

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t}
  {X : Type} (M : SPBCS Mg P X k kN kS L e)

/-! ### The trees of a global round -/

/-- The trees of global round `g`, in order (computable): those of the prover round at offset
`g`. -/
def treesAt (g : ℕ) : List M.Tree :=
  M.treeList.filter fun τ => τ.leaf.off n + τ.tree.msg.1.1 = g

theorem mem_treesAt {g : ℕ} {τ : M.Tree} : τ ∈ M.treesAt g ↔ τ.leaf.off n + τ.tree.msg.1.1 = g := by
  simp [treesAt, M.mem_treeList]

theorem sum_map_treesAt {A : Type*} [AddCommMonoid A] (g : ℕ) (f : M.Tree → A) :
    ((M.treesAt g).map f).sum =
      ∑ τ ∈ Finset.univ.filter (fun τ : M.Tree => τ.leaf.off n + τ.tree.msg.1.1 = g), f τ := by
  classical
  rw [treesAt, ← List.sum_toFinset _ (M.nodup_treeList.filter _)]
  congr 1
  ext τ
  simp [M.mem_treeList]

open Classical in
/-- The default-leaf program of global round `g`: if a tree of the round has no leaves, the `leaf`
query of the default leaf, returning its digest; otherwise no query. -/
noncomputable def defaultAt (g : ℕ) : OracleProg (Query k kN kS L) (Out k e) (Digest k) :=
  if ∃ τ : M.Tree, τ.leaf.off n + τ.tree.msg.1.1 = g ∧
      (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree = 0 then
    MerkleTree.leafProg (⟨fun _ => 0, ⟨0, Fin.elim0⟩⟩ : MerkleLeaf kN L)
  else .pure fun _ => 0

theorem length_trace_defaultAt_le (h : Query k kN kS L → Out k e) (g : ℕ) :
    ((M.defaultAt g).trace h).length ≤ 1 := by
  unfold defaultAt
  split_ifs <;> simp [MerkleTree.length_trace_leafProg]

/-! ### The program -/

/-- **A key program**: on the chains of all leaves and a challenge, an oracle program returning the
challenge's key. -/
abbrev KeyProg : Type :=
  ((q : t.Leaf) → M.Items q) → ChIdx P t → OracleProg (Query k kN kS L) (Out k e) (Digest k)

section ProverProg

variable [∀ j i, Nonempty ((P j).Challenge i)] (E : (j : ι) → (M.comp j).Encoder)
  (prv : CausalProver P t X) (x : X) (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS)

/-- The prover's state between global rounds: the streams of the challenges so far and the heaps
of the trees committed so far. -/
abbrev PState := (ChIdx P t → Out k e) × (M.Tree → ℕ → Digest k)

/-- The initial state: no streams (the default answer) and no heaps (all-zero digests). -/
def proverInitState : M.PState := (fun _ => SPBCS.defaultOut, fun _ _ _ => 0)

/-- The writes at a state: the honest write of the causal prover's message at the challenges read
from the streams, at the roots of the heaps. -/
noncomputable def stateWrites (st : M.PState) : M.WriteAll :=
  fun p i => honestWrite' E prv x st.1 p i fun τ => st.2 ⟨p, ⟨i, τ⟩⟩ 1

/-- The chains at a state: every leaf's chain with the writes and the streams of the state. -/
noncomputable def stateChains (st : M.PState) : (q : t.Leaf) → M.Items q :=
  fun q => M.writeLeaf st.1 (M.stateWrites E prv x st) q (n q.label)

/-- **Global round `g` of the prover program** from the state `st` (module docstring). -/
noncomputable def proverStep (kp : M.KeyProg) (g : ℕ) (st : M.PState) :
    OracleProg (Query k kN kS L) (Out k e) M.PState :=
  match (t.slots n)[g]? with
  | none => .pure st
  | some s =>
    if hd : (P s.leaf.label).dir s.round = .P_to_V then
      (M.defaultAt g).bind fun dflt =>
      (OracleProg.tabulate st.2 (M.treesAt g) fun τ =>
        MerkleTree.treeHeapProg ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
          (leafFn E ν τ.leaf τ.tree.msg (prv.run x (M.chOfStreams st.1) τ.leaf τ.tree.msg.1)
            τ.tree.tree) dflt).bind fun hp =>
      .pure (st.1, hp)
    else
      (kp (M.stateChains E prv x st) ⟨s.leaf, (P s.leaf.label).chIdx s.round hd⟩).bind fun key =>
      .query (.xof key σ) fun w =>
        .pure (Function.update st.1 ⟨s.leaf, (P s.leaf.label).chIdx s.round hd⟩ w, st.2)

/-- **The proof at the end of the prover program**: from the state after the global rounds, the
proof from the writes, the opened leaves at the query phase's positions and the heaps, in the
format `B` by the format bounds `hb`. -/
noncomputable def proverOut {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} {B : ℕ}
    (hb : M.FormatBounds Qs B B) (st : M.PState) : M.BProof B :=
  ⟨M.proofOfHeaps σ (honestWrite' E prv x st.1) st.2
    (honestOpened E prv x ν st.1 ((Qs x).pos (M.stateChains E prv x st) (M.chOfStreams st.1)))
    ((Qs x).pos (M.stateChains E prv x st) (M.chOfStreams st.1)),
    M.bounded_proofOfHeaps _ _ _ _ _ (by rw [honestOpened, List.length_map]; exact hb.pos_le x _ _)
      hb.nLeaves_le⟩

theorem proverOut_val {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} {B : ℕ}
    (hb : M.FormatBounds Qs B B) (st : M.PState) :
    (M.proverOut E prv x ν σ hb st).val = M.proofOfHeaps σ (honestWrite' E prv x st.1) st.2
      (honestOpened E prv x ν st.1 ((Qs x).pos (M.stateChains E prv x st) (M.chOfStreams st.1)))
      ((Qs x).pos (M.stateChains E prv x st) (M.chOfStreams st.1)) :=
  rfl

/-- **The prover program** over the compiler's oracle: the global rounds from the initial state,
then the proof `proverOut`. -/
noncomputable def proverProg (kp : M.KeyProg) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {B : ℕ} (hb : M.FormatBounds Qs B B) :
    OracleProg (Query k kN kS L) (Out k e) (M.BProof B) :=
  (OracleProg.iterate (M.proverStep E prv x ν σ kp) (t.size n) M.proverInitState).bind fun st =>
  .pure (M.proverOut E prv x ν σ hb st)

/-! #### The count -/

variable {M} in
/-- Each global round makes at most `2 (number of leaves of its trees) + K + 1` queries, for a key
program of at most `K` queries. -/
theorem length_trace_proverStep_le {kp : M.KeyProg} {K : ℕ}
    (hK : ∀ chs c h, ((kp chs c).trace h).length ≤ K) (h : Query k kN kS L → Out k e) (g : ℕ)
    (st : M.PState) :
    ((M.proverStep E prv x ν σ kp g st).trace h).length ≤
      2 * ∑ τ ∈ Finset.univ.filter (fun τ : M.Tree => τ.leaf.off n + τ.tree.msg.1.1 = g),
        (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree + (K + 1) := by
  unfold proverStep
  split
  · simp
  · split_ifs with hd
    · simp only [OracleProg.trace_bind, List.length_append, OracleProg.trace_pure, List.length_nil,
        add_zero, OracleProg.length_trace_tabulate, MerkleTree.length_trace_treeHeapProg]
      have h1 := M.length_trace_defaultAt_le h g
      have h2 : ((M.treesAt g).map fun τ => (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree +
          ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree - 1)).sum ≤
          2 * ∑ τ ∈ Finset.univ.filter (fun τ : M.Tree => τ.leaf.off n + τ.tree.msg.1.1 = g),
            (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree := by
        rw [sum_map_treesAt, Finset.mul_sum]
        exact Finset.sum_le_sum fun τ _ => by omega
      omega
    · simp only [OracleProg.trace_bind, List.length_append, OracleProg.trace_query,
        OracleProg.trace_pure, List.length_cons, List.length_nil]
      have := hK (M.stateChains E prv x st) ⟨_, (P _).chIdx _ hd⟩ h
      omega

variable {M} in
/-- **The prover program makes at most `2 |Pos| + (K + 1) · t.size n` queries.** -/
theorem length_trace_proverProg_le {kp : M.KeyProg} {K : ℕ}
    (hK : ∀ chs c h, ((kp chs c).trace h).length ≤ K) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {B : ℕ} (hb : M.FormatBounds Qs B B) (h : Query k kN kS L → Out k e) :
    ((M.proverProg E prv x ν σ kp hb).trace h).length ≤
      2 * Fintype.card M.Pos + (K + 1) * t.size n := by
  unfold proverProg
  rw [OracleProg.trace_bind, List.length_append, OracleProg.trace_pure, List.length_nil, add_zero]
  refine (OracleProg.length_trace_iterate_le h _ _
    (length_trace_proverStep_le E prv x ν σ hK h) _ _).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul,
    Finset.sum_fiberwise_of_maps_to (g := fun τ : M.Tree => τ.leaf.off n + τ.tree.msg.1.1)
      (fun τ _ => Finset.mem_range.2 (by
        have := Leaf.off_add_le n τ.leaf
        have := τ.tree.msg.1.2
        omega)), M.sum_nLeaves]
  ring

end ProverProg

/-! ### The counted program -/

section NIProverProg

variable [∀ j i, Nonempty ((P j).Challenge i)] {Wit R : Type} [Fintype R] [Nonempty R]
  (honest : Wit → R → CausalProver P t X)

/-- **The honest prover of the compiled composite as a counted oracle program**, for a key
program `kp x σ` at each statement and salt making at most `K` queries. On the statement `x`, the
witness `w` and the uniform coins (the Fiat–Shamir salt `σ`, the causal prover's coins and a Merkle
salt per position), the prover program `proverProg` of `honest w` (module docstring).

Running time: polynomial in the proof size when `kp` is. Per prover round of a leaf, one run of
the causal prover's message function (polynomial by assumption on the IOP prover), the leaf
encodings `E` and the leaf and node queries of the round's trees; per challenge round, one run of
the key program and one `xof` query; then the query phase's positions, the opened leaves and one
multiproof per tree read from the heaps. Oracle queries: at most `2 |Pos| + (K + 1) · t.size n`.
This running time is argued here, not proved in Lean. -/
noncomputable def niProverProgOf (E : (j : ι) → (M.comp j).Encoder)
    (kp : X → FiatShamirSalt kS → M.KeyProg) {K : ℕ}
    (hK : ∀ x σ chs c h, ((kp x σ chs c).trace h).length ≤ K) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {B : ℕ} (hb : M.FormatBounds Qs B B) :
    NARG.Prover (Query k kN kS L) (Out k e) X Wit (M.BProof B)
      (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) where
  prog x w a := M.proverProg E (honest w a.coins.iop) x a.coins.merkleSalts a.salt (kp x a.salt) hb
  coins := PMF.uniformOfFintype _
  q := 2 * Fintype.card M.Pos + (K + 1) * t.size n
  prog_queries x w a h := length_trace_proverProg_le E _ x _ _ (hK x a.salt) hb h

end NIProverProg

end

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t}
  {X : Type} (M : SPBCS Mg P X k kN kS L e)

theorem run_defaultAt (h : Query k kN kS L → Out k e) {τ : M.Tree}
    (hτ : (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree = 0) :
    (M.defaultAt (τ.leaf.off n + τ.tree.msg.1.1)).run h = defaultLeafDigest h := by
  rw [defaultAt, ite_eq_left ⟨τ, rfl, hτ⟩]
  rfl

/-- **A prefix of a built chain is the shorter built chain.** -/
theorem buildLeaf_take (h : Query k kN kS L → Out k e) (ρ : ChIdx P t → Out k e)
    (wr : M.RootWriteFn) (ld : M.Pos → Digest k) (p : t.Leaf) {r r' : ℕ} (hr : r ≤ r') :
    (M.buildLeaf h ρ wr ld p r').take r = M.buildLeaf h ρ wr ld p r := by
  rw [buildLeaf_eq_writeLeaf, buildLeaf_eq_writeLeaf, writeLeaf_take _ _ _ _ hr]

section ProverProg

variable [∀ j i, Nonempty ((P j).Challenge i)] (E : (j : ι) → (M.comp j).Encoder)
  (prv : CausalProver P t X) (x : X) (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS)

/-! #### The run -/

variable (h : Query k kN kS L → Out k e) (ρH : ChIdx P t → Out k e)

/-- **The key program reads the causal past, and the honest streams are its answers**: the key of a
challenge reads only the chains of the leaves before its leaf and its own items before it (`congr`);
and the stream `ρH c` is the oracle at the `xof` input of the key the program computes on the built
chains at `ρH` and the salt (`honest`). -/
structure KeyLaw (kp : M.KeyProg) : Prop where
  /-- The key reads only the causal past. -/
  congr : ∀ (chs chs' : (q : t.Leaf) → M.Items q) (c : ChIdx P t),
    (∀ q, q.Before c.leaf → chs q = chs' q) →
    (chs c.leaf).take c.idx.1.1 = (chs' c.leaf).take c.idx.1.1 →
    (kp chs c).run h = (kp chs' c).run h
  /-- The honest streams are the oracle at the keys of the built chains. -/
  honest : ∀ c, ρH c = h (.xof ((kp (fun q => M.buildLeaf h ρH (honestWrite' E prv x ρH)
    (honestDigest E prv x ν h ρH) q (n q.label)) c).run h) σ)

/-- **The invariant of the prover program** after the global rounds before `g`: the streams of
the challenges before `g` are `ρH`, and the heaps of the trees of the prover rounds before `g` are
the trees over the honest leaf digests at `ρH` (at the root and the heap positions). -/
structure ProverInv (g : ℕ) (st : M.PState) : Prop where
  /-- The streams so far. -/
  streams : ∀ c : ChIdx P t, gIdx c < g → st.1 c = ρH c
  /-- The heaps so far. -/
  heaps : ∀ τ : M.Tree, τ.leaf.off n + τ.tree.msg.1.1 < g → ∀ j,
    MerkleTree.InWindow ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree) j →
    st.2 τ j = MerkleTree.nodeDigest h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
      (M.leafDigestsOf h (honestDigest E prv x ν h ρH) τ.leaf τ.tree.msg τ.tree.tree) j

variable {M E prv x ν σ h ρH}

/-- Under the invariant, a message of a round before `g` is the message at the streams `ρH`. -/
theorem ProverInv.run_message {g : ℕ} {st : M.PState} (hi : M.ProverInv E prv x ν h ρH g st)
    (p : t.Leaf) (i : (P p.label).MessageIdx) (hpi : p.off n + i.1.1 ≤ g) :
    prv.run x (M.chOfStreams st.1) p i.1 = prv.run x (M.chOfStreams ρH) p i.1 :=
  CausalProver.run_message_congr prv x p i
    (fun c hc => by
      have := Leaf.Before.off_add_le n hc
      have := c.idx.1.2
      simp only [chOfStreams]
      rw [hi.streams c (by unfold gIdx; omega)])
    fun j hj => by
      have hj' : j.1.1 < i.1.1 := hj
      simp only [chOfStreams]
      rw [hi.streams ⟨p, j⟩ (by unfold gIdx; dsimp only; omega)]

/-- Under the invariant, the chain of the rounds before `g` at the state is the honest built
chain. -/
theorem ProverInv.writeLeaf_eq {g : ℕ} {st : M.PState} (hi : M.ProverInv E prv x ν h ρH g st)
    (p : t.Leaf) (r : ℕ) (hr : p.off n + r ≤ g) :
    M.writeLeaf st.1 (M.stateWrites E prv x st) p r =
      M.buildLeaf h ρH (honestWrite' E prv x ρH) (honestDigest E prv x ν h ρH) p r := by
  rw [buildLeaf_eq_writeLeaf]
  refine M.writeLeaf_congr r (fun c hc => hi.streams ⟨p, c⟩ (by unfold gIdx; dsimp only; omega))
    fun i hir => ?_
  simp only [stateWrites, honestWrite']
  rw [hi.run_message p i (by omega)]
  congr 1
  funext τ
  exact hi.heaps ⟨p, ⟨i, τ⟩⟩ (by dsimp only; omega) 1 (Or.inr rfl)

/-- **A global round preserves the invariant.** -/
theorem ProverInv.step {kp : M.KeyProg} (hK : M.KeyLaw E prv x ν σ h ρH kp) {g : ℕ}
    (hg : g < t.size n) {st : M.PState} (hi : M.ProverInv E prv x ν h ρH g st) :
    M.ProverInv E prv x ν h ρH (g + 1) ((M.proverStep E prv x ν σ kp g st).run h) := by
  obtain ⟨s, hs⟩ := exists_slots_getElem n hg
  have hgs := eq_off_of_slots_getElem n hs
  -- the slot of a round at offset `g`
  have hslot : ∀ (q : t.Leaf) (r : Fin (n q.label)), q.off n + r = g →
      (⟨q, r⟩ : SPTerm.Slot n t) = s := fun q r hqr => by
    have := slots_getElem n q r
    rw [hqr, hs] at this
    exact (Option.some_inj.1 this).symm
  unfold proverStep
  simp only [hs]
  by_cases hd : (P s.leaf.label).dir s.round = .P_to_V
  · rw [dite_eq_left hd]
    simp only [OracleProg.run_bind, OracleProg.run_tabulate, OracleProg.run_pure,
      MerkleTree.run_treeHeapProg]
    refine ⟨fun c hc => hi.streams c ?_, fun τ hτ j hj => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h1 | h1
      · exact h1
      · exfalso
        have he := hslot c.leaf c.idx.1 h1
        subst he
        have := c.idx.2
        rw [this] at hd
        exact absurd hd (by decide)
    · by_cases hτg : τ.leaf.off n + τ.tree.msg.1.1 = g
      · have hmem : τ ∈ M.treesAt g := M.mem_treesAt.2 hτg
        simp only [hmem, ite_true]
        rw [hi.run_message τ.leaf τ.tree.msg hτg.le]
        refine MerkleTree.nodeDigest_congr_window h (fun j hj => ?_) (fun h0 => ?_) hj
        · rw [ite_eq_left hj, ← congrFun (root_leafFn E prv x ν h ρH τ.leaf τ.tree.msg τ.tree.tree) j]
        · rw [ite_eq_right (by omega), leafDigestsOf, dite_eq_right (by omega), ← hτg, M.run_defaultAt h h0]
      · have hmem : τ ∉ M.treesAt g := fun hm => hτg (M.mem_treesAt.1 hm)
        simp only [hmem, ite_false]
        exact hi.heaps τ (by omega) j hj
  · rw [dite_eq_right hd]
    simp only [OracleProg.run_bind, OracleProg.run_query, OracleProg.run_pure]
    set c0 : ChIdx P t := ⟨s.leaf, (P s.leaf.label).chIdx s.round hd⟩ with hc0
    have hgc0 : gIdx c0 = g := by
      rw [hgs]
      rfl
    have hkey : (kp (M.stateChains E prv x st) c0).run h =
        (kp (fun q => M.buildLeaf h ρH (honestWrite' E prv x ρH) (honestDigest E prv x ν h ρH) q
          (n q.label)) c0).run h := by
      refine hK.congr _ _ c0 (fun q hq => ?_) ?_
      · have : q.off n + n q.label ≤ s.leaf.off n := Leaf.Before.off_add_le n hq
        exact hi.writeLeaf_eq q _ (by omega)
      · show (M.writeLeaf st.1 (M.stateWrites E prv x st) s.leaf (n s.leaf.label)).take _ =
          (M.buildLeaf h ρH _ _ s.leaf (n s.leaf.label)).take _
        have hle : c0.idx.1.1 ≤ n s.leaf.label := c0.idx.1.2.le
        rw [M.writeLeaf_take _ _ _ hle, M.buildLeaf_take _ _ _ _ _ hle,
          hi.writeLeaf_eq s.leaf _ (by show s.leaf.off n + s.round.1 ≤ g; omega)]
    refine ⟨fun c hc => ?_, fun τ hτ j hj => hi.heaps τ ?_ j hj⟩
    · dsimp only
      by_cases he : c = c0
      · subst he
        rw [Function.update_self, hkey]
        exact (hK.honest c0).symm
      · rw [Function.update_of_ne he]
        refine hi.streams c ?_
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h1 | h1
        · exact h1
        · exact absurd (gIdx_injective (h1.trans hgc0.symm)) he
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hτ with h1 | h1
      · exact h1
      · exfalso
        have he := hslot τ.leaf τ.tree.msg.1 h1
        subst he
        exact hd τ.tree.msg.2

/-- The invariant after `m ≤ t.size n` global rounds. -/
theorem proverInv_iterate {kp : M.KeyProg} (hK : M.KeyLaw E prv x ν σ h ρH kp) : ∀ m ≤ t.size n,
    M.ProverInv E prv x ν h ρH m
      ((OracleProg.iterate (M.proverStep E prv x ν σ kp) m M.proverInitState).run h)
  | 0, _ => ⟨fun c hc => absurd hc (Nat.not_lt_zero _), fun τ hτ => absurd hτ (Nat.not_lt_zero _)⟩
  | m + 1, hm => by
    rw [OracleProg.run_iterate_succ]
    exact (proverInv_iterate hK m (by omega)).step hK (by omega)

variable (E prv x ν σ h ρH)

/-- **The prover program computes the built honest proof** at the streams `ρH`, for a key program
with its key law. -/
theorem run_proverProg {kp : M.KeyProg} (hK : M.KeyLaw E prv x ν σ h ρH kp) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B) :
    ((M.proverProg E prv x ν σ kp hb).run h).val =
      M.buildProof h σ (honestWrite' E prv x ρH) (honestDigest E prv x ν h ρH)
        (honestOpened E prv x ν ρH (VE.posC x (M.chOfStreams ρH))) (VE.posC x (M.chOfStreams ρH)) := by
  have hi := proverInv_iterate hK (t.size n) le_rfl
  unfold proverProg
  rw [OracleProg.run_bind, OracleProg.run_pure, proverOut_val]
  generalize (OracleProg.iterate (M.proverStep E prv x ν σ kp) (t.size n) M.proverInitState).run h = st at hi
  have hs : st.1 = ρH := funext fun c => hi.streams c (gIdx_lt_size c)
  have hW : M.WritesAll (M.stateChains E prv x st) := fun p i =>
    ⟨_, M.writeLeaf_getElem?_write _ _ p i⟩
  have hpos : (Qs x).pos (M.stateChains E prv x st) (M.chOfStreams st.1) =
      VE.posC x (M.chOfStreams ρH) := by
    rw [VE.pos_eq x _ _ hW, hs]
  have hheaps : M.HeapsOf h (honestDigest E prv x ν h ρH) st.2 := fun τ j hj =>
    hi.heaps τ (by
      have := Leaf.off_add_le n τ.leaf
      have := τ.tree.msg.1.2
      omega) j hj
  rw [hpos, hs, ← hheaps.buildProof_eq]

end ProverProg

/-! ### The counted program -/

section NIProverProg

variable [∀ j i, Nonempty ((P j).Challenge i)] {Wit R : Type} [Fintype R] [Nonempty R]
  (honest : Wit → R → CausalProver P t X)

/-- **The counted program's classical semantics is the built honest proof**, when every key
program has its key law at the honest streams `ρH`. -/
theorem toFn_niProverProgOf (E : (j : ι) → (M.comp j).Encoder)
    (kp : X → FiatShamirSalt kS → M.KeyProg) {K : ℕ}
    (hK : ∀ x σ chs c h, ((kp x σ chs c).trace h).length ≤ K) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B)
    (ρH : Wit → R → X → (M.Pos → MerkleSalt kN) → FiatShamirSalt kS →
      (Query k kN kS L → Out k e) → ChIdx P t → Out k e)
    (hlaw : ∀ w r x ν σ h, M.KeyLaw E (honest w r) x ν σ h (ρH w r x ν σ h) (kp x σ))
    (h : Query k kN kS L → Out k e) (x : X) (w : Wit)
    (a : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :
    ((M.niProverProgOf honest E kp hK hb).toFn.prove h x w a).val =
      M.buildProof h a.salt
        (honestWrite' E (honest w a.coins.iop) x (ρH w a.coins.iop x a.coins.merkleSalts a.salt h))
        (honestDigest E (honest w a.coins.iop) x a.coins.merkleSalts h
          (ρH w a.coins.iop x a.coins.merkleSalts a.salt h))
        (honestOpened E (honest w a.coins.iop) x a.coins.merkleSalts
          (ρH w a.coins.iop x a.coins.merkleSalts a.salt h)
          (VE.posC x (M.chOfStreams (ρH w a.coins.iop x a.coins.merkleSalts a.salt h))))
        (VE.posC x (M.chOfStreams (ρH w a.coins.iop x a.coins.merkleSalts a.salt h))) :=
  run_proverProg E _ x _ _ _ _ (hlaw _ _ _ _ _ _) VE hb

end NIProverProg

end

end GordieHowe.SPBCS

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped BigOperators

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e) (Λ : SiteLayout Mg)

/-- **The key program of the spBCS compiler** at the statement `x` and the salt `σ`: the
final inputs of all sites on the chains so far (`finalsProg`), then the challenge's chain input
with those final digests and its own items before it. -/
def mergeKeyProg (x : X) (σ : FiatShamirSalt kS) : M.KeyProg := fun chs c =>
  (M.finalsProg ⟨σ, x⟩ chs Λ).bind fun fs =>
  M.keyProg ⟨σ, x⟩ chs fs c.leaf ((chs c.leaf).take c.idx.1.1)

theorem length_trace_mergeKeyProg (x : X) (σ : FiatShamirSalt kS) chs c
    (h : Query k kN kS L → Out k e) :
    ((M.mergeKeyProg Λ x σ chs c).trace h).length ≤ Fintype.card Mg.Site + 1 := by
  simp only [mergeKeyProg, OracleProg.trace_bind, List.length_append, M.length_trace_keyProg]
  exact Nat.add_le_add_right (M.length_trace_finalsProg_le _ _ h Λ) _

theorem run_mergeKeyProg (x : X) (σ : FiatShamirSalt kS) chs c (h : Query k kN kS L → Out k e) :
    (M.mergeKeyProg Λ x σ chs c).run h =
      M.key h ⟨σ, x⟩ chs (M.finalsWith h ⟨σ, x⟩ chs) c.leaf ((chs c.leaf).take c.idx.1.1) := by
  simp only [mergeKeyProg, OracleProg.run_bind, run_finalsProg, run_keyProg]

variable [∀ j i, Nonempty ((P j).Challenge i)]

variable {M} in
/-- **The key program with merges has its key law at the honest streams** (`honestStreams_eq`). -/
theorem keyLaw_mergeKeyProg (E : (j : ι) → (M.comp j).Encoder) (prv : CausalProver P t X)
    (x : X) (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS) (h : Query k kN kS L → Out k e) :
    M.KeyLaw E prv x ν σ h (honestStreams E prv x ν σ h) (M.mergeKeyProg Λ x σ) where
  congr chs chs' c hb ho := by
    rw [run_mergeKeyProg, run_mergeKeyProg, ho]
    refine congrFun (key_congr (fun q hq => hb q hq.1) fun s hs => ?_) _
    exact finalsWith_congr_of_hides hb hs
  honest c := by
    rw [honestStreams_eq, keyStep, run_mergeKeyProg, buildKey, buildFinals,
      M.buildLeaf_take h _ _ _ c.leaf c.idx.1.2.le]
    rfl

variable {Wit R : Type} [Fintype R] [Nonempty R] (honest : Wit → R → CausalProver P t X)

/-- **The honest prover of the spBCS compiler** (paper `prot:generalized-bcs`): the generic prover
program (`niProverProgOf`) at the key program with merges,
against the compiler's oracle `Query → Out`, with uniform coins (the Fiat–Shamir salt, the causal
prover's coins and a Merkle salt per position). Its proofs are in the format `B` by the format
bounds `hb` of the query phases. At most `2 |Pos| + (|sites| + 2) · t.size n` queries.
Completeness, zero knowledge and witness indistinguishability are stated for this one object; in
the quantum random-oracle model it runs through `queryEncoding`.

Running time: that of `SPBCS.niProverProgOf`, with, per challenge, the final inputs of all
sites (`|sites|` `transcript` queries, each one encoding, after sorting the sites of `Λ` by rank)
and its chain input. This running time is argued here, not proved in Lean. -/
noncomputable def niProver (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {B : ℕ} (hb : M.FormatBounds Qs B B) :
    NARG.Prover (Query k kN kS L) (Out k e) X Wit (M.BProof B)
      (SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :=
  M.niProverProgOf honest E (M.mergeKeyProg Λ)
    (fun x σ chs c h => M.length_trace_mergeKeyProg Λ x σ chs c h) hb

/-- **The prover's classical semantics is the compiled proof** `prove` of the causal prover at
the coins, for a query phase with view laws `VE`. -/
theorem toFn_niProver (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B)
    (h : Query k kN kS L → Out k e) (x : X) (w : Wit)
    (a : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) :
    ((M.niProver Λ honest E hb).toFn.prove h x w a).val =
      prove (honest w a.coins.iop) x a.salt E a.coins.merkleSalts h (Qs x) := by
  rw [niProver, M.toFn_niProverProgOf honest E (M.mergeKeyProg Λ)
    (fun x σ chs c h => M.length_trace_mergeKeyProg Λ x σ chs c h) VE hb
    (fun w r x ν σ h => honestStreams E (honest w r) x ν σ h)
    (fun w r x ν σ h => keyLaw_mergeKeyProg Λ E (honest w r) x ν σ h) h x w a,
    ← honestProof_eq_buildProof E _ x _ _ _ VE, ← prove_eq_honestProof]

variable [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-- **Bridge to the hybrid argument**: the prover run through `queryEncoding` is the prover of the
zero-knowledge games, whose proofs are encoded by the proof device `SPBCS.Internal.encodeTotal`;
within the format bounds the device is the constructor of a bounded proof. -/
theorem toFn_encode_niProver (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B) :
    (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).toFn =
      M.niProverZKM B honest E Qs := by
  have hp : ∀ H x w a,
      (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).toFn.prove H x w a =
        (M.niProverZKM B honest E Qs).prove H x w a := by
    intro H x w a
    rw [NARG.Prover.toFn_encode_prove, NARG.Prover.toFn_mapOutput_prove, decode_queryEncoding]
    show _ = SPBCS.Internal.encodeTotal M B _
    rw [SPBCS.Internal.encodeTotal_of_bounded _ (prove_eq_honestProof E _ x _ _ _ (Qs x) ▸
      bounded_honestProof E _ x _ _ (Qs x) _ (hb.pos_le x) hb.nLeaves_le)]
    exact congrArg some (Subtype.ext (M.toFn_niProver Λ honest E VE hb _ x w a))
  unfold NARG.Prover.toFn niProverZKM
  congr 1
  funext H x w a
  exact hp H x w a

open Classical in
/-- **Everlasting zero knowledge of the spBCS compiler against query-bounded
adversaries** (QROM; Unruh 2017 Definition 6, p. 14, over the paper's `(t, Q)`-adversaries,
`def:adversary`, with the query bound of `def:narg-zk-post`; paper `thm:bcs-zk`(1)): the prover
`niProver` and the simulator `niSimulator`, both with proofs in the format `B` of the format bounds
`hb`, run through `queryEncoding`: every query-bounded adversary making at most `tq` queries on
every branch before its last proof query and answered on `Q` proof queries has advantage at most
`zkError δ tq Q`.

The statements `X` and witnesses `Wit` are arbitrary types. The adversary writes its proof queries in a
register with finite alphabets `X'` and `W'`, read as statements and witnesses through arbitrary
maps `fx` and `fw` (`comap`). This is no restriction on the adversaries of `def:adversary`: their
registers are those of Watrous (TQI, Definition 2.1, p. 59), whose alphabets are finite (p. 1), so
the proof queries of one adversary range over a finite set of statements and witnesses, which `X'`, `W'`
with the inclusions `fx`, `fw` cover. -/
theorem everlastingZeroKnowledge_qrom (E : (j : ι) → (M.comp j).Encoder)
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ}
    (hb : M.FormatBounds Qs B B) {Pub : Type} {pub : X → Pub} {Sim : CausalJointSimulator VE.MV Pub}
    (T : M.Preimages) {rel : Set (X × Wit)} {δ : NNReal} {X' W' : Type} [Fintype X'] [DecidableEq X']
    [Fintype W'] [DecidableEq W'] (fx : X' → X) (fw : W' → Wit)
    (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    GordieHowe.NARG.QROM.EverlastingZeroKnowledge (fun x w => (fx x, fw w) ∈ rel) queryEncoding
      ((M.niProver Λ honest E hb).comap fx fw)
      ((M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T).comap fx)
      (M.zkError δ) := by
  apply EverlastingZeroKnowledgePure.everlastingZeroKnowledge
  rw [NARG.Prover.mapOutput_comap, NARG.Prover.encode_comap, NARG.Simulator.encode_comap,
    NARG.Prover.toFn_comap, NARG.Simulator.toFn_comap, M.toFn_encode_niProver Λ honest E VE hb,
    M.encode_niSimulator Λ E VE hb, toFn_niJointSimulatorProg]
  exact everlastingZeroKnowledge VE B T fx fw hvzk

end

end GordieHowe.SPBCS
