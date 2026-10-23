-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimProg
public import GordieHowe.SPBCS.FullPast.ProverProg
public import GordieHowe.SPBCS.FullPast.Online

@[expose] public section

/-!
# The honest prover of the spBCS compiler

The honest prover `niProver`: the generic prover program of the compiler over the term
(`GordieHowe.SPBCS.Base.niProverProgOf`, `GordieHowe/SPBCS/FullPast/ProverProg.lean`) at the key
program with merges `mergeKeyProg`, which, for a challenge, queries the final inputs of all sites in
the order `siteOrder` (`finalsProg`) and then its chain input (`keyProg`). The key law holds at the
honest streams `honestStreams` (`keyLaw_mergeKeyProg`, from `honestStreams_eq`), so the program's
classical semantics is the compiled proof `prove` (`toFn_niProver`), in the format `B` of the
format bounds of the query phases. Run through `queryEncoding` it is the prover of the
zero-knowledge games `niProverZKM` (`toFn_encode_niProver`, the bridge from the hybrid argument).
At most `2 |Pos| + (|sites| + 2) · t.size n` queries.
-/

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
    M.toFullPast.KeyLaw E prv x ν σ h (honestStreams E prv x ν σ h) (M.mergeKeyProg Λ x σ) where
  congr chs chs' c hb ho := by
    rw [run_mergeKeyProg, run_mergeKeyProg, ho]
    refine congrFun (key_congr (fun q hq => hb q hq.1) fun s hs => ?_) _
    exact finalsWith_congr_of_hides hb hs
  honest c := by
    rw [honestStreams_eq, keyStep, run_mergeKeyProg, buildKey, buildFinals,
      M.toFullPast.buildLeaf_take h _ _ _ c.leaf c.idx.1.2.le]
    rfl

variable {Wit R : Type} [Fintype R] [Nonempty R] (honest : Wit → R → CausalProver P t X)

/-- **The honest prover of the spBCS compiler** (paper `prot:generalized-bcs`): the generic prover
program of the compiler over the term (`Base.niProverProgOf`) at the key program with merges,
against the compiler's oracle `Query → Out`, with uniform coins (the Fiat–Shamir salt, the causal
prover's coins and a Merkle salt per position). Its proofs are in the format `B` by the format
bounds `hb` of the query phases. At most `2 |Pos| + (|sites| + 2) · t.size n` queries.
Completeness, zero knowledge and witness indistinguishability are stated for this one object; in
the quantum random-oracle model it runs through `queryEncoding`.

Running time: that of `Base.niProverProgOf`, with, per challenge, the final inputs of all
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
  rw [niProver, M.toFullPast.toFn_niProverProgOf honest E (M.mergeKeyProg Λ)
    (fun x σ chs c h => M.length_trace_mergeKeyProg Λ x σ chs c h) VE hb
    (fun w r x ν σ h => honestStreams E (honest w r) x ν σ h)
    (fun w r x ν σ h => keyLaw_mergeKeyProg Λ E (honest w r) x ν σ h) h x w a,
    ← honestProof_eq_buildProof E _ x _ _ _ VE, ← prove_eq_honestProof]

variable [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-- **Bridge to the hybrid argument**: the prover run through `queryEncoding` is the prover of the
zero-knowledge games, whose proofs are encoded by the proof device `FullPast.Internal.encodeTotal`;
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
    show _ = FullPast.Internal.encodeTotal M.toFullPast B _
    rw [FullPast.Internal.encodeTotal_of_bounded _ (prove_eq_honestProof E _ x _ _ _ (Qs x) ▸
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
