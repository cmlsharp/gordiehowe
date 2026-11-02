-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Headline
public import GordieHowe.SPBCS.CompleteNARG
public import GordieHowe.SPBCS.ZeroKnowledgeQuery
public import GordieHowe.SPBCS.ZeroKnowledgeROMProver
public import GordieHowe.SPBCS.ZeroKnowledgeSampler
public import GordieHowe.SPBCS.WitnessIndistAdaptive
public import GordieHowe.SPBCS.WitnessSampler

@[expose] public section

/-!
# The guarantees of the spBCS compiler

The spBCS compiler on a series–parallel term with arbitrarily nested merges
(`GordieHowe/SPBCS/Basic.lean`, paper `prot:generalized-bcs`) satisfies the guarantees of paper
`thm:bcs-main` with the errors of the paper's Appendix I, for every Merkle opening format
`M.opening` (`GordieHowe/SPBCS/Merkle/Opening.lean`): the authentication paths of `prot:generalized-bcs`
(`PerLeaf.opening`) and the compressed multiproofs of the configurations (`Multiproof.opening`),
at the same errors. The proof-format bound `B` of the zero-knowledge games bounds the opened
leaves and, through `MerkleFormat.pathCap`, the path digests of each tree.

## Completeness

`CompletenessGuarantees`, `completenessGuarantees` (paper `thm:bcs-complete`(2)): for the honest
prover `prove` with uniform coins `r`, from a bound `εc` on the composite verifier's rejection of
the honest run over uniform coins and uniform challenges (the completeness error of
`def:iop-complete`),

* `completeness`: for `(x, w) ∈ rel`, any Merkle salts `ν` and Fiat–Shamir salt `σ`, the honest
  proof is rejected over uniform coins and a uniform oracle with probability at most
  `εc + overrun + keyCollision (t.size n) k` (part (2) at `t = 0`);
* `completenessOfSampler`: the same at a witness drawn by a witness sampler that misses `rel` on
  the proof query `u` for `x` with probability at most `η`, with `η` added;

Part (1), for a prover with fixed coins, is `prob_not_accepts_prove_le`. The clauses above are
`prob_not_accepts_prove_coins_le` over uniform coins of the honest prover. Part (2) against
adversaries choosing `(x, w)` after their queries (`def:narg-complete`) is `GordieHowe.SPBCS.complete_rom`
(`NARG.ROM.Complete`, extra term `t / 2^(8kS)`) and `GordieHowe.SPBCS.complete_qrom`
(`NARG.QROM.Complete`, extra term `2t / 2^(4kS)`), at the honest prover `niProver` with uniform
coins, Merkle salts and Fiat–Shamir salt.

The key-collision term is the paper's `errkey = binom(nmsg, 2) 2^(-8b)` with `nmsg = t.size n`,
the rounds of all leaves; the final inputs of the branches add no key.
## Zero knowledge and witness indistinguishability

`GordieHowe.SPBCS.PrivacyGuarantees`, `GordieHowe.SPBCS.privacyGuarantees` (paper `thm:bcs-zk`, `thm:bcs-wi`): for the honest prover
`niProver` and the simulator `niSimulator` of `prot:bcs-simulator` (at most
`2 |Pos| + t.size n + |sites|` queries), with proofs in the format of the format bounds, from honest-verifier zero knowledge of the composite at the joint simulator `Sim` with
error `δ` (`GordieHowe.IOP.CausalHVZK`):

* `zeroKnowledge`: everlasting zero knowledge against query-bounded adversaries (QROM) at
  `zkError δ` (part (1) of `thm:bcs-zk`);
* `zeroKnowledgeOfSampler`: the same at witnesses drawn by a witness sampler missing `rel` with
  probability at most `η`, at `zkError δ + Q · η`;
* `zeroKnowledgeROM`: everlasting zero knowledge against classical query-bounded adversaries at
  `zkErrorROM δ` (part (2));
* `zeroKnowledgeQueryCounted`, `zeroKnowledgeROMQuery`: every query counted, at `zkErrorQuery δ` and
  `zkErrorROMQuery δ` (zero knowledge of `def:narg-zk` in the QROM and the ROM);
* `witnessIndist`: unconditional adaptive multi-theorem witness indistinguishability with `Q` proof queries whose statements and
  witnesses have total encoding length at most `ℓ` under injective binary encodings `eX`, `eW`,
  at `Q · wiError δ (choiceCount ℓ)` (`thm:bcs-wi`, `GordieHowe.SPBCS.unconditionallyWitnessIndistinguishable`).

The errors are those of the spBCS compiler (`zkError`, `wiError`, …): the key-collision term counts the `t.size n`
chain inputs of the rounds; the final inputs of the branches are answered by the slice and add no
key.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open GordieHowe.QROM (replaceSlice ProofQuery)
open scoped ENNReal NNReal

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {X : Type} (M : SPBCS Mg P X k kN kS L e)

/-! ### Completeness -/

/-- **The completeness guarantees of the spBCS compiler** (module docstring) for the
encoders `E`, the query phases `Qs`, the causal honest prover `honest` with uniform coins in `R`,
the relation `rel` and the bound `εc` on the composite verifier's rejection of the honest run over
uniform coins and challenges. -/
structure CompletenessGuarantees (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    (Qs : ∀ x, M.IOPQueries V x) {Wit R : Type} [Fintype R] [Nonempty R]
    (honest : Wit → R → CausalProver P t X) (rel : Set (X × Wit)) (εc : ℝ≥0∞) : Prop where
  /-- Completeness for a fixed statement, over uniform coins and a uniform oracle. -/
  completeness : ∀ x w (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS), (x, w) ∈ rel →
    Pr[q ← R × (Query k kN kS L → Out k e) :
        ¬ M.Accepts q.2 x (prove (honest w q.1) x σ E ν q.2 (Qs x)) (Qs x)] ≤
      εc + M.overrun + SPBCS.keyCollision (t.size n) k
  /-- Completeness at a witness drawn by a witness sampler, averaged over uniform coins. -/
  completenessOfSampler : ∀ {U : Type} (D : WitnessSampler U Wit) x u (η : ℝ≥0),
    D.MissesAtMostAt rel x u η → ∀ (ν : M.Pos → MerkleSalt kN) (σ : FiatShamirSalt kS),
    ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * Pr[d ← D.Draw (Query k kN kS L → Out k e) :
        ¬ M.Accepts d.oracle x
          (prove (honest (D.draw u d.coins) r) x σ E ν d.oracle (Qs x)) (Qs x)] ≤
      εc + M.overrun + SPBCS.keyCollision (t.size n) k + η

variable {M}

/-- **The spBCS compiler is complete** (`CompletenessGuarantees`, paper `thm:bcs-complete`)
when the IOP has completeness error at most `εc` (`def:iop-complete`): for every pair in `rel`, the
composite verifier rejects the run of the honest causal prover with probability at most `εc` over
its uniform coins and uniform challenges (`hc`). -/
@[headline]
theorem completenessGuarantees {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {Wit R : Type} [Fintype R] [Nonempty R]
    {honest : Wit → R → CausalProver P t X} {rel : Set (X × Wit)} {εc : ℝ≥0∞}
    (hc : ∀ x w, (x, w) ∈ rel →
      Pr[q ← R × Chs P t : V x ((honest w q.1).run x q.2) ≠ true] ≤ εc) :
    M.CompletenessGuarantees E Qs honest rel εc where
  completeness x w ν σ hw := prob_not_accepts_prove_coins_le x σ E ν (Qs x) (honest w) (hc x w hw)
  completenessOfSampler D x _ _ hD ν σ :=
    D.prob_draw_coins_le hD
      (fun w r h => ¬ M.Accepts h x (prove (honest w r) x σ E ν h (Qs x)) (Qs x))
      fun w hw => prob_not_accepts_prove_coins_le x σ E ν (Qs x) (honest w) (hc x w hw)

/-! ### Zero knowledge and witness indistinguishability -/

section ZK

variable [∀ j i, Fintype ((M.comp j).MessageWrite i)]

variable (M) in
open Classical in
/-- **The zero-knowledge and witness-indistinguishability guarantees of the spBCS
compiler** (module docstring) at the encoders `E`, the view laws `VE` of the query phases `Qs`, the
format bounds `hb` at `B`, the site layout `Λ` of the prover, the causal honest prover `honest`, the
joint simulator `Sim` of the composite view on public statements `pub x`, the preimage samplers `T`,
the relation `rel` and the HVZK error `δ`. The zero-knowledge statements name the prover `niProver`
and the simulator `niSimulator`, run through `queryEncoding` in the QROM. The zero-knowledge
adversary classes are the paper's `def:adversary`. The witness-indistinguishability adversary is
that of the paper's `def:narg-wi`: it chooses each statement and witness pair as a function of the
oracle and the earlier proofs. -/
structure PrivacyGuarantees (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    (Qs : ∀ x, M.IOPQueries V x) (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B)
    (Λ : SiteLayout Mg) {Wit R : Type} [Fintype R] [Nonempty R]
    (honest : Wit → R → CausalProver P t X) {Pub : Type} (pub : X → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) (rel : Set (X × Wit)) (δ : ℝ≥0) :
    Prop where
  /-- Zero knowledge in the QROM against query-bounded adversaries. -/
  zeroKnowledge : ∀ (X' W' : Type) [Fintype X'] [DecidableEq X'] [Fintype W'] [DecidableEq W']
    (fx : X' → X) (fw : W' → Wit),
    GordieHowe.NARG.QROM.EverlastingZeroKnowledge (fun x w => (fx x, fw w) ∈ rel) queryEncoding
      ((M.niProver Λ honest E hb).comap fx fw)
      ((M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T).comap fx)
      (M.zkError δ)
  /-- Zero knowledge in the QROM against query-bounded adversaries at witnesses drawn by a witness
  sampler. -/
  zeroKnowledgeOfSampler : ∀ {U : Type} (D : WitnessSampler U Wit) (relU : Set (X × U))
    (η : ℝ≥0), D.MissesAtMost rel relU η →
    M.ZeroKnowledgeOfSampler Λ VE hb honest pub Sim T D relU (fun tq Q => M.zkError δ tq Q + Q * η)
  /-- Unconditional witness indistinguishability against adaptively chosen statements of bounded
  encoding length. -/
  witnessIndist : ∀ (eX : SPBCS.BitEncoding X) (eW : SPBCS.BitEncoding Wit) (Q ℓ : ℕ),
    M.WitnessIndistinguishableOfLength (M.niProver Λ honest E hb) eX eW rel Q ℓ
      (Q * M.wiError δ (SPBCS.choiceCount ℓ))
  /-- Zero knowledge in the ROM against query-bounded classical adversaries. -/
  zeroKnowledgeROM : GordieHowe.NARG.ROM.EverlastingZeroKnowledge (fun x w => (x, w) ∈ rel)
    (M.niProver Λ honest E hb)
    (M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T)
    (M.zkErrorROM δ)
  /-- Zero knowledge in the QROM against adversaries all of whose queries are counted. -/
  zeroKnowledgeQueryCounted : ∀ (X' W' : Type) [Fintype X'] [DecidableEq X'] [Fintype W']
    [DecidableEq W'] (fx : X' → X) (fw : W' → Wit),
    GordieHowe.NARG.QROM.ZeroKnowledge (fun x w => (fx x, fw w) ∈ rel) queryEncoding
      ((M.niProver Λ honest E hb).comap fx fw)
      ((M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T).comap fx)
      (M.zkErrorQuery δ)
  /-- Zero knowledge in the ROM against classical adversaries all of whose queries are counted. -/
  zeroKnowledgeROMQuery : NARG.ROM.ZeroKnowledge (fun x w => (x, w) ∈ rel)
    (M.niProver Λ honest E hb)
    (M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T)
    (M.zkErrorROMQuery δ)

open Classical in
/-- **The spBCS compiler is zero knowledge and witness indistinguishable** (`PrivacyGuarantees`,
paper `thm:bcs-zk`, `thm:bcs-wi`) when the composite is honest-verifier zero knowledge at the joint
simulator `Sim` with error `δ` (`hvzk`, CY24 Definition 23.1.8). -/
@[headline]
theorem privacyGuarantees {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B)
    (Λ : SiteLayout Mg) {Wit R : Type} [Fintype R] [Nonempty R]
    {honest : Wit → R → CausalProver P t X} {Pub : Type} (pub : X → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {rel : Set (X × Wit)} {δ : ℝ≥0}
    (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    M.PrivacyGuarantees E Qs VE hb Λ honest pub Sim T rel δ where
  zeroKnowledge X' W' _ _ _ _ fx fw := M.everlastingZeroKnowledge_qrom Λ honest E VE hb T fx fw hvzk
  zeroKnowledgeOfSampler D _ _ hD := zeroKnowledgeOfSampler Λ VE hb T D hD hvzk
  witnessIndist eX eW Q ℓ :=
    unconditionallyWitnessIndistinguishable Λ VE hb hvzk eX eW Q ℓ
  zeroKnowledgeROM := everlastingZeroKnowledge_rom Λ VE hb honest pub T hvzk
  zeroKnowledgeQueryCounted X' W' _ _ _ _ fx fw := zeroKnowledgeQuery_queryBounded VE B T Λ hb fx fw hvzk
  zeroKnowledgeROMQuery := zeroKnowledge_rom Λ VE hb honest pub T hvzk

end ZK

end

end GordieHowe.SPBCS
