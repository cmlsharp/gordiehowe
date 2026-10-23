-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Instability
public import GordieHowe.Model.QROM.Expansion
public import GordieHowe.Model.QROM.ExpandAdv
public import GordieHowe.Model.QROM.Compressed
public import GordieHowe.Model.QROM.QueryStep
public import GordieHowe.Model.QROM.OracleSimulation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# The quantum lifting results of CMS19 and their generic assembly

Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum Random Oracle Model"
(CMS19, ePrint 2019/834). Page numbers are the printed ones.

The quantum objects are defined in the pure-vector model of `PQ/Quantum/`, the model of the
zero-knowledge layer. An adversary in `C*_t` is a `t`-query oracle algorithm with one query
register and a measured classical output (`QueryAlg`, `GordieHowe/Model/Quantum/Pure/QueryAlg.lean`, CMS19
section 3.2 quoted against it); here its output is a tuple `(a, b, c)` (`Adv`). The real game's
law is the Born distribution of its output with a uniformly random oracle `h : {0,1}^m → {0,1}^n`
(`QueryAlg.realLaw`). The compressed phase oracle `O = Dec ∘ O0 ∘ Dec`, the database register
with `t` slots, the final state `|Sim*(𝒜)⟩`, the outcome of `Sim*(𝒜)` and the projectors `P`
and `P_t` are defined in `GordieHowe/Model/QROM/Compressed.lean` (sections 3.5, 3.6, 5.1 and App. A quoted
against them). The oracle range is `BitStr I J = I → J → ZMod 2` (XOR), read as answers in `B`
through an equivalence `e`; the development uses `XOut k e` read as `Out k e` by `outEquiv`. The
expanded adversary of Proposition 8.11 is a composition of runs (`expandAdv`,
`GordieHowe/Model/QROM/ExpandAdv.lean`). The winning probabilities of Defs 4.6–4.8 and the values `ω*_O`,
`ω*_S`, `ω*_D` are defined from these.

## What is proved

Every quantum statement of CMS19 used here is proved in the model; this layer cites no
mathematics:
- Lemma 4.9, first inequality (`Lifting.oracle_sim`, p. 20, restating Zhandry, "How to
  Record Quantum Queries, and Applications to Quantum Indifferentiability", CRYPTO 2019, ePrint
  2018/276, Lemma 5), `√Pr[𝒜 wins G*_O] ≤ √Pr[𝒜 wins G*_S] + √(k / 2^n)`: Zhandry's Lemmas 2–5
  for the fixed-bound compressed phase oracle (`GordieHowe/Model/QROM/Purified.lean`,
  `GordieHowe/Model/QROM/FourierCompression.lean`, `GordieHowe/Model/QROM/OracleSimulation.lean`);
- Proposition 8.11's quantum half (`expand_adversary`: the adversary that runs a proof producer
  `𝒜` and then expands its proof has the real-game law of `𝒜`'s proof and oracle,
  post-processed by the expansion; the classical half is `GordieHowe.SPBCS.mem_game_of_verify`,
  `GordieHowe/SPBCS/Knowledge.lean`);
- Proposition 5.8 (`measured_prob`, `Pr[D ∈ P] = ‖P |Sim*(𝒜)⟩‖²`, from the support of
  `|Sim*(𝒜)⟩` on database states, `supported_simState`);
- Lemma 5.9 (`measured_norm_le`, `‖P |Sim*(𝒜)⟩‖ ≤ t · ‖P(P_t O P_t)P̄‖` for `∅ ∉ P`, from the
  unitarity of the Hadamard transform, `Dec` and `O0`, `GordieHowe/Model/QROM/Compressed.lean`);
- Lemma 5.10 (`query_step_le`, `‖P(P_t O P_t)P̄‖² ≤ 6 I(P, t)`, with the inputs that the paper's
  proof omits included, `GordieHowe/Model/QROM/QueryStep.lean`);
- that the outcome of `Sim*(𝒜)` has total weight `1` (`simLaw_univ`).

The development instantiates the oracle at the paper's: domain `{0,1}^m` (`Bits m`,
`GordieHowe/Model/QROM/QueryBits.lean`) and range `{0,1}^n` (`XOut k e`, `n = 8(k + e)`). The spBCS compiler's
tagged queries enter through the injective encoding `Query.toBits` (proved); its base games are
pushed forward (`BaseGame.map`) and its database properties pulled back by restriction
(`DB.restrict`), whose instabilities over `{0,1}^m` are at most those over the tagged queries
(`instab_preimage_restrict_le`, `condInstab_preimage_restrict_le`). The remaining modelling
claim is that the hashes (SHA-384 / SHA-256 on the leaf, node and transcript inputs, cSHAKE256 on
the XOF inputs), on their injectively padded inputs, are independent uniformly random functions.
The model's single oracle `{0,1}^m → {0,1}^(8(k + e))` simulates them: a hash whose real answer
has `k` bytes is the model oracle read on its `k`-byte prefix (`Out.digest`), and a real query
with a `k`-byte answer register is a model query whose other `8e` answer qubits are in the
uniform superposition, which XOR leaves unchanged; real queries outside the encoded domain are
answered by an independent random function that the adversary simulates in its work register
(a purified truth table), one model query per real query.

The rest of the development uses `expand_adversary` (through `winO_expandAdv`), Lemma 4.9's first
inequality (through `oracle_sim_card`) and `measured_le` (through its union form `dbProb_union_le`).
Proposition 5.8 and Lemmas 5.9 and 5.10 enter only through the proof of `measured_le`.

From them we prove: the measured-database bound `Pr[D ∈ R] ≤ t² · 6 · I(R, t)` for
`∅ ∉ R` (`Lifting.measured_le`), the basic lifting lemma 5.7 (`basic_lifting`), the
second half of Lemma 4.9 (`ω*_S ≤ ω*_D`, classical), the lifting lemma 5.13
(`lifting_lemma`), and the assembly theorems of the soundness proof (section 8.5.1, p. 43)
and the knowledge proof (section 8.5.2, pp. 43–44).

## Paper text (ePrint 2019/834, version of January 14, 2020)

Definition 4.1, p. 18:

    Let A, B, C be finite sets, k ∈ ℕ. A base game is a set of tuples
    G ⊆ A^k × B^k × C.

    We will use C_t to denote the set of all classical algorithms that make at most
    t queries to an oracle, and C*_t to denote the set of all quantum algorithms
    that make at most t queries to an oracle.

Section 4.2, p. 19:

    A quantum algorithm A plays the quantum oracle game of G as follows: A has
    access to a random oracle h : {0,1}^m → {0,1}^n and wins if it outputs
    (a, b, c) ∈ G with h(a_i) = b_i for all i ∈ [k].

Definition 4.6, p. 20. The value of the quantum oracle game of G is

    ω*_O(G, t) := max_{A ∈ C*_t} Pr[A wins G*_O]
                = max_{A ∈ C*_t} Pr[ (a, b, c) ∈ G and ∀ i ∈ [k], h(a_i) = b_i
                                     | h ← U(m, n), (a, b, c) ← A^h ] .

Text before Definition 4.7, p. 20:

    One can simulate the interaction of a quantum algorithm A with a random oracle
    via the compressed phase oracle O of Zhandry [Zha19]. (See Section 3.6 for the
    definition of O.) We denote by Sim*(A) the probabilistic process that executes
    A while answering its queries with O, and then outputs ((a, b, c), D) where
    (a, b, c) is the output of A (obtained by measuring its output register in the
    computational basis) and D is the result of measuring the database registers
    in the computational basis after A has halted. The quantum algorithm A wins if
    ((a, b, c), D) is such that (a, b, c) ∈ G and D(a_i) = b_i for all i ∈ [k].

Definition 4.7, p. 20. The value of the quantum simulated oracle game of G is

    ω*_S(G, t) := max_{A ∈ C*_t} Pr[A wins G*_S]
                = max_{A ∈ C*_t} Pr[ (a, b, c) ∈ G and ∀ i ∈ [k], D(a_i) = b_i
                                     | ((a, b, c), D) ← Sim*(A) ] .

Text before Definition 4.8, p. 20:

    We again simulate the quantum algorithm A using Sim*(A) to obtain
    ((a, b, c), D) but now we discard the tuple (a, b, c) and only consider the
    database D. Concretely, the quantum algorithm A wins if there exists a tuple
    (a', b', c) ∈ G such that D(a'_i) = b'_i for all i ∈ [k].

Definition 4.8, p. 20. The value of the quantum database game of G is

    ω*_D(G, t) := max_{A ∈ C*_t} Pr[A wins G*_D]
                = max_{A ∈ C*_t} Pr[ ∃ (a', b', c') ∈ G s.t. ∀ i ∈ [k], D(a'_i) = b'_i
                                     | ((a, b, c), D) ← Sim*(A) ] .

Lemma 4.9 ([Zha19]), p. 20. For every quantum algorithm A:

    √Pr[A wins G*_O] ≤ √Pr[A wins G*_S] + √(k/2^n) ,
     Pr[A wins G*_S] ≤ Pr[A wins G*_D] .

    In particular, the values of the three types of quantum games are related:

    ∀ t ∈ ℕ, √ω*_O(G, t) ≤ √ω*_S(G, t) + √(k/2^n)
         and ω*_S(G, t) ≤ ω*_D(G, t) .

    Proof. [...] The fact that √Pr[A wins G*_O] ≤ √Pr[A wins G*_S] + √(k/2^n) is a
    restatement of [Zha19, Lemma 5]. [...] if A wins G*_S then A wins G*_D
    trivially, so Pr[A wins G*_S] ≤ Pr[A wins G*_D].

Section 3.6, pp. 16–17 (compressed phase oracle), excerpts:

    [...] we follow Zhandry [Zha19] and extend the adversary's initial state with a
    random superposition of all functions h [...]. In fact, instead of considering
    a superposition of functions h, we will consider a superposition of databases
    D, according to the compressed oracle formalism of [Zha19]. Specifically,
    throughout this paper we will only deal with the compressed phase oracle with m
    input bits and n output bits, which we denote by O. We fix the database query
    bound of the compressed oracle to be t in advance. For the purposes of this
    paper, we will only use the fact that O is a certain unitary matrix,
    indistinguishable from a real random oracle, whose action is given by the
    following lemma [...].

    Lemma 3.2 ([Zha19]). The compressed phase oracle O (with query bound t) acts
    on a quantum state |x, u, z, D⟩, where x ∈ {0,1}^m, u ∈ {0,1}^n, z ∈ {0,1}^*,
    and D : {0,1}^m ⇀ {0,1}^n is a database with |D| ≤ t, as follows.
    - If |D| = t or u = 0^n, then O|x, u, z, D⟩ = (−1)^{u·D(x)} |x, u, z, D⟩,
      where u·⊥ := 0.
    - If D(x) = ⊥, |D| < t, and u ≠ 0^n, then O|x, u, z, D⟩ = |x, u, z⟩ ⊗ |φ⟩ where
        |φ⟩ := (1/√2^n) Σ_{y ∈ {0,1}^n} (−1)^{u·y} |D + [x ↦ y]⟩ .
    - If D(x) ≠ ⊥, |D| < t, and u ≠ 0^n, then O|x, u, z, D⟩ = |x, u, z⟩ ⊗ |φ⟩ where
        |φ⟩ := (−1)^{u·D(x)} |D⟩ + ((−1)^{u·D(x)}/√2^n) |D − x⟩
               + (1/2^n) Σ_{y ∈ {0,1}^n} (1 − (−1)^{u·y} − (−1)^{u·D(x)}) |D − x + [x ↦ y]⟩ .

    Given a quantum algorithm A described by unitaries A_1, ..., A_t and initial
    state |φ_0⟩, we write |Sim*(A)⟩ to represent the final state of A before
    measurement when simulated using O as the oracle. Formally,
    |Sim*(A)⟩ = A_t O ··· A_1 O |φ_0, ∅⟩, where ∅ denotes that the D register holds
    the empty database with t slots, and we implicitly extend each A_i to act as
    the identity on D.

    Lemma 3.3 ([Zha19, Lemma 4]). For any quantum oracle algorithm A making at
    most t queries,
      Tr_D(|Sim*(A)⟩⟨Sim*(A)|) = (1/(2^n)^{2^m}) Σ_{h : {0,1}^m → {0,1}^n} |A^h⟩⟨A^h| .

So `Sim*(A)` runs `A` with every query answered by `O`, starting from the empty
database, and "measure the database register" is the computational-basis
measurement of the `D` register of `|Sim*(A)⟩`, whose outcome is a database
`D` with `|D| ≤ t`.

Definition 5.2, p. 21. The database property of a base game G ⊆ A^k × B^k × C is

    P_G := {D : ∃ (a, b, c) ∈ G with D(a_i) = b_i ∀ i ∈ [k]} .

Proposition 5.3, p. 21. For every base game G ⊆ A^k × B^k × C and quantum
algorithm A,

    Pr[A wins G*_D] = Pr[ D ∈ P_G | ((a, b, c), D) ← Sim*(A) ] .

Lemma 5.7 (Basic lifting lemma), p. 22. For any base game G,

    ω*_D(G, t) ≤ t² · 6I(P_G, t) .

Proposition 5.8, p. 22. For every database property P and quantum adversary A,

    Pr[ D ∈ P | ((a, b, c), D) ← Sim*(A) ] = ‖P |Sim*(A)⟩‖² ,

    where P := I ⊗ Σ_{D ∈ P} |D⟩⟨D| is the projector that maps all basis states of
    the form |x, u, z⟩ ⊗ |D⟩ to 0 if D ∉ P, and is otherwise the identity.

Text after Proposition 5.8, p. 22:

    We learn that in order to bound ω*_D(G, t) it suffices to bound
    ‖P_G |Sim*(A)⟩‖ for every A ∈ C*_t. Next, define
    P_t := I ⊗ Σ_{D : |D| ≤ t} |D⟩⟨D| to be the projector that maps all basis
    states of the form |x, u, z⟩ ⊗ |D⟩ to 0 if |D| > t, and is otherwise the
    identity. [...] The first lemma shows that ‖P |Sim*(A)⟩‖ is bounded by
    t‖P(P_t O P_t)P̄‖. [...] The second lemma shows that ‖P(P_t O P_t)P̄‖² is
    bounded by I(P, t). Combining the two lemmas with Proposition 5.8 completes
    the proof of Lemma 5.7.

(`P̄` is the projector of the negated property `P̄`, i.e. `I − P`.)

Lemma 5.9, p. 22. Let P be a database property with ∅ ∉ P. For every A ∈ C*_t,

    ‖P |Sim*(A)⟩‖ ≤ t · ‖P(P_t O P_t)P̄‖ .

Lemma 5.10, p. 22. For any database property P,

    ‖P(P_t O P_t)P̄‖² ≤ 6 I(P, t) .

Lemma 5.13 (Lifting lemma), p. 25. Let G be a base game. Then for any database
property Q,

    ω*_D(G, t) ≤ t² · 6 (I(P_G | Q̄, t) + I(Q, t)) .

    Proof. Let P and Q be two database properties. We show that for every
    A ∈ C*_t it holds that
      ‖P |Sim*(A)⟩‖² ≤ t² · 6 (I(P | Q̄, t) + I(Q, t)) .
    Let R = P ∪ Q. Then by Lemmas 5.9 and 5.10 we have that
      ‖P |Sim*(A)⟩‖² ≤ ‖R |Sim*(A)⟩‖² ≤ t² · ‖[R, P_t O P_t]‖² ≤ t² · 6 I(R, t) ,
    where the first inequality holds since P ⊆ R. Finally, we use the fact that
    I(R, t) = I(P ∪ Q, t) ≤ I(P | Q̄, t) + I(Q, t), which completes the proof.

Proposition 8.11 and its proof, p. 42:

    Proposition 8.11. The probability that a t-query classical adversary A causes the BCS
    verifier V to accept x is at most ω_O(G^BCS_{V,x}, t + O(q log ℓ)). The probability
    that a t-query quantum adversary A causes the BCS verifier V to accept x is at most
    ω*_O(G^BCS_{V,x}, t + O(q log ℓ)).

    Proof. Let A be a (either classical or quantum) oracle algorithm. Let B be the
    algorithm that, when given access to an oracle h, runs A^h to obtain π and then
    outputs BCSExpand^h(π). The query complexity of B is t + O(q log ℓ) because A makes t
    queries and BCSExpand makes O(q log ℓ) queries. Let ((x_i)_{i=1}^a, (y_i)_{i=1}^a) be
    the output of B. By definition of BCSExpand, h(x_i) = y_i for all i ∈ [a]. Hence B^h
    wins G^BCS_{V,x} if and only if V^h(x, π) = 1.

Section 8.5.2, p. 43, on the same construction:

    Following the proof of Proposition 8.11, we obtain a t-query quantum adversary B that
    wins the BCS oracle game G^BCS_{V,x} with probability at least µ, for t := t' + O(q log ℓ).
    This transformation can be efficiently performed with black-box access to A, because B
    merely extends A with some classical computation that depends on A's (classical) output.

Section 8.5.1, p. 43, "Finishing the proof of soundness" (used by
`soundness_of_instability`):

    Since P_BCS ⊆ P_col ∪ P, we get that for any A ∈ C*_t,
    Pr_A[A wins G^BCS_{V,x}] ≤ Pr[D ∈ P_col ∪ P | ((a, b, c), D) ← Sim*(A)]. We also
    have that I(P_col ∪ P | P̄_col, t) = I(P | P̄_col, t) and ∅ ∉ P ∪ P_col (as
    state(x, ∅) = 0). Therefore, by Lemmas 5.9 and 5.10 we have that
    Pr[D ∈ P_col ∪ P | ((a, b, c), D) ← Sim*(A)] ≤ t²·6(I(P | P̄_col, t) + I(P_col, t))
    ≤ 6(t²ε + 4t³/2^λ). [...] By Lemma 4.9, we have that
    √ω*_O(G^BCS_{V,x}, t) ≤ √ω*_D(G^BCS_{V,x}, t) + O(√(q log ℓ / 2^λ)).

Section 8.5.2, pp. 43–44 (used by `knowledge_of_instability`): the extractor
`E^A(x, 1^{t'}, 1^λ)` sets `t := t' + O(q log ℓ)`, computes `|Sim*(B)⟩` by simulating
`B` via `A`, measures the database register of `|Sim*(B)⟩` to obtain `D`, and tries
to extract a witness from `D`. Then, p. 44:

    Let P_{E,σ} be the set of databases D where running tr ← BCSExtract(D, σ) and
    then w ← E(x, tr) has (x, w) ∈ R. Note that E^A(x, 1^{t'}, 1^λ) outputs a valid
    witness if and only if D ∈ ∪_{σ ∈ {0,1}^λ} P_{E,σ}. [...]

      Pr[E^A(x, 1^{t'}, 1^λ) outputs a valid witness] = Pr[D ∈ ∪_σ P_{E,σ}]
      ≥ Pr[D ∈ ∪_σ P_{E,σ} ∩ P_BCS] = Pr[D ∈ P_BCS] − Pr[D ∈ ∩_σ P̄_{E,σ} ∩ P_BCS]
      ≥ Pr[D ∈ P_BCS] − Pr[D ∈ ∩_{σ ∈ {0,1}^λ} P̄_{E,σ} ∩ ((∪_σ P_σ) ∪ P_col)]
      ≥ Pr[D ∈ P_BCS] − Pr[D ∈ P_col ∪ (∪_σ (P_σ ∩ P̄_{E,σ}))]
      ≥ Pr[B wins the BCS database game] − t² · 6 I(P_col ∪ (∪_σ (P_σ ∩ P̄_{E,σ})), t) ,

    where the second inequality follows by Proposition 8.12 and the third by the
    fact that ∩_{σ ∈ {0,1}^λ} P̄_{E,σ} ∩ ((∪_σ P_σ) ∪ P_col)
    ⊆ P_col ∪ (∪_σ (P_σ ∩ P̄_{E,σ})).
    We have that the probability that B wins the quantum database game of
    G^Mic_{V,x} is Ω(µ − q log ℓ / 2^λ) by Lemma 4.9. [...]
    Proposition 8.14. I(P_col ∪ (∪_σ (P_σ ∩ P̄_{E,σ})), t) < k + (2t + 1)/2^λ.
    Proof. We have that I(P_col ∪ (∪_σ (P_σ ∩ P̄_{E,σ})), t)
    ≤ I(P_col, t) + I(∪_σ (P_σ ∩ P̄_{E,σ}) | P̄_col, t). [...]

## Deviations from the paper

- Outcomes. The real game's outcome is a probability distribution (`QueryAlg.realLaw`); the
  outcome of `Sim*(𝒜)` is the outer measure of Born weights of `|Sim*(𝒜)⟩` (`simLaw`), of total
  weight `1` (`simLaw_univ`, from the unitarity of `O`). The deviations of the definitions of
  `O`, `Dec` and the database register are in `GordieHowe/Model/QROM/Compressed.lean`.
- Proof producers. Proposition 8.11's `B` is `expandAdv e X k 𝒜`. The paper's query count
  `t + O(q log ℓ)` is the exact count `t + k`: the expansion makes one query per entry of the
  base game's query tuple, its `k` entries (padding queries included).
- Norms are extended nonnegative reals (`‖·‖ₑ`), so that Prop 5.8 is an equation in
  `ℝ≥0∞` with `dbProb`; for vectors and operators this is the usual norm.
- Range. The paper's oracle has range `{0,1}^n`. Here the oracle's range is `BitStr I J`,
  and the base games, databases and the real game's oracle hold answers in a finite type `B`,
  read through `e : BitStr I J ≃ B`. `oracle_sim` takes `hn : Fintype.card B = 2 ^ n` and has
  `2^n` as in Lemma 4.9; `oracle_sim_card` states it with `Fintype.card B`. The development uses
  `B = Out k e` (`k + e` bytes), with `n = 8(k + e)` (`Out.card_eq_two_pow`).
- Maxima over `C*_t` are suprema in `ℝ≥0∞`.
- Finite sets. Def 4.1 asks for finite sets; the adversaries' output type here (for the
  proof-of-possession, `PK × NIProof`) is infinite. The statements of CMS19 used here do not depend on
  finiteness of the output set.
- Def 4.8's displayed formula writes `∃ (a', b', c') ∈ G`, the text before it
  writes `(a', b', c) ∈ G`. The `c` is a typo (Def 4.4, p. 19, has `c'`); `winD`
  quantifies over the whole tuple.
- `∅ ∉ ·` hypotheses. Lemma 5.9 needs `∅ ∉ P`, so `measured_le` carries `∅ ∉ R` and
  `basic_lifting` carries `∅ ∉ P_G`, which the paper's statement of Lemma 5.7 omits.
  The proof of Lemma 5.13 applies Lemma 5.9 to `R = P_G ∪ Q` without checking
  `∅ ∉ R`, and Lemma 5.13 as stated is false without it: take `Q` the property of
  all databases. Then `Q̄ = ∅`, so `I(Q, t) = 0` (every flip into `Q̄` has
  probability 0) and `I(P_G | Q̄, t) = 0` (both flips start from the empty property), so
  the right side is `0`; but for `k = 1`, `G = A × B × C` and `t ≥ 1`, `P_G` is the set of
  nonempty databases, and a single phase-oracle query at `(a, u)` with `u ≠ 0^n` leaves a
  nonempty database with probability 1 (Lemma 3.2, second case), so `ω*_D(G, t) = 1`. We add
  `∅ ∉ P_G` (automatic for `k > 0`, `BaseGame.empty_notMem_dbProperty`) and `∅ ∉ Q`.
  Section 8.5.1 checks `∅ ∉ P ∪ P_col` explicitly.
- The displayed chain in the proof of Lemma 5.13 writes the commutator `‖[R, P_t O P_t]‖²`
  in the middle. The p. 23 identity `‖[P, A]‖² = ‖PAP̄‖² + ‖P̄AP‖²` is false for operator
  norms: for a projector `P`, `[P, A] = PAP̄ − P̄AP` and its norm is the larger of `‖PAP̄‖`
  and `‖P̄AP‖` (counterexample: `A` the swap on `ℂ²`, `P = |0⟩⟨0|`). With the maximum the
  chain holds with factor 6, by Lemma 5.10 at `R` and at `R̄` (instability is symmetric
  under complement). `measured_le` uses the `‖R(P_t O P_t)R̄‖` form of Lemma 5.9 directly.
- The compressed oracle. Lemma 3.2's first case and App. A's "If |D| = t, then Dec_x does
  nothing" are wrong when `D(x) ≠ ⊥`: the stated map is not unitary. `O` is `Dec ∘ O0 ∘ Dec`
  as defined in App. A (Zhandry's compressed phase oracle at a fixed bound). Its action is
  Lemma 3.2 with the cases corrected: the phase action `(−1)^{u·D(x)} |x, u, z, D⟩` if
  `u = 0^n`, or `D(x) = ⊥` and `|D| = t`; the second case unchanged; the third case for
  `D(x) ≠ ⊥` and `|D| ≤ t`. The paper's proof of Lemma 5.10 omits the terms with `|D| = t`,
  `D(x) ≠ ⊥`, `u ≠ 0^n`; with them included the accounting again gives `6 I(P, t)`,
  which `query_step_le` proves.
- The adversary's form. `|Sim*(𝒜)⟩` is `A_t O ⋯ A_1 O |φ_0, ∅⟩` by definition (`simState`):
  each `A_i` acts as the identity on the database register, the database starts empty, and the
  adversary makes exactly `t` queries, `t` also being the bound of `O`. An adversary with fewer
  queries is padded (`GordieHowe/Model/Quantum/Pure/QueryAlg.lean`).
-/

namespace GordieHowe.QROM

open scoped ENNReal

/-! ### Square roots in `ℝ≥0∞` -/

/-- The square root on `ℝ≥0∞`, as the power `1/2`. -/
noncomputable def esqrt (a : ℝ≥0∞) : ℝ≥0∞ := a ^ (1 / 2 : ℝ)

theorem esqrt_mul_self (a : ℝ≥0∞) : esqrt a * esqrt a = a := by
  rw [esqrt, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

/-- `√a ≤ b` when `a ≤ b²`. -/
theorem esqrt_le_of_le_sq {a b : ℝ≥0∞} (h : a ≤ b ^ 2) : esqrt a ≤ b := by
  calc esqrt a ≤ esqrt (b ^ 2) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = b := by
      rw [esqrt, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

theorem esqrt_sq (a : ℝ≥0∞) : esqrt a ^ 2 = a := by rw [sq, esqrt_mul_self]

@[gcongr] theorem esqrt_le_esqrt {a b : ℝ≥0∞} (h : a ≤ b) : esqrt a ≤ esqrt b :=
  ENNReal.rpow_le_rpow h (by norm_num)

theorem esqrt_le_one {a : ℝ≥0∞} (h : a ≤ 1) : esqrt a ≤ 1 :=
  ENNReal.rpow_le_one h (by norm_num)

theorem le_sq_of_esqrt_le {a b : ℝ≥0∞} (h : esqrt a ≤ b) : a ≤ b ^ 2 := by
  rw [← esqrt_sq a]
  exact pow_le_pow_left₀ zero_le h 2

/-- From `√a ≤ √s + r` with `a ≤ 1`: `a ≤ s + 2r`. This is the step
`µ − Pr[𝒜 wins G*_S] ≤ 2√(k/2^λ)` of CMS19 section 8.5.2. -/
theorem le_add_two_mul_of_esqrt_le {a s r : ℝ≥0∞} (ha : a ≤ 1)
    (h : esqrt a ≤ esqrt s + r) : a ≤ s + 2 * r := by
  rcases le_total s 1 with hs | hs
  · have hu := esqrt_le_one ha
    have hv := esqrt_le_one hs
    calc a = esqrt a * esqrt a := (esqrt_mul_self a).symm
      _ ≤ (esqrt s + r) * esqrt a := by gcongr
      _ = esqrt s * esqrt a + r * esqrt a := add_mul _ _ _
      _ ≤ esqrt s * (esqrt s + r) + r :=
          add_le_add (by gcongr) (mul_le_of_le_one_right zero_le hu)
      _ = esqrt s * esqrt s + esqrt s * r + r := by rw [mul_add]
      _ ≤ s + r + r := by
          rw [esqrt_mul_self]
          gcongr
          exact mul_le_of_le_one_left zero_le hv
      _ = s + 2 * r := by rw [two_mul, add_assoc]
  · exact (ha.trans hs).trans le_self_add

/-- `ε + c·t/n + t/n = ε + (c+1)·t/n`. -/
theorem add_mul_div_add_div (ε c n : ℝ≥0∞) (t : ℕ) :
    ε + c * t / n + (t : ℝ≥0∞) / n = ε + (c + 1) * t / n := by
  rw [add_assoc, ENNReal.div_add_div_same, add_mul, one_mul]

/-! ### Base games -/

/-- A base game `G ⊆ A^k × B^k × C` (CMS19 Def 4.1, p. 18): a set of tuples
`(a, b, c)` of `k` oracle queries, `k` claimed answers and an output (`BaseGame.Tuple`). -/
abbrev BaseGame (A B C : Type*) (k : ℕ) := Set (BaseGame.Tuple A B C k)

variable {A B C : Type*} {k : ℕ} [DecidableEq A]

/-- `P_G` (CMS19 Def 5.2, p. 21): the databases consistent with some tuple of `G`,
`{D : ∃ (a, b, c) ∈ G, D(a_i) = b_i for all i ∈ [k]}`. -/
def BaseGame.dbProperty (G : BaseGame A B C k) : Set (DB A B) :=
  {D | ∃ o ∈ G, o.InDB D}

/-- For `k > 0` the empty database has no entries, so it is not in `P_G`. -/
theorem BaseGame.empty_notMem_dbProperty (G : BaseGame A B C k) (hk : 0 < k) :
    (∅ : DB A B) ∉ G.dbProperty := by
  rintro ⟨o, -, h⟩
  have := h ⟨0, hk⟩
  simp [Finmap.lookup_empty] at this

/-! ### Base games with encoded queries -/

section Map

variable {A' : Type*} [DecidableEq A']

/-- The base game `G` with its queries encoded by an injection `ι : A ↪ A'`:
`{(ι ∘ a, b, c) : (a, b, c) ∈ G}`. A win against an oracle `h : A' → B` is a win of `G`
against `h ∘ ι`. -/
def BaseGame.map (ι : A ↪ A') (G : BaseGame A B C k) : BaseGame A' B C k :=
  (fun o => ⟨ι ∘ o.queries, o.answers, o.out⟩) '' G

omit [DecidableEq A] [DecidableEq A'] in
theorem BaseGame.mem_map {ι : A ↪ A'} {G : BaseGame A B C k} {o : BaseGame.Tuple A B C k} :
    o ∈ G → ⟨ι ∘ o.queries, o.answers, o.out⟩ ∈ G.map ι :=
  Set.mem_image_of_mem _

/-- `P_{G.map ι}` is `P_G` pulled back along the restriction: a database on `A'` is consistent
with a tuple of the encoded game when its restriction to `A` is consistent with the tuple of
`G`. -/
theorem BaseGame.dbProperty_map (ι : A ↪ A') (G : BaseGame A B C k) :
    (G.map ι).dbProperty = DB.restrict ι ⁻¹' G.dbProperty := by
  ext D
  constructor
  · rintro ⟨_, ⟨o, ho, rfl⟩, hD⟩
    exact ⟨o, ho, fun i => (DB.lookup_restrict _).trans (hD i)⟩
  · rintro ⟨o, ho, hD⟩
    exact ⟨_, ⟨o, ho, rfl⟩, fun i => (DB.lookup_restrict _).symm.trans (hD i)⟩

end Map

/-! ### Quantum adversaries and their games -/

/-- **`C*_t` for base games with `k` queries** (CMS19 Def 4.1, p. 18, and section 3.2, p. 14): the
`t`-query quantum oracle algorithms (`QueryAlg`) with oracle domain `X`, oracle range `Y`, whose
measured output is a tuple `(a, b, c)` of `k` queries, `k` claimed answers in `B` and an output in
`C`. -/
abbrev Adv (X Y B C : Type) [Fintype X] [Fintype Y] (k t : ℕ) : Type 1 :=
  Quantum.QueryAlg X Y t (BaseGame.Tuple X B C k)

section Games

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {B C : Type} [Fintype B] (e : BitStr I J ≃ B) {k t : ℕ}

/-- `Pr[𝒜 wins G*_O]` (CMS19 Def 4.6, p. 20): `(a, b, c) ∈ G` and `h(a_i) = b_i`, for
`h ← U(m, n)` uniform and `(a, b, c) ← 𝒜^h` (`QueryAlg.realLaw`), the oracle read through `e`. -/
noncomputable def winO (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame (Bits m) B C k) :
    ℝ≥0∞ :=
  (𝒜.realLaw e).toOuterMeasure {p | p.out ∈ G ∧ p.out.AnsweredBy p.oracle}

/-- `Pr[𝒜 wins G*_S]` (CMS19 Def 4.7, p. 20): `(a, b, c) ∈ G` and `D(a_i) = b_i` for
`((a, b, c), D) ← Sim*(𝒜)` (`simLaw`); `D(a_i) = ⊥` loses. -/
noncomputable def winS (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame (Bits m) B C k) :
    ℝ≥0∞ :=
  simLaw e 𝒜 {p | p.1 ∈ G ∧ p.1.InDB p.2}

/-- The probability that the measured database of `Sim*(𝒜)` lies in `P`
(CMS19 Proposition 5.8, p. 22, left-hand side). -/
noncomputable def dbProb (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (P : Set (DB (Bits m) B)) :
    ℝ≥0∞ :=
  simLaw e 𝒜 {p | p.2 ∈ P}

/-- The probability that the measured output `c` and the measured database `D` of `Sim*(𝒜)`
satisfy `R c D`. With `R c D` independent of `c` this is `dbProb`; the knowledge bound for an
adversary that outputs its statement reads the statement from `c`. -/
noncomputable def simProb (𝒜 : Adv (Bits m) (BitStr I J) B C k t)
    (R : C → DB (Bits m) B → Prop) : ℝ≥0∞ :=
  simLaw e 𝒜 {p | R p.1.out p.2}

@[simp]
theorem simProb_eq_zero (𝒜 : Adv (Bits m) (BitStr I J) B C k t) {R : C → DB (Bits m) B → Prop}
    (h : ∀ c D, ¬ R c D) : simProb e 𝒜 R = 0 := by
  have : {p : BaseGame.Tuple (Bits m) B C k × DB (Bits m) B | R p.1.out p.2} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun _ hp => h _ _ hp
  simp only [simProb, this, MeasureTheory.measure_empty]

theorem simProb_mono (𝒜 : Adv (Bits m) (BitStr I J) B C k t) {R R' : C → DB (Bits m) B → Prop}
    (h : ∀ c D, R c D → R' c D) : simProb e 𝒜 R ≤ simProb e 𝒜 R' :=
  MeasureTheory.measure_mono fun _ hp => h _ _ hp

/-- `Pr[𝒜 wins G*_D]` (CMS19 Def 4.8, p. 20): some `(a', b', c') ∈ G` has
`D(a'_i) = b'_i`. The text before Def 4.8 writes `(a', b', c)`; the displayed
formula of Def 4.8 and Def 4.4 (p. 19) have `c'`. -/
noncomputable def winD (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame (Bits m) B C k) :
    ℝ≥0∞ :=
  simLaw e 𝒜 {p | ∃ o ∈ G, o.InDB p.2}

/-- CMS19 Proposition 5.3, p. 21: winning the database game is the measured database
lying in `P_G`. -/
theorem winD_eq_dbProb (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame (Bits m) B C k) :
    winD e 𝒜 G = dbProb e 𝒜 G.dbProperty := rfl

/-- `Pr[𝒜 wins (G.map ι)*_D]` is the probability that the restriction of the measured database
lies in `P_G`. -/
theorem winD_map {A' : Type*} [DecidableEq A'] {ι : A' ↪ Bits m}
    (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame A' B C k) :
    winD e 𝒜 (G.map ι) = dbProb e 𝒜 (DB.restrict ι ⁻¹' G.dbProperty) := by
  rw [winD_eq_dbProb, BaseGame.dbProperty_map]

/-- CMS19 Lemma 4.9, second inequality, p. 20 (classical: the event is contained). -/
theorem winS_le_winD (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame (Bits m) B C k) :
    winS e 𝒜 G ≤ winD e 𝒜 G :=
  MeasureTheory.measure_mono fun p hp => ⟨p.1, hp.1, hp.2⟩

/-- **The simulated win splits along a cover of the base game** (the step of CMS19 section
8.5.2, p. 44, that uses Proposition 8.12): if every database consistent with a tuple
`(a, b, c) ∈ G` satisfies `R c` or lies in `P`, then `Pr[𝒜 wins G*_S]` is at most the
probability that the measured output and database of `Sim*(𝒜)` satisfy `R`, plus
`Pr[D ∈ P]`. -/
theorem winS_le_simProb_add (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame (Bits m) B C k)
    {R : C → DB (Bits m) B → Prop} {P : Set (DB (Bits m) B)}
    (hG : ∀ o ∈ G, ∀ D : DB (Bits m) B, o.InDB D → R o.out D ∨ D ∈ P) :
    winS e 𝒜 G ≤ simProb e 𝒜 R + dbProb e 𝒜 P :=
  (MeasureTheory.measure_mono fun p hp => hG p.1 hp.1 p.2 hp.2).trans
    (MeasureTheory.measure_union_le
      {p : BaseGame.Tuple (Bits m) B C k × DB (Bits m) B | R p.1.out p.2} {p | p.2 ∈ P})

theorem winO_le_one [Nonempty B] (𝒜 : Adv (Bits m) (BitStr I J) B C k t)
    (G : BaseGame (Bits m) B C k) : winO e 𝒜 G ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
    ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _))

theorem dbProb_mono (𝒜 : Adv (Bits m) (BitStr I J) B C k t) {P P' : Set (DB (Bits m) B)}
    (h : P ⊆ P') : dbProb e 𝒜 P ≤ dbProb e 𝒜 P' :=
  MeasureTheory.measure_mono fun _ hp => h hp

@[simp]
theorem dbProb_empty (𝒜 : Adv (Bits m) (BitStr I J) B C k t) : dbProb e 𝒜 ∅ = 0 := by
  simp only [dbProb, Set.mem_empty_iff_false, Set.ofPred_false, MeasureTheory.measure_empty]

theorem dbProb_union_le (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (P P' : Set (DB (Bits m) B)) :
    dbProb e 𝒜 (P ∪ P') ≤ dbProb e 𝒜 P + dbProb e 𝒜 P' :=
  MeasureTheory.measure_union_le
    {p : BaseGame.Tuple (Bits m) B C k × DB (Bits m) B | p.2 ∈ P} {p | p.2 ∈ P'}

/-- **CMS19 Proposition 5.8** (p. 22): "For every database property P and quantum adversary A,
Pr[D ∈ P | ((a, b, c), D) ← Sim*(A)] = ‖P |Sim*(A)⟩‖²", for the projector
`P = I ⊗ ∑_{D ∈ P} |D⟩⟨D|` (`dbProj`). -/
theorem measured_prob (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (P : Set (DB (Bits m) B)) :
    dbProb e 𝒜 P = ‖dbProj e 𝒜.W t P (simState e 𝒜)‖ₑ ^ 2 := by
  rw [dbProb, simLaw, MeasureTheory.OuterMeasure.map_apply, Quantum.bornWeight_apply, dbProj]
  congr 2
  refine (supported_simState e 𝒜).mask_eq fun b hb => ?_
  obtain ⟨hsize, hs⟩ := IsDBState.dbSlots_slotsDB e hb
  constructor
  · intro h
    exact ⟨slotsDB e b.2, h, hsize, hs.symm⟩
  · rintro ⟨D, hD, hDt, hbD⟩
    show slotsDB e b.2 ∈ P
    rwa [hbD, slotsDB_dbSlots e hDt]

/-- `ω*_O(G, t)` (CMS19 Def 4.6, p. 20). The maximum over `C*_t` is a supremum. -/
noncomputable def ωO (G : BaseGame (Bits m) B C k) (t : ℕ) : ℝ≥0∞ :=
  ⨆ 𝒜 : Adv (Bits m) (BitStr I J) B C k t, winO e 𝒜 G

/-- `ω*_S(G, t)` (CMS19 Def 4.7, p. 20). -/
noncomputable def ωS (G : BaseGame (Bits m) B C k) (t : ℕ) : ℝ≥0∞ :=
  ⨆ 𝒜 : Adv (Bits m) (BitStr I J) B C k t, winS e 𝒜 G

/-- `ω*_D(G, t)` (CMS19 Def 4.8, p. 20). -/
noncomputable def ωD (G : BaseGame (Bits m) B C k) (t : ℕ) : ℝ≥0∞ :=
  ⨆ 𝒜 : Adv (Bits m) (BitStr I J) B C k t, winD e 𝒜 G

/-- CMS19 Lemma 4.9, `ω*_S(G, t) ≤ ω*_D(G, t)`. -/
theorem ωS_le_ωD (G : BaseGame (Bits m) B C k) (t : ℕ) : ωS e G t ≤ ωD e G t :=
  iSup_mono fun 𝒜 => winS_le_winD e 𝒜 G

end Games

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {B : Type} [Fintype B] [Nonempty B]

/-- **CMS19 Proposition 8.11** (p. 42), per adversary: if every expanded accepted proof wins
`G` (the classical half), the probability that `𝒜` outputs an accepted proof is at most
`Pr[expandAdv e X k 𝒜 wins G*_O]`. The quantum half is the proved `expand_adversary`. -/
theorem winO_expandAdv {C : Type} {k t : ℕ} (e : BitStr I J ≃ B) (X : Expansion (Bits m) B C)
    (𝒜 : Quantum.QueryAlg (Bits m) (BitStr I J) t C) {G : BaseGame (Bits m) B C k}
    {Acc : Set (Quantum.Outcome C (Bits m) B)} (hG : ∀ p ∈ Acc, X.expand p.oracle p.out ∈ G) :
    (𝒜.realLaw e).toOuterMeasure Acc ≤ winO e (expandAdv e X k 𝒜) G := by
  rw [winO, expand_adversary, PMF.toOuterMeasure_map_apply]
  exact MeasureTheory.measure_mono fun p hp => ⟨hG p hp, fun _ => rfl⟩

namespace Lifting

/-! ### CMS19's lifting results

The theorems below are CMS19's quantum lifting results for the objects defined above (the
namespace is named after the paper section's role, not a structure): Lemma 4.9's first inequality
(`oracle_sim`, proved as Zhandry's Lemma 5 in `GordieHowe/Model/QROM/OracleSimulation.lean`), the measured-database
bound, Lemmas 5.7 and 5.13 and the assembly theorems of section 8.5. -/

variable (e : BitStr I J ≃ B) {C : Type} {k : ℕ} {t : ℕ}

/-- **CMS19 Lemma 4.9** ([Zha19]), first inequality (p. 20), with the range size written
`Fintype.card B`: `√Pr[𝒜 wins G*_O] ≤ √Pr[𝒜 wins G*_S] + √(k / |B|)`. This is Zhandry's Lemma 5
("How to Record Quantum Queries", ePrint 2018/276, p. 16, proof App. B.3), proved for the
fixed-bound compressed phase oracle of `Sim*` as `oracle_sim_sets`; repeated `a_i` and `k = 0` are
included (Zhandry's proof, App. B.3, pp. 33–35, assumes distinct `a_i` and starts at `k = 1`). -/
theorem oracle_sim_card (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame (Bits m) B C k) :
    esqrt (winO e 𝒜 G) ≤ esqrt (winS e 𝒜 G) + esqrt (k / Fintype.card B) := by
  classical
  exact oracle_sim_sets e 𝒜 G

/-- **CMS19 Lemma 4.9** ([Zha19]), first inequality (p. 20): "For every quantum algorithm A:
√Pr[A wins G*_O] ≤ √Pr[A wins G*_S] + √(k/2^n)", for a range `B` with `2^n` elements.
Correspondence: `√` ↔ `esqrt`; the second inequality is `winS_le_winD`, the "In particular" form
is `ωO_le_sq` (squared). -/
theorem oracle_sim {n : ℕ} (hn : Fintype.card B = 2 ^ n) (𝒜 : Adv (Bits m) (BitStr I J) B C k t)
    (G : BaseGame (Bits m) B C k) :
    esqrt (winO e 𝒜 G) ≤ esqrt (winS e 𝒜 G) + esqrt (k / 2 ^ n) := by
  have h := oracle_sim_card e 𝒜 G
  rwa [hn, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **The measured-database bound**: for a database property `R` with `∅ ∉ R`,
`Pr[D ∈ R | ((a, b, c), D) ← Sim*(𝒜)] ≤ t² · 6 · I(R, t)`. This is Proposition 5.8, then
Lemma 5.9 squared, then Lemma 5.10:
`Pr[D ∈ R] = ‖R |Sim*(𝒜)⟩‖² ≤ t² · ‖R(P_t O P_t)R̄‖² ≤ t² · 6 · I(R, t)`.

The paper states this combination only for `R = P_G` (Lemma 5.7, `basic_lifting`); its
proofs of Lemma 5.13 (p. 25, `R = P ∪ Q`) and of knowledge (section 8.5.2, p. 44,
`R = P_col ∪ (∪_σ (P_σ ∩ P̄_{E,σ}))`) use it for general `R` with `∅ ∉ R`. The displayed
chain on p. 25 writes the commutator `‖[R, P_t O P_t]‖²`; this proof uses the
`‖R(P_t O P_t)R̄‖` form of Lemma 5.9 directly (module docstring, "Deviations"). -/
theorem measured_le (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (R : Set (DB (Bits m) B)) (hR : (∅ : DB (Bits m) B) ∉ R) :
    dbProb e 𝒜 R ≤ (t : ℝ≥0∞) ^ 2 * 6 * instab R t := by
  rw [measured_prob, mul_assoc]
  calc ‖dbProj e 𝒜.W t R (simState e 𝒜)‖ₑ ^ 2
      ≤ ((t : ℝ≥0∞) * ‖dbProj e 𝒜.W t R ∘L queryStepOp e 𝒜.W t ∘L dbProj e 𝒜.W t Rᶜ‖ₑ) ^ 2 := by
        gcongr
        exact measured_norm_le e 𝒜 R hR
    _ = (t : ℝ≥0∞) ^ 2 * ‖dbProj e 𝒜.W t R ∘L queryStepOp e 𝒜.W t ∘L dbProj e 𝒜.W t Rᶜ‖ₑ ^ 2 :=
        mul_pow _ _ 2
    _ ≤ (t : ℝ≥0∞) ^ 2 * (6 * instab R t) := by
        gcongr
        exact query_step_le e 𝒜.W t R

/-- **CMS19 Lemma 5.7** (basic lifting lemma, p. 22): "For any base game G,
ω*_D(G, t) ≤ t² · 6I(P_G, t)." The hypothesis `∅ ∉ P_G` is needed for Lemma 5.9 and is
absent from the paper's statement, as for Lemma 5.13; it holds for `k > 0`
(`BaseGame.empty_notMem_dbProperty`). -/
theorem basic_lifting (G : BaseGame (Bits m) B C k) (hG : (∅ : DB (Bits m) B) ∉ G.dbProperty) :
    ωD e G t ≤ (t : ℝ≥0∞) ^ 2 * 6 * instab G.dbProperty t :=
  iSup_le fun 𝒜 => measured_le e 𝒜 _ hG

/-- CMS19 Lemma 4.9, first inequality, squared: `Pr[𝒜 wins G*_O] ≤ (√Pr[𝒜 wins G*_S] + √(k/|B|))²`. -/
theorem winO_le_sq (𝒜 : Adv (Bits m) (BitStr I J) B C k t) (G : BaseGame (Bits m) B C k) :
    winO e 𝒜 G ≤ (esqrt (winS e 𝒜 G) + esqrt (k / Fintype.card B)) ^ 2 :=
  le_sq_of_esqrt_le (oracle_sim_card e 𝒜 G)

/-- CMS19 Lemma 4.9 at the level of values: `ω*_O ≤ (√ω*_S + √(k/|B|))²`. -/
theorem ωO_le_sq (G : BaseGame (Bits m) B C k) :
    ωO e G t ≤ (esqrt (ωS e G t) + esqrt (k / Fintype.card B)) ^ 2 :=
  iSup_le fun 𝒜 => (winO_le_sq e 𝒜 G).trans
    (by gcongr; exact le_iSup (fun 𝒜 => winS e 𝒜 G) 𝒜)

/-- The measured-database bound for a union, as in the proof of CMS19 Lemma 5.13
(p. 25): for `∅ ∉ P` and `∅ ∉ Q`,
`Pr[D ∈ P ∪ Q] ≤ t² · 6 · (I(P | Q̄, t) + I(Q, t))`. -/
theorem dbProb_union_le {P Q : Set (DB (Bits m) B)} (hP : (∅ : DB (Bits m) B) ∉ P) (hQ : (∅ : DB (Bits m) B) ∉ Q)
    (𝒜 : Adv (Bits m) (BitStr I J) B C k t) :
    dbProb e 𝒜 (P ∪ Q) ≤ (t : ℝ≥0∞) ^ 2 * 6 * (condInstab P Qᶜ t + instab Q t) :=
  (measured_le e 𝒜 _ fun h0 => h0.elim hP hQ).trans (by gcongr; exact instab_union_le)

/-- CMS19 Lemma 5.13 (lifting lemma), p. 25, per adversary. The hypotheses
`∅ ∉ P_G` and `∅ ∉ Q` are needed (Lemma 5.9 is applied to `P_G ∪ Q`); see
`BaseGame.empty_notMem_dbProperty` for `P_G`. -/
theorem winD_le (G : BaseGame (Bits m) B C k) {Q : Set (DB (Bits m) B)} (hG : (∅ : DB (Bits m) B) ∉ G.dbProperty)
    (hQ : (∅ : DB (Bits m) B) ∉ Q) (𝒜 : Adv (Bits m) (BitStr I J) B C k t) :
    winD e 𝒜 G ≤ (t : ℝ≥0∞) ^ 2 * 6 * (condInstab G.dbProperty Qᶜ t + instab Q t) :=
  (dbProb_mono e 𝒜 Set.subset_union_left).trans (Lifting.dbProb_union_le e hG hQ 𝒜)

/-- CMS19 Lemma 5.13 (lifting lemma), p. 25:
`ω*_D(G, t) ≤ t² · 6 · (I(P_G | Q̄, t) + I(Q, t))`, for `∅ ∉ P_G` and `∅ ∉ Q`.
The paper states it for every `Q`; that is false for `Q` the property of all
databases (module docstring, "Deviations"), hence `hQ`. -/
theorem lifting_lemma (G : BaseGame (Bits m) B C k) {Q : Set (DB (Bits m) B)}
    (hG : (∅ : DB (Bits m) B) ∉ G.dbProperty) (hQ : (∅ : DB (Bits m) B) ∉ Q) :
    ωD e G t ≤ (t : ℝ≥0∞) ^ 2 * 6 * (condInstab G.dbProperty Qᶜ t + instab Q t) :=
  iSup_le fun 𝒜 => winD_le e G hG hQ 𝒜

/-- The bound on the measured database used by both assembly theorems: if `P_G`
lies in `P ∪ P_col` with `∅ ∉ P` and `I(P | P̄_col, t) ≤ ε + c·t/|B|`, then
`Pr[D ∈ P ∪ P_col] ≤ 6 t² (ε + (c+1) t/|B|)` (CMS19 p. 43, "Finishing the proof of
soundness", using Lemma 6.11). -/
theorem dbProb_union_collision_le {P : Set (DB (Bits m) B)} (hP : (∅ : DB (Bits m) B) ∉ P)
    {ε c : ℝ≥0∞} (hI : condInstab P collisionᶜ t ≤ ε + c * t / Fintype.card B)
    (𝒜 : Adv (Bits m) (BitStr I J) B C k t) :
    dbProb e 𝒜 (P ∪ collision) ≤ 6 * (t : ℝ≥0∞) ^ 2 * (ε + (c + 1) * t / Fintype.card B) := by
  refine (Lifting.dbProb_union_le e hP empty_notMem_collision 𝒜).trans ?_
  rw [mul_comm ((t : ℝ≥0∞) ^ 2) 6, ← add_mul_div_add_div]
  gcongr
  exact instab_collision_le

/-- Generic soundness assembly (CMS19 section 8.5.1, p. 43; section 6.3, p. 33).
Let `P` be a property with `P_G ⊆ P ∪ P_col` (Proposition 8.12) and `∅ ∉ P`, and
suppose `I(P | P̄_col, t) ≤ ε + c·t/|B|` (Lemma 8.13 with `c·t ≥ 2t + 1`). Then
`ω*_O(G, t) ≤ (√(6 t² (ε + (c+1) t/|B|)) + √(k/|B|))²`. -/
theorem soundness_of_instability (G : BaseGame (Bits m) B C k) {P : Set (DB (Bits m) B)}
    (hsub : G.dbProperty ⊆ P ∪ collision) (hP : (∅ : DB (Bits m) B) ∉ P) {ε c : ℝ≥0∞}
    (hI : condInstab P collisionᶜ t ≤ ε + c * t / Fintype.card B) :
    ωO e G t ≤ (esqrt (6 * (t : ℝ≥0∞) ^ 2 * (ε + (c + 1) * t / Fintype.card B))
      + esqrt (k / Fintype.card B)) ^ 2 := by
  refine iSup_le fun 𝒜 => (winO_le_sq e 𝒜 G).trans ?_
  gcongr
  calc winS e 𝒜 G ≤ winD e 𝒜 G := winS_le_winD e 𝒜 G
    _ ≤ dbProb e 𝒜 (P ∪ collision) := dbProb_mono e 𝒜 hsub
    _ ≤ _ := dbProb_union_collision_le e hP hI 𝒜

/-- `soundness_of_instability` with `P = P_G`, the form of Lemma 6.10 for Micali
(CMS19 p. 33): from `I(P_G | P̄_col, t) ≤ ε + c·t/|B|`. -/
theorem soundness_of_instability_self (G : BaseGame (Bits m) B C k)
    (hG : (∅ : DB (Bits m) B) ∉ G.dbProperty) {ε c : ℝ≥0∞}
    (hI : condInstab G.dbProperty collisionᶜ t ≤ ε + c * t / Fintype.card B) :
    ωO e G t ≤ (esqrt (6 * (t : ℝ≥0∞) ^ 2 * (ε + (c + 1) * t / Fintype.card B))
      + esqrt (k / Fintype.card B)) ^ 2 :=
  soundness_of_instability e G Set.subset_union_left hG hI

/-- Generic knowledge assembly (CMS19 section 8.5.2, pp. 43–44). `E` is the set of
databases from which the extractor outputs a valid witness (`∪_σ P_{E,σ}`), so
`dbProb e 𝒜 E` is the extraction probability. `Bad` is `∪_σ (P_σ ∩ P̄_{E,σ})`; the
hypothesis `hsub` is the inclusion `P_G ∩ Ē ⊆ Bad ∪ P_col` used in the chain on p. 44
(from Proposition 8.12), and `hI` is Proposition 8.14's bound on
`I(Bad | P̄_col, t)` with `c·t ≥ 2t + 1`. The conclusion is
`µ − Pr[extract] ≤ 2√(k/|B|) + 6t² (κ + (c+1) t/|B|)` with `µ = Pr[𝒜 wins G*_O]`,
written without subtraction. -/
theorem knowledge_of_instability (G : BaseGame (Bits m) B C k) {E Bad : Set (DB (Bits m) B)}
    (hsub : G.dbProperty ⊆ E ∪ (Bad ∪ collision)) (hBad : (∅ : DB (Bits m) B) ∉ Bad)
    {κ c : ℝ≥0∞} (hI : condInstab Bad collisionᶜ t ≤ κ + c * t / Fintype.card B)
    (𝒜 : Adv (Bits m) (BitStr I J) B C k t) :
    winO e 𝒜 G ≤ dbProb e 𝒜 E + 2 * esqrt (k / Fintype.card B)
      + 6 * (t : ℝ≥0∞) ^ 2 * (κ + (c + 1) * t / Fintype.card B) := by
  have hO := le_add_two_mul_of_esqrt_le (winO_le_one e 𝒜 G)
    (oracle_sim_card e 𝒜 G)
  have hS : winS e 𝒜 G ≤ dbProb e 𝒜 E
      + 6 * (t : ℝ≥0∞) ^ 2 * (κ + (c + 1) * t / Fintype.card B) :=
    calc winS e 𝒜 G ≤ winD e 𝒜 G := winS_le_winD e 𝒜 G
      _ ≤ dbProb e 𝒜 (E ∪ (Bad ∪ collision)) := dbProb_mono e 𝒜 hsub
      _ ≤ dbProb e 𝒜 E + dbProb e 𝒜 (Bad ∪ collision) := _root_.GordieHowe.QROM.dbProb_union_le e 𝒜 _ _
      _ ≤ _ := by gcongr; exact dbProb_union_collision_le e hBad hI 𝒜
  calc winO e 𝒜 G ≤ winS e 𝒜 G + 2 * esqrt (k / Fintype.card B) := hO
    _ ≤ _ := by
        rw [add_right_comm]
        gcongr

end Lifting

end GordieHowe.QROM
