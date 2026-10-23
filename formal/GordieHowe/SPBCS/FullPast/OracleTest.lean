-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.SimExtractTest
public import GordieHowe.Model.Quantum.Interactive.ProgAlg
public import GordieHowe.Model.Quantum.Interactive.KeptTestAdaptive
public import GordieHowe.Model.Quantum.Interactive.Embed
public import GordieHowe.Model.Quantum.Interactive.Test
public import GordieHowe.Model.Quantum.OracleTestBoundary
public import GordieHowe.Model.QROM.Instability
public import GordieHowe.SPBCS.Extraction.ProveLemmas
public import GordieHowe.SPBCS.FullPast.ProverProg
public import GordieHowe.SPBCS.FullPast.Online

@[expose] public section

/-!
# The oracle-test gap lemma for the series–parallel base model: eq. (6) fails for oracle tests

The counterexample to eq. (6) of Unruh 2017 (ePrint 2017/398, Definition 14, p. 21) for tests that
query the oracle (the oracle-test gap lemma of `GordieHowe/Model/Quantum/OracleTestBoundary.lean`), stated for
the simulation-extraction game of the series–parallel base model (`GordieHowe.SPBCS.FullPast`) and generic in
the verifier's acceptance predicate `acc` and the honest prover program `Pv`, so that it applies to
the spBCS compiler (`acc = GordieHowe.SPBCS.Accepts`, `Pv` the prover `GordieHowe.SPBCS.niProver` run through `queryEncoding`,
`GordieHowe.SPBCS.oracleTest_eq6_fails_eventually`, `GordieHowe/SPBCS/OracleTest.lean`). Only the game reads the model.

- `WinsWith acc`, `winTestProbWith acc`: the event of Prove with the acceptance predicate `acc` (a
  fresh statement accepted under the final oracle), and the probability that an adversary with
  run-time kinds wins it with a query-free test of its workspace; the spBCS compiler's
  `GordieHowe.SPBCS.Wins` and `GordieHowe.SPBCS.winTestProb` are the case `acc = Accepts`.
- `SimExtractionAdversary.acceptsQTestWith acc`: Prove with `acc` and a residual-state test that
  queries the oracle; the spBCS compiler's `GordieHowe.SPBCS.acceptsQTest` is the case `acc = Accepts`.
- `FixedSimExtractionAdversary`: adversaries with a static schedule (`Quantum.IAlg`); with
  channels as steps, their embedding is a query-bounded adversary of `def:adversary`
  (`toQueryBounded`).
- `oracleTestAdversary Pv π₀ x wit X'`: the honest prover program on `x` with a witness drawn from
  `wit`, plus one kept query on the uniform superposition of the Merkle-node inputs (`nodeInputs`),
  no proof query; `oracleTestQB`: its embedding, a query-bounded adversary with one query more than the
  prover program; `oracleTestQBTest`: its test (one query to the final oracle, then the projective
  measurement onto that superposition), a residual-state test of the adversaries with run-time
  kinds (`IAlg.QTest.toAdaptive`); the statements below are about them, in the form of the
  query-free headlines (`acceptsQTest`, Unruh's Prove with the test).
- `winTestProbWith_oracleTestQB`: Prove with the test is the probability that `acc` holds for the
  claim of the prover program (the pure run of the adversary followed by the test,
  `OracleProg.pureRun_withTest_keptTest_toAdaptive`).
- `oracleTest_acceptsQTestWith_ge`: Prove passes the test with probability at least `1 − εc` when
  `acc` rejects the claim of the honest prover program with probability at most `εc`.
- `oracleTest_eq6_fails_eventually_with` (and `GordieHowe.SPBCS.oracleTest_eq6_fails_eventually` for the
  spBCS compiler): along a family of instances within the bounds `OracleTestBounds` (statements,
  witness laws and rejection bounds depending on `η`; digests of at least `η` bytes, completeness
  error eventually at most `1/2`, the byte lengths of the model, the statement and the witnesses
  polynomial in `η`), with polynomially bounded assignment lists, eq. (6) fails for all large `η`,
  for every polynomially bounded `p`, every `d` and every negligible `µ`.
-/

namespace GordieHowe.SPBCS

open Finset GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

variable {k kN kS L e : ℕ}

/-! ### Oracle inputs -/

/-- **A uniform oracle on bit strings seen through the query encoding is uniform**: an event on
`chainOracle H` for `H` uniform has the probability of that event on a uniform oracle on queries
(the encoding `Query.toBits` is injective). -/
theorem probUniform_chainOracle (E : (Query k kN kS L → Out k e) → Prop) :
    Pr[H ← (Bits (queryBits k kN kS L) → XOut k e) : E (chainOracle H)] =
      Pr[h ← (Query k kN kS L → Out k e) : E h] := by
  have h1 : Pr[H ← (Bits (queryBits k kN kS L) → XOut k e) : E (chainOracle H)] =
      Pr[H ← (Bits (queryBits k kN kS L) → XOut k e) :
        (fun g : Query k kN kS L → XOut k e => E (outEquiv k e ∘ g)) (H ∘ Query.toBits)] := rfl
  rw [h1]
  exact (probUniform_comp_embedding Query.toBits _).trans
    (QROM.probUniform_equiv (Equiv.arrowCongr (Equiv.refl _) (outEquiv k e)) E)

/-- **The Merkle-node inputs** `H(0x02 ‖ left ‖ right)` (`Query.node`), as oracle inputs: the set
`X0` of the oracle-test gap lemma. -/
noncomputable def nodeInputs : Finset (Bits (queryBits k kN kS L)) :=
  Finset.univ.image fun lr : Digest k × Digest k => Query.toBits (.node lr.1 lr.2 : Query k kN kS L)

theorem nodeInputs_nonempty : (nodeInputs (k := k) (kN := kN) (kS := kS) (L := L)).Nonempty :=
  Finset.univ_nonempty.image _

/-- There are `|Digest k|^2` Merkle-node inputs: the query encoding is injective. -/
theorem card_nodeInputs :
    (nodeInputs (k := k) (kN := kN) (kS := kS) (L := L)).card = Fintype.card (Digest k) ^ 2 := by
  rw [nodeInputs, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod, sq]
  intro a b h
  have h' := Query.toBits.injective h
  simp only [Query.node.injEq] at h'
  exact Prod.ext h'.1 h'.2

/-- At least `2^k` Merkle-node inputs. -/
theorem two_pow_le_card_nodeInputs :
    2 ^ k ≤ (nodeInputs (k := k) (kN := kN) (kS := kS) (L := L)).card := by
  rw [card_nodeInputs]
  simp only [Digest, Byte, Fintype.card_fun, Fintype.card_fin]
  calc 2 ^ k ≤ 256 ^ k := Nat.pow_le_pow_left (by norm_num) _
    _ ≤ (256 ^ k) ^ 2 := Nat.le_self_pow (by norm_num) _

/-- At least `2^k` oracle answers: an answer has `k + e` bytes. -/
theorem two_pow_le_card_xOut : 2 ^ k ≤ Fintype.card (XOut k e) := by
  simp only [XOut, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  calc 2 ^ k ≤ 2 ^ (8 * (k + e)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ 8) ^ (k + e) := by rw [pow_mul]

/-- **The error of the oracle-test gap lemma is negligible along a family** whose digests grow (`k η ≥ η`) and whose
assignment lists are polynomially bounded (`ℓ η ≤ C' η^c'`): `(1/√|Y| + √(ℓ/N))² ≤ 2/|Y| + 2ℓ/N`,
both below `2^-η` times a polynomial, so it is eventually below `η^-j` for every `j`. -/
theorem lemma1Error_negligible {k kN kS L e ℓ : ℕ → ℕ} (hk : ∀ η, η ≤ k η) {C' : ℝ} {c' : ℕ}
    (hC' : 0 ≤ C') (hℓ : ∀ᶠ η in Filter.atTop, (ℓ η : ℝ) ≤ C' * (η : ℝ) ^ c') (j : ℕ) :
    ∀ᶠ η : ℕ in Filter.atTop, (η : ℝ) ^ j *
      ((√(Fintype.card (XOut (k η) (e η)) : ℝ))⁻¹ +
        √(ℓ η / (nodeInputs (k := k η) (kN := kN η) (kS := kS η) (L := L η)).card)) ^ 2 ≤ 1 := by
  have ht1 := tendsto_pow_const_div_const_pow_of_one_lt j (by norm_num : (1 : ℝ) < 2)
  have ht2 := tendsto_pow_const_div_const_pow_of_one_lt (j + c') (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hℓ, (tendsto_order.1 ht1).2 (1 / 4) (by norm_num),
    (tendsto_order.1 ht2).2 (1 / (4 * (C' + 1))) (by positivity)] with η hℓη h1 h2
  have h2η : (0 : ℝ) < 2 ^ η := by positivity
  have hY : (2 : ℝ) ^ η ≤ Fintype.card (XOut (k η) (e η)) := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num) (hk η)).trans two_pow_le_card_xOut
  have hN : (2 : ℝ) ^ η ≤ (nodeInputs (k := k η) (kN := kN η) (kS := kS η) (L := L η)).card := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num) (hk η)).trans two_pow_le_card_nodeInputs
  have hYpos : (0 : ℝ) < Fintype.card (XOut (k η) (e η)) := h2η.trans_le hY
  have hNpos : (0 : ℝ) < (nodeInputs (k := k η) (kN := kN η) (kS := kS η) (L := L η)).card :=
    h2η.trans_le hN
  set u := (√(Fintype.card (XOut (k η) (e η)) : ℝ))⁻¹
  set v := √((ℓ η : ℝ) / (nodeInputs (k := k η) (kN := kN η) (kS := kS η) (L := L η)).card)
  have hu : u ^ 2 ≤ ((2 : ℝ) ^ η)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hYpos.le]
    exact inv_anti₀ h2η hY
  have hv : v ^ 2 ≤ C' * (η : ℝ) ^ c' / 2 ^ η := by
    rw [Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) hNpos.le)]
    exact div_le_div₀ (by positivity) hℓη h2η hN
  have hsq : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by nlinarith [sq_nonneg (u - v)]
  have hxk : (0 : ℝ) ≤ (η : ℝ) ^ j := by positivity
  calc (η : ℝ) ^ j * (u + v) ^ 2 ≤
        (η : ℝ) ^ j * (2 * ((2 : ℝ) ^ η)⁻¹ + 2 * (C' * (η : ℝ) ^ c' / 2 ^ η)) :=
        mul_le_mul_of_nonneg_left (hsq.trans (by linarith)) hxk
    _ = 2 * ((η : ℝ) ^ j / 2 ^ η) + 2 * C' * ((η : ℝ) ^ (j + c') / 2 ^ η) := by
        rw [pow_add]
        field_simp
    _ ≤ 2 * (1 / 4) + 2 * C' * (1 / (4 * (C' + 1))) := by
        gcongr
    _ ≤ 1 := by
        rw [show 2 * C' * (1 / (4 * (C' + 1))) = C' / (2 * (C' + 1)) by field_simp; ring]
        have : C' / (2 * (C' + 1)) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith
        linarith

/-- A fixed oracle input, the padding query of the compiled program after the prover's last
query. -/
def padInput : Bits (queryBits k kN kS L) := fun _ => false

/-- The basis state of the kept pair that the test accepts. -/
def keptAccept : Bits (queryBits k kN kS L) × XOut k e := (padInput, 0)

theorem norm_graphState {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {X0 : Finset X} (hX0 : X0.Nonempty) (G : X → Y) : ‖graphState X0 G‖ = 1 := by
  have hN : (0 : ℝ) < X0.card := Nat.cast_pos.2 hX0.card_pos
  have h : ‖graphState X0 G‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    have hx : ∀ x, ∑ y, ‖graphState X0 G (x, y)‖ ^ 2 =
        if x ∈ X0 then ((√(X0.card : ℝ))⁻¹) ^ 2 else 0 := by
      intro x
      rw [Fintype.sum_eq_single (G x) fun y hy => by simp [graphState, hy]]
      by_cases hx : x ∈ X0
      · simp [graphState, hx]
      · simp [graphState, hx]
    rw [Fintype.sum_congr _ _ hx, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, inv_pow, Real.sq_sqrt hN.le, mul_inv_cancel₀ hN.ne']
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [h, one_pow])

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  {M : Base P t X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

/-! ### Prove with an acceptance predicate -/

section Wins

variable (acc : (Bits (queryBits k kN kS L) → XOut k e) → Claim X M.NIProof → Prop)

/-- **The event of Prove with the acceptance predicate `acc`**: no statement sent to the simulator
is the adversary's statement, and `acc` holds for its output under the base oracle `H`
reprogrammed by the simulator's assignments. `Wins` is the case of the composite verifier. -/
def WinsWith (A : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (Claim X M.NIProof))
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
    (fx : X' → X) (H : Bits (queryBits k kN kS L) → XOut k e) (v : M.Register B A Psim Q) : Prop :=
  (∀ x' ∈ queried A Psim Q v, fx x' ≠ (advOut A Psim Q v).stmt) ∧
    acc (H.reprogram (finalAss A Psim Q v)) (advOut A Psim Q v)

/-- **The probability that an adversary with run-time kinds wins Prove with `acc` and the
query-free test `ok` accepts.** -/
noncomputable def winTestProbWith
    (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (Claim X M.NIProof))
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
    (fx : X' → X) (ok : A.W → Prop) : ℝ≥0∞ :=
  ((A.toKindAlg.composeBothOut (simExtChallenger Psim Q) id).realLaw (outEquiv k e)).toOuterMeasure
    {p | ∃ v, p.out = some v ∧ WinsWith acc A.toTPKindAlg Psim Q fx ((outEquiv k e).symm ∘ p.oracle) v ∧
      ok (advWorkspace A.toTPKindAlg Psim Q v).1}

/-- **The probability that an adversary with run-time kinds wins Prove with `acc` and the test
`ok` accepts**, averaged over its auxiliary input. -/
noncomputable def SimExtractionAdversary.acceptsTestWith {tq Q : ℕ}
    (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) (ok : (a : 𝒜.Aux) → (𝒜.alg a).W → Prop) : ℝ≥0∞ :=
  ∑' a, 𝒜.aux a * winTestProbWith acc (𝒜.alg a) Psim Q fx (ok a)

/-- **The probability that `𝒜` wins Prove with `acc` and its residual-state test accepts** (Unruh
2017, Definition 14, p. 21, Prove with the test `Π^{H_final}`): `acceptsTestWith` of the
adversary followed by the test (`A^Π`). The composite's `acceptsQTest` is the case of its
verifier's acceptance. -/
noncomputable def SimExtractionAdversary.acceptsQTestWith {tq Q tTest : ℕ}
    (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) (T : 𝒜.QTest tTest) : ℝ≥0∞ :=
  (𝒜.withTest T).acceptsTestWith acc Psim fx T.okWithTest

end Wins

/-! ### Adversaries with a static schedule -/

variable (M B) in
/-- **An adversary with a static schedule in the simulation-extraction game** (proof-internal):
auxiliary input, then an interactive adversary with a static schedule (`Quantum.IAlg`) with
proof queries in the finite type `X'`, replies the simulator's proofs, and output a statement and a
proof; at most `Q` request slots, and at most `tq` queries of its own over its query slots and its
post phase. -/
structure FixedSimExtractionAdversary (X' : Type) [Fintype X'] [DecidableEq X'] (tq Q : ℕ) where
  /-- The values of the auxiliary input. -/
  Aux : Type
  /-- The distribution of the auxiliary input, independent of the oracle. -/
  aux : PMF Aux
  /-- The interactive adversary run on each value. -/
  alg : Aux → IAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) (Claim X M.NIProof)
  /-- At most `Q` request slots. -/
  requests_le : ∀ a, (alg a).requests ≤ Q
  /-- At most `tq` queries of its own: the query slots and the post phase. -/
  queries_le : ∀ a, (alg a).width * ((alg a).querySlots + (alg a).post) ≤ tq

/-- **A static-schedule adversary whose steps are channels as a query-bounded adversary**
(`Quantum.QueryBoundedAdversary`, the paper's `def:adversary`): at every auxiliary value the
embedding `IAlg.toAdaptive` (`Quantum.QueryBoundedAdversary.ofIAlg`), with the query count of the
static schedule. -/
noncomputable def FixedSimExtractionAdversary.toQueryBounded {tq Q : ℕ}
    (𝒜 : M.FixedSimExtractionAdversary B X' tq Q) (h : ∀ a, (𝒜.alg a).TracePreserving) :
    M.QBSimExtractionAdversary B X' tq :=
  QueryBoundedAdversary.ofIAlg 𝒜.aux 𝒜.alg h 𝒜.queries_le

/-! ### The adversary of the oracle-test gap lemma and its test -/

section Lemma1

variable {Wit C : Type}
  (Pv : NARG.Prover (Bits (queryBits k kN kS L)) (XOut k e) X Wit (M.Response B) C)
  (π₀ : X → Wit → C → M.NIProof)

/-- A response read as a proof, with the fallback `π₀` where no proof was built. -/
def responseProof (π₀ : M.NIProof) : M.Response B → M.NIProof
  | none => π₀
  | some π => π.1

/-- **The honest prover program as a claim program**: `Pv` at the statement `x`, the witness `w`
and the coins `c`, its response read as a proof of `x` (the fallback `π₀ x w c` where the response
is `unparsed`).

Running time: that of the prover program (at most `Pv.q` queries), then a constant-time read of
the response. This running time is argued here, not proved in Lean. -/
noncomputable def claimProg (x : X) (w : Wit) (c : C) :
    OracleProg (Bits (queryBits k kN kS L)) (XOut k e) (Claim X M.NIProof) :=
  (Pv.prog x w c).bind fun r => .pure ⟨x, responseProof (π₀ x w c) r⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem length_trace_claimProg_le (x : X) (w : Wit) (c : C)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    ((claimProg Pv π₀ x w c).trace H).length ≤ Pv.q := by
  rw [claimProg, OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
  exact Pv.prog_queries x w c H

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The claim of the claim program** is the statement with the proof read from the prover's
response. -/
theorem run_claimProg (x : X) (w : Wit) (c : C) (H : Bits (queryBits k kN kS L) → XOut k e) :
    (claimProg Pv π₀ x w c).run H = ⟨x, responseProof (π₀ x w c) (Pv.toFn.prove H x w c)⟩ := by
  rw [claimProg, OracleProg.run_bind]
  rfl

variable (M B) in
/-- **The adversary of the oracle-test gap lemma**: on the auxiliary input of a
witness `w` (drawn from `wit`) and the prover's coins `c`, the compilation of
`claimProg Pv π₀ x w c` with one extra query on the uniform superposition of the Merkle-node
inputs with the answer register at `0`, whose registers it keeps (`OracleProg.toIAlg`); its
statement is `x`, it makes no proof query (`Q = 0`) and at most `Pv.q + 1` queries.

Running time: the prover program with basis-state queries (a classical deterministic computation
given the coins, made reversible), each answer recorded in a table of `Pv.q` answers, plus one
query on the uniform superposition of the Merkle-node inputs, prepared from `|padInput, 0⟩` by one
`X` gate on the tag bit and `16k` Hadamard gates (`GordieHowe/Model/QROM/QueryBits.lean`); polynomial when the
prover program is. This running time is argued here, not proved in Lean. -/
noncomputable def oracleTestAdversary (x : X) (wit : PMF Wit) (X' : Type) [Fintype X']
    [DecidableEq X'] [Nonempty X'] : M.FixedSimExtractionAdversary B X' (Pv.q + 1) 0 where
  Aux := Wit × C
  aux := wit.bind fun w => Pv.coins.map fun c => (w, c)
  alg a := OracleProg.toIAlg (Req := X') (claimProg Pv π₀ x a.1 a.2) Pv.q padInput
    (zeroUniform nodeInputs) (norm_graphState nodeInputs_nonempty 0)
  requests_le a := by
    simp [IAlg.requests]
  queries_le a := by
    simp [IAlg.querySlots, IAlg.querySlotSet]

variable (M B) in
/-- **The adversary of the oracle-test gap lemma as a query-bounded adversary** (`def:adversary`): the embedding of
`oracleTestAdversary` into the adversaries with run-time kinds (`Quantum.QueryBoundedAdversary.ofIAlg`),
whose steps are basis permutations (`OracleProg.toIAlg_tracePreserving`), with at most `Pv.q + 1`
queries and no proof query.

Running time: that of `oracleTestAdversary`. This running time is argued here, not proved in
Lean. -/
noncomputable def oracleTestQB (x : X) (wit : PMF Wit) (X' : Type) [Fintype X'] [DecidableEq X']
    [Nonempty X'] : M.QBSimExtractionAdversary B X' (Pv.q + 1) :=
  (oracleTestAdversary M B Pv π₀ x wit X').toQueryBounded fun a =>
    OracleProg.toIAlg_tracePreserving (Req := X') (Resp := M.Response B)
      (claimProg Pv π₀ x a.1 a.2) Pv.q padInput (zeroUniform nodeInputs)
      (norm_graphState nodeInputs_nonempty 0)

/-- **The test of the oracle-test gap lemma**, for the query-bounded adversary
`oracleTestQB`: at each auxiliary value, the test of the kept registers (`OracleProg.keptTest`),
lifted to the embedding (`IAlg.QTest.toAdaptive`): one query that uncomputes the kept answer,
then the projective measurement onto the uniform superposition of the Merkle-node inputs with the
answer register at `0`; one query.

Running time: one query and the inverse of the state preparation (`O(k)` gates).
This running time is argued here, not proved in Lean. -/
noncomputable def oracleTestQBTest (x : X) (wit : PMF Wit) (X' : Type) [Fintype X']
    [DecidableEq X'] [Nonempty X'] : ((oracleTestQB M B Pv π₀ x wit X').toSimExtraction 0).QTest 1 where
  test a := (OracleProg.keptTest (Req := X') (claimProg Pv π₀ x a.1 a.2) Pv.q padInput
    (zeroUniform nodeInputs) (norm_graphState nodeInputs_nonempty 0) keptAccept).toAdaptive
  queries_le _ := le_rfl

variable [Nonempty X'] (acc : (Bits (queryBits k kN kS L) → XOut k e) → Claim X M.NIProof → Prop)

set_option hygiene false in
/-- The compiled claim program, in the proof below. -/
local notation "𝔸" => OracleProg.toIAlg (Req := X') (Resp := M.Response B)
  (claimProg Pv π₀ x a.1 a.2) Pv.q padInput (zeroUniform nodeInputs)
  (norm_graphState nodeInputs_nonempty 0)

set_option hygiene false in
/-- The lifted test, in the proof below. -/
local notation "𝕋" => (OracleProg.keptTest (Req := X') (Resp := M.Response B)
  (claimProg Pv π₀ x a.1 a.2) Pv.q padInput (zeroUniform nodeInputs)
  (norm_graphState nodeInputs_nonempty 0) keptAccept).toAdaptive

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The Prove-with-test probability of one auxiliary value** is the probability that `acc`
holds for the claim of the prover program, over a uniform oracle `H`: the adversary makes no
proof query, so the final oracle is `H`, the kept registers hold the graph state of `H` on the
Merkle-node inputs and the test accepts. -/
theorem winTestProbWith_oracleTestQB (x : X) (wit : PMF Wit) (a : Wit × C)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) :
    winTestProbWith acc ((((oracleTestQB M B Pv π₀ x wit X').toSimExtraction 0).alg a).withTest
      ((oracleTestQBTest Pv π₀ x wit X').test a)) Psim 0 fx
      ((oracleTestQBTest Pv π₀ x wit X').okWithTest a) =
      Pr[H ← (Bits (queryBits k kN kS L) → XOut k e) : acc H ((claimProg Pv π₀ x a.1 a.2).run H)] := by
  classical
  set C := simExtChallenger Psim 0
  -- the final basis state of the adversary followed by the test
  let dStar : (Bits (queryBits k kN kS L) → XOut k e) →
      DReg ((𝔸).toAdaptive.withTest 𝕋).W ((𝔸).toAdaptive.withTest 𝕋).width (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) := fun H =>
    (𝔸).toAdaptive.copySplit.symm ((𝔸).cntSplit.symm
      ((((OracleProg.tab (claimProg Pv π₀ x a.1 a.2) Pv.q padInput H Pv.q, keptAccept),
        (OracleProg.req₀, none)),
        fun _ => (OracleProg.xs (claimProg Pv π₀ x a.1 a.2) padInput H Pv.q, 0)), (𝔸).cntFinal),
      (𝔸).toAdaptive.outRep ((OracleProg.tab (claimProg Pv π₀ x a.1 a.2) Pv.q padInput H Pv.q,
        keptAccept), (𝔸).cntFinal))
  let vStar : (Bits (queryBits k kN kS L) → XOut k e) → C.Coins → ((𝔸).toAdaptive.withTest 𝕋).toKindAlg.CW C := fun H c =>
    ((𝔸).toAdaptive.withTest 𝕋).core.cwLift C (queryCount (𝔸).sched) (cntAt (𝔸).sched ((𝔸).toAdaptive.withTest 𝕋).core.slots)
      (((𝔸).toAdaptive.withTest 𝕋).core.blankReg C (dStar H) c)
  have hU : ∀ k, ∃ r₀, ((𝔸).toAdaptive.step k).PureAt r₀ ((fun k => (𝔸).cntMat ((1 : Matrix _ _ ℂ).submatrix (OracleProg.stepPerm (claimProg Pv π₀ x a.1 a.2) Pv.q padInput k).symm (Equiv.refl _)) k) k) := fun k =>
    ⟨(), (𝔸).toKindAlg_step_pureAt (KrausMap.pureAt_ofPerm _)⟩
  have hV : ∀ b, ∃ r₀, ((𝕋).step b).toKrausMap.PureAt r₀ ((fun b => (𝔸).cntLift (OracleProg.keptTestMat Pv.q (zeroUniform nodeInputs) (norm_graphState nodeInputs_nonempty 0) keptAccept b)) b) := fun b =>
    ⟨(), IAlg.QTest.toAdaptive_step_pureAt _ (OracleProg.keptTest_step_pureAt _ _ _ _ _ _ b)⟩
  have hinit : ((𝔸).toAdaptive.withTest 𝕋).core.init.mat = proj ((𝔸).toAdaptive.copyVec
      ((𝔸).liftCnt (OracleProg.initVec (claimProg Pv π₀ x a.1 a.2) Pv.q padInput
        (zeroUniform nodeInputs)) 0) (𝔸).toAdaptive.copyBlank) :=
    (𝔸).toAdaptive.withTest_init_of_proj ((𝔸).toKindAlg_init_of_proj rfl)
  -- the output law: the final basis state, with the challenger's coins
  have hlaw : ∀ H, (((𝔸).toAdaptive.withTest 𝕋).toKindAlg.composeBothOut C id).outLaw H =
      C.coins.map fun c => some (vStar H c) := by
    intro H
    refine pmf_eq_of_apply_some fun v => ?_
    have h := ((𝔸).toAdaptive.withTest 𝕋).core.outLaw_composeBothOut_toAdaptive_of_pure C (sched := (𝔸).sched)
      (fun w => (𝔸).toKindAlg_kind_eq_false (fun _ => rfl) w.1) (fun _ => rfl)
      ((𝔸).toAdaptive.withTestMat 𝕋 (fun k => (𝔸).cntMat ((1 : Matrix _ _ ℂ).submatrix (OracleProg.stepPerm (claimProg Pv π₀ x a.1 a.2) Pv.q padInput k).symm (Equiv.refl _)) k) (fun b => (𝔸).cntLift (OracleProg.keptTestMat Pv.q (zeroUniform nodeInputs) (norm_graphState nodeInputs_nonempty 0) keptAccept b))) ((𝔸).toAdaptive.withTestStep_pureAt 𝕋 hU hV) hinit
      id H v
    refine h.trans ?_
    rw [OracleProg.pureRun_withTest_keptTest_toAdaptive (Req := X') (Resp := M.Response B)
      (claimProg Pv π₀ x a.1 a.2) Pv.q padInput H (zeroUniform nodeInputs)
      (norm_graphState nodeInputs_nonempty 0) keptAccept]
    refine Eq.trans (congrArg ENNReal.ofReal (Finset.sum_congr rfl fun c _ =>
      congrArg ((C.coins c).toReal * ·) (?_ : _ = if vStar H c = v then (1 : ℝ) else 0))) ?_
    · refine (Finset.sum_eq_single (dStar H) (fun d _ hd => ?_)
        (fun h => absurd (Finset.mem_univ _) h)).trans ?_
      · erw [OracleProg.norm_copyVec_liftCnt_regVec_single_sq]
        split_ifs with h1 h2
        · exact absurd h2 hd
        · rfl
        · rfl
      · erw [OracleProg.norm_copyVec_liftCnt_regVec_single_sq]
        by_cases hv : vStar H c = v
        · simp only [hv, ↓reduceIte]
          split_ifs with h1 h2 <;> first | rfl | exact absurd rfl h2 | exact absurd hv h1
        · simp only [hv, ↓reduceIte]
          split_ifs with h1 h2 <;> first | rfl | exact absurd h1 hv
    rw [PMF.map_apply, tsum_fintype, ENNReal.ofReal_sum_of_nonneg fun c _ => by positivity]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hv : vStar H c = v
    · simp [hv, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    · simp [hv, Ne.symm hv]
  -- the event at each oracle and coins
  have hq : ∀ H c, queried ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 (vStar H c) = [] := fun H c => by
    unfold queried KindAlg.stateAt
    erw [Challenger.regState_blank]
    rfl
  have hf : ∀ H c, finalAss ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 (vStar H c) = [] := fun H c => by
    unfold finalAss KindAlg.postAss KindAlg.stateAt
    erw [Challenger.regState_blank]
  have ho : ∀ H c, advOut ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 (vStar H c) =
      (claimProg Pv π₀ x a.1 a.2).run H := fun H c => by
    show (𝔸).toAdaptive.out ((𝔸).toAdaptive.outRep
      ((OracleProg.tab (claimProg Pv π₀ x a.1 a.2) Pv.q padInput H Pv.q, keptAccept),
        (𝔸).cntFinal)) = _
    refine ((𝔸).toAdaptive.out_outRep _).trans ?_
    show (OracleProgAns.result (claimProg Pv π₀ x a.1 a.2) (OracleProg.answers Pv.q
      (OracleProg.tab (claimProg Pv π₀ x a.1 a.2) Pv.q padInput H Pv.q) Pv.q)).getD
        ((claimProg Pv π₀ x a.1 a.2).run 0) = _
    rw [OracleProg.result_answers_tab (claimProg Pv π₀ x a.1 a.2) Pv.q padInput H
      (length_trace_claimProg_le Pv π₀ x a.1 a.2 H), Option.getD_some]
  have hwin : ∀ H c, (WinsWith acc ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 fx H (vStar H c) ∧
      (oracleTestQBTest Pv π₀ x wit X').okWithTest a
        (advWorkspace ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 (vStar H c)).1) ↔
      acc H ((claimProg Pv π₀ x a.1 a.2).run H) := fun H c => by
    have hok : (oracleTestQBTest Pv π₀ x wit X').okWithTest a
        (advWorkspace ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 (vStar H c)).1 := rfl
    rw [WinsWith, hq, hf, ho]
    simp only [List.not_mem_nil, IsEmpty.forall_iff, forall_const, true_and, and_iff_left hok]
    rfl
  -- the probability
  show (((((𝔸).toAdaptive.withTest 𝕋).toKindAlg.composeBothOut C id).realLaw (outEquiv k e)).toOuterMeasure
    {o | ∃ v, o.out = some v ∧ WinsWith acc ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 fx ((outEquiv k e).symm ∘ o.oracle) v ∧
      (oracleTestQBTest Pv π₀ x wit X').okWithTest a (advWorkspace ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 v).1}) = _
  rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply, probUniform, PMF.toOuterMeasure_apply]
  refine tsum_congr fun H => ?_
  rw [hlaw, PMF.map_comp, PMF.toOuterMeasure_map_apply]
  have hset : ((fun o => (⟨o, outEquiv k e ∘ H⟩ : Outcome _ _ _)) ∘
      fun c => some (vStar H c)) ⁻¹'
      {o | ∃ v, o.out = some v ∧ WinsWith acc ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 fx ((outEquiv k e).symm ∘ o.oracle) v ∧
        (oracleTestQBTest Pv π₀ x wit X').okWithTest a (advWorkspace ((𝔸).toAdaptive.withTest 𝕋).toTPKindAlg Psim 0 v).1} =
      {_c | acc H ((claimProg Pv π₀ x a.1 a.2).run H)} := by
    ext c
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply, Option.some.injEq,
      exists_eq_left', ← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp]
    exact hwin H c
  rw [hset]
  by_cases hG : acc H ((claimProg Pv π₀ x a.1 a.2).run H)
  · have h1 : C.coins.toOuterMeasure {_c | acc H ((claimProg Pv π₀ x a.1 a.2).run H)} = 1 :=
      (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun _ _ => hG
    rw [h1]
    simp [Set.indicator]
    exact hG
  · have h0 : C.coins.toOuterMeasure {_c | acc H ((claimProg Pv π₀ x a.1 a.2).run H)} = 0 :=
      (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 fun _ _ h => hG h)
    rw [h0]
    simp [Set.indicator]
    exact fun h => absurd h hG

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The Prove-with-test probability is at most `1`. -/
theorem oracleTest_acceptsQTestWith_le_one (x : X) (wit : PMF Wit)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) :
    ((oracleTestQB M B Pv π₀ x wit X').toSimExtraction 0).acceptsQTestWith acc Psim fx
      (oracleTestQBTest Pv π₀ x wit X') ≤ 1 := by
  show ∑' a, (oracleTestAdversary M B Pv π₀ x wit X').aux a * winTestProbWith acc _ Psim 0 fx _
    ≤ 1
  calc _ ≤ ∑' a, (oracleTestAdversary M B Pv π₀ x wit X').aux a * 1 :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (PMF.toOuterMeasure_apply_le_one _ _)
    _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The oracle-test gap lemma, for Prove**: for the query-bounded adversary
`oracleTestQB M B Pv π₀ x wit X'` and its test `oracleTestQBTest`, the probability of winning Prove
with `acc` and the test accepting is at least `1 − εc`, against any simulator, when `acc` rejects
the claim of the prover program on `x` with probability at most `εc` at every witness of `wit` and
all coins (`hc`). -/
theorem oracleTest_acceptsQTestWith_ge {εc : ℝ≥0∞} (x : X) (wit : PMF Wit)
    (hc : ∀ w ∈ wit.support, ∀ c, Pr[H ← (Bits (queryBits k kN kS L) → XOut k e) :
      ¬ acc H ((claimProg Pv π₀ x w c).run H)] ≤ εc)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) :
    1 - εc ≤ ((oracleTestQB M B Pv π₀ x wit X').toSimExtraction 0).acceptsQTestWith acc Psim fx
      (oracleTestQBTest Pv π₀ x wit X') := by
  have hper : ∀ a, (oracleTestAdversary M B Pv π₀ x wit X').aux a ≠ 0 →
      1 - εc ≤ winTestProbWith acc ((((oracleTestQB M B Pv π₀ x wit X').toSimExtraction 0).alg
        a).withTest ((oracleTestQBTest Pv π₀ x wit X').test a)) Psim 0 fx
        ((oracleTestQBTest Pv π₀ x wit X').okWithTest a) := by
    intro a ha
    have hw : a.1 ∈ wit.support := by
      obtain ⟨w, hw, hc⟩ := (PMF.mem_support_bind_iff
        (wit) (fun w => Pv.coins.map fun c => (w, c)) a).1 ha
      rw [PMF.support_map] at hc
      obtain ⟨c, _, rfl⟩ := hc
      exact hw
    rw [winTestProbWith_oracleTestQB Pv π₀ acc x wit a Psim fx]
    have hadd := probUniform_add_not (C := Bits (queryBits k kN kS L) → XOut k e) fun H =>
      acc H ((claimProg Pv π₀ x a.1 a.2).run H)
    rw [ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_of_le_of_eq le_add_self hadd)) hadd]
    exact tsub_le_tsub_left (hc a.1 hw a.2) 1
  show 1 - εc ≤ ∑' a, (oracleTestAdversary M B Pv π₀ x wit X').aux a *
    winTestProbWith acc ((((oracleTestQB M B Pv π₀ x wit X').toSimExtraction 0).alg a).withTest
      ((oracleTestQBTest Pv π₀ x wit X').test a)) Psim 0 fx
      ((oracleTestQBTest Pv π₀ x wit X').okWithTest a)
  calc 1 - εc
      = ∑' a, (oracleTestAdversary M B Pv π₀ x wit X').aux a * (1 - εc) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := ENNReal.tsum_le_tsum fun a => by
        by_cases ha : (oracleTestAdversary M B Pv π₀ x wit X').aux a = 0
        · simp [ha]
        · exact mul_le_mul' le_rfl (hper a ha)

end Lemma1

/-! ### Families: eq. (6) fails eventually -/

section Family

variable [Nonempty X']

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **Eq. (6) fails eventually along a family, for every blind extractor** (Unruh 2017, Definition
14, p. 21: "a polynomial `p > 0`" and "a negligible `µ`"): for a family of
models `M η` with digests of at least `η` bytes (`hk`), prover programs `Pv η` and acceptance
predicates `acc η` that reject the claim of the prover program on the statement `x η` with
probability at most `εc η` at every witness of the witness law `wit η` and all coins (`hc`), `εc η` eventually at most `1/2` (`hεc`), and
extractors blind on the Merkle-node inputs whose assignment lists have length at most `ℓ η ≤ C'
η^c'` for all large `η` (`hℓ`), the adversary of the oracle-test gap lemma, a query-bounded adversary of
`def:adversary` (`oracleTestQB`), and its test (`oracleTestQBTest`) make eq. (6) fail for all large `η`, for every `p`
bounded by a polynomial `C η^c`, every exponent `d` and every negligible `µ`
(`Quantum.eq6_fails_eventually`, `lemma1Error_negligible`). -/
theorem oracleTest_eq6_fails_eventually_with {k kN kS L e : ℕ → ℕ}
    {M : ∀ η, Base P t X (k η) (kN η) (kS η) (L η) (e η)} {B : ℕ → ℕ}
    [∀ η j i, Fintype (((M η).comp j).MessageWrite i)] {Wit : Type} {Cn : ℕ → Type}
    (Pv : ∀ η, NARG.Prover (Bits (queryBits (k η) (kN η) (kS η) (L η))) (XOut (k η) (e η)) X Wit
      ((M η).Response (B η)) (Cn η))
    (π₀ : ∀ η, X → Wit → Cn η → (M η).NIProof)
    (acc : ∀ η, (Bits (queryBits (k η) (kN η) (kS η) (L η)) → XOut (k η) (e η)) →
      Claim X (M η).NIProof → Prop)
    {εc : ℕ → ℝ≥0∞} (x : ℕ → X) (wit : ℕ → PMF Wit)
    (hc : ∀ η, ∀ w ∈ (wit η).support, ∀ c,
      Pr[H ← (Bits (queryBits (k η) (kN η) (kS η) (L η)) → XOut (k η) (e η)) :
        ¬ acc η H ((claimProg (Pv η) (π₀ η) (x η) w c).run H)] ≤ εc η)
    (hεc : ∀ᶠ η in Filter.atTop, εc η ≤ 1 / 2) (hk : ∀ η, η ≤ k η)
    (Psim : ∀ η, NARG.Simulator (Bits (queryBits (k η) (kN η) (kS η) (L η))) (XOut (k η) (e η)) X'
      ((M η).Response (B η)) SC)
    (fx : X' → X) {ℓ : ℕ → ℕ} {C' : ℝ} {c' : ℕ}
    (hℓ : ∀ᶠ η in Filter.atTop, (ℓ η : ℝ) ≤ C' * (η : ℝ) ^ c')
    (Ext : ∀ η, BlindExtractor (Bits (queryBits (k η) (kN η) (kS η) (L η))) (XOut (k η) (e η))
      nodeInputs (ℓ η))
    {p μ : ℕ → ℝ} {C : ℝ} {c : ℕ} (hC : 0 < C) (hp : ∀ η, 0 < p η)
    (hpoly : ∀ η, p η ≤ C * (η : ℝ) ^ c) (d : ℕ)
    (hμ : ∀ j : ℕ, ∀ᶠ η : ℕ in Filter.atTop, (η : ℝ) ^ j * μ η ≤ 1) :
    ∀ᶠ η in Filter.atTop, (Ext η).extractAccept <
      (p η)⁻¹ * (((oracleTestQB (M η) (B η) (Pv η) (π₀ η) (x η) (wit η) X').toSimExtraction
          0).acceptsQTestWith (acc η) (Psim η) fx
          (oracleTestQBTest (Pv η) (π₀ η) (x η) (wit η) X')).toReal ^ d - μ η := by
  have hC' : 0 ≤ C' := by
    obtain ⟨η, hη, h1⟩ := (hℓ.and (Filter.eventually_ge_atTop 1)).exists
    have hpos : (0 : ℝ) < (η : ℝ) ^ c' := pow_pos (by exact_mod_cast h1) _
    exact nonneg_of_mul_nonneg_left ((Nat.cast_nonneg _).trans hη) hpos
  refine Quantum.eq6_fails_eventually (a := fun η => ((√(Fintype.card (XOut (k η) (e η)) : ℝ))⁻¹ +
      √(ℓ η / (nodeInputs (k := k η) (kN := kN η) (kS := kS η) (L := L η)).card)) ^ 2)
    (ε := fun η => (εc η).toReal) hC hp hpoly ?_ ?_ ?_ (lemma1Error_negligible hk hC' hℓ) hμ
  · filter_upwards [hεc] with η hη
    have hη1 : εc η ≤ 1 := hη.trans (by norm_num)
    have h1 := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
      (oracleTest_acceptsQTestWith_le_one (Pv η) (π₀ η) (acc η) (x η) (wit η) (Psim η) fx))
      (oracleTest_acceptsQTestWith_ge (Pv η) (π₀ η) (acc η) (x η) (wit η) (hc η) (Psim η) fx)
    rwa [ENNReal.toReal_sub_of_le hη1 ENNReal.one_ne_top, ENNReal.toReal_one] at h1
  · filter_upwards [hεc] with η hη
    have := ENNReal.toReal_mono (by norm_num) hη
    simpa using this
  · exact Filter.Eventually.of_forall fun η => (Ext η).extractAccept_le nodeInputs_nonempty

/-- **The bounds of a family of instances for the oracle test** (Unruh 2017, Definition 14, p. 21:
the adversary and the test range over polynomial-time families of circuits, the test making
polynomially many queries, p. 19; the auxiliary input is a state of polynomial length, p. 21 and
footnote 16, p. 20), for a family of models `M η` of one composite, IOP rejection bounds `ε η`,
statements `x η` and witness laws `wit η`, the byte lengths `size` and `wsize` of the encodings of
statements and witnesses, and one constant pair `C, c`:
- `k_ge`: digests of at least `η` bytes;
- `completenessError_le`: the completeness error `ε η + overrun + keyCollision (t.size n) k` is
  eventually at most `1/2`;
- `lengths_le`: eventually the digest, the XOF extension, the Merkle salt, the Fiat–Shamir salt
  and the chain input have at most `C η^c` bytes in all;
- `sizes_le`: eventually the statement and every witness of the witness law have at most `C η^c`
  bytes in all (`|x| + |w| ≤ C k^c'`).

The honest IOP prover does not depend on `η`; its running time on the statement and a witness is
polynomial in their lengths, which `sizes_le` bounds. The compiled honest prover adds hashing and
Merkle trees on inputs of at most `L` bytes, and the adversary and test of the oracle-test gap lemma
add one query each, one `X` gate and `16k` Hadamard gates (`oracleTestAdversary`,
`oracleTestQBTest`), so, by this argument, they run in time polynomial in `η` under these bounds.
The development has no cost model for quantum algorithms: `lengths_le` and `sizes_le` record the
polynomial-time quantifiers of Unruh's definition, and the proofs do not use them (the probability
inequality holds without them). -/
structure OracleTestBounds {k kN kS L e : ℕ → ℕ}
    (M : ∀ η, Base P t X (k η) (kN η) (kS η) (L η) (e η)) (ε : ℕ → ℝ≥0∞) {Wit : Type}
    (x : ℕ → X) (wit : ℕ → PMF Wit) (size : X → ℕ) (wsize : Wit → ℕ) (C : ℝ) (c : ℕ) : Prop where
  /-- Digests have at least `η` bytes. -/
  k_ge : ∀ η, η ≤ k η
  /-- The completeness error is eventually at most `1/2`. -/
  completenessError_le : ∀ᶠ η in Filter.atTop,
    ε η + (M η).overrun + SPBCS.keyCollision (t.size n) (k η) ≤ 1 / 2
  /-- The byte lengths of the model are eventually at most `C η^c` in all. -/
  lengths_le : ∀ᶠ η in Filter.atTop, (k η + e η + kN η + kS η + L η : ℝ) ≤ C * (η : ℝ) ^ c
  /-- The statement and every witness of the witness law have eventually at most `C η^c` bytes
  in all. -/
  sizes_le : ∀ᶠ η in Filter.atTop, ∀ w ∈ (wit η).support,
    (size (x η) + wsize w : ℝ) ≤ C * (η : ℝ) ^ c

end Family

end Base
end GordieHowe.SPBCS
