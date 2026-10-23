-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimExtractTest
public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.SPBCS.FullPast.OracleTest
public import GordieHowe.Headline

@[expose] public section

/-!
# The oracle-test gap lemma for the spBCS compiler: eq. (6) fails for oracle tests

The counterexample to eq. (6) of Unruh 2017 (ePrint 2017/398, Definition 14, p. 21) for tests that
query the oracle (the oracle-test gap lemma of `GordieHowe/Model/Quantum/OracleTestBoundary.lean`) for the spBCS
compiler: the generic construction of `GordieHowe/SPBCS/FullPast/OracleTest.lean` at the acceptance of the
spBCS verifier (`Accepts`) and the honest spBCS prover `niProver` at a site layout `Λ`, run through
`queryEncoding`.

- `honestOracleTestQB`, `honestOracleTestQBTest`: the adversary of the oracle-test gap lemma, a
  query-bounded adversary of `def:adversary` with one query more than the honest prover
  (`GordieHowe.SPBCS.Base.oracleTestQB`), and its test with one query
  (`GordieHowe.SPBCS.Base.oracleTestQBTest`); the spBCS verifier rejects the claim of the
  honest prover program with probability at most `ε + overrun + keyCollision (t.size n) k`
  (`prob_not_accepts_claimProg_le`).
- `oracleTest_eq6_fails_eventually`: along a family of spBCS compilers within the bounds
  `GordieHowe.SPBCS.Base.OracleTestBounds`, with polynomially bounded assignment lists, eq. (6) fails for all
  large `η`, for every polynomially bounded `p`, every `d` and every negligible `µ`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open Base (SimExtractionAdversary claimProg oracleTestQB oracleTestQBTest run_claimProg)
open scoped NNReal ENNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}

section

variable {M : SPBCS Mg P X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  (Λ : SiteLayout Mg)
  {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]
  {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x} {Wit R : Type} [Fintype R] [Nonempty R]
  (honest : Wit → R → CausalProver P t X)

variable (E Qs) in
/-- **The fallback proof of the claim program** at the honest spBCS prover: the honest proof
against the zero oracle (never read for an honest proof within the proof bound). -/
noncomputable def honestFallback (x : X) (w : Wit)
    (c : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R)) : M.NIProof :=
  prove (honest w c.coins.iop) x c.salt E c.coins.merkleSalts (chainOracle 0) (Qs x)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The claim program of the honest spBCS prover returns the honest proof** when `B` bounds
the proof format (`hb`). -/
theorem run_claimProg_niProver (VE : M.ViewEncoder E Qs) (hb : M.FormatBounds Qs B B) (x : X)
    (w : Wit) (c : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R))
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    (claimProg (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (honestFallback E Qs honest) x w c).run H =
      ⟨x, prove (honest w c.coins.iop) x c.salt E c.coins.merkleSalts (chainOracle H) (Qs x)⟩ := by
  rw [run_claimProg, NARG.Prover.toFn_encode_prove, NARG.Prover.toFn_mapOutput_prove,
    decode_queryEncoding]
  exact congrArg (Claim.mk x) (M.toFn_niProver Λ honest E VE hb _ x w c)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The spBCS verifier rejects the claim of the honest prover program** with probability at
most `ε + overrun + keyCollision (t.size n) k` (`prob_not_accepts_prove_le`). -/
theorem prob_not_accepts_claimProg_le (VE : M.ViewEncoder E Qs) (hb : M.FormatBounds Qs B B)
    {ε : ℝ≥0∞} (x : X) (w : Wit) (c : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R))
    (hε : Pr[ch ← Chs P t : V x ((honest w c.coins.iop).run x ch) ≠ true] ≤ ε) :
    Pr[H ← (Bits (queryBits k kN kS L) → XOut k e) :
        ¬ (fun H (o : Claim X M.NIProof) => M.Accepts (chainOracle H) o.stmt o.proof (Qs o.stmt)) H
          ((claimProg (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (honestFallback E Qs honest) x w c).run H)] ≤
      ε + M.overrun + SPBCS.keyCollision (t.size n) k := by
  have hfun : ∀ H, ((fun H (o : Claim X M.NIProof) => M.Accepts (chainOracle H) o.stmt o.proof
      (Qs o.stmt)) H ((claimProg (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (honestFallback E Qs honest) x w
        c).run H)) = M.Accepts (chainOracle H) x
        (prove (honest w c.coins.iop) x c.salt E c.coins.merkleSalts (chainOracle H) (Qs x))
        (Qs x) := fun H =>
    congrArg (fun o : Claim X M.NIProof => M.Accepts (chainOracle H) o.stmt o.proof (Qs o.stmt))
      (run_claimProg_niProver Λ honest VE hb x w c H)
  simp only [hfun]
  refine (probUniform_chainOracle (fun h =>
    ¬ M.Accepts h x (prove (honest w c.coins.iop) x c.salt E c.coins.merkleSalts h (Qs x))
      (Qs x))).trans_le ?_
  exact prob_not_accepts_prove_le (honest w c.coins.iop) x c.salt E c.coins.merkleSalts (Qs x) hε

variable [Nonempty X']

variable (M B E Qs) in
/-- **The adversary of the oracle-test gap lemma at the honest spBCS prover**, a query-bounded adversary of
`def:adversary` (`Base.oracleTestQB` at the honest prover `niProver` run through `queryEncoding`): the
honest prover on `x` with a witness drawn from `wit`, plus one kept query on the uniform
superposition of the Merkle-node inputs; no proof query, at most one query more than the honest
prover. -/
noncomputable abbrev honestOracleTestQB (hb : M.FormatBounds Qs B B) (x : X) (wit : PMF Wit) (X' : Type) [Fintype X']
    [DecidableEq X'] [Nonempty X'] :
    M.QBSimExtractionAdversary B X' ((((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q + 1) :=
  oracleTestQB M.toBase B (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (honestFallback E Qs honest) x
    wit X'

variable (M B E Qs) in
/-- **The test of the oracle-test gap lemma for `honestOracleTestQB`** (`Base.oracleTestQBTest`): one query
to the final oracle, then the projective measurement onto the uniform superposition of the
Merkle-node inputs with the answer register at `0`. -/
noncomputable abbrev honestOracleTestQBTest (hb : M.FormatBounds Qs B B) (x : X) (wit : PMF Wit) (X' : Type) [Fintype X']
    [DecidableEq X'] [Nonempty X'] :
    ((honestOracleTestQB M B Λ E Qs honest hb x wit X').toSimExtraction 0).QTest 1 :=
  oracleTestQBTest (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) (honestFallback E Qs honest) x wit X'

/-- **Eq. (6) fails eventually for the spBCS compiler, for every blind extractor** (Unruh
2017, Definition 14, p. 21: "a polynomial `p > 0`" and "a negligible `µ`"): for a family of spBCS compilers `M η` of one
composite and one term with merges, at one site layout `Λ`, within the bounds
`Base.OracleTestBounds` at constants `C', c'` (digests of at least `η` bytes, completeness
error `ε η + overrun + keyCollision (t.size n) k` eventually at most `1/2`, byte lengths of the
model, the statement and the witnesses at most `C' η^c'`), with `B η` bounding the proof format
(`hb`), when the composite verifier rejects the honest run on the statement `x η` with probability
at most `ε η` at every witness of `wit η` and all coins (`hε`), and for extractors blind on the
Merkle-node inputs whose assignment lists have length at most `ℓ η ≤ C' η^c'` for all large `η`, the adversary
`honestOracleTestQB` and its test `honestOracleTestQBTest` make eq. (6) fail for all large `η`, for
every `p` bounded by a polynomial `C η^c`, every exponent `d` and every negligible `µ`. By the argument of `Base.OracleTestBounds`, the
adversary and the test run in time polynomial in `η` under the bounds, so the statement has
Unruh's quantifiers. -/
@[headline]
theorem oracleTest_eq6_fails_eventually {k kN kS L e : ℕ → ℕ}
    {M : ∀ η, SPBCS Mg P X (k η) (kN η) (kS η) (L η) (e η)} {B : ℕ → ℕ}
    [∀ η j i, Fintype (((M η).comp j).MessageWrite i)]
    {E : ∀ η, (j : ι) → ((M η).comp j).Encoder} {Qs : ∀ η x, (M η).IOPQueries V x}
    (VE : ∀ η, (M η).ViewEncoder (E η) (Qs η)) (hb : ∀ η, (M η).FormatBounds (Qs η) (B η) (B η))
    {ε : ℕ → ℝ≥0∞} (x : ℕ → X) (wit : ℕ → PMF Wit)
    (hε : ∀ η, ∀ w ∈ (wit η).support, ∀ r,
      Pr[ch ← Chs P t : V (x η) ((honest w r).run (x η) ch) ≠ true] ≤ ε η)
    {size : X → ℕ} {wsize : Wit → ℕ} {C' : ℝ} {c' : ℕ}
    (hS : Base.OracleTestBounds (fun η => (M η).toBase) ε x wit size wsize C' c')
    (Psim : ∀ η, NARG.Simulator (Bits (queryBits (k η) (kN η) (kS η) (L η))) (XOut (k η) (e η)) X'
      ((M η).Response (B η)) SC)
    (fx : X' → X) {ℓ : ℕ → ℕ} (hℓ : ∀ᶠ η in Filter.atTop, (ℓ η : ℝ) ≤ C' * (η : ℝ) ^ c')
    (Ext : ∀ η, BlindExtractor (Bits (queryBits (k η) (kN η) (kS η) (L η))) (XOut (k η) (e η))
      nodeInputs (ℓ η))
    {p μ : ℕ → ℝ} {C : ℝ} {c : ℕ} (hC : 0 < C) (hp : ∀ η, 0 < p η)
    (hpoly : ∀ η, p η ≤ C * (η : ℝ) ^ c) (d : ℕ)
    (hμ : ∀ j : ℕ, ∀ᶠ η : ℕ in Filter.atTop, (η : ℝ) ^ j * μ η ≤ 1) :
    ∀ᶠ η in Filter.atTop, (Ext η).extractAccept <
      (p η)⁻¹ * (acceptsQTest (Qs η)
        ((honestOracleTestQB (M η) (B η) Λ (E η) (Qs η) honest (hb η) (x η) (wit η) X').toSimExtraction 0)
        (Psim η) fx
        (honestOracleTestQBTest (M η) (B η) Λ (E η) (Qs η) honest (hb η) (x η) (wit η) X')).toReal ^ d -
        μ η :=
  Base.oracleTest_eq6_fails_eventually_with
    (fun η => (((M η).niProver Λ honest (E η) (hb η)).mapOutput some).encode queryEncoding)
    (fun η => honestFallback (E η) (Qs η) honest)
    (fun η H o => (M η).Accepts (chainOracle H) o.stmt o.proof (Qs η o.stmt)) x wit
    (fun η w hw c => prob_not_accepts_claimProg_le Λ honest (VE η) (hb η) (x η) w c (hε η w hw _))
    hS.completenessError_le hS.k_ge Psim fx hℓ Ext hC hp hpoly d hμ

end

end GordieHowe.SPBCS
