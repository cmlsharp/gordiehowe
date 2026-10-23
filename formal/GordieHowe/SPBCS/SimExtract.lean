-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimExtractGame
public import GordieHowe.SPBCS.FullPast.SimExtract
public import GordieHowe.Model.Quantum.Interactive.QueryBounded

@[expose] public section

/-!
# Simulation-sound extractability of the spBCS compiler in the QROM

Weak simulation-sound extractability with straight-line extraction (paper `thm:bcs-se`(1);
Unruh 2017, ePrint 2017/398, Definition 14, p. 21, eq. (6), weak variant, for residual-state tests
that make no oracle queries) of the spBCS compiler, against query-bounded adversaries
(`Quantum.QueryBoundedAdversary`, the paper's `(t, Q)`-adversaries), given a simulation oracle that
runs a counted simulator program assigning only at the keys of its chain inputs
(`SimAssignsAtKeys`) on any statement. The argument uses the spBCS cover (`cover_simExtGame`, through the
translation of the database).

The extractor is `dbExtract` (the database extractor on the translated database) on the measured
database of the simulated run expanded by the verifier's and the simulator's queries
(`extractsAt`). The error (`simExtractionError`) is the spBCS knowledge error
`knowledgeError k e (kq + Q q) (t + Q q + kq + Q q) c nJ κ`, with `q` the queries of one run of
the simulator program: the paper's `errse(t, Q)` with `k = kq + Q q_S` and `T = t + k + Q q_S`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}

section

variable {M : SPBCS Mg P X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' : Type} [Fintype X']
  [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

variable (M) in
/-- **The database extractor `dbExtract` at `E` returns a witness for `x`** from a database over
the oracle's inputs, restricted to the encoded queries. -/
def extractsAt [DecidableEq X] {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
    (x : X) (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  D.restrict Query.toBits ∈ M.extracts rel E x

/-! ### The game at one adversary -/

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)

/-- **The simulated adversary of the extractor**: the composed algorithm of the trace-preserving
form of `A` with the simulation challenger, as a coherent pure algorithm (`Alg.toQueryAlgCoh`)
outputting its classical registers, followed by the extraction queries (`simExtractionExpansion`).

Running time: `A` with the simulation challenger (each of its at most `Q` answered proof queries one run
of the simulator program, `Psim.q` queries), in pure serial form, then `kq + Q · Psim.q`
extraction queries computed from the measured registers by the spBCS verifier's query program;
polynomial when `A` and `Psim` are. This running time is argued here, not proved in Lean. -/
noncomputable abbrev extAdv :
    Adv (Bits (queryBits k kN kS L)) (XOut k e) (Out k e) (Base.Reg A Psim Q)
      (kq + Q * Psim.q)
      ((A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth + (kq + Q * Psim.q)) :=
  expandAdv (outEquiv k e) (simExtractionExpansion A.toTPKindAlg Psim Q Qs) (kq + Q * Psim.q)
    ((A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).toQueryAlgCoh.mapOut
      (·.getD (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut))

/-- The per-branch query count of the simulated adversary: `branchQueries + kq + Q · q`. -/
noncomputable def extAdvQueryCount :
    QueryCount (outEquiv k e) (extAdv Qs A Psim Q kq)
      (FullPast.branchQueries A Psim Q + (kq + Q * Psim.q)) :=
  QueryCount.expandAdv (kq + Q * Psim.q) (outEquiv k e)
    (simExtractionExpansion A.toTPKindAlg Psim Q Qs)
    (AdaptiveIAlg.tpQueryCount (outEquiv k e) A (simExtChallenger Psim Q) id _)

variable (fx : X' → X)

/-- **The probability that `A` wins Prove and the query-free test `ok` accepts.** -/
noncomputable def winTestProb (ok : A.W → Prop) : ℝ≥0∞ :=
  ((A.toKindAlg.composeBothOut (simExtChallenger Psim Q) id).realLaw (outEquiv k e)).toOuterMeasure
    {p | ∃ v, p.out = some v ∧ Wins A.toTPKindAlg Psim Q Qs fx ((outEquiv k e).symm ∘ p.oracle) v ∧
      ok (Base.advWorkspace A.toTPKindAlg Psim Q v).1}

/-- **The probability that the extractor `dbExtract` returns a witness for `A`'s statement, the
statement is fresh and the test `ok` accepts**, in one simulated run of `extAdv`. -/
noncomputable def extractFreshTestProb [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (ok : A.W → Prop) : ℝ≥0∞ :=
  simProb (outEquiv k e) (extAdv Qs A Psim Q kq) fun c D =>
    M.extractsAt rel E (Base.advOut A.toTPKindAlg Psim Q c).stmt D ∧
      Base.Fresh A Psim Q fx c ∧ ok (Base.advWorkspace A.toTPKindAlg Psim Q c).1

variable {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]

/-- Expanding a fresh accepting run that passes the test gives a winning tuple of `simExtGame`
that passes the test. -/
theorem winTestProb_le_winO
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    {Psim' : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)}
    (hA : M.SimAssignsAtKeys B Psim' fx)
    (ok : A.W → Prop) :
    winTestProb Qs A Psim' Q fx ok ≤ winO (outEquiv k e) (extAdv Qs A Psim' Q kq)
      (simExtGame A.toTPKindAlg Psim' Q Qs fx (kq + Q * Psim'.q) ∩
        {o | ok (Base.advWorkspace A.toTPKindAlg Psim' Q o.out).1}) := by
  set e' := outEquiv k e
  set C := simExtChallenger Psim' Q
  set Acc : Set (Outcome (Base.Reg A Psim' Q) (Bits (queryBits k kN kS L)) (Out k e)) :=
    {p | (Wins A.toTPKindAlg Psim' Q Qs fx (e'.symm ∘ p.oracle) p.out ∧
      ok (Base.advWorkspace A.toTPKindAlg Psim' Q p.out).1) ∧
      A.toTPKindAlg.Consistent C (e'.symm ∘ p.oracle) p.out}
  have hdom := A.realLaw_composeBothOut_le C id e'
    {p | ∃ v, p.out = some v ∧ Wins A.toTPKindAlg Psim' Q Qs fx (e'.symm ∘ p.oracle) v ∧
      ok (Base.advWorkspace A.toTPKindAlg Psim' Q v).1} (fun p ⟨v, hv, _⟩ => by rw [hv]; simp)
  refine hdom.trans ?_
  have hinter := A.toTPKindAlg.realLaw_composeBothOut_inter C e'
    (fun v f => Wins A.toTPKindAlg Psim' Q Qs fx (e'.symm ∘ f) v ∧
      ok (Base.advWorkspace A.toTPKindAlg Psim' Q v).1)
  refine le_of_eq_of_le (by convert hinter using 1) ?_
  refine le_trans (MeasureTheory.measure_mono
    (t := {p : Outcome (Option (Base.Reg A Psim' Q)) (Bits (queryBits k kN kS L)) (Out k e) |
      ∃ o ∈ p.out, ⟨o, p.oracle⟩ ∈ Acc})
    ?_) ?_
  · rintro p ⟨v, hv, hw, hc⟩
    exact ⟨v, hv, hw, hc⟩
  refine ((A.toTPKindAlg.composeBothOut C id).toOuterMeasure_realLaw_le_coh e'
    (A.toTPKindAlg.composeBothOut C id).defaultOut Acc).trans ?_
  refine winO_expandAdv e' (simExtractionExpansion A.toTPKindAlg Psim' Q Qs) _ fun p hp =>
    ⟨?_, hp.1.2⟩
  have hm := expand_mem_simExtGame Q Qs fx A.toTPKindAlg hkq hA hp.2 hp.1.1
  have he : (fun a => e' ((e'.symm ∘ p.oracle) a)) = p.oracle :=
    funext fun a => e'.apply_symm_apply _
  rwa [he] at hm

/-- **Simulation-sound extractability of the spBCS argument at one adversary and a query-free
test**, with freshness in the extraction experiment: `winTestProb ok ≤ extractFreshTestProb ok +
knowledgeError k e (kq + Q q) (b + kq + Q q) c_in nJ (max_c ε c)`, with `b` the per-branch query
count of the composed algorithm. -/
theorem winTestProb_le_fresh [DecidableEq X]
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Psim' : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C))
    (hA : M.SimAssignsAtKeys B Psim' fx)
    (ok : A.W → Prop) :
    winTestProb Qs A Psim' Q fx ok ≤ extractFreshTestProb Qs A Psim' Q kq fx rel E ok +
      knowledgeError k e (kq + Q * Psim'.q)
        (FullPast.branchQueries A Psim' Q + (kq + Q * Psim'.q))
        M.senc.digestsPerInput Mg.nJ (maxError ε) := by
  set e' := outEquiv k e
  set K := kq + Q * Psim'.q
  set b := FullPast.branchQueries A Psim' Q + K
  set G := simExtGame A.toTPKindAlg Psim' Q Qs fx K ∩
    {o | ok (Base.advWorkspace A.toTPKindAlg Psim' Q o.out).1}
  set 𝒜 := extAdv Qs A Psim' Q kq
  have hexpand := winTestProb_le_winO Qs A Q kq fx hkq hA ok
  have hsimulation : winO e' 𝒜 G ≤ winS e' 𝒜 G + 2 * esqrt (K / Fintype.card (Out k e)) :=
    le_add_two_mul_of_esqrt_le (winO_le_one e' 𝒜 G) (Lifting.oracle_sim_card e' 𝒜 G)
  have hcover : winS e' 𝒜 G ≤ extractFreshTestProb Qs A Psim' Q kq fx rel E ok +
      dbProb e' 𝒜 (DB.restrict Query.toBits ⁻¹' (M.bad rel E St ∪ digestCollision)) := by
    refine winS_le_simProb_add e' 𝒜 G fun o ho D hD => ?_
    rcases cover_simExtGame A.toTPKindAlg Psim' Q fx St hrbr ho.1 hD with hE | hbad
    · exact Or.inl ⟨hE, ho.1.1, ho.2⟩
    · exact Or.inr hbad
  have hbad : dbProb e' 𝒜 (DB.restrict Query.toBits ⁻¹' (M.bad rel E St ∪ digestCollision)) ≤
      6 * (b : ℝ≥0∞) ^ 2 * (maxError ε +
        (((max 2 M.senc.digestsPerInput + Mg.nJ + 1) * b : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) :=
    dbProb_bad_union_le_of_queryCount hrbr 𝒜 (extAdvQueryCount Qs A Psim' Q kq)
  calc winTestProb Qs A Psim' Q fx ok ≤ winS e' 𝒜 G + 2 * esqrt (K / Fintype.card (Out k e)) :=
        hexpand.trans hsimulation
    _ ≤ extractFreshTestProb Qs A Psim' Q kq fx rel E ok + 6 * (b : ℝ≥0∞) ^ 2 *
          ((maxError ε : ℝ≥0∞) + (((max 2 M.senc.digestsPerInput + Mg.nJ + 1) * b : ℕ) : ℝ≥0∞) /
            2 ^ (8 * k)) + 2 * esqrt (K / Fintype.card (Out k e)) := by
        gcongr
        exact hcover.trans (add_le_add le_rfl hbad)
    _ = _ := by
        rw [knowledgeError]
        ring

/-! ### The bundled notion and the headline -/

variable (M) in
/-- **The simulation-sound extractability error of the spBCS argument** at the verifier's
query bound `kq`, a challenge-error bound `κ`, `q` simulator queries per proof query, `tq` adversary
queries and `Q` proof queries: the spBCS knowledge error at `kq + Q · q` appended queries and
`tq + Q · q + kq + Q · q` queries in all. -/
noncomputable def simExtractionError (kq : ℕ) (κ : ℝ≥0) (q tq Q : ℕ) : ℝ≥0∞ :=
  knowledgeError k e (kq + Q * q) (tq + Q * q + (kq + Q * q)) M.senc.digestsPerInput Mg.nJ κ

variable (M B) in
/-- **The query-bounded adversaries of the simulation-extraction game** of the spBCS argument
with proof queries in `X'` (`Quantum.QueryBoundedAdversary`, the paper's `(t, Q)`-adversaries). -/
abbrev QBSimExtractionAdversary (X' : Type) [Fintype X'] [DecidableEq X'] (tq : ℕ) : Type 1 :=
  QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) (Claim X M.NIProof) tq

/-- **A query-bounded adversary as an adversary of the simulation-extraction game** answered on
`Q` proof queries (proof-internal): the same auxiliary input, algorithms and query bound. -/
def QBSimExtractionAdversary.toSimExtraction {tq : ℕ} (Q : ℕ)
    (𝒜 : M.QBSimExtractionAdversary B X' tq) : M.SimExtractionAdversary B X' tq Q where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  alg := 𝒜.alg
  queries_le := 𝒜.queries_le

/-- **The probability that `𝒜` wins Prove and the test `ok` accepts**, averaged over its
auxiliary input. -/
noncomputable def acceptsTest {tq Q : ℕ} (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) (ok : (a : 𝒜.Aux) → (𝒜.alg a).W → Prop) : ℝ≥0∞ :=
  ∑' a, 𝒜.aux a * winTestProb Qs (𝒜.alg a) Psim Q fx (ok a)

/-- **The probability that `dbExtract` returns a witness for `𝒜`'s statement, the statement is
fresh and the test `ok` accepts**, averaged over its auxiliary input. -/
noncomputable def extractsFreshTest [DecidableEq X] {tq Q : ℕ}
    (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (kq : ℕ) (fx : X' → X) {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
    (ok : (a : 𝒜.Aux) → (𝒜.alg a).W → Prop) : ℝ≥0∞ :=
  ∑' a, 𝒜.aux a * extractFreshTestProb Qs (𝒜.alg a) Psim Q kq fx rel E (ok a)

variable (M B) in
/-- **Weak simulation-sound extractability of the spBCS argument with freshness in both experiments,
for residual-state tests without oracle queries, against query-bounded adversaries** (Unruh 2017,
Definition 14, p. 21, eq. (6), `d = 1`, `p = 1`): for every finite type of queried statements read
through `fx`, every query-bounded adversary with at most `tq` queries whose first `Q` proof queries are
answered, and every query-free test `ok`, the probability that it outputs a fresh statement with a
proof the spBCS verifier accepts under the final oracle and the test accepts is at most the
probability that the database extractor `dbExtract` at `E` returns a witness for the statement, the
statement is fresh and the test accepts, plus `ε tq Q`. -/
def SimulationSoundExtractableFresh [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq Q : ℕ)
    (𝒜 : M.QBSimExtractionAdversary B X' tq)
    (ok : (a : (𝒜.toSimExtraction Q).Aux) → ((𝒜.toSimExtraction Q).alg a).W → Prop),
    acceptsTest Qs (𝒜.toSimExtraction Q) (Sim.comap fx) fx ok ≤
      extractsFreshTest Qs (𝒜.toSimExtraction Q) (Sim.comap fx) kq fx rel E ok + ε tq Q

variable (M B) in
/-- **Weak simulation-sound extractability of the spBCS argument with freshness in both experiments
over the game's adversaries** (proof-internal; the headline form is
`SimulationSoundExtractableFresh`, over the query-bounded adversaries): as
`SimulationSoundExtractableFresh`, for every adversary of the simulation-extraction game
(`Base.SimExtractionAdversary`), whose steps need not be channels. -/
def SimulationSoundExtractableFreshGame [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq Q : ℕ)
    (𝒜 : M.SimExtractionAdversary B X' tq Q) (ok : (a : 𝒜.Aux) → (𝒜.alg a).W → Prop),
    acceptsTest Qs 𝒜 (Sim.comap fx) fx ok ≤
      extractsFreshTest Qs 𝒜 (Sim.comap fx) kq fx rel E ok + ε tq Q

variable {Qs} in
/-- The notion over the game's adversaries gives the notion over the query-bounded adversaries. -/
theorem SimulationSoundExtractableFreshGame.queryBounded [DecidableEq X] {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {kq : ℕ}
    {Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC}
    {ε : ℕ → ℕ → ℝ≥0∞} (h : M.SimulationSoundExtractableFreshGame B Qs rel E kq Sim ε) :
    M.SimulationSoundExtractableFresh B Qs rel E kq Sim ε := fun X' _ _ fx tq Q 𝒜 ok =>
  h X' fx tq Q (𝒜.toSimExtraction Q) ok

/-- **Simulation-sound extractability of the spBCS compiler over the game's adversaries**
(proof-internal): the bound of `simulation_sound_extractability` for every adversary of the
simulation-extraction game, whose steps need not be channels. -/
theorem simulation_sound_extractability_game [DecidableEq X] {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (hA : M.SimAssignsAtKeys B Sim id) :
    M.SimulationSoundExtractableFreshGame B Qs rel E kq Sim
      (M.simExtractionError kq (maxError ε) Sim.q) := by
  intro X' _ _ fx tq Q 𝒜 ok
  set Psim := Sim.comap fx
  have hq : Psim.q = Sim.q := rfl
  rw [← hq]
  refine Base.SimExtractionAdversary.tsum_le_tsum_add 𝒜 fun a => ?_
  refine (winTestProb_le_fresh Qs (𝒜.alg a) Q kq fx hkq hrbr Psim (hA.comap fx) (ok a)).trans
    (add_le_add le_rfl ?_)
  unfold simExtractionError knowledgeError
  have h2 := 𝒜.queries_le a
  have hb : FullPast.branchQueries (𝒜.alg a) Psim Q + (kq + Q * Psim.q) ≤
      tq + Q * Psim.q + (kq + Q * Psim.q) := by
    change (𝒜.alg a).width * (𝒜.alg a).budget + Q * Psim.q + (𝒜.alg a).width * (𝒜.alg a).post +
      (kq + Q * Psim.q) ≤ tq + Q * Psim.q + (kq + Q * Psim.q)
    nlinarith
  gcongr

/-- **Simulation-sound extractability of the spBCS compiler in the QROM** (paper
`thm:bcs-se`(1); Unruh 2017, Definition 14, p. 21, weak variant, eq. (6) with `d = 1`, `p = 1`,
for residual-state tests that make no oracle queries, with straight-line extraction and freshness
in both events): for a composite causally round-by-round knowledge sound at the causal extractor
`E` with errors `ε` (`hrbr`), query phases whose accepting runs make at most `kq` verifier queries
(`hkq`), and a counted simulator program `Sim` that assigns only at the keys of its chain inputs
(`hA`), with the simulation oracle running `Sim` on any statement: against every query-bounded
adversary, the bound `simExtractionError kq (max_c ε c) q tq Q` with `q` the queries of one run
of `Sim`, the extractor `dbExtract`. -/
theorem simulation_sound_extractability [DecidableEq X] {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (hA : M.SimAssignsAtKeys B Sim id) :
    M.SimulationSoundExtractableFresh B Qs rel E kq Sim
      (M.simExtractionError kq (maxError ε) Sim.q) :=
  (simulation_sound_extractability_game Qs hkq hrbr Sim hA).queryBounded

end

end GordieHowe.SPBCS
