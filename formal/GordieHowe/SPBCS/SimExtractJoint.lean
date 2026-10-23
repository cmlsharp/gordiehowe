-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Headline
public import GordieHowe.SPBCS.SimOracle

@[expose] public section

/-!
# Weak online simulation extractability of the spBCS compiler in the QROM

Weak online simulation extractability (paper `thm:bcs-se`, combining Unruh 2015,
ePrint 2014/587, Definition 4, p. 7, Unruh 2017, ePrint 2017/398, Definition 11, p. 17, and
Don–Fehr–Majenz–Schaffner 2022, ePrint 2022/270, Definition 3.1, p. 10): the extractor's single run
with simulated proofs gives the adversary's output, the challenger's registers and the adversary's
quantum residual state jointly with a witness.

- `GordieHowe.SPBCS.WeakOnlineSimulationExtraction`, `WeakSimExtraction`, `GordieHowe.SPBCS.WeakOnlineSimulationExtraction.unruhSimExtraction`: the two
  notions on the laws of the simulated run and the extractor's run, and the implication at error
  `errsim + errse` for tests that are events of the measured output.
- `AcceptsFinal`, `verdictGame`, `expand_mem_verdictGame_iff`: on the control (the adversary's
  output and the challenger's registers, `GordieHowe.SPBCS.Base.Ctrl`), the spBCS verifier accepts under
  the final oracle exactly when the expanded control wins the verdict game;
  `expand_mem_simExtGame_iff`: on registers consistent with the oracle, the expanded registers win
  `simExtGame` exactly when the adversary wins (`Wins`).
- `simVerifier` (the final verifier as a `GordieHowe.NARG.QROM.Verifier` on the control) with its
  base game `simVerifier.game` (`mem_verdictGame_of_mem_game`), `simExtVerifier`, `simExtKnowledgeBound`
  (the knowledge bound of `simExtGame`).
- `simRun`, `simRunModel`, `extRun`: the simulated runs and the extraction run, each measuring only
  the control; `extRunFull`, `simLaw_extRun`: the extraction run with all composed registers
  measured, and the equality of the laws of the control and the database in the two (the
  measurement of the adversary's workspace acts on registers separate from the control and the
  database, so it commutes with their measurements).
- `GordieHowe.SPBCS.WeakOnlineSimExtracts`, `GordieHowe.SPBCS.WeakOnlineSimulationExtractable`, `GordieHowe.SPBCS.weak_online_simulation_extractability_qrom`
  (paper `thm:bcs-se`(1), joint form): at every value of the control and the verdict, the state of
  the composed registers in the extraction run (the database traced out, the adversary's workspace
  unmeasured) is their state in the model's simulated run, and the extraction run wins without
  extraction with probability at most `simExtractionError`.
- `GordieHowe.SPBCS.WeakOnlineSimulationExtractable.unruhSimExtraction_of_queryFreeTest`: the joint form gives weak
  simulation-sound extractability with fresh extraction (`SimulationSoundExtractableFresh`) at
  the same error.
- `CL06Extraction`, `GordieHowe.SPBCS.WeakOnlineSimulationExtractable.cl06Extraction`: the joint form gives the
  extraction property of Chase–Lysyanskaya 2006, Definition 2.2, in the QROM.
-/

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {X Y B C C' : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- **Expanding an algorithm with a relabelled output** is expanding the algorithm with the
expansion read through the relabelling, its output relabelled: the same registers and steps. -/
theorem expandAdv_mapOut (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {t : ℕ}
    (𝒜 : QueryAlg X Y t C') (g : C' → C) :
    expandAdv e E k (𝒜.mapOut g) =
      (expandAdv e ⟨fun c => E.next (g c)⟩ k 𝒜).mapOut fun o => ⟨o.queries, o.answers, g o.out⟩ :=
  rfl

section ComapIn

variable {X B C C' : Type} (E : Expansion X B C) (π : C' → C) (h : X → B) (c : C')

/-- **The run of an expansion read through a map of its inputs** is the run on the image. -/
theorem Expansion.run_comapIn : ∀ i, (E.comapIn π).run h c i = E.run h (π c) i
  | 0 => rfl
  | i + 1 => by
    rw [Expansion.run, Expansion.run, Expansion.run_comapIn i]
    rfl

/-- **The output of an expansion read through a map of its inputs** is the expansion of the
image, with the input in place of the image. -/
theorem Expansion.expand_comapIn {k : ℕ} :
    ((E.comapIn π).expand h c : BaseGame.Tuple X B C' k) =
      ⟨(E.expand h (π c) (k := k)).queries, (E.expand h (π c) (k := k)).answers, c⟩ := by
  have hq : ((E.comapIn π).queries h c : Fin k → X) = E.queries h (π c) :=
    funext fun i => by simp only [Expansion.queries, Expansion.run_comapIn]
  simp only [Expansion.expand, hq]

end ComapIn

end GordieHowe.QROM

namespace GordieHowe.Quantum.KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (A : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **The coherent pure form of a composition with a relabelled output** is the coherent pure form
of the composition with its output relabelled: the same registers and steps. -/
theorem toQueryAlgCoh_composeBothOut_comp {O' O'' : Type} (f : A.CW C → O') (g : O' → O'') :
    (A.composeBothOut C (g ∘ f)).toQueryAlgCoh =
      (A.composeBothOut C f).toQueryAlgCoh.mapOut (Option.map g) := by
  have hout : (A.composeBothOut C (g ∘ f)).haltOutCoh =
      Option.map g ∘ (A.composeBothOut C f).haltOutCoh := by
    funext w
    simp only [Function.comp, Alg.haltOutCoh]
    split <;> rfl
  unfold Alg.toQueryAlgCoh QueryAlg.mapOut
  dsimp only
  rw [hout]
  rfl

end GordieHowe.Quantum.KindAlg

namespace GordieHowe.SPBCS

open MeasureTheory
open scoped ENNReal

/-! ### The two notions on the laws of the two runs -/

section Laws

variable {Ω₁ Ω₂ O : Type} (μ : OuterMeasure Ω₁) (ν : OuterMeasure Ω₂) (out₁ : Ω₁ → O)
  (out₂ : Ω₂ → O) (win₁ : Set Ω₁) (win₂ : Set Ω₂) (ext : Set Ω₂)

/-- **Weak online simulation extraction, on the laws of the two runs** (combining Unruh 2015,
ePrint 2014/587, Definition 4, p. 7; Unruh 2017, ePrint 2017/398, Definition 11, p. 17;
Don–Fehr–Majenz–Schaffner 2022, ePrint 2022/270, Definition 3.1, p. 10; the paper's `def:bcs-se`).
`μ` is the law of the simulated run, with output `out₁` and win event `win₁` (a fresh statement with
an accepted proof); `ν` is the law of the extractor's single run, with output `out₂`, win event
`win₂` and extraction event `ext`.

* `sim_le`: on every event of the output, winning has probability in the simulated run at most
  its probability in the extractor's run plus `errsim`. A trace distance at most `errsim` between
  the states of output and verdict in the two runs implies it, since measuring does not increase
  trace distance.
* `winsNotExtracts_le`: the extractor's run wins without extraction with probability at most
  `errse`. -/
structure WeakOnlineSimulationExtraction (errsim errse : ℝ≥0∞) : Prop where
  /-- The simulation clause, on the events of the output and the verdict. -/
  sim_le : ∀ S : Set O, μ (win₁ ∩ out₁ ⁻¹' S) ≤ ν (win₂ ∩ out₂ ⁻¹' S) + errsim
  /-- The extraction clause. -/
  winsNotExtracts_le : ν (win₂ \ ext) ≤ errse

/-- **Weak simulation-sound extractability for query-free tests, on the laws of the two runs**
(Unruh 2017, ePrint 2017/398, Definition 14, p. 21, eq. (6), weak variant, `d = 1`, `p = 1`, for
tests that are events of the measured output, with extraction in one run): for every test `S`,
the simulated run wins and passes the test with probability at most the probability that the
extractor's run extracts and passes the test, plus `err`. -/
def WeakSimExtraction (err : ℝ≥0∞) : Prop :=
  ∀ S : Set O, μ (win₁ ∩ out₁ ⁻¹' S) ≤ ν (ext ∩ out₂ ⁻¹' S) + err

variable {μ ν out₁ out₂ win₁ win₂ ext} in
/-- **The joint form gives the weak form for query-free tests**, on the laws of the two runs:
weak online simulation extraction with simulation error `errsim` and
extraction error `errse` gives weak simulation-sound extractability (Unruh 2017, Definition 14,
p. 21, eq. (6)) for tests that are events of the measured output, at error `errsim + errse`. -/
@[headline]
theorem WeakOnlineSimulationExtraction.unruhSimExtraction {errsim errse : ℝ≥0∞}
    (h : WeakOnlineSimulationExtraction μ ν out₁ out₂ win₁ win₂ ext errsim errse) :
    WeakSimExtraction μ ν out₁ out₂ win₁ ext (errsim + errse) := fun S =>
  calc μ (win₁ ∩ out₁ ⁻¹' S) ≤ ν (win₂ ∩ out₂ ⁻¹' S) + errsim := h.sim_le S
    _ ≤ ν (ext ∩ out₂ ⁻¹' S) + ν (win₂ \ ext) + errsim := by
        gcongr
        refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
        by_cases he : ω ∈ ext
        · exact Or.inl ⟨he, hω.2⟩
        · exact Or.inr ⟨hω.1, he⟩
    _ = ν (ext ∩ out₂ ⁻¹' S) + (errsim + ν (win₂ \ ext)) := by ring
    _ ≤ ν (ext ∩ out₂ ⁻¹' S) + (errsim + errse) := by
        gcongr
        exact h.winsNotExtracts_le

end Laws

namespace QROM

open GordieHowe.QROM

variable {m k e : ℕ} {Cl Stmt O : Type} (V : NARG.QROM.Verifier m k e Cl Stmt) (claimOf : O → Cl)

/-- **The expansion of a terminating output is the verifier's expansion of its claim**: the
queries and answers of `expansionOpt` on `some c`, with the claim of `c`, are the verifier's
expanded claim. -/
theorem expand_expansionOpt_some (o₀ : O) (h : Bits m → Out k e) (c : O) :
    (⟨((V.expansionOpt claimOf o₀).expand (k := V.kq) h (some c)).queries,
        ((V.expansionOpt claimOf o₀).expand (k := V.kq) h (some c)).answers, claimOf c⟩ :
      GordieHowe.QROM.BaseGame.Tuple (Bits m) (Out k e) Cl V.kq) =
      V.expansion.expand (k := V.kq) h (claimOf c) := by
  have hq : ((V.expansionOpt claimOf o₀).queries h (some c) : Fin V.kq → _) =
      V.expansion.queries h (claimOf c) :=
    funext (queries_expansionOpt V claimOf o₀ h (some c))
  simp only [Expansion.expand, hq]

end QROM

end GordieHowe.SPBCS

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

/-! ### The verdict under the final oracle -/

section Verdict

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)

/-- **The spBCS verifier accepts the output of a control under the final oracle**: the
base oracle `H` reprogrammed by the assignments in force after the last slot, read from the
challenger's registers `c.2`, accepts the adversary's output `c.1`. `Wins` is this with freshness
(`wins_iff`). -/
def AcceptsFinal (H : Bits (queryBits k kN kS L) → XOut k e)
    (c : Base.Ctrl A.toTPKindAlg Psim Q) : Prop :=
  M.Accepts (chainOracle (H.reprogram (A.toTPKindAlg.postAss (simExtChallenger Psim Q) c.2)))
    c.1.stmt c.1.proof (Qs c.1.stmt)

theorem wins_iff (fx : X' → X) (H : Bits (queryBits k kN kS L) → XOut k e)
    (v : Base.Reg A Psim Q) :
    Wins A.toTPKindAlg Psim Q Qs fx H v ↔
      Base.Fresh A Psim Q fx v ∧
        AcceptsFinal Qs A Psim Q H (Base.ctrlOf A.toTPKindAlg Psim Q v) :=
  Iff.rfl

/-- **The base game of the verdict under the final oracle** with `K` queries, on the control (the
second condition of `simExtGame`): an oracle under which the spBCS verifier accepts the
output, each of its queries in the tuple with that answer, read through the assignments of the
challenger's registers, as its final answer. -/
def verdictGame (K : ℕ) :
    GordieHowe.QROM.BaseGame (Bits (queryBits k kN kS L)) (Out k e) (Base.Ctrl A.toTPKindAlg Psim Q) K :=
  {o | ∃ h, M.Accepts h o.out.1.stmt o.out.1.proof (Qs o.out.1.stmt) ∧
    ∀ q ∈ M.queries o.out.1.stmt o.out.1.proof h (Qs o.out.1.stmt),
      ∃ i, o.queries i = Query.toBits q ∧
        Base.finalAnswerOf A.toTPKindAlg Psim Q o.out.2 (o.queries i) (o.answers i) = h q}

theorem mem_verdictGame_of_mem_simExtGame (fx : X' → X) {K : ℕ}
    {o : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (Base.Reg A Psim Q) K}
    (ho : o ∈ simExtGame A.toTPKindAlg Psim Q Qs fx K) :
    (⟨o.queries, o.answers, Base.ctrlOf A.toTPKindAlg Psim Q o.out⟩ :
      GordieHowe.QROM.BaseGame.Tuple _ _ _ K) ∈ verdictGame Qs A Psim Q K :=
  ho.2.1

/-- **The verdict game decides acceptance under the final oracle**: the control expanded by the
extraction queries wins `verdictGame` exactly when the spBCS verifier accepts its output
under the final oracle. Hypothesis `hkq`: accepting runs make at most `kq` verifier queries. -/
theorem expand_mem_verdictGame_iff
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    (H : Bits (queryBits k kN kS L) → XOut k e) (c : Base.Ctrl A.toTPKindAlg Psim Q) :
    (ctrlExpansion A.toTPKindAlg Psim Q Qs).expand (fun a => outEquiv k e (H a)) c ∈
        verdictGame Qs A Psim Q (kq + Q * Psim.q) ↔ AcceptsFinal Qs A Psim Q H c := by
  constructor
  · rintro ⟨h', hv, hcov⟩
    refine accepts_of_eqOn_queries (h := h') (fun q hq => ?_) hv
    obtain ⟨i, hi1, hi2⟩ := hcov q hq
    have ha : ((ctrlExpansion A.toTPKindAlg Psim Q Qs).expand
        (fun a => outEquiv k e (H a)) c).answers i = outEquiv k e (H (Query.toBits q)) := by
      show outEquiv k e (H (((ctrlExpansion A.toTPKindAlg Psim Q Qs).expand
        (fun a => outEquiv k e (H a)) c).queries i)) = _
      rw [hi1]
    rw [← hi2, hi1, ha]
    exact (Base.finalAnswerOf_eq A.toTPKindAlg Psim Q H c.2 q).symm
  · intro hv
    set h := chainOracle (H.reprogram (A.toTPKindAlg.postAss (simExtChallenger Psim Q) c.2))
    have htr := trace_extractionProgOf A.toTPKindAlg Psim Q Qs H c
    have hlen : ((extractionProgOf A.toTPKindAlg Psim Q Qs c).trace
        (fun a => outEquiv k e (H a))).length ≤ kq + Q * Psim.q := by
      rw [htr, List.length_append, List.length_map]
      exact Nat.add_le_add (hkq _ h _ hv)
        (FullPast.simQueryInputsOf_length_le A.toTPKindAlg Psim Q c.2)
    refine ⟨h, hv, fun q hq => ?_⟩
    have hmem : ∃ i : Fin (kq + Q * Psim.q),
        ((ctrlExpansion A.toTPKindAlg Psim Q Qs).expand
          (fun a => outEquiv k e (H a)) c).queries i = Query.toBits q ∧
        ((ctrlExpansion A.toTPKindAlg Psim Q Qs).expand
          (fun a => outEquiv k e (H a)) c).answers i = outEquiv k e (H (Query.toBits q)) :=
      OracleProg.mem_expand_toExpansion _ _ _ c hlen
        (by rw [htr]; exact List.mem_append_left _ (List.mem_map_of_mem hq))
    obtain ⟨i, hi1, hi2⟩ := hmem
    refine ⟨i, hi1, ?_⟩
    rw [hi1, hi2]
    exact Base.finalAnswerOf_eq A.toTPKindAlg Psim Q H c.2 q

variable {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]

/-- **On registers consistent with the oracle, the expanded registers win `simExtGame` exactly
when the adversary wins.** Hypotheses: `hkq`, accepting runs make at most `kq` verifier queries;
`hA`, the simulator program assigns only at the keys of its chain inputs; `hv`, the registers are
consistent with `H`. -/
theorem expand_mem_simExtGame_iff
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    {Psim' : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)} {fx : X' → X} (hA : M.SimAssignsAtKeys B Psim' fx)
    {H : Bits (queryBits k kN kS L) → XOut k e} {v : Base.Reg A Psim' Q}
    (hv : A.toTPKindAlg.Consistent (simExtChallenger Psim' Q) H v) :
    (simExtractionExpansion A.toTPKindAlg Psim' Q Qs).expand (fun a => outEquiv k e (H a)) v ∈
        simExtGame A.toTPKindAlg Psim' Q Qs fx (kq + Q * Psim'.q) ↔
      Wins A.toTPKindAlg Psim' Q Qs fx H v :=
  ⟨fun ho => ⟨ho.1, (expand_mem_verdictGame_iff Qs A Psim' Q kq hkq H
      (Base.ctrlOf A.toTPKindAlg Psim' Q v)).1 (by
        have hm := mem_verdictGame_of_mem_simExtGame Qs A Psim' Q fx ho
        rw [← comapIn_ctrlExpansion, Expansion.expand_comapIn] at hm
        exact hm)⟩,
    expand_mem_simExtGame Q Qs fx A.toTPKindAlg hkq hA hv⟩

end Verdict

/-! ### The runs and the compiled verifiers -/

section Verifiers

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)

/-- **The simulated run of `A`**: the composition of its trace-preserving form with the
simulation challenger answering `Q` proof queries by `Psim`, outputting the control (the adversary's
output and the challenger's registers); the adversary's workspace is not measured.

Running time: that of `A`, plus one run of the simulator program (`Psim.q` queries) for each of
the at most `Q` answered proof queries; polynomial when `A` and `Psim` are.
This running time is argued here, not proved in Lean. -/
noncomputable abbrev simRun :
    Alg (Bits (queryBits k kN kS L)) (XOut k e) (Base.Ctrl A.toTPKindAlg Psim Q) :=
  A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) (Base.ctrlOf A.toTPKindAlg Psim Q)

/-- **The model's simulated run of `A`** (`AdaptiveIAlg.toKindAlg`): the composition of `A` with
the simulation challenger answering `Q` proof queries by `Psim`, outputting the control; the
adversary's workspace is not measured.

Running time: that of `A`, plus one run of the simulator program (`Psim.q` queries) for each of
the at most `Q` answered proof queries; polynomial when `A` and `Psim` are.
This running time is argued here, not proved in Lean. -/
noncomputable abbrev simRunModel :
    Alg (Bits (queryBits k kN kS L)) (XOut k e) (Base.Ctrl A.toTPKindAlg Psim Q) :=
  A.toKindAlg.composeBothOut (simExtChallenger Psim Q) (Base.ctrlOf A.toTPKindAlg Psim Q)

/-- **The spBCS verifier under the final oracle, on the control** (a `NARG.QROM.Verifier`): the
extraction queries (`ctrlExpansion`, `kq + Q · q` of them); on their answers it accepts when an
oracle with these answers accepts the adversary's output under the oracle reprogrammed by the
assignments in force (`AcceptsFinal`, `NARG.Verifier.ofOracle`); and the adversary's statement. -/
noncomputable def simVerifier :
    NARG.QROM.Verifier (queryBits k kN kS L) k e (Base.Ctrl A.toTPKindAlg Psim Q) X :=
  NARG.Verifier.ofOracle (kq + Q * Psim.q) (ctrlExpansion A.toTPKindAlg Psim Q Qs)
    (fun h c => AcceptsFinal Qs A Psim Q ((outEquiv k e).symm ∘ h) c) fun c => c.1.stmt

/-- **A win of the base game of `simVerifier` wins the verdict game** (`expand_mem_verdictGame_iff`).
Hypothesis `hkq`: accepting runs make at most `kq` verifier queries. -/
theorem mem_verdictGame_of_mem_game
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    {o : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e)
      (Base.Ctrl A.toTPKindAlg Psim Q) (kq + Q * Psim.q)}
    (ho : o ∈ (simVerifier Qs A Psim Q kq).game) : o ∈ verdictGame Qs A Psim Q (kq + Q * Psim.q) := by
  obtain ⟨h, he, hv⟩ := NARG.Verifier.mem_game_ofOracle.1 ho
  have hh : h = fun a => outEquiv k e (((outEquiv k e).symm ∘ h) a) :=
    funext fun a => ((outEquiv k e).apply_symm_apply (h a)).symm
  rw [← he, hh]
  exact (expand_mem_verdictGame_iff Qs A Psim Q kq hkq _ o.out).2 hv

/-- **The simulation-extraction game as a `NARG.QROM.Verifier` on the composed registers**
(proof-internal): the extraction queries; on their answers it accepts when the queries computed
from the answers, the answers and the registers win `simExtGame`, which also asks for a fresh
statement and the structure of the assignments; and the adversary's statement. Its extraction run
is `extRunFull`. -/
noncomputable def simExtVerifier (fx : X' → X) :
    NARG.QROM.Verifier (queryBits k kN kS L) k e (Base.Reg A Psim Q) X where
  kq := kq + Q * Psim.q
  expansion := simExtractionExpansion A.toTPKindAlg Psim Q Qs
  AcceptsOn v a := (⟨(simExtractionExpansion A.toTPKindAlg Psim Q Qs).queriesOn v a, a, v⟩ :
    GordieHowe.QROM.BaseGame.Tuple _ _ _ _) ∈ simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q)
  stmt v := (Base.advOut A.toTPKindAlg Psim Q v).stmt

/-- **The base game of `simExtVerifier` is `simExtGame` on the tuples whose queries are computed
from their answers.** -/
theorem mem_game_simExtVerifier_iff (fx : X' → X)
    {o : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (Base.Reg A Psim Q)
      (kq + Q * Psim.q)} :
    o ∈ (simExtVerifier Qs A Psim Q kq fx).game ↔
      o.queries = (simExtractionExpansion A.toTPKindAlg Psim Q Qs).queriesOn o.out o.answers ∧
        o ∈ simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q) := by
  rcases o with ⟨q, a, v⟩
  refine and_congr_right fun hq => ?_
  simp only at hq
  subst hq
  rfl

/-- **The knowledge bound of the simulation-extraction game** (CMS19 Proposition 8.12 for
`simExtGame`, by the cover `cover_simExtGame`, and the database bound
`dbProb_bad_union_le_of_queryCount`), from causal round-by-round knowledge soundness. -/
noncomputable def simExtKnowledgeBound [DecidableEq X] (fx : X' → X) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε) :
    (simExtVerifier Qs A Psim Q kq fx).KnowledgeBound rel (M.dbExtractBits E) (M.dbBound ε) where
  bad := DB.restrict Query.toBits ⁻¹' (M.bad rel E St ∪ digestCollision)
  mem_of_game _ ho _ hD := (cover_simExtGame A.toTPKindAlg Psim Q fx St hrbr
      ((mem_game_simExtVerifier_iff Qs A Psim Q kq fx).1 ho).2 hD).imp_left
    (M.extractsAt_dbExtractBits_iff rel E).2
  dbProb_le 𝒜 hb := dbProb_bad_union_le_of_queryCount hrbr 𝒜 hb
  mono := M.dbBound_mono ε

/-- **The extraction run of `A`**: the coherent pure form of its simulated run, followed by the
extraction queries on its measured control (`NARG.QROM.Verifier.expandedOpt` of `simVerifier`), run against
CMS19's compressed oracle by `simLaw`. The adversary's workspace is not measured.

Running time: the simulated run in pure serial form (`simRun`), then `kq + Q · Psim.q` extraction
queries computed from the measured control by the spBCS verifier's query program; polynomial
when `A` and `Psim` are. This running time is argued here, not proved in Lean. -/
noncomputable abbrev extRun
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) :=
  (simVerifier Qs A Psim Q kq).expandedOpt id (simRun A Psim Q).defaultOut
    (simRun A Psim Q).toQueryAlgCoh

/-- **The extraction run of `A` with all composed registers measured** (proof-internal): the
coherent pure form of the composition of `A` with the simulation challenger outputting all
composed registers, followed by the extraction queries of `simVerifier` on the control read from
them.

Running time: that of `extRun`, whose operations it applies in the same order.
This running time is argued here, not proved in Lean. -/
noncomputable abbrev extRunFull
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) :=
  (simVerifier Qs A Psim Q kq).expandedOpt (Base.ctrlOf A.toTPKindAlg Psim Q)
    (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut
    (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).toQueryAlgCoh

/-- **Measuring the workspace commutes with the extraction run's measurements**: the extraction
run, which measures the control and the database, has the law of the extraction run with all
composed registers measured, read through the control. The measurement of the adversary's
workspace acts on registers separate from the control and the database, so it does not change
their joint law. -/
theorem simLaw_extRun
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    (S : Set (GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e)
      (Option (Base.Ctrl A.toTPKindAlg Psim Q)) (kq + Q * Psim.q) ×
      DB (Bits (queryBits k kN kS L)) (Out k e))) :
    simLaw (outEquiv k e) (extRun Qs A Psim Q kq hkq) S =
      simLaw (outEquiv k e) (extRunFull Qs A Psim Q kq hkq)
        {p | (⟨p.1.queries, p.1.answers, p.1.out.map (Base.ctrlOf A.toTPKindAlg Psim Q)⟩,
          p.2) ∈ S} := by
  have hcoh : (simRun A Psim Q).toQueryAlgCoh =
      (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).toQueryAlgCoh.mapOut
        (Option.map (Base.ctrlOf A.toTPKindAlg Psim Q)) :=
    A.toTPKindAlg.toQueryAlgCoh_composeBothOut_comp (simExtChallenger Psim Q) id
      (Base.ctrlOf A.toTPKindAlg Psim Q)
  have hexp : (⟨fun c => ((simVerifier Qs A Psim Q kq).expansionOpt id
      (simRun A Psim Q).defaultOut).next (Option.map (Base.ctrlOf A.toTPKindAlg Psim Q) c)⟩ :
        Expansion (Bits (queryBits k kN kS L)) (Out k e)
          (Option (Base.Reg A Psim Q))) =
      (simVerifier Qs A Psim Q kq).expansionOpt (Base.ctrlOf A.toTPKindAlg Psim Q)
        (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut := by
    congr 1
    funext c
    cases c <;> rfl
  unfold extRun extRunFull NARG.QROM.Verifier.expandedOpt
  rw [hcoh, expandAdv_mapOut, ← hexp]
  rfl

/-- **The extraction run wins without extraction** at an outcome: the measured control is fresh,
the spBCS verifier accepts its output on the answers it received (`verdictGame`), and the
database extractor `dbExtract` at `E` returns no witness for its statement from the measured
database. -/
def WinsNotExtracts (fx : X' → X) [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit)
    (p : GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e)
        (Option (Base.Ctrl A.toTPKindAlg Psim Q)) (kq + Q * Psim.q) ×
      DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  ∃ c ∈ p.1.out, Base.FreshOf A.toTPKindAlg Psim Q fx c ∧
    (⟨p.1.queries, p.1.answers, c⟩ : GordieHowe.QROM.BaseGame.Tuple _ _ _ _) ∈
      verdictGame Qs A Psim Q (kq + Q * Psim.q) ∧
    ¬ M.extractsAt rel E c.1.stmt p.2

end Verifiers

/-! ### The joint form -/

variable (M B) in
/-- **Weak online simulation extractability of the spBCS compiler at one query-bounded
adversary** (the paper's `thm:bcs-se`, joint form; Unruh 2015, ePrint 2014/587, Definition 4,
p. 7, same run with simulated proofs; Unruh 2017, ePrint 2017/398, Definition 11, p. 17, joint
output; Don–Fehr–Majenz–Schaffner 2022, ePrint 2022/270, Definition 3.1, p. 10, with
`εsim = 0` and a quantum auxiliary output), with the simulator program `Psim` answering `Q`
proof queries and the database extractor `dbExtract` at `E`:

* `outputState_eq`: at every auxiliary input `a` and every value `vo` of the control and the
  verdict, the state of the composed registers in the extraction run (`extRun`, the database
  traced out) is their state in the model's simulated run (`simRunModel`). The control is the
  adversary's output (statement and proof) and the simulation challenger's registers (the
  queried statements, the assignments); it is measured. The adversary's workspace, its
  auxiliary register `Z`, is not measured and keeps its quantum state, as in
  Don–Fehr–Majenz–Schaffner's Definition 3.1. The verdict is the verifier's acceptance of the
  output under the final oracle (`AcceptsFinal`) in the simulated run and on the answers it
  received (`verdictGame`) in the extraction run.
* `winsNotExtracts_le`: averaged over the auxiliary input, the extraction run outputs a fresh
  statement with a proof the verifier accepts while `dbExtract` returns no witness with
  probability at most `ε`. -/
structure WeakOnlineSimExtracts [DecidableEq X] {tq : ℕ} (𝒜 : M.QBSimExtractionAdversary B X' tq)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (Q kq : ℕ) (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    (fx : X' → X) {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
    (ε : ℝ≥0∞) : Prop where
  /-- The state clause: the extraction run leaves the composed registers in the model's simulated
  run's state, the adversary's workspace unmeasured. -/
  outputState_eq : ∀ (a : 𝒜.Aux)
    (vo : NARG.VerifiedOutput (Base.Ctrl (𝒜.alg a).toTPKindAlg Psim Q)),
    (simVerifier Qs (𝒜.alg a) Psim Q kq).extractionOutputState id NARG.QROM.compressedSim (simRun (𝒜.alg a) Psim Q)
        (simRun (𝒜.alg a) Psim Q).defaultOut vo =
      (simVerifier Qs (𝒜.alg a) Psim Q kq).realOutputState id (simRunModel (𝒜.alg a) Psim Q) vo
  /-- The extraction clause. -/
  winsNotExtracts_le : ∑' a, 𝒜.aux a * simLaw (outEquiv k e) (extRun Qs (𝒜.alg a) Psim Q kq hkq)
    {p | WinsNotExtracts Qs (𝒜.alg a) Psim Q kq fx rel E p} ≤ ε

variable (M B) in
/-- **Weak online simulation extractability of the spBCS compiler** (the paper's
`thm:bcs-se`, joint form; `WeakOnlineSimExtracts`): for every finite type of queried statements read
through `fx` and every query-bounded adversary with at most `tq` queries of its own whose first
`Q` proof queries are answered by the simulator program `Sim`, the extraction run of the database
extractor `dbExtract` at `E` leaves the control, the verdict and the adversary's unmeasured
workspace in the model's simulated run's state, and wins without extraction with probability at
most `ε tq Q`. -/
def WeakOnlineSimulationExtractable [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq Q : ℕ)
    (𝒜 : M.QBSimExtractionAdversary B X' tq),
    WeakOnlineSimExtracts M B Qs 𝒜 (Sim.comap fx) Q kq hkq fx rel E (ε tq Q)

/-! ### The state clause -/

section State

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)
  (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)

/-- **Within the budget, the simulated run's state is the model's**: an adversary that never asks
for a query slot over its budget on a branch of positive weight has the same final state in the
trace-preserving composition and in the model's (`AdaptiveIAlg.WithinBudget.final_composeBothOut_eq`).
-/
theorem realOutputState_simRun_eq_model (hB : A.WithinBudget)
    (vo : NARG.VerifiedOutput (Base.Ctrl A.toTPKindAlg Psim Q)) :
    (simVerifier Qs A Psim Q kq).realOutputState id (simRun A Psim Q) vo =
      (simVerifier Qs A Psim Q kq).realOutputState id (simRunModel A Psim Q) vo := by
  unfold NARG.QROM.Verifier.realOutputState Quantum.Alg.outputState
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [hB.final_composeBothOut_eq (simExtChallenger Psim Q) (Base.ctrlOf A.toTPKindAlg Psim Q) h]

/-- **The extraction run leaves the composed registers in the model's simulated run's state** at
every value of the control and the verdict, the adversary's workspace unmeasured
(`GordieHowe.SPBCS.QROM.extractionOutputState_eq` and `realOutputState_simRun_eq_model`). -/
theorem extractionOutputState_eq_model (hB : A.WithinBudget)
    (vo : NARG.VerifiedOutput (Base.Ctrl A.toTPKindAlg Psim Q)) :
    (simVerifier Qs A Psim Q kq).extractionOutputState id NARG.QROM.compressedSim (simRun A Psim Q)
        (simRun A Psim Q).defaultOut vo =
      (simVerifier Qs A Psim Q kq).realOutputState id (simRunModel A Psim Q) vo :=
  (QROM.extractionOutputState_eq (simVerifier Qs A Psim Q kq) id (simRun A Psim Q) _
    vo).trans (realOutputState_simRun_eq_model Qs A Psim Q kq hB vo)

end State

/-! ### The extraction clause -/

section Extraction

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof)) (Q kq : ℕ)
  (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
  {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]

/-- **A fresh output accepted under the final oracle wins `simExtGame` in the extraction run, almost
surely**: the outcomes of the extraction run with all composed registers measured whose output is
fresh and whose control wins the verdict game but not `simExtGame` have probability `0`, since on
registers consistent with the oracle the two games agree (`expand_mem_simExtGame_iff`) and the
simulated run is supported on consistent registers (`KindAlg.realLaw_composeBothOut_inter`). -/
theorem simLaw_verdict_not_simExtGame
    {Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)} {fx : X' → X} (hA : M.SimAssignsAtKeys B Psim fx) :
    simLaw (outEquiv k e) (extRunFull Qs A Psim Q kq hkq)
        {p | ∃ v ∈ p.1.out, Base.Fresh A Psim Q fx v ∧
          (⟨p.1.queries, p.1.answers, Base.ctrlOf A.toTPKindAlg Psim Q v⟩ :
            GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∈
            verdictGame Qs A Psim Q (kq + Q * Psim.q) ∧
          (⟨p.1.queries, p.1.answers, v⟩ : GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∉
            simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q)} = 0 := by
  set e' := outEquiv k e
  set A₀ := A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id
  set V1 := simExtVerifier Qs A Psim Q kq fx
  set Ec := ctrlExpansion A.toTPKindAlg Psim Q Qs
  set E := simExtractionExpansion A.toTPKindAlg Psim Q Qs
  set T : Set (GordieHowe.QROM.BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e)
      (Option (Base.Reg A Psim Q)) (kq + Q * Psim.q)) :=
    {o | ∃ v ∈ o.out, Base.Fresh A Psim Q fx v ∧
      (⟨o.queries, o.answers, Base.ctrlOf A.toTPKindAlg Psim Q v⟩ :
        GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∈
        verdictGame Qs A Psim Q (kq + Q * Psim.q) ∧
      (⟨o.queries, o.answers, v⟩ : GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∉
        simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q)}
  have hrun : extRunFull Qs A Psim Q kq hkq = V1.expandedOpt id A₀.defaultOut A₀.toQueryAlgCoh :=
    rfl
  refine le_antisymm ?_ zero_le
  calc simLaw e' (extRunFull Qs A Psim Q kq hkq) {p | p.1 ∈ T}
      = ((V1.expandedOpt id A₀.defaultOut A₀.toQueryAlgCoh).realLaw e').toOuterMeasure
          {p | p.out ∈ T} := by
        rw [hrun]
        exact simLaw_out e' _ T
    _ = (A₀.realLaw e').toOuterMeasure
          ((fun p => (⟨(V1.expansionOpt id A₀.defaultOut).expand p.oracle p.out,
            p.oracle⟩ : Outcome _ _ _)) ⁻¹' {p | p.out ∈ T}) := by
        rw [expand_adversary, PMF.toOuterMeasure_map_apply, Quantum.Alg.realLaw_toQueryAlgCoh]
        rfl
    _ ≤ (A₀.realLaw e').toOuterMeasure {p | ∃ v, p.out = some v ∧
            (Base.Fresh A Psim Q fx v ∧
              Ec.expand (k := kq + Q * Psim.q) p.oracle (Base.ctrlOf A.toTPKindAlg Psim Q v) ∈
                verdictGame Qs A Psim Q (kq + Q * Psim.q) ∧
              E.expand (k := kq + Q * Psim.q) p.oracle v ∉
                simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q))} := by
        refine MeasureTheory.measure_mono ?_
        rintro ⟨o, f⟩ ⟨v, hv, hf, hg, hng⟩
        obtain rfl : o = some v := hv
        have hexp : (⟨((V1.expansionOpt id A₀.defaultOut).expand
              (k := kq + Q * Psim.q) f (some v)).queries,
            ((V1.expansionOpt id A₀.defaultOut).expand
              (k := kq + Q * Psim.q) f (some v)).answers, v⟩ :
            GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) = E.expand (k := kq + Q * Psim.q) f v :=
          QROM.expand_expansionOpt_some V1 id A₀.defaultOut f v
        have hexpc : (⟨((V1.expansionOpt id A₀.defaultOut).expand
              (k := kq + Q * Psim.q) f (some v)).queries,
            ((V1.expansionOpt id A₀.defaultOut).expand
              (k := kq + Q * Psim.q) f (some v)).answers,
              Base.ctrlOf A.toTPKindAlg Psim Q v⟩ :
            GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) =
              Ec.expand (k := kq + Q * Psim.q) f (Base.ctrlOf A.toTPKindAlg Psim Q v) :=
          QROM.expand_expansionOpt_some (simVerifier Qs A Psim Q kq)
            (Base.ctrlOf A.toTPKindAlg Psim Q) A₀.defaultOut f v
        change (⟨((V1.expansionOpt id A₀.defaultOut).expand
              (k := kq + Q * Psim.q) f (some v)).queries,
            ((V1.expansionOpt id A₀.defaultOut).expand
              (k := kq + Q * Psim.q) f (some v)).answers,
              Base.ctrlOf A.toTPKindAlg Psim Q v⟩ :
            GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∈
          verdictGame Qs A Psim Q (kq + Q * Psim.q) at hg
        change (⟨((V1.expansionOpt id A₀.defaultOut).expand
              (k := kq + Q * Psim.q) f (some v)).queries,
            ((V1.expansionOpt id A₀.defaultOut).expand
              (k := kq + Q * Psim.q) f (some v)).answers, v⟩ :
            GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∉
          simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q) at hng
        rw [hexpc] at hg
        rw [hexp] at hng
        exact ⟨v, rfl, hf, hg, hng⟩
    _ = (A₀.realLaw e').toOuterMeasure
          {p | ∃ v, p.out = some v ∧
            (Base.Fresh A Psim Q fx v ∧
              Ec.expand (k := kq + Q * Psim.q) p.oracle (Base.ctrlOf A.toTPKindAlg Psim Q v) ∈
                verdictGame Qs A Psim Q (kq + Q * Psim.q) ∧
              E.expand (k := kq + Q * Psim.q) p.oracle v ∉
                simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q)) ∧
            A.toTPKindAlg.Consistent (simExtChallenger Psim Q) (e'.symm ∘ p.oracle) v} :=
        KindAlg.realLaw_composeBothOut_inter _ _ e' fun v f =>
          Base.Fresh A Psim Q fx v ∧
            Ec.expand (k := kq + Q * Psim.q) f (Base.ctrlOf A.toTPKindAlg Psim Q v) ∈
              verdictGame Qs A Psim Q (kq + Q * Psim.q) ∧
            E.expand (k := kq + Q * Psim.q) f v ∉
              simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q)
    _ = 0 := by
        refine MeasureTheory.measure_mono_null (fun p hp => ?_) MeasureTheory.measure_empty
        obtain ⟨v, -, ⟨hf, hg, hng⟩, hc⟩ := hp
        have he : p.oracle = fun a => e' ((e'.symm ∘ p.oracle) a) :=
          funext fun a => (e'.apply_symm_apply _).symm
        rw [he] at hg hng
        exact hng ((expand_mem_simExtGame_iff Qs A Q kq hkq hA hc).2
          ⟨hf, (expand_mem_verdictGame_iff Qs A Psim Q kq hkq _
            (Base.ctrlOf A.toTPKindAlg Psim Q v)).1 hg⟩)

variable [DecidableEq X]

/-- **The extraction run of one adversary wins without extraction with probability at most the
spBCS knowledge error** at `kq + Q · q` appended queries and `b + kq + Q · q` queries, with `b` the
per-branch query count of the simulated run: the extraction run with all composed registers
measured has the law of the control and the database (`simLaw_extRun`), the knowledge bound of
`simExtGame` (`simExtKnowledgeBound`, `GordieHowe.SPBCS.QROM.simLaw_acceptsNotExtracts_le_of_queryCount`)
and `simLaw_verdict_not_simExtGame`. -/
theorem simLaw_winsNotExtracts_le {Wit : Type} {rel : Set (X × Wit)}
    {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X} {ε : ChIdx P t → ℝ≥0}
    (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)} {fx : X' → X} (hA : M.SimAssignsAtKeys B Psim fx) :
    simLaw (outEquiv k e) (extRun Qs A Psim Q kq hkq)
        {p | WinsNotExtracts Qs A Psim Q kq fx rel E p} ≤
      knowledgeError k e (kq + Q * Psim.q) (FullPast.branchQueries A Psim Q + (kq + Q * Psim.q))
        M.senc.digestsPerInput Mg.nJ (maxError ε) := by
  set A₀ := A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id
  set V1 := simExtVerifier Qs A Psim Q kq fx
  set ν := simLaw (outEquiv k e) (extRunFull Qs A Psim Q kq hkq)
  have hrun : extRunFull Qs A Psim Q kq hkq = V1.expandedOpt id A₀.defaultOut A₀.toQueryAlgCoh :=
    rfl
  have hK := QROM.simLaw_acceptsNotExtracts_le_of_queryCount V1 id
    (simExtKnowledgeBound Qs A Psim Q kq fx hrbr) A₀.defaultOut A₀.toQueryAlgCoh
    (AdaptiveIAlg.tpQueryCount (outEquiv k e) A (simExtChallenger Psim Q) id id)
  rw [← hrun] at hK
  have h0 := simLaw_verdict_not_simExtGame Qs A Q kq hkq hA
  have h1 := QROM.simLaw_queries_ne V1 id A₀.defaultOut A₀.toQueryAlgCoh
  rw [← hrun] at h1
  refine (simLaw_extRun Qs A Psim Q kq hkq _).trans_le ?_
  calc ν {p | (⟨p.1.queries, p.1.answers, p.1.out.map (Base.ctrlOf A.toTPKindAlg Psim Q)⟩,
          p.2) ∈ {p | WinsNotExtracts Qs A Psim Q kq fx rel E p}}
      ≤ ν (({p | V1.AcceptsNotExtracts id rel (M.dbExtractBits E) p.1 p.2} ∪
          {p | ∃ v ∈ p.1.out, Base.Fresh A Psim Q fx v ∧
            (⟨p.1.queries, p.1.answers, Base.ctrlOf A.toTPKindAlg Psim Q v⟩ :
              GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∈
              verdictGame Qs A Psim Q (kq + Q * Psim.q) ∧
            (⟨p.1.queries, p.1.answers, v⟩ : GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∉
              simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q)}) ∪
          {p | p.1.queries ≠ (V1.expansionOpt id A₀.defaultOut).queriesOn p.1.out p.1.answers}) := by
        refine MeasureTheory.measure_mono fun p hp => ?_
        obtain ⟨c, hc, hf, hg, hne⟩ := hp
        obtain ⟨v, hv, rfl⟩ := Option.mem_map.1 hc
        by_cases hq : p.1.queries = (V1.expansionOpt id A₀.defaultOut).queriesOn p.1.out p.1.answers
        · by_cases hs : (⟨p.1.queries, p.1.answers, v⟩ : GordieHowe.QROM.BaseGame.Tuple _ _ _ _) ∈
              simExtGame A.toTPKindAlg Psim Q Qs fx (kq + Q * Psim.q)
          · have hq' : p.1.queries =
                (simExtractionExpansion A.toTPKindAlg Psim Q Qs).queriesOn v p.1.answers := by
              rw [hq, Option.mem_def.1 hv]
              rfl
            exact Or.inl (Or.inl ⟨v, hv, (mem_game_simExtVerifier_iff Qs A Psim Q kq fx).2 ⟨hq', hs⟩,
              fun h => hne ((M.extractsAt_dbExtractBits_iff rel E).1 h)⟩)
          · exact Or.inl (Or.inr ⟨v, hv, hf, hg, hs⟩)
        · exact Or.inr hq
    _ ≤ ν {p | V1.AcceptsNotExtracts id rel (M.dbExtractBits E) p.1 p.2} + 0 + 0 :=
        (MeasureTheory.measure_union_le _ _).trans (add_le_add
          ((MeasureTheory.measure_union_le _ _).trans (add_le_add le_rfl h0.le)) h1.le)
    _ ≤ _ := by
        rw [add_zero, add_zero]
        exact hK

end Extraction

/-! ### The theorem -/

variable {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]

/-- **Weak online simulation extractability of the spBCS compiler in the QROM** (paper
`thm:bcs-se`(1), joint form; `WeakOnlineSimulationExtractable`): for a composite causally
round-by-round knowledge sound at the causal extractor `E` with errors `ε` (`hrbr`), query phases
whose accepting runs make at most `kq` verifier queries (`hkq`), and a counted simulator program
`Sim` that assigns only at the keys of its chain inputs (`hA`), with the simulation oracle running
`Sim` on any statement: against every query-bounded adversary, the extraction run of the database
extractor `dbExtract` leaves the control (the adversary's output and the challenger's registers),
the verdict and the adversary's unmeasured workspace in the model's simulated run's state, and
wins without extraction with probability at most `simExtractionError kq (max_c ε c) q tq Q`, with
`q` the queries of one run of `Sim`.

The statements `X` are an arbitrary type. The adversary's proof queries range over a finite alphabet
`X'` read as statements through an arbitrary map `fx` (`WeakOnlineSimulationExtractable`); as for
zero knowledge (`everlastingZeroKnowledge_qrom`), this covers every adversary of
`def:adversary`, whose registers have finite alphabets (Watrous, TQI, Definition 2.1, p. 59). -/
@[headline]
theorem weak_online_simulation_extractability_qrom [DecidableEq X] {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (hA : M.SimAssignsAtKeys B Sim id) :
    M.WeakOnlineSimulationExtractable B Qs rel E kq hkq Sim
      (M.simExtractionError kq (maxError ε) Sim.q) := by
  intro X' _ _ fx tq Q 𝒜
  refine ⟨fun a vo => extractionOutputState_eq_model Qs (𝒜.alg a) _ Q kq (𝒜.withinBudget a) vo,
    ?_⟩
  set Psim := Sim.comap fx
  have hq : Psim.q = Sim.q := rfl
  rw [← hq]
  have key : ∀ a, simLaw (outEquiv k e) (extRun Qs (𝒜.alg a) Psim Q kq hkq)
      {p | WinsNotExtracts Qs (𝒜.alg a) Psim Q kq fx rel E p} ≤
      M.simExtractionError kq (maxError ε) Psim.q tq Q := fun a => by
    refine (simLaw_winsNotExtracts_le Qs (𝒜.alg a) Q kq hkq hrbr (hA.comap fx)).trans ?_
    unfold simExtractionError knowledgeError
    have h2 := 𝒜.queries_le a
    have hb : FullPast.branchQueries (𝒜.alg a) Psim Q + (kq + Q * Psim.q) ≤
        tq + Q * Psim.q + (kq + Q * Psim.q) := by
      change (𝒜.alg a).width * (𝒜.alg a).budget + Q * Psim.q + (𝒜.alg a).width * (𝒜.alg a).post +
        (kq + Q * Psim.q) ≤ tq + Q * Psim.q + (kq + Q * Psim.q)
      nlinarith
    gcongr
  calc ∑' a, 𝒜.aux a * simLaw (outEquiv k e) (extRun Qs (𝒜.alg a) Psim Q kq hkq)
        {p | WinsNotExtracts Qs (𝒜.alg a) Psim Q kq fx rel E p}
      ≤ ∑' a, 𝒜.aux a * M.simExtractionError kq (maxError ε) Psim.q tq Q :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (key a) zero_le
    _ = M.simExtractionError kq (maxError ε) Psim.q tq Q := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### The weak form for query-free tests -/

section WeakForm

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)
  (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) (fx : X' → X)
  [DecidableEq X] {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)

/-- **The laws of the model's simulated run and the extraction run of one adversary, with all
composed registers measured, are weak online simulation extraction**
(`WeakOnlineSimulationExtraction`) with simulation error `0` and extraction error the probability of
`WinsNotExtracts` in the extraction run (`extRun`, the workspace unmeasured): the output is all
composed registers (read as the default output when the run does not terminate), the win events
are `Wins` under the uniform oracle and freshness with the verdict game in the extraction run, and
the extraction event is `dbExtract` returning a witness from the measured database. Measuring the
workspace after the extraction run's measurements does not change the law of the control and the
database (`simLaw_extRun`). -/
theorem jointSimExtraction_extRun (hB : A.WithinBudget) :
    WeakOnlineSimulationExtraction
      (((A.toKindAlg.composeBothOut (simExtChallenger Psim Q) id).realLaw
        (outEquiv k e)).toOuterMeasure)
      (simLaw (outEquiv k e) (extRunFull Qs A Psim Q kq hkq))
      (fun p => p.out.getD (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)
      (fun p => p.1.out.getD
        (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)
      {p | ∃ v, p.out = some v ∧ Wins A.toTPKindAlg Psim Q Qs fx ((outEquiv k e).symm ∘ p.oracle) v}
      {p | ∃ v ∈ p.1.out, Base.Fresh A Psim Q fx v ∧
        (⟨p.1.queries, p.1.answers, Base.ctrlOf A.toTPKindAlg Psim Q v⟩ :
          GordieHowe.QROM.BaseGame.Tuple _ _ _ (kq + Q * Psim.q)) ∈
          verdictGame Qs A Psim Q (kq + Q * Psim.q)}
      {p | ∃ v ∈ p.1.out, M.extractsAt rel E (Base.advOut A.toTPKindAlg Psim Q v).stmt p.2}
      0 (simLaw (outEquiv k e) (extRun Qs A Psim Q kq hkq)
        {p | WinsNotExtracts Qs A Psim Q kq fx rel E p}) where
  sim_le S := by
    set V2 := simVerifier Qs A Psim Q kq
    set A₀ := A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id
    have hv := QROM.simLaw_verdict V2 (Base.ctrlOf A.toTPKindAlg Psim Q) A₀.defaultOut
      A₀.toQueryAlgCoh {vo | vo.accepted ∧ ∃ v ∈ vo.out, Base.Fresh A Psim Q fx v ∧ v ∈ S}
    rw [Quantum.Alg.realLaw_toQueryAlgCoh] at hv
    rw [add_zero, hB.realLaw_composeBothOut_eq (simExtChallenger Psim Q) id (outEquiv k e)]
    calc _ ≤ (A₀.realLaw (outEquiv k e)).toOuterMeasure
          {p | (⟨p.out, ∃ c ∈ p.out, V2.Accepted p.oracle (Base.ctrlOf A.toTPKindAlg Psim Q c)⟩ :
            NARG.VerifiedOutput (Base.Reg A Psim Q)) ∈
              {vo | vo.accepted ∧ ∃ v ∈ vo.out, Base.Fresh A Psim Q fx v ∧ v ∈ S}} := by
          refine MeasureTheory.measure_mono ?_
          rintro ⟨o, f⟩ ⟨⟨v, hv, hw⟩, hS⟩
          obtain rfl : o = some v := hv
          exact ⟨⟨v, rfl, NARG.Verifier.ofOracle_accepted_of hw.2⟩, v, rfl, hw.1, hS⟩
      _ = _ := hv.symm
      _ ≤ _ := by
          refine MeasureTheory.measure_mono ?_
          rintro ⟨o, D⟩ ⟨⟨c, hc, hg⟩, v, hv, hf, hS⟩
          obtain rfl : c = v := Option.mem_unique hc hv
          have hout : o.out = some c := hc
          refine ⟨⟨c, hc, hf, mem_verdictGame_of_mem_game Qs A Psim Q kq hkq hg⟩, ?_⟩
          show o.out.getD _ ∈ S
          rw [hout]
          exact hS
  winsNotExtracts_le := by
    refine le_of_le_of_eq ?_ (simLaw_extRun Qs A Psim Q kq hkq _).symm
    exact MeasureTheory.measure_mono fun p ⟨⟨v, hv, hf, hg⟩, hne⟩ =>
      ⟨Base.ctrlOf A.toTPKindAlg Psim Q v, Option.mem_map_of_mem _ hv, hf, hg,
        fun hx => hne ⟨v, hv, hx⟩⟩

/-- **The fresh extraction event of `SimulationSoundExtractableFresh` is that of the extraction
run with all composed registers measured**: `extAdv` is that run with its output read as the
default output when the simulated run does not terminate. -/
theorem extractFreshTestProb_eq_simLaw (ok : A.W → Prop) :
    extractFreshTestProb Qs A Psim Q kq fx rel E ok =
      simLaw (outEquiv k e) (extRunFull Qs A Psim Q kq hkq)
        {p | M.extractsAt rel E
            (Base.advOut A.toTPKindAlg Psim Q (p.1.out.getD
              (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)).stmt
            p.2 ∧
          Base.Fresh A Psim Q fx
            (p.1.out.getD (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut) ∧
          ok (Base.advWorkspace A.toTPKindAlg Psim Q
            (p.1.out.getD
              (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)).1} := by
  unfold extractFreshTestProb simProb extAdv
  rw [expandAdv_mapOut, simLaw_mapOut]
  have hrun : extRunFull Qs A Psim Q kq hkq = expandAdv (outEquiv k e)
      ⟨fun c => (simExtractionExpansion A.toTPKindAlg Psim Q Qs).next
        (c.getD (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)⟩
      (kq + Q * Psim.q) (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).toQueryAlgCoh :=
    rfl
  rw [hrun]
  rfl

end WeakForm

variable {Qs} in
/-- **The joint form gives weak simulation-sound extractability for query-free tests**
(weak online simulation extractability implies Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6), weak variant, with fresh extraction, for tests that are classical
predicates of the workspace measured in the computational basis): if the spBCS compiler is
weakly online simulation extractable with error `ε` (`WeakOnlineSimulationExtractable`,
simulation error `0`), it is weakly simulation-sound extractable with freshness in both experiments
(`SimulationSoundExtractableFresh`) at the same error `ε = 0 + ε`
(`WeakOnlineSimulationExtraction.unruhSimExtraction`). The test acts on the workspace, which the joint form
leaves unmeasured, after the extraction run's measurements; it commutes with the measurement of
the database, which acts on separate registers (`simLaw_extRun`). -/
@[headline]
theorem WeakOnlineSimulationExtractable.unruhSimExtraction_of_queryFreeTest [DecidableEq X]
    {Wit : Type} {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {kq : ℕ}
    {hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq}
    {Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC}
    {ε : ℕ → ℕ → ℝ≥0∞} (h : M.WeakOnlineSimulationExtractable B Qs rel E kq hkq Sim ε) :
    M.SimulationSoundExtractableFresh B Qs rel E kq Sim ε := by
  intro X' _ _ fx tq Q 𝒜 ok
  set Psim := Sim.comap fx
  have hj : ∑' a : (𝒜.toSimExtraction Q).Aux, (𝒜.toSimExtraction Q).aux a *
      simLaw (outEquiv k e) (extRun Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq hkq)
        {p | WinsNotExtracts Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq fx rel E p} ≤ ε tq Q :=
    (h X' fx tq Q 𝒜).winsNotExtracts_le
  have key : ∀ a : (𝒜.toSimExtraction Q).Aux,
      winTestProb Qs ((𝒜.toSimExtraction Q).alg a) Psim Q fx (ok a) ≤
        extractFreshTestProb Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq fx rel E (ok a) +
          simLaw (outEquiv k e) (extRun Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq hkq)
            {p | WinsNotExtracts Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq fx rel E p} :=
      fun a => by
    have hw := (jointSimExtraction_extRun Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq hkq fx rel E
      (𝒜.withinBudget a)).unruhSimExtraction
      {v | Base.Fresh ((𝒜.toSimExtraction Q).alg a) Psim Q fx v ∧
        ok a (Base.advWorkspace ((𝒜.toSimExtraction Q).alg a).toTPKindAlg Psim Q v).1}
    rw [zero_add] at hw
    have hx := extractFreshTestProb_eq_simLaw Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq hkq fx
      rel E (ok a)
    refine le_trans ?_ ((hw.trans (add_le_add (MeasureTheory.measure_mono ?_) le_rfl)).trans
      (add_le_add hx.symm.le le_rfl))
    · refine MeasureTheory.measure_mono ?_
      rintro ⟨o, f⟩ ⟨v, hv, hw, hok⟩
      have hout : o = some v := hv
      subst hout
      exact ⟨⟨v, rfl, hw⟩, hw.1, hok⟩
    · rintro ⟨o, D⟩ ⟨⟨v, hv, hx⟩, hS⟩
      have hout : o.out = some v := hv
      refine ⟨?_, hS⟩
      show M.extractsAt rel E (Base.advOut _ Psim Q (o.out.getD _)).stmt D
      rw [hout]
      exact hx
  calc acceptsTest Qs (𝒜.toSimExtraction Q) Psim fx ok
      ≤ ∑' a, (𝒜.toSimExtraction Q).aux a *
          (extractFreshTestProb Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq fx rel E (ok a) +
            simLaw (outEquiv k e) (extRun Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq hkq)
              {p | WinsNotExtracts Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq fx rel E p}) :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (key a) zero_le
    _ = extractsFreshTest Qs (𝒜.toSimExtraction Q) Psim kq fx rel E ok +
          ∑' a, (𝒜.toSimExtraction Q).aux a *
            simLaw (outEquiv k e) (extRun Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq hkq)
              {p | WinsNotExtracts Qs ((𝒜.toSimExtraction Q).alg a) Psim Q kq fx rel E p} := by
        simp only [mul_add]
        rw [ENNReal.tsum_add]
        rfl
    _ ≤ _ := add_le_add le_rfl hj

/-! ### Extraction of signatures of knowledge -/

variable (M B) in
/-- **The extraction property of signatures of knowledge in the QROM** (Chase–Lysyanskaya 2006,
ePrint 2006/184, Definition 2.2 (SimExt-security), pp. 8–9, the Extraction condition, p. 9: "Pr[(p, τ) ← Simsetup(1^k);
(M_L, x, m, σ) ← A^{Sim(p,τ,·,·,·,·)}(s, p); w ← Extract(p, τ, M_L, x, m, σ) : M_L(x, w) ∨
(M_L, x, m) ∈ Q+ ∨ ¬Verify(p, M_L, x, m, σ)] = 1 − ν(k)"), for the spBCS compiler with the
simulator program `Sim` and the database extractor `dbExtract` at `E`. CL06's simulated setup and
its trapdoor are the extractor's simulation of the oracle and its database: for every finite type
of queried statements read through `fx` and every query-bounded adversary with at most `tq`
queries of its own whose first `Q` proof queries are answered by `Sim`, averaged over its auxiliary
input, the extraction run (`extRun`, which measures the adversary's output `o` and the
challenger's registers `u` and leaves the adversary's workspace unmeasured) outputs a statement
and a proof such that the spBCS verifier accepts the proof on the answers it received, the
statement is not in `Q+`, and no witness `dbExtract` returns from the measured database is a
witness of the statement, with probability at most `ε tq Q`.

CL06's `Q+` is the list of the queries sent to `Sim` with a valid witness. A CL06 adversary is run
as an adversary that checks each witness itself, a classical computation at no query cost, and
makes proof queries only for the statements sent with a valid witness, so its list of queried statements
(`Base.queriedOf` read through `fx`) is `Q+`. CL06's message is part of the statement: for the
relation `R' = {((x, m), w) | (x, w) ∈ R}` the statements are the pairs `(x, m)`. CL06 asks this
for probabilistic polynomial-time adversaries with classical auxiliary input; here the
adversaries are the query-bounded quantum adversaries of `def:adversary`, with a concrete error. -/
def CL06Extraction [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq Q : ℕ)
    (𝒜 : M.QBSimExtractionAdversary B X' tq),
    ∑' a, 𝒜.aux a * simLaw (outEquiv k e) (extRun Qs (𝒜.alg a) (Sim.comap fx) Q kq hkq)
      {p | ∃ o u, (o, u) ∈ p.1.out ∧
        (⟨p.1.queries, p.1.answers, (o, u)⟩ : GordieHowe.QROM.BaseGame.Tuple _ _ _ _) ∈
          verdictGame Qs (𝒜.alg a) (Sim.comap fx) Q (kq + Q * (Sim.comap fx).q) ∧
        o.stmt ∉ (Base.queriedOf (𝒜.alg a).toTPKindAlg (Sim.comap fx) Q u).map fx ∧
        ∀ w ∈ M.dbExtractBits E o.stmt p.2, (o.stmt, w) ∉ rel} ≤ ε tq Q

variable {Qs} in
/-- **The joint form gives the extraction property of signatures of knowledge in the QROM**
(weak online simulation extractability implies Chase–Lysyanskaya 2006,
ePrint 2006/184, Definition 2.2, "Extraction", pp. 8–9, with the extractor's simulation of the
oracle as the simulated setup and the queried statements as `Q+`; `CL06Extraction`): if the
spBCS compiler is weakly online simulation extractable with error `ε`
(`WeakOnlineSimulationExtractable`), a forger that outputs a statement not in `Q+` with an
accepted proof has a witness extracted in the same run, except with probability `ε tq Q`. The
state clause of the joint form gives the joint state of the forger's output, the challenger's
registers and the forger's unmeasured workspace in that run: it is their state against a
uniformly random oracle with simulated proofs. -/
@[headline]
theorem WeakOnlineSimulationExtractable.cl06Extraction [DecidableEq X] {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {kq : ℕ}
    {hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq}
    {Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC}
    {ε : ℕ → ℕ → ℝ≥0∞} (h : M.WeakOnlineSimulationExtractable B Qs rel E kq hkq Sim ε) :
    M.CL06Extraction B Qs rel E kq hkq Sim ε := by
  intro X' _ _ fx tq Q 𝒜
  refine le_trans (ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left
    (MeasureTheory.measure_mono fun p hp => ?_) zero_le) (h X' fx tq Q 𝒜).winsNotExtracts_le
  obtain ⟨o, u, hc, hg, hQ, hw⟩ := hp
  refine ⟨(o, u), hc, fun x' hx' heq => hQ ?_, hg, fun ⟨w, hmem, hrel⟩ => hw w (by rw [dbExtractBits_eq]; exact hmem) hrel⟩
  rw [← heq]
  exact List.mem_map_of_mem hx'

end

end GordieHowe.SPBCS
