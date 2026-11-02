-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.Ring.Transform
public import LatticeCrypto.Ring.Norms
public import GordieHowe.Model.RingSignature.Adversary
public import GordieHowe.Model.Quantum.Interactive.ConstOut
public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Foundations.ToMathlib.PMFFiber
public import GordieHowe.Foundations.ToMathlib.FintypeBytes

@[expose] public section

/-!
# SelfTargetMSIS

The SelfTargetMSIS problem of the Dilithium security proof, in the quantum random-oracle model:
given a uniform matrix `A` and a uniform vector `t`, and quantum access to a random oracle `H`,
find a message `µ` and short `(z, c, u)` with `c` the challenge of `H` at the encoding of
`u + A z + c t` and `µ`.

## Sources

- Kiltz, Lyubashevsky and Schaffner (EUROCRYPT 2018, ePrint 2017/916), §4.5.1:
  `Adv^SelfTargetMSIS_{H,m,k,γ}(A) = Pr[‖y‖∞ ≤ γ ∧ H([I | A] · y ‖ M) = c | A ← R_q^{m×k};
  (y = (r, c), M) ← A^{|H⟩}(A)]`.
- *CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation* (Version 3.1),
  §6.1, and §6.2.1, eq. (12): the instance is `[A | t | I_k]` with `(A, t)` uniform, and the
  solution `(z, c, u′)`.
- Barbosa et al. (CRYPTO 2023, ePrint 2023/246), §6.2, Definition 4: `H : R_q^m × M → B_τ` a random
  oracle, a win when `‖r‖∞ ≤ γ` and `H([I_m | A] · r, µ)` is the last entry of `r`.
- VCVio's `SelfTargetMSIS.Problem` (`LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean`,
  commit `eb0f6e4`) states the classical-ROM experiment of the same problem.

## The library's form

- The instance `(A, t)` is uniform on `Hat^{k×l} × R_q^k`: the matrix `[A | t]` of the sources with
  its last column named. `A` acts by the vendored `A * z` (`TransformOps.coeffMatVecMul`) and `c t`
  is `c • t` (`TransformOps.coeffScalarVecMul`).
- The oracle is a uniform `H : X → Y` on finite types; the adversary reaches it by at most `t`
  superposition queries. A public encoding `enc : R_q^k → M → X` makes the oracle's input from
  `u + A z + c • t` and the message, and a public map `chal : Y → R_q` reads the challenge from
  the oracle's output. The sources' `H` is `chal ∘ H ∘ enc`; their `[I | A | t] · (u, z, c)` is
  `u + A z + c • t`. The Dilithium specification writes `A z − c t + u′` (eq. (10)); a reduction
  from the signature game passes `(A, −t)`, as Barbosa et al. (Figure 6) do.
- The adversary is a `RingSignature.GameAdversary` with requests `Unit` and responses `Empty`,
  against the challenger `silentChallenger`, which answers no request: the library's one adversary
  class, query-bounded quantum algorithms in the QROM that need not be efficient; a classical
  adversary with classical oracle access is a member.
  Its start input is `(A, t)` and the table `V.view H` of the oracle (`OracleView`).
  `V := OracleView.queriesOnly X Y` hands out no table: the game of the sources (KLS18 §4.5.1,
  BBD23 Definition 4).
- `Solves norm γ enc chal A t H out`: `out = (z, c, u, µ)` with `‖z‖∞, ‖c‖∞, ‖u‖∞ ≤ γ` and
  `chal (H (enc (u + A * z + c • t) µ)) = c`. `selfTargetWinProb`: the probability of a solution in
  the run's law. `SelfTargetMSISHard`: every adversary of a class wins with probability at most
  `ε`; `selfTargetMSISHard_one`: every class at `ε = 1`, for every `V`.

## The unrestricted class with the table

- `toOuterMeasure_compl_fintype`: a PMF on a finite type gives a complement `1` minus the
  probability of the set. `prob_exists_mem_uniform`: a uniform `H : X → Y` hits `S` at one of the
  points of an injective `e : M → X` with probability `1 − (1 − Pr[S])^|M|`.
- `tableAdv enc chal c₀ tq`: with the whole oracle as its table (`OracleView.whole`), the
  adversary with no query that outputs `z = 0`, `c = c₀`, `u = 0` and a message `µ` with
  `chal (H (enc (0 + A * 0 + c₀ • t) µ)) = c₀`, if there is one.
  `le_selfTargetWinProb_tableAdv`: when `‖0‖∞ ≤ γ`, `‖c₀‖∞ ≤ γ` and `enc v` is injective for every
  `v`, it wins with probability at least `1 − (1 − p₀)^|M|`, where `p₀` is the probability that
  `chal y = c₀` for a uniform `y`. `not_selfTargetMSISHard_univ_whole`: so with the oracle as a
  table, no bound `ε < 1 − (1 − p₀)^|M|` holds for every adversary.
-/

namespace GordieHowe.Lattice

open LatticeCrypto TransformOps GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

/-- **The silent challenger**: no coins, and no request answered (`Q := 0`); a request gets the
reply with no response and no assignment. -/
noncomputable def silentChallenger (X Y : Type) : Challenger X Y Unit Empty where
  Coins := Unit
  coins := PMF.pure ()
  Q := 0
  q := 0
  respond _ _ _ := .pure ⟨none, []⟩
  respond_queries _ _ _ _ := by simp [OracleProg.trace]

variable {Coeff : Type} [CommRing Coeff] {ring : NegacyclicRing Coeff} {Hat : Type}
  [AddCommGroup Hat] [ops : TransformOps ring Hat] (norm : NormOps ring.backend) {k l : ℕ}
  {X Y M : Type}

/-- **A SelfTargetMSIS solution** for the instance `(A, t)` at the oracle `H`: `(z, c, u, µ)` with
`‖z‖∞, ‖c‖∞, ‖u‖∞ ≤ γ` and `chal (H (enc (u + A * z + c • t) µ)) = c`. -/
def Solves (γ : ℕ) (enc : PolyVec ring.Poly k → M → X) (chal : Y → ring.Poly)
    (A : PolyMatrix Hat k l) (t : PolyVec ring.Poly k) (H : X → Y)
    (out : PolyVec ring.Poly l × ring.Poly × PolyVec ring.Poly k × M) : Prop :=
  PolyVec.cInfNorm norm out.1 ≤ γ ∧ norm.cInfNorm out.2.1 ≤ γ ∧
    PolyVec.cInfNorm norm out.2.2.1 ≤ γ ∧
    chal (H (enc (out.2.2.1 + A * out.1 + out.2.1 • t) out.2.2.2)) = out.2.1

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [Fintype (PolyMatrix Hat k l)] [Nonempty (PolyMatrix Hat k l)]
  [Fintype (PolyVec ring.Poly k)] [Nonempty (PolyVec ring.Poly k)]

/-- **A SelfTargetMSIS adversary** with at most `t` oracle queries: on the instance `(A, t)` and
the table `V` of the oracle, a query-bounded quantum adversary with no requests and output
`(z, c, u, µ)`. `V := OracleView.queriesOnly X Y` is the adversary of the sources (KLS18 §4.5.1,
BBD23 Definition 4). -/
abbrev SelfTargetAdversary (V : OracleView X Y) (k l : ℕ) (Hat : Type) (P : Type) (M : Type)
    (tq : ℕ) : Type 1 :=
  GameAdversary X Y Unit Empty ((PolyMatrix Hat k l × PolyVec P k) × V.Tab)
    (PolyVec P l × P × PolyVec P k × M) tq

/-- **The SelfTargetMSIS win probability** of `B`: the instance `(A, t)` and the oracle `H`
uniform, the run of `B` on `(A, t)` and the table `V.view H`, and a solution in its output. -/
noncomputable def selfTargetWinProb (V : OracleView X Y) (γ : ℕ) (enc : PolyVec ring.Poly k → M → X)
    (chal : Y → ring.Poly) {tq : ℕ}
    (B : SelfTargetAdversary V k l Hat ring.Poly M tq) : ℝ≥0∞ :=
  (runLaw (fun At H => B (At, V.view H)) fun _ => silentChallenger X Y).toOuterMeasure
    {r | ∃ out hist, r.2.2 = some (out, hist) ∧ Solves norm γ enc chal r.1.1 r.1.2 r.2.1 out}

/-- **Hardness of SelfTargetMSIS for the class `𝒜`** of `t`-query adversaries. -/
def SelfTargetMSISHard (V : OracleView X Y) (γ : ℕ) (enc : PolyVec ring.Poly k → M → X)
    (chal : Y → ring.Poly) {tq : ℕ} (𝒜 : Set (SelfTargetAdversary V k l Hat ring.Poly M tq))
    (ε : ℝ≥0∞) : Prop :=
  ∀ B ∈ 𝒜, selfTargetWinProb norm V γ enc chal B ≤ ε

/-- **Every class at `ε = 1`.** -/
theorem selfTargetMSISHard_one (V : OracleView X Y) (γ : ℕ) (enc : PolyVec ring.Poly k → M → X)
    (chal : Y → ring.Poly) {tq : ℕ} (𝒜 : Set (SelfTargetAdversary V k l Hat ring.Poly M tq)) :
    SelfTargetMSISHard norm V γ enc chal 𝒜 1 :=
  fun _ _ => prob_runLaw_le_one _ _ _

/-! ### The unrestricted class with the table -/

omit [DecidableEq X] [Nonempty X] [DecidableEq Y] [AddGroup Y] [Nonempty Y] in
/-- **The complement of a set** under a PMF on a finite type: `1` minus the probability of the
set. -/
theorem toOuterMeasure_compl_fintype {α : Type*} [Fintype α] (p : PMF α) (s : Set α) :
    p.toOuterMeasure sᶜ = 1 - p.toOuterMeasure s := by
  classical
  have hne : p.toOuterMeasure s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (p.toOuterMeasure_apply_le_one s)
  refine ENNReal.eq_sub_of_add_eq hne ?_
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
    ← Finset.sum_add_distrib]
  simp_rw [add_comm (sᶜ.indicator _ _), Set.indicator_self_add_compl_apply]
  rw [← tsum_fintype (L := .unconditional _), p.tsum_coe]

omit [Nonempty X] [DecidableEq Y] [AddGroup Y] in
/-- **A uniform function hits a set at one of `m` distinct points** with probability
`1 − (1 − Pr[S])^m`: for an injective `e : M → X` and a uniform `H : X → Y`, the values
`H (e µ)` are independent and uniform. -/
theorem prob_exists_mem_uniform [Fintype M] {e : M → X} (he : Function.Injective e)
    (S : Set Y) :
    (PMF.uniformOfFintype (X → Y)).toOuterMeasure {H | ∃ μ, H (e μ) ∈ S} =
      1 - (1 - (PMF.uniformOfFintype Y).toOuterMeasure S) ^ Fintype.card M := by
  classical
  have hset : {H : X → Y | ∃ μ, H (e μ) ∈ S}ᶜ =
      {H | ∀ x, H x ∈ (if x ∈ Set.range e then Sᶜ else Set.univ : Set Y)} := by
    ext H
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists]
    constructor
    · intro h x
      split_ifs with hx
      · obtain ⟨μ, rfl⟩ := hx
        exact h μ
      · trivial
    · intro h μ
      simpa using h (e μ)
  have hrange : (Finset.univ.filter fun x => x ∈ Set.range e) = Finset.univ.image e := by
    ext x
    simp
  rw [← compl_compl {H : X → Y | ∃ μ, H (e μ) ∈ S}, toOuterMeasure_compl_fintype, hset,
    ← PMF.pi_uniformOfFintype, PMF.toOuterMeasure_pi_forall, ← toOuterMeasure_compl_fintype]
  congr 2
  simp_rw [apply_ite (fun s => (PMF.uniformOfFintype Y).toOuterMeasure s),
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, hrange,
    Finset.card_image_of_injective _ he, Finset.card_univ]

/-- **The message the table adversary outputs**: on `(A, t)` and the oracle `H`, a message `μ`
with `chal (H (enc (0 + A * 0 + c₀ • t) μ)) = c₀`, if there is one. -/
noncomputable def tableMsg [Nonempty M] (enc : PolyVec ring.Poly k → M → X)
    (chal : Y → ring.Poly) (c₀ : ring.Poly)
    (inp : (PolyMatrix Hat k l × PolyVec ring.Poly k) × (X → Y)) : M :=
  Classical.epsilon fun μ => chal (inp.2 (enc ((0 : PolyVec ring.Poly k) +
    inp.1.1 * (0 : PolyVec ring.Poly l) + c₀ • inp.1.2) μ)) = c₀

/-- **The table adversary**: with the whole oracle as its table (`OracleView.whole`), it outputs
`z = 0`, `c = c₀`, `u = 0` and the message `tableMsg`, with no query and no request. -/
noncomputable def tableAdv [Nonempty M] (enc : PolyVec ring.Poly k → M → X)
    (chal : Y → ring.Poly) (c₀ : ring.Poly) (tq : ℕ) :
    SelfTargetAdversary (OracleView.whole X Y) k l Hat ring.Poly M tq := fun inp =>
  (QueryBoundedAdversary.ofLaw X Y Unit Empty
    (PMF.pure ((0, c₀, 0, tableMsg enc chal c₀ inp) :
      PolyVec ring.Poly l × ring.Poly × PolyVec ring.Poly k × M))).mono (Nat.zero_le tq)

/-- **The table adversary wins with probability at least `1 − (1 − p₀)^|M|`**, where `p₀` is the
probability that `chal y = c₀` for a uniform `y`, when `‖0‖∞ ≤ γ`, `‖c₀‖∞ ≤ γ` and `enc v` is
injective for every `v`. -/
theorem le_selfTargetWinProb_tableAdv [Fintype M] [Nonempty M] {γ : ℕ}
    {enc : PolyVec ring.Poly k → M → X} {chal : Y → ring.Poly} {c₀ : ring.Poly}
    (h0 : norm.cInfNorm 0 ≤ γ) (hc₀ : norm.cInfNorm c₀ ≤ γ)
    (henc : ∀ v, Function.Injective (enc v)) (tq : ℕ) :
    1 - (1 - (PMF.uniformOfFintype Y).toOuterMeasure {y | chal y = c₀}) ^ Fintype.card M ≤
      selfTargetWinProb norm (OracleView.whole X Y) γ enc chal
        (tableAdv (Hat := Hat) (l := l) enc chal c₀ tq) := by
  have hz : ∀ {j : ℕ}, PolyVec.cInfNorm norm (0 : PolyVec ring.Poly j) ≤ γ := fun {j} =>
    (PolyVec.cInfNorm_le_iff norm).2 fun i => by
      simpa [Vector.get_eq_getElem, Vector.getElem_zero] using h0
  unfold selfTargetWinProb runLaw
  rw [PMF.toOuterMeasure_bind_apply]
  refine le_trans (b := ∑' At, PMF.uniformOfFintype (PolyMatrix Hat k l × PolyVec ring.Poly k) At *
      (1 - (1 - (PMF.uniformOfFintype Y).toOuterMeasure {y | chal y = c₀}) ^ Fintype.card M)) ?_
    (ENNReal.tsum_le_tsum fun At => mul_le_mul_of_nonneg_left ?_ zero_le)
  · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  obtain ⟨A, t⟩ := At
  rw [PMF.toOuterMeasure_bind_apply,
    ← prob_exists_mem_uniform (henc ((0 : PolyVec ring.Poly k) + A * (0 : PolyVec ring.Poly l) +
      c₀ • t)) {y | chal y = c₀}, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun H => ?_
  by_cases hH : H ∈ {H : X → Y | ∃ μ, H (enc ((0 : PolyVec ring.Poly k) +
      A * (0 : PolyVec ring.Poly l) + c₀ • t) μ) ∈ {y | chal y = c₀}}
  · rw [Set.indicator_of_mem hH]
    refine le_of_eq ?_
    dsimp only [tableAdv]
    -- the run of a `0`-query adversary drawing a point mass is that point with no history
    have hrun : ∀ (o : PolyVec ring.Poly l × ring.Poly × PolyVec ring.Poly k × M),
        ((QueryBoundedAdversary.ofLaw X Y Unit Empty (PMF.pure o)).mono
          (Nat.zero_le tq)).transcriptLaw (silentChallenger X Y) H = PMF.pure (some (o, [])) :=
      fun o => by
      rw [show ((QueryBoundedAdversary.ofLaw X Y Unit Empty (PMF.pure o)).mono
          (Nat.zero_le tq)).transcriptLaw (silentChallenger X Y) H =
          (QueryBoundedAdversary.ofLaw X Y Unit Empty (PMF.pure o)).transcriptLaw
          (silentChallenger X Y) H from rfl,
        QueryBoundedAdversary.transcriptLaw_ofLaw, PMF.pure_map]
    have hmem : (((A, t), H, some ((0, c₀, 0, tableMsg enc chal c₀ ((A, t), H)), [])) :
        (PolyMatrix Hat k l × PolyVec ring.Poly k) × (X → Y) ×
          Option ((PolyVec ring.Poly l × ring.Poly × PolyVec ring.Poly k × M) ×
            List (HistoryEntry Unit Empty))) ∈
        {r | ∃ out hist, r.2.2 = some (out, hist) ∧ Solves norm γ enc chal r.1.1 r.1.2 r.2.1 out} :=
      ⟨_, [], rfl, hz, hc₀, hz, Classical.epsilon_spec (p := fun μ => chal (H (enc
        ((0 : PolyVec ring.Poly k) + A * (0 : PolyVec ring.Poly l) + c₀ • t) μ)) = c₀) hH⟩
    rw [hrun, PMF.pure_map, PMF.toOuterMeasure_pure_apply]
    split_ifs with h
    · rw [mul_one]
    · exact absurd hmem h
  · rw [Set.indicator_of_notMem hH]
    exact zero_le

/-- **With the oracle as a table, SelfTargetMSIS is not `ε`-hard for every adversary** at any
`ε < 1 − (1 − p₀)^|M|`, where `p₀` is the probability that `chal y = c₀` for a uniform `y`, when
`‖0‖∞ ≤ γ`, `‖c₀‖∞ ≤ γ` and `enc v` is injective for every `v`: the table adversary
(`tableAdv`), with no query, wins with at least that probability. -/
theorem not_selfTargetMSISHard_univ_whole [Fintype M] {γ : ℕ}
    {enc : PolyVec ring.Poly k → M → X} {chal : Y → ring.Poly} {c₀ : ring.Poly}
    (h0 : norm.cInfNorm 0 ≤ γ) (hc₀ : norm.cInfNorm c₀ ≤ γ)
    (henc : ∀ v, Function.Injective (enc v)) {tq : ℕ} {ε : ℝ≥0∞}
    (hε : ε < 1 - (1 - (PMF.uniformOfFintype Y).toOuterMeasure {y | chal y = c₀}) ^
      Fintype.card M) :
    ¬ SelfTargetMSISHard norm (OracleView.whole X Y) γ enc chal
      (Set.univ : Set (SelfTargetAdversary (OracleView.whole X Y) k l Hat ring.Poly M tq)) ε := by
  intro h
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Fintype.card_eq_zero, pow_zero, tsub_self] at hε
    exact absurd hε (not_lt.2 zero_le)
  · exact absurd (hε.trans_le (le_selfTargetWinProb_tableAdv norm h0 hc₀ henc tq))
      (not_lt.2 (h _ (Set.mem_univ _)))

end GordieHowe.Lattice
