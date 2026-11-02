-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.QueryCountExpand
public import GordieHowe.Model.QROM.AdaptiveCount
public import GordieHowe.Model.QROM.CoherentBridgeCore
public import GordieHowe.Model.Quantum.Interactive.AdaptiveTP

@[expose] public section

/-!
# Finding a collision of the random oracle in an interaction

An adversary with run-time kinds interacts with a challenger, and a readout `F` of the composed
registers names at most `ℓ` points `pts o`. This file bounds the probability, averaged over the
uniform oracle `H`, that two distinct named points in a set `D` have the same image under
`f ∘ e ∘ H` (`collision_le`): the collision game of CMS19 (Chiesa, Manohar and Spooner, ePrint
2019/834), section 2, after Lemma 2.3, with the collision taken after a map `f` of answers.

The proof: the model's law is at most the law of the trace-preserving form
(`realLaw_composeBothOut_le`), which is the law of a pure query algorithm
(`toOuterMeasure_realLaw_le_coh`). Appending `ℓ` classical queries at the named points
(`ptsExpansion`, padded with `default`) puts every accepted outcome in the base game
`collisionGame` (`winO_expandAdv`). The oracle simulation (CMS19 Lemma 4.9, `oracle_sim_card`)
moves to the simulated game, whose winning databases have a collision after `f`
(`dbProperty_collisionGame_subset`). The measured-database bound of CMS19 Lemmas 5.9 and 5.10 with
constant 6, at the per-branch count `b = width · budget + Q · q + width · post + ℓ` of the
composition with the appended queries (`tpQueryCount`, `QueryCount.expandAdv`,
`measured_le_of_queryCount`), and the instability `(b − 1) / c` of collisions after `f`
(`instab_collisionOn_le`) bound that game. `collision_le_add` removes the square roots and
`collision_le_real` states the bound in `ℝ`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

open GordieHowe.QROM GordieHowe.IOP

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {B Z : Type} [Fintype B] [Nonempty B] (e : BitStr I J ≃ B) (f : B → Z)

/-- **The expansion that queries the named points**: query `j` is the `j`-th point of `pts o`, and
`default` past the end of the list. -/
def ptsExpansion {O' : Type} (pts : O' → List (Bits m)) : Expansion (Bits m) B O' where
  next o answers := (pts o).getD answers.length default

omit [Fintype B] [Nonempty B] in
/-- The queries of `ptsExpansion` are the named points, padded with `default`. -/
theorem ptsExpansion_queries {O' : Type} (pts : O' → List (Bits m)) (h : Bits m → B) (o : O')
    {k : ℕ} (i : Fin k) : (ptsExpansion (B := B) pts).queries h o i = (pts o).getD i default := by
  have hr := (ptsExpansion (B := B) pts).run_eq_of_next h (c := o)
    (f := fun j => (pts o).getD j default) (fun i => by simp [ptsExpansion]) k
  simp [Expansion.queries, hr]

/-- **The collision game on the expanded tuple**: two distinct queries in `D` whose answers agree
after `f`. -/
def collisionGame {O' : Type} (D : Set (Bits m)) (k : ℕ) : BaseGame (Bits m) B O' k :=
  {t | ∃ i j, t.queries i ≠ t.queries j ∧ t.queries i ∈ D ∧ t.queries j ∈ D ∧
    f (t.answers i) = f (t.answers j)}

omit [Fintype B] [Nonempty B] in
/-- The databases consistent with a tuple of `collisionGame` have a collision after `f`. -/
theorem dbProperty_collisionGame_subset {O' : Type} (D : Set (Bits m)) (k : ℕ) :
    (collisionGame (O' := O') f D k).dbProperty ⊆ collisionOn f := by
  rintro DB ⟨t, ⟨i, j, hne, -, -, heq⟩, hin⟩
  refine ⟨t.queries i, Finmap.mem_of_lookup_eq_some (hin i), t.queries j,
    Finmap.mem_of_lookup_eq_some (hin j), hne, ?_⟩
  rw [hin i, hin j, Option.map_some, Option.map_some, heq]

/-- **A collision of the random oracle among named points, in an interaction** (CMS19, Chiesa,
Manohar and Spooner, ePrint 2019/834, section 2, after Lemma 2.3: the collision game). For an
adversary with run-time kinds against a challenger, a readout `F` of the composed registers and at
most `ℓ` points `pts o` named by the readout, the probability, averaged over the uniform oracle,
that two distinct named points in `D` have the same image under `f ∘ e` is at most
`(√(6 b² (b − 1) / c) + √(ℓ / |B|))²` with `b = width (budget + post) + Q q + ℓ`, for `c` with
`Pr[y ← B : f y ∈ S] ≤ |S| / c`. -/
theorem collision_le {c : ℝ≥0∞} (hf : ∀ S : Finset Z, Pr[y ← B : f y ∈ S] ≤ S.card / c)
    {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (Ch : Challenger (Bits m) (BitStr I J) Req Resp) {O' : Type} [DecidableEq O']
    (F : A.toKindAlg.CW Ch → O') (D : Set (Bits m)) (ℓ : ℕ) (pts : O' → List (Bits m))
    (hℓ : ∀ o, (pts o).length ≤ ℓ) :
    ∑ H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
        ((A.toKindAlg.composeBothOut Ch F).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, ∃ x ∈ pts v, ∃ x' ∈ pts v, x ∈ D ∧ x' ∈ D ∧ x ≠ x' ∧
            f (e (H x)) = f (e (H x'))} ≤
      (esqrt (6 * ((A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ : ℕ) : ℝ≥0∞) ^ 2 *
          ((A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ - 1 : ℕ) : ℝ≥0∞) / c) +
        esqrt (ℓ / Fintype.card B)) ^ 2 := by
  classical
  set T := A.toTPKindAlg.composeBothOut Ch F
  set b₀ := A.width * A.budget + Ch.Q * Ch.q + A.width * A.post
  have hb : A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ = b₀ + ℓ := by
    simp only [b₀]; ring
  rw [hb]
  set P : O' → (Bits m → B) → Prop := fun v g => ∃ x ∈ pts v, ∃ x' ∈ pts v, x ∈ D ∧ x' ∈ D ∧
    x ≠ x' ∧ f (g x) = f (g x')
  set 𝒜 := T.toQueryAlgCoh.mapOut (·.getD T.defaultOut)
  set X := ptsExpansion (B := B) pts
  set G := collisionGame (O' := O') f D ℓ
  set 𝒜X := expandAdv e X ℓ 𝒜
  -- the sum over oracles is the model's real law
  have hlhs : ∑ H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
        ((A.toKindAlg.composeBothOut Ch F).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, ∃ x ∈ pts v, ∃ x' ∈ pts v, x ∈ D ∧ x' ∈ D ∧ x ≠ x' ∧
            f (e (H x)) = f (e (H x'))} =
      ((A.toKindAlg.composeBothOut Ch F).realLaw e).toOuterMeasure
        {p | ∃ v ∈ p.out, P v p.oracle} := by
    rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  have hO : ((A.toKindAlg.composeBothOut Ch F).realLaw e).toOuterMeasure
      {p | ∃ v ∈ p.out, P v p.oracle} ≤ winO e 𝒜X G := by
    refine (A.realLaw_composeBothOut_le (freeze := false) Ch F e _ fun p hp => by
      obtain ⟨v, hv, _⟩ := hp
      rw [Option.mem_def] at hv; rw [hv]; simp).trans ?_
    refine (T.toOuterMeasure_realLaw_le_coh e T.defaultOut {p | P p.out p.oracle}).trans ?_
    refine winO_expandAdv e X 𝒜 fun p hp => ?_
    obtain ⟨x, hx, x', hx', hD, hD', hne, heq⟩ := hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
    have hqi : X.queries p.oracle p.out (⟨i, hi.trans_le (hℓ _)⟩ : Fin ℓ) = (pts p.out)[i] := by
      rw [ptsExpansion_queries]; simp [hi]
    have hqj : X.queries p.oracle p.out (⟨j, hj.trans_le (hℓ _)⟩ : Fin ℓ) = (pts p.out)[j] := by
      rw [ptsExpansion_queries]; simp [hj]
    refine ⟨⟨i, hi.trans_le (hℓ _)⟩, ⟨j, hj.trans_le (hℓ _)⟩, ?_, ?_, ?_, ?_⟩
    · show X.queries _ _ _ ≠ X.queries _ _ _
      rw [hqi, hqj]; exact hne
    · show X.queries _ _ _ ∈ D
      rw [hqi]; exact hD
    · show X.queries _ _ _ ∈ D
      rw [hqj]; exact hD'
    · show f (p.oracle (X.queries _ _ _)) = f (p.oracle (X.queries _ _ _))
      rw [hqi, hqj]; exact heq
  have hcount := QueryCount.expandAdv ℓ e X (AdaptiveIAlg.tpQueryCount e A Ch F (·.getD T.defaultOut))
  have hD : winS e 𝒜X G ≤ 6 * ((b₀ + ℓ : ℕ) : ℝ≥0∞) ^ 2 * ((b₀ + ℓ - 1 : ℕ) : ℝ≥0∞) / c := by
    refine (winS_le_winD e 𝒜X G).trans ?_
    rw [winD_eq_dbProb]
    refine (dbProb_mono e 𝒜X (dbProperty_collisionGame_subset f D ℓ)).trans ?_
    refine (Lifting.measured_le_of_queryCount e 𝒜X hcount _ (empty_notMem_collisionOn (f := f))).trans ?_
    calc ((b₀ + ℓ : ℕ) : ℝ≥0∞) ^ 2 * 6 * instab (collisionOn f) (b₀ + ℓ)
        ≤ ((b₀ + ℓ : ℕ) : ℝ≥0∞) ^ 2 * 6 * (((b₀ + ℓ - 1 : ℕ) : ℝ≥0∞) / c) := by
          gcongr; exact instab_collisionOn_le hf
      _ = _ := by rw [← mul_div_assoc, mul_comm (_ ^ 2) (6 : ℝ≥0∞)]
  rw [hlhs]
  refine le_sq_of_esqrt_le ((esqrt_le_esqrt hO).trans ?_)
  refine (Lifting.oracle_sim_card e 𝒜X G).trans ?_
  gcongr

/-- `(a + b)² ≤ 2a² + 2b²` in `ℝ≥0∞`. -/
theorem ennreal_add_sq_le_two_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  rw [← ENNReal.coe_add, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
    ← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]

/-- **`collision_le` without square roots**: at most `12 b² (b − 1) / c + 2 ℓ / |B|`. -/
theorem collision_le_add {c : ℝ≥0∞} (hf : ∀ S : Finset Z, Pr[y ← B : f y ∈ S] ≤ S.card / c)
    {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (Ch : Challenger (Bits m) (BitStr I J) Req Resp) {O' : Type} [DecidableEq O']
    (F : A.toKindAlg.CW Ch → O') (D : Set (Bits m)) (ℓ : ℕ) (pts : O' → List (Bits m))
    (hℓ : ∀ o, (pts o).length ≤ ℓ) :
    ∑ H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
        ((A.toKindAlg.composeBothOut Ch F).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, ∃ x ∈ pts v, ∃ x' ∈ pts v, x ∈ D ∧ x' ∈ D ∧ x ≠ x' ∧
            f (e (H x)) = f (e (H x'))} ≤
      12 * ((A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ : ℕ) : ℝ≥0∞) ^ 2 *
          ((A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ - 1 : ℕ) : ℝ≥0∞) / c +
        2 * ℓ / Fintype.card B := by
  refine (collision_le e f hf A Ch F D ℓ pts hℓ).trans ((ennreal_add_sq_le_two_mul _ _).trans_eq ?_)
  rw [esqrt_sq, esqrt_sq]
  simp only [div_eq_mul_inv]
  ring

/-- **`collision_le_add` in `ℝ`**, for `c > 0`: the real probability, averaged over the uniform
oracle, is at most `12 b² (b − 1) / c + 2 ℓ / |B|`. -/
theorem collision_le_real {c : ℝ} (hc : 0 < c)
    (hf : ∀ S : Finset Z, Pr[y ← B : f y ∈ S] ≤ S.card / ENNReal.ofReal c)
    {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (Ch : Challenger (Bits m) (BitStr I J) Req Resp) {O' : Type} [DecidableEq O']
    (F : A.toKindAlg.CW Ch → O') (D : Set (Bits m)) (ℓ : ℕ) (pts : O' → List (Bits m))
    (hℓ : ∀ o, (pts o).length ≤ ℓ) :
    ∑ H, (PMF.uniformOfFintype (Bits m → BitStr I J) H).toReal *
        (((A.toKindAlg.composeBothOut Ch F).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, ∃ x ∈ pts v, ∃ x' ∈ pts v, x ∈ D ∧ x' ∈ D ∧ x ≠ x' ∧
            f (e (H x)) = f (e (H x'))}).toReal ≤
      12 * ((A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ : ℕ) : ℝ) ^ 2 *
          ((A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ - 1 : ℕ) : ℝ) / c +
        2 * ℓ / Fintype.card B := by
  have h := collision_le_add e f hf A Ch F D ℓ pts hℓ
  have hc' : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hc
  have hB : (Fintype.card B : ℝ≥0∞) ≠ 0 := by simp
  have hfin : 12 * ((A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ : ℕ) : ℝ≥0∞) ^ 2 *
          ((A.width * (A.budget + A.post) + Ch.Q * Ch.q + ℓ - 1 : ℕ) : ℝ≥0∞) / ENNReal.ofReal c +
        2 * ℓ / Fintype.card B ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (by finiteness) hc',
      ENNReal.div_ne_top (by finiteness) hB⟩
  have hreal := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_sum fun H _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    ((PMF.toOuterMeasure_apply_le_one _ _).trans_lt ENNReal.one_lt_top).ne] at hreal
  simp only [ENNReal.toReal_mul] at hreal
  refine hreal.trans_eq ?_
  rw [ENNReal.toReal_add (ENNReal.div_ne_top (by finiteness) hc')
    (ENNReal.div_ne_top (by finiteness) hB)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hc.le]

end AdaptiveIAlg

end GordieHowe.Quantum
