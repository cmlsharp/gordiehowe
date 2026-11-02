-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Anonymity
public import GordieHowe.Model.RingSignature.Transcript
public import GordieHowe.Model.Quantum.Interactive.SaltReprogram

@[expose] public section

/-!
# Reprogramming at hidden fresh salts in the ring-signature games

The game-level form of `GordieHowe/Model/Quantum/Interactive/SaltReprogram.lean`, for the
adversaries of `GordieHowe/Model/RingSignature/Adversary.lean` (`Quantum.QueryBoundedAdversary`,
`GameAdversary`). A challenger `C₀` reads the random oracle at hidden fresh salts and `C₁` reads
fresh functions in their place (`Challenger.SaltFreshPair`: the salts `ρ ← ν`, an injective
embedding `emb : S × U → X` of the salted inputs into the oracle's domain, the other reads of the
oracle outside the range of `emb`). Against them:

- `QueryBoundedAdversary.sum_transcriptLaw_out_mem`: through
  `QueryBoundedAdversary.transcriptLaw_out_mem` (`GordieHowe/Model/RingSignature/Transcript.lean`),
  the probability of an event of the adversary's output, averaged over an oracle law, is the
  average over the auxiliary input of the output `true` of the adversary with the event as its
  output.
- `QueryBoundedAdversary.advantage_salt_fresh_le_of_law`: for an oracle law uniform on the range
  of `emb` given the rest, a `t`-query adversary's output lies in `E` against `C₀` and against `C₁`
  with probabilities at most `Pr[two salts collide] + 2 t √ε` apart, for `ε` bounding the
  probability that a given point of `S` is a salt.
- `QueryBoundedAdversary.advantage_salt_fresh_le`: the same for the uniform oracle and an
  adversary chosen from the oracle's values outside the range of `emb` (such as a table of them,
  `OracleView.view_eq_of_agreeOffRange`), by conditioning on those values
  (`sum_uniform_eq_sum_offRangeLaw`, `advantage_sum_uniform_le`, `toReal_bind_uniform`).
- `RingSignature.gameAdvantage_runLaw_salt_fresh_le`: the bound for the run of a game
  (`runLaw`), with start draws, for the events of the adversary's output (`RunOutIn E`,
  `toOuterMeasure_runLaw_runOutIn`).
  `RingSignature.gameAdvantage_runLaw_le_of_saltFresh`: the advantage between two runs against
  salted challengers is at most that between their fresh counterparts plus twice the bound.
- `RingSignature.anonAdvantage_le_of_saltFresh`: the anonymity advantage is at most the
  advantage between the two fresh counterparts of the experiments plus twice the bound.
- `RingSignature.gameAdvantage_runLaw_salt_fresh_le_of_pi`,
  `RingSignature.anonAdvantage_le_of_saltFresh_of_pi`: for independent salts with point
  probabilities at most `δ` (min-entropy `κ`, `δ = 2^{-κ}`), the bound is
  `C(K, 2) δ + 2 t √(K δ)`.

For a split `e : Y ≃ Y₁ × Y₂` of the oracle's values, with challengers reading only the first
components at the salts (`Challenger.SaltFreshPairOn`) and adversaries and tables that agree on
oracles related by `AgreeOffRangeOn` (equal outside the range of `emb` and in the second
components everywhere): `QueryBoundedAdversary.advantage_saltOn_fresh_le_of_law`,
`QueryBoundedAdversary.advantage_sum_uniform_le_of_offRangeLawOn`,
`QueryBoundedAdversary.advantage_saltOn_fresh_le` (conditioning on `offRangeLawOn`),
`OracleView.view_eq_of_agreeOffRangeOn`, `RingSignature.gameAdvantage_runLaw_saltOn_fresh_le`,
`RingSignature.gameAdvantage_runLaw_le_of_saltFreshOn`,
`RingSignature.anonAdvantage_le_of_saltFreshOn`,
`RingSignature.gameAdvantage_runLaw_saltOn_fresh_le_of_pi`,
`RingSignature.anonAdvantage_le_of_saltFreshOn_of_pi`, with the same bounds. Each statement
without a split above is derived from its counterpart at `wholeSplit Y` (`SaltFreshPair.toOn`).
-/

namespace GordieHowe

open GordieHowe.Quantum
open scoped ENNReal

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

namespace Quantum.QueryBoundedAdversary

variable {S U : Type} [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U] {K : ℕ}
  {emb : S × U → X} {ν : PMF (Fin K → S)} {C₀ C₁ : Challenger X Y Req Resp}
  {Y₁ Y₂ : Type} [Fintype Y₁] [Nonempty Y₁] {e : Y ≃ Y₁ × Y₂}

open Classical in
/-- The probability that the output lies in `E`, averaged over the oracle law `μH`, as one
average over the auxiliary input. -/
theorem sum_transcriptLaw_out_mem (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (μH : PMF (X → Y)) (E : Set O) :
    ∑ H, (μH H).toReal * ((𝒜.transcriptLaw C H).toOuterMeasure (OutIn E)).toReal =
      (∑' a, 𝒜.aux a * ∑ H, μH H * (((𝒜.alg a).mapOut fun o => decide (o ∈ E)).compose
        C).outLaw H (some true)).toReal := by
  have hfin : ∀ H, μH H * (𝒜.transcriptLaw C H).toOuterMeasure (OutIn E) ≠ ⊤ := fun H =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _))
  simp only [← ENNReal.toReal_mul]
  rw [← ENNReal.toReal_sum fun H _ => hfin H]
  congr 1
  simp only [transcriptLaw_out_mem, ← ENNReal.tsum_mul_left]
  rw [← tsum_fintype (L := .unconditional _), ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun H _ => by ring

/-- **Reprogramming the first components at hidden fresh salts against a `t`-query
adversary**, for a split `e : Y ≃ Y₁ × Y₂` and an oracle law `μH` uniform in the first components
on the range of the injective embedding `emb` given the rest (`IsUniformOnRangeOn`): the
adversary's output lies in `E` against the salted challenger `C₀` and against its fresh
counterpart `C₁` (`Challenger.SaltFreshPairOn`) with probabilities at most
`Pr[two salts collide] + 2 t √ε` apart, for `ε` bounding the probability that a given point
of `S` is a salt. -/
theorem advantage_saltOn_fresh_le_of_law (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (P : C₀.SaltFreshPairOn emb e ν C₁) (hemb : Function.Injective emb) {μH : PMF (X → Y)}
    (hμH : IsUniformOnRangeOn emb e μH) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Set O) :
    GordieHowe.advantage
      (∑ H, (μH H).toReal * ((𝒜.transcriptLaw C₀ H).toOuterMeasure (OutIn E)).toReal)
      (∑ H, (μH H).toReal * ((𝒜.transcriptLaw C₁ H).toOuterMeasure (OutIn E)).toReal) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε := by
  classical
  rw [sum_transcriptLaw_out_mem, sum_transcriptLaw_out_mem]
  have hle : ∀ (C : Challenger X Y Req Resp) a, ∑ H, μH H *
      (((𝒜.alg a).mapOut fun o => decide (o ∈ E)).compose C).outLaw H (some true) ≤ 1 :=
    fun C a => by
      calc ∑ H, μH H * (((𝒜.alg a).mapOut fun o => decide (o ∈ E)).compose C).outLaw H
            (some true) ≤ ∑ H, μH H * 1 :=
            Finset.sum_le_sum fun H _ => mul_le_mul_right (PMF.coe_le_one _ _) _
        _ = 1 := by
          simp only [mul_one]
          rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  refine PMF.abs_toReal_tsum_mul_sub_le 𝒜.aux (hle C₀) (hle C₁) fun a => ?_
  set B := (𝒜.alg a).mapOut fun o => decide (o ∈ E)
  have hreal : ∀ C : Challenger X Y Req Resp, (∑ H, μH H * (B.compose C).outLaw H (some true)).toReal =
      ∑ H, (μH H).toReal * ((B.compose C).outLaw H (some true)).toReal := fun C => by
    rw [ENNReal.toReal_sum fun H _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)]
    simp only [ENNReal.toReal_mul]
  rw [hreal, hreal]
  exact B.advantage_saltOn_fresh_le_of_queries_le P hemb hμH hε true (𝒜.queries_le a)

/-- **Reprogramming at hidden fresh salts against a `t`-query adversary**, for an oracle law
`μH` uniform on the range of the injective embedding `emb` given the rest: the adversary's output
lies in `E` against the salted challenger `C₀` and against its fresh counterpart `C₁`
(`Challenger.SaltFreshPair`) with probabilities at most `Pr[two salts collide] + 2 t √ε` apart,
for `ε` bounding the probability that a given point of `S` is a salt
(`advantage_saltOn_fresh_le_of_law` at the split with a trivial second component). -/
theorem advantage_salt_fresh_le_of_law (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (P : C₀.SaltFreshPair emb ν C₁) (hemb : Function.Injective emb) {μH : PMF (X → Y)}
    (hμH : IsUniformOnRange emb μH) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Set O) :
    GordieHowe.advantage
      (∑ H, (μH H).toReal * ((𝒜.transcriptLaw C₀ H).toOuterMeasure (OutIn E)).toReal)
      (∑ H, (μH H).toReal * ((𝒜.transcriptLaw C₁ H).toOuterMeasure (OutIn E)).toReal) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε :=
  advantage_saltOn_fresh_le_of_law 𝒜 P.toOn hemb hμH.isUniformOnRangeOn hε E

omit [DecidableEq Y] [Nonempty X] [AddGroup Y] [Fintype S] [DecidableEq S] [Fintype U]
  [DecidableEq U] [Fintype Y₁] [Nonempty Y₁] in
/-- **Averages over the uniform oracle within a bound, by classes of `AgreeOffRangeOn`**: if for
every `H₀` the averages over the oracles agreeing with `H₀` off the range and in the second
components are within `b`, so are the averages over the uniform oracle. -/
theorem advantage_sum_uniform_le_of_offRangeLawOn {f₀ f₁ : (X → Y) → ℝ} {b : ℝ}
    (h : ∀ H₀, |∑ H, (offRangeLawOn emb e H₀ H).toReal * f₀ H -
      ∑ H, (offRangeLawOn emb e H₀ H).toReal * f₁ H| ≤ b) :
    GordieHowe.advantage (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * f₀ H)
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * f₁ H) ≤ b := by
  rw [GordieHowe.advantage, sum_uniform_eq_sum_offRangeLawOn (emb := emb) (e := e) f₀,
    sum_uniform_eq_sum_offRangeLawOn (emb := emb) (e := e) f₁, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ H₀, |(PMF.uniformOfFintype (X → Y) H₀).toReal *
          ∑ H, (offRangeLawOn emb e H₀ H).toReal * f₀ H -
        (PMF.uniformOfFintype (X → Y) H₀).toReal * ∑ H, (offRangeLawOn emb e H₀ H).toReal * f₁ H|
      ≤ ∑ H₀, (PMF.uniformOfFintype (X → Y) H₀).toReal * b :=
        Finset.sum_le_sum fun H₀ _ => by
          rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_mul_of_nonneg_left (h H₀) ENNReal.toReal_nonneg
    _ = b := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

omit [DecidableEq Y] [Nonempty X] [AddGroup Y] [Fintype S] [DecidableEq S] [Fintype U]
  [DecidableEq U] in
/-- **Averages over the uniform oracle within a bound**: if for every `H₀` the averages over the
oracles agreeing with `H₀` off the range are within `b`, so are the averages over the uniform
oracle. -/
theorem advantage_sum_uniform_le {f₀ f₁ : (X → Y) → ℝ} {b : ℝ}
    (h : ∀ H₀, |∑ H, (offRangeLaw emb H₀ H).toReal * f₀ H -
      ∑ H, (offRangeLaw emb H₀ H).toReal * f₁ H| ≤ b) :
    GordieHowe.advantage (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * f₀ H)
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * f₁ H) ≤ b := by
  simp only [offRangeLaw_eq_offRangeLawOn] at h
  exact advantage_sum_uniform_le_of_offRangeLawOn h

/-- The probability of an event of the transcript with the oracle uniform, as an average. -/
theorem toReal_bind_uniform (𝒜 : (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (W : Set (Option (O × List (HistoryEntry Req Resp)))) :
    (((PMF.uniformOfFintype (X → Y)).bind fun H => (𝒜 H).transcriptLaw C H).toOuterMeasure
      W).toReal = ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((𝒜 H).transcriptLaw C H).toOuterMeasure W).toReal := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum fun H _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _))]
  simp only [ENNReal.toReal_mul]

/-- **Reprogramming the first components at hidden fresh salts against a `t`-query adversary
that reads the oracle's first components off the salted inputs**: the oracle uniform, a split
`e : Y ≃ Y₁ × Y₂`, and the adversary `𝒜 H` chosen from the oracle's values outside the range of
the injective embedding `emb` and its second components everywhere (for example from a table of
them). Its output lies in `E` against the salted challenger `C₀` and against its fresh
counterpart `C₁` (`Challenger.SaltFreshPairOn`) with probabilities at most
`Pr[two salts collide] + 2 t √ε` apart, for `ε` bounding the probability that a given point
of `S` is a salt. The proof conditions on the oracle's values outside the range and the second
components (`sum_uniform_eq_sum_offRangeLawOn`), under which the adversary is fixed and the
oracle law is uniform in the first components on the range
(`advantage_saltOn_fresh_le_of_law`). -/
theorem advantage_saltOn_fresh_le (𝒜 : (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (h𝒜 : ∀ H H', AgreeOffRangeOn emb e H H' → 𝒜 H = 𝒜 H') (P : C₀.SaltFreshPairOn emb e ν C₁)
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Set O) :
    GordieHowe.advantage
      (((PMF.uniformOfFintype (X → Y)).bind fun H => (𝒜 H).transcriptLaw C₀ H).toOuterMeasure
        (OutIn E)).toReal
      (((PMF.uniformOfFintype (X → Y)).bind fun H => (𝒜 H).transcriptLaw C₁ H).toOuterMeasure
        (OutIn E)).toReal ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε := by
  rw [toReal_bind_uniform, toReal_bind_uniform]
  refine advantage_sum_uniform_le_of_offRangeLawOn (emb := emb) (e := e) fun H₀ => ?_
  have hfix : ∀ C : Challenger X Y Req Resp, ∑ H, (offRangeLawOn emb e H₀ H).toReal *
      (((𝒜 H).transcriptLaw C H).toOuterMeasure (OutIn E)).toReal =
      ∑ H, (offRangeLawOn emb e H₀ H).toReal *
        (((𝒜 H₀).transcriptLaw C H).toOuterMeasure (OutIn E)).toReal := fun C =>
    Finset.sum_congr rfl fun H _ => by
      by_cases h0 : offRangeLawOn emb e H₀ H = 0
      · simp [h0]
      · rw [h𝒜 H H₀ (agreeOffRangeOn_of_offRangeLawOn_ne_zero h0)]
  rw [hfix, hfix]
  exact advantage_saltOn_fresh_le_of_law (𝒜 H₀) P hemb (isUniformOnRangeOn_offRangeLawOn H₀) hε E

/-- **Reprogramming at hidden fresh salts against a `t`-query adversary that reads the oracle
off the salted inputs**: the oracle uniform, and the adversary `𝒜 H` chosen from the oracle's
values outside the range of the injective embedding `emb` (for example from a table of them).
Its output lies in `E` against the salted challenger `C₀` and against its fresh counterpart `C₁`
(`Challenger.SaltFreshPair`) with probabilities at most `Pr[two salts collide] + 2 t √ε` apart,
for `ε` bounding the probability that a given point of `S` is a salt. The proof conditions on
the oracle's values outside the range (`sum_uniform_eq_sum_offRangeLaw`), under which the
adversary is fixed and the oracle law is uniform on the range
(`advantage_salt_fresh_le_of_law`); `advantage_saltOn_fresh_le` at the split with a trivial second
component. -/
theorem advantage_salt_fresh_le (𝒜 : (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (h𝒜 : ∀ H H', AgreeOffRange emb H H' → 𝒜 H = 𝒜 H') (P : C₀.SaltFreshPair emb ν C₁)
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Set O) :
    GordieHowe.advantage
      (((PMF.uniformOfFintype (X → Y)).bind fun H => (𝒜 H).transcriptLaw C₀ H).toOuterMeasure
        (OutIn E)).toReal
      (((PMF.uniformOfFintype (X → Y)).bind fun H => (𝒜 H).transcriptLaw C₁ H).toOuterMeasure
        (OutIn E)).toReal ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε :=
  advantage_saltOn_fresh_le 𝒜 (fun H H' h => h𝒜 H H' h.1) P.toOn hemb hε E

end Quantum.QueryBoundedAdversary

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X] [AddGroup Y]
  [Nonempty Y] in
/-- **A table of the oracle off the salted inputs is read off the range**: for a table on the
points satisfying `P`, none of them in the range of the embedding, two oracles that agree outside
the range have the same table. -/
theorem RingSignature.OracleView.view_eq_of_agreeOffRange {S U : Type} {emb : S × U → X}
    {P : X → Prop} (hP : ∀ x, P x → x ∉ Set.range emb) {H H' : X → Y}
    (h : AgreeOffRange emb H H') :
    (RingSignature.OracleView.tableOn Y P).view H = (RingSignature.OracleView.tableOn Y P).view H' :=
  funext fun x => h x.1 (hP x.1 x.2)

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X] [AddGroup Y]
  [Nonempty Y] in
/-- **A table of the oracle off the salted inputs is read off the range and the second
components**: `view_eq_of_agreeOffRange` for oracles related by `AgreeOffRangeOn`. -/
theorem RingSignature.OracleView.view_eq_of_agreeOffRangeOn {S U Y₁ Y₂ : Type}
    {emb : S × U → X} {e : Y ≃ Y₁ × Y₂} {P : X → Prop} (hP : ∀ x, P x → x ∉ Set.range emb)
    {H H' : X → Y} (h : AgreeOffRangeOn emb e H H') :
    (RingSignature.OracleView.tableOn Y P).view H =
      (RingSignature.OracleView.tableOn Y P).view H' :=
  view_eq_of_agreeOffRange hP h.1

namespace RingSignature

open Quantum.QueryBoundedAdversary

variable {S U : Type} [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U] {K : ℕ}
  {emb : S × U → X} {ν : PMF (Fin K → S)}
  {Y₁ Y₂ : Type} [Fintype Y₁] [Nonempty Y₁] {e : Y ≃ Y₁ × Y₂}

/-- An output event of the run is the average over the start draws of the output event under
the transcript law with the oracle uniform. -/
theorem toOuterMeasure_runLaw_runOutIn {Start : Type} [Fintype Start] [Nonempty Start]
    (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C : Start → Challenger X Y Req Resp) (E : Set O) :
    (runLaw A C).toOuterMeasure (RunOutIn E) =
      ∑' k, PMF.uniformOfFintype Start k *
        ((PMF.uniformOfFintype (X → Y)).bind fun H => (A k H).transcriptLaw (C k) H).toOuterMeasure
          (OutIn E) := by
  rw [runLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun k => ?_
  congr 1
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => ?_
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- **Reprogramming the first components at hidden fresh salts in a game's run**: for a split
`e : Y ≃ Y₁ × Y₂`, with start draws `k`, the adversary `A k H` chosen from the start draws, the
oracle's values outside the range of the injective embedding `emb` and its second components
everywhere, and for every `k` a salted challenger `C₀ k` reading first components with its fresh
counterpart `C₁ k` (`Challenger.SaltFreshPairOn`, salts `ρ ← ν`), the probabilities that the
adversary's output lies in `E` in the two runs are at most `Pr[two salts collide] + 2 t √ε`
apart, for `ε` bounding the probability that a given point of `S` is a salt. -/
theorem gameAdvantage_runLaw_saltOn_fresh_le {Start : Type} [Fintype Start] [Nonempty Start]
    (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRangeOn emb e H H' → A k H = A k H')
    {C₀ C₁ : Start → Challenger X Y Req Resp} (P : ∀ k, (C₀ k).SaltFreshPairOn emb e ν (C₁ k))
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Set O) :
    gameAdvantage (runLaw A C₀) (runLaw A C₁) (RunOutIn E) ≤
      (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε := by
  rw [gameAdvantage]
  change |((runLaw A C₀).toOuterMeasure (RunOutIn E)).toReal -
    ((runLaw A C₁).toOuterMeasure (RunOutIn E)).toReal| ≤ _
  rw [toOuterMeasure_runLaw_runOutIn, toOuterMeasure_runLaw_runOutIn]
  exact PMF.abs_toReal_tsum_mul_sub_le _ (fun _ => PMF.toOuterMeasure_apply_le_one _ _)
    (fun _ => PMF.toOuterMeasure_apply_le_one _ _) fun k =>
      advantage_saltOn_fresh_le (A k) (hA k) (P k) hemb hε E

/-- **Reprogramming at hidden fresh salts in a game's run**: with start draws `k`, the
adversary `A k H` chosen from the start draws and the oracle's values outside the range of the
injective embedding `emb` (for a `GameAdversary`, from its start input), and for every `k` a
salted challenger `C₀ k` with its fresh counterpart `C₁ k` (`Challenger.SaltFreshPair`, salts
`ρ ← ν`), the probabilities that the adversary's output lies in `E` in the two runs are at most
`Pr[two salts collide] + 2 t √ε` apart, for `ε` bounding the probability that a given point of `S`
is a salt (`gameAdvantage_runLaw_saltOn_fresh_le` at the split with a trivial second
component). -/
theorem gameAdvantage_runLaw_salt_fresh_le {Start : Type} [Fintype Start] [Nonempty Start]
    (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRange emb H H' → A k H = A k H')
    {C₀ C₁ : Start → Challenger X Y Req Resp} (P : ∀ k, (C₀ k).SaltFreshPair emb ν (C₁ k))
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Set O) :
    gameAdvantage (runLaw A C₀) (runLaw A C₁) (RunOutIn E) ≤
      (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε :=
  gameAdvantage_runLaw_saltOn_fresh_le A (fun k H H' h => hA k H H' h.1) (fun k => (P k).toOn)
    hemb hε E

/-- **Two experiments through their fresh counterparts, for first components**: the advantage
between the runs against the salted challengers `C₀` and `C₀'` reading first components is at
most the advantage between the runs against their fresh counterparts `C₁` and `C₁'` plus twice
`Pr[two salts collide] + 2 t √ε`. -/
theorem gameAdvantage_runLaw_le_of_saltFreshOn {Start : Type} [Fintype Start] [Nonempty Start]
    (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRangeOn emb e H H' → A k H = A k H')
    {C₀ C₁ C₀' C₁' : Start → Challenger X Y Req Resp}
    (P : ∀ k, (C₀ k).SaltFreshPairOn emb e ν (C₁ k))
    (P' : ∀ k, (C₀' k).SaltFreshPairOn emb e ν (C₁' k))
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Set O) :
    gameAdvantage (runLaw A C₀) (runLaw A C₀') (RunOutIn E) ≤
      gameAdvantage (runLaw A C₁) (runLaw A C₁') (RunOutIn E) +
        2 * ((ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε) := by
  have h₀ := gameAdvantage_runLaw_saltOn_fresh_le A hA P hemb hε E
  have h₁ := gameAdvantage_runLaw_saltOn_fresh_le A hA P' hemb hε E
  rw [gameAdvantage] at h₀ h₁ ⊢
  rw [gameAdvantage]
  refine (advantage_le_add _ (Pr[x ~ runLaw A C₁ : x ∈ RunOutIn E]).toReal _).trans ?_
  refine (add_le_add le_rfl (advantage_le_add _
    (Pr[x ~ runLaw A C₁' : x ∈ RunOutIn E]).toReal _)).trans ?_
  rw [advantage_comm (Pr[x ~ runLaw A C₁' : x ∈ RunOutIn E]).toReal] at *
  linarith [advantage_comm (Pr[x ~ runLaw A C₀' : x ∈ RunOutIn E]).toReal
    (Pr[x ~ runLaw A C₁' : x ∈ RunOutIn E]).toReal]

/-- **Two experiments through their fresh counterparts**: the advantage between the runs against
the salted challengers `C₀` and `C₀'` is at most the advantage between the runs against their
fresh counterparts `C₁` and `C₁'` plus twice `Pr[two salts collide] + 2 t √ε`
(`gameAdvantage_runLaw_le_of_saltFreshOn` at the split with a trivial second component). -/
theorem gameAdvantage_runLaw_le_of_saltFresh {Start : Type} [Fintype Start] [Nonempty Start]
    (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRange emb H H' → A k H = A k H')
    {C₀ C₁ C₀' C₁' : Start → Challenger X Y Req Resp}
    (P : ∀ k, (C₀ k).SaltFreshPair emb ν (C₁ k)) (P' : ∀ k, (C₀' k).SaltFreshPair emb ν (C₁' k))
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Set O) :
    gameAdvantage (runLaw A C₀) (runLaw A C₀') (RunOutIn E) ≤
      gameAdvantage (runLaw A C₁) (runLaw A C₁') (RunOutIn E) +
        2 * ((ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε) :=
  gameAdvantage_runLaw_le_of_saltFreshOn A (fun k H H' h => hA k H H' h.1)
    (fun k => (P k).toOn) (fun k => (P' k).toOn) hemb hε E

/-- **Anonymity through the fresh counterparts of the experiments, for first components**: for
a split `e : Y ≃ Y₁ × Y₂`, a table `V` of the oracle that agrees on oracles related by
`AgreeOffRangeOn` (equal outside the range of the injective embedding `emb` and equal in their
second components everywhere), and for every bit `b` and all users' key coins a fresh
counterpart `C₁ b keys` of the anonymity challenger of experiment `b`
(`Challenger.SaltFreshPairOn`, salts `ρ ← ν`), the anonymity advantage of every `t`-query
adversary with `Q` challenges is at most the advantage between the runs against the two fresh
counterparts plus twice `Pr[two salts collide] + 2 t √ε`. -/
theorem anonAdvantage_le_of_saltFreshOn {N : ℕ} {TS' : RingTypes} {S' : RingScheme X Y N TS'} {n : ℕ}
    {V : OracleView X Y} (hV : ∀ H H', AgreeOffRangeOn emb e H H' → V.view H = V.view H')
    (A : AnonAdversary S' n V t) (Q : ℕ)
    {C₁ : Bool → (Fin n → S'.KeyCoins) → Challenger X Y (AnonRequest S' n) S'.Sig}
    (P : ∀ b keys, (anonChallenger S' n keys b Q).SaltFreshPairOn emb e ν (C₁ b keys))
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) :
    anonAdvantage A Q ≤
      gameAdvantage (runLaw (fun keys H => A (keys, V.view H)) (C₁ false))
        (runLaw (fun keys H => A (keys, V.view H)) (C₁ true)) anonAccepts +
        2 * ((ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε) := by
  have hacc : (anonAccepts : Set ((Fin n → S'.KeyCoins) × (X → Y) ×
      Option (Bool × List (HistoryEntry (AnonRequest S' n) S'.Sig)))) = RunOutIn {true} := by
    ext x
    simp [anonAccepts, RunOutIn]
  rw [anonAdvantage, anonLaw, anonLaw, hacc]
  exact gameAdvantage_runLaw_le_of_saltFreshOn _ (fun keys H H' h => by rw [hV H H' h])
    (P false) (P true) hemb hε {true}

/-- **Anonymity through the fresh counterparts of the experiments**: for a table `V` of the oracle
read off the range of the injective embedding `emb`, and for every bit `b` and all users' key
coins a fresh counterpart `C₁ b keys` of the anonymity challenger of experiment `b`
(`Challenger.SaltFreshPair`, salts `ρ ← ν`), the anonymity advantage of every `t`-query adversary
with `Q` challenges is at most the advantage between the runs against the two fresh counterparts
plus twice `Pr[two salts collide] + 2 t √ε` (`anonAdvantage_le_of_saltFreshOn` at the split with
a trivial second component). -/
theorem anonAdvantage_le_of_saltFresh {N : ℕ} {TS' : RingTypes} {S' : RingScheme X Y N TS'} {n : ℕ}
    {V : OracleView X Y} (hV : ∀ H H', AgreeOffRange emb H H' → V.view H = V.view H')
    (A : AnonAdversary S' n V t) (Q : ℕ)
    {C₁ : Bool → (Fin n → S'.KeyCoins) → Challenger X Y (AnonRequest S' n) S'.Sig}
    (P : ∀ b keys, (anonChallenger S' n keys b Q).SaltFreshPair emb ν (C₁ b keys))
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) :
    anonAdvantage A Q ≤
      gameAdvantage (runLaw (fun keys H => A (keys, V.view H)) (C₁ false))
        (runLaw (fun keys H => A (keys, V.view H)) (C₁ true)) anonAccepts +
        2 * ((ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε) :=
  anonAdvantage_le_of_saltFreshOn (e := wholeSplit Y) (fun H H' h => hV H H' h.1) A Q
    (fun b keys => (P b keys).toOn) hemb hε

/-- **`gameAdvantage_runLaw_saltOn_fresh_le` for independent salts of min-entropy `κ`**: for
salts drawn independently with point probabilities at most `δ` (`δ = 2^{-κ}`), the bound is
`C(K, 2) δ + 2 t √(K δ)`. -/
theorem gameAdvantage_runLaw_saltOn_fresh_le_of_pi {Start : Type} [Fintype Start]
    [Nonempty Start] (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRangeOn emb e H H' → A k H = A k H') {p : Fin K → PMF S}
    {C₀ C₁ : Start → Challenger X Y Req Resp}
    (P : ∀ k, (C₀ k).SaltFreshPairOn emb e (PMF.pi p) (C₁ k))
    (hemb : Function.Injective emb) {δ : ℝ} (hδ : ∀ i s, (p i s).toReal ≤ δ) (E : Set O) :
    gameAdvantage (runLaw A C₀) (runLaw A C₁) (RunOutIn E) ≤
      K.choose 2 * δ + 2 * t * √(K * δ) :=
  (gameAdvantage_runLaw_saltOn_fresh_le A hA P hemb (toReal_pi_exists_eq_le p hδ) E).trans
    (add_le_add (toReal_pi_not_injective_le p hδ) le_rfl)

/-- **`gameAdvantage_runLaw_salt_fresh_le` for independent salts of min-entropy `κ`**: for salts
drawn independently with point probabilities at most `δ` (`δ = 2^{-κ}`), the bound is
`C(K, 2) δ + 2 t √(K δ)`. -/
theorem gameAdvantage_runLaw_salt_fresh_le_of_pi {Start : Type} [Fintype Start]
    [Nonempty Start] (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRange emb H H' → A k H = A k H') {p : Fin K → PMF S}
    {C₀ C₁ : Start → Challenger X Y Req Resp} (P : ∀ k, (C₀ k).SaltFreshPair emb (PMF.pi p) (C₁ k))
    (hemb : Function.Injective emb) {δ : ℝ} (hδ : ∀ i s, (p i s).toReal ≤ δ) (E : Set O) :
    gameAdvantage (runLaw A C₀) (runLaw A C₁) (RunOutIn E) ≤
      K.choose 2 * δ + 2 * t * √(K * δ) :=
  gameAdvantage_runLaw_saltOn_fresh_le_of_pi A (fun k H H' h => hA k H H' h.1)
    (fun k => (P k).toOn) hemb hδ E

/-- **`anonAdvantage_le_of_saltFreshOn` for independent salts of min-entropy `κ`**: for salts
drawn independently with point probabilities at most `δ` (`δ = 2^{-κ}`), the anonymity advantage
is at most the advantage between the runs against the two fresh counterparts plus
`2 (C(K, 2) δ + 2 t √(K δ))`. -/
theorem anonAdvantage_le_of_saltFreshOn_of_pi {N : ℕ} {TS' : RingTypes} {S' : RingScheme X Y N TS'} {n : ℕ}
    {V : OracleView X Y} (hV : ∀ H H', AgreeOffRangeOn emb e H H' → V.view H = V.view H')
    (A : AnonAdversary S' n V t) (Q : ℕ) {p : Fin K → PMF S}
    {C₁ : Bool → (Fin n → S'.KeyCoins) → Challenger X Y (AnonRequest S' n) S'.Sig}
    (P : ∀ b keys, (anonChallenger S' n keys b Q).SaltFreshPairOn emb e (PMF.pi p) (C₁ b keys))
    (hemb : Function.Injective emb) {δ : ℝ} (hδ : ∀ i s, (p i s).toReal ≤ δ) :
    anonAdvantage A Q ≤
      gameAdvantage (runLaw (fun keys H => A (keys, V.view H)) (C₁ false))
        (runLaw (fun keys H => A (keys, V.view H)) (C₁ true)) anonAccepts +
        2 * (K.choose 2 * δ + 2 * t * √(K * δ)) := by
  refine (anonAdvantage_le_of_saltFreshOn hV A Q P hemb (toReal_pi_exists_eq_le p hδ)).trans ?_
  have h := toReal_pi_not_injective_le p hδ
  linarith

/-- **`anonAdvantage_le_of_saltFresh` for independent salts of min-entropy `κ`**: for salts drawn
independently with point probabilities at most `δ` (`δ = 2^{-κ}`), the anonymity advantage is at
most the advantage between the runs against the two fresh counterparts plus
`2 (C(K, 2) δ + 2 t √(K δ))`. -/
theorem anonAdvantage_le_of_saltFresh_of_pi {N : ℕ} {TS' : RingTypes} {S' : RingScheme X Y N TS'} {n : ℕ}
    {V : OracleView X Y} (hV : ∀ H H', AgreeOffRange emb H H' → V.view H = V.view H')
    (A : AnonAdversary S' n V t) (Q : ℕ) {p : Fin K → PMF S}
    {C₁ : Bool → (Fin n → S'.KeyCoins) → Challenger X Y (AnonRequest S' n) S'.Sig}
    (P : ∀ b keys, (anonChallenger S' n keys b Q).SaltFreshPair emb (PMF.pi p) (C₁ b keys))
    (hemb : Function.Injective emb) {δ : ℝ} (hδ : ∀ i s, (p i s).toReal ≤ δ) :
    anonAdvantage A Q ≤
      gameAdvantage (runLaw (fun keys H => A (keys, V.view H)) (C₁ false))
        (runLaw (fun keys H => A (keys, V.view H)) (C₁ true)) anonAccepts +
        2 * (K.choose 2 * δ + 2 * t * √(K * δ)) :=
  anonAdvantage_le_of_saltFreshOn_of_pi (e := wholeSplit Y) (fun H H' h => hV H H' h.1) A Q
    (fun b keys => (P b keys).toOn) hemb hδ

end RingSignature

end GordieHowe
