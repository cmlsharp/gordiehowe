-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RevealedReprogram
public import GordieHowe.Model.RingSignature.SaltReprogram

@[expose] public section

/-!
# Adaptive reprogramming at revealed points in the ring-signature games

The game-level form of `GordieHowe/Model/Quantum/Interactive/RevealedReprogram.lean`: adaptive
reprogramming at points revealed to the adversary (Grilo, Hövelmanns, Hülsing, Majenz, "Tight
adaptive reprogramming in the QROM", ASIACRYPT 2021, Theorem 1), for the adversaries of
`GordieHowe/Model/RingSignature/Adversary.lean`.

`RingSignature.runLawIn` is the law of a game's run with start draws `k`, the uniform oracle `H`
and, when the adversary terminates, its output, the answered requests and the final oracle in
force (`QueryBoundedAdversary.transcriptLawIn`). For a `RevealedPair` of challengers `C₀ k` and
`C₁ k` at every `k` (with `Q` requests and at most `qc` classical reads per request), an adversary
`A k H` and an event that read the oracle only through its classical part (`SameClassical`: the
values off `B` and the second components), `RingSignature.gameAdvantage_runLawIn_revealed_le`
bounds the advantage of a `t`-query adversary by `Q (√(ε W) + ε W / 2)` with `W = t + qc Q`.

The proof conditions on the classical part (`sum_uniform_mixB`, `sameClassical_mixB`) and applies
`AdaptiveIAlg.advantage_revealed_le_mixB_of_queries_le` at each value of the auxiliary input
(`AdaptiveIAlg.abs_sum_transcriptIn_mixB_le`, which also handles the non-terminating runs).
`RingSignature.toOuterMeasure_runLawIn` writes the probability of an event of the run as the
average over the start draws and the oracle.

The theorem applies to events of the output, the answered requests and the final oracle in
force.
-/

namespace GordieHowe

open GordieHowe.Quantum
open scoped ENNReal

variable {X Y Y₁ Y₂ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **Two oracles with the same classical part**: they agree outside `B`, and their values have
the same second component everywhere. They differ at most in the first component on `B`, the part
that may be reprogrammed. -/
def SameClassical [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : Y ≃+ Y₁ × Y₂) (B : Set X)
    (H H' : X → Y) : Prop :=
  (∀ x ∉ B, H x = H' x) ∧ ∀ x, (sp (H x)).2 = (sp (H' x)).2

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] in
open Classical in
/-- A mixed oracle has the classical part of its base oracle. -/
theorem sameClassical_mixB [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : Y ≃+ Y₁ × Y₂)
    (B : Set X) (H : X → Y) (g : X → Y₁) : SameClassical sp B (mixB sp B H g) H :=
  ⟨fun _ hx => mixB_of_notMem sp B H g hx, fun x => snd_sp_mixB sp B H g x⟩

/-- A set and its complement have total probability one. -/
theorem PMF.toOuterMeasure_add_compl {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s + p.toOuterMeasure sᶜ = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  simp only [Set.indicator_self_add_compl_apply, PMF.tsum_coe]

/-- The probability of a complement, in `ℝ`. -/
theorem PMF.toReal_toOuterMeasure_compl {α : Type*} (p : PMF α) (s : Set α) :
    (p.toOuterMeasure sᶜ).toReal = 1 - (p.toOuterMeasure s).toReal := by
  have h := congrArg ENNReal.toReal (PMF.toOuterMeasure_add_compl p s)
  have hs : p.toOuterMeasure s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  have hc : p.toOuterMeasure sᶜ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  rw [ENNReal.toReal_add hs hc, ENNReal.toReal_one] at h
  linarith

/-- An average of values at most one is at most one. -/
theorem PMF.tsum_mul_le_one {α : Type*} (μ : PMF α) {p : α → ℝ≥0∞} (hp : ∀ a, p a ≤ 1) :
    ∑' a, μ a * p a ≤ 1 :=
  calc ∑' a, μ a * p a ≤ ∑' a, μ a * 1 := ENNReal.tsum_le_tsum fun a => by gcongr; exact hp a
    _ = 1 := by simp only [mul_one, PMF.tsum_coe]

/-- An average over a finite type, in `ℝ`. -/
theorem PMF.toReal_tsum_mul_fintype {α : Type*} [Fintype α] (μ : PMF α) {p : α → ℝ≥0∞}
    (hp : ∀ a, p a ≤ 1) : (∑' a, μ a * p a).toReal = ∑ a, (μ a).toReal * (p a).toReal := by
  rw [tsum_fintype, ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hp a))]
  simp only [ENNReal.toReal_mul]

/-- A scaled finite sum of averages is the average of the scaled finite sums. -/
theorem PMF.sum_toReal_tsum_mul {α γ : Type*} [Fintype γ] (μ : PMF α) (N : ℕ)
    (q : α → γ → ℝ≥0∞) (hq : ∀ a g, q a g ≤ 1) :
    ∑ g, (N : ℝ)⁻¹ * (∑' a, μ a * q a g).toReal =
      (∑' a, μ a * ((N : ℝ≥0∞)⁻¹ * ∑ g, q a g)).toReal := by
  have hfin : ∀ g, ∑' a, μ a * q a g ≠ ⊤ := fun g =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.tsum_mul_le_one μ fun a => hq a g)
  have h : ∑' a, μ a * ((N : ℝ≥0∞)⁻¹ * ∑ g, q a g) = (N : ℝ≥0∞)⁻¹ * ∑ g, ∑' a, μ a * q a g := by
    calc ∑' a, μ a * ((N : ℝ≥0∞)⁻¹ * ∑ g, q a g) =
          ∑' a, ∑ g, (N : ℝ≥0∞)⁻¹ * (μ a * q a g) := tsum_congr fun a => by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun g _ => by ring
      _ = ∑' a, ∑' g, (N : ℝ≥0∞)⁻¹ * (μ a * q a g) :=
          tsum_congr fun a => (tsum_fintype (L := .unconditional _) _).symm
      _ = ∑' g, ∑' a, (N : ℝ≥0∞)⁻¹ * (μ a * q a g) := ENNReal.tsum_comm
      _ = ∑ g, ∑' a, (N : ℝ≥0∞)⁻¹ * (μ a * q a g) := tsum_fintype (L := .unconditional _) _
      _ = _ := by
          rw [Finset.mul_sum]
          simp only [ENNReal.tsum_mul_left]
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun g _ => hfin g, Finset.mul_sum]

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

/-- The output of a composition is the output of the composition with the registers as output,
mapped. -/
theorem Quantum.KindAlg.outLaw_composeBothOut_eq_map {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)
    (C : Challenger X Y Req Resp) {O' : Type} (f : B.CW C → O') (H : X → Y) :
    (B.composeBothOut C f).outLaw H = ((B.composeBothOut C id).outLaw H).map (Option.map f) := by
  simp only [Alg.outLaw]
  rw [PMF.map_comp, Option.map_comp_map]
  rfl

/-- The preimage under `Option.map f` of a set without `none`. -/
theorem Option.preimage_map_of_notMem {α β : Type*} (f : α → β) {S : Set (Option β)}
    (hS : none ∉ S) : Option.map f ⁻¹' S = {o | ∃ v ∈ o, some (f v) ∈ S} := by
  ext o
  cases o <;> simp [hS]

/-- The preimage under `Option.map f` of a set with `none`. -/
theorem Option.preimage_map_of_mem {α β : Type*} (f : α → β) {S : Set (Option β)}
    (hS : none ∈ S) : Option.map f ⁻¹' S = {o | ∃ v ∈ o, some (f v) ∉ S}ᶜ := by
  ext o
  cases o <;> simp [hS]

namespace Quantum.AdaptiveIAlg

open Classical in
/-- **Adaptive reprogramming at revealed points for an event of the output, the answered
requests and the final oracle in force** at fixed values off `B` and fixed second components,
with `width (budget + post) ≤ t`: `|Y₁^X| Q (√(ε W) + ε W / 2)` with `W = t + C₀.q Q`; the
event may contain the non-terminating runs. -/
theorem abs_sum_transcriptIn_mixB_le [Nonempty Req] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁]
    [DecidableEq Y₁] [Nonempty Y₁] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) {sp : Y ≃+ Y₁ × Y₂}
    {B : Set X} {ε : ℝ} {C₀ C₁ : Challenger X Y Req Resp} (P : C₀.RevealedPair sp B ε C₁)
    (S : Set (Option (O × List Req × (X → Y)))) (H : X → Y)
    (ht : A.width * (A.budget + A.post) ≤ t) :
    |∑ g : X → Y₁, (((A.toKindAlg.composeBothOut C₀ fun v =>
          (A.output C₀ v, (requests v.chal.logs).take C₀.Q,
            C₀.toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)).outLaw
          (mixB sp B H g)).toOuterMeasure S).toReal -
      ∑ g : X → Y₁, (((A.toKindAlg.composeBothOut C₁ fun v =>
          (A.output C₁ v, (requests v.chal.logs).take C₁.Q,
            C₁.toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)).outLaw
          (mixB sp B H g)).toOuterMeasure S).toReal| ≤
      Fintype.card (X → Y₁) * C₀.Q * (√(ε * (t + C₀.q * C₀.Q)) + ε * (t + C₀.q * C₀.Q) / 2) := by
  have hpre : ∀ (C : Challenger X Y Req Resp) (n : ℕ) (g : X → Y₁),
      ((A.toKindAlg.composeBothOut C fun v => (A.output C v, (requests v.chal.logs).take n,
          C.toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)).outLaw
        (mixB sp B H g)).toOuterMeasure S =
      ((A.toKindAlg.composeBothOut C id).outLaw (mixB sp B H g)).toOuterMeasure
        (Option.map (fun v => (A.output C v, (requests v.chal.logs).take n,
          C.toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)) ⁻¹' S) := fun C n g => by
    rw [KindAlg.outLaw_composeBothOut_eq_map, PMF.toOuterMeasure_map_apply]
  simp only [P.Q_eq, hpre]
  by_cases hn : none ∈ S
  · simp only [Option.preimage_map_of_mem _ hn, PMF.toReal_toOuterMeasure_compl,
      Finset.sum_sub_distrib]
    rw [show ∀ a b c : ℝ, a - b - (a - c) = c - b from fun _ _ _ => by ring, abs_sub_comm]
    exact A.advantage_revealed_le_mixB_of_queries_le P
      (fun o lg O => some (o, (requests lg).take C₀.Q, O) ∉ S) H ht
  · simp only [Option.preimage_map_of_notMem _ hn]
    exact A.advantage_revealed_le_mixB_of_queries_le P
      (fun o lg O => some (o, (requests lg).take C₀.Q, O) ∈ S) H ht

end Quantum.AdaptiveIAlg

namespace Quantum.QueryBoundedAdversary

/-- **The law of the adversary's output, the answered requests and the final oracle in force** at
the oracle `H` against the challenger `C`: the auxiliary input drawn, then the composed algorithm
run; the answered requests are the first `C.Q` logged requests, and the final oracle in force is
the oracle of the challenger's state after them; `none` when the run does not terminate. -/
noncomputable def transcriptLawIn (A : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) : PMF (Option (O × List Req × (X → Y))) :=
  A.aux.bind fun a =>
    ((A.alg a).toKindAlg.composeBothOut C fun v =>
      ((A.alg a).output C v, (requests v.chal.logs).take C.Q,
        C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)).outLaw H

end Quantum.QueryBoundedAdversary

namespace RingSignature

/-- **The law of a game's run with the answered requests and the final oracle in force**: as
`runLaw`, with the transcript `transcriptLawIn`. -/
noncomputable def runLawIn {K : Type} [Fintype K] [Nonempty K]
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C : K → Challenger X Y Req Resp) : PMF (K × (X → Y) × Option (O × List Req × (X → Y))) :=
  (PMF.uniformOfFintype K).bind fun k =>
    (PMF.uniformOfFintype (X → Y)).bind fun H =>
      ((A k H).transcriptLawIn (C k) H).map fun o => (k, H, o)

/-- **An event of a game's run** is the average over the start draws and the oracle of the event
under `transcriptLawIn`. -/
theorem toOuterMeasure_runLawIn {K : Type} [Fintype K] [Nonempty K]
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C : K → Challenger X Y Req Resp) (E : Set (K × (X → Y) × Option (O × List Req × (X → Y)))) :
    (runLawIn A C).toOuterMeasure E =
      ∑' k, PMF.uniformOfFintype K k * ∑' H, PMF.uniformOfFintype (X → Y) H *
        ((A k H).transcriptLawIn (C k) H).toOuterMeasure {o | (k, H, o) ∈ E} := by
  rw [runLawIn, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun k => ?_
  rw [PMF.toOuterMeasure_bind_apply]
  refine congrArg _ (tsum_congr fun H => ?_)
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- **Adaptive reprogramming at revealed points in a game's run** (GHHM21 Theorem 1): with start
draws `k`, for every `k` a `RevealedPair` of challengers `C₀ k` and `C₁ k` with `Q` requests and
at most `qc` classical reads per request, an adversary `A k H` and an event that read the oracle
only through its classical part (`SameClassical`), the runs against `C₀` and against `C₁` of a
`t`-query adversary differ on the event by at most `Q (√(ε W) + ε W / 2)` with `W = t + qc Q`. -/
theorem gameAdvantage_runLawIn_revealed_le {K : Type} [Fintype K] [Nonempty K] [Nonempty Req]
    [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
    {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ}
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', SameClassical sp B H H' → A k H = A k H')
    {C₀ C₁ : K → Challenger X Y Req Resp} (P : ∀ k, (C₀ k).RevealedPair sp B ε (C₁ k))
    {Q qc : ℕ} (hQ : ∀ k, (C₀ k).Q = Q) (hq : ∀ k, (C₀ k).q ≤ qc)
    (E : Set (K × (X → Y) × Option (O × List Req × (X → Y))))
    (hE : ∀ k H H' x, SameClassical sp B H H' → ((k, H, x) ∈ E ↔ (k, H', x) ∈ E)) :
    gameAdvantage (runLawIn A C₀) (runLawIn A C₁) E ≤
      Q * (√(ε * (t + qc * Q)) + ε * (t + qc * Q) / 2) := by
  classical
  set b : ℝ := Q * (√(ε * (t + qc * Q)) + ε * (t + qc * Q) / 2) with hb
  set N : ℕ := Fintype.card (X → Y₁) with hNdef
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr Fintype.card_pos
  -- The bound at each start draw is at most `b`.
  have hbk : ∀ k, ((C₀ k).Q : ℝ) * (√(ε * (t + (C₀ k).q * (C₀ k).Q)) +
      ε * (t + (C₀ k).q * (C₀ k).Q) / 2) ≤ b := fun k => by
    rw [hb, hQ k]
    rcases Nat.eq_zero_or_pos Q with h0 | h0
    · simp [h0]
    have hε : 0 ≤ ε := by
      obtain ⟨ω₀, -⟩ := (P k).ν.support_nonempty
      obtain ⟨c₀, -⟩ := (P k).ζ.support_nonempty
      exact ENNReal.toReal_nonneg.trans ((P k).pts_le ω₀ (fun _ => c₀) []
        (Classical.arbitrary Req) (fun _ => Classical.arbitrary Y) (Classical.arbitrary X)
        ((hQ k).symm ▸ h0))
    have hW : ((t + (C₀ k).q * Q : ℕ) : ℝ) ≤ ((t + qc * Q : ℕ) : ℝ) :=
      Nat.cast_le.2 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hq k)) _)
    push_cast at hW
    have hm := mul_le_mul_of_nonneg_left hW hε
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact add_le_add (Real.sqrt_le_sqrt hm) (by linarith)
  have hle : ∀ (C : K → Challenger X Y Req Resp) k, ∑' H, PMF.uniformOfFintype (X → Y) H *
      ((A k H).transcriptLawIn (C k) H).toOuterMeasure {o | (k, H, o) ∈ E} ≤ 1 := fun C k =>
    PMF.tsum_mul_le_one _ fun _ => PMF.toOuterMeasure_apply_le_one _ _
  rw [gameAdvantage]
  change |((runLawIn A C₀).toOuterMeasure E).toReal -
    ((runLawIn A C₁).toOuterMeasure E).toReal| ≤ _
  rw [toOuterMeasure_runLawIn, toOuterMeasure_runLawIn]
  refine PMF.abs_toReal_tsum_mul_sub_le _ (hle C₀) (hle C₁) fun k => ?_
  rw [PMF.toReal_tsum_mul_fintype _ fun _ => PMF.toOuterMeasure_apply_le_one _ _,
    PMF.toReal_tsum_mul_fintype _ fun _ => PMF.toOuterMeasure_apply_le_one _ _,
    ← sum_uniform_mixB sp B (fun H => (((A k H).transcriptLawIn (C₀ k) H).toOuterMeasure
      {o | (k, H, o) ∈ E}).toReal),
    ← sum_uniform_mixB sp B (fun H => (((A k H).transcriptLawIn (C₁ k) H).toOuterMeasure
      {o | (k, H, o) ∈ E}).toReal),
    ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  refine abs_sum_mul_le _ _ (fun _ => ENNReal.toReal_nonneg)
    (PMF.sum_toReal (PMF.uniformOfFintype (X → Y))) fun H => ?_
  -- At the mixed oracle the adversary and the event are those at the base oracle.
  have hmix : ∀ (C : K → Challenger X Y Req Resp) (g : X → Y₁),
      ((A k (mixB sp B H g)).transcriptLawIn (C k) (mixB sp B H g)).toOuterMeasure
        {o | (k, mixB sp B H g, o) ∈ E} =
      ∑' a, (A k H).aux a * (((((A k H).alg a).toKindAlg.composeBothOut (C k) fun v =>
          (((A k H).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q,
            (C k).toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)).outLaw
          (mixB sp B H g)).toOuterMeasure {o | (k, H, o) ∈ E}) := fun C g => by
    have hs := sameClassical_mixB sp B H g
    rw [hA k _ _ hs, QueryBoundedAdversary.transcriptLawIn, PMF.toOuterMeasure_bind_apply]
    refine tsum_congr fun a => ?_
    congr 2
    ext o
    exact hE k _ _ o hs
  simp only [hmix]
  rw [PMF.sum_toReal_tsum_mul _ N _ fun _ _ => PMF.toOuterMeasure_apply_le_one _ _,
    PMF.sum_toReal_tsum_mul _ N _ fun _ _ => PMF.toOuterMeasure_apply_le_one _ _]
  have hle' : ∀ (C : K → Challenger X Y Req Resp) a, (N : ℝ≥0∞)⁻¹ *
      ∑ g : X → Y₁, ((((A k H).alg a).toKindAlg.composeBothOut (C k) fun v =>
          (((A k H).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q,
            (C k).toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)).outLaw
          (mixB sp B H g)).toOuterMeasure {o | (k, H, o) ∈ E} ≤ 1 := fun C a => by
    calc (N : ℝ≥0∞)⁻¹ * ∑ g : X → Y₁, _ ≤ (N : ℝ≥0∞)⁻¹ * ∑ _g : X → Y₁, 1 := by
          gcongr with g
          exact PMF.toOuterMeasure_apply_le_one _ _
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _)
  refine PMF.abs_toReal_tsum_mul_sub_le _ (hle' C₀) (hle' C₁) fun a => ?_
  have hreal : ∀ (C : K → Challenger X Y Req Resp), ((N : ℝ≥0∞)⁻¹ *
      ∑ g : X → Y₁, ((((A k H).alg a).toKindAlg.composeBothOut (C k) fun v =>
          (((A k H).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q,
            (C k).toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)).outLaw
          (mixB sp B H g)).toOuterMeasure {o | (k, H, o) ∈ E}).toReal =
      (N : ℝ)⁻¹ * ∑ g : X → Y₁, (((((A k H).alg a).toKindAlg.composeBothOut (C k) fun v =>
          (((A k H).alg a).output (C k) v, (requests v.chal.logs).take (C k).Q,
            (C k).toPureEnv.oracle (mixB sp B H g, v.chal.coins) v.chal.logs)).outLaw
          (mixB sp B H g)).toOuterMeasure {o | (k, H, o) ∈ E}).toReal := fun C => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum fun g _ =>
        ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)]
  rw [hreal, hreal, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hN)]
  have hkey := ((A k H).alg a).abs_sum_transcriptIn_mixB_le (P k) {o | (k, H, o) ∈ E} H
    ((A k H).queries_le a)
  calc (N : ℝ)⁻¹ * |_| ≤ (N : ℝ)⁻¹ * (N * (C₀ k).Q * (√(ε * (t + (C₀ k).q * (C₀ k).Q)) +
        ε * (t + (C₀ k).q * (C₀ k).Q) / 2)) :=
        mul_le_mul_of_nonneg_left hkey (inv_pos.mpr hN).le
    _ = (C₀ k).Q * (√(ε * (t + (C₀ k).q * (C₀ k).Q)) + ε * (t + (C₀ k).q * (C₀ k).Q) / 2) := by
        field_simp
    _ ≤ b := hbk k

end RingSignature

end GordieHowe
