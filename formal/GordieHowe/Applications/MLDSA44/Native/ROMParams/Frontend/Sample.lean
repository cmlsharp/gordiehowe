-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Shuffle

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, SampleInBall's view

The instance of the frontend's SampleInBall view (`GordieHowe.MLDSA44.Native.ROMParams.SampleView`, `sampleView`):

* **the events** (`sampleEvent`): at `h2c.sample.select.delta` (challenge `0`) the selection's
  fingerprint event (`SelectFirstTau.badEvent`, degree `264`), at `h2c.sample.mem.delta`
  (challenge `1`) the memory check's permutation event (`SampleInBall.bad`, degree `295`); each
  reads the committed values and its challenge (`sampleEvent_use`), with probability at most
  `264/2^128` and `295/2^128` (`sampleEvent_bound`, Schwartz–Zippel);
* **the soundness** (`sampledAt`): without the events, the selection selects the first `39`
  candidates below the rising threshold (`selectRun`, `SelectFirstTau.sound`), the memory check
  makes H's decoded challenge the shuffle's ternary decoding (`shuffles_or_bad`), so the
  fixed-stream `SampleInBall` of the stream is H's decoded challenge, whose support and sign are
  bits.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits IOP
open scoped NNReal ENNReal

/-- **The program facts of domain `H` SampleInBall's events read** (`MldsaHShuffle` and): the challenges `560`, `567` (the source challenges `0`, `1`, one coordinate of domain `H`'s field, drawn whole) and the events' values reading nothing from the run. Each program instantiates it by `decide`. -/
class MldsaHSample (program : RealizedProgram) : Prop extends MldsaHShuffle program where
  /-- `δ` of the selection is challenge `0`. -/
  kind560 : (program.value 560).kind = .challenge 0
  /-- Challenge `0` lies in the field of value `560`. -/
  field560 : program.chalField 0 = program.valueField 560
  /-- `δ` of the memory check is challenge `1`. -/
  kind567 : (program.value 567).kind = .challenge 1
  /-- Challenge `1` lies in the field of value `567`. -/
  field567 : program.chalField 1 = program.valueField 567
  /-- The values the events read read nothing from the run (`RealizedProgram.nodeReads`). -/
  sampleReads_nil : ∀ v ∈ [555, 556, 557, 559, 561, 562, 563, 564, 565, 566], program.nodeReads program.fuel v = []
  /-- **The source program's challenges are `h2c.sample.select.delta` and `h2c.sample.mem.delta`**
  (challenges `0` and `1`; `mac.beta` and `alpha:A` are realization challenges). -/
  isSourceChal_iff : ∀ {j : ℕ}, program.IsSourceChal j ↔ j = 0 ∨ j = 1
  /-- The challenges are one coordinate of `GF(2^128)`, drawn whole. -/
  chalFacts : (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧ program.chalField 0 = 1 ∧ (program.challenge 1).size = 1 ∧ (program.challenge 1).sampler = .full ∧ program.chalField 1 = 1

set_option maxRecDepth 4096 in
/-- The native program at the ROM parameters has these facts. -/
instance : MldsaHSample program where
  kind560 := RealizedProgram.Kind.eq_of_challenge? (by decide +kernel)
  field560 := by decide +kernel
  kind567 := RealizedProgram.Kind.eq_of_challenge? (by decide +kernel)
  field567 := by decide +kernel
  sampleReads_nil := by
    decide +kernel
  isSourceChal_iff := by
    intro j
    constructor
    · intro h
      have hj : j < 4 := h.1
      have key : ∀ j < 4, program.IsSourceChal j → j = 0 ∨ j = 1 := by decide +kernel
      exact key j hj h
    · rintro (rfl | rfl) <;> decide +kernel
  chalFacts := by
    decide +kernel

/-- **The round errors of SampleInBall's challenges** over a field of `2^bits` elements:
`264/2^bits` at `h2c.sample.select.delta` (challenge `0`), `295/2^bits` at `h2c.sample.mem.delta`
(challenge `1`), `0` elsewhere. -/
noncomputable def sampleEpsOf (bits j : ℕ) : ℝ≥0 :=
  if j = 0 then 264 / 2 ^ bits else if j = 1 then 295 / 2 ^ bits else 0

@[simp] theorem sampleEpsOf_zero (bits : ℕ) : sampleEpsOf bits 0 = 264 / 2 ^ bits := rfl

/-- **The round errors of `Π_P₀`'s challenges** over `GF(2^128)`: `264/2^128` at
`h2c.sample.select.delta`, `295/2^128` at `h2c.sample.mem.delta`, `0` elsewhere. -/
noncomputable def sampleEps (j : ℕ) : ℝ≥0 := sampleEpsOf 128 j

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaHSample program] {F0 FH : RealizedProgram.FieldInterp} [HField FH]
  [MldsaHConsts program FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The events -/

/-- **The selection's event** at the committed values: the fingerprint event of the candidates,
the selected bytes and the low threshold bits (degree `264`). -/
noncomputable def selBadE (e : program.Env interp) : ChallengeEvent (interp 1).K :=
  SelectFirstTau.badEvent selF 39 (candBits (program.reader e)) (jBits (program.reader e))
    (lowThr (program.reader e)) (by decide)

/-- **The memory check's event** at the committed values: the permutation event of the packed
records (degree `295`). -/
noncomputable def memBadE (e : program.Env interp) : ChallengeEvent (interp 1).K :=
  (samM program F0 FH).bad (samLowered e)

/-- **SampleInBall's events**: at challenge `0` (`h2c.sample.select.delta`) `δ` is a root of the
selection's event, at challenge `1` (`h2c.sample.mem.delta`) of the memory check's. -/
def sampleEvent (j : ℕ) (e : program.Env interp) : Prop :=
  (j = 0 ∧ (selBadE e).BadAt (RealizedProgram.castElt (e.chal 0 0))) ∨
    (j = 1 ∧ (memBadE e).BadAt (RealizedProgram.castElt (e.chal 1 0)))

/-- **`δ` of the selection is challenge `0`.** -/
theorem selDelta_eq (e : program.Env interp) :
    selDelta (program.reader e) = RealizedProgram.castElt (e.chal 0 0) := by
  have hk : (program.value 560).kind = .challenge 0 := MldsaHSample.kind560
  have hf : program.chalField 0 = program.valueField 560 := MldsaHSample.field560
  unfold selDelta
  rw [RealizedProgram.evalE_leaf]
  exact RealizedProgram.castElt_reader_of_challenge e hk hf 0

/-- **`δ` of the memory check is challenge `1`.** -/
theorem memDelta_eq (e : program.Env interp) :
    memDelta (program.reader e) = RealizedProgram.castElt (e.chal 1 0) := by
  have hk : (program.value 567).kind = .challenge 1 := MldsaHSample.kind567
  have hf : program.chalField 1 = program.valueField 567 := MldsaHSample.field567
  unfold memDelta
  rw [RealizedProgram.evalE_leaf]
  exact RealizedProgram.castElt_reader_of_challenge e hk hf 0

/-! ## The challenge-use rule -/

/-- The values the events read read nothing from the run (`RealizedProgram.nodeReads`). -/
theorem sampleReads_nil : ∀ v ∈ [555, 556, 557, 559, 561, 562, 563, 564, 565, 566], program.nodeReads program.fuel v = [] :=
  MldsaHSample.sampleReads_nil

/-- **The events' values read alike** in two environments of one statement and committed
assignment. -/
theorem reader_sample {e e' : program.Env interp} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg)
    {v : ℕ} (hv : v ∈ [555, 556, 557, 559, 561, 562, 563, 564, 565, 566]) :
    program.reader e v = program.reader e' v :=
  RealizedProgram.reader_eq_of_nodeReads_nil ((sampleReads_nil (program := program)) v hv) hs ha

/-- **The selection's event is fixed by the statement and the committed assignment.** -/
theorem selBadE_congr {e e' : program.Env interp} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    selBadE e = selBadE e' := by
  unfold selBadE candBits HashCircuit.candidates sibByte Falcon512.HashCircuit.byteWires sibBits jBits lowThr
  simp only [RealizedProgram.evalE_leaf, reader_sample hs ha (show 555 ∈ _ by simp),
    reader_sample hs ha (show 556 ∈ _ by simp), reader_sample hs ha (show 557 ∈ _ by simp),
    reader_sample hs ha (show 559 ∈ _ by simp)]

/-- **The memory check's event is fixed by the statement and the committed assignment.** -/
theorem memBadE_congr {e e' : program.Env interp} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    memBadE e = memBadE e' := by
  unfold memBadE SampleInBall.bad SampleInBall.readsPacked SampleInBall.writesPacked
  simp only [samLowered_base, samLowered_readValue, samLowered_origin, samLowered_cEnc,
    samLowered_finalOrigin, samLowered_unit, samM_positions]
  unfold jBits
  simp only [RealizedProgram.evalE_leaf, reader_sample hs ha (show 557 ∈ _ by simp),
    reader_sample hs ha (show 561 ∈ _ by simp), reader_sample hs ha (show 563 ∈ _ by simp),
    reader_sample hs ha (show 564 ∈ _ by simp), reader_sample hs ha (show 565 ∈ _ by simp),
    reader_sample hs ha (show 566 ∈ _ by simp)]

/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): each event reads the committed
assignment and its challenge. -/
theorem sampleEvent_use : RealizedProgram.ChallengeUseAt program interp sampleEvent := by
  intro j e e' h
  unfold sampleEvent
  rw [selBadE_congr h.stmt h.asg, memBadE_congr h.stmt h.asg]
  by_cases hj0 : j = 0
  · subst hj0
    rw [h.chal 0 (Or.inr ⟨rfl, le_refl 0⟩)]
    simp
  · by_cases hj1 : j = 1
    · subst hj1
      rw [h.chal 1 (Or.inr ⟨rfl, le_refl 1⟩)]
      simp
    · simp [hj0, hj1]

/-! ## The probabilities -/

/-- **The source program's challenges are `h2c.sample.select.delta` and `h2c.sample.mem.delta`**
(challenges `0` and `1`; `mac.beta` and `alpha:A` are realization challenges). -/
theorem isSourceChal_iff : ∀ {j : ℕ}, program.IsSourceChal j ↔ j = 0 ∨ j = 1 :=
  MldsaHSample.isSourceChal_iff

/-- The challenges are one coordinate of `GF(2^128)`, drawn whole. -/
theorem chalFacts : (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧ program.chalField 0 = 1 ∧ (program.challenge 1).size = 1 ∧ (program.challenge 1).sampler = .full ∧ program.chalField 1 = 1 :=
  MldsaHSample.chalFacts

/-- **The events' probabilities** (`RealizedProgram.rbr_of_events`' `hbound`): at most `264/2^128` at
`h2c.sample.select.delta` and `295/2^128` at `h2c.sample.mem.delta`
(`RealizedProgram.probUniform_badAt_setChal_le`, Schwartz–Zippel). -/
theorem sampleEvent_bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env interp,
    Pr[c ← program.ChalVal interp j : sampleEvent j (e.setChal j c)] ≤
      sampleEpsOf (HField.bits FH) j := by
  intro j hj e
  rcases isSourceChal_iff.1 hj with rfl | rfl
  · have hset : ∀ c, sampleEvent 0 (e.setChal 0 c) ↔
        (selBadE e).BadAt (RealizedProgram.castElt ((e.setChal 0 c).chal 0 0)) := fun c => by
      simp only [sampleEvent, true_and, zero_ne_one, false_and, or_false]
      rw [selBadE_congr (e := e.setChal 0 c) (e' := e) rfl rfl]
    simp only [hset]
    refine (RealizedProgram.probUniform_badAt_setChal_le (j := 0) (chalFacts (program := program)).1 (chalFacts (program := program)).2.1 (chalFacts (program := program)).2.2.1
      (selBadE e) e).trans ?_
    have hdeg : (selBadE e).deg = 264 := rfl
    have hcard : Fintype.card (interp 1).K = 2 ^ HField.bits FH := HField.card
    rw [hdeg, hcard]
    simp only [sampleEpsOf]
    norm_num
  · have hset : ∀ c, sampleEvent 1 (e.setChal 1 c) ↔
        (memBadE e).BadAt (RealizedProgram.castElt ((e.setChal 1 c).chal 1 0)) := fun c => by
      simp only [sampleEvent, one_ne_zero, false_and, false_or, true_and]
      rw [memBadE_congr (e := e.setChal 1 c) (e' := e) rfl rfl]
    simp only [hset]
    refine (RealizedProgram.probUniform_badAt_setChal_le (j := 1) (chalFacts (program := program)).2.2.2.1 (chalFacts (program := program)).2.2.2.2.1
      (chalFacts (program := program)).2.2.2.2.2 (memBadE e) e).trans ?_
    have hdeg : (memBadE e).deg = 295 := (samM program F0 FH).bad_deg _
    have hcard : Fintype.card (interp 1).K = 2 ^ HField.bits FH := HField.card
    rw [hdeg, hcard]
    simp only [sampleEpsOf, if_neg one_ne_zero]
    norm_num

/-! ## Soundness -/

/-- **The stream's bytes are bytes of bits.** -/
theorem sibByte_bool (e : program.Env interp) (o : Fin (264 + 8)) :
    AllBool (sibByte (program.reader e) o) := fun _ => sibBits_bool e _

theorem chalPair_fst (rd : program.Valuation interp) (k : Fin 256) :
    (chalPair rd k).1 = program.evalE rd 1 (.ref 523) k := by
  simp only [chalPair]

theorem chalPair_snd (rd : program.Valuation interp) (k : Fin 256) :
    (chalPair rd k).2 = program.evalE rd 1 (.ref 522) k := by
  simp only [chalPair]

/-- **SampleInBall's soundness** (`SampleView.sound`): where the source program holds and neither
event occurred, the fixed-stream `SampleInBall` of the stream is H's decoded challenge, whose
support and sign are bits. The selection selects the first `39` candidates below the rising
threshold (`selectRun`, `SelectFirstTau.sound`), so the positions are checked
(`MLDSA44.acceptedCandidates_le`) and the memory check makes the decoded challenge the shuffle's
ternary decoding (`shuffles_or_bad`, `MemoryShuffle.decodeTernary_encode`). -/
theorem sampledAt {e : program.Env interp} (hs : HSat e)
    (hno : ∀ j, program.IsSourceChal j → ¬ sampleEvent j e) : SampledAt (program.reader e) := by
  set rd := program.reader e
  have hfirst := (SelectFirstTau.sound (τ := 39) (by norm_num) (by norm_num) (by norm_num)
    (candBits_bool e) (jBits_bool hs) (lowThr_bool e) (selectRun hs)).resolve_right fun hb =>
      hno 0 (isSourceChal_iff.2 (.inl rfl)) (.inl ⟨rfl, by rw [← selDelta_eq]; exact hb⟩)
  have hsh := (shuffles_or_bad hs).resolve_right fun hb =>
    hno 1 (isSourceChal_iff.2 (.inr rfl)) (.inr ⟨rfl, by rw [← memDelta_eq]; exact hb⟩)
  have hacc : MLDSA44.acceptedCandidates mldsa44 (sibStream rd) =
      some fun j => natOfBits (jBits rd j) :=
    (SelectFirstTau.acceptedCandidates_eq mldsa44 _).trans hfirst
  have hp : SampleInBall.Positioned (samM program F0 FH).N ((samM program F0 FH).positions (samLowered e).base)
      ((samM program F0 FH).signs (samLowered e).base) := by
    rw [samLowered_base, samM_positions, samM_signs, samM_N]
    exact ⟨jBits_bool hs, fun t => MLDSA44.acceptedCandidates_le mldsa44 hacc t,
      fun t => sibBits_bool e _⟩
  have hdec := hsh hp
  rw [samLowered_base, samM_chal, samM_positions, samM_signs] at hdec
  have hsgn := Native.signBoolsOf_signWires (out := sibByte rd) (sibByte_bool e)
  have hfix : MLDSA44.fixedStreamChallenge mldsa44 (sibStream rd) =
      some (SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd)) := by
    refine (MLDSA44.fixedStreamChallenge_eq_some_iff mldsa44).mpr ⟨_, hacc, ?_⟩
    unfold SampleInBall.shuffleOf signsH
    exact congrArg _ hsgn
  have hval : ∀ k : Fin 256, chalPair rd k =
      ((if SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k = 0 then 0 else 1 : (interp 1).K),
        (if SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k = -1 then 1 else 0 : (interp 1).K)) :=
    fun k => by
      rw [hdec k]
      exact MemoryShuffle.decodeTernary_encode (samM program F0 FH).Θ
        (SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k)
        (MemoryShuffle.shuffle_ternary _ _ _ _ k)
  have hsup : ∀ k, supH rd k = if SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k = 0 then 0
      else 1 := fun k => by
    unfold supH
    rw [← chalPair_fst, hval k]
    split
    · exact HField.toNat_zero
    · exact HField.toNat_one
  have hsg : ∀ k, sgnH rd k = if SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k = -1 then 1
      else 0 := fun k => by
    unfold sgnH
    rw [← chalPair_snd, hval k]
    by_cases h : SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k = -1
    · rw [if_pos h, if_pos h]
      exact HField.toNat_one
    · rw [if_neg h, if_neg h]
      exact HField.toNat_zero
  refine ⟨?_, fun k => ?_, fun k => ?_⟩
  · rw [hfix]
    refine congrArg some (funext fun k => ?_)
    unfold chalH
    rw [hsup k, hsg k]
    rcases MemoryShuffle.shuffle_ternary (samM program F0 FH).N (samM program F0 FH).τ (fun t => natOfBits (jBits rd t))
      (SampleInBall.signBoolsOf (signsH rd)) k with h | h | h
    · change SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k = 0 at h
      simp [h]
    · change SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k = 1 at h
      simp [h]
    · change SampleInBall.shuffleOf (samM program F0 FH).N (jBits rd) (signsH rd) k = -1 at h
      simp [h]
  · rw [hsup k]
    split <;> norm_num
  · rw [hsg k]
    split <;> norm_num

/-- **SampleInBall's view of `MLDSA44.Native.ROMParams`** (`SampleView`): the events `sampleEvent` at
`h2c.sample.select.delta` and `h2c.sample.mem.delta` with errors `264/2^128` and `295/2^128`, and
the soundness `sampledAt`. -/
noncomputable def sampleView : SampleView program F0 FH where
  event := sampleEvent
  eps := sampleEpsOf (HField.bits FH)
  use := sampleEvent_use
  bound := sampleEvent_bound
  sound _ hs hno := sampledAt hs hno

end GordieHowe.MLDSA44.Native.ROMParams
