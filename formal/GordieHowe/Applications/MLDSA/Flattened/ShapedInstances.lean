-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Shaped
public import GordieHowe.Applications.MLDSA.Flattened.PresentationAverage
public import GordieHowe.Applications.MLDSA.Signing.BinomialFloorDyadic
public import GordieHowe.Applications.MLDSA.Signing.SampleInBallShape

public section

/-!
# The shaped cut-off at ML-DSA-65 and ML-DSA-87

The public spectrum tables `spectrumTable65`, `spectrumTable87` (`incrementTable` of 256 antitone
natural increments) are concave and satisfy the fill condition at `M = 4` with
`x_max = 233 / 4096` at ML-DSA-65 and `x_max = 15 / 256` at ML-DSA-87
(`shiftBoundMax_spectrumTable65_le`, `shiftBoundMax_spectrumTable87_le`). So the constant
functions `x_max` satisfy the shape bound (`shapeBound_spectrumTable65`,
`shapeBound_spectrumTable87`), and every key under the table has the exact floor at the constant
cut-off `Pr[Bin(N, x_max) ≤ ω]` (`keyFloor_mldsa65_of_spectrumEnvelope`,
`keyFloor_mldsa87_of_spectrumEnvelope`).

For a public `x̂ ≤ x_max` satisfying the shape bound, the shaped cut-offs `shapedCutoff65`,
`shapedCutoff87` have mean shape at least `2^-14` and `2^-18`, and the presentations averaged over
a uniform matrix, counted on the matrices whose key is under the table, have advantage in the
quantum random-oracle model (`GordieHowe.QROM.ZeroKnowledge`, query-bounded quantum adversaries,
`R` of 64 bytes) at most

* `Q / 2^504 + (11 Q + 22) / 2^185 + Q δ + Q (Q - 1) / 2^513 + 2 t √(Q / 2^512)
  + 4 Q t / 2^256 + Q (Q - 1) / 2^512` at ML-DSA-65
  (`expect_zkAdvantage_honestPresenter_le_mldsa65_shaped`);
* `Q / 2^758 + (12 Q + 24) / 2^276 + Q δ + …` with the same salt terms at ML-DSA-87
  (`expect_zkAdvantage_honestPresenter_le_mldsa87_shaped`).

The computed shapes `xhat65`, `xhat87` (`shapedXhat` at `P = 40`, `L = 32`, capped at `x_max`)
satisfy the shape bound (`shapeBound_xhat65`, `shapeBound_xhat87`), so the bounds above hold at
the computed cut-offs `computedCutoff65`, `computedCutoff87` with no shape hypothesis
(`expect_zkAdvantage_honestPresenter_le_mldsa65_computedShape`,
`expect_zkAdvantage_honestPresenter_le_mldsa87_computedShape`). The key checks `spectrumCheck65`,
`spectrumCheck87` imply the spectrum envelopes (`spectrumEnvelope_of_spectrumCheck65`,
`spectrumEnvelope_of_spectrumCheck87`).
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF GordieHowe.MLDSA.Regularity
open scoped ENNReal BigOperators

attribute [local instance] concreteNTTRingOps

/-! ### The tables -/

/-- **The spectrum increments of ML-DSA-65**: a public list of 256 antitone naturals;
`spectrumTable65 m` is the sum of the first `m` entries. -/
def spectrumIncrements65 : List ℕ :=
    [31911673118, 31911673118, 26631181216, 26631181216, 22727520149, 22727520149, 19688158878,
    19688158878, 18582985695, 18582985695, 17328661840, 17328661840, 17167629520, 17167629520,
    16565446054, 16565446054, 14558437873, 14558437873, 14409557237, 14409557237, 14362840762,
    14362840762, 14357890076, 14357890076, 14331786458, 14331786458, 13591433841, 13591433841,
    13324456837, 13324456837, 13087724025, 13087724025, 12977728779, 12977728779, 12910489459,
    12910489459, 12666555649, 12666555649, 12585994482, 12585994482, 12570962399, 12570962399,
    12499672518, 12499672518, 12496072019, 12496072019, 12191919862, 12191919862, 11953836862,
    11953836862, 11627901686, 11627901686, 11616560114, 11616560114, 11452377357, 11452377357,
    11139313965, 11139313965, 11018956328, 11018956328, 11018956328, 11018956328, 11018956328,
    11018956328, 11018956328, 11018956328, 10792854749, 10792854749, 10709916128, 10709916128,
    10642909733, 10642909733, 10517998000, 10517998000, 10517998000, 10517998000, 10517998000,
    10517998000, 10517998000, 10517998000, 10517998000, 10517998000, 10517998000, 10517998000,
    10517998000, 10517998000, 10478296419, 10478296419, 10435411795, 10435411795, 10368047966,
    10368047966, 10190435683, 10190435683, 10135127403, 10135127403, 10021197866, 10021197866,
    9881040609, 9881040609, 9730576318, 9730576318, 9618303269, 9618303269, 9561798636, 9561798636,
    9551215521, 9551215521, 9487716829, 9487716829, 9334767807, 9334767807, 9241084230, 9241084230,
    9133486157, 9133486157, 9117556268, 9117556268, 8958091727, 8958091727, 8924106123, 8924106123,
    8872515737, 8872515737, 8816057118, 8816057118, 8688884883, 8688884883, 8637165659, 8637165659,
    8591372979, 8591372979, 8515054914, 8515054914, 8446209448, 8446209448, 8403720541, 8403720541,
    8195546062, 8195546062, 8087671908, 8087671908, 8018209861, 8018209861, 7937649347, 7937649347,
    7715661602, 7715661602, 7606315015, 7606315015, 7594121426, 7594121426, 7393695628, 7393695628,
    7237028711, 7237028711, 7106911609, 7106911609, 7065876730, 7065876730, 7051428477, 7051428477,
    7001844281, 7001844281, 6991113923, 6991113923, 6844146661, 6844146661, 6810704017, 6810704017,
    6782994660, 6782994660, 6774675411, 6774675411, 6750067368, 6750067368, 6715143087, 6715143087,
    6641604240, 6641604240, 6620576050, 6620576050, 6556304331, 6556304331, 6408214339, 6408214339,
    6398496278, 6398496278, 6345323026, 6345323026, 6310702435, 6310702435, 6308098068, 6308098068,
    6147538406, 6147538406, 6056496006, 6056496006, 5888657001, 5888657001, 5845956431, 5845956431,
    5812578206, 5812578206, 5767779419, 5767779419, 5766214958, 5766214958, 5715103113, 5715103113,
    5579823292, 5579823292, 5438359250, 5438359250, 5356952087, 5356952087, 5273419098, 5273419098,
    5186563931, 5186563931, 5065723160, 5065723160, 5006052795, 5006052795, 4945554187, 4945554187,
    4802700536, 4802700536, 4798485695, 4798485695, 4745514902, 4745514902, 4563669374, 4563669374,
    4551218109, 4551218109, 4421680778, 4421680778, 4186772430, 4186772430, 3845904091, 3845904091,
    3657791517, 3657791517, 3542932507, 3542932507, 3430567431, 3430567431, 3263114939, 3263114939,
    3081932006, 3081932006, 2490087389, 2490087389, 2137982543, 2137982543]

/-- **The spectrum table of ML-DSA-65**: the table `E` at which `SpectrumEnvelope E t₀` is the
condition on the key in the ML-DSA-65 statements of this file. -/
noncomputable def spectrumTable65 : ℕ → ℝ := incrementTable spectrumIncrements65

/-- **The spectrum increments of ML-DSA-87**: a public list of 256 antitone naturals;
`spectrumTable87 m` is the sum of the first `m` entries. -/
def spectrumIncrements87 : List ℕ :=
    [37378528045, 37378528045, 26935512467, 26935512467, 26096712988, 26096712988, 21304358245,
    21304358245, 21304358245, 21304358245, 19851853534, 19851853534, 19161588297, 19161588297,
    18932010783, 18932010783, 18932010783, 18932010783, 18932010783, 18932010783, 18932010783,
    18932010783, 18932010783, 18932010783, 18932010783, 18932010783, 18592522177, 18592522177,
    18592522177, 18592522177, 18592522177, 18592522177, 17908189729, 17908189729, 17732771339,
    17732771339, 17205538910, 17205538910, 16472226521, 16472226521, 16445229680, 16445229680,
    16141970828, 16141970828, 16141970828, 16141970828, 16141970828, 16141970828, 16141970828,
    16141970828, 16141970828, 16141970828, 16141970828, 16141970828, 15805484870, 15805484870,
    15770320599, 15770320599, 15624291198, 15624291198, 15386321882, 15386321882, 15204151426,
    15204151426, 15200976874, 15200976874, 15180952775, 15180952775, 14780959199, 14780959199,
    14641034706, 14641034706, 14247390235, 14247390235, 14213569044, 14213569044, 13815406940,
    13815406940, 13551430716, 13551430716, 13338558241, 13338558241, 13338558241, 13338558241,
    13338558241, 13338558241, 13338558241, 13338558241, 13338558241, 13338558241, 13338558241,
    13338558241, 13338558241, 13338558241, 13338558241, 13338558241, 13338558241, 13338558241,
    13241872158, 13241872158, 12914373359, 12914373359, 12875944239, 12875944239, 12737185929,
    12737185929, 12654368743, 12654368743, 12620804068, 12620804068, 12418686354, 12418686354,
    12362988452, 12362988452, 12255484205, 12255484205, 12214501251, 12214501251, 12091686161,
    12091686161, 11964821420, 11964821420, 11864212524, 11864212524, 11858752184, 11858752184,
    11846153270, 11846153270, 11650310691, 11650310691, 11285063794, 11285063794, 11146670317,
    11146670317, 11078105957, 11078105957, 11041634776, 11041634776, 10964204963, 10964204963,
    10946984826, 10946984826, 10859473450, 10859473450, 10817663540, 10817663540, 10803751226,
    10803751226, 10772825513, 10772825513, 10701464096, 10701464096, 10628558218, 10628558218,
    10508540184, 10508540184, 10402543915, 10402543915, 10268443312, 10268443312, 10024685943,
    10024685943, 9996107326, 9996107326, 9902612681, 9902612681, 9691653838, 9691653838, 9214220665,
    9214220665, 9126076911, 9126076911, 9011032773, 9011032773, 9008770805, 9008770805, 8917598934,
    8917598934, 8856890653, 8856890653, 8846991506, 8846991506, 8829029541, 8829029541, 8790138299,
    8790138299, 8697093616, 8697093616, 8567018341, 8567018341, 8412134393, 8412134393, 8172244259,
    8172244259, 8065053269, 8065053269, 8065053269, 8065053269, 8065053269, 8065053269, 8065053269,
    8065053269, 8065053269, 8065053269, 8065053269, 8065053269, 8065053269, 8065053269, 8065053269,
    8065053269, 8065053269, 8065053269, 7893848435, 7893848435, 7874434624, 7874434624, 7667211697,
    7667211697, 7485877918, 7485877918, 7319589421, 7319589421, 7319589421, 7319589421, 7319589421,
    7319589421, 7319589421, 7319589421, 7319589421, 7319589421, 6938151554, 6938151554, 6824166248,
    6824166248, 6548957272, 6548957272, 6487218794, 6487218794, 6174910540, 6174910540, 6162926874,
    6162926874, 6142318878, 6142318878, 5679891084, 5679891084, 5487822606, 5487822606, 4828867580,
    4828867580, 4652410851, 4652410851, 3605849593, 3605849593, 2629980969, 2629980969]

/-- **The spectrum table of ML-DSA-87**: the table `E` at which `SpectrumEnvelope E t₀` is the
condition on the key in the ML-DSA-87 statements of this file. -/
noncomputable def spectrumTable87 : ℕ → ℝ := incrementTable spectrumIncrements87

/-- The ML-DSA-65 table is concave. -/
theorem concaveTable_spectrumTable65 : ConcaveTable spectrumTable65 ringDegree :=
  concaveTable_incrementTable (by decide +kernel) _

/-- The ML-DSA-87 table is concave. -/
theorem concaveTable_spectrumTable87 : ConcaveTable spectrumTable87 ringDegree :=
  concaveTable_incrementTable (by decide +kernel) _

/-- **The fill condition at ML-DSA-65**: `shiftBoundMax E 49 4 ≤ 1536 · 523383² · (233/4096)²`. -/
theorem shiftBoundMax_spectrumTable65_le :
    shiftBoundMax spectrumTable65 mldsa65.tau 4 ≤
      (mldsa65.k * ringDegree : ℕ) * ((2 * (mldsa65.gamma2 - mldsa65.beta) - 1 : ℕ) : ℝ) ^ 2 *
        (233 / 4096 : ℝ) ^ 2 := by
  obtain ⟨hk, -, -, hg2, hb, -⟩ := mldsa65_vals
  obtain ⟨hτ, -⟩ := mldsa65_tau_lambda
  have h4 : spectrumTable65 4 = 117085708668 := incrementTable_eq (by decide +kernel)
  have h5 : spectrumTable65 (4 + 1) = 139813228817 := incrementTable_eq (by decide +kernel)
  rw [shiftBoundMax, h4, h5, hk, hg2, hb, hτ]
  norm_num [ringDegree]

/-- **The fill condition at ML-DSA-87**: `shiftBoundMax E 60 4 ≤ 2048 · 523535² · (15/256)²`. -/
theorem shiftBoundMax_spectrumTable87_le :
    shiftBoundMax spectrumTable87 mldsa87.tau 4 ≤
      (mldsa87.k * ringDegree : ℕ) * ((2 * (mldsa87.gamma2 - mldsa87.beta) - 1 : ℕ) : ℝ) ^ 2 *
        (15 / 256 : ℝ) ^ 2 := by
  obtain ⟨hk, -, -, hg2, hb, -⟩ := mldsa87_vals
  obtain ⟨hτ, -⟩ := mldsa87_tau_lambda
  have h4 : spectrumTable87 4 = 128628081024 := incrementTable_eq (by decide +kernel)
  have h5 : spectrumTable87 (4 + 1) = 154724794012 := incrementTable_eq (by decide +kernel)
  rw [shiftBoundMax, h4, h5, hk, hg2, hb, hτ]
  norm_num [ringDegree]

/-! ### The constant cut-offs -/

/-- **The shape bound at the constant `233 / 4096`** at ML-DSA-65. -/
theorem shapeBound_spectrumTable65 :
    ShapeBound (concretePrimitives mldsa65) spectrumTable65 fun _ => 233 / 4096 :=
  shapeBound_const (sampleInBallShape_concrete mldsa65) concaveTable_spectrumTable65
    (by norm_num [ringDegree]) (incrementTable_le_succ _ 4)
    (by simpa using shiftBoundMax_spectrumTable65_le)

/-- **The shape bound at the constant `15 / 256`** at ML-DSA-87. -/
theorem shapeBound_spectrumTable87 :
    ShapeBound (concretePrimitives mldsa87) spectrumTable87 fun _ => 15 / 256 :=
  shapeBound_const (sampleInBallShape_concrete mldsa87) concaveTable_spectrumTable87
    (by norm_num [ringDegree]) (incrementTable_le_succ _ 4)
    (by simpa using shiftBoundMax_spectrumTable87_le)

/-- **The exact floor at the constant cut-off at ML-DSA-65**: a key with `‖t₀‖∞ ≤ 2^12` under the
table has the floor at `Pr[Bin(1536, 233/4096) ≤ 55]` with defect `0`. -/
theorem keyFloor_mldsa65_of_spectrumEnvelope {t0 : RqVec mldsa65.k}
    (ht0 : polyVecNorm t0 ≤ 4096) (hE : SpectrumEnvelope spectrumTable65 t0) :
    KeyFloor (concretePrimitives mldsa65)
      (binomialCdfQ (233 / 4096) (mldsa65.k * ringDegree) mldsa65.omega).toNNRat 0 t0 := by
  have := concreteNTTRingLaws
  exact keyFloor_of_spectrumEnvelope floorParams_mldsa65 (by norm_num)
    (sampleInBallShape_concrete mldsa65) ht0 hE concaveTable_spectrumTable65
    (by norm_num [ringDegree]) (incrementTable_le_succ _ 4) (by norm_num) (by norm_num)
    (by simpa using shiftBoundMax_spectrumTable65_le)

/-- **The exact floor at the constant cut-off at ML-DSA-87**: a key with `‖t₀‖∞ ≤ 2^12` under the
table has the floor at `Pr[Bin(2048, 15/256) ≤ 75]` with defect `0`. -/
theorem keyFloor_mldsa87_of_spectrumEnvelope {t0 : RqVec mldsa87.k}
    (ht0 : polyVecNorm t0 ≤ 4096) (hE : SpectrumEnvelope spectrumTable87 t0) :
    KeyFloor (concretePrimitives mldsa87)
      (binomialCdfQ (15 / 256) (mldsa87.k * ringDegree) mldsa87.omega).toNNRat 0 t0 := by
  have := concreteNTTRingLaws
  exact keyFloor_of_spectrumEnvelope floorParams_mldsa87 (by norm_num)
    (sampleInBallShape_concrete mldsa87) ht0 hE concaveTable_spectrumTable87
    (by norm_num [ringDegree]) (incrementTable_le_succ _ 4) (by norm_num) (by norm_num)
    (by simpa using shiftBoundMax_spectrumTable87_le)

/-! ### The shaped cut-offs -/

/-- **The shaped cut-off at ML-DSA-65** of a public `x̂ ≤ 233 / 4096`. -/
abbrev shapedCutoff65 (xhat : CommitHashBytes mldsa65 → ℚ≥0) (hx : ∀ c, xhat c ≤ 233 / 4096) :
    Cutoff mldsa65 :=
  shapedCutoff mldsa65 xhat fun c => (hx c).trans_lt (by norm_num)

/-- **The shaped cut-off at ML-DSA-87** of a public `x̂ ≤ 15 / 256`. -/
abbrev shapedCutoff87 (xhat : CommitHashBytes mldsa87 → ℚ≥0) (hx : ∀ c, xhat c ≤ 15 / 256) :
    Cutoff mldsa87 :=
  shapedCutoff mldsa87 xhat fun c => (hx c).trans_lt (by norm_num)

/-- **The mean shape at ML-DSA-65** is at least `2^-14`. -/
theorem one_div_two_pow_le_meanShape_shapedCutoff65 (xhat : CommitHashBytes mldsa65 → ℚ≥0)
    (hx : ∀ c, xhat c ≤ 233 / 4096) : 1 / 2 ^ 14 ≤ (shapedCutoff65 xhat hx).meanShape := by
  obtain ⟨hk, -, -, -, -, hω⟩ := mldsa65_vals
  have h1 : (233 / 4096 : ℚ≥0) < 1 := by norm_num
  have h := binomialCdf_le_meanShape_shapedCutoff (fun c => (hx c).trans_lt h1) hx h1.le
  have e : (((233 / 4096 : ℚ≥0) : ℚ) : ℝ) = 233 / 4096 := by norm_num
  rw [e, hk, hω] at h
  exact two_pow_neg_le_binomialCdf_1536_55.trans h

/-- **The mean shape at ML-DSA-87** is at least `2^-18`. -/
theorem one_div_two_pow_le_meanShape_shapedCutoff87 (xhat : CommitHashBytes mldsa87 → ℚ≥0)
    (hx : ∀ c, xhat c ≤ 15 / 256) : 1 / 2 ^ 18 ≤ (shapedCutoff87 xhat hx).meanShape := by
  obtain ⟨hk, -, -, -, -, hω⟩ := mldsa87_vals
  have h1 : (15 / 256 : ℚ≥0) < 1 := by norm_num
  have h := binomialCdf_le_meanShape_shapedCutoff (fun c => (hx c).trans_lt h1) hx h1.le
  have e : (((15 / 256 : ℚ≥0) : ℚ) : ℝ) = 15 / 256 := by norm_num
  rw [e, hk, hω] at h
  exact two_pow_neg_le_binomialCdf_2048_75.trans h

/-! ### The computed shapes and key checks -/

/-- The scale `2^40` of the fixed-point spectrum in the computed shape and the key check. -/
def spectrumScaleBits : ℕ := 40

/-- The denominator `2^32` of the computed shape. -/
def shapeDenomBits : ℕ := 32

/-- **The computed shape at ML-DSA-65**: `xhatFix` of the challenge at `P = 40`, `L = 32`, capped
at `233 / 4096`. -/
def xhat65 : CommitHashBytes mldsa65 → ℚ≥0 :=
  shapedXhat (concretePrimitives mldsa65) spectrumScaleBits shapeDenomBits spectrumIncrements65
    (233 / 4096)

/-- **The computed shape at ML-DSA-87**: `xhatFix` of the challenge at `P = 40`, `L = 32`, capped
at `15 / 256`. -/
def xhat87 : CommitHashBytes mldsa87 → ℚ≥0 :=
  shapedXhat (concretePrimitives mldsa87) spectrumScaleBits shapeDenomBits spectrumIncrements87
    (15 / 256)

/-- The computed shape at ML-DSA-65 is at most `233 / 4096`. -/
theorem xhat65_le (c : CommitHashBytes mldsa65) : xhat65 c ≤ 233 / 4096 :=
  shapedXhat_le _ _ _ _ _ c

/-- The computed shape at ML-DSA-87 is at most `15 / 256`. -/
theorem xhat87_le (c : CommitHashBytes mldsa87) : xhat87 c ≤ 15 / 256 :=
  shapedXhat_le _ _ _ _ _ c

/-- **The shape bound at the computed shape at ML-DSA-65**. -/
theorem shapeBound_xhat65 : ShapeBound (concretePrimitives mldsa65) spectrumTable65 xhat65 := by
  obtain ⟨hk, -, -, hg2, hb, -⟩ := mldsa65_vals
  exact shapeBound_shapedXhat (sampleInBallShape_concrete mldsa65) (by rw [hk]; norm_num)
    (by rw [hg2, hb]; norm_num) _ _ (by decide +kernel) (M := 4) (by norm_num [ringDegree])
    (by simpa [spectrumTable65] using shiftBoundMax_spectrumTable65_le)

/-- **The shape bound at the computed shape at ML-DSA-87**. -/
theorem shapeBound_xhat87 : ShapeBound (concretePrimitives mldsa87) spectrumTable87 xhat87 := by
  obtain ⟨hk, -, -, hg2, hb, -⟩ := mldsa87_vals
  exact shapeBound_shapedXhat (sampleInBallShape_concrete mldsa87) (by rw [hk]; norm_num)
    (by rw [hg2, hb]; norm_num) _ _ (by decide +kernel) (M := 4) (by norm_num [ringDegree])
    (by simpa [spectrumTable87] using shiftBoundMax_spectrumTable87_le)

/-- **The computed cut-off at ML-DSA-65**: the shaped cut-off at the computed shape `xhat65`. -/
abbrev computedCutoff65 : Cutoff mldsa65 := shapedCutoff65 xhat65 xhat65_le

/-- **The computed cut-off at ML-DSA-87**: the shaped cut-off at the computed shape `xhat87`. -/
abbrev computedCutoff87 : Cutoff mldsa87 := shapedCutoff87 xhat87 xhat87_le

/-- **The key check at ML-DSA-65**: the spectrum check of `t₀` at `P = 40` against the
increments of `spectrumTable65`. -/
def spectrumCheck65 (t0 : RqVec mldsa65.k) : Bool :=
  spectrumCheck spectrumScaleBits spectrumIncrements65 t0

/-- **The key check at ML-DSA-87**: the spectrum check of `t₀` at `P = 40` against the
increments of `spectrumTable87`. -/
def spectrumCheck87 (t0 : RqVec mldsa87.k) : Bool :=
  spectrumCheck spectrumScaleBits spectrumIncrements87 t0

/-- A key passing the ML-DSA-65 key check is under `spectrumTable65`. -/
theorem spectrumEnvelope_of_spectrumCheck65 {t0 : RqVec mldsa65.k}
    (h : spectrumCheck65 t0 = true) : SpectrumEnvelope spectrumTable65 t0 :=
  spectrumEnvelope_of_spectrumCheck h

/-- A key passing the ML-DSA-87 key check is under `spectrumTable87`. -/
theorem spectrumEnvelope_of_spectrumCheck87 {t0 : RqVec mldsa87.k}
    (h : spectrumCheck87 t0 = true) : SpectrumEnvelope spectrumTable87 t0 :=
  spectrumEnvelope_of_spectrumCheck h

/-- **The public data of the computed shaped cut-off at ML-DSA-65** are valid. -/
theorem shapedSetup_mldsa65 :
    ShapedSetup (concretePrimitives mldsa65) spectrumTable65 xhat65 :=
  shapedSetup_of_floorParams floorParams_mldsa65 (by norm_num) (sampleInBallShape_concrete _)
    (fun c => (xhat65_le c).trans_lt (by norm_num)) shapeBound_xhat65

/-- **The public data of the computed shaped cut-off at ML-DSA-87** are valid. -/
theorem shapedSetup_mldsa87 :
    ShapedSetup (concretePrimitives mldsa87) spectrumTable87 xhat87 :=
  shapedSetup_of_floorParams floorParams_mldsa87 (by norm_num) (sampleInBallShape_concrete _)
    (fun c => (xhat87_le c).trans_lt (by norm_num)) shapeBound_xhat87

/-- A key with `‖t₀‖∞ ≤ 2^12` passing the ML-DSA-65 key check is under `spectrumTable65`. -/
theorem keyUnderTable_of_spectrumCheck65 {t0 : RqVec mldsa65.k} (ht0 : polyVecNorm t0 ≤ 4096)
    (h : spectrumCheck65 t0 = true) : KeyUnderTable spectrumTable65 t0 :=
  ⟨ht0, spectrumEnvelope_of_spectrumCheck65 h⟩

/-- A key with `‖t₀‖∞ ≤ 2^12` passing the ML-DSA-87 key check is under `spectrumTable87`. -/
theorem keyUnderTable_of_spectrumCheck87 {t0 : RqVec mldsa87.k} (ht0 : polyVecNorm t0 ≤ 4096)
    (h : spectrumCheck87 t0 = true) : KeyUnderTable spectrumTable87 t0 :=
  ⟨ht0, spectrumEnvelope_of_spectrumCheck87 h⟩

/-! ### The presentations averaged over a uniform matrix -/

/-- **The presentations at ML-DSA-65 with the shaped cut-off, in the quantum random-oracle model**,
averaged over a uniform matrix and counted on the matrices whose key is under the table: for a
public `x̂ ≤ 233 / 4096` satisfying the shape bound, a sampler `f` within `δ` of the shaped target,
`R` of 64 bytes, every family of query-bounded quantum adversaries all of whose queries are counted,
with `Q` presentations answered, and every group structure on the oracle's values, the advantage
against the simulator program `flatPresentSimProgOf f` is at most `Q / 2^504 + (11 Q + 22) / 2^185 +
Q δ + Q (Q - 1) / 2^513 + 2 t √(Q / 2^512) + 4 Q t / 2^256 + Q (Q - 1) / 2^512`. -/
theorem expect_zkAdvantage_honestPresenter_le_mldsa65_shaped {Ctx : Type} [Fintype Ctx]
    [DecidableEq Ctx] [AddCommGroup (PresOut mldsa65)] (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {xhat : CommitHashBytes mldsa65 → ℚ≥0}
    (hx : ∀ c, xhat c ≤ 233 / 4096)
    (hb : ShapeBound (concretePrimitives mldsa65) spectrumTable65 xhat)
    {C : Type} [Fintype C] [Nonempty C] [DecidableEq C]
    (f : C → BucketVec mldsa65 × CommitHashBytes mldsa65)
    {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget (shapedCutoff65 xhat hx)) ≤ δ)
    (trOf : TqMatrix mldsa65.k mldsa65.l → _root_.MLDSA.Bytes 64) {t Q : ℕ}
    (𝒟 : TqMatrix mldsa65.k mldsa65.l → Quantum.QueryBoundedAdversary
      (PresIn mldsa65 (_root_.MLDSA.Bytes 64) Ctx) (PresOut mldsa65) (QROM.ProofQuery Ctx Unit)
      (Option (Presentation mldsa65)) Bool t) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        {aHat | SpectrumEnvelope spectrumTable65 (matrixKey sk₀ aHat).t0}.indicator
          (fun aHat => (𝒟 aHat).zkAdvantage (fun _ _ => True) (honestPresenterProg (trOf aHat))
            (honestPresenterLaw (concretePrimitives mldsa65) (matrixKey sk₀ aHat) aHat
              (shapedCutoff65 xhat hx))
            (flatPresentSimProgOf f) Q) aHat ≤
      Q / 2 ^ 504 + (11 * Q + 22) / 2 ^ 185 + Q * δ +
        ((Q * (Q - 1) / (2 * 2 ^ 512) + 2 * t * √(Q / 2 ^ 512)) +
          (4 * Q * t / 2 ^ 256 + Q * (Q - 1) / 2 ^ 512)) := by
  have := concreteNTTRingLaws
  have hm := one_div_two_pow_le_meanShape_shapedCutoff65 xhat hx
  have hf : ∀ aHat ∈ {aHat | SpectrumEnvelope spectrumTable65 (matrixKey sk₀ aHat).t0},
      KeyFloorAt (concretePrimitives mldsa65) (shapedCutoff65 xhat hx) 0
        (matrixKey sk₀ aHat).t0 := fun aHat hS =>
    keyFloorAt_shapedCutoff_of_shapeBound floorParams_mldsa65 (by norm_num)
      (sampleInBallShape_concrete _)
      (by simpa only [matrixKey_eq] using polyVecNorm_matrixKey_t0_le sk₀ aHat) hS _ hb
  have h := expect_zkAdvantage_honestPresenter_le_mldsa65_of_keyFloorAt sk₀ hs1 hs2 le_rfl _ hf f
    hδ trOf (Q := Q) 𝒟
  refine h.trans ?_
  simp only [shapedCutoff_top, ENNReal.nnratCast_one, ENNReal.toReal_one, one_mul, sub_zero,
    mul_one, mul_zero, add_zero, one_pow]
  generalize (shapedCutoff65 xhat hx).meanShape = L at hm ⊢
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hm
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hm' : ((1 : ℝ) / 2) ^ 14 ≤ L := by rwa [one_div_pow]
  have hsq : √((1 / 2) ^ 1020 / L) ≤ (1 / 2) ^ 503 := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hL]
    calc ((1 : ℝ) / 2) ^ 1020 = ((1 / 2) ^ 503) ^ 2 * (1 / 2) ^ 14 := by
          rw [← pow_mul, ← pow_add]
      _ ≤ ((1 / 2) ^ 503) ^ 2 * L := mul_le_mul_of_nonneg_left hm' (by positivity)
  have h1 : Q * √((1 / 2) ^ 1020 / L) / 2 ≤ Q / 2 ^ 504 := by
    calc Q * √((1 / 2) ^ 1020 / L) / 2 ≤ Q * (1 / 2) ^ 503 / 2 := by gcongr
      _ = Q / 2 ^ 504 := by rw [one_div_pow, mul_one_div, div_div, ← pow_succ]
  have h2 : (11 * Q + 22) / 2 ^ 199 / L ≤ (11 * Q + 22) / 2 ^ 185 := by
    rw [div_le_iff₀ hL]
    calc (11 * Q + 22 : ℝ) / 2 ^ 199 = (11 * Q + 22) / 2 ^ 185 * (1 / 2 ^ 14) := by
          rw [mul_one_div, div_div, ← pow_add]
      _ ≤ (11 * Q + 22) / 2 ^ 185 * L := mul_le_mul_of_nonneg_left hm (by positivity)
  exact add_le_add (add_le_add (add_le_add h1 h2) le_rfl) le_rfl

/-- **The presentations at ML-DSA-87 with the shaped cut-off, in the quantum random-oracle model**,
averaged over a uniform matrix and counted on the matrices whose key is under the table: for a
public `x̂ ≤ 15 / 256` satisfying the shape bound, a sampler `f` within `δ` of the shaped target,
`R` of 64 bytes, every family of query-bounded quantum adversaries all of whose queries are counted,
with `Q` presentations answered, and every group structure on the oracle's values, the advantage
against the simulator program `flatPresentSimProgOf f` is at most `Q / 2^758 + (12 Q + 24) / 2^276 +
Q δ + Q (Q - 1) / 2^513 + 2 t √(Q / 2^512) + 4 Q t / 2^256 + Q (Q - 1) / 2^512`. -/
theorem expect_zkAdvantage_honestPresenter_le_mldsa87_shaped {Ctx : Type} [Fintype Ctx]
    [DecidableEq Ctx] [AddCommGroup (PresOut mldsa87)] (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {xhat : CommitHashBytes mldsa87 → ℚ≥0}
    (hx : ∀ c, xhat c ≤ 15 / 256)
    (hb : ShapeBound (concretePrimitives mldsa87) spectrumTable87 xhat)
    {C : Type} [Fintype C] [Nonempty C] [DecidableEq C]
    (f : C → BucketVec mldsa87 × CommitHashBytes mldsa87)
    {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget (shapedCutoff87 xhat hx)) ≤ δ)
    (trOf : TqMatrix mldsa87.k mldsa87.l → _root_.MLDSA.Bytes 64) {t Q : ℕ}
    (𝒟 : TqMatrix mldsa87.k mldsa87.l → Quantum.QueryBoundedAdversary
      (PresIn mldsa87 (_root_.MLDSA.Bytes 64) Ctx) (PresOut mldsa87) (QROM.ProofQuery Ctx Unit)
      (Option (Presentation mldsa87)) Bool t) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        {aHat | SpectrumEnvelope spectrumTable87 (matrixKey sk₀ aHat).t0}.indicator
          (fun aHat => (𝒟 aHat).zkAdvantage (fun _ _ => True) (honestPresenterProg (trOf aHat))
            (honestPresenterLaw (concretePrimitives mldsa87) (matrixKey sk₀ aHat) aHat
              (shapedCutoff87 xhat hx))
            (flatPresentSimProgOf f) Q) aHat ≤
      Q / 2 ^ 758 + (12 * Q + 24) / 2 ^ 276 + Q * δ +
        ((Q * (Q - 1) / (2 * 2 ^ 512) + 2 * t * √(Q / 2 ^ 512)) +
          (4 * Q * t / 2 ^ 256 + Q * (Q - 1) / 2 ^ 512)) := by
  have := concreteNTTRingLaws
  have hm := one_div_two_pow_le_meanShape_shapedCutoff87 xhat hx
  have hf : ∀ aHat ∈ {aHat | SpectrumEnvelope spectrumTable87 (matrixKey sk₀ aHat).t0},
      KeyFloorAt (concretePrimitives mldsa87) (shapedCutoff87 xhat hx) 0
        (matrixKey sk₀ aHat).t0 := fun aHat hS =>
    keyFloorAt_shapedCutoff_of_shapeBound floorParams_mldsa87 (by norm_num)
      (sampleInBallShape_concrete _)
      (by simpa only [matrixKey_eq] using polyVecNorm_matrixKey_t0_le sk₀ aHat) hS _ hb
  have h := expect_zkAdvantage_honestPresenter_le_mldsa87_of_keyFloorAt sk₀ hs1 hs2 le_rfl _ hf f
    hδ trOf (Q := Q) 𝒟
  refine h.trans ?_
  simp only [shapedCutoff_top, ENNReal.nnratCast_one, ENNReal.toReal_one, one_mul, sub_zero,
    mul_one, mul_zero, add_zero, one_pow]
  generalize (shapedCutoff87 xhat hx).meanShape = L at hm ⊢
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hm
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hm' : ((1 : ℝ) / 2) ^ 18 ≤ L := by rwa [one_div_pow]
  have hsq : √((1 / 2) ^ 1533 / L) ≤ (1 / 2) ^ 757 := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hL]
    calc ((1 : ℝ) / 2) ^ 1533 ≤ ((1 / 2) ^ 757) ^ 2 * (1 / 2) ^ 18 := by
          rw [← pow_mul, ← pow_add]
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
      _ ≤ ((1 / 2) ^ 757) ^ 2 * L := mul_le_mul_of_nonneg_left hm' (by positivity)
  have h1 : Q * √((1 / 2) ^ 1533 / L) / 2 ≤ Q / 2 ^ 758 := by
    calc Q * √((1 / 2) ^ 1533 / L) / 2 ≤ Q * (1 / 2) ^ 757 / 2 := by gcongr
      _ = Q / 2 ^ 758 := by rw [one_div_pow, mul_one_div, div_div, ← pow_succ]
  have h2 : (12 * Q + 24) / 2 ^ 294 / L ≤ (12 * Q + 24) / 2 ^ 276 := by
    rw [div_le_iff₀ hL]
    calc (12 * Q + 24 : ℝ) / 2 ^ 294 = (12 * Q + 24) / 2 ^ 276 * (1 / 2 ^ 18) := by
          rw [mul_one_div, div_div, ← pow_add]
      _ ≤ (12 * Q + 24) / 2 ^ 276 * L := mul_le_mul_of_nonneg_left hm (by positivity)
  exact add_le_add (add_le_add (add_le_add h1 h2) le_rfl) le_rfl

/-! ### The presentations at the computed cut-offs -/

/-- **The presentations at ML-DSA-65 with the computed cut-off, in the quantum random-oracle
model**, averaged over a uniform matrix and counted on the matrices whose key is under the table:
for a sampler `f` within `δ` of the target of `computedCutoff65`, `R` of 64 bytes, every family of
query-bounded quantum adversaries all of whose queries are counted, with `Q` presentations answered,
and every group structure on the oracle's values, the advantage against the simulator program
`flatPresentSimProgOf f` is at most `Q / 2^504 + (11 Q + 22) / 2^185 + Q δ + Q (Q - 1) / 2^513 + 2 t
√(Q / 2^512) + 4 Q t / 2^256 + Q (Q - 1) / 2^512`. -/
theorem expect_zkAdvantage_honestPresenter_le_mldsa65_computedShape {Ctx : Type} [Fintype Ctx]
    [DecidableEq Ctx] [AddCommGroup (PresOut mldsa65)] (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {C : Type} [Fintype C] [Nonempty C] [DecidableEq C]
    (f : C → BucketVec mldsa65 × CommitHashBytes mldsa65)
    {δ : ℝ} (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget computedCutoff65) ≤ δ)
    (trOf : TqMatrix mldsa65.k mldsa65.l → _root_.MLDSA.Bytes 64) {t Q : ℕ}
    (𝒟 : TqMatrix mldsa65.k mldsa65.l → Quantum.QueryBoundedAdversary
      (PresIn mldsa65 (_root_.MLDSA.Bytes 64) Ctx) (PresOut mldsa65) (QROM.ProofQuery Ctx Unit)
      (Option (Presentation mldsa65)) Bool t) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        {aHat | SpectrumEnvelope spectrumTable65 (matrixKey sk₀ aHat).t0}.indicator
          (fun aHat => (𝒟 aHat).zkAdvantage (fun _ _ => True) (honestPresenterProg (trOf aHat))
            (honestPresenterLaw (concretePrimitives mldsa65) (matrixKey sk₀ aHat) aHat
              computedCutoff65)
            (flatPresentSimProgOf f) Q) aHat ≤
      Q / 2 ^ 504 + (11 * Q + 22) / 2 ^ 185 + Q * δ +
        ((Q * (Q - 1) / (2 * 2 ^ 512) + 2 * t * √(Q / 2 ^ 512)) +
          (4 * Q * t / 2 ^ 256 + Q * (Q - 1) / 2 ^ 512)) :=
  expect_zkAdvantage_honestPresenter_le_mldsa65_shaped sk₀ hs1 hs2 xhat65_le shapeBound_xhat65 f
    hδ trOf 𝒟

/-- **The presentations at ML-DSA-87 with the computed cut-off, in the quantum random-oracle
model**, averaged over a uniform matrix and counted on the matrices whose key is under the table:
for a sampler `f` within `δ` of the target of `computedCutoff87`, `R` of 64 bytes, every family of
query-bounded quantum adversaries all of whose queries are counted, with `Q` presentations answered,
and every group structure on the oracle's values, the advantage against the simulator program
`flatPresentSimProgOf f` is at most `Q / 2^758 + (12 Q + 24) / 2^276 + Q δ + Q (Q - 1) / 2^513 + 2 t
√(Q / 2^512) + 4 Q t / 2^256 + Q (Q - 1) / 2^512`. -/
theorem expect_zkAdvantage_honestPresenter_le_mldsa87_computedShape {Ctx : Type} [Fintype Ctx]
    [DecidableEq Ctx] [AddCommGroup (PresOut mldsa87)] (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {C : Type} [Fintype C] [Nonempty C] [DecidableEq C]
    (f : C → BucketVec mldsa87 × CommitHashBytes mldsa87)
    {δ : ℝ} (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget computedCutoff87) ≤ δ)
    (trOf : TqMatrix mldsa87.k mldsa87.l → _root_.MLDSA.Bytes 64) {t Q : ℕ}
    (𝒟 : TqMatrix mldsa87.k mldsa87.l → Quantum.QueryBoundedAdversary
      (PresIn mldsa87 (_root_.MLDSA.Bytes 64) Ctx) (PresOut mldsa87) (QROM.ProofQuery Ctx Unit)
      (Option (Presentation mldsa87)) Bool t) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        {aHat | SpectrumEnvelope spectrumTable87 (matrixKey sk₀ aHat).t0}.indicator
          (fun aHat => (𝒟 aHat).zkAdvantage (fun _ _ => True) (honestPresenterProg (trOf aHat))
            (honestPresenterLaw (concretePrimitives mldsa87) (matrixKey sk₀ aHat) aHat
              computedCutoff87)
            (flatPresentSimProgOf f) Q) aHat ≤
      Q / 2 ^ 758 + (12 * Q + 24) / 2 ^ 276 + Q * δ +
        ((Q * (Q - 1) / (2 * 2 ^ 512) + 2 * t * √(Q / 2 ^ 512)) +
          (4 * Q * t / 2 ^ 256 + Q * (Q - 1) / 2 ^ 512)) :=
  expect_zkAdvantage_honestPresenter_le_mldsa87_shaped sk₀ hs1 hs2 xhat87_le shapeBound_xhat87 f
    hδ trOf 𝒟

end GordieHowe.MLDSA
