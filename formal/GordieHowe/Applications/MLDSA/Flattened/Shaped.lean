-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.PresentationBound
public import GordieHowe.Applications.MLDSA.Regularity.ShiftSpectrum
public import GordieHowe.Headline

public section

/-!
# The shaped cut-off

With `N = 256 k` and `D = 2 (γ₂ − β) − 1`, a public function `x̂` of the commitment hash with
values below one gives the cut-off `shapedCutoff p x̂` of level one whose value at `c̃` is the
binomial probability `Pr[Bin(N, x̂ c̃) ≤ ω]`. The condition `ShapeBound prims E x̂` asks that
`N D² (x̂ c̃)²` bound the shift bound of the challenge at every `c̃` under a public table `E`; it
involves `x̂`, `E` and `SampleInBall`, and no key.

* `ShapedSetup`, `KeyUnderTable`: the public data of a shaped cut-off are valid, and a key is
  under the table.
* `keyFloorAt_shapedCutoff`: for valid public data and a key under the table `E`, the shaped
  cut-off is below the check weight at every commitment hash, so the floor holds at it with
  defect `0`.
* `shapeBound_const`, `ShapeBound.min`: under a concave table the fill condition gives the bound
  at a constant, and the bound is closed under pointwise minimum.
* `shapedXhat`, `shapeBound_shapedXhat`: the computed shape `xhatFix` of the challenge capped
  at `x_max` satisfies the shape bound under the table of antitone increments.
* `binomialCdf_le_meanShape_shapedCutoff`: `x̂ ≤ x_max` bounds the mean shape below by
  `Pr[Bin(N, x_max) ≤ ω]`.
* `keyFloor_of_spectrumEnvelope`: the constant cut-off `Pr[Bin(N, x) ≤ ω]` under the fill
  condition at `x`.
* `zeroKnowledge_presentations_shaped`: zero knowledge of the presentations in the quantum
  random-oracle model at the shaped cut-off.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF GordieHowe.MLDSA.Regularity GordieHowe.ROM.NIZK
open scoped ENNReal BigOperators

variable {p : Params}

/-- **The shaped cut-off** of a public function `x̂` of the commitment hash with values below 1:
level 1 and, at `c̃`, the binomial probability `Pr[Bin(N, x̂ c̃) ≤ ω]`. -/
@[expose] def shapedCutoff (p : Params) (xhat : CommitHashBytes p → ℚ≥0) (h : ∀ c, xhat c < 1) :
    Cutoff p where
  top := 1
  shape c := (binomialCdfQ (xhat c) (p.k * ringDegree) p.omega).toNNRat
  shape_ne_zero c := (Rat.toNNRat_pos.2 (binomialCdfQ_pos (NNRat.cast_nonneg _)
    (by exact_mod_cast h c) _ _)).ne'
  shape_le_one c := by
    simpa using (Rat.toNNRat_le_toNNRat_iff zero_le_one).2
      (binomialCdfQ_le_one (NNRat.cast_nonneg _) (by exact_mod_cast (h c).le) _ _)
  val c := (binomialCdfQ (xhat c) (p.k * ringDegree) p.omega).toNNRat
  val_eq _ := (one_mul _).symm

section Projections

variable (xhat : CommitHashBytes p → ℚ≥0) (h : ∀ c, xhat c < 1) (c : CommitHashBytes p)

/-- The level of the shaped cut-off is one. -/
@[simp] theorem shapedCutoff_top : (shapedCutoff p xhat h).top = 1 := rfl

/-- The shape of the shaped cut-off. -/
@[simp] theorem shapedCutoff_shape :
    (shapedCutoff p xhat h).shape c = (binomialCdfQ (xhat c) (p.k * ringDegree) p.omega).toNNRat :=
  rfl

/-- The value of the shaped cut-off. -/
@[simp] theorem shapedCutoff_val :
    (shapedCutoff p xhat h).val c = (binomialCdfQ (xhat c) (p.k * ringDegree) p.omega).toNNRat :=
  rfl

end Projections

/-- **The shape bound**: at every commitment hash, `N · D² · (x̂ c̃)²` is at least the shift bound
of the challenge at `c̃` under the table `E`. A condition on the public function `x̂`, the table and
`SampleInBall`; no key appears in it. -/
def ShapeBound (prims : Primitives p) (E : ℕ → ℝ) (xhat : CommitHashBytes p → ℚ≥0) : Prop :=
  ∀ c, shiftBound E (centeredPoly (prims.sampleInBall c)) ≤
    (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 * ((xhat c : ℚ) : ℝ) ^ 2

/-- **The public data of a shaped cut-off are valid**: the parameter set admits the acceptance
floor (`FloorParams` at some `x₀ ≤ 1/2` and `κ`), `SampleInBall` has the shape the floor reads,
and the public function `x̂` is below 1 and satisfies the shape bound for the table `E`. No key
appears in it. -/
structure ShapedSetup (prims : Primitives p) (E : ℕ → ℝ) (xhat : CommitHashBytes p → ℚ≥0) :
    Prop where
  /-- The parameter conditions of the acceptance floor hold at some `x₀ ≤ 1/2`. -/
  floorParams : ∃ x₀ κ : ℝ, FloorParams p x₀ κ ∧ x₀ ≤ 1 / 2
  /-- `SampleInBall` outputs are ternary of weight at most `τ`. -/
  sampleInBallShape : SampleInBallShape prims
  /-- `x̂` is below 1 at every commitment hash. -/
  xhat_lt_one : ∀ c, xhat c < 1
  /-- `x̂` satisfies the shape bound for the table. -/
  shapeBound : ShapeBound prims E xhat

/-- **The shaped cut-off of valid public data**: `shapedCutoff` of `x̂`. -/
abbrev ShapedSetup.cutoff {prims : Primitives p} {E : ℕ → ℝ} {xhat : CommitHashBytes p → ℚ≥0}
    (S : ShapedSetup prims E xhat) : Cutoff p :=
  shapedCutoff p xhat S.xhat_lt_one

/-- **A key under the table `E`**: `‖t₀‖∞ ≤ 2^12` and every sum of `m` values of the key spectrum
is at most `E m`. A condition on `t₀` and the table alone, decided from `t₀`. -/
structure KeyUnderTable {k : ℕ} (E : ℕ → ℝ) (t0 : RqVec k) : Prop where
  /-- The coefficients of `t₀` are at most `2^12` in absolute value. -/
  norm_le : polyVecNorm t0 ≤ 4096
  /-- The key spectrum is under the envelope. -/
  spectrumEnvelope : SpectrumEnvelope E t0

/-- The public data of a shaped cut-off from the floor parameters at `x₀ ≤ 1/2`, the shape of
`SampleInBall`, `x̂ < 1` and the shape bound. -/
theorem shapedSetup_of_floorParams {x₀ κ : ℝ} (hf : FloorParams p x₀ κ) (hx₀ : x₀ ≤ 1 / 2)
    {prims : Primitives p} (hshape : SampleInBallShape prims) {E : ℕ → ℝ}
    {xhat : CommitHashBytes p → ℚ≥0} (h : ∀ c, xhat c < 1) (hb : ShapeBound prims E xhat) :
    ShapedSetup prims E xhat :=
  ⟨⟨x₀, κ, hf, hx₀⟩, hshape, h, hb⟩

/-- **The shape bound is closed under pointwise minimum**, so a function satisfying it may be
capped at another one, such as a constant. -/
theorem ShapeBound.min {prims : Primitives p} {E : ℕ → ℝ} {x₁ x₂ : CommitHashBytes p → ℚ≥0}
    (h₁ : ShapeBound prims E x₁) (h₂ : ShapeBound prims E x₂) :
    ShapeBound prims E fun c => min (x₁ c) (x₂ c) := fun c => by
  dsimp only
  rcases min_cases (x₁ c) (x₂ c) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · exact h₁ c
  · exact h₂ c

/-- **The shape bound at a constant**: for `SampleInBall` of the shape of FIPS 204 and a concave
table `E` with `E M ≤ E (M + 1)`, `M < n`, the fill condition `shiftBoundMax E τ M ≤ N · D² · x²`
gives the shape bound at the constant `x`. -/
theorem shapeBound_const [NeZero (bucketCount p)] [Nonempty (MaskBox p)]
    {prims : Primitives p} (hshape : SampleInBallShape prims) {E : ℕ → ℝ}
    (hE : ConcaveTable E ringDegree) {M : ℕ} (hM : M < ringDegree) (hinc : E M ≤ E (M + 1))
    {x : ℚ≥0}
    (hx : shiftBoundMax E p.tau M ≤
      (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 * ((x : ℚ) : ℝ) ^ 2) :
    ShapeBound prims E fun _ => x := fun c =>
  (shiftBound_le_shiftBoundMax (hshape.norm_le_one c) (hshape.weight_le c) hE hM hinc).trans hx

/-- **The computed shape**: at `c̃`, the computed shape `xhatFix` of the challenge, capped at
`x_max`. -/
def shapedXhat (prims : Primitives p) (P L : ℕ) (l : List ℕ) (xmax : ℚ≥0) :
    CommitHashBytes p → ℚ≥0 :=
  fun c => min xmax (xhatFix p P L l (centeredPoly (prims.sampleInBall c)))

/-- The computed shape is at most its cap. -/
theorem shapedXhat_le (prims : Primitives p) (P L : ℕ) (l : List ℕ) (xmax : ℚ≥0)
    (c : CommitHashBytes p) : shapedXhat prims P L l xmax c ≤ xmax :=
  min_le_left _ _

/-- **The shape bound at the computed shape**: for `SampleInBall` of the shape of FIPS 204,
antitone increments `l`, `0 < k`, `β < γ₂`, `M < n` and the fill condition at `x_max`, the
computed shape satisfies the shape bound under `incrementTable l`. -/
theorem shapeBound_shapedXhat [NeZero (bucketCount p)] [Nonempty (MaskBox p)]
    {prims : Primitives p} (hshape : SampleInBallShape prims) (hk : 0 < p.k)
    (hβ : p.beta < p.gamma2) (P L : ℕ) {l : List ℕ} (hl : l.antitoneB = true) {M : ℕ}
    (hM : M < ringDegree) {xmax : ℚ≥0}
    (hx : shiftBoundMax (incrementTable l) p.tau M ≤
      (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 *
        ((xmax : ℚ) : ℝ) ^ 2) :
    ShapeBound prims (incrementTable l) (shapedXhat prims P L l xmax) :=
  (shapeBound_const hshape (concaveTable_incrementTable hl _) hM (incrementTable_le_succ l M)
    hx).min fun _ => shiftBound_le_xhatFix hk hβ P L hl _

/-- **The mean shape of the shaped cut-off**: if `x̂ ≤ x_max ≤ 1` at every commitment hash, the
mean shape is at least `Pr[Bin(N, x_max) ≤ ω]`. -/
theorem binomialCdf_le_meanShape_shapedCutoff {xhat : CommitHashBytes p → ℚ≥0}
    (h : ∀ c, xhat c < 1) {xmax : ℚ≥0} (hx : ∀ c, xhat c ≤ xmax) (hx1 : xmax ≤ 1) :
    binomialCdf ((xmax : ℚ) : ℝ) (p.k * ringDegree) p.omega ≤
      (shapedCutoff p xhat h).meanShape := by
  refine Cutoff.le_meanShape _ fun c => ?_
  have hq0 : 0 ≤ binomialCdfQ (xhat c) (p.k * ringDegree) p.omega :=
    (binomialCdfQ_pos (NNRat.cast_nonneg _) (by exact_mod_cast h c) _ _).le
  have hle := binomialCdfQ_anti_prob (NNRat.cast_nonneg _) (by exact_mod_cast hx c :
    ((xhat c : ℚ)) ≤ xmax) (by exact_mod_cast hx1) (p.k * ringDegree) p.omega
  have e : (((binomialCdfQ (xhat c) (p.k * ringDegree) p.omega).toNNRat : ℚ≥0) : ℝ) =
      (binomialCdfQ (xhat c) (p.k * ringDegree) p.omega : ℝ) := by
    rw [← Rat.cast_nnratCast (K := ℝ), Rat.coe_toNNRat _ hq0]
  rw [shapedCutoff_shape, e]
  exact_mod_cast hle

section Floor

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [nttOps : NTTRingOps]
  [NTTRingLaws nttOps]

/-- **The exact floor at the shaped cut-off**: for `SampleInBall` of the shape of FIPS 204, a key
with `‖t₀‖∞ ≤ 2^12` under the spectrum envelope `E`, and `x̂` satisfying the shape bound, the
shaped cut-off is below the check weight at every commitment hash, so the floor holds at it with
defect `0`. -/
theorem keyFloorAt_shapedCutoff_of_shapeBound {x₀ κ : ℝ} (hf : FloorParams p x₀ κ)
    (hx₀ : x₀ ≤ 1 / 2) {prims : Primitives p} (hshape : SampleInBallShape prims) {t0 : RqVec p.k}
    (ht0 : polyVecNorm t0 ≤ 4096) {E : ℕ → ℝ} (hE : SpectrumEnvelope E t0)
    {xhat : CommitHashBytes p → ℚ≥0} (h : ∀ c, xhat c < 1) (hb : ShapeBound prims E xhat) :
    KeyFloorAt prims (shapedCutoff p xhat h) 0 t0 :=
  KeyFloorAt.of_le_checkWeight (by simp) (by simp) fun c =>
    toNNRat_binomialCdfQ_le_checkWeight hf hx₀ prims hshape t0 ht0 hE c (NNRat.cast_nonneg _)
      (by exact_mod_cast (h c).le) (hb c)

/-- **The exact floor at the shaped cut-off**: for valid public data of a shaped cut-off and a key
under the table `E`, the shaped cut-off is below the check weight at every commitment hash, so the
floor holds at it with defect `0`. -/
@[headline]
theorem keyFloorAt_shapedCutoff {prims : Primitives p} {E : ℕ → ℝ}
    {xhat : CommitHashBytes p → ℚ≥0} (S : ShapedSetup prims E xhat) {t0 : RqVec p.k}
    (K : KeyUnderTable E t0) :
    KeyFloorAt prims S.cutoff 0 t0 :=
  let ⟨_, _, hf, hx₀⟩ := S.floorParams
  keyFloorAt_shapedCutoff_of_shapeBound hf hx₀ S.sampleInBallShape K.norm_le K.spectrumEnvelope
    S.xhat_lt_one S.shapeBound

/-- **The exact floor at a constant cut-off**: for `SampleInBall` of the shape of FIPS 204, a key
with `‖t₀‖∞ ≤ 2^12` under a concave spectrum envelope `E` with `E M ≤ E (M + 1)`, `M < n`, and
a rational `x ∈ [0, 1)` with `shiftBoundMax E τ M ≤ N · D² · x²`, the floor holds at the constant
cut-off `Pr[Bin(N, x) ≤ ω]` with defect `0`. -/
theorem keyFloor_of_spectrumEnvelope {x₀ κ : ℝ} (hf : FloorParams p x₀ κ) (hx₀ : x₀ ≤ 1 / 2)
    {prims : Primitives p} (hshape : SampleInBallShape prims) {t0 : RqVec p.k}
    (ht0 : polyVecNorm t0 ≤ 4096) {E : ℕ → ℝ} (hE : SpectrumEnvelope E t0)
    (hEc : ConcaveTable E ringDegree) {M : ℕ} (hM : M < ringDegree) (hinc : E M ≤ E (M + 1))
    {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hx : shiftBoundMax E p.tau M ≤
      (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 * (x : ℝ) ^ 2) :
    KeyFloor prims (binomialCdfQ x (p.k * ringDegree) p.omega).toNNRat 0 t0 := by
  have hpos := binomialCdfQ_pos hx0 hx1 (p.k * ringDegree) p.omega
  refine keyFloorAt_const_iff.1 (KeyFloorAt.of_le_checkWeight ?_ ?_ fun c =>
    toNNRat_binomialCdfQ_le_checkWeight_of_shiftBoundMax hf hx₀ prims hshape t0 ht0 hE hEc hM
      hinc hx0 hx1.le hx c)
  · exact ENNReal.nnratCast_ne_zero.2 (Rat.toNNRat_pos.2 hpos).ne'
  · have h1 := (Rat.toNNRat_le_toNNRat_iff zero_le_one).2 (binomialCdfQ_le_one hx0 hx1.le
      (p.k * ringDegree) p.omega)
    rw [Rat.toNNRat_one] at h1
    exact ENNReal.nnratCast_le_one.2 h1

end Floor

section Presentations

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [nttOps : NTTRingOps] {Rnd Ctx : Type}
  [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd] [Fintype Ctx] [DecidableEq Ctx]

/-- **The presentations of the flattened signer at the shaped cut-off are zero knowledge in the
quantum random-oracle model** (`GordieHowe.QROM.ZeroKnowledge`, query-bounded quantum adversaries
all of whose queries are counted): for `SampleInBall` of the shape of FIPS 204, a key with
`‖t₀‖∞ ≤ 2^12` under the spectrum envelope `E`, `x̂` satisfying the shape bound, and a sampler `f`
whose output on uniform coins is within `δ` of the shaped target, for every group structure on
the oracle's values, the honest presenter's program and the simulator program
`flatPresentSimProgOf f` are within

    Q · (flatOracleConcError + signerRegGap + δ)
      + Q (Q - 1) / (2 |Rnd|) + 2 t √(Q / |Rnd|) + 4 Q t / 2^256 + Q (Q - 1) / 2^512

with `Q` presentations answered (`zeroKnowledge_presentations_of_keyFloorAt`). -/
theorem zeroKnowledge_presentations_shaped_of_shapeBound [AddCommGroup (PresOut p)]
    (tr : _root_.MLDSA.Bytes 64)
    (prims : Primitives p) (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {x₀ κ : ℝ}
    (hf : FloorParams p x₀ κ) (hx₀ : x₀ ≤ 1 / 2) (hshape : SampleInBallShape prims)
    (ht0 : polyVecNorm sk.t0 ≤ 4096) {E : ℕ → ℝ} (hE : SpectrumEnvelope E sk.t0)
    {xhat : CommitHashBytes p → ℚ≥0} (h : ∀ c, xhat c < 1) (hb : ShapeBound prims E xhat)
    {C : Type} [Fintype C] [Nonempty C] [DecidableEq C] (f : C → BucketVec p × CommitHashBytes p)
    {δ : ℝ} (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget (shapedCutoff p xhat h)) ≤ δ) :
    GordieHowe.QROM.ZeroKnowledge (fun (_ : Ctx) (_ : Unit) => True)
      (honestPresenterProg (Rnd := Rnd) tr)
      (honestPresenterLaw prims sk aHat (shapedCutoff p xhat h)) (flatPresentSimProgOf f)
      fun t Q =>
        Q * (flatOracleConcError prims sk aHat (shapedCutoff p xhat h) +
          signerRegGap prims sk aHat (shapedCutoff p xhat h) + δ) +
          (Q * (Q - 1) / (2 * Fintype.card Rnd) + 2 * t * √(Q / Fintype.card Rnd)) +
          (4 * Q * t / 2 ^ 256 + Q * (Q - 1) / 2 ^ 512) := by
  have := h_laws.transform
  have hb' := zeroKnowledge_presentations_of_keyFloorAt (Rnd := Rnd) (Ctx := Ctx) tr prims sk aHat
    (shapedCutoff p xhat h) hp h_laws hs2
    (keyFloorAt_shapedCutoff_of_shapeBound hf hx₀ hshape ht0 hE h hb) f hδ
  simpa only [add_zero, sub_zero, div_one] using hb'

/-- **The presentations of the flattened signer at the shaped cut-off are zero knowledge in the
quantum random-oracle model** (`GordieHowe.QROM.ZeroKnowledge`, query-bounded quantum adversaries
all of whose queries are counted): for valid public data of a shaped cut-off, a key under the
table `E`, and a sampler `f` whose output on uniform coins is within `δ` of the shaped target,
for every group structure on the oracle's values, the honest presenter's program and the
simulator program `flatPresentSimProgOf f` are within

    Q · (flatOracleConcError + signerRegGap + δ)
      + Q (Q - 1) / (2 |Rnd|) + 2 t √(Q / |Rnd|) + 4 Q t / 2^256 + Q (Q - 1) / 2^512

with `Q` presentations answered. -/
@[headline]
theorem zeroKnowledge_presentations_shaped [AddCommGroup (PresOut p)] (tr : _root_.MLDSA.Bytes 64)
    (prims : Primitives p) (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {E : ℕ → ℝ}
    {xhat : CommitHashBytes p → ℚ≥0} (S : ShapedSetup prims E xhat)
    (K : KeyUnderTable E sk.t0) {C : Type} [Fintype C] [Nonempty C] [DecidableEq C]
    (f : C → BucketVec p × CommitHashBytes p) {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget S.cutoff) ≤ δ) :
    GordieHowe.QROM.ZeroKnowledge (fun (_ : Ctx) (_ : Unit) => True)
      (honestPresenterProg (Rnd := Rnd) tr) (honestPresenterLaw prims sk aHat S.cutoff)
      (flatPresentSimProgOf f)
      fun t Q =>
        Q * (flatOracleConcError prims sk aHat S.cutoff + signerRegGap prims sk aHat S.cutoff +
          δ) +
          (Q * (Q - 1) / (2 * Fintype.card Rnd) + 2 * t * √(Q / Fintype.card Rnd)) +
          (4 * Q * t / 2 ^ 256 + Q * (Q - 1) / 2 ^ 512) :=
  let ⟨_, _, hf, hx₀⟩ := S.floorParams
  zeroKnowledge_presentations_shaped_of_shapeBound tr prims sk aHat hp h_laws hs2 hf hx₀
    S.sampleInBallShape K.norm_le K.spectrumEnvelope S.xhat_lt_one S.shapeBound f hδ

end Presentations

end GordieHowe.MLDSA
