-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1AnonQuery

public section

/-!
# Anonymity of the ML-DSA ring publishing `w₁` with three random oracles

The anonymity headlines of `MLDSAW1AnonQuery.lean` with `SampleInBall`, `ExpandS` and `ExpandA`
random oracles `G_B`, `G_S`, `G_A`, averaged over them, and with every term numeric. The adversary
is a family indexed by the three oracles, so it holds them whole; it has `t` superposition queries
to the joint oracle of `H_µ`, `H`, `G`, the mask derivation and the proof system's hash, quantum
memory across rounds and `Q` adaptive challenges.

- `randomOraclePrimitives G_B G_S G_A`: the concrete primitives with the three random oracles
  (`oraclePrimitives`, `withExpandA`). `signingLaws_randomOraclePrimitives`,
  `verifyLaws_randomOraclePrimitives`: their signing and verification laws.
- `W1Oracles.atRandomOracles`: an oracle placement of the concrete primitives at the random-oracle
  primitives (the published keys are the same type). `W1Oracles.UniformSplit.atRandomOracles`,
  `W1Oracles.ReadsFst.atRandomOracles`: its hypotheses carry over.
- `expect_w1CouplingError_randomOracle_le`: the coupling error averaged over the three oracles is
  at most `2 (2 / ((1 - s) θ) · n R + √(N n log (C + 1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) +
  2 k / D + 2 (1 - Lk)^k`, for a bound `R` on the averaged regularity gap: the average of
  `regGapAt` over `G_A` is `regGapAvg` (`expect_regGapAt_withExpandA`), the average of `collAt` is
  at most the collision bound (`expect_collAt_withExpandA_le`), Jensen's inequality for the square
  root (`expect_w1CouplingError_le`) and the McDiarmid numbers (`sqrt_add_sqrt_le_of_le`).
- `w1Scheme.expect_anonAdvantage_le`: the averaged advantage of `w1Scheme` at the random-oracle
  primitives, the concrete encoding and `W1Oracles.atRandomOracles`, at any approved parameter set,
  from `hedgedScheme.anonAdvantage_le_coupling` at each triple of oracles, with keep level
  `Lk = β_min θ (1 - s) / 32` (`mul_div_le_keepLevel`) and check parameters (`CheckParams`).
- `w1Scheme.expect_anonAdvantage_le_mldsa{44,65,87}`: **the headlines** at ML-DSA-44, -65 and -87,
  with the regularity bounds `expect_regGapAvg_le_mldsa{44,65,87}`, and their forms with
  ring-binding (`bmsg := Prod.mk`, `w1Scheme.expect_anonAdvantage_le_bind_mldsa{44,65,87}`) and
  converted (`bmsg := fun _ m => m`, `w1Scheme.expect_anonAdvantage_le_conv_mldsa{44,65,87}`) base
  messages.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity GordieHowe.RingSignature
open scoped ENNReal NNReal BigOperators

attribute [local instance] concreteNTTRingOps

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The primitives with three random oracles -/

section Primitives

/-- **The concrete primitives with `SampleInBall`, `ExpandS` and `ExpandA` random oracles**:
`SampleInBall = G_B` onto `B_τ` and `ExpandS = G_S` onto the coefficient arrays of `η`-bounded
secrets (`oraclePrimitives`), and `ExpandA = G_A` (`withExpandA`). -/
noncomputable abbrev randomOraclePrimitives (GB : CommitHashBytes p → ChallengeBall p.tau)
    (GS : Bytes 64 → SecretCoeffs p) (GA : Bytes 32 → TqMatrix p.k p.l) : Primitives p :=
  withExpandA (oraclePrimitives GB GS) GA

/-- The signing laws hold at the random-oracle primitives of an approved parameter set
(`signingLaws_concreteWithSampleInBallExpandS`, the oracle `G_B` of challenge shape). -/
theorem signingLaws_randomOraclePrimitives [NeZero (bucketCount p)] [Nonempty (MaskBox p)]
    (hp : p.isApproved)
    (GB : CommitHashBytes p → ChallengeBall p.tau) (GS : Bytes 64 → SecretCoeffs p)
    (GA : Bytes 32 → TqMatrix p.k p.l) : SigningLaws (randomOraclePrimitives GB GS GA) :=
  SigningLaws.withExpandA _
    (signingLaws_concreteWithSampleInBallExpandS hp (sampleInBallShape_oraclePrims GB) _) GA

/-- The verification laws hold at the random-oracle primitives of an approved parameter set
(`verifyLaws_concreteWithSampleInBallExpandS`). -/
theorem verifyLaws_randomOraclePrimitives [NeZero (bucketCount p)] [Nonempty (MaskBox p)]
    (hp : p.isApproved)
    (GB : CommitHashBytes p → ChallengeBall p.tau) (GS : Bytes 64 → SecretCoeffs p)
    (GA : Bytes 32 → TqMatrix p.k p.l) : VerifyLaws (randomOraclePrimitives GB GS GA) :=
  VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS hp _ _) GA

/-- **The oracle placement `O` at the random-oracle primitives**: the same points and decodings.
The check oracle's points are rings of published keys `(ρ, t₁, t₀)`, the same type at both
primitives. -/
@[expose] def W1Oracles.atRandomOracles
    (O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps)
    (GB : CommitHashBytes p → ChallengeBall p.tau) (GS : Bytes 64 → SecretCoeffs p)
    (GA : Bytes 32 → TqMatrix p.k p.l) :
    W1Oracles X Y p (randomOraclePrimitives GB GS GA) Msg N reps :=
  ⟨O.muPt, O.muAns, O.chPt, O.chAns, O.gPt, O.gAns⟩

variable {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps}

/-- A domain separation with uniform decodings is one at the random-oracle primitives. -/
theorem W1Oracles.UniformSplit.atRandomOracles [Fintype Y] [Nonempty Y] (hO : O.UniformSplit)
    (GB : CommitHashBytes p → ChallengeBall p.tau) (GS : Bytes 64 → SecretCoeffs p)
    (GA : Bytes 32 → TqMatrix p.k p.l) : (O.atRandomOracles GB GS GA).UniformSplit :=
  ⟨hO.muPt_injective, hO.chPt_injective, hO.gPt_injective, hO.muPt_ne_chPt, hO.muPt_ne_gPt,
    hO.chPt_ne_gPt, hO.map_muAns, hO.map_chAns, hO.map_gAns⟩

/-- Decodings reading only the first component do so at the random-oracle primitives. -/
theorem W1Oracles.ReadsFst.atRandomOracles {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
    {sp : RingSignature.OracleSplit Y Y₁ Y₂} (h : O.ReadsFst sp)
    (GB : CommitHashBytes p → ChallengeBall p.tau) (GS : Bytes 64 → SecretCoeffs p)
    (GA : Bytes 32 → TqMatrix p.k p.l) : (O.atRandomOracles GB GS GA).ReadsFst sp :=
  ⟨h.muAns_eq, h.chAns_eq, h.gAns_eq⟩

end Primitives

/-! ### The coupling error averaged over the oracles -/

section Coupling

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- An average over the three oracles is an average over their triples. -/
theorem expect_oracles_eq_expect_prod
    (f : (CommitHashBytes p → ChallengeBall p.tau) → (Bytes 64 → SecretCoeffs p) →
      (Bytes 32 → TqMatrix p.k p.l) → ℝ) :
    𝔼 GB, 𝔼 GS, 𝔼 GA, f GB GS GA = 𝔼 g : (CommitHashBytes p → ChallengeBall p.tau) ×
      (Bytes 64 → SecretCoeffs p) × (Bytes 32 → TqMatrix p.k p.l), f g.1 g.2.1 g.2.2 := by
  rw [eq_comm, ← Finset.univ_product_univ, Finset.expect_product]
  refine Finset.expect_congr rfl fun GB _ => ?_
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- **The coupling error averaged over `SampleInBall`, `ExpandS` and `ExpandA` random oracles**:
for a bound `R` on `𝔼_{G_B, G_S} regGapAvg`, collision bound at most `2^-4352`, stand-in scale with
`K |V| ≥ 1/16` and `|V| ≥ 2^4100`, `β_min ∈ (0, 1]`, `θ ∈ (0, 1)`, `s < 1` and `n ≥ 1`, the average
of `w1CouplingError` is at most
`2 (2 / ((1 - s) θ) · n R + √(N n log (C + 1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D +
2 (1 - Lk)^k`. The average of `regGapAt` over `G_A` is `regGapAvg` (`expect_regGapAt_withExpandA`);
that of `collAt` is at most the collision bound (`expect_collAt_withExpandA_le`); `collAt` enters
under a square root (`expect_w1CouplingError_le`); the McDiarmid terms are bounded as in
`expect_mcDiarmidTerms_le_of` (`sqrt_add_sqrt_le_of_le` with `ε = 2^-4352`, `L = 1/16` and
`c = 2^-2001`). -/
theorem expect_w1CouplingError_randomOracle_le (hp : p.isApproved) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hs1 : s < 1) (N n : ℕ) [NeZero n] (C k D : ℕ) (Lk : ℝ) {R : ℝ}
    (hR : 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 GS : Bytes 64 → SecretCoeffs p,
      regGapAvg (oraclePrimitives GB GS) βmin ≤ R)
    (hCP : commitCollisionBound p ≤ (1 / 2 ^ 17) ^ ringDegree)
    (hK : 1 / 16 ≤ (standinScale p).toReal * Fintype.card (BucketVec p))
    (hW : (2 : ℝ) ^ 4100 ≤ Fintype.card (BucketVec p)) :
    𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 GS : Bytes 64 → SecretCoeffs p,
      𝔼 GA : Bytes 32 → TqMatrix p.k p.l,
        w1CouplingError (randomOraclePrimitives GB GS GA) βmin N n s θ C k D Lk ≤
      2 * (2 * (1 - s)⁻¹ / θ * (n * R) +
          √(N * n * Real.log (C + 1)) /
            (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
        2 * (k * (D : ℝ)⁻¹) + 2 * (1 - Lk) ^ k := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty (tau_le_ringDegree hp)
  have hβt : (βmin : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hW0 : (0 : ℝ) < Fintype.card (BucketVec p) := lt_of_lt_of_le (by positivity) hW
  have hlog : Real.log C ≤ Real.log (C + 1) := by
    rcases Nat.eq_zero_or_pos C with rfl | hC
    · simp
    · exact Real.log_le_log (by exact_mod_cast hC) (by linarith)
  have hR' : 𝔼 g : (CommitHashBytes p → ChallengeBall p.tau) × (Bytes 64 → SecretCoeffs p) ×
      (Bytes 32 → TqMatrix p.k p.l),
        regGapAt (randomOraclePrimitives g.1 g.2.1 g.2.2) βmin ≤ R := by
    rw [← expect_oracles_eq_expect_prod fun GB GS GA =>
      regGapAt (randomOraclePrimitives GB GS GA) βmin]
    refine le_of_eq_of_le (Finset.expect_congr rfl fun GB _ => Finset.expect_congr rfl fun GS _ =>
      expect_regGapAt_withExpandA (oraclePrimitives GB GS) βmin) hR
  have hε : 𝔼 g : (CommitHashBytes p → ChallengeBall p.tau) × (Bytes 64 → SecretCoeffs p) ×
      (Bytes 32 → TqMatrix p.k p.l),
        collAt (randomOraclePrimitives g.1 g.2.1 g.2.2) ≤ (1 / 2 ^ 17) ^ ringDegree := by
    rw [← expect_oracles_eq_expect_prod fun GB GS GA => collAt (randomOraclePrimitives GB GS GA)]
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      (expect_collAt_withExpandA_le (oraclePrimitives GB GS)
        (SigningParams.of_isApproved hp)).trans hCP).trans_eq ?_
    rw [Finset.expect_const Finset.univ_nonempty, Finset.expect_const Finset.univ_nonempty]
  have hbound : 4 * ((1 / 2 ^ 17) ^ ringDegree) / (1 / 16) ^ 2 +
      4 / (Fintype.card (BucketVec p) : ℝ) ≤ (1 / 2 ^ 2001 : ℝ) ^ 2 := by
    have h4 : 4 / (Fintype.card (BucketVec p) : ℝ) ≤ 4 / 2 ^ 4100 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hW
    change 4 * ((1 / 2 ^ 17 : ℝ) ^ 256) / (1 / 16) ^ 2 + 4 / (Fintype.card (BucketVec p) : ℝ) ≤
      (1 / 2 ^ 2001 : ℝ) ^ 2
    exact (add_le_add le_rfl h4).trans four_mul_div_add_four_div_le
  have hX : 1 / 16 * (βmin : ℝ≥0∞).toReal ≤
      (standinScale p * βmin).toReal * Fintype.card (BucketVec p) := by
    rw [ENNReal.toReal_mul, mul_right_comm]
    exact mul_le_mul_of_nonneg_right hK hb0.le
  have hM := sqrt_add_sqrt_le_of_le (Nat.cast_nonneg N) hn hθ0 hθ1 hs1 hb0 hb1
    (Real.log_natCast_nonneg C) hlog hW0 (by norm_num) (by positivity) (by positivity) hbound hX
  rw [mul_assoc (2 : ℝ) (n : ℝ)] at hM
  have hM' : 2 * (1 / 2 ^ 2001 : ℝ) * √(N * n * Real.log (C + 1)) /
      (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal) =
      √(N * n * Real.log (C + 1)) /
        (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal)) := by
    rw [show (2 : ℝ) ^ 2001 = 2 * 2 ^ 2000 from pow_succ' 2 2000]
    field_simp
  rw [expect_oracles_eq_expect_prod fun GB GS GA =>
    w1CouplingError (randomOraclePrimitives GB GS GA) βmin N n s θ C k D Lk]
  have hE := expect_w1CouplingError_le βmin N n s θ C k D Lk
    (fun g : (CommitHashBytes p → ChallengeBall p.tau) × (Bytes 64 → SecretCoeffs p) ×
      (Bytes 32 → TqMatrix p.k p.l) => randomOraclePrimitives g.1 g.2.1 g.2.2) hs1 hθ0.le hR' hε
  refine hE.trans ?_
  linarith [hM.trans_eq hM']

end Coupling

/-! ### Anonymity averaged over the oracles -/

section Anonymity

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps} {M : MaskOracle X Y p T Msg}
  {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg} {TPS : PSTypes}
  {PS : ∀ (GB : CommitHashBytes p → ChallengeBall p.tau) (GS : Bytes 64 → SecretCoeffs p)
    (GA : Bytes 32 → TqMatrix p.k p.l),
    ProofSystem X Y
      (RingSignature.RingStmt (w1Base p (randomOraclePrimitives GB GS GA) (concreteEnc p)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg))
      (RingSignature.RingWitOf (FIPSSignature p (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [DecidablePred adm] {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂]

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles**, at an approved parameter set: for every family of anonymity
adversaries indexed by the three oracles `G_B`, `G_S`, `G_A`, with `t` superposition queries to the
joint oracle and tables reading its base components only off the mask and check points (`hV`), and
every number `Q` of challenges, the advantage averaged over the three oracles is at most
`Q · (2 (2 / ((1 - s) θ) · n R + √(N n log (C + 1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D +
2 (1 - β_min θ (1 - s) / 32)^k) + Q · wi (Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) +
2 (√Q + 2 t)² / 2^240`, for a bound `R` on `𝔼_{G_B, G_S} regGapAvg` (`hR`), the numbers of the
collision bound and of the bucket vectors of the parameter set (`hCP`, `hK`, `hW`), check
parameters (`hcp`) with `0 ≤ s`, and `θ ∈ (0, 1)`. At each triple of oracles this is
`hedgedScheme.anonAdvantage_le_coupling` at the keep level `β_min θ (1 - s) / 32`
(`mul_div_le_keepLevel`); the coupling error averages by
`expect_w1CouplingError_randomOracle_le`. -/
theorem w1Scheme.expect_anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hp : p.isApproved) (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base p (randomOraclePrimitives GB GS GA) (concreteEnc p)
          (O.atRandomOracles GB GS GA) M βmin tol k D bmsg) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme p (randomOraclePrimitives GB GS GA) (concreteEnc p)
          (O.atRandomOracles GB GS GA) M βmin tol k D bmsg (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {R : ℝ}
    (hR : 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 GS : Bytes 64 → SecretCoeffs p,
      regGapAvg (oraclePrimitives GB GS) βmin ≤ R)
    (hCP : commitCollisionBound p ≤ (1 / 2 ^ 17) ^ ringDegree)
    (hK : 1 / 16 ≤ (standinScale p).toReal * Fintype.card (BucketVec p))
    (hW : (2 : ℝ) ^ 4100 ≤ Fintype.card (BucketVec p)) {t : ℕ}
    (A : ∀ GB GS GA,
      AnonAdversary (w1Scheme p (randomOraclePrimitives GB GS GA) (concreteEnc p)
          (O.atRandomOracles GB GS GA) M βmin tol k D bmsg (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 GS : Bytes 64 → SecretCoeffs p,
      𝔼 GA : Bytes 32 → TqMatrix p.k p.l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * R) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) := by
  have := challengeBall_nonempty (tau_le_ringDegree hp)
  have hβt : (βmin : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  have hs1 := hcp.s_lt_one
  have hLk := mul_div_le_keepLevel hK βmin hθ0.le hs1.le
  have hLk1 : (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32 ≤ 1 := by
    have h1 : (βmin : ℝ≥0∞).toReal * θ * (1 - s) ≤ 1 * 1 * 1 :=
      mul_le_mul (mul_le_mul hb1 hθ1.le hθ0.le zero_le_one) (by linarith) (by linarith)
        (by positivity)
    linarith
  set E : ℝ := Q * wi (Q * C) +
    2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
    2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) with hEdef
  have hcheck : (√(Q : ℝ) + 2 * t) ^ 2 * checkError reps tol s x ≤
      (√(Q : ℝ) + 2 * t) ^ 2 / 2 ^ 240 :=
    (mul_le_mul_of_nonneg_left hcp.checkError_le (sq_nonneg _)).trans_eq (mul_one_div _ _)
  have hpt : ∀ GB GS GA, anonAdvantage (A GB GS GA) Q ≤
      Q * w1CouplingError (randomOraclePrimitives GB GS GA) βmin N n s θ C k D
        ((βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) + E := fun GB GS GA => by
    have h := hedgedScheme.anonAdvantage_le_coupling (randomOraclePrimitives GB GS GA) sp
      (SigningParams.of_isApproved hp) hT hβ0 hβt (hO.atRandomOracles GB GS GA) hMask
      (signingLaws_randomOraclePrimitives hp GB GS GA)
      (verifyLaws_randomOraclePrimitives hp GB GS GA)
      (fun w => concreteEnc_highBitsVec hp w) (fun _ => (secretOfCoeffs_bounded _).2) hM hdisj
      (hsp.atRandomOracles GB GS GA) hMsp (hPS GB GS GA) hV (hwi GB GS GA) (hC GB GS GA) hθ0 hθ1
      hs1 hcp.one_le_x hLk hLk1 (A GB GS GA) Q
    simp only [E]
    linarith
  have hE := expect_w1CouplingError_randomOracle_le hp hβ0 hβ1 hθ0 hθ1 hs1 N n C k D
    ((βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) hR hCP hK hW
  refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
    Finset.expect_le_expect fun GA _ => hpt GB GS GA).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect,
    Finset.expect_const Finset.univ_nonempty]
  linarith [mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg Q), hEdef]

end Anonymity

/-! ### ML-DSA-44, ML-DSA-65 and ML-DSA-87 -/

section Instances

variable [Fintype Msg] [DecidableEq Msg] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y] [Nonempty Y] {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg] {n : ℕ} {Y₁ Y₂ : Type} [AddGroup Y₁] [AddGroup Y₂]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] {TPS : PSTypes}

section P44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D bmsg))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-44 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-44 with the regularity
bound `11 · 2^-101 · (24/5) / β_min`, `expect_regGapAvg_le_mldsa44`): for every family of anonymity
adversaries indexed by the oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t`
superposition queries to the joint oracle of `H_µ`, `H`, `G`, the mask derivation and the proof
system's hash, and tables reading the base components only off the mask and check points, and every
number `Q` of challenges, the advantage averaged over the three oracles is at most `Q · (2 (2 / ((1
- s) θ) · n R + √(N n log (C + 1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1
- s) / 32)^k) + Q · wi (Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240`
with `R` = `11 · 2^-101 · (24/5) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check
parameters (`CheckParams`, for instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_mldsa44 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le sp isApproved_mldsa44 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa44 hβ0 hβ1)
    commitCollisionBound_le_mldsa44 one_div_sixteen_le_standinScale_mul_card_mldsa44
    two_pow_le_card_bucketVec_mldsa44 A Q

end P44

section P44Bind

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-44 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** with ring-binding base messages (`bmsg := Prod.mk`, the base message `(R,
m)`) (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-44 with the regularity bound `11 · 2^-101 ·
(24/5) / β_min`, `expect_regGapAvg_le_mldsa44`): for every family of anonymity adversaries indexed
by the oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t` superposition queries to the
joint oracle of `H_µ`, `H`, `G`, the mask derivation and the proof system's hash, and tables reading
the base components only off the mask and check points, and every number `Q` of challenges, the
advantage averaged over the three oracles is at most `Q · (2 (2 / ((1 - s) θ) · n R + √(N n log (C +
1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1 - s) / 32)^k) + Q · wi (Q · C)
+ 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240` with `R` = `11 · 2^-101 ·
(24/5) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check parameters (`CheckParams`, for
instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_bind_mldsa44 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le (bmsg := Prod.mk) (PS := PS) sp
    isApproved_mldsa44 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa44 hβ0 hβ1)
    commitCollisionBound_le_mldsa44 one_div_sixteen_le_standinScale_mul_card_mldsa44
    two_pow_le_card_bucketVec_mldsa44 A Q

end P44Bind

section P44Conv

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m)))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-44 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** with converted base messages (`bmsg := fun _ m => m`, the base message
`m`) (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-44 with the regularity bound `11 · 2^-101 ·
(24/5) / β_min`, `expect_regGapAvg_le_mldsa44`): for every family of anonymity adversaries indexed
by the oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t` superposition queries to the
joint oracle of `H_µ`, `H`, `G`, the mask derivation and the proof system's hash, and tables reading
the base components only off the mask and check points, and every number `Q` of challenges, the
advantage averaged over the three oracles is at most `Q · (2 (2 / ((1 - s) θ) · n R + √(N n log (C +
1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1 - s) / 32)^k) + Q · wi (Q · C)
+ 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240` with `R` = `11 · 2^-101 ·
(24/5) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check parameters (`CheckParams`, for
instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_conv_mldsa44 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m)) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m) (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m) (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le (bmsg := fun _ m => m) (PS := PS) sp
    isApproved_mldsa44 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa44 hβ0 hβ1)
    commitCollisionBound_le_mldsa44 one_div_sixteen_le_standinScale_mul_card_mldsa44
    two_pow_le_card_bucketVec_mldsa44 A Q

end P44Conv

section P65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D bmsg))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-65 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-65 with the regularity
bound `11 · 2^-199 · (9/2) / β_min`, `expect_regGapAvg_le_mldsa65`): for every family of anonymity
adversaries indexed by the oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t`
superposition queries to the joint oracle of `H_µ`, `H`, `G`, the mask derivation and the proof
system's hash, and tables reading the base components only off the mask and check points, and every
number `Q` of challenges, the advantage averaged over the three oracles is at most `Q · (2 (2 / ((1
- s) θ) · n R + √(N n log (C + 1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1
- s) / 32)^k) + Q · wi (Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240`
with `R` = `11 · 2^-199 · (9/2) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check
parameters (`CheckParams`, for instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_mldsa65 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le sp isApproved_mldsa65 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa65 hβ0 hβ1)
    commitCollisionBound_le_mldsa65 one_div_sixteen_le_standinScale_mul_card_mldsa65
    two_pow_le_card_bucketVec_mldsa65 A Q

end P65

section P65Bind

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-65 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** with ring-binding base messages (`bmsg := Prod.mk`, the base message `(R,
m)`) (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-65 with the regularity bound `11 · 2^-199 · (9/2)
/ β_min`, `expect_regGapAvg_le_mldsa65`): for every family of anonymity adversaries indexed by the
oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t` superposition queries to the joint
oracle of `H_µ`, `H`, `G`, the mask derivation and the proof system's hash, and tables reading the
base components only off the mask and check points, and every number `Q` of challenges, the
advantage averaged over the three oracles is at most `Q · (2 (2 / ((1 - s) θ) · n R + √(N n log (C +
1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1 - s) / 32)^k) + Q · wi (Q · C)
+ 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240` with `R` = `11 · 2^-199 ·
(9/2) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check parameters (`CheckParams`, for
instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_bind_mldsa65 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le (bmsg := Prod.mk) (PS := PS) sp
    isApproved_mldsa65 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa65 hβ0 hβ1)
    commitCollisionBound_le_mldsa65 one_div_sixteen_le_standinScale_mul_card_mldsa65
    two_pow_le_card_bucketVec_mldsa65 A Q

end P65Bind

section P65Conv

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m)))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-65 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** with converted base messages (`bmsg := fun _ m => m`, the base message
`m`) (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-65 with the regularity bound `11 · 2^-199 · (9/2)
/ β_min`, `expect_regGapAvg_le_mldsa65`): for every family of anonymity adversaries indexed by the
oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t` superposition queries to the joint
oracle of `H_µ`, `H`, `G`, the mask derivation and the proof system's hash, and tables reading the
base components only off the mask and check points, and every number `Q` of challenges, the
advantage averaged over the three oracles is at most `Q · (2 (2 / ((1 - s) θ) · n R + √(N n log (C +
1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1 - s) / 32)^k) + Q · wi (Q · C)
+ 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240` with `R` = `11 · 2^-199 ·
(9/2) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check parameters (`CheckParams`, for
instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_conv_mldsa65 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m)) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m) (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m) (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le (bmsg := fun _ m => m) (PS := PS) sp
    isApproved_mldsa65 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa65 hβ0 hβ1)
    commitCollisionBound_le_mldsa65 one_div_sixteen_le_standinScale_mul_card_mldsa65
    two_pow_le_card_bucketVec_mldsa65 A Q

end P65Conv

section P87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D bmsg))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-87 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-87 with the regularity
bound `12 · 2^-294 · (33/5) / β_min`, `expect_regGapAvg_le_mldsa87`): for every family of anonymity
adversaries indexed by the oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t`
superposition queries to the joint oracle of `H_µ`, `H`, `G`, the mask derivation and the proof
system's hash, and tables reading the base components only off the mask and check points, and every
number `Q` of challenges, the advantage averaged over the three oracles is at most `Q · (2 (2 / ((1
- s) θ) · n R + √(N n log (C + 1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1
- s) / 32)^k) + Q · wi (Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240`
with `R` = `12 · 2^-294 · (33/5) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check
parameters (`CheckParams`, for instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_mldsa87 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D bmsg (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le sp isApproved_mldsa87 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa87 hβ0 hβ1)
    commitCollisionBound_le_mldsa87 one_div_sixteen_le_standinScale_mul_card_mldsa87
    two_pow_le_card_bucketVec_mldsa87 A Q

end P87

section P87Bind

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-87 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** with ring-binding base messages (`bmsg := Prod.mk`, the base message `(R,
m)`) (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-87 with the regularity bound `12 · 2^-294 ·
(33/5) / β_min`, `expect_regGapAvg_le_mldsa87`): for every family of anonymity adversaries indexed
by the oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t` superposition queries to the
joint oracle of `H_µ`, `H`, `G`, the mask derivation and the proof system's hash, and tables reading
the base components only off the mask and check points, and every number `Q` of challenges, the
advantage averaged over the three oracles is at most `Q · (2 (2 / ((1 - s) θ) · n R + √(N n log (C +
1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1 - s) / 32)^k) + Q · wi (Q · C)
+ 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240` with `R` = `12 · 2^-294 ·
(33/5) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check parameters (`CheckParams`, for
instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_bind_mldsa87 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D Prod.mk (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le (bmsg := Prod.mk) (PS := PS) sp
    isApproved_mldsa87 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa87 hβ0 hβ1)
    commitCollisionBound_le_mldsa87 one_div_sixteen_le_standinScale_mul_card_mldsa87
    two_pow_le_card_bucketVec_mldsa87 A Q

end P87Bind

section P87Conv

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {PS : ∀ (GB : CommitHashBytes Pm → ChallengeBall (Pm).tau) (GS : Bytes 64 → SecretCoeffs Pm)
    (GA : Bytes 32 → TqMatrix (Pm).k (Pm).l),
    ProofSystem X Y (RingSignature.RingStmt (w1Base Pm (randomOraclePrimitives GB GS GA)
      (concreteEnc Pm) (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m)))
      (RingSignature.RingWitOf (FIPSSignature Pm (randomOraclePrimitives GB GS GA))) TPS}
  {adm : KeyRing (PubKey Pm Kg) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-87 ring signature publishing `w₁` with `SampleInBall`, `ExpandS` and
`ExpandA` random oracles** with converted base messages (`bmsg := fun _ m => m`, the base message
`m`) (`w1Scheme.expect_anonAdvantage_le` at ML-DSA-87 with the regularity bound `12 · 2^-294 ·
(33/5) / β_min`, `expect_regGapAvg_le_mldsa87`): for every family of anonymity adversaries indexed
by the oracles `G_B`, `G_S`, `G_A` (each oracle given whole), with `t` superposition queries to the
joint oracle of `H_µ`, `H`, `G`, the mask derivation and the proof system's hash, and tables reading
the base components only off the mask and check points, and every number `Q` of challenges, the
advantage averaged over the three oracles is at most `Q · (2 (2 / ((1 - s) θ) · n R + √(N n log (C +
1)) / (2^2000 θ (1 - θ) (1 - s) β_min)) + 2 k / D + 2 (1 - β_min θ (1 - s) / 32)^k) + Q · wi (Q · C)
+ 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² / 2^240` with `R` = `12 · 2^-294 ·
(33/5) / β_min`, for `β_min ∈ (0, 1]`, `n ≥ 1` honest users, check parameters (`CheckParams`, for
instance `checkParams_tol2`) with `0 ≤ s`, and `θ ∈ (0, 1)`. -/
@[headline]
theorem w1Scheme.expect_anonAdvantage_le_conv_mldsa87 (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : ∀ GB GS GA, (PS GB GS GA).ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ GB GS GA ω₂ h₁, PubWI (fun h => (PS GB GS GA).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1Base Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m)) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ GB GS GA (keys : Fin n → Bytes 32), (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m) (PS GB GS GA) adm) n =>
        c.Valid keys).card ≤ C)
    [NeZero n] {s θ x : ℝ} (hcp : CheckParams reps tol s x) (hs0 : 0 ≤ s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {t : ℕ}
    (A : ∀ GB GS GA, AnonAdversary (w1Scheme Pm (randomOraclePrimitives GB GS GA) (concreteEnc Pm)
        (O.atRandomOracles GB GS GA) M βmin tol k D (fun _ m => m) (PS GB GS GA) adm) n V t)
    (Q : ℕ) :
    𝔼 GB : CommitHashBytes Pm → ChallengeBall (Pm).tau, 𝔼 GS : Bytes 64 → SecretCoeffs Pm,
      𝔼 GA : Bytes 32 → TqMatrix (Pm).k (Pm).l, anonAdvantage (A GB GS GA) Q ≤
      Q * (2 * (2 * (1 - s)⁻¹ / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) /
              (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal))) +
          2 * (k * (D : ℝ)⁻¹) + 2 * (1 - (βmin : ℝ≥0∞).toReal * θ * (1 - s) / 32) ^ k) +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) :=
  w1Scheme.expect_anonAdvantage_le (bmsg := fun _ m => m) (PS := PS) sp
    isApproved_mldsa87 hT hβ0 hβ1 hO hMask hM hdisj hsp hMsp hPS
    hV hwi hC hcp hs0 hθ0 hθ1 (expect_regGapAvg_le_mldsa87 hβ0 hβ1)
    commitCollisionBound_le_mldsa87 one_div_sixteen_le_standinScale_mul_card_mldsa87
    two_pow_le_card_bucketVec_mldsa87 A Q

end P87Conv

end Instances

end GordieHowe.Ring.MLDSAW1
