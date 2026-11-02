-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Hedged
public import GordieHowe.Applications.Ring.PublicW1.MaskOracleQROM

@[expose] public section

/-!
# The ML-DSA ring signer publishing `w₁` with FIPS 204 hedged signing, in the quantum random-oracle model

The headlines of `GordieHowe/Applications/Ring/PublicW1/MLDSAPublicW1Hedged.lean` for adversaries
that query the mask oracle (`H(K ‖ rnd ‖ µ)` composed with ExpandMask, a random oracle onto the
mask box) in superposition: in each round, and for the guess, the adversary runs a quantum
algorithm with `q` queries to the mask oracle, whose answers are encoded in a finite additive
group `G` by `enc`, and the outcome is measured (`MaskedSigner.QAdversary`, `MaskedSigner.QDist`,
`GordieHowe/Applications/Ring/PublicW1/MaskOracleQROM.lean`). The other oracles are given whole.

- `advantage_le_hedgedQ`: anonymity against the hedged signer from anonymity against the
  ideal-mask signer, for a lower bound `s̄` on the keep probability of one ring attempt
  (`KeepBound`): at every mask oracle a classical adversary with the same set of challenges
  against the ideal-mask signer, plus twice the hedged error
  `k² / 2^256 + 2 · 2 q √(k / 2^256) + 2 (1 - s̄)^k` (`MaskedSigner.hedgeErrorQ` at `Q = 1`).
- `advantage_le_bkm06_mldsa{44,65,87}_hedged_qrom`: the ML-DSA headlines at the check parameters,
  with `KeepBound` a hypothesis.
- `advantage_le_bkm06_mldsa{44,65,87}_hedged_keep_qrom`: the same with the keep bound discharged
  as in `advantage_le_bkm06_mldsa{44,65,87}_hedged_keep`: the ideal-mask bound plus
  `2 · (k² / 2^256 + 4 q √(k / 2^256) + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity + McDiarmid) + C / 2^240))`.

The query term is one-way to hiding (AHU19 Theorem 3) for each of the two quantum phases (the
choice and the guess), with the set of the mask points at the `k` nonces drawn for the hedged
calls: `2 q √(k / 2^256)` each, against `2 q k / 2^256` for the two classical phases of the
classical headlines. The adversary keeps no quantum state between the choice and the guess (its
state between them is classical); the check term `C / 2^240` and the check oracle `G` are as in the
classical headlines. `MLDSAPublicW1HedgedQROMQuery.lean` states the headlines with
`2 (q + 1) / 2^240` for adversaries with `q` check-oracle queries. Deterministic signing (`rnd = 0`) is not covered.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA PMF Finset
open scoped ENNReal BigOperators

section Signer

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High]

section HedgedQ

open IOP GordieHowe.SPBCS GordieHowe.QROM

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p} {T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e} {n : ℕ}
  {G : Type} [Fintype G] [AddGroup G] {q : ℕ}
  {E : (j : ι) → (M.comp j).Encoder}
  {V : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt →
    FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
  {honest : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Wit →
    R → CausalProver P τ (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt}

/-- **Anonymity against FIPS 204 hedged signing in the quantum random-oracle model from anonymity
against the ideal-mask signer** (BKM06 Definition 4, ePrint 2005/304, p. 6, one challenge, keys
given at the start as in CCLM22 Experiment 2, p. 21): for an adversary and a distinguisher with `q`
superposition queries to the mask oracle per phase (`H(K ‖ rnd ‖ µ)` composed with ExpandMask, a
random oracle, its answers encoded by `encY`), and a lower bound `s̄` on the keep probability of
one ring attempt (`hkeep`), the advantage is at most the average over the mask oracle of the
advantage of a classical adversary with the same set of challenges against the ideal-mask signer,
plus `2 · 𝔼_{keys, HG} (k² / 2^256 + 2 · 2 q √(k / 2^256) + 2 (1 - s̄)^k)` for every number `k`
of attempts. Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_hedgedQ
    (A : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).QAdversary M G n 1 q)
    (D : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).QDist M G n 1 q)
    (encY : MaskBox p → G) (ka : ℕ)
    (sbar : (Fin n → _root_.MLDSA.Bytes 32) → GameOrc prims Msg N reps → ℝ≥0∞)
    (hkeep : KeepBound prims βmin tol A.choices sbar) :
    ∃ tab : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).MaskOrc → A.Table,
      A.advantage D encY E Qs honest ≤
        𝔼 Y : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).MaskOrc,
          (A.atTable (tab Y)).advantage E Qs honest ((A.atTable (tab Y)).likelierDist E Qs honest) +
        2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32, 𝔼 HG : GameOrc prims Msg N reps,
          ((hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).hedgeErrorQ 1 q ka
            (1 - sbar keys HG)).toReal :=
  MaskedSigner.QAdversary.exists_advantage_le A D encY E Qs honest ka (fun keys HG => 1 - sbar keys HG)
    (fun keys HG => (tsub_le_self : (1 : ℝ≥0∞) - sbar keys HG ≤ 1)) fun keys HG c hc hv ha b => by
      have hlt : c.idx b < c.ring.1.length := by
        cases b
        · exact hv.idx₀_lt
        · exact hv.idx₁_lt
      exact (meanAttempt_none_le prims hT keys HG c b hlt ha).trans
        (hkeep.keep keys HG c hc hv ha b hlt)

end HedgedQ

end Signer

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity IOP GordieHowe.SPBCS GordieHowe.QROM
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

section Hedged_mldsa44_qrom

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ} {G : Type} [Fintype G] [AddGroup G] {q : ℕ}
  {M : ∀ (GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau) (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc _root_.MLDSA.mldsa44)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).QAdversary (M GB GS GA) G n 1 q)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc _root_.MLDSA.mldsa44)).Stmt}
  (D : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).QDist (M GB GS GA) G n 1 q)
  (encY : MaskBox _root_.MLDSA.mldsa44 → G)

open Classical in
/-- **Anonymity at ML-DSA-44 with FIPS 204 hedged signing at the check parameters, in the quantum
random-oracle model** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the start
as in CCLM22 Experiment 2, p. 21): `advantage_le_bkm06_mldsa44_checkParams` for a classical
adversary with the same set of challenges against the ideal-mask signer at every fixed mask
oracle (`advantage_le_hedgedQ`), plus twice the hedged error
`k² / 2^256 + 2 · 2 q √(k / 2^256) + 2 (1 - s̄)^k` averaged over the oracles and the users' coins,
for an adversary and a distinguisher with `q` superposition queries to the mask oracle per phase
(`MaskedSigner.QAdversary`, `MaskedSigner.QDist`, the answers encoded by `encY`), at most `C`
challenges of its set valid for any key vector (`hC`), a lower bound `s̄` on the keep probability
of one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step) and every number `k`
of attempts (`ka`). The masks are `ExpandMask(H(K ‖ rnd ‖ µ), κ)` with `H` and ExpandMask one
random oracle, at most `T` per call and a fresh `rnd` per call; deterministic signing
(`rnd = 0`) is not covered. The check term `C / 2^240` counts the candidate rings per key vector,
not the mask-oracle queries. -/
theorem advantage_le_bkm06_mldsa44_hedged_qrom (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44) (_GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l),
      (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
                    (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240
  -- at every oracle, the hedged step and a classical adversary at every mask oracle
  have hstep := fun GB GS GA => advantage_le_hedgedQ (withExpandA (oraclePrimitives GB GS) GA) hT
    (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA) (A GB GS GA) (D GB GS GA)
    encY ka (sbar GB GS GA) (hkeep GB GS GA)
  choose tab htab using hstep
  -- at every fixed mask oracle, the ideal-mask bound for the classical adversaries
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44,
      𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            ((A GB GS GA).atTable (tab GB GS GA Y)).advantage (E GB GS GA) (Qs GB GS GA)
              (honest GB GS GA) (((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
                (Qs GB GS GA) (honest GB GS GA)) ≤ B := fun Y =>
    advantage_le_bkm06_mldsa44_checkParams (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      (fun GB GS GA => ((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA)) hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz
      fun GB GS GA => (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
  exact expect3_le_of_mix _ _ (fun GB GS GA (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44) =>
      ((A GB GS GA).atTable (tab GB GS GA Y)).advantage (E GB GS GA) (Qs GB GS GA)
        (honest GB GS GA) (((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
          (Qs GB GS GA) (honest GB GS GA))) htab hY

open Classical in
/-- **Anonymity at ML-DSA-44 with FIPS 204 hedged signing in the quantum random-oracle model, the
keep bound discharged** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`):
`advantage_le_bkm06_mldsa44_hedged_qrom` with the keep bound `s̄ = β_min θ / 64` on the good event,
whose failure is at most twice the anonymity error plus the check term, as in
`advantage_le_bkm06_mldsa44_hedged_keep`. For every adversary and distinguisher with `q`
superposition queries to the mask oracle per phase (the answers encoded by `encY`) and every
number `k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 · (k² / 2^256 + 4 q √(k / 2^256) + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity + McDiarmid) + C / 2^240))`.
Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa44_hedged_keep_qrom (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) (ka : ℕ) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * (ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ /
          64) ^ ka +
          (2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
            C / 2 ^ 240))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty (τ := _root_.MLDSA.mldsa44.tau) (by
    rw [show _root_.MLDSA.mldsa44.tau = 39 from rfl]; norm_num [ringDegree])
  have hp' := SigningParams.of_isApproved isApproved_mldsa44
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  -- a classical adversary with the set of challenges of `A`, for the good event
  set A' := fun GB GS GA => (A GB GS GA).atTable fun x =>
    (((A GB GS GA).entryAlg x).outLaw 0).support_nonempty.some
  set Lk : ℝ := (βmin : ℝ≥0∞).toReal * θ / 64
  have hLk0 : 0 ≤ Lk := by positivity
  have hLk1 : Lk ≤ 1 := by
    have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 := mul_le_one₀ hb1 hθ0.le hθ1.le
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1
    linarith
  have hLk : Lk ≤ keepLevel _root_.MLDSA.mldsa44 βmin (1 / 2) θ := by
    have hK := one_div_sixteen_le_standinScale_mul_card_mldsa44
    unfold keepLevel
    rw [ENNReal.toReal_mul]
    have hx := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ _
    nlinarith [hx]
  set good := fun GB GS GA => KeepGood (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
    hβ0 hβt (1 / 2) θ
  have hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices fun keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0 :=
    fun GB GS GA => keepBound_of_keepGood _ (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1 (by norm_num) hLk
  have hC' : ∀ GB GS GA, (A' GB GS GA).ValidCountLe C := fun GB GS GA =>
    (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
  have h1 := advantage_le_bkm06_mldsa44_hedged_qrom hT A D encY hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz
    hC ka (fun GB GS GA keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0) hkeep
  refine h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le_two))
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
        2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
          √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
    have hM : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
                  keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log (C + 1) / 2)) ≤
          √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
            (βmin : ℝ≥0∞).toReal)) :=
      (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
        expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβ1 hβt hθ0 hθ1
          (by norm_num) C
          commitCollisionBound_le_mldsa44 one_div_sixteen_le_standinScale_mul_card_mldsa44
          two_pow_le_card_bucketVec_mldsa44).trans_eq
        (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
    have hI := expect_idealAnonError_le (p := _root_.MLDSA.mldsa44) (A := A') isApproved_mldsa44 hβ0 hβt hθ0
      (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa44 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
      (βmin : ℝ≥0∞).toReal)) =
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
      rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
      generalize (2 : ℝ) ^ 1999 = T
      ring
    rw [h2]
    refine add_le_add le_rfl (hM.trans_eq hm)
  -- the failure of the good event
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have hE2 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
        (if good GB GS GA keys HG then 0 else 1 : ℝ) ≤
      2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240 := fun GB GS GA => by
    have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
      (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa44 (sampleInBallShape_oraclePrims GB) _)
      GA
    have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA)
      hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2)
      (by norm_num) (hC' GB GS GA)
    have hK := fun keys => expect_ite_keepGood_le (withExpandA (oraclePrimitives GB GS) GA)
      (A' GB GS GA) hp' hβ0 hβt (s := 1 / 2) (θ := θ) (by norm_num) hθ0 (x := 89) (by norm_num)
      (hC' GB GS GA) keys
    calc _ ≤ 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          (2 * 𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
            oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
              keys HG.1 +
            (C : ℝ) * checkError reps tol (1 / 2) 89) := Finset.expect_le_expect fun keys _ => hK keys
      _ ≤ 2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + (C : ℝ) * (1 / 2 ^ 240) := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
          exact add_le_add (mul_le_mul_of_nonneg_left hO zero_le_two)
            (mul_le_mul_of_nonneg_left hchk (Nat.cast_nonneg _))
      _ = _ := by rw [mul_one_div]
  -- the hedged error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka
            (1 - if good GB GS GA keys HG then ENNReal.ofReal Lk else 0)).toReal ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka +
          (2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240)) :=
    fun GB GS GA => by
      have h := MaskedSigner.expect_toReal_hedgeErrorQ_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT) 1 q ka
        (good GB GS GA) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      have h3 := hE2 GB GS GA
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * (2 * q * √(ka / 2 ^ 256))) =
          ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) := by ring
      rw [hc]
      nlinarith [h3]
  refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
    Finset.expect_le_expect fun GA _ => hE1 GB GS GA).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hfin := hE3
  nlinarith [hfin]

end Hedged_mldsa44_qrom

section Hedged_mldsa65_qrom

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ} {G : Type} [Fintype G] [AddGroup G] {q : ℕ}
  {M : ∀ (GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau) (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc _root_.MLDSA.mldsa65)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa65) T hT).QAdversary (M GB GS GA) G n 1 q)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa65)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa65)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc _root_.MLDSA.mldsa65)).Stmt}
  (D : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa65) T hT).QDist (M GB GS GA) G n 1 q)
  (encY : MaskBox _root_.MLDSA.mldsa65 → G)

open Classical in
/-- **Anonymity at ML-DSA-65 with FIPS 204 hedged signing at the check parameters, in the quantum
random-oracle model** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the start
as in CCLM22 Experiment 2, p. 21): `advantage_le_bkm06_mldsa65_checkParams` for a classical
adversary with the same set of challenges against the ideal-mask signer at every fixed mask
oracle (`advantage_le_hedgedQ`), plus twice the hedged error
`k² / 2^256 + 2 · 2 q √(k / 2^256) + 2 (1 - s̄)^k` averaged over the oracles and the users' coins,
for an adversary and a distinguisher with `q` superposition queries to the mask oracle per phase
(`MaskedSigner.QAdversary`, `MaskedSigner.QDist`, the answers encoded by `encY`), at most `C`
challenges of its set valid for any key vector (`hC`), a lower bound `s̄` on the keep probability
of one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step) and every number `k`
of attempts (`ka`). The masks are `ExpandMask(H(K ‖ rnd ‖ µ), κ)` with `H` and ExpandMask one
random oracle, at most `T` per call and a fresh `rnd` per call; deterministic signing
(`rnd = 0`) is not covered. The check term `C / 2^240` counts the candidate rings per key vector,
not the mask-oracle queries. -/
theorem advantage_le_bkm06_mldsa65_hedged_qrom (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa65)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa65)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65) (_GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l),
      (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa65) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa65) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
                    (concreteEnc _root_.MLDSA.mldsa65) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240
  -- at every oracle, the hedged step and a classical adversary at every mask oracle
  have hstep := fun GB GS GA => advantage_le_hedgedQ (withExpandA (oraclePrimitives GB GS) GA) hT
    (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA) (A GB GS GA) (D GB GS GA)
    encY ka (sbar GB GS GA) (hkeep GB GS GA)
  choose tab htab using hstep
  -- at every fixed mask oracle, the ideal-mask bound for the classical adversaries
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa65,
      𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
            ((A GB GS GA).atTable (tab GB GS GA Y)).advantage (E GB GS GA) (Qs GB GS GA)
              (honest GB GS GA) (((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
                (Qs GB GS GA) (honest GB GS GA)) ≤ B := fun Y =>
    advantage_le_bkm06_mldsa65_checkParams (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      (fun GB GS GA => ((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA)) hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz
      fun GB GS GA => (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
  exact expect3_le_of_mix _ _ (fun GB GS GA (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa65) =>
      ((A GB GS GA).atTable (tab GB GS GA Y)).advantage (E GB GS GA) (Qs GB GS GA)
        (honest GB GS GA) (((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
          (Qs GB GS GA) (honest GB GS GA))) htab hY

open Classical in
/-- **Anonymity at ML-DSA-65 with FIPS 204 hedged signing in the quantum random-oracle model, the
keep bound discharged** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`):
`advantage_le_bkm06_mldsa65_hedged_qrom` with the keep bound `s̄ = β_min θ / 64` on the good event,
whose failure is at most twice the anonymity error plus the check term, as in
`advantage_le_bkm06_mldsa65_hedged_keep`. For every adversary and distinguisher with `q`
superposition queries to the mask oracle per phase (the answers encoded by `encY`) and every
number `k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 · (k² / 2^256 + 4 q √(k / 2^256) + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity + McDiarmid) + C / 2^240))`.
Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa65_hedged_keep_qrom (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa65)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa65)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) (ka : ℕ) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * (ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ /
          64) ^ ka +
          (2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
            C / 2 ^ 240))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa65.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa65
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  -- a classical adversary with the set of challenges of `A`, for the good event
  set A' := fun GB GS GA => (A GB GS GA).atTable fun x =>
    (((A GB GS GA).entryAlg x).outLaw 0).support_nonempty.some
  set Lk : ℝ := (βmin : ℝ≥0∞).toReal * θ / 64
  have hLk0 : 0 ≤ Lk := by positivity
  have hLk1 : Lk ≤ 1 := by
    have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 := mul_le_one₀ hb1 hθ0.le hθ1.le
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1
    linarith
  have hLk : Lk ≤ keepLevel _root_.MLDSA.mldsa65 βmin (1 / 2) θ := by
    have hK := one_div_sixteen_le_standinScale_mul_card_mldsa65
    unfold keepLevel
    rw [ENNReal.toReal_mul]
    have hx := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ _
    nlinarith [hx]
  set good := fun GB GS GA => KeepGood (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
    hβ0 hβt (1 / 2) θ
  have hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices fun keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0 :=
    fun GB GS GA => keepBound_of_keepGood _ (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1 (by norm_num) hLk
  have hC' : ∀ GB GS GA, (A' GB GS GA).ValidCountLe C := fun GB GS GA =>
    (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
  have h1 := advantage_le_bkm06_mldsa65_hedged_qrom hT A D encY hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz
    hC ka (fun GB GS GA keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0) hkeep
  refine h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le_two))
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
        2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
          √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
    have hM : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa65 → ChallengeBall _root_.MLDSA.mldsa65.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa65,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
                  keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log (C + 1) / 2)) ≤
          √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
            (βmin : ℝ≥0∞).toReal)) :=
      (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
        expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβ1 hβt hθ0 hθ1
          (by norm_num) C
          commitCollisionBound_le_mldsa65 one_div_sixteen_le_standinScale_mul_card_mldsa65
          two_pow_le_card_bucketVec_mldsa65).trans_eq
        (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
    have hI := expect_idealAnonError_le (p := _root_.MLDSA.mldsa65) (A := A') isApproved_mldsa65 hβ0 hβt hθ0
      (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa65 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa65.k _root_.MLDSA.mldsa65.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
      (βmin : ℝ≥0∞).toReal)) =
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
      rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
      generalize (2 : ℝ) ^ 1999 = T
      ring
    rw [h2]
    refine add_le_add le_rfl (hM.trans_eq hm)
  -- the failure of the good event
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have hE2 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa65) Msg N reps,
        (if good GB GS GA keys HG then 0 else 1 : ℝ) ≤
      2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240 := fun GB GS GA => by
    have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
      (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa65 (sampleInBallShape_oraclePrims GB) _)
      GA
    have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA)
      hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2)
      (by norm_num) (hC' GB GS GA)
    have hK := fun keys => expect_ite_keepGood_le (withExpandA (oraclePrimitives GB GS) GA)
      (A' GB GS GA) hp' hβ0 hβt (s := 1 / 2) (θ := θ) (by norm_num) hθ0 (x := 89) (by norm_num)
      (hC' GB GS GA) keys
    calc _ ≤ 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          (2 * 𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa65) Msg N reps,
            oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
              keys HG.1 +
            (C : ℝ) * checkError reps tol (1 / 2) 89) := Finset.expect_le_expect fun keys _ => hK keys
      _ ≤ 2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + (C : ℝ) * (1 / 2 ^ 240) := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
          exact add_le_add (mul_le_mul_of_nonneg_left hO zero_le_two)
            (mul_le_mul_of_nonneg_left hchk (Nat.cast_nonneg _))
      _ = _ := by rw [mul_one_div]
  -- the hedged error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa65) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc _root_.MLDSA.mldsa65) T hT).hedgeErrorQ 1 q ka
            (1 - if good GB GS GA keys HG then ENNReal.ofReal Lk else 0)).toReal ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka +
          (2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240)) :=
    fun GB GS GA => by
      have h := MaskedSigner.expect_toReal_hedgeErrorQ_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa65) T hT) 1 q ka
        (good GB GS GA) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa65) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      have h3 := hE2 GB GS GA
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * (2 * q * √(ka / 2 ^ 256))) =
          ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) := by ring
      rw [hc]
      nlinarith [h3]
  refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
    Finset.expect_le_expect fun GA _ => hE1 GB GS GA).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hfin := hE3
  nlinarith [hfin]

end Hedged_mldsa65_qrom

section Hedged_mldsa87_qrom

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ} {G : Type} [Fintype G] [AddGroup G] {q : ℕ}
  {M : ∀ (GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau) (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc _root_.MLDSA.mldsa87)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa87) T hT).QAdversary (M GB GS GA) G n 1 q)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa87)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa87)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc _root_.MLDSA.mldsa87)).Stmt}
  (D : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa87) T hT).QDist (M GB GS GA) G n 1 q)
  (encY : MaskBox _root_.MLDSA.mldsa87 → G)

open Classical in
/-- **Anonymity at ML-DSA-87 with FIPS 204 hedged signing at the check parameters, in the quantum
random-oracle model** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the start
as in CCLM22 Experiment 2, p. 21): `advantage_le_bkm06_mldsa87_checkParams` for a classical
adversary with the same set of challenges against the ideal-mask signer at every fixed mask
oracle (`advantage_le_hedgedQ`), plus twice the hedged error
`k² / 2^256 + 2 · 2 q √(k / 2^256) + 2 (1 - s̄)^k` averaged over the oracles and the users' coins,
for an adversary and a distinguisher with `q` superposition queries to the mask oracle per phase
(`MaskedSigner.QAdversary`, `MaskedSigner.QDist`, the answers encoded by `encY`), at most `C`
challenges of its set valid for any key vector (`hC`), a lower bound `s̄` on the keep probability
of one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step) and every number `k`
of attempts (`ka`). The masks are `ExpandMask(H(K ‖ rnd ‖ µ), κ)` with `H` and ExpandMask one
random oracle, at most `T` per call and a fresh `rnd` per call; deterministic signing
(`rnd = 0`) is not covered. The check term `C / 2^240` counts the candidate rings per key vector,
not the mask-oracle queries. -/
theorem advantage_le_bkm06_mldsa87_hedged_qrom (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa87)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa87)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87) (_GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l),
      (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa87) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa87) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
                    (concreteEnc _root_.MLDSA.mldsa87) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240
  -- at every oracle, the hedged step and a classical adversary at every mask oracle
  have hstep := fun GB GS GA => advantage_le_hedgedQ (withExpandA (oraclePrimitives GB GS) GA) hT
    (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA) (A GB GS GA) (D GB GS GA)
    encY ka (sbar GB GS GA) (hkeep GB GS GA)
  choose tab htab using hstep
  -- at every fixed mask oracle, the ideal-mask bound for the classical adversaries
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa87,
      𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
            ((A GB GS GA).atTable (tab GB GS GA Y)).advantage (E GB GS GA) (Qs GB GS GA)
              (honest GB GS GA) (((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
                (Qs GB GS GA) (honest GB GS GA)) ≤ B := fun Y =>
    advantage_le_bkm06_mldsa87_checkParams (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      (fun GB GS GA => ((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA)) hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz
      fun GB GS GA => (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
  exact expect3_le_of_mix _ _ (fun GB GS GA (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa87) =>
      ((A GB GS GA).atTable (tab GB GS GA Y)).advantage (E GB GS GA) (Qs GB GS GA)
        (honest GB GS GA) (((A GB GS GA).atTable (tab GB GS GA Y)).likelierDist (E GB GS GA)
          (Qs GB GS GA) (honest GB GS GA))) htab hY

open Classical in
/-- **Anonymity at ML-DSA-87 with FIPS 204 hedged signing in the quantum random-oracle model, the
keep bound discharged** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`):
`advantage_le_bkm06_mldsa87_hedged_qrom` with the keep bound `s̄ = β_min θ / 64` on the good event,
whose failure is at most twice the anonymity error plus the check term, as in
`advantage_le_bkm06_mldsa87_hedged_keep`. For every adversary and distinguisher with `q`
superposition queries to the mask oracle per phase (the answers encoded by `encY`) and every
number `k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 · (k² / 2^256 + 4 q √(k / 2^256) + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity + McDiarmid) +
  C / 2^240))`.
Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa87_hedged_keep_qrom (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa87)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa87)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) (ka : ℕ) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * (ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ /
          64) ^ ka +
          (2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
            C / 2 ^ 240))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa87.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa87
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  -- a classical adversary with the set of challenges of `A`, for the good event
  set A' := fun GB GS GA => (A GB GS GA).atTable fun x =>
    (((A GB GS GA).entryAlg x).outLaw 0).support_nonempty.some
  set Lk : ℝ := (βmin : ℝ≥0∞).toReal * θ / 64
  have hLk0 : 0 ≤ Lk := by positivity
  have hLk1 : Lk ≤ 1 := by
    have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 := mul_le_one₀ hb1 hθ0.le hθ1.le
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1
    linarith
  have hLk : Lk ≤ keepLevel _root_.MLDSA.mldsa87 βmin (1 / 2) θ := by
    have hK := one_div_sixteen_le_standinScale_mul_card_mldsa87
    unfold keepLevel
    rw [ENNReal.toReal_mul]
    have hx := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ _
    nlinarith [hx]
  set good := fun GB GS GA => KeepGood (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
    hβ0 hβt (1 / 2) θ
  have hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices fun keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0 :=
    fun GB GS GA => keepBound_of_keepGood _ (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1 (by norm_num) hLk
  have hC' : ∀ GB GS GA, (A' GB GS GA).ValidCountLe C := fun GB GS GA =>
    (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
  have h1 := advantage_le_bkm06_mldsa87_hedged_qrom hT A D encY hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz
    hC ka (fun GB GS GA keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0) hkeep
  refine h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le_two))
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
        2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
          √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
    have hM : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa87 → ChallengeBall _root_.MLDSA.mldsa87.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa87,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
                  keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log (C + 1) / 2)) ≤
          √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
            (βmin : ℝ≥0∞).toReal)) :=
      (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
        expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβ1 hβt hθ0 hθ1
          (by norm_num) C
          commitCollisionBound_le_mldsa87 one_div_sixteen_le_standinScale_mul_card_mldsa87
          two_pow_le_card_bucketVec_mldsa87).trans_eq
        (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
    have hI := expect_idealAnonError_le (p := _root_.MLDSA.mldsa87) (A := A') isApproved_mldsa87 hβ0 hβt hθ0
      (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa87 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa87.k _root_.MLDSA.mldsa87.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
      (βmin : ℝ≥0∞).toReal)) =
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
      rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
      generalize (2 : ℝ) ^ 1999 = T
      ring
    rw [h2]
    refine add_le_add le_rfl (hM.trans_eq hm)
  -- the failure of the good event
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have hE2 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa87) Msg N reps,
        (if good GB GS GA keys HG then 0 else 1 : ℝ) ≤
      2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240 := fun GB GS GA => by
    have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
      (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa87 (sampleInBallShape_oraclePrims GB) _)
      GA
    have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA)
      hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2)
      (by norm_num) (hC' GB GS GA)
    have hK := fun keys => expect_ite_keepGood_le (withExpandA (oraclePrimitives GB GS) GA)
      (A' GB GS GA) hp' hβ0 hβt (s := 1 / 2) (θ := θ) (by norm_num) hθ0 (x := 89) (by norm_num)
      (hC' GB GS GA) keys
    calc _ ≤ 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          (2 * 𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa87) Msg N reps,
            oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
              keys HG.1 +
            (C : ℝ) * checkError reps tol (1 / 2) 89) := Finset.expect_le_expect fun keys _ => hK keys
      _ ≤ 2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + (C : ℝ) * (1 / 2 ^ 240) := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
          exact add_le_add (mul_le_mul_of_nonneg_left hO zero_le_two)
            (mul_le_mul_of_nonneg_left hchk (Nat.cast_nonneg _))
      _ = _ := by rw [mul_one_div]
  -- the hedged error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa87) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc _root_.MLDSA.mldsa87) T hT).hedgeErrorQ 1 q ka
            (1 - if good GB GS GA keys HG then ENNReal.ofReal Lk else 0)).toReal ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka +
          (2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240)) :=
    fun GB GS GA => by
      have h := MaskedSigner.expect_toReal_hedgeErrorQ_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa87) T hT) 1 q ka
        (good GB GS GA) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa87) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      have h3 := hE2 GB GS GA
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * (2 * q * √(ka / 2 ^ 256))) =
          ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) := by ring
      rw [hc]
      nlinarith [h3]
  refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
    Finset.expect_le_expect fun GA _ => hE1 GB GS GA).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hfin := hE3
  nlinarith [hfin]

end Hedged_mldsa87_qrom

end GordieHowe.Ring.MLDSAW1
