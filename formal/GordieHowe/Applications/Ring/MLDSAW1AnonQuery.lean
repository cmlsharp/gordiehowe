-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1IdealDist
public import GordieHowe.Model.RingSignature.UntilBad
public import GordieHowe.Model.RingSignature.Search
public import GordieHowe.Applications.Ring.MLDSAW1Split
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Regularity

@[expose] public section

/-!
# Anonymity of the ML-DSA ring publishing `w₁` against check-oracle queries

The anonymity headlines of the ML-DSA ring publishing `w₁` for adversaries that reach the check
oracle `G` by superposition queries only.

- `admLow`: the supported rings of defect at most `s`. The hedged scheme on them refuses every ring
  of larger defect before it reads `G`.
- `BadReq`: a request on which the two schemes may answer differently: a valid challenge on a
  supported ring of defect above `s` that passes the check against `G`.
- `hedgedScheme.run_sign_admLow`: off the bad requests, the hedged scheme and the hedged scheme on
  `admLow` sign alike.
- `anonAccepts_eq_runOutIn`, `gameAdvantage_anon_restr_le_bad`: in each experiment, the anonymity
  challenger and the challenger answering with the signer on `admLow` (`restrChallenger`) are
  identical until a bad request is answered (`gameAdvantage_runLaw_le_untilBad`).
  `hedgedScheme.run_sign_eq`: signing by the hedged scheme on any rings at an oracle.
- `PMF.toReal_toOuterMeasure_uniformOfFintype_eq_expect`, `ringCheck_congr`, `checkLabel`,
  `checkLabel_gPt`, `checkLabel_eq_none`, `checkLabel_eq_none_of_notMem`, `checkLabel_gPt_of_le`,
  `CheckHit`, `readsBlocks_checkHit`, `toReal_uniform_checkHit_le`: the check points of the rings of
  defect above `s` as the labels of a search, the hit (the ring passes the check) reading only the
  base components at its label's points, of probability at most `checkError` per ring.
- `restrAns_admLow_congr`, `toReal_runLaw_badReq_le`: the signer on `admLow` reads the oracle off
  the labels, so a bad request is answered with probability at most `(√Q + 2 t)² · checkError`
  (`RingSignature.toReal_runLaw_hit_le`, `GordieHowe/Model/RingSignature/Search.lean`).
- `hedgedScheme.anonAdvantage_le_coupling`: the anonymity bound of the headlines at any primitives
  with the signing and verification laws, a coherent encoding and `‖s₂‖∞ ≤ η` for every honest key, with
  `w1CouplingError` at those primitives (`MLDSAW1AnonOracle.lean` applies it at random-oracle
  `ExpandA`, `ExpandS` and `SampleInBall`).
- `w1Concrete.anonAdvantage_le_coupling`, `w1Concrete.anonAdvantage_le_coupling_checkParams`,
  `w1Scheme44.anonAdvantage_le`, `w1Scheme65.anonAdvantage_le`, `w1Scheme87.anonAdvantage_le`:
  **the anonymity headlines** at the scheme constants: for every anonymity adversary with `t`
  superposition queries whose table reads the base components only off the mask and check points,
  and every number `Q` of challenges, the advantage is at most
  `Q · w1CouplingError + Q · wi (Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) +
  2 (√Q + 2 t)² · checkError reps tol s x` (`2 (√Q + 2 t)² / 2^240` at check parameters): the two
  until-bad steps, and the reprogramming hop and coupling for the scheme on `admLow`
  (`gameAdvantage_restrChallenger_le`, `MLDSAW1Anonymity.lean`;
  `expect_idealDist_le`, `MLDSAW1IdealDist.lean`), at any primitives with the signing and
  verification laws (`hedgedScheme.anonAdvantage_le_coupling`).
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature
open scoped ENNReal NNReal BigOperators

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-- The acceptance event of the anonymity game is the output event `RunOutIn {true}`. -/
theorem anonAccepts_eq_runOutIn [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y]
    [DecidableEq Y] [AddGroup Y] [Nonempty Y]
    {N' n : ℕ} {TS : RingTypes} {S : RingScheme X Y N' TS} :
    (anonAccepts : Set ((Fin n → S.KeyCoins) × (X → Y) ×
      Option (Bool × List (Quantum.HistoryEntry (AnonRequest S n) S.Sig)))) = RunOutIn {true} := by
  ext x
  simp [anonAccepts, RunOutIn]

/-! ### The scheme on the rings of low defect -/

section Restrict

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm]

/-- **The supported rings of defect at most `s`**: the rings of `adm` whose members' check defects
sum to at most `s` (`LowDefect`), a function of the published keys only. -/
def admLow (s : ℝ) (R : KeyRing (PubKey p prims) N) : Prop :=
  adm R ∧ LowDefect prims βmin s R

open Classical in
noncomputable instance (s : ℝ) : DecidablePred (admLow prims βmin adm s) :=
  fun _ => inferInstance

/-- **A bad request** at the users' key coins `keys` and the oracle `H`: a valid challenge on a
supported ring of defect above `s` that passes the public check against the check oracle read
from `H`. -/
def BadReq {n : ℕ} {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
    (s : ℝ) (keys : Fin n → Bytes 32) (H : X → Y)
    (c : AnonRequest (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n) : Prop :=
  c.Valid keys ∧ adm c.ring ∧ s < ringDefect prims βmin c.ring.1 ∧
    RingCheck prims βmin tol (O.gOrc H) c.ring

variable {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **Off the bad rings, the hedged scheme and the hedged scheme on the rings of low defect sign
alike**: unless the ring is supported, of defect above `s` and passes the check against the check
oracle read from `H`, both refuse or both sign identically. On a supported ring of defect above `s`
that fails the check, the hedged signer refuses (`run_bsign_w1BaseSigner`), as the signer on
`admLow` does. -/
theorem hedgedScheme.run_sign_admLow (s : ℝ)
    (kp : (hedgedBase prims O M βmin tol enc k D bmsg).PK ×
      (hedgedBase prims O M βmin tol enc k D bmsg).SK)
    (R : KeyRing (PubKey p prims) N)
    (m : (hedgedBase prims O M βmin tol enc k D bmsg).Msg)
    (c : (hedgedScheme prims O M βmin tol enc k D bmsg PS adm).SignCoins) (H : X → Y)
    (h : ¬ (adm R ∧ s < ringDefect prims βmin R.1 ∧ RingCheck prims βmin tol (O.gOrc H) R)) :
    ((hedgedScheme prims O M βmin tol enc k D bmsg PS adm).sign kp R m c).run H =
      ((hedgedScheme prims O M βmin tol enc k D bmsg PS
        (admLow prims βmin adm s)).sign kp R m c).run H := by
  obtain ⟨cb, cp⟩ := c
  dsimp only [hedgedScheme, RingSignature.ofBase_sign]
  change (if R.1.idxOf kp.1 < R.1.length ∧ adm R then
      signAt (hedgedBase prims O M βmin tol enc k D bmsg) PS kp.1 kp.2 R (R.1.idxOf kp.1) m (cb, cp)
      else OracleProg.pure none).run H =
    (if R.1.idxOf kp.1 < R.1.length ∧ admLow prims βmin adm s R then
      signAt (hedgedBase prims O M βmin tol enc k D bmsg) PS kp.1 kp.2 R (R.1.idxOf kp.1) m (cb, cp)
      else OracleProg.pure none).run H
  by_cases hlow : LowDefect prims βmin s R
  · have hiff : (R.1.idxOf kp.1 < R.1.length ∧ adm R) ↔
        (R.1.idxOf kp.1 < R.1.length ∧ admLow prims βmin adm s R) :=
      ⟨fun h' => ⟨h'.1, h'.2, hlow⟩, fun h' => ⟨h'.1, h'.2.1⟩⟩
    simp only [hiff]
  · have hnot : ¬ (R.1.idxOf kp.1 < R.1.length ∧ admLow prims βmin adm s R) :=
      fun h' => hlow h'.2.2
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)]
    split_ifs with ha
    · have hchk : ¬ RingCheck prims βmin tol (O.gOrc H) R :=
        fun hc => h ⟨ha.2, lt_of_not_ge hlow, hc⟩
      have hb : ((hedgedBase prims O M βmin tol enc k D bmsg).bsign kp.2 R (R.1.idxOf kp.1) m
          cb).run H = none :=
        (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.hedged M) k D bmsg kp.2 R _ m cb
          H).trans (ite_eq_right_of_eq_false _ _ (eq_false fun h' => hchk h'.1))
      rw [run_signAt_eq _ PS H kp.1 kp.2 R _ m cb cp, hb]
      rfl
    · rfl

variable [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X] [Nonempty X]
  [AddGroup Y]

/-- **The hedged scheme and the hedged scheme on the rings of low defect, until a bad request**:
in experiment `b` with `Q` challenges, the probabilities that the adversary outputs `1` against the
anonymity challenger and against the challenger answering with the signer on `admLow` (with the
same challenges, `restrChallenger`) are at most the probability, against the second, that a bad
request (`BadReq`) is answered (`gameAdvantage_runLaw_le_untilBad`;
`hedgedScheme.run_sign_admLow` off the bad requests). -/
theorem gameAdvantage_anon_restr_le_bad {n : ℕ} {V : OracleView X Y} {t : ℕ}
    (A : AnonAdversary (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n V t) (s : ℝ)
    (b : Bool) (Q : ℕ) :
    gameAdvantage (runLaw (fun keys H => A (keys, V.view H))
        (fun keys => anonChallenger (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n keys b Q))
      (runLaw (fun keys H => A (keys, V.view H))
        (fun keys => restrChallenger prims O M βmin tol enc k D bmsg PS adm n
          (admLow prims βmin adm s) keys b Q)) anonAccepts ≤
      ((runLaw (fun keys H => A (keys, V.view H))
        (fun keys => restrChallenger prims O M βmin tol enc k D bmsg PS adm n
          (admLow prims βmin adm s) keys b Q)).toOuterMeasure
        (RunBad fun keys H c => BadReq prims O M βmin tol enc k D bmsg adm PS s keys H c)).toReal := by
  rw [anonAccepts_eq_runOutIn]
  have h₀ : ∀ keys : Fin n → Bytes 32,
      (anonChallenger (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n keys b Q).AnswersBy
        (fun ω H j c => anonAns (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) keys b Q H
          ω j c) :=
    fun keys => anonChallenger_answersBy (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) keys b Q
  have h₁ : ∀ keys : Fin n → Bytes 32,
      (restrChallenger prims O M βmin tol enc k D bmsg PS adm n
        (admLow prims βmin adm s) keys b Q).AnswersBy
        (restrAns prims O M βmin tol enc k D bmsg PS adm n
          (admLow prims βmin adm s) keys b Q) :=
    fun keys => restrChallenger_answersBy prims O M βmin tol enc k D bmsg PS adm n
      (admLow prims βmin adm s) keys b Q
  refine gameAdvantage_runLaw_le_untilBad h₀ h₁ (fun _ => rfl) (fun _ => Equiv.refl _)
    (fun _ _ => rfl) (fun keys H c => BadReq prims O M βmin tol enc k D bmsg adm PS s keys H c)
    (fun keys c H j req hj hbad => ?_) {true}
  change restrAns prims O M βmin tol enc k D bmsg PS adm n
      (admLow prims βmin adm s) keys b Q c H j req =
    anonAns (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) keys b Q H c j req
  have hj' : j < Q := hj
  simp only [restrAns, anonAns, hj', ↓reduceDIte]
  split_ifs with hv
  · exact (hedgedScheme.run_sign_admLow prims O M βmin tol enc k D bmsg adm PS s _ req.ring
      req.msg _ H fun h => hbad ⟨hv, h⟩).symm
  · rfl

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X] [Nonempty X]
  [AddGroup Y]
  [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **Signing by the hedged scheme on the rings `adm'`** at the oracle `H`: on a ring holding the
key and supported by `adm'`, the base signature at the key's position with its public value and
its proof (`run_signAt_eq`); `none` otherwise. -/
theorem hedgedScheme.run_sign_eq (adm' : KeyRing (PubKey p prims) N → Prop)
    [DecidablePred adm']
    (kp : (hedgedBase prims O M βmin tol enc k D bmsg).PK ×
      (hedgedBase prims O M βmin tol enc k D bmsg).SK)
    (R : KeyRing (PubKey p prims) N)
    (m : (hedgedBase prims O M βmin tol enc k D bmsg).Msg)
    (cb : (hedgedBase prims O M βmin tol enc k D bmsg).Coins) (cp : PS.Coins) (H : X → Y) :
    ((RingSignature.ofBase (hedgedBase prims O M βmin tol enc k D bmsg) PS adm').sign kp R m
        (cb, cp)).run H =
      if R.1.idxOf kp.1 < R.1.length ∧ adm' R then
        (((hedgedBase prims O M βmin tol enc k D bmsg).bsign kp.2 R (R.1.idxOf kp.1) m cb).run
          H).map fun σ => (((hedgedBase prims O M βmin tol enc k D bmsg).pub kp.1 σ).run H,
            (PS.prove ⟨R, m, ((hedgedBase prims O M βmin tol enc k D bmsg).pub kp.1 σ).run H⟩
              ⟨R.1.idxOf kp.1, σ⟩ cp).run H)
      else none := by
  dsimp only [RingSignature.ofBase_sign]
  change (if R.1.idxOf kp.1 < R.1.length ∧ adm' R then
      signAt (hedgedBase prims O M βmin tol enc k D bmsg) PS kp.1 kp.2 R (R.1.idxOf kp.1) m (cb, cp)
      else OracleProg.pure none).run H = _
  split_ifs
  · exact run_signAt_eq _ PS H kp.1 kp.2 R _ m cb cp
  · rfl

end Restrict

/-! ### The check oracle's points as labels of a search -/

/-- **A uniform probability is an average of an indicator.** -/
theorem _root_.PMF.toReal_toOuterMeasure_uniformOfFintype_eq_expect {α : Type*} [Fintype α]
    [Nonempty α] (S : Set α) [DecidablePred (· ∈ S)] :
    ((PMF.uniformOfFintype α).toOuterMeasure S).toReal = 𝔼 a, if a ∈ S then (1 : ℝ) else 0 := by
  rw [PMF.toReal_toOuterMeasure_uniformOfFintype, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole]

section Search

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)

omit [NeZero (bucketCount p)] [Fintype prims.Power2High] [DecidableEq prims.Power2High] in
/-- **A ring check is decided by the check oracle at the ring's points**: two check oracles that
agree at every point `(R, j, r)` give the same check of `R`. -/
theorem ringCheck_congr {G G' : CheckOrc p prims N reps} {R : KeyRing (PubKey p prims) N}
    (h : ∀ j r, G (R, j, r) = G' (R, j, r)) :
    RingCheck prims βmin tol G R ↔ RingCheck prims βmin tol G' R := by
  simp only [RingCheck, checkFails, h]

open Classical in
/-- **The label of a point**: the ring `R` at a check point `(R, j, r)` of a ring of defect above
`s`; no label elsewhere. -/
noncomputable def checkLabel (s : ℝ) (x : X) : Option (KeyRing (PubKey p prims) N) :=
  if h : ∃ a, O.gPt a = x ∧ s < ringDefect prims βmin a.1.1 then some h.choose.1 else none

omit [NeZero (bucketCount p)] [DecidableEq prims.Power2High] in
/-- The check points of a ring of defect above `s` carry its label. -/
theorem checkLabel_gPt (hg : Function.Injective O.gPt) {s : ℝ}
    (a : KeyRing (PubKey p prims) N × Fin N × Fin reps) (hs : s < ringDefect prims βmin a.1.1) :
    checkLabel O βmin s (O.gPt a) = some a.1 := by
  unfold checkLabel
  split_ifs with h
  · rw [hg h.choose_spec.1]
  · exact absurd ⟨a, rfl, hs⟩ h

omit [NeZero (bucketCount p)] [DecidableEq prims.Power2High] in
/-- A point that is not a check point of a ring of defect above `s` has no label. -/
theorem checkLabel_eq_none {s : ℝ} {x : X}
    (hx : ∀ a, O.gPt a = x → ¬ s < ringDefect prims βmin a.1.1) : checkLabel O βmin s x = none := by
  unfold checkLabel
  split_ifs with h
  · obtain ⟨a, ha, hs⟩ := h
    exact absurd hs (hx a ha)
  · rfl

omit [NeZero (bucketCount p)] [DecidableEq prims.Power2High] in
/-- A point off the check points has no label. -/
theorem checkLabel_eq_none_of_notMem {s : ℝ} {x : X} (hx : x ∉ Set.range O.gPt) :
    checkLabel O βmin s x = none :=
  checkLabel_eq_none O βmin fun a ha => absurd ⟨a, ha⟩ hx

omit [NeZero (bucketCount p)] [DecidableEq prims.Power2High] in
/-- The check points of a ring of defect at most `s` have no label. -/
theorem checkLabel_gPt_of_le (hg : Function.Injective O.gPt) {s : ℝ}
    (a : KeyRing (PubKey p prims) N × Fin N × Fin reps) (hs : ringDefect prims βmin a.1.1 ≤ s) :
    checkLabel O βmin s (O.gPt a) = none :=
  checkLabel_eq_none O βmin fun a' ha' => by
    rw [hg ha']
    exact not_lt.2 hs

/-- **The searched predicate**: the ring has defect above `s` and passes the check against the
check oracle read from `H`. -/
def CheckHit (s : ℝ) (R : KeyRing (PubKey p prims) N) (H : X → Y) : Prop :=
  s < ringDefect prims βmin R.1 ∧ RingCheck prims βmin tol (O.gOrc H) R

variable {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  (sp : OracleSplit Y Y₁ Y₂)

omit [NeZero (bucketCount p)] [DecidableEq prims.Power2High] [Fintype Y₁] [DecidableEq Y₁] in
/-- **The searched predicate reads only the base components at its label's points**, when the
check oracle's decoding reads only the base component (`W1Oracles.ReadsFst`). -/
theorem readsBlocks_checkHit (hsp : O.ReadsFst sp) (hg : Function.Injective O.gPt) (s : ℝ) :
    Quantum.ReadsBlocks sp.toEquiv (checkLabel O βmin s) (CheckHit O βmin tol s) := by
  intro R H H' hb
  by_cases hs : s < ringDefect prims βmin R.1
  · refine and_congr_right fun _ => ringCheck_congr βmin tol fun j r => ?_
    have hx := checkLabel_gPt O βmin hg (R, j, r) hs
    have := congrFun hb ⟨O.gPt (R, j, r), hx⟩
    exact hsp.gAns_eq _ _ this
  · simp only [CheckHit, hs, false_and]

omit [AddGroup Y] in
/-- **A ring hit with probability at most `checkError`** under the uniform oracle, for a domain
separation with uniform decodings and `x ≥ 1` (`W1Oracles.expect_ringCheck_gOrc_le`). -/
theorem toReal_uniform_checkHit_le [Fintype Msg] [DecidableEq Msg] [Fintype X] [DecidableEq X]
    [Fintype Y] [Nonempty Y]
    (hO : O.UniformSplit) (s : ℝ) {x : ℝ} (hx : 1 ≤ x) (R : KeyRing (PubKey p prims) N) :
    ((PMF.uniformOfFintype (X → Y)).toOuterMeasure {H | CheckHit O βmin tol s R H}).toReal ≤
      checkError reps tol s x := by
  classical
  rw [PMF.toReal_toOuterMeasure_uniformOfFintype_eq_expect]
  by_cases hs : s < ringDefect prims βmin R.1
  · simpa only [Set.mem_ofPred_eq, CheckHit, hs, true_and] using
      O.expect_ringCheck_gOrc_le hO βmin tol R hs.le hx
  · simp only [Set.mem_ofPred_eq, CheckHit, hs, false_and, ite_false, Finset.expect_const_zero]
    exact checkError_nonneg reps tol s (zero_le_one.trans hx)

end Search

/-! ### The bad requests through the search lemma -/

section BadSearch

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm]
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X] [Nonempty X] [AddGroup Y]
  {Y₁ Y₂ : Type} [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  {sp : OracleSplit Y Y₁ Y₂}

omit [DecidableEq Y] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y₁] [DecidableEq Y₁]
  [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **The signer on the rings of low defect reads the oracle off the labels**: at two oracles with
the same second components and the same values off the check points of the rings of defect above
`s` (`Quantum.AgreeOffLabels`), its answers agree, for a domain separation (`hO`), a mask oracle
off the base signer's points (`hdisj`) and an honest prover reading the base components only off a
set `B` holding the check points (`hPS`, `hB`). On a ring of defect at most `s` it reads the check
oracle at unlabelled points only. -/
theorem restrAns_admLow_congr (hO : O.UniformSplit) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    {B : Set X} (hPS : PS.ReadsOff sp B) (hB : Set.range O.gPt ⊆ B) {n : ℕ} (s : ℝ)
    (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ)
    (ω : Fin Q → (hedgedScheme prims O M βmin tol enc k D bmsg PS adm).SignCoins) (j : ℕ)
    (c : AnonRequest (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n) {H H' : X → Y}
    (h : Quantum.AgreeOffLabels sp.toEquiv (checkLabel O βmin s) H H') :
    restrAns prims O M βmin tol enc k D bmsg PS adm n
        (admLow prims βmin adm s) keys b Q ω H j c =
      restrAns prims O M βmin tol enc k D bmsg PS adm n
        (admLow prims βmin adm s) keys b Q ω H' j c := by
  have hg := hO.gPt_injective
  have hoff : ∀ z, checkLabel O βmin s z = none → H z = H' z := fun z hz => (h z).1 hz
  have hprf : ∀ x w cp, (PS.prove x w cp).run H = (PS.prove x w cp).run H' := fun x w cp =>
    hPS x w cp H H' (fun z => (h z).2) fun z hz =>
      hoff z (checkLabel_eq_none_of_notMem O βmin fun hr => hz (hB hr))
  have hmu : O.muOrc H = O.muOrc H' := funext fun a => by
    simp only [MLDSAOracles.muOrc]
    rw [hoff _ (checkLabel_eq_none_of_notMem O βmin fun ⟨b', hb'⟩ => hO.muPt_ne_gPt a b' hb'.symm)]
  have hch : O.chOrc H = O.chOrc H' := funext fun a => by
    simp only [MLDSAOracles.chOrc]
    rw [hoff _ (checkLabel_eq_none_of_notMem O βmin fun ⟨b', hb'⟩ => hO.chPt_ne_gPt a b' hb'.symm)]
  have hh : O.hOrc H = O.hOrc H' := by simp only [MLDSAOracles.hOrc, hmu, hch]
  have hm : ∀ (rv : (MaskSource.hedged M).Rnd) u,
      ((MaskSource.hedged M).read rv u).run H = ((MaskSource.hedged M).read rv u).run H' :=
    fun rv u => by
      change M.ans (H (M.pt (rv, u))) = M.ans (H' (M.pt (rv, u)))
      rw [hoff _ (checkLabel_eq_none_of_notMem O βmin
        fun ⟨b', hb'⟩ => hdisj _ (Or.inr (Or.inr ⟨b', rfl⟩)) ⟨_, hb'.symm⟩)]
  have hsign : ∀ (kp : (hedgedBase prims O M βmin tol enc k D bmsg).PK ×
      (hedgedBase prims O M βmin tol enc k D bmsg).SK)
      (R : KeyRing (PubKey p prims) N)
      (m : (hedgedBase prims O M βmin tol enc k D bmsg).Msg)
      (cb : (hedgedBase prims O M βmin tol enc k D bmsg).Coins) (cp : PS.Coins),
      ((RingSignature.ofBase (hedgedBase prims O M βmin tol enc k D bmsg) PS
        (admLow prims βmin adm s)).sign kp R m (cb, cp)).run H =
      ((RingSignature.ofBase (hedgedBase prims O M βmin tol enc k D bmsg) PS
        (admLow prims βmin adm s)).sign kp R m (cb, cp)).run H' := by
    intro kp R m cb cp
    refine (hedgedScheme.run_sign_eq prims O M βmin tol enc k D bmsg PS
      (admLow prims βmin adm s) kp R m cb cp H).trans
      (Eq.trans ?_ (hedgedScheme.run_sign_eq prims O M βmin tol enc k D bmsg PS
        (admLow prims βmin adm s) kp R m cb cp H').symm)
    split_ifs with ha
    · have hck : RingCheck prims βmin tol (O.gOrc H) R ↔ RingCheck prims βmin tol (O.gOrc H') R :=
        ringCheck_congr βmin tol fun j' r => by
          simp only [W1Oracles.gOrc]
          rw [hoff _ (checkLabel_gPt_of_le O βmin hg (R, j', r) ha.2.2)]
      have hbs : ((hedgedBase prims O M βmin tol enc k D bmsg).bsign kp.2 R (R.1.idxOf kp.1) m
          cb).run H = ((hedgedBase prims O M βmin tol enc k D bmsg).bsign kp.2 R (R.1.idxOf kp.1) m
          cb).run H' := by
        refine (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.hedged M) k D bmsg kp.2 R
          (R.1.idxOf kp.1) m cb H).trans (Eq.trans ?_ (run_bsign_w1BaseSigner prims O βmin tol enc
            (MaskSource.hedged M) k D bmsg kp.2 R (R.1.idxOf kp.1) m cb H').symm)
        simp only [hh, hm]
        by_cases hc : RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m)
        · have hc' : RingCheck prims βmin tol (O.gOrc H') R ∧
              MuDistinct prims (O.muOrc H') R (bmsg R m) := ⟨hck.1 hc.1, hmu ▸ hc.2⟩
          simp only [hc, hc', and_self, ite_true]
        · have hc' : ¬ (RingCheck prims βmin tol (O.gOrc H') R ∧
              MuDistinct prims (O.muOrc H') R (bmsg R m)) :=
            fun h' => hc ⟨hck.2 h'.1, hmu ▸ h'.2⟩
          simp only [hc, hc', ite_false]
      rw [hbs]
      simp only [hprf]
      rfl
    · rfl
  unfold restrAns
  split_ifs with hj hv
  · generalize ω ⟨j, hj⟩ = cc
    obtain ⟨cb, cp⟩ := cc
    exact hsign _ _ _ cb cp
  · rfl
  · rfl

/-- **A bad request is answered with probability at most `(√Q + 2 t)² · checkError`** against the
challenger answering with the signer on the rings of low defect, for every anonymity adversary
with `t` superposition queries whose table reads the base components only off a set `B` holding
the check points (`hV`, `hB`), every `Q`, and `x ≥ 1`: the QROM search lemma
(`RingSignature.toReal_runLaw_hit_le`) for the labels of the check points of the rings of defect
above `s` (`checkLabel`), the hit `CheckHit` of probability at most `checkError` per ring
(`toReal_uniform_checkHit_le`), and the label of a valid challenge on a supported ring its ring. -/
theorem toReal_runLaw_badReq_le (hO : O.UniformSplit) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) {B : Set X} (hPS : PS.ReadsOff sp B) (hB : Set.range O.gPt ⊆ B)
    {n : ℕ} {V : OracleView X Y} (hV : V.ReadsOff sp B) {t : ℕ}
    (A : AnonAdversary (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n V t) (s : ℝ)
    {x : ℝ} (hx : 1 ≤ x) (b : Bool) (Q : ℕ) :
    ((runLaw (fun keys H => A (keys, V.view H))
        (fun keys => restrChallenger prims O M βmin tol enc k D bmsg PS adm n
          (admLow prims βmin adm s) keys b Q)).toOuterMeasure
        (RunBad fun keys H c => BadReq prims O M βmin tol enc k D bmsg adm PS s keys H c)).toReal ≤
      (√Q + 2 * t) ^ 2 * checkError reps tol s x := by
  classical
  have hBn : ∀ z ∉ B, checkLabel O βmin s z = none := fun z hz =>
    checkLabel_eq_none_of_notMem O βmin fun hr => hz (hB hr)
  let lab : (Fin n → Bytes 32) →
      AnonRequest (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n →
      Option (KeyRing (PubKey p prims) N) :=
    fun keys c => if c.Valid keys ∧ adm c.ring then some c.ring else none
  refine le_trans (ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _)) (PMF.toOuterMeasure_mono _ ?_))
    (RingSignature.toReal_runLaw_hit_le (e := sp.toEquiv) (κ := checkLabel O βmin s)
      (fun keys H => A (keys, V.view H))
      (fun keys H H' hag => by
        rw [hV H H' (fun z => (hag z).2) fun z hz => (hag z).1 (hBn z hz)])
      (fun keys => restrChallenger_answersBy prims O M βmin tol enc k D bmsg PS adm n
        (admLow prims βmin adm s) keys b Q) (fun _ => le_rfl)
      (fun keys ω j c H H' hag => restrAns_admLow_congr prims O M βmin tol enc k D bmsg adm PS hO
        hdisj hPS hB s keys b Q ω j c hag)
      (readsBlocks_checkHit O βmin tol sp hsp hO.gPt_injective s)
      (checkError_nonneg reps tol s (zero_le_one.trans hx))
      (toReal_uniform_checkHit_le O βmin tol hO s hx) lab)
  rintro ⟨keys, H, o⟩ ⟨⟨pr, hpr, he, hhe, hbad⟩, -⟩
  exact ⟨pr, hpr, he, hhe, he.request.ring,
    by simp [lab, hbad.1, hbad.2.1], hbad.2.2⟩

end BadSearch

/-! ### The headline at any primitives -/

section Generic

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg}
  {βmin : ℚ≥0} {tol : ℕ} {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D]
  {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop} [DecidablePred adm] {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂]

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁`, against check-oracle queries**, at
any primitives `prims` with the signing and verification laws (`h_laws`, `hv`), an encoding `enc`
coherent with `bucketsOf` (`henc`) and `‖s₂‖∞ ≤ η` for every honest key (`hs2`): for every
anonymity adversary with `t` superposition queries whose table reads the base components of the
oracle only off the mask oracle's points and the check oracle's points (`hV`), and every number
`Q` of challenges, the advantage is at most
`Q · w1CouplingError + Q · wi (Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) +
2 (√Q + 2 t)² · checkError reps tol s x`, with `w1CouplingError` at `prims`.
The proof compares, in each experiment, the scheme with the scheme on the rings of defect at most
`s` (`admLow`) until a bad request (`gameAdvantage_anon_restr_le_bad`), bounds the bad requests by
the QROM search lemma (`toReal_runLaw_badReq_le`), and bounds the scheme on `admLow` by the
reprogramming hop with the fresh-mask signer's correctness error `0`
(`gameAdvantage_restrChallenger_le`, `correctWithin_w1BaseSigner`) and the coupling
(`expect_idealDist_le`). -/
theorem hedgedScheme.anonAdvantage_le_coupling (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hp : SigningParams p) (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (hedgedBase prims O M βmin tol enc k D bmsg) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n V t)
    (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError prims βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) := by
  have h0 := (gameAdvantage_anon_restr_le_bad prims O M βmin tol enc k D bmsg adm PS A s false Q).trans
    (toReal_runLaw_badReq_le prims O M βmin tol enc k D bmsg adm PS hO hdisj hsp hPS Set.subset_union_right hV A s hx false Q)
  have h1 := (gameAdvantage_anon_restr_le_bad prims O M βmin tol enc k D bmsg adm PS A s true Q).trans
    (toReal_runLaw_badReq_le prims O M βmin tol enc k D bmsg adm PS hO hdisj hsp hPS Set.subset_union_right hV A s hx true Q)
  rw [gameAdvantage_comm] at h1
  have hwi' : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (hedgedBase prims O M βmin tol enc k D bmsg)
        (admLow prims βmin adm s)
        (O.split.symm (ω₂, h₁))) wi := fun ω₂ h₁ =>
    (hwi ω₂ h₁).mono (RingSignature.ringRel_mono _ (fun _ h => h.1) _)
  have hC' : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (hedgedScheme prims O M βmin tol enc k D bmsg PS
        (admLow prims βmin adm s)) n =>
        c.Valid keys).card ≤ C := fun keys =>
    le_of_eq_of_le (Finset.card_equiv (show RingSignature.AnonRequest
        (hedgedScheme prims O M βmin tol enc k D bmsg PS
          (admLow prims βmin adm s)) n ≃
        RingSignature.AnonRequest (hedgedScheme prims O M βmin tol enc k D bmsg PS adm) n from
      ⟨fun c => ⟨c.ring, c.msg, c.user₀, c.user₁⟩, fun c => ⟨c.ring, c.msg, c.user₀, c.user₁⟩,
        fun _ => rfl, fun _ => rfl⟩) fun c => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl) (hC keys)
  have hmid := gameAdvantage_restrChallenger_le prims O M βmin tol enc k D bmsg PS adm n sp
    (admLow prims βmin adm s) hM hdisj hMsp Set.subset_union_left hPS hV hwi' hC'
    (correctWithin_w1BaseSigner prims h_laws hv henc hs2 (MaskSource.fresh M) O βmin tol k D bmsg)
    A Q
  simp only [NNReal.coe_zero, mul_zero, add_zero] at hmid
  have hE := expect_idealDist_le prims O M βmin tol enc k D bmsg PS (admLow prims βmin adm s) n hp
    hβ0 hβt hT hO hMask h_laws hv henc hs2 hθ0 hθ1 hs1 hLk hLk1 (fun _ h => h.2) hC'
  have hlin : (𝔼 keys : (Fin n → Bytes 32), 𝔼 ω₂ : ({x // O.IsPt x} → Y),
        ((Q : ℝ) * idealDist prims O M βmin tol enc k D bmsg
          PS (admLow prims βmin adm s) n
          keys ω₂ + Q * wi (Q * C))) =
      Q * 𝔼 keys : (Fin n → Bytes 32), 𝔼 ω₂ : ({x // O.IsPt x} → Y),
        idealDist prims O M βmin tol enc k D bmsg PS
          (admLow prims βmin adm s) n keys
          ω₂ + Q * wi (Q * C) := by
    simp only [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty,
      ← Finset.mul_expect]
  have hmid' := (hmid.trans_eq (congrArg (· + _) hlin)).trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)) le_rfl) le_rfl)
  refine le_trans (gameAdvantage_le_add₃ _ _ _ _ anonAccepts)
    (le_trans (add_le_add (add_le_add h0 hmid') h1) (le_of_eq ?_))
  ring

end Generic

/-! ### The headline at the concrete primitives -/

section Concrete

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps} {M : MaskOracle X Y p T Msg}
  {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [DecidablePred adm] {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂]

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁`, against check-oracle queries**, at
the concrete primitives of an approved parameter set: for every anonymity adversary with `t`
superposition queries whose table reads the base components of the oracle only off the mask
oracle's points and the check oracle's points (`hV`: the check oracle `G` is reached by queries
only), and every number `Q` of challenges, the advantage is at most
`Q · w1CouplingError + Q · wi (Q · C) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) +
2 (√Q + 2 t)² · checkError reps tol s x`.
The oracle's values split as `Y ≃+ Y₁ × Y₂` (`sp`): the base signer's decodings and the mask
decoding read `Y₁` (`hsp`, `hMsp`), and the honest prover reads `Y₁` only off the mask and check
points (`hPS`). It is `hedgedScheme.anonAdvantage_le_coupling` with the signing and verification
laws of the concrete primitives, the coherence of `concreteEnc` and `‖s₂‖∞ ≤ η` for every honest
key. -/
@[headline]
theorem w1Concrete.anonAdvantage_le_coupling (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hp : p.isApproved) (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1ConcreteBase p O M βmin tol k D bmsg) adm (O.split.symm (ω₂, h₁)))
      wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Concrete p O M βmin tol k D bmsg PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1Concrete p O M βmin tol k D bmsg PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError (concretePrimitivesKeyGen p) βmin N n s θ C k D Lk +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  hedgedScheme.anonAdvantage_le_coupling (concretePrimitivesKeyGen p) sp
    (SigningParams.of_isApproved hp) hT hβ0 hβt hO hMask (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (concreteEnc_highBitsVec_keyGen hp)
    (fun seed => keyGenFromSeed_s2_bounded hp seed) hM hdisj hsp hMsp hPS hV hwi hC hθ0 hθ1 hs1 hx
    hLk hLk1 A Q

open Classical in
/-- **`w1Concrete.anonAdvantage_le_coupling` at check parameters** (`CheckParams`: check error at
most `2^-240`, for instance `checkParams_tol2`): the check term is `2 (√Q + 2 t)² / 2^240`. -/
@[headline]
theorem w1Concrete.anonAdvantage_le_coupling_checkParams (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hp : p.isApproved) (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1ConcreteBase p O M βmin tol k D bmsg) adm (O.split.symm (ω₂, h₁)))
      wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Concrete p O M βmin tol k D bmsg PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hcp : CheckParams reps tol s x) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1Concrete p O M βmin tol k D bmsg PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError (concretePrimitivesKeyGen p) βmin N n s θ C k D Lk +
        Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 / 2 ^ 240) := by
  refine (w1Concrete.anonAdvantage_le_coupling sp hp hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hcp.s_lt_one hcp.one_le_x hLk hLk1 A Q).trans ?_
  have h := mul_le_mul_of_nonneg_left hcp.checkError_le (sq_nonneg (√(Q : ℝ) + 2 * t))
  rw [mul_one_div] at h
  linarith

end Concrete

/-! ### ML-DSA-44, ML-DSA-65 and ML-DSA-87 -/

section Instances

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [Fintype Msg] [DecidableEq Msg] [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y] [Nonempty Y] {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg] {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂]

section P44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-44 ring signature publishing `w₁`** (`w1Scheme44`;
`w1Concrete.anonAdvantage_le_coupling` at ML-DSA-44): for every anonymity adversary with `t` superposition
queries whose table reads the base components only off the mask and check points, and every
number `Q` of challenges, the advantage is at most `Q · w1CouplingError + Q · wi (Q · C) +
2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² · checkError reps tol s x`. -/
@[headline]
theorem w1Scheme44.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm (O.split.symm (ω₂, h₁)))
      wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme44 O M βmin tol k D bmsg PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1Scheme44 O M βmin tol k D bmsg PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Concrete.anonAdvantage_le_coupling sp (Or.inl rfl) hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV hwi
    hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end P44

section P65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-65 ring signature publishing `w₁`** (`w1Scheme65`;
`w1Concrete.anonAdvantage_le_coupling` at ML-DSA-65): for every anonymity adversary with `t` superposition
queries whose table reads the base components only off the mask and check points, and every
number `Q` of challenges, the advantage is at most `Q · w1CouplingError + Q · wi (Q · C) +
2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² · checkError reps tol s x`. -/
@[headline]
theorem w1Scheme65.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm (O.split.symm (ω₂, h₁)))
      wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme65 O M βmin tol k D bmsg PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1Scheme65 O M βmin tol k D bmsg PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Concrete.anonAdvantage_le_coupling sp (Or.inr (Or.inl rfl)) hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV hwi
    hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end P65

section P87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-87 ring signature publishing `w₁`** (`w1Scheme87`;
`w1Concrete.anonAdvantage_le_coupling` at ML-DSA-87): for every anonymity adversary with `t` superposition
queries whose table reads the base components only off the mask and check points, and every
number `Q` of challenges, the advantage is at most `Q · w1CouplingError + Q · wi (Q · C) +
2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)) + 2 (√Q + 2 t)² · checkError reps tol s x`. -/
@[headline]
theorem w1Scheme87.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm (O.split.symm (ω₂, h₁)))
      wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Scheme87 O M βmin tol k D bmsg PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1Scheme87 O M βmin tol k D bmsg PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Concrete.anonAdvantage_le_coupling sp (Or.inr (Or.inr rfl)) hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV hwi
    hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end P87

end Instances

/-! ### Ring-binding and converted base messages -/

section BaseMessages

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂]

section BindGeneric

variable {O : W1Oracles X Y p (concretePrimitivesKeyGen p)
    (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg) N reps}
  {M : MaskOracle X Y p T (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg)}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing
    (w1ConcreteBase p O M βmin tol k D Prod.mk).PK N → Prop}
  [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁` with ring-binding base messages**
(`w1BindConcrete`; `w1Concrete.anonAdvantage_le_coupling` at `bmsg := Prod.mk`). -/
@[headline]
theorem w1BindConcrete.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hp : p.isApproved) (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel
        (w1ConcreteBase p O M βmin tol k D Prod.mk) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1BindConcrete p O M βmin tol k D PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1BindConcrete p O M βmin tol k D PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError (concretePrimitivesKeyGen p) βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Concrete.anonAdvantage_le_coupling sp hp hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end BindGeneric

section Bind44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D Prod.mk).PK N → Prop}
  [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-44 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindScheme44`; `w1Scheme44.anonAdvantage_le` at `bmsg := Prod.mk`). -/
@[headline]
theorem w1BindScheme44.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1BindScheme44 O M βmin tol k D PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1BindScheme44 O M βmin tol k D PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Scheme44.anonAdvantage_le sp  hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end Bind44

section Bind65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D Prod.mk).PK N → Prop}
  [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-65 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindScheme65`; `w1Scheme65.anonAdvantage_le` at `bmsg := Prod.mk`). -/
@[headline]
theorem w1BindScheme65.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1BindScheme65 O M βmin tol k D PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1BindScheme65 O M βmin tol k D PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Scheme65.anonAdvantage_le sp  hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end Bind65

section Bind87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D Prod.mk).PK N → Prop}
  [DecidablePred adm]

open Classical in
/-- **Anonymity of the ML-DSA-87 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindScheme87`; `w1Scheme87.anonAdvantage_le` at `bmsg := Prod.mk`). -/
@[headline]
theorem w1BindScheme87.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1BindScheme87 O M βmin tol k D PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1BindScheme87 O M βmin tol k D PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Scheme87.anonAdvantage_le sp  hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end Bind87

section ConvGeneric

variable {O : W1Oracles X Y p (concretePrimitivesKeyGen p)
    Msg N reps}
  {M : MaskOracle X Y p T Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m))) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing
    (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m)).PK N → Prop}
  [DecidablePred adm]

open Classical in
/-- **Anonymity of the converted ML-DSA ring signature publishing `w₁`** (`w1ConvConcrete`;
`w1Concrete.anonAdvantage_le_coupling` at `bmsg := fun _ m => m`). -/
@[headline]
theorem w1ConvConcrete.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hp : p.isApproved) (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel
        (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m)) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1ConvConcrete p O M βmin tol k D PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1ConvConcrete p O M βmin tol k D PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError (concretePrimitivesKeyGen p) βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Concrete.anonAdvantage_le_coupling sp hp hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end ConvGeneric

section Conv44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg
    Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m))) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).PK N → Prop}
  [DecidablePred adm]

open Classical in
/-- **Anonymity of the converted ML-DSA-44 ring signature publishing `w₁`** (`w1ConvScheme44`;
`w1Scheme44.anonAdvantage_le` at `bmsg := fun _ m => m`). -/
@[headline]
theorem w1ConvScheme44.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1ConvScheme44 O M βmin tol k D PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1ConvScheme44 O M βmin tol k D PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Scheme44.anonAdvantage_le sp  hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end Conv44

section Conv65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg
    Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m))) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).PK N → Prop}
  [DecidablePred adm]

open Classical in
/-- **Anonymity of the converted ML-DSA-65 ring signature publishing `w₁`** (`w1ConvScheme65`;
`w1Scheme65.anonAdvantage_le` at `bmsg := fun _ m => m`). -/
@[headline]
theorem w1ConvScheme65.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1ConvScheme65 O M βmin tol k D PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1ConvScheme65 O M βmin tol k D PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Scheme65.anonAdvantage_le sp  hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end Conv65

section Conv87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg
    Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m))) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).PK N → Prop}
  [DecidablePred adm]

open Classical in
/-- **Anonymity of the converted ML-DSA-87 ring signature publishing `w₁`** (`w1ConvScheme87`;
`w1Scheme87.anonAdvantage_le` at `bmsg := fun _ m => m`). -/
@[headline]
theorem w1ConvScheme87.anonAdvantage_le (sp : RingSignature.OracleSplit Y Y₁ Y₂)
    (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hsp : O.ReadsFst sp) (hMsp : M.ReadsFst sp)
    (hPS : PS.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {V : OracleView X Y} (hV : V.ReadsOff sp (Set.range M.pt ∪ Set.range O.gPt))
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)) adm
        (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1ConvScheme87 O M βmin tol k D PS adm) n =>
        c.Valid keys).card ≤ C)
    {s θ x Lk : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hx : 1 ≤ x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1)
    {t : ℕ} (A : AnonAdversary (w1ConvScheme87 O M βmin tol k D PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * w1CouplingError Kg βmin N n s θ C k D Lk + Q * wi (Q * C) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
        2 * ((√Q + 2 * t) ^ 2 * checkError reps tol s x) :=
  w1Scheme87.anonAdvantage_le sp  hT hβ0 hβt hO hMask hM hdisj hsp hMsp hPS hV
    hwi hC hθ0 hθ1 hs1 hx hLk hLk1 A Q

end Conv87

end BaseMessages

end GordieHowe.Ring.MLDSAW1
