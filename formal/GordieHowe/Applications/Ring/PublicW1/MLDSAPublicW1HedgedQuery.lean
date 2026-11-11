-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Hedged
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Query

@[expose] public section

/-!
# The hedged ML-DSA ring signer publishing `w₁` against adversaries with `q` check-oracle queries

The headlines of `MLDSAPublicW1Hedged.lean` with the check term of `MLDSAPublicW1Query.lean`:
the adversary's choices read the check oracle `G` through at most `q` classical queries
(`CheckQueryBounded`, at every mask oracle), and read the mask oracle through at most `q`
classical queries (`MaskedSigner.QueryBounded`). The check term `C / 2^240`, which counts the
candidate rings per key vector, becomes `2 (q + 1) / 2^240`.

- `MaskedSigner.restrict`: the hedged signer of the signer that also refuses the rings outside a
  predicate (`PubSigner.restrict`).
- `expect_restrictBad_le`, `advantage_hedged_le_restrictLow`: the hedged signer against the
  hedged signer that also refuses the rings of defect above `s` (`lowOk`): identical until the
  chosen ring has defect above `s` and passes the check (`advantage_le_restrict_one`), which the
  search lemma bounds by `(q + 1) · checkError` (`expect_badChoice_le`).
- `meanAttempt_none_le_keepLevel`, `expect_ite_oracleError_le`,
  `advantage_restrictLow_le_hedged`: against the restricted signer, every admitted ring has
  defect at most `s`, so one hedged call keeps with probability at least the keep level when the
  anonymity error is below `1/2`, with no check term (`keep_ge_of_familyBound_lt`), and the
  hedged step (`MaskedSigner.advantage_le_atMask`) needs no check either.
- `advantage_le_bkm06_mldsa{44,65,87}_hedged_query`: `advantage_le_bkm06_mldsa{44,65,87}_hedged`
  with the check term `2 (q + 1) / 2^240`.
- `advantage_le_bkm06_mldsa{44,65,87}_hedged_keep_query`:
  `advantage_le_bkm06_mldsa{44,65,87}_hedged_keep` with the check term `2 (q + 1) / 2^240`; the
  hedged error has no check term.

Deterministic signing (`rnd = 0`) is not covered.
-/

namespace GordieHowe.Ring

section Restrict

variable {N : ℕ} {RMsg : Type} {S : PubSigner N RMsg} [∀ H R m, Decidable (S.Admit H R m)]

variable [Fintype S.Sig] [Fintype S.Pub]

/-- **The hedged signer of the signer that also refuses the rings outside `Ok`**: the same
nonces, mask points, masks and attempts; only the refusal rule changes (`PubSigner.restrict`). -/
@[reducible]
def MaskedSigner.restrict (W : MaskedSigner S) (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) :
    MaskedSigner (S.restrict Ok) :=
  { W with signLaw_eq := W.signLaw_eq }

/-- The hedged signer of the restricted signer is the restricted hedged signer. -/
theorem MaskedSigner.real_restrict (W : MaskedSigner S) [Fintype W.Rnd] [Nonempty W.Rnd]
    [DecidableEq W.Rnd] [Fintype W.Pt] [DecidableEq W.Pt] [Fintype W.Mask] [Nonempty W.Mask]
    (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) :
    (W.restrict Ok).real = W.real.restrict fun HY R m => Ok HY.1 R m :=
  rfl

end Restrict

namespace MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA PMF Finset
open scoped ENNReal BigOperators

section Signer

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High]

section HedgedQuery

open IOP GordieHowe.SPBCS GordieHowe.QROM

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p} {T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e} {n Q : ℕ}

/-- **The rings of defect at most `s`**, as a refusal predicate of the game's oracles with a mask
oracle, the ring and the message (`lowOk` at the game's oracles). -/
def lowOkMask (βmin : ℚ≥0) (s : ℝ) {N reps : ℕ} {Yo : Type} (HY : GameOrc prims Msg N reps × Yo)
    (R : RingOf (PubKey p prims) N) (m : Msg) : Prop :=
  lowOk prims βmin s HY.1 R m

omit [∀ j i, Nonempty ((P j).Challenge i)] in
open Classical in
/-- **The chosen ring is admitted, has defect above `s`, and the adversary reads the check
oracle through `q` queries**: at the users' coins `keys`, the probability over the game's oracles
and the proof system's oracle that the signer admits the ring of the challenge and the ring has
defect above `s` is at most `(q + 1) · checkError reps tol s x` for every `x ≥ 1`
(`expect_badChoice_le`: the admitted ring passes the check). -/
theorem expect_restrictBad_le
    (A : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n 1) {q : ℕ}
    (hq : CheckQueryBounded prims A q) (s : ℝ) {x : ℝ} (hx : 1 ≤ x)
    (keys : Fin n → _root_.MLDSA.Bytes 32) :
    𝔼 H : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
      𝔼 h : Query k kN kS L → Out k e,
        (if (pubSigner prims (Msg := Msg) N βmin reps tol enc).Admit H
              (A.choose 0 keys H h Fin.elim0).ring (A.choose 0 keys H h Fin.elim0).msg ∧
            ¬ lowOk prims βmin s H (A.choose 0 keys H h Fin.elim0).ring
              (A.choose 0 keys H h Fin.elim0).msg
          then 1 else 0 : ℝ) ≤
      (q + 1) * checkError reps tol s x := by
  refine (Finset.expect_prod_eq_expect_expect (α := SchOrc p Msg)
    (β := CheckOrc p prims N reps) _).trans_le ?_
  refine (Finset.expect_le_expect fun H _ => ?_).trans_eq (Fintype.expect_const _)
  rw [Finset.expect_comm]
  refine (Finset.expect_le_expect fun h _ => ?_).trans_eq (Fintype.expect_const _)
  obtain ⟨alg, halg⟩ := hq.choose 0 keys H h Fin.elim0
  refine (Finset.expect_le_expect fun G _ => ?_).trans
    (expect_badChoice_le prims (βmin := βmin) (tol := tol) s hx alg RingChoice.ring)
  rw [halg G]
  split_ifs with h' hb'
  · exact le_rfl
  · exact absurd ⟨lt_of_not_ge h'.2, h'.1.2⟩ hb'
  · norm_num
  · exact le_rfl

variable {E : (j : ι) → (M.comp j).Encoder}
  {V : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt →
    FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  {honest : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Wit →
    R → CausalProver P τ (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt}

open Classical in
omit [DecidableEq R] in
/-- **The hedged signer against the hedged signer that also refuses the rings of defect above
`s`** (one challenge): for an adversary whose choices read the check oracle through `q` queries
at every mask oracle (`hqc`), the advantage is at most the advantage against the restricted
signer plus `2 (q + 1) · checkError reps tol s x` for every `x ≥ 1` (`advantage_le_restrict_one`,
`expect_restrictBad_le` at every mask oracle). -/
theorem advantage_hedged_le_restrictLow
    (A : PubAnonAdversary (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).real M n 1)
    {q : ℕ} (hqc : ∀ Y, CheckQueryBounded prims
      ((hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).atMask A Y) q)
    (s : ℝ) {x : ℝ} (hx : 1 ≤ x)
    (D : (Fin n → _root_.MLDSA.Bytes 32) →
      (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).real.Orc →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) M.NIProof 1 → Prop) :
    A.advantage (V := fun HY => V HY.1) E (fun HY => Qs HY.1) (fun HY => honest HY.1) D ≤
      (A.restrict (lowOkMask prims βmin s)).advantage (V := fun HY => V HY.1) E
          (fun HY => Qs HY.1) (fun HY => honest HY.1) D +
        2 * ((q + 1) * checkError reps tol s x) := by
  refine (PubAnonAdversary.advantage_le_restrict_one
    (S := (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).real)
    (lowOkMask prims βmin s) E (fun HY => Qs HY.1) (fun HY => honest HY.1) A D).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le_two))
  refine (Finset.expect_le_expect fun keys _ => ?_).trans_eq (Fintype.expect_const _)
  refine (Finset.expect_prod_eq_expect_expect
    (α := (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc)
    (β := (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).MaskOrc)
    _).trans_le ?_
  rw [Finset.expect_comm]
  refine (Finset.expect_le_expect fun Y _ => ?_).trans_eq (Fintype.expect_const _)
  exact expect_restrictBad_le prims _ (hqc Y) s hx keys

open Classical in
/-- **On a ring of defect at most `s`, a hedged call keeps when the anonymity error is below
`1/2`**: for a valid admissible challenge of the set of `A'` whose ring has defect at most `s`,
at oracles where the anonymity error of `A'` is below `1/2`, one hedged call with fresh masks
rejects with probability at most `1 - Lk` for any `Lk` at most the keep level
(`meanAttempt_none_le`, `keep_ge_of_familyBound_lt`). -/
theorem meanAttempt_none_le_keepLevel
    (A' : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n Q)
    (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hs1 : s < 1) {Lk : ℝ} (hLk : Lk ≤ keepLevel p βmin s θ)
    (keys : Fin n → _root_.MLDSA.Bytes 32) (HG : GameOrc prims Msg N reps)
    (c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n) (hcm : c ∈ A'.choices)
    (hv : c.Valid _ keys) (ha : RingAdmissible prims βmin tol HG c.ring c.msg)
    (hd : LowDefect prims βmin s c.ring)
    (hO : oracleError prims A' hp hβ0 hβt s θ keys HG.1 < 1 / 2) (b : Bool) :
    (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).meanAttempt HG keys c b none ≤
      1 - ENNReal.ofReal Lk := by
  have hlt : c.idx b < c.ring.1.length := by
    cases b
    · exact hv.idx₀_lt
    · exact hv.idx₁_lt
  refine (meanAttempt_none_le prims hT keys HG c b hlt ha).trans ?_
  let m : ValidChoiceMu prims A' s keys HG.1.1 := ⟨⟨c, hcm⟩, hv, ha.1, hd⟩
  have hne : Nonempty (ValidChoiceMu prims A' s keys HG.1.1) := ⟨m⟩
  have hF : familyBound (familyMu prims A' hp hβ0 hβt s keys HG.1.1) θ HG.1.2 < 1 / 2 := by
    unfold oracleError at hO
    rwa [dif_pos hne] at hO
  have hkeep := keep_ge_of_familyBound_lt (familyMu prims A' hp hβ0 hβt s keys HG.1.1) hθ0 hθ1
    (familyMu_mass_pos hp hβ0 hβt hs1 keys HG.1.1) hF m b
  have hnone : (familyMu prims A' hp hβ0 hβt s keys HG.1.1 m).attempt b HG.1.2 none =
      ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1 ⟨c.idx b, hlt⟩ c.msg
        (schemeOrc HG.1) none :=
    (ringAttemptOut_apply_none prims N βmin reps tol enc hp hβ0 hβt keys HG.1.1 c hv ha.1 HG.1.2
      b).symm
  have hmass : (1 - s) * Fintype.card (BucketVec p) ≤
      (familyMu prims A' hp hβ0 hβt s keys HG.1.1 m).wts.mass := by
    calc (1 - s) * Fintype.card (BucketVec p) = ∑ _v : BucketVec p, (1 - s) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v _ =>
          one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt hd v
  have hlev : Lk ≤
      (1 - ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1 ⟨c.idx b, hlt⟩
        c.msg (schemeOrc HG.1) none).toReal := by
    calc Lk ≤ keepLevel p βmin s θ := hLk
      _ ≤ (standinScale p * βmin).toReal *
          (θ * (familyMu prims A' hp hβ0 hβt s keys HG.1.1 m).wts.mass) / 2 := by
          unfold keepLevel
          gcongr
      _ ≤ (1 - (familyMu prims A' hp hβ0 hβt s keys HG.1.1 m).attempt b HG.1.2 none).toReal :=
          hkeep
      _ = _ := by rw [hnone]
  set r := ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1 ⟨c.idx b, hlt⟩
    c.msg (schemeOrc HG.1) none
  have hr1 : r ≤ 1 := PMF.coe_le_one _ _
  have h1 : ENNReal.ofReal Lk ≤ 1 - r := by
    rw [← ENNReal.ofReal_toReal (a := 1 - r) (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
    exact ENNReal.ofReal_le_ofReal hlev
  have hx1 : ENNReal.ofReal Lk ≤ 1 := h1.trans tsub_le_self
  rw [ENNReal.le_sub_iff_add_le_right (ne_top_of_le_ne_top ENNReal.one_ne_top hx1) hx1]
  calc r + ENNReal.ofReal Lk ≤ r + (1 - r) := add_le_add le_rfl h1
    _ = 1 := add_tsub_cancel_of_le hr1

open Classical in
/-- **The anonymity error is below `1/2` except rarely** (Markov): the probability over the game's
oracles that the anonymity error at the users' coins `keys` is at least `1/2` is at most twice its
average. -/
theorem expect_ite_oracleError_le
    (A' : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n Q)
    (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hs1 : s < 1)
    (hθ0 : 0 < θ) (keys : Fin n → _root_.MLDSA.Bytes 32) :
    𝔼 HG : GameOrc prims Msg N reps,
        (if oracleError prims A' hp hβ0 hβt s θ keys HG.1 < 1 / 2 then 0 else 1 : ℝ) ≤
      2 * 𝔼 HG : GameOrc prims Msg N reps, oracleError prims A' hp hβ0 hβt s θ keys HG.1 := by
  rw [Finset.mul_expect]
  refine Finset.expect_le_expect fun HG _ => ?_
  have h0 := oracleError_nonneg (A := A') hp hβ0 hβt hs1 hθ0 keys HG.1
  split_ifs with hO
  · linarith
  · push Not at hO
    linarith

open Classical in
omit [DecidableEq R] in
/-- **Anonymity against the restricted hedged signer from anonymity against the restricted
ideal-mask signer** (one challenge): for an adversary and a distinguisher with `q` mask-oracle
queries per phase (`hq`), against the hedged signer that also refuses the rings of defect above
`s`, the advantage is at most the average over the mask oracle of the advantage of the adversary
at that mask oracle against the restricted ideal-mask signer, plus twice the hedged error with
the keep bound `Lk` on the event that the anonymity error of the adversary at any fixed mask
oracle `Y0` is below `1/2` (`MaskedSigner.advantage_le_atMask`,
`meanAttempt_none_le_keepLevel`). No check term enters. -/
theorem advantage_restrictLow_le_hedged
    (A : PubAnonAdversary (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).real M n 1)
    (D : (Fin n → _root_.MLDSA.Bytes 32) →
      (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).real.Orc →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) M.NIProof 1 → Prop) {q : ℕ}
    (hq : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).QueryBounded A D q) (ka : ℕ)
    (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hs1 : s < 1) {Lk : ℝ} (hLk : Lk ≤ keepLevel p βmin s θ)
    (Y0 : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).MaskOrc) :
    (A.restrict (lowOkMask prims βmin s)).advantage (V := fun HY => V HY.1) E
        (fun HY => Qs HY.1) (fun HY => honest HY.1) D ≤
      𝔼 Y : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).MaskOrc,
        (((hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).atMask A Y).restrict
          (lowOk prims βmin s)).advantage E Qs honest (fun keys H => D keys (H, Y)) +
      2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32, 𝔼 HG : GameOrc prims Msg N reps,
        ((hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).hedgeError 1 q ka
          (1 - if oracleError prims ((hedgedSigner prims (Msg := Msg) N βmin reps tol enc T
              hT).atMask A Y0) hp hβ0 hβt s θ keys HG.1 < 1 / 2
            then ENNReal.ofReal Lk else 0)).toReal :=
  MaskedSigner.advantage_le_atMask
    (W := (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).restrict (lowOk prims βmin s))
    (A.restrict (lowOkMask prims βmin s) :) D ⟨hq.choose, hq.dist⟩ ka _
    (fun _ _ => tsub_le_self) fun keys HG c hc hv ha b => by
      split_ifs with hO
      · exact meanAttempt_none_le_keepLevel prims hT _ hp hβ0 hβt hθ0 hθ1 hs1 hLk keys HG c hc hv
          ha.1 ha.2 hO b
      · rw [tsub_zero]
        exact PMF.coe_le_one _ _

end HedgedQuery

end Signer

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity IOP GordieHowe.SPBCS GordieHowe.QROM
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

section HedgedQuery_mldsa44

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc _root_.MLDSA.mldsa44)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).real (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [DecidableEq R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc _root_.MLDSA.mldsa44)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps ×
      (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44) →
    (Query k kN kS L → Out k e) → PubHist (BucketVec _root_.MLDSA.mldsa44) (M GB GS GA).NIProof 1 →
      Prop)

open Classical in
omit [DecidableEq R] in
/-- **Anonymity at ML-DSA-44 with FIPS 204 hedged signing, against adversaries with `q`
check-oracle queries** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the
start as in CCLM22 Experiment 2, p. 21): `advantage_le_bkm06_mldsa44_hedged` with the check term
`2 (q + 1) / 2^240` in place of `C / 2^240`, for an adversary whose choices read the check oracle
through `q` classical queries at every mask oracle (`hqc`, `CheckQueryBounded`) and that, with
the distinguisher, reads the mask oracle through `q` classical queries per phase (`hq`), with
full key exposure; at every fixed mask oracle the ideal-mask bound is
`advantage_le_bkm06_mldsa44_query_checkParams`. `s̄` is a lower bound on the keep probability of
one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step). Deterministic signing
(`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa44_hedged_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
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
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q)
    (hqc : ∀ GB GS GA Y, CheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y) q) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44)
      (_GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l),
      (Fin n → _root_.MLDSA.Bytes 32) →
        GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
                    reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeError 1 q ka
                      (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240
  have hrow : CheckParams reps tol (1 / 2) 89 := by
    rw [hreps, htol]
    exact checkParams_tol2
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  have hm : ∀ X : ℝ, X / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * (βmin : ℝ≥0∞).toReal)) =
      X / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := fun X => by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  -- at every fixed mask oracle, the ideal-mask bound against `q` check-oracle queries
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44,
      𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y).advantage
                (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
                (fun keys H => D GB GS GA keys (H, Y)) ≤ B := fun Y => by
    have h := advantage_le_bkm06_mldsa44_query_checkParams
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
        βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y)
      (fun GB GS GA keys H => D GB GS GA keys (H, Y)) (fun GB GS GA => hqc GB GS GA Y) hβ0 hβ1
      hβt hrow hθ0 hθ1 Rv hz hC
    rw [h2, hm] at h
    exact h
  -- at every oracle, the hedged step
  refine expect3_le_of_mix _ _ (fun GB GS GA
      (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44) =>
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA)
          (Qs GB GS GA) (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y)))
    (fun GB GS GA => ?_) hY
  exact advantage_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
    (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
    (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka (sbar GB GS GA) (hkeep GB GS GA)

open Classical in
omit [DecidableEq R] in
/-- **Anonymity at ML-DSA-44 with FIPS 204 hedged signing against adversaries with `q`
check-oracle queries, the keep bound discharged** (BKM06 Definition 4, ePrint 2005/304, p. 6,
`Q = 1`): `advantage_le_bkm06_mldsa44_hedged_keep` with the check term `2 (q + 1) / 2^240` in
place of `C / 2^240`, for an adversary whose choices read the check oracle through `q` classical
queries at every mask oracle (`hqc`) and that, with the distinguisher, reads the mask oracle
through `q` classical queries per phase (`hq`), with full key exposure. The proof compares the
hedged signer with the hedged signer that also refuses the rings of defect above `1/2`
(`advantage_hedged_le_restrictLow`, the check term); against it every admitted ring has defect at
most `1/2`, so the keep bound `s̄ = β_min θ / 64` holds when the anonymity error is below `1/2`,
with no check term in the hedged error (`advantage_restrictLow_le_hedged`), and the ideal-mask
bound has none either (`advantage_restrictLow_le`, `expect_le_bkm06_mldsa44_of`). For every
number `k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 (q + 1) / 2^240 + 2 · ((k² + 2 q k) / 2^256 + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity +
McDiarmid)))`. Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa44_hedged_keep_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
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
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q)
    (hqc : ∀ GB GS GA Y, CheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y) q) (ka : ℕ) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240 +
        2 * ((ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ / 64) ^ ka +
          2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty (τ := _root_.MLDSA.mldsa44.tau) (by
    rw [show _root_.MLDSA.mldsa44.tau = 39 from rfl]; norm_num [ringDegree])
  have hp' := SigningParams.of_isApproved isApproved_mldsa44
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  set Y0 : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44 :=
    fun _ => Classical.arbitrary _
  set A' := fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
    βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y0
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
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  have hm : ∀ X : ℝ, X / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * (βmin : ℝ≥0∞).toReal)) =
      X / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := fun X => by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  set RM : ℝ := 2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
    √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))
  set Bi : ℝ := 2 * RM +
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (M GB GS GA).wiError δ C
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44,
      𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            (((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y).restrict
                (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
                (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
                (fun keys H => D GB GS GA keys (H, Y)) ≤ Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa44
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa44 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa44 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) (hC GB GS GA) (fun keys H => D GB GS GA keys (H, Y))
    have h := expect_le_bkm06_mldsa44_of
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
        βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y)
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0) _
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  -- at every oracle, the restriction and the hedged step
  have hstep : ∀ GB GS GA,
      (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
          (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
        𝔼 Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44,
          (((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y).restrict
              (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
              (fun keys H => D GB GS GA keys (H, Y)) +
          2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
                tol (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeError 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                    hβt (1 / 2) θ keys HG.1 < 1 / 2
                  then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    have h1 := advantage_hedged_le_restrictLow (withExpandA (oraclePrimitives GB GS) GA) hT
      (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
      (A GB GS GA) (hqc GB GS GA) (1 / 2) (x := 89) (by norm_num) (D GB GS GA)
    have h2 : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
            tol (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeError 1 q ka
            (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                hβt (1 / 2) θ keys HG.1 < 1 / 2
              then ENNReal.ofReal Lk else 0)).toReal :=
      advantage_restrictLow_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
        (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
        (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka hp' hβ0 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num)
        hLk Y0
    have key : ∀ {a b c d f : ℝ}, a ≤ b + 2 * f → b ≤ c + 2 * d → a ≤ c + 2 * (d + f) :=
      fun h h' => by linarith
    exact key h1 h2
  refine (expect3_le_of_mix _ _ _ hstep hY).trans ?_
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤ RM := by
    have hM : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log C / 2) +
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
    have hI := expect_idealAnonError_le (p := _root_.MLDSA.mldsa44) (A := A') isApproved_mldsa44
      hβ0 hβt hθ0 (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa44 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 →
          TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    rw [h2]
    exact add_le_add le_rfl (hM.trans_eq (hm _))
  -- the hedged error, with the failure of the keep event at most twice the anonymity error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeError 1 q ka
            (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                hβt (1 / 2) θ keys HG.1 < 1 / 2
              then ENNReal.ofReal Lk else 0)).toReal ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka +
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C) :=
    fun GB GS GA => by
      have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
        (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa44
          (sampleInBallShape_oraclePrims GB) _) GA
      have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA)
        (A' GB GS GA) hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1
        (s := 1 / 2) (by norm_num) (hC GB GS GA)
      have hK : 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
            (if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                (1 / 2) θ keys HG.1 < 1 / 2 then 0 else 1 : ℝ) ≤
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C := by
        refine (Finset.expect_le_expect fun keys _ =>
          expect_ite_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
            hβ0 hβt (by norm_num) hθ0 keys).trans ?_
        rw [← Finset.mul_expect]
        exact mul_le_mul_of_nonneg_left hO zero_le_two
      have h := MaskedSigner.expect_toReal_hedgeError_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc _root_.MLDSA.mldsa44) T hT) 1 q ka
        (fun (keys : Fin n → _root_.MLDSA.Bytes 32)
          (HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps) =>
          oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
            keys HG.1 < 1 / 2) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).Rnd : ℝ) =
            2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * q * ka * (2 ^ 256)⁻¹) =
          (ka ^ 2 + 2 * q * ka) / 2 ^ 256 := by ring
      rw [hc]
      nlinarith [hK]
  have hE : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
                tol (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeError 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                    hβt (1 / 2) θ keys HG.1 < 1 / 2
                  then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka + 2 * RM) + (q + 1) / 2 ^ 240 := by
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      Finset.expect_le_expect fun GA _ => add_le_add (hE1 GB GS GA) le_rfl).trans ?_
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
    have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
    have hcq := mul_le_mul_of_nonneg_left hchk hq0
    rw [mul_one_div] at hcq
    nlinarith [hE3]
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  nlinarith [hE]

end HedgedQuery_mldsa44

section HedgedQuery_mldsa65

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc mldsa65)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa65) T hT).real (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [DecidableEq R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc mldsa65)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps ×
      (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65) →
    (Query k kN kS L → Out k e) → PubHist (BucketVec mldsa65) (M GB GS GA).NIProof 1 →
      Prop)

open Classical in
omit [DecidableEq R] in
/-- **Anonymity at ML-DSA-65 with FIPS 204 hedged signing, against adversaries with `q`
check-oracle queries** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the
start as in CCLM22 Experiment 2, p. 21): `advantage_le_bkm06_mldsa65_hedged` with the check term
`2 (q + 1) / 2^240` in place of `C / 2^240`, for an adversary whose choices read the check oracle
through `q` classical queries at every mask oracle (`hqc`, `CheckQueryBounded`) and that, with
the distinguisher, reads the mask oracle through `q` classical queries per phase (`hq`), with
full key exposure; at every fixed mask oracle the ideal-mask bound is
`advantage_le_bkm06_mldsa65_query_checkParams`. `s̄` is a lower bound on the keep probability of
one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step). Deterministic signing
(`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa65_hedged_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q)
    (hqc : ∀ GB GS GA Y, CheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y) q) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65)
      (_GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l),
      (Fin n → _root_.MLDSA.Bytes 32) →
        GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
                    reps tol (concreteEnc mldsa65) T hT).hedgeError 1 q ka
                      (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240
  have hrow : CheckParams reps tol (1 / 2) 89 := by
    rw [hreps, htol]
    exact checkParams_tol2
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  have hm : ∀ X : ℝ, X / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * (βmin : ℝ≥0∞).toReal)) =
      X / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := fun X => by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  -- at every fixed mask oracle, the ideal-mask bound against `q` check-oracle queries
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65,
      𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
            ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y).advantage
                (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
                (fun keys H => D GB GS GA keys (H, Y)) ≤ B := fun Y => by
    have h := advantage_le_bkm06_mldsa65_query_checkParams
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
        βmin reps tol (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y)
      (fun GB GS GA keys H => D GB GS GA keys (H, Y)) (fun GB GS GA => hqc GB GS GA Y) hβ0 hβ1
      hβt hrow hθ0 hθ1 Rv hz hC
    rw [h2, hm] at h
    exact h
  -- at every oracle, the hedged step
  refine expect3_le_of_mix _ _ (fun GB GS GA
      (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65) =>
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA)
          (Qs GB GS GA) (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y)))
    (fun GB GS GA => ?_) hY
  exact advantage_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
    (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
    (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka (sbar GB GS GA) (hkeep GB GS GA)

open Classical in
omit [DecidableEq R] in
/-- **Anonymity at ML-DSA-65 with FIPS 204 hedged signing against adversaries with `q`
check-oracle queries, the keep bound discharged** (BKM06 Definition 4, ePrint 2005/304, p. 6,
`Q = 1`): `advantage_le_bkm06_mldsa65_hedged_keep` with the check term `2 (q + 1) / 2^240` in
place of `C / 2^240`, for an adversary whose choices read the check oracle through `q` classical
queries at every mask oracle (`hqc`) and that, with the distinguisher, reads the mask oracle
through `q` classical queries per phase (`hq`), with full key exposure. The proof compares the
hedged signer with the hedged signer that also refuses the rings of defect above `1/2`
(`advantage_hedged_le_restrictLow`, the check term); against it every admitted ring has defect at
most `1/2`, so the keep bound `s̄ = β_min θ / 64` holds when the anonymity error is below `1/2`,
with no check term in the hedged error (`advantage_restrictLow_le_hedged`), and the ideal-mask
bound has none either (`advantage_restrictLow_le`, `expect_le_bkm06_mldsa65_of`). For every
number `k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 (q + 1) / 2^240 + 2 · ((k² + 2 q k) / 2^256 + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity +
McDiarmid)))`. Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa65_hedged_keep_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q)
    (hqc : ∀ GB GS GA Y, CheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y) q) (ka : ℕ) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240 +
        2 * ((ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ / 64) ^ ka +
          2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa65.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa65
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  set Y0 : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65 :=
    fun _ => Classical.arbitrary _
  set A' := fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
    βmin reps tol (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y0
  set Lk : ℝ := (βmin : ℝ≥0∞).toReal * θ / 64
  have hLk0 : 0 ≤ Lk := by positivity
  have hLk1 : Lk ≤ 1 := by
    have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 := mul_le_one₀ hb1 hθ0.le hθ1.le
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1
    linarith
  have hLk : Lk ≤ keepLevel mldsa65 βmin (1 / 2) θ := by
    have hK := one_div_sixteen_le_standinScale_mul_card_mldsa65
    unfold keepLevel
    rw [ENNReal.toReal_mul]
    have hx := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ _
    nlinarith [hx]
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  have hm : ∀ X : ℝ, X / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * (βmin : ℝ≥0∞).toReal)) =
      X / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := fun X => by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  set RM : ℝ := 2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
    √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))
  set Bi : ℝ := 2 * RM +
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (M GB GS GA).wiError δ C
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65,
      𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
            (((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y).restrict
                (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
                (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
                (fun keys H => D GB GS GA keys (H, Y)) ≤ Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa65
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa65 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa65 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) (hC GB GS GA) (fun keys H => D GB GS GA keys (H, Y))
    have h := expect_le_bkm06_mldsa65_of
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
        βmin reps tol (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y)
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0) _
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  -- at every oracle, the restriction and the hedged step
  have hstep : ∀ GB GS GA,
      (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
          (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
        𝔼 Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65,
          (((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y).restrict
              (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
              (fun keys H => D GB GS GA keys (H, Y)) +
          2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
                tol (concreteEnc mldsa65) T hT).hedgeError 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                    hβt (1 / 2) θ keys HG.1 < 1 / 2
                  then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    have h1 := advantage_hedged_le_restrictLow (withExpandA (oraclePrimitives GB GS) GA) hT
      (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
      (A GB GS GA) (hqc GB GS GA) (1 / 2) (x := 89) (by norm_num) (D GB GS GA)
    have h2 : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
            tol (concreteEnc mldsa65) T hT).hedgeError 1 q ka
            (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                hβt (1 / 2) θ keys HG.1 < 1 / 2
              then ENNReal.ofReal Lk else 0)).toReal :=
      advantage_restrictLow_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
        (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
        (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka hp' hβ0 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num)
        hLk Y0
    have key : ∀ {a b c d f : ℝ}, a ≤ b + 2 * f → b ≤ c + 2 * d → a ≤ c + 2 * (d + f) :=
      fun h h' => by linarith
    exact key h1 h2
  refine (expect3_le_of_mix _ _ _ hstep hY).trans ?_
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤ RM := by
    have hM : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log C / 2) +
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
    have hI := expect_idealAnonError_le (p := mldsa65) (A := A') isApproved_mldsa65
      hβ0 hβt hθ0 (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa65 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 →
          TqMatrix mldsa65.k mldsa65.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    rw [h2]
    exact add_le_add le_rfl (hM.trans_eq (hm _))
  -- the hedged error, with the failure of the keep event at most twice the anonymity error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc mldsa65) T hT).hedgeError 1 q ka
            (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                hβt (1 / 2) θ keys HG.1 < 1 / 2
              then ENNReal.ofReal Lk else 0)).toReal ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka +
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C) :=
    fun GB GS GA => by
      have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
        (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa65
          (sampleInBallShape_oraclePrims GB) _) GA
      have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA)
        (A' GB GS GA) hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1
        (s := 1 / 2) (by norm_num) (hC GB GS GA)
      have hK : 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
            (if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                (1 / 2) θ keys HG.1 < 1 / 2 then 0 else 1 : ℝ) ≤
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C := by
        refine (Finset.expect_le_expect fun keys _ =>
          expect_ite_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
            hβ0 hβt (by norm_num) hθ0 keys).trans ?_
        rw [← Finset.mul_expect]
        exact mul_le_mul_of_nonneg_left hO zero_le_two
      have h := MaskedSigner.expect_toReal_hedgeError_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc mldsa65) T hT) 1 q ka
        (fun (keys : Fin n → _root_.MLDSA.Bytes 32)
          (HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps) =>
          oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
            keys HG.1 < 1 / 2) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc mldsa65) T hT).Rnd : ℝ) =
            2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * q * ka * (2 ^ 256)⁻¹) =
          (ka ^ 2 + 2 * q * ka) / 2 ^ 256 := by ring
      rw [hc]
      nlinarith [hK]
  have hE : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
                tol (concreteEnc mldsa65) T hT).hedgeError 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                    hβt (1 / 2) θ keys HG.1 < 1 / 2
                  then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka + 2 * RM) + (q + 1) / 2 ^ 240 := by
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      Finset.expect_le_expect fun GA _ => add_le_add (hE1 GB GS GA) le_rfl).trans ?_
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
    have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
    have hcq := mul_le_mul_of_nonneg_left hchk hq0
    rw [mul_one_div] at hcq
    nlinarith [hE3]
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  nlinarith [hE]

end HedgedQuery_mldsa65

section HedgedQuery_mldsa87

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc mldsa87)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa87) T hT).real (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [DecidableEq R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc mldsa87)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps ×
      (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87) →
    (Query k kN kS L → Out k e) → PubHist (BucketVec mldsa87) (M GB GS GA).NIProof 1 →
      Prop)

open Classical in
omit [DecidableEq R] in
/-- **Anonymity at ML-DSA-87 with FIPS 204 hedged signing, against adversaries with `q`
check-oracle queries** (BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the
start as in CCLM22 Experiment 2, p. 21): `advantage_le_bkm06_mldsa87_hedged` with the check term
`2 (q + 1) / 2^240` in place of `C / 2^240`, for an adversary whose choices read the check oracle
through `q` classical queries at every mask oracle (`hqc`, `CheckQueryBounded`) and that, with
the distinguisher, reads the mask oracle through `q` classical queries per phase (`hq`), with
full key exposure; at every fixed mask oracle the ideal-mask bound is
`advantage_le_bkm06_mldsa87_query_checkParams`. `s̄` is a lower bound on the keep probability of
one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step). Deterministic signing
(`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa87_hedged_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q)
    (hqc : ∀ GB GS GA Y, CheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y) q) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87)
      (_GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l),
      (Fin n → _root_.MLDSA.Bytes 32) →
        GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
                    reps tol (concreteEnc mldsa87) T hT).hedgeError 1 q ka
                      (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240
  have hrow : CheckParams reps tol (1 / 2) 89 := by
    rw [hreps, htol]
    exact checkParams_tol2
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  have hm : ∀ X : ℝ, X / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * (βmin : ℝ≥0∞).toReal)) =
      X / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := fun X => by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  -- at every fixed mask oracle, the ideal-mask bound against `q` check-oracle queries
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87,
      𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
            ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y).advantage
                (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
                (fun keys H => D GB GS GA keys (H, Y)) ≤ B := fun Y => by
    have h := advantage_le_bkm06_mldsa87_query_checkParams
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
        βmin reps tol (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y)
      (fun GB GS GA keys H => D GB GS GA keys (H, Y)) (fun GB GS GA => hqc GB GS GA Y) hβ0 hβ1
      hβt hrow hθ0 hθ1 Rv hz hC
    rw [h2, hm] at h
    exact h
  -- at every oracle, the hedged step
  refine expect3_le_of_mix _ _ (fun GB GS GA
      (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87) =>
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA)
          (Qs GB GS GA) (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y)))
    (fun GB GS GA => ?_) hY
  exact advantage_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
    (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
    (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka (sbar GB GS GA) (hkeep GB GS GA)

open Classical in
omit [DecidableEq R] in
/-- **Anonymity at ML-DSA-87 with FIPS 204 hedged signing against adversaries with `q`
check-oracle queries, the keep bound discharged** (BKM06 Definition 4, ePrint 2005/304, p. 6,
`Q = 1`): `advantage_le_bkm06_mldsa87_hedged_keep` with the check term `2 (q + 1) / 2^240` in
place of `C / 2^240`, for an adversary whose choices read the check oracle through `q` classical
queries at every mask oracle (`hqc`) and that, with the distinguisher, reads the mask oracle
through `q` classical queries per phase (`hq`), with full key exposure. The proof compares the
hedged signer with the hedged signer that also refuses the rings of defect above `1/2`
(`advantage_hedged_le_restrictLow`, the check term); against it every admitted ring has defect at
most `1/2`, so the keep bound `s̄ = β_min θ / 64` holds when the anonymity error is below `1/2`,
with no check term in the hedged error (`advantage_restrictLow_le_hedged`), and the ideal-mask
bound has none either (`advantage_restrictLow_le`, `expect_le_bkm06_mldsa87_of`). For every
number `k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 (q + 1) / 2^240 + 2 · ((k² + 2 q k) / 2^256 + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity +
McDiarmid)))`. Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa87_hedged_keep_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q)
    (hqc : ∀ GB GS GA Y, CheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y) q) (ka : ℕ) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240 +
        2 * ((ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ / 64) ^ ka +
          2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa87.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa87
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  set Y0 : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87 :=
    fun _ => Classical.arbitrary _
  set A' := fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
    βmin reps tol (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y0
  set Lk : ℝ := (βmin : ℝ≥0∞).toReal * θ / 64
  have hLk0 : 0 ≤ Lk := by positivity
  have hLk1 : Lk ≤ 1 := by
    have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 := mul_le_one₀ hb1 hθ0.le hθ1.le
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1
    linarith
  have hLk : Lk ≤ keepLevel mldsa87 βmin (1 / 2) θ := by
    have hK := one_div_sixteen_le_standinScale_mul_card_mldsa87
    unfold keepLevel
    rw [ENNReal.toReal_mul]
    have hx := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ _
    nlinarith [hx]
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  have hm : ∀ X : ℝ, X / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * (βmin : ℝ≥0∞).toReal)) =
      X / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := fun X => by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  set RM : ℝ := 2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
    √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))
  set Bi : ℝ := 2 * RM +
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (M GB GS GA).wiError δ C
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87,
      𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
            (((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y).restrict
                (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
                (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
                (fun keys H => D GB GS GA keys (H, Y)) ≤ Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa87
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa87 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa87 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) (hC GB GS GA) (fun keys H => D GB GS GA keys (H, Y))
    have h := expect_le_bkm06_mldsa87_of
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
        βmin reps tol (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y)
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0) _
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  -- at every oracle, the restriction and the hedged step
  have hstep : ∀ GB GS GA,
      (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
          (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
        𝔼 Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87,
          (((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y).restrict
              (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
              (fun keys H => D GB GS GA keys (H, Y)) +
          2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
                tol (concreteEnc mldsa87) T hT).hedgeError 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                    hβt (1 / 2) θ keys HG.1 < 1 / 2
                  then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    have h1 := advantage_hedged_le_restrictLow (withExpandA (oraclePrimitives GB GS) GA) hT
      (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
      (A GB GS GA) (hqc GB GS GA) (1 / 2) (x := 89) (by norm_num) (D GB GS GA)
    have h2 : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
            tol (concreteEnc mldsa87) T hT).hedgeError 1 q ka
            (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                hβt (1 / 2) θ keys HG.1 < 1 / 2
              then ENNReal.ofReal Lk else 0)).toReal :=
      advantage_restrictLow_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
        (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
        (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka hp' hβ0 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num)
        hLk Y0
    have key : ∀ {a b c d f : ℝ}, a ≤ b + 2 * f → b ≤ c + 2 * d → a ≤ c + 2 * (d + f) :=
      fun h h' => by linarith
    exact key h1 h2
  refine (expect3_le_of_mix _ _ _ hstep hY).trans ?_
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤ RM := by
    have hM : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log C / 2) +
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
    have hI := expect_idealAnonError_le (p := mldsa87) (A := A') isApproved_mldsa87
      hβ0 hβt hθ0 (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa87 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 →
          TqMatrix mldsa87.k mldsa87.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    rw [h2]
    exact add_le_add le_rfl (hM.trans_eq (hm _))
  -- the hedged error, with the failure of the keep event at most twice the anonymity error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc mldsa87) T hT).hedgeError 1 q ka
            (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                hβt (1 / 2) θ keys HG.1 < 1 / 2
              then ENNReal.ofReal Lk else 0)).toReal ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka +
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C) :=
    fun GB GS GA => by
      have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
        (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa87
          (sampleInBallShape_oraclePrims GB) _) GA
      have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA)
        (A' GB GS GA) hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1
        (s := 1 / 2) (by norm_num) (hC GB GS GA)
      have hK : 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
            (if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                (1 / 2) θ keys HG.1 < 1 / 2 then 0 else 1 : ℝ) ≤
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C := by
        refine (Finset.expect_le_expect fun keys _ =>
          expect_ite_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
            hβ0 hβt (by norm_num) hθ0 keys).trans ?_
        rw [← Finset.mul_expect]
        exact mul_le_mul_of_nonneg_left hO zero_le_two
      have h := MaskedSigner.expect_toReal_hedgeError_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc mldsa87) T hT) 1 q ka
        (fun (keys : Fin n → _root_.MLDSA.Bytes 32)
          (HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps) =>
          oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
            keys HG.1 < 1 / 2) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc mldsa87) T hT).Rnd : ℝ) =
            2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * q * ka * (2 ^ 256)⁻¹) =
          (ka ^ 2 + 2 * q * ka) / 2 ^ 256 := by ring
      rw [hc]
      nlinarith [hK]
  have hE : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps
                tol (concreteEnc mldsa87) T hT).hedgeError 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0
                    hβt (1 / 2) θ keys HG.1 < 1 / 2
                  then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka + 2 * RM) + (q + 1) / 2 ^ 240 := by
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      Finset.expect_le_expect fun GA _ => add_le_add (hE1 GB GS GA) le_rfl).trans ?_
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
    have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
    have hcq := mul_le_mul_of_nonneg_left hchk hq0
    rw [mul_one_div] at hcq
    nlinarith [hE3]
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  nlinarith [hE]

end HedgedQuery_mldsa87

end MLDSAW1

end GordieHowe.Ring
