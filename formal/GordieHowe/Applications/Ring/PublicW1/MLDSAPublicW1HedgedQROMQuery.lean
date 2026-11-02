-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1HedgedQROM
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1HedgedQuery

@[expose] public section

/-!
# The hedged ML-DSA ring signer publishing `w₁` in the quantum random-oracle model, against `q` check-oracle queries

The headlines of `MLDSAPublicW1HedgedQROM.lean` with the check term of `MLDSAPublicW1Query.lean`,
at one adversary class: in each round the adversary's challenge is the measured output of a
quantum algorithm with `q` superposition queries to the mask oracle (`MaskedSigner.QAdversary`),
and that quantum algorithm is the output of a classical algorithm with `q` queries to the check
oracle `G` (`QCheckQueryBounded`; the quantum algorithm reads `G` only through those queries); the
distinguisher makes `q` superposition queries to the mask oracle. The check term `C / 2^240`
becomes `2 (q + 1) / 2^240`.

- `MaskedSigner.QAdversary.restrict`, `MaskedSigner.QAdversary.advantage_le_restrict_one`: the
  quantum game against the hedged signer and against the hedged signer that also refuses the
  rings outside `Ok` are identical until the measured challenge is admitted and refused by `Ok`.
- `QCheckQueryBounded`, `expect_restrictBadQ_le`: the measured challenge's ring has defect above
  `s` and passes the check with probability at most `(q + 1) · checkError`
  (`ROM.expect_weighted_label_le`, the ring drawn from the measured law).
- `advantage_le_bkm06_mldsa{44,65,87}_hedged_qrom_query`:
  `advantage_le_bkm06_mldsa{44,65,87}_hedged_qrom` with the check term `2 (q + 1) / 2^240`.
- `advantage_le_bkm06_mldsa{44,65,87}_hedged_keep_qrom_query`:
  `advantage_le_bkm06_mldsa{44,65,87}_hedged_keep_qrom` with the check term `2 (q + 1) / 2^240`;
  the hedged error has no check term.

Deterministic signing (`rnd = 0`) is not covered.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM PMF
open GordieHowe.Quantum (QueryAlg)
open scoped ENNReal BigOperators

section RestrictQ

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {S : PubSigner N RMsg}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {M : SPBCS Mg P S.Stmt k kN kS L e} {n Q : ℕ}
  {G : Type} [Fintype G] [AddGroup G]

namespace MaskedSigner

/-- **The quantum adversary against the hedged signer that also refuses the rings outside
`Ok`** (`MaskedSigner.restrict`): the same set of challenges and the same quantum algorithms.

Running time: that of the adversary. This running time is argued here, not proved in Lean. -/
def QAdversary.restrict {W : MaskedSigner S} {q : ℕ} (A : W.QAdversary M G n Q q)
    (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) : (W.restrict Ok).QAdversary M G n Q q where
  choices := A.choices
  choose := A.choose
  choose_mem := A.choose_mem
  choose_valid := A.choose_valid

omit [DecidableEq RMsg] [∀ j i, Nonempty ((P j).Challenge i)] in
/-- A uniform average of values at most one is at most one. -/
theorem sum_uniform_mul_le_one {α : Type*} [Fintype α] [Nonempty α] {f : α → ℝ≥0∞}
    (hf : ∀ a, f a ≤ 1) : ∑ a, PMF.uniformOfFintype α a * f a ≤ 1 :=
  (Finset.sum_le_sum fun a _ => mul_le_of_le_one_right' (hf a)).trans_eq (PMF.sum_coe _)

open Classical in
/-- **Anonymity against the restricted hedged signer from anonymity against classical adversaries
against the restricted ideal-mask signer** (`QAdversary.exists_advantage_le` for
`W.restrict Ok`): for a bound `ρ` on the rejection probability of a fresh-mask attempt of every
valid challenge that `S` admits and `Ok` accepts, there is a table of measured challenges at
every mask oracle such that the advantage of `A.restrict Ok` is at most the average over the mask
oracle of the advantage of the classical adversary at the table against the restricted ideal-mask
signer, with the distinguisher that guesses the likelier experiment, plus twice the hedged
error. -/
theorem QAdversary.exists_advantage_restrict_le {W : MaskedSigner S} {q : ℕ}
    (A : W.QAdversary M G n 1 q) (D : W.QDist M G n 1 q) (enc : W.Mask → G)
    (E : (j : ι) → (M.comp j).Encoder) {V : S.Orc → S.Stmt → FullTr P τ → Bool}
    (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type} [Fintype R] [Nonempty R]
    (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)
    (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) (ka : ℕ)
    (ρ : (Fin n → S.KeyCoins) → S.Orc → ℝ≥0∞) (hρ1 : ∀ keys H, ρ keys H ≤ 1)
    (hρ : ∀ keys H, ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg →
      Ok H c.ring c.msg → ∀ b, W.meanAttempt H keys c b none ≤ ρ keys H) :
    ∃ T : W.MaskOrc → A.Table, (A.restrict Ok).advantage D enc E Qs honest ≤
      𝔼 Y : W.MaskOrc, ((A.atTable (T Y)).restrict Ok).advantage E Qs honest
          (((A.atTable (T Y)).restrict Ok).likelierDist E Qs honest) +
        2 * 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, (W.hedgeErrorQ 1 q ka (ρ keys H)).toReal := by
  obtain ⟨T, hT⟩ := QAdversary.exists_advantage_le (W := W.restrict Ok) (A.restrict Ok) D enc E Qs
    honest ka ρ hρ1 fun keys H c hc hv ha b => hρ keys H c hc hv ha.1 ha.2 b
  exact ⟨T, hT⟩

omit [DecidableEq RMsg] [∀ j i, Nonempty ((P j).Challenge i)] in
open Classical in
/-- **The quantum game against `W` and against `W.restrict Ok` are identical until bad** (one
challenge): for each experiment `b`, the excess of one game over the other is at most the
probability, over the users' coins, the oracle of the base scheme, the mask oracle and the oracle
of the compiled argument, that the measured challenge is admitted by `S` and refused by `Ok`
(`etv_seqRun_le`; the two rounds differ only in `PubSigner.proved`). -/
theorem QAdversary.etv_game_restrict_le {W : MaskedSigner S} {q : ℕ} (A : W.QAdversary M G n 1 q)
    (D : W.QDist M G n 1 q) (enc : W.Mask → G) (E : (j : ι) → (M.comp j).Encoder)
    {V : S.Orc → S.Stmt → FullTr P τ → Bool} (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type}
    [Fintype R] [Nonempty R] (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)
    (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) (b : Bool) :
    PMF.etv (A.game D enc E Qs honest b) ((A.restrict Ok).game D enc E Qs honest b) ≤
      ∑ keys, PMF.uniformOfFintype (Fin n → S.KeyCoins) keys *
        ∑ H, PMF.uniformOfFintype S.Orc H * ∑ Y, PMF.uniformOfFintype W.MaskOrc Y *
          ∑ h, PMF.uniformOfFintype (Query k kN kS L → Out k e) h *
            ((A.choose 0 keys H h Fin.elim0).outLaw (enc ∘ Y)).toOuterMeasure
              {c | S.Admit H c.ring c.msg ∧ ¬ Ok H c.ring c.msg} := by
  unfold QAdversary.game
  refine (PMF.etv_bind_left_le _ _ _).trans ?_
  rw [tsum_fintype]
  refine Finset.sum_le_sum fun keys _ => mul_le_mul_right ?_ _
  refine (PMF.etv_bind_left_le _ _ _).trans ?_
  rw [tsum_fintype]
  refine Finset.sum_le_sum fun H _ => mul_le_mul_right ?_ _
  refine (PMF.etv_bind_left_le _ _ _).trans ?_
  rw [tsum_fintype]
  refine Finset.sum_le_sum fun Y _ => mul_le_mul_right ?_ _
  unfold acceptLaw
  refine (PMF.etv_bind_right_le _ _ _).trans ?_
  refine (etv_seqRun_le _ _ 1 le_rfl).trans ?_
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, seqRun]
  rw [PMF.tsum_map_mul, tsum_fintype]
  refine Finset.sum_le_sum fun h _ => mul_le_mul_right ?_ _
  simp only [QAdversary.rounds, drawSteps, measChoice]
  refine (PMF.etv_bind_le_toOuterMeasure_ne _ _ _).trans (MeasureTheory.measure_mono ?_)
  intro c hne
  by_contra hc
  apply hne
  have hpr : ∀ x, S.proved H b c x = (S.restrict Ok).proved H b c x := fun x => by
    unfold PubSigner.proved
    by_cases ha : S.Admit H c.ring c.msg
    · have hok : Ok H c.ring c.msg := by
        by_contra hn
        exact hc ⟨ha, hn⟩
      rw [if_pos ha, if_pos (show (S.restrict Ok).Admit H c.ring c.msg from ⟨ha, hok⟩)]
      rfl
    · rw [if_neg ha, if_neg (show ¬ (S.restrict Ok).Admit H c.ring c.msg from fun h => ha h.1)]
      rfl
  congr 1
  funext x
  congr 1
  exact hpr x

omit [DecidableEq RMsg] [∀ j i, Nonempty ((P j).Challenge i)] in
open Classical in
/-- **The advantage against the hedged signer from the advantage against the hedged signer that
also refuses the rings outside `Ok`** in the quantum random-oracle model, one challenge: at most
the advantage against the restricted signer plus twice the probability that the measured
challenge is admitted by `S` and refused by `Ok` (`QAdversary.etv_game_restrict_le`). -/
theorem QAdversary.advantage_le_restrict_one {W : MaskedSigner S} {q : ℕ}
    (A : W.QAdversary M G n 1 q) (D : W.QDist M G n 1 q) (enc : W.Mask → G)
    (E : (j : ι) → (M.comp j).Encoder) {V : S.Orc → S.Stmt → FullTr P τ → Bool}
    (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type} [Fintype R] [Nonempty R]
    (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)
    (Ok : S.Orc → RingOf S.PK N → RMsg → Prop) :
    A.advantage D enc E Qs honest ≤ (A.restrict Ok).advantage D enc E Qs honest +
      2 * 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, 𝔼 Y : W.MaskOrc,
        𝔼 h : Query k kN kS L → Out k e,
          (((A.choose 0 keys H h Fin.elim0).outLaw (enc ∘ Y)).toOuterMeasure
            {c | S.Admit H c.ring c.msg ∧ ¬ Ok H c.ring c.msg}).toReal := by
  set bad : ℝ≥0∞ := ∑ keys, PMF.uniformOfFintype (Fin n → S.KeyCoins) keys *
    ∑ H, PMF.uniformOfFintype S.Orc H * ∑ Y, PMF.uniformOfFintype W.MaskOrc Y *
      ∑ h, PMF.uniformOfFintype (Query k kN kS L → Out k e) h *
        ((A.choose 0 keys H h Fin.elim0).outLaw (enc ∘ Y)).toOuterMeasure
          {c | S.Admit H c.ring c.msg ∧ ¬ Ok H c.ring c.msg}
  have hb1 : ∀ keys H Y h, ((A.choose 0 keys H h Fin.elim0).outLaw (enc ∘ Y)).toOuterMeasure
      {c | S.Admit H c.ring c.msg ∧ ¬ Ok H c.ring c.msg} ≤ 1 := fun _keys _H _Y _h =>
    PMF.toOuterMeasure_apply_le_one _ _
  have hbad1 : bad ≤ 1 := sum_uniform_mul_le_one fun keys => sum_uniform_mul_le_one fun H =>
    sum_uniform_mul_le_one fun Y => sum_uniform_mul_le_one fun h => hb1 keys H Y h
  have hbadR : bad.toReal = 𝔼 keys : Fin n → S.KeyCoins, 𝔼 H : S.Orc, 𝔼 Y : W.MaskOrc,
      𝔼 h : Query k kN kS L → Out k e,
        (((A.choose 0 keys H h Fin.elim0).outLaw (enc ∘ Y)).toOuterMeasure
          {c | S.Admit H c.ring c.msg ∧ ¬ Ok H c.ring c.msg}).toReal := by
    have hne : ∀ {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ≥0∞), (∀ a, f a ≤ 1) →
        ∀ a, f a ≠ ⊤ := fun f hf a => ne_top_of_le_ne_top ENNReal.one_ne_top (hf a)
    rw [toReal_sum_uniform_mul (hne _ fun keys => sum_uniform_mul_le_one fun H =>
      sum_uniform_mul_le_one fun Y => sum_uniform_mul_le_one fun h => hb1 keys H Y h)]
    refine Finset.expect_congr rfl fun keys _ => ?_
    rw [toReal_sum_uniform_mul (hne _ fun H => sum_uniform_mul_le_one fun Y =>
      sum_uniform_mul_le_one fun h => hb1 keys H Y h)]
    refine Finset.expect_congr rfl fun H _ => ?_
    rw [toReal_sum_uniform_mul (hne _ fun Y => sum_uniform_mul_le_one fun h => hb1 keys H Y h)]
    refine Finset.expect_congr rfl fun Y _ => ?_
    rw [toReal_sum_uniform_mul (hne _ fun h => hb1 keys H Y h)]
  rw [← hbadR]
  have hc : ∀ b, EClose (A.game D enc E Qs honest b true)
      ((A.restrict Ok).game D enc E Qs honest b true) bad := fun b =>
    eclose_apply_of_etv_le (A.etv_game_restrict_le D enc E Qs honest Ok b)
  have hbt : bad ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hbad1
  have hreal : ∀ b, |(A.game D enc E Qs honest b true).toReal -
      ((A.restrict Ok).game D enc E Qs honest b true).toReal| ≤ bad.toReal := fun b => by
    have h1 := (hc b).1
    have h2 := (hc b).2
    have hP : A.game D enc E Qs honest b true ≠ ⊤ := PMF.apply_ne_top _ _
    have hI : (A.restrict Ok).game D enc E Qs honest b true ≠ ⊤ := PMF.apply_ne_top _ _
    have r1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI, hbt⟩) h1
    have r2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hP, hbt⟩) h2
    rw [ENNReal.toReal_add hI hbt] at r1
    rw [ENNReal.toReal_add hP hbt] at r2
    rw [abs_le]
    constructor <;> linarith
  unfold QAdversary.advantage
  rw [GordieHowe.gameAdvantage_true, GordieHowe.gameAdvantage_true]
  set a0 := (A.game D enc E Qs honest false true).toReal
  set a1 := (A.game D enc E Qs honest true true).toReal
  set b0 := ((A.restrict Ok).game D enc E Qs honest false true).toReal
  set b1 := ((A.restrict Ok).game D enc E Qs honest true true).toReal
  have h0 : |a0 - b0| ≤ bad.toReal := hreal false
  have h1 : |a1 - b1| ≤ bad.toReal := hreal true
  have e1 := abs_sub_le a0 b0 a1
  have e2 := abs_sub_le b0 b1 a1
  rw [abs_sub_comm b1 a1] at e2
  linarith

end MaskedSigner

end RestrictQ

namespace MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA Finset

section Signer

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High]

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e} {n Q : ℕ}
  {G : Type} [Fintype G] [AddGroup G]

/-- **A quantum adversary whose choices read the check oracle through `qc` classical queries**:
every round's quantum algorithm, at every value of the users' coins, the scheme's oracles
`(H_µ, H)`, the proof system's oracle and the history, is the output of a deterministic
classical algorithm making `qc` queries to the check oracle `G` (`ROM.Alg`, CY24 p. 20); its
superposition queries go to the mask oracle only. The adversary keeps full key exposure and sees
the other oracles whole. -/
structure QCheckQueryBounded (W : MaskedSigner (pubSigner prims (Msg := Msg) N βmin reps tol enc))
    {q : ℕ} (A : W.QAdversary M G n Q q) (qc : ℕ) : Prop where
  /-- Every round's quantum algorithm is computed from `qc` queries to `G`. -/
  choose : ∀ j keys H h hist, ∃ alg : ROM.Alg (RingOf (PubKey p prims) N × Fin N × Fin reps)
    (CommitHashBytes p) (QueryAlg (W.Rnd × W.Pt) G q
      ((pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n)) qc,
    ∀ Gc, A.choose j keys (H, Gc) h hist = alg.output Gc

omit [∀ j i, Nonempty ((P j).Challenge i)] in
open Classical in
/-- **The measured challenge's ring is admitted with defect above `s`, for a quantum adversary
with `q` check-oracle queries**: at the users' coins `keys`, the probability over the game's
oracles, the mask oracle and the proof system's oracle that the measured challenge is admitted
and its ring has defect above `s` is at most `(q + 1) · checkError reps tol s x` for every
`x ≥ 1` (`ROM.expect_weighted_label_le` with the law of the measured challenge's ring; the
admitted ring passes the check). -/
theorem expect_restrictBadQ_le (W : MaskedSigner (pubSigner prims (Msg := Msg) N βmin reps tol enc))
    {q : ℕ} (A : W.QAdversary M G n 1 q) (hqc : QCheckQueryBounded prims W A q)
    (encY : W.Mask → G) (s : ℝ) {x : ℝ} (hx : 1 ≤ x) (keys : Fin n → _root_.MLDSA.Bytes 32) :
    𝔼 H : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc, 𝔼 Y : W.MaskOrc,
      𝔼 h : Query k kN kS L → Out k e,
        (((A.choose 0 keys H h Fin.elim0).outLaw (encY ∘ Y)).toOuterMeasure
          {c | (pubSigner prims (Msg := Msg) N βmin reps tol enc).Admit H c.ring c.msg ∧
            ¬ lowOk prims βmin s H c.ring c.msg}).toReal ≤
      (q + 1) * checkError reps tol s x := by
  have hε : ∀ l : RingOf (PubKey p prims) N, 𝔼 G : CheckOrc p prims N reps,
      (if s < ringDefect prims βmin l.1 ∧ RingCheck prims βmin tol G l then 1 else 0 : ℝ) ≤
        checkError reps tol s x := fun l => by
    by_cases hl : s < ringDefect prims βmin l.1
    · refine (Finset.expect_le_expect fun G _ => ?_).trans
        (expect_ringCheck_le prims βmin tol l hl.le hx)
      by_cases h : RingCheck prims βmin tol G l <;> simp [hl, h]
    · simp only [hl, false_and, if_false, Finset.expect_const_zero]
      exact checkError_nonneg reps tol s (zero_le_one.trans hx)
  have hε0 : 0 ≤ checkError reps tol s x := checkError_nonneg reps tol s (zero_le_one.trans hx)
  refine (Finset.expect_prod_eq_expect_expect (α := SchOrc p Msg) (β := CheckOrc p prims N reps)
    (hαβ := (pubSigner prims (Msg := Msg) N βmin reps tol enc).instFintypeOrc) _).trans_le ?_
  refine (Finset.expect_le_expect fun Hs _ => ?_).trans_eq (Fintype.expect_const _)
  rw [Finset.expect_comm]
  refine (Finset.expect_le_expect fun Y _ => ?_).trans_eq (Fintype.expect_const _)
  rw [Finset.expect_comm]
  refine (Finset.expect_le_expect fun h _ => ?_).trans_eq (Fintype.expect_const _)
  obtain ⟨alg, halg⟩ := hqc.choose 0 keys Hs h Fin.elim0
  -- the classical algorithm followed by the law of the measured challenge's ring
  let alg' : ROM.Alg (RingOf (PubKey p prims) N × Fin N × Fin reps) (CommitHashBytes p)
      (PMF (RingOf (PubKey p prims) N)) q :=
    ⟨alg.next, fun ans => ((alg.out ans).outLaw (encY ∘ Y)).map RingChoice.ring⟩
  have hq : ∀ Gc i, alg'.queries Gc i = alg.queries Gc i := fun Gc i => by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [ROM.Alg.queries_succ, ROM.Alg.queryAt, ih]
      rfl
  have halg' : ∀ Gc, alg'.output Gc = ((alg.output Gc).outLaw (encY ∘ Y)).map RingChoice.ring :=
    fun Gc => by
      unfold ROM.Alg.output
      rw [hq]
      rfl
  have hw1 : ∀ μ : PMF (RingOf (PubKey p prims) N), ∑ l, (μ l).toReal ≤ 1 := fun μ =>
    (PMF.sum_toReal _).le
  refine (Finset.expect_le_expect fun Gc _ => ?_).trans
    (ROM.expect_weighted_label_le (fun x : RingOf (PubKey p prims) N × Fin N × Fin reps => x.1)
      alg' (fun l (G : CheckOrc p prims N reps) =>
        s < ringDefect prims βmin l.1 ∧ RingCheck prims βmin tol G l)
      (localPred_highCheck prims s) (fun l => by convert hε l using 3) hε0 (fun μ l => (μ l).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) hw1)
  rw [halg' Gc]
  rw [halg Gc]
  set μ := (alg.output Gc).outLaw (encY ∘ Y)
  have hsub : {c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n |
      (pubSigner prims (Msg := Msg) N βmin reps tol enc).Admit (Hs, Gc) c.ring c.msg ∧
        ¬ lowOk prims βmin s (Hs, Gc) c.ring c.msg} ⊆
      RingChoice.ring ⁻¹' {l | s < ringDefect prims βmin l.1 ∧ RingCheck prims βmin tol Gc l} :=
    fun c hc => ⟨lt_of_not_ge hc.2, hc.1.2⟩
  have hle := (MeasureTheory.measure_mono (μ := μ.toOuterMeasure) hsub).trans_eq
    (PMF.toOuterMeasure_map_apply RingChoice.ring μ _).symm
  refine (ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _)) hle).trans_eq ?_
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum fun l _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (Set.indicator_le (fun l _ => PMF.coe_le_one _ l) l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs <;> first
    | exact (mul_one _).symm
    | rw [mul_zero, ENNReal.toReal_zero]

end Signer


open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity IOP GordieHowe.SPBCS GordieHowe.QROM
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

section HedgedQROMQuery_mldsa44

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ} {G : Type} [Fintype G] [AddGroup G] {q : ℕ}
  {M : ∀ (GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44)
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
/-- **Anonymity at ML-DSA-44 with FIPS 204 hedged signing in the quantum random-oracle model,
against adversaries with `q` check-oracle queries** (BKM06 Definition 4, ePrint 2005/304, p. 6,
`Q = 1`, keys given at the start as in CCLM22 Experiment 2, p. 21):
`advantage_le_bkm06_mldsa44_hedged_qrom` with the check term `2 (q + 1) / 2^240` in place of
`C / 2^240`, for an adversary whose round algorithm is computed from `q` classical queries to the
check oracle (`hqc`, `QCheckQueryBounded`) and makes `q` superposition queries to the mask oracle,
with a distinguisher making `q` superposition queries to the mask oracle, with full key exposure.
The proof compares the hedged signer with the hedged signer that also refuses the rings of defect
above `1/2` (`QAdversary.advantage_le_restrict_one`, `expect_restrictBadQ_le`, the check term);
against it the reduction to classical adversaries (`QAdversary.exists_advantage_le`) and the
ideal-mask bound (`advantage_restrictLow_le`, `expect_le_bkm06_mldsa44_of`) have no check term.
`s̄` is a lower bound on the keep probability of one ring attempt (`hkeep`, a hypothesis not proved
in Lean in this step). Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa44_hedged_qrom_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
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
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C)
    (hqc : ∀ GB GS GA, QCheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT) (A GB GS GA) q) (ka : ℕ)
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
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
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
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka
                    (1 - sbar GB GS GA keys HG)).toReal := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty (τ := _root_.MLDSA.mldsa44.tau) (by
    rw [show _root_.MLDSA.mldsa44.tau = 39 from rfl]; norm_num [ringDegree])
  have hp' := SigningParams.of_isApproved isApproved_mldsa44
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
  -- at every oracle, the restriction and the reduction to classical adversaries
  have hstep0 : ∀ GB GS GA, ∃ tab : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44) → (A GB GS GA).Table,
      (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
        𝔼 Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44),
          (((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA) ((((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) +
        2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal +
          (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    obtain ⟨tab, htab⟩ := MaskedSigner.QAdversary.exists_advantage_restrict_le (A GB GS GA)
      (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
      (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2)) ka
      (fun keys HG => 1 - sbar GB GS GA keys HG) (fun _ _ => tsub_le_self)
      fun keys HG c hc hv ha _ b => by
        have hlt : c.idx b < c.ring.1.length := by
          cases b
          · exact hv.idx₀_lt
          · exact hv.idx₁_lt
        exact (meanAttempt_none_le (withExpandA (oraclePrimitives GB GS) GA) hT keys HG c b hlt
          ha).trans ((hkeep GB GS GA).keep keys HG c hc hv ha b hlt)
    refine ⟨tab, ?_⟩
    have h1 := MaskedSigner.QAdversary.advantage_le_restrict_one (A GB GS GA) (D GB GS GA) encY
      (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))
    have hbad := (Finset.expect_le_expect (s := Finset.univ) fun keys _ =>
      expect_restrictBadQ_le (withExpandA (oraclePrimitives GB GS) GA) _ (A GB GS GA)
        (hqc GB GS GA) encY (1 / 2) (x := 89) (by norm_num) keys).trans_eq
      (Fintype.expect_const _)
    have htab' : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal := htab
    have key : ∀ {a b c d f B : ℝ}, a ≤ b + 2 * B → B ≤ f → b ≤ c + 2 * d →
        a ≤ c + 2 * (d + f) := fun h h' h'' => by linarith
    exact key h1 hbad htab'
  choose tab htab using hstep0
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44,
      𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA)
              (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) ≤
        Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((A GB GS GA).atTable (tab GB GS GA Y)) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa44
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa44 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa44 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) ((A GB GS GA).validCountLe_atTable (hC GB GS GA) _)
      ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA))
    have h := expect_le_bkm06_mldsa44_of (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0)
      (fun GB GS GA => (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
        (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)))
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  refine (expect3_le_of_mix _ _ _ htab hY).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
  have hcq := mul_le_mul_of_nonneg_left hchk hq0
  rw [mul_one_div] at hcq
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  linarith

open Classical in
/-- **Anonymity at ML-DSA-44 with FIPS 204 hedged signing in the quantum random-oracle model,
against adversaries with `q` check-oracle queries, the keep bound discharged** (BKM06 Definition 4,
ePrint 2005/304, p. 6, `Q = 1`): `advantage_le_bkm06_mldsa44_hedged_keep_qrom` with the check term
`2 (q + 1) / 2^240` in place of `C / 2^240`, for an adversary whose round algorithm is computed
from `q` classical queries to the check oracle (`hqc`) and makes `q` superposition queries to the
mask oracle, with a distinguisher making `q` superposition queries to the mask oracle, with full
key exposure. Against the hedged signer that also refuses the rings of defect above `1/2`
(`QAdversary.advantage_le_restrict_one`, the check term) every admitted ring has defect at most
`1/2`, so the keep bound `s̄ = β_min θ / 64` holds when the anonymity error is below `1/2`
(`meanAttempt_none_le_keepLevel`), with no check term in the hedged error. For every number `k`
of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 (q + 1) / 2^240 + 2 · (k² / 2^256 + 4 q √(k / 2^256) + 2 · ((1 - β_min θ / 64)^k +
2 · (regularity + McDiarmid)))`. Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa44_hedged_keep_qrom_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
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
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C)
    (hqc : ∀ GB GS GA, QCheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT) (A GB GS GA) q) (ka : ℕ) :
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
          2 * (q + 1) / 2 ^ 240 +
        2 * (ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ /
          64) ^ ka +
          2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty (τ := _root_.MLDSA.mldsa44.tau) (by
    rw [show _root_.MLDSA.mldsa44.tau = 39 from rfl]; norm_num [ringDegree])
  have hp' := SigningParams.of_isApproved isApproved_mldsa44
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  -- a classical adversary with the set of challenges of `A`, for the keep event
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
  have hC' : ∀ GB GS GA, (A' GB GS GA).ValidCountLe C := fun GB GS GA =>
    (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
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
  -- at every oracle, the restriction and the reduction to classical adversaries
  have hstep0 : ∀ GB GS GA, ∃ tab : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44) → (A GB GS GA).Table,
      (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
        𝔼 Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44),
          (((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA) ((((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) +
        2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal +
          (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    obtain ⟨tab, htab⟩ := MaskedSigner.QAdversary.exists_advantage_restrict_le (A GB GS GA)
      (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2)) ka
      (fun keys HG => (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)) (fun _ _ => tsub_le_self)
      fun keys HG c hc hv ha hok b => by
        split_ifs with hO
        · exact meanAttempt_none_le_keepLevel (withExpandA (oraclePrimitives GB GS) GA) hT (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1
            (s := 1 / 2) (by norm_num) hLk keys HG c hc hv ha hok hO b
        · rw [tsub_zero]
          exact PMF.coe_le_one _ _
    refine ⟨tab, ?_⟩
    have h1 := MaskedSigner.QAdversary.advantage_le_restrict_one (A GB GS GA) (D GB GS GA) encY
      (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))
    have hbad := (Finset.expect_le_expect (s := Finset.univ) fun keys _ =>
      expect_restrictBadQ_le (withExpandA (oraclePrimitives GB GS) GA) _ (A GB GS GA)
        (hqc GB GS GA) encY (1 / 2) (x := 89) (by norm_num) keys).trans_eq
      (Fintype.expect_const _)
    have htab' : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal := htab
    have key : ∀ {a b c d f B : ℝ}, a ≤ b + 2 * B → B ≤ f → b ≤ c + 2 * d →
        a ≤ c + 2 * (d + f) := fun h h' h'' => by linarith
    exact key h1 hbad htab'
  choose tab htab using hstep0
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44),
      𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA)
              (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict
                (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) ≤
        Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((A GB GS GA).atTable (tab GB GS GA Y)) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa44
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa44 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa44 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) ((A GB GS GA).validCountLe_atTable (hC GB GS GA) _)
      ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA))
    have h := expect_le_bkm06_mldsa44_of (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0)
      (fun GB GS GA => (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
        (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable
          (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA)))
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  refine (expect3_le_of_mix _ _ _ htab hY).trans ?_
  -- the anonymity error of the adversaries `A'`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤ RM := by
    have hM : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys *
                  Real.log (C + 1) / 2)) ≤
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
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
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
        (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka +
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C) :=
    fun GB GS GA => by
      have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
        (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa44
          (sampleInBallShape_oraclePrims GB) _) GA
      have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA)
        (A' GB GS GA) hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1
        (s := 1 / 2) (by norm_num) (hC' GB GS GA)
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
      have h := MaskedSigner.expect_toReal_hedgeErrorQ_le (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT) 1 q ka
        (fun (keys : Fin n → _root_.MLDSA.Bytes 32)
          (HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps) =>
          oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
            keys HG.1 < 1 / 2) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * (2 * q * √(ka / 2 ^ 256))) =
          ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) := by ring
      rw [hc]
      nlinarith [hK]
  have hE : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka + 2 * RM) +
          (q + 1) / 2 ^ 240 := by
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      Finset.expect_le_expect fun GA _ => add_le_add (hE1 GB GS GA) le_rfl).trans ?_
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
    have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
    have hcq := mul_le_mul_of_nonneg_left hchk hq0
    rw [mul_one_div] at hcq
    nlinarith [hE3]
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  nlinarith [hE]

end HedgedQROMQuery_mldsa44

section HedgedQROMQuery_mldsa65

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ} {G : Type} [Fintype G] [AddGroup G] {q : ℕ}
  {M : ∀ (GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc mldsa65)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa65) T hT).QAdversary (M GB GS GA) G n 1 q)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc mldsa65)).Stmt}
  (D : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa65) T hT).QDist (M GB GS GA) G n 1 q)
  (encY : MaskBox mldsa65 → G)

open Classical in
/-- **Anonymity at ML-DSA-65 with FIPS 204 hedged signing in the quantum random-oracle model,
against adversaries with `q` check-oracle queries** (BKM06 Definition 4, ePrint 2005/304, p. 6,
`Q = 1`, keys given at the start as in CCLM22 Experiment 2, p. 21):
`advantage_le_bkm06_mldsa65_hedged_qrom` with the check term `2 (q + 1) / 2^240` in place of
`C / 2^240`, for an adversary whose round algorithm is computed from `q` classical queries to the
check oracle (`hqc`, `QCheckQueryBounded`) and makes `q` superposition queries to the mask oracle,
with a distinguisher making `q` superposition queries to the mask oracle, with full key exposure.
The proof compares the hedged signer with the hedged signer that also refuses the rings of defect
above `1/2` (`QAdversary.advantage_le_restrict_one`, `expect_restrictBadQ_le`, the check term);
against it the reduction to classical adversaries (`QAdversary.exists_advantage_le`) and the
ideal-mask bound (`advantage_restrictLow_le`, `expect_le_bkm06_mldsa65_of`) have no check term.
`s̄` is a lower bound on the keep probability of one ring attempt (`hkeep`, a hypothesis not proved
in Lean in this step). Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa65_hedged_qrom_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
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
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C)
    (hqc : ∀ GB GS GA, QCheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT) (A GB GS GA) q) (ka : ℕ)
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
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
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
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).hedgeErrorQ 1 q ka
                    (1 - sbar GB GS GA keys HG)).toReal := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa65.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa65
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
  -- at every oracle, the restriction and the reduction to classical adversaries
  have hstep0 : ∀ GB GS GA, ∃ tab : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65) → (A GB GS GA).Table,
      (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
        𝔼 Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65),
          (((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA) ((((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) +
        2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal +
          (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    obtain ⟨tab, htab⟩ := MaskedSigner.QAdversary.exists_advantage_restrict_le (A GB GS GA)
      (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
      (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2)) ka
      (fun keys HG => 1 - sbar GB GS GA keys HG) (fun _ _ => tsub_le_self)
      fun keys HG c hc hv ha _ b => by
        have hlt : c.idx b < c.ring.1.length := by
          cases b
          · exact hv.idx₀_lt
          · exact hv.idx₁_lt
        exact (meanAttempt_none_le (withExpandA (oraclePrimitives GB GS) GA) hT keys HG c b hlt
          ha).trans ((hkeep GB GS GA).keep keys HG c hc hv ha b hlt)
    refine ⟨tab, ?_⟩
    have h1 := MaskedSigner.QAdversary.advantage_le_restrict_one (A GB GS GA) (D GB GS GA) encY
      (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))
    have hbad := (Finset.expect_le_expect (s := Finset.univ) fun keys _ =>
      expect_restrictBadQ_le (withExpandA (oraclePrimitives GB GS) GA) _ (A GB GS GA)
        (hqc GB GS GA) encY (1 / 2) (x := 89) (by norm_num) keys).trans_eq
      (Fintype.expect_const _)
    have htab' : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal := htab
    have key : ∀ {a b c d f B : ℝ}, a ≤ b + 2 * B → B ≤ f → b ≤ c + 2 * d →
        a ≤ c + 2 * (d + f) := fun h h' h'' => by linarith
    exact key h1 hbad htab'
  choose tab htab using hstep0
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65,
      𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
            (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA)
              (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) ≤
        Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((A GB GS GA).atTable (tab GB GS GA Y)) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa65
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa65 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa65 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) ((A GB GS GA).validCountLe_atTable (hC GB GS GA) _)
      ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA))
    have h := expect_le_bkm06_mldsa65_of (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0)
      (fun GB GS GA => (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
        (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)))
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  refine (expect3_le_of_mix _ _ _ htab hY).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
  have hcq := mul_le_mul_of_nonneg_left hchk hq0
  rw [mul_one_div] at hcq
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  linarith

open Classical in
/-- **Anonymity at ML-DSA-65 with FIPS 204 hedged signing in the quantum random-oracle model,
against adversaries with `q` check-oracle queries, the keep bound discharged** (BKM06 Definition 4,
ePrint 2005/304, p. 6, `Q = 1`): `advantage_le_bkm06_mldsa65_hedged_keep_qrom` with the check term
`2 (q + 1) / 2^240` in place of `C / 2^240`, for an adversary whose round algorithm is computed
from `q` classical queries to the check oracle (`hqc`) and makes `q` superposition queries to the
mask oracle, with a distinguisher making `q` superposition queries to the mask oracle, with full
key exposure. Against the hedged signer that also refuses the rings of defect above `1/2`
(`QAdversary.advantage_le_restrict_one`, the check term) every admitted ring has defect at most
`1/2`, so the keep bound `s̄ = β_min θ / 64` holds when the anonymity error is below `1/2`
(`meanAttempt_none_le_keepLevel`), with no check term in the hedged error. For every number `k`
of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 (q + 1) / 2^240 + 2 · (k² / 2^256 + 4 q √(k / 2^256) + 2 · ((1 - β_min θ / 64)^k +
2 · (regularity + McDiarmid)))`. Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa65_hedged_keep_qrom_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
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
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C)
    (hqc : ∀ GB GS GA, QCheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT) (A GB GS GA) q) (ka : ℕ) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240 +
        2 * (ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ /
          64) ^ ka +
          2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa65.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa65
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  -- a classical adversary with the set of challenges of `A`, for the keep event
  set A' := fun GB GS GA => (A GB GS GA).atTable fun x =>
    (((A GB GS GA).entryAlg x).outLaw 0).support_nonempty.some
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
  have hC' : ∀ GB GS GA, (A' GB GS GA).ValidCountLe C := fun GB GS GA =>
    (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
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
  -- at every oracle, the restriction and the reduction to classical adversaries
  have hstep0 : ∀ GB GS GA, ∃ tab : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65) → (A GB GS GA).Table,
      (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
        𝔼 Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65),
          (((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA) ((((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) +
        2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).hedgeErrorQ 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal +
          (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    obtain ⟨tab, htab⟩ := MaskedSigner.QAdversary.exists_advantage_restrict_le (A GB GS GA)
      (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2)) ka
      (fun keys HG => (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)) (fun _ _ => tsub_le_self)
      fun keys HG c hc hv ha hok b => by
        split_ifs with hO
        · exact meanAttempt_none_le_keepLevel (withExpandA (oraclePrimitives GB GS) GA) hT (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1
            (s := 1 / 2) (by norm_num) hLk keys HG c hc hv ha hok hO b
        · rw [tsub_zero]
          exact PMF.coe_le_one _ _
    refine ⟨tab, ?_⟩
    have h1 := MaskedSigner.QAdversary.advantage_le_restrict_one (A GB GS GA) (D GB GS GA) encY
      (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))
    have hbad := (Finset.expect_le_expect (s := Finset.univ) fun keys _ =>
      expect_restrictBadQ_le (withExpandA (oraclePrimitives GB GS) GA) _ (A GB GS GA)
        (hqc GB GS GA) encY (1 / 2) (x := 89) (by norm_num) keys).trans_eq
      (Fintype.expect_const _)
    have htab' : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal := htab
    have key : ∀ {a b c d f B : ℝ}, a ≤ b + 2 * B → B ≤ f → b ≤ c + 2 * d →
        a ≤ c + 2 * (d + f) := fun h h' h'' => by linarith
    exact key h1 hbad htab'
  choose tab htab using hstep0
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65),
      𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
            (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA)
              (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict
                (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) ≤
        Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((A GB GS GA).atTable (tab GB GS GA Y)) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa65
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa65 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa65 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) ((A GB GS GA).validCountLe_atTable (hC GB GS GA) _)
      ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA))
    have h := expect_le_bkm06_mldsa65_of (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0)
      (fun GB GS GA => (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
        (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable
          (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA)))
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  refine (expect3_le_of_mix _ _ _ htab hY).trans ?_
  -- the anonymity error of the adversaries `A'`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤ RM := by
    have hM : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys *
                  Real.log (C + 1) / 2)) ≤
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
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
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
        (concreteEnc mldsa65) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka +
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C) :=
    fun GB GS GA => by
      have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
        (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa65
          (sampleInBallShape_oraclePrims GB) _) GA
      have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA)
        (A' GB GS GA) hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1
        (s := 1 / 2) (by norm_num) (hC' GB GS GA)
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
      have h := MaskedSigner.expect_toReal_hedgeErrorQ_le (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT) 1 q ka
        (fun (keys : Fin n → _root_.MLDSA.Bytes 32)
          (HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps) =>
          oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
            keys HG.1 < 1 / 2) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * (2 * q * √(ka / 2 ^ 256))) =
          ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) := by ring
      rw [hc]
      nlinarith [hK]
  have hE : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka + 2 * RM) +
          (q + 1) / 2 ^ 240 := by
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      Finset.expect_le_expect fun GA _ => add_le_add (hE1 GB GS GA) le_rfl).trans ?_
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
    have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
    have hcq := mul_le_mul_of_nonneg_left hchk hq0
    rw [mul_one_div] at hcq
    nlinarith [hE3]
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  nlinarith [hE]

end HedgedQROMQuery_mldsa65

section HedgedQROMQuery_mldsa87

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ} {G : Type} [Fintype G] [AddGroup G] {q : ℕ}
  {M : ∀ (GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc mldsa87)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa87) T hT).QAdversary (M GB GS GA) G n 1 q)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc mldsa87)).Stmt}
  (D : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa87) T hT).QDist (M GB GS GA) G n 1 q)
  (encY : MaskBox mldsa87 → G)

open Classical in
/-- **Anonymity at ML-DSA-87 with FIPS 204 hedged signing in the quantum random-oracle model,
against adversaries with `q` check-oracle queries** (BKM06 Definition 4, ePrint 2005/304, p. 6,
`Q = 1`, keys given at the start as in CCLM22 Experiment 2, p. 21):
`advantage_le_bkm06_mldsa87_hedged_qrom` with the check term `2 (q + 1) / 2^240` in place of
`C / 2^240`, for an adversary whose round algorithm is computed from `q` classical queries to the
check oracle (`hqc`, `QCheckQueryBounded`) and makes `q` superposition queries to the mask oracle,
with a distinguisher making `q` superposition queries to the mask oracle, with full key exposure.
The proof compares the hedged signer with the hedged signer that also refuses the rings of defect
above `1/2` (`QAdversary.advantage_le_restrict_one`, `expect_restrictBadQ_le`, the check term);
against it the reduction to classical adversaries (`QAdversary.exists_advantage_le`) and the
ideal-mask bound (`advantage_restrictLow_le`, `expect_le_bkm06_mldsa87_of`) have no check term.
`s̄` is a lower bound on the keep probability of one ring attempt (`hkeep`, a hypothesis not proved
in Lean in this step). Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa87_hedged_qrom_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
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
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C)
    (hqc : ∀ GB GS GA, QCheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT) (A GB GS GA) q) (ka : ℕ)
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
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
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
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).hedgeErrorQ 1 q ka
                    (1 - sbar GB GS GA keys HG)).toReal := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa87.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa87
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
  -- at every oracle, the restriction and the reduction to classical adversaries
  have hstep0 : ∀ GB GS GA, ∃ tab : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87) → (A GB GS GA).Table,
      (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
        𝔼 Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87),
          (((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA) ((((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) +
        2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal +
          (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    obtain ⟨tab, htab⟩ := MaskedSigner.QAdversary.exists_advantage_restrict_le (A GB GS GA)
      (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)
      (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2)) ka
      (fun keys HG => 1 - sbar GB GS GA keys HG) (fun _ _ => tsub_le_self)
      fun keys HG c hc hv ha _ b => by
        have hlt : c.idx b < c.ring.1.length := by
          cases b
          · exact hv.idx₀_lt
          · exact hv.idx₁_lt
        exact (meanAttempt_none_le (withExpandA (oraclePrimitives GB GS) GA) hT keys HG c b hlt
          ha).trans ((hkeep GB GS GA).keep keys HG c hc hv ha b hlt)
    refine ⟨tab, ?_⟩
    have h1 := MaskedSigner.QAdversary.advantage_le_restrict_one (A GB GS GA) (D GB GS GA) encY
      (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))
    have hbad := (Finset.expect_le_expect (s := Finset.univ) fun keys _ =>
      expect_restrictBadQ_le (withExpandA (oraclePrimitives GB GS) GA) _ (A GB GS GA)
        (hqc GB GS GA) encY (1 / 2) (x := 89) (by norm_num) keys).trans_eq
      (Fintype.expect_const _)
    have htab' : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).hedgeErrorQ 1 q ka (1 - sbar GB GS GA keys HG)).toReal := htab
    have key : ∀ {a b c d f B : ℝ}, a ≤ b + 2 * B → B ≤ f → b ≤ c + 2 * d →
        a ≤ c + 2 * (d + f) := fun h h' h'' => by linarith
    exact key h1 hbad htab'
  choose tab htab using hstep0
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87,
      𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
            (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA)
              (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) ≤
        Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((A GB GS GA).atTable (tab GB GS GA Y)) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa87
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa87 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa87 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) ((A GB GS GA).validCountLe_atTable (hC GB GS GA) _)
      ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA))
    have h := expect_le_bkm06_mldsa87_of (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0)
      (fun GB GS GA => (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
        (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)))
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  refine (expect3_le_of_mix _ _ _ htab hY).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
  have hcq := mul_le_mul_of_nonneg_left hchk hq0
  rw [mul_one_div] at hcq
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  linarith

open Classical in
/-- **Anonymity at ML-DSA-87 with FIPS 204 hedged signing in the quantum random-oracle model,
against adversaries with `q` check-oracle queries, the keep bound discharged** (BKM06 Definition 4,
ePrint 2005/304, p. 6, `Q = 1`): `advantage_le_bkm06_mldsa87_hedged_keep_qrom` with the check term
`2 (q + 1) / 2^240` in place of `C / 2^240`, for an adversary whose round algorithm is computed
from `q` classical queries to the check oracle (`hqc`) and makes `q` superposition queries to the
mask oracle, with a distinguisher making `q` superposition queries to the mask oracle, with full
key exposure. Against the hedged signer that also refuses the rings of defect above `1/2`
(`QAdversary.advantage_le_restrict_one`, the check term) every admitted ring has defect at most
`1/2`, so the keep bound `s̄ = β_min θ / 64` holds when the anonymity error is below `1/2`
(`meanAttempt_none_le_keepLevel`), with no check term in the hedged error. For every number `k`
of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 (q + 1) / 2^240 + 2 · (k² / 2^256 + 4 q √(k / 2^256) + 2 · ((1 - β_min θ / 64)^k +
2 · (regularity + McDiarmid)))`. Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa87_hedged_keep_qrom_query (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
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
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C)
    (hqc : ∀ GB GS GA, QCheckQueryBounded (withExpandA (oraclePrimitives GB GS) GA)
      (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT) (A GB GS GA) q) (ka : ℕ) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
                (M GB GS GA).wiError δ C +
          2 * (q + 1) / 2 ^ 240 +
        2 * (ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ /
          64) ^ ka +
          2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa87.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa87
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  -- a classical adversary with the set of challenges of `A`, for the keep event
  set A' := fun GB GS GA => (A GB GS GA).atTable fun x =>
    (((A GB GS GA).entryAlg x).outLaw 0).support_nonempty.some
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
  have hC' : ∀ GB GS GA, (A' GB GS GA).ValidCountLe C := fun GB GS GA =>
    (A GB GS GA).validCountLe_atTable (hC GB GS GA) _
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
  -- at every oracle, the restriction and the reduction to classical adversaries
  have hstep0 : ∀ GB GS GA, ∃ tab : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87) → (A GB GS GA).Table,
      (A GB GS GA).advantage (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ≤
        𝔼 Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87),
          (((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA) ((((A GB GS GA).atTable (tab Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist
              (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) +
        2 * (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).hedgeErrorQ 1 q ka
                (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal +
          (q + 1) * checkError reps tol (1 / 2) 89) := fun GB GS GA => by
    obtain ⟨tab, htab⟩ := MaskedSigner.QAdversary.exists_advantage_restrict_le (A GB GS GA)
      (D GB GS GA) encY (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2)) ka
      (fun keys HG => (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)) (fun _ _ => tsub_le_self)
      fun keys HG c hc hv ha hok b => by
        split_ifs with hO
        · exact meanAttempt_none_le_keepLevel (withExpandA (oraclePrimitives GB GS) GA) hT (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1
            (s := 1 / 2) (by norm_num) hLk keys HG c hc hv ha hok hO b
        · rw [tsub_zero]
          exact PMF.coe_le_one _ _
    refine ⟨tab, ?_⟩
    have h1 := MaskedSigner.QAdversary.advantage_le_restrict_one (A GB GS GA) (D GB GS GA) encY
      (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))
    have hbad := (Finset.expect_le_expect (s := Finset.univ) fun keys _ =>
      expect_restrictBadQ_le (withExpandA (oraclePrimitives GB GS) GA) _ (A GB GS GA)
        (hqc GB GS GA) encY (1 / 2) (x := 89) (by norm_num) keys).trans_eq
      (Fintype.expect_const _)
    have htab' : _ ≤ _ + 2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
          ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal := htab
    have key : ∀ {a b c d f B : ℝ}, a ≤ b + 2 * B → B ≤ f → b ≤ c + 2 * d →
        a ≤ c + 2 * (d + f) := fun h h' h'' => by linarith
    exact key h1 hbad htab'
  choose tab htab using hstep0
  -- at every fixed mask oracle, the restricted ideal-mask bound: no check term
  have hY : ∀ Y : (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87),
      𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
            (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage (E GB GS GA)
              (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict
                (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA) (honest GB GS GA)) ≤
        Bi := fun Y => by
    have hcore := fun GB GS GA => advantage_restrictLow_le (withExpandA (oraclePrimitives GB GS) GA)
      ((A GB GS GA).atTable (tab GB GS GA Y)) hp' hβ0 hβt
      (SigningLaws.withExpandA _ (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa87
        (sampleInBallShape_oraclePrims GB) _) GA)
      (VerifyLaws.withExpandA _ (verifyLaws_concreteWithSampleInBallExpandS isApproved_mldsa87 _ _) GA)
      (fun w => concreteEnc_highBitsVec isApproved_mldsa87 w)
      (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2) (by norm_num)
      (Rv GB GS GA) (hz GB GS GA) ((A GB GS GA).validCountLe_atTable (hC GB GS GA) _)
      ((((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA)
        (Qs GB GS GA) (honest GB GS GA))
    have h := expect_le_bkm06_mldsa87_of (fun GB GS GA => (A GB GS GA).atTable (tab GB GS GA Y))
      hβ0 hβ1 hβt hθ0 hθ1 (s := 1 / 2) (by norm_num) (chk := 0)
      (fun GB GS GA => (((A GB GS GA).atTable (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).advantage
        (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) ((((A GB GS GA).atTable
          (tab GB GS GA Y)).restrict (lowOk (withExpandA (oraclePrimitives GB GS) GA) βmin (1 / 2))).likelierDist (E GB GS GA) (Qs GB GS GA)
            (honest GB GS GA)))
      (fun GB GS GA => by
        simpa only [Nat.cast_one, one_mul, one_add_one_eq_two, add_zero] using hcore GB GS GA)
      le_rfl
    rw [h2, hm, add_zero] at h
    exact h
  refine (expect3_le_of_mix _ _ _ htab hY).trans ?_
  -- the anonymity error of the adversaries `A'`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤ RM := by
    have hM : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys *
                  Real.log (C + 1) / 2)) ≤
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
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
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
        (concreteEnc mldsa87) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka +
          2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C) :=
    fun GB GS GA => by
      have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
        (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa87
          (sampleInBallShape_oraclePrims GB) _) GA
      have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA)
        (A' GB GS GA) hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1
        (s := 1 / 2) (by norm_num) (hC' GB GS GA)
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
      have h := MaskedSigner.expect_toReal_hedgeErrorQ_le (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT) 1 q ka
        (fun (keys : Fin n → _root_.MLDSA.Bytes 32)
          (HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps) =>
          oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
            keys HG.1 < 1 / 2) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * (2 * q * √(ka / 2 ^ 256))) =
          ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) := by ring
      rw [hc]
      nlinarith [hK]
  have hE : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
              ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).hedgeErrorQ 1 q ka (1 - if oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ keys HG.1 < 1 / 2
                then ENNReal.ofReal Lk else 0)).toReal +
            (q + 1) * checkError reps tol (1 / 2) 89) ≤
        ka ^ 2 / 2 ^ 256 + 4 * q * √(ka / 2 ^ 256) + 2 * ((1 - Lk) ^ ka + 2 * RM) +
          (q + 1) / 2 ^ 240 := by
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      Finset.expect_le_expect fun GA _ => add_le_add (hE1 GB GS GA) le_rfl).trans ?_
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
    have hq0 : (0 : ℝ) ≤ q + 1 := by positivity
    have hcq := mul_le_mul_of_nonneg_left hchk hq0
    rw [mul_one_div] at hcq
    nlinarith [hE3]
  have hfin : 2 * ((q + 1 : ℝ) / 2 ^ 240) = 2 * (q + 1) / 2 ^ 240 := by ring
  nlinarith [hE]

end HedgedQROMQuery_mldsa87

end MLDSAW1

end GordieHowe.Ring
