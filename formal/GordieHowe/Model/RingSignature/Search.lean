-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.HistoryLogs
public import GordieHowe.Model.RingSignature.Adversary
public import GordieHowe.Model.Quantum.O2H.Search

@[expose] public section

/-!
# Search in the QROM against the adversaries of the ring-signature games

The game-level form of `Distinguisher.eventProb_searchLogs_le`
(`GordieHowe/Model/Quantum/O2H/Search.lean`). The oracle's values split as `e : Y ≃ Y₁ × Y₂`, its
points are labelled by `κ : X → Option L`, and a label `l` is hit by `H` when `P l H`, a predicate
that reads only the block of `H` at `l` (`ReadsBlocks`), holds with probability at most `ε` for
the uniform oracle. Requests carry labels `lab : Req → Option L`. For a challenger answering
request by request (`Challenger.AnswersBy resp`) whose responses do not change when only the
blocks of the oracle change, a `t`-query adversary's history has an entry whose request has a hit
label with probability at most `(√Q + 2 t)² ε`.

- `Challenger.respEnv C resp μH`: the pure environment with the oracle as its state that answers by
  `resp`; `Challenger.final_toPureEnv_eq`: the pure game of a challenger answering by `resp` has
  the final states of `respEnv`.
- `QueryBoundedAdversary.sum_transcriptLaw_hit_le`: the bound for an oracle law uniform on the
  labels, through `QueryBoundedAdversary.transcriptLaw_histHas`
  (`GordieHowe/Model/RingSignature/HistoryLogs.lean`) and `eventProb_searchLogs_le_of_mul_le`.
- `QueryBoundedAdversary.sum_uniform_transcriptLaw_hit_le`: the uniform oracle, with the adversary
  chosen from the oracle's rest (agreement off the labels), by conditioning on the rest
  (`IsUniformOnLabels.sum_mul_eq`, `expect_setLabelBlocks_eq`).
- `RingSignature.toReal_runLaw_hit_le`: the bound for the run of a game (`runLaw`), with start
  draws `k`, the adversary `A k H`, challengers `C k` with at most `Q` requests and labels
  `lab k`. `RingSignature.toReal_runLaw_hit_le_of_lab`: labels independent of `k`.
-/

namespace GordieHowe

open GordieHowe.Quantum
open Finset
open scoped BigOperators ENNReal

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

namespace Quantum.Challenger

/-- **The pure environment of a challenger answering by `resp`**, with the oracle as its state:
the tape `(H, c)` with `H ← μH` and the coins `c` independent, request number `j` answered by
`resp c H j`, the oracle never changed. -/
noncomputable def respEnv (C : Challenger X Y Req Resp)
    (resp : C.Coins → (X → Y) → ℕ → Req → Option Resp) (μH : PMF (X → Y)) :
    Env ((X → Y) × C.Coins) Req Resp X Y C.Q where
  μ := prodLaw μH C.coins
  oracle₀ ω := ω.1
  respond ω j req s := ⟨resp ω.2 ω.1 j req, s⟩

variable {C : Challenger X Y Req Resp} {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- The oracle in force of `respEnv` is the oracle of the tape. -/
theorem respEnv_oracleIn (μH : PMF (X → Y)) (ω : (X → Y) × C.Coins) (rs : List Req) :
    (C.respEnv resp μH).oracleIn ω rs = ω.1 :=
  Env.oracleIn_of_keepsState (fun _ _ _ _ => rfl) ω rs

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- `respEnv` answers request number `j < Q` by `resp`, and later requests by `none`. -/
theorem respEnv_answerAfter (μH : PMF (X → Y)) (ω : (X → Y) × C.Coins) (rs : List Req)
    (req : Req) : (C.respEnv resp μH).answerAfter ω rs req =
      if rs.length < C.Q then resp ω.2 ω.1 rs.length req else none := by
  unfold Env.answerAfter
  split_ifs <;> rfl

omit [DecidableEq Y] [Nonempty X] in
/-- **The pure game of a challenger answering by `resp` has the final states of `respEnv`.** -/
theorem final_toPureEnv_eq {W : Type*} [Fintype W] {n m : ℕ}
    (D : Distinguisher W X Y Req Resp n m) (h : C.AnswersBy resp) (μH : PMF (X → Y))
    (post : (X → Y) → QState (DReg W n X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req Resp))
    (ω : (X → Y) × C.Coins) :
    D.final C.toPureEnv post ω = D.final (C.respEnv resp μH) post ω :=
  D.final_congr _ _ (fun lg k => by
      simp only [Env.answer]
      rcases lg k with _ | req
      · rfl
      · simp only [Option.elim, h.answerAfter, respEnv_answerAfter])
    (fun lg => by
      rw [h.oracle]
      exact (respEnv_oracleIn μH ω _).symm) post

end Quantum.Challenger

namespace Quantum.QueryBoundedAdversary

variable {Y₁ Y₂ L : Type} [Fintype L] [DecidableEq L] [Fintype Y₁] [DecidableEq Y₁]
  {e : Y ≃ Y₁ × Y₂} {κ : X → Option L}

/-- **The history event of a search**: the adversary terminates and its history has an entry whose
request has a label `l` with `P l H`. -/
def HistHit (lab : Req → Option L) (P : L → (X → Y) → Prop) (H : X → Y) :
    Set (Option (O × List (HistoryEntry Req Resp))) :=
  {x | ∃ p ∈ x, ∃ h ∈ p.2, ∃ l, lab h.request = some l ∧ P l H}

/-- **Search against a `t`-query adversary, for an oracle law uniform on the labels**: for a
challenger answering request by request (`Challenger.AnswersBy resp`) whose responses do not
change when only the blocks of the oracle change (`hresp`), and a predicate `P l` of the labels
that reads only the blocks (`hP`) and holds with probability at most `ε` under `μH` (`hε`), the
adversary's history has an entry whose request has a label `l` with `P l H` with probability, averaged
over `H ← μH`, at most `(√Q + 2 t)² ε`. -/
theorem sum_transcriptLaw_hit_le (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}
    (hC : C.AnswersBy resp)
    (hresp : ∀ c j req H H', AgreeOffLabels e κ H H' → resp c H j req = resp c H' j req)
    {μH : PMF (X → Y)} (hμH : IsUniformOnLabels e κ μH) {P : L → (X → Y) → Prop}
    (hP : ReadsBlocks e κ P) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ l, (μH.toOuterMeasure {H | P l H}).toReal ≤ ε) (lab : Req → Option L) :
    ∑ H, (μH H).toReal * ((𝒜.transcriptLaw C H).toOuterMeasure (HistHit lab P H)).toReal ≤
      (√C.Q + 2 * t) ^ 2 * ε := by
  classical
  set b : ℝ := (√C.Q + 2 * t) ^ 2 * ε
  have hb0 : 0 ≤ b := by positivity
  set G : 𝒜.Aux → (X → Y) → ℝ := fun a H => ∑ c, (C.coins c).toReal *
    prob ((𝒜.alg a).outAcc Set.univ ∩
      logsIn {lg | ∃ req ∈ (requests lg).take C.Q, (fun req => ∃ l, lab req = some l ∧ P l H) req})
      ((𝒜.alg a).runDil.final C.toPureEnv noPost (H, c))
  have hG0 : ∀ a H, 0 ≤ G a H := fun a H =>
    sum_nonneg fun c _ => mul_nonneg ENNReal.toReal_nonneg (prob_nonneg _ _)
  have hT : ∀ H, (𝒜.transcriptLaw C H).toOuterMeasure (HistHit lab P H) =
      ∑' a, 𝒜.aux a * ENNReal.ofReal (G a H) := fun H =>
    𝒜.transcriptLaw_histHas C hC H fun req => ∃ l, lab req = some l ∧ P l H
  -- the bound for each auxiliary input
  have haux : ∀ a, ∑ H, (μH H).toReal * G a H ≤ b := by
    intro a
    have hbl : ∀ l, (μH.toOuterMeasure {H | blockPred e κ P l (labelBlocks e κ H l)}).toReal ≤ ε :=
      fun l => by simpa only [hP.blockPred_iff] using hε l
    have hs := (𝒜.alg a).runDil.eventProb_searchLogs_le_of_mul_le (𝒜.alg a).runDilBudget
      (C.respEnv resp μH) (fun H c => prodLaw_apply _ _ _ _) hμH (fun ω rs => Challenger.respEnv_oracleIn μH ω rs)
      (fun H H' c rs req h => by
        rw [Challenger.respEnv_answerAfter, Challenger.respEnv_answerAfter, hresp c _ req H H' h])
      (blockPred e κ P) lab ((𝒜.alg a).outAcc Set.univ) hε0 hbl (𝒜.queries_le a)
    refine le_of_eq_of_le ?_ hs
    unfold Distinguisher.eventProb
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun H _ => ?_
    simp only [G, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    have hset : ∀ m, searchLogs (m := m) lab
        (fun l => blockPred e κ P l (labelBlocks e κ H l)) C.Q =
        {lg | ∃ req ∈ (requests lg).take C.Q, ∃ l, lab req = some l ∧ P l H} := fun m => by
      simp only [searchLogs, hP.blockPred_iff]
    change _ = (prodLaw μH C.coins (H, c)).toReal * _
    rw [hset, prodLaw_apply, ENNReal.toReal_mul,
      ← C.final_toPureEnv_eq (𝒜.alg a).runDil hC μH noPost (H, c)]
    ring
  -- the average over the auxiliary input
  have hfin : ∀ H, (𝒜.transcriptLaw C H).toOuterMeasure (HistHit lab P H) ≠ ⊤ := fun H =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  have hsum : ∑ H, μH H * (𝒜.transcriptLaw C H).toOuterMeasure (HistHit lab P H) ≤
      ENNReal.ofReal b := by
    simp only [hT, ← ENNReal.tsum_mul_left]
    rw [← tsum_fintype (L := .unconditional _), ENNReal.tsum_comm]
    calc ∑' a, ∑' H, μH H * (𝒜.aux a * ENNReal.ofReal (G a H))
        = ∑' a, 𝒜.aux a * ENNReal.ofReal (∑ H, (μH H).toReal * G a H) := by
          refine tsum_congr fun a => ?_
          rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg fun H _ =>
            mul_nonneg ENNReal.toReal_nonneg (hG0 a H), mul_sum]
          refine sum_congr rfl fun H _ => ?_
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
          ring
      _ ≤ ∑' a, 𝒜.aux a * ENNReal.ofReal b :=
          ENNReal.tsum_le_tsum fun a => by gcongr; exact haux a
      _ = ENNReal.ofReal b := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hreal : ∑ H, (μH H).toReal * ((𝒜.transcriptLaw C H).toOuterMeasure (HistHit lab P H)).toReal =
      (∑ H, μH H * (𝒜.transcriptLaw C H).toOuterMeasure (HistHit lab P H)).toReal := by
    rw [ENNReal.toReal_sum fun H _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin H)]
    simp only [ENNReal.toReal_mul]
  rw [hreal]
  exact (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.2 fun H _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin H)) ENNReal.ofReal_ne_top).2 hsum |>.trans
    (ENNReal.toReal_ofReal hb0).le

/-- **Search against a `t`-query adversary chosen from the oracle's rest, for the uniform
oracle**: the adversary `𝒜 H` depends on `H` only off the labels (`h𝒜`), and `P l H` holds with
probability at most `ε` for the uniform oracle; otherwise as `sum_transcriptLaw_hit_le`. The proof
conditions on the rest of the oracle (`IsUniformOnLabels.sum_mul_eq`, `expect_setLabelBlocks_eq`),
under which the adversary is fixed and the oracle law is `offLabelsLaw`. -/
theorem sum_uniform_transcriptLaw_hit_le (𝒜 : (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (h𝒜 : ∀ H H', AgreeOffLabels e κ H H' → 𝒜 H = 𝒜 H')
    (C : Challenger X Y Req Resp) {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}
    (hC : C.AnswersBy resp)
    (hresp : ∀ c j req H H', AgreeOffLabels e κ H H' → resp c H j req = resp c H' j req)
    {P : L → (X → Y) → Prop} (hP : ReadsBlocks e κ P) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ l, ((PMF.uniformOfFintype (X → Y)).toOuterMeasure {H | P l H}).toReal ≤ ε)
    (lab : Req → Option L) :
    ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((𝒜 H).transcriptLaw C H).toOuterMeasure (HistHit lab P H)).toReal ≤
      (√C.Q + 2 * t) ^ 2 * ε := by
  classical
  have hset : ∀ l, {H : X → Y | P l H} =
      {H | labelBlocks e κ H ∈ {u : LabelBlocks κ Y₁ | blockPred e κ P l (u l)}} := fun l => by
    ext H
    simp [hP.blockPred_iff]
  rw [(isUniformOnLabels_uniform (e := e) (κ := κ)).sum_mul_eq (Y₁ := Y₁)]
  calc ∑ H₀, (PMF.uniformOfFintype (X → Y) H₀).toReal * 𝔼 u,
        (((𝒜 (setLabelBlocks e κ H₀ u)).transcriptLaw C (setLabelBlocks e κ H₀ u)).toOuterMeasure
          (HistHit lab P (setLabelBlocks e κ H₀ u))).toReal
      ≤ ∑ H₀, (PMF.uniformOfFintype (X → Y) H₀).toReal * ((√C.Q + 2 * t) ^ 2 * ε) := by
        refine sum_le_sum fun H₀ _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        have hfix : ∀ u, 𝒜 (setLabelBlocks e κ H₀ u) = 𝒜 H₀ := fun u =>
          h𝒜 _ _ (agreeOffLabels_setLabelBlocks H₀ u).symm
        simp only [hfix]
        rw [expect_setLabelBlocks_eq H₀
          (fun H => (((𝒜 H₀).transcriptLaw C H).toOuterMeasure (HistHit lab P H)).toReal)]
        refine (𝒜 H₀).sum_transcriptLaw_hit_le C hC hresp (isUniformOnLabels_offLabelsLaw H₀) hP
          hε0 (fun l => ?_) lab
        rw [hset, (isUniformOnLabels_offLabelsLaw H₀).toReal_toOuterMeasure_eq,
          ← (isUniformOnLabels_uniform (e := e) (κ := κ)).toReal_toOuterMeasure_eq, ← hset]
        exact hε l
    _ = (√C.Q + 2 * t) ^ 2 * ε := by rw [← sum_mul, PMF.sum_toReal, one_mul]

end Quantum.QueryBoundedAdversary

namespace RingSignature

variable {Y₁ Y₂ L : Type} [Fintype L] [DecidableEq L] [Fintype Y₁] [DecidableEq Y₁]
  {e : Y ≃ Y₁ × Y₂} {κ : X → Option L}

/-- **Search in a game's run**: with start draws `k`, the adversary `A k H` chosen from the start
draw and the oracle's rest off the labels (`hA`), for every `k` a challenger `C k` with at most `Q`
requests answering request by request (`hC`, `hQ`) whose responses do not change when only the
blocks of the oracle change (`hresp`), a predicate `P l` of the labels that reads only the blocks
(`hP`) and holds with probability at most `ε` for the uniform oracle (`hε`), and labels
`lab k` of the requests, the adversary's history has an entry whose request has a label `l` with
`P l H` with probability at most `(√Q + 2 t)² ε`. -/
theorem toReal_runLaw_hit_le {K : Type} [Fintype K] [Nonempty K]
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffLabels e κ H H' → A k H = A k H')
    {C : K → Challenger X Y Req Resp} {resp : ∀ k, (C k).Coins → (X → Y) → ℕ → Req → Option Resp}
    (hC : ∀ k, (C k).AnswersBy (resp k)) {Q : ℕ} (hQ : ∀ k, (C k).Q ≤ Q)
    (hresp : ∀ k c j req H H', AgreeOffLabels e κ H H' → resp k c H j req = resp k c H' j req)
    {P : L → (X → Y) → Prop} (hP : ReadsBlocks e κ P) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ l, ((PMF.uniformOfFintype (X → Y)).toOuterMeasure {H | P l H}).toReal ≤ ε)
    (lab : K → Req → Option L) :
    ((runLaw A C).toOuterMeasure
        {x | ∃ p ∈ x.2.2, ∃ h ∈ p.2, ∃ l, lab x.1 h.request = some l ∧ P l x.2.1}).toReal ≤
      (√Q + 2 * t) ^ 2 * ε := by
  set b : ℝ := (√Q + 2 * t) ^ 2 * ε
  have hb0 : 0 ≤ b := by positivity
  have hfin : ∀ k H, ((A k H).transcriptLaw (C k) H).toOuterMeasure
      (QueryBoundedAdversary.HistHit (lab k) P H) ≠ ⊤ := fun k H =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  have hk : ∀ k, ∑ H, PMF.uniformOfFintype (X → Y) H * ((A k H).transcriptLaw (C k) H).toOuterMeasure
      (QueryBoundedAdversary.HistHit (lab k) P H) ≤ ENNReal.ofReal b := by
    intro k
    rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sum_ne_top.2 fun H _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin k H)) hb0,
      ENNReal.toReal_sum fun H _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin k H)]
    simp only [ENNReal.toReal_mul]
    refine (QueryBoundedAdversary.sum_uniform_transcriptLaw_hit_le (A k) (hA k) (C k) (hC k)
      (hresp k) hP hε0 hε (lab k)).trans ?_
    have hq : √((C k).Q : ℝ) ≤ √Q := Real.sqrt_le_sqrt (by exact_mod_cast hQ k)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) 2) hε0
  have hlaw : (runLaw A C).toOuterMeasure
      {x | ∃ p ∈ x.2.2, ∃ h ∈ p.2, ∃ l, lab x.1 h.request = some l ∧ P l x.2.1} =
      ∑' k, PMF.uniformOfFintype K k * ∑ H, PMF.uniformOfFintype (X → Y) H *
        ((A k H).transcriptLaw (C k) H).toOuterMeasure
          (QueryBoundedAdversary.HistHit (lab k) P H) := by
    rw [runLaw, PMF.toOuterMeasure_bind_apply]
    refine tsum_congr fun k => ?_
    congr 1
    rw [PMF.toOuterMeasure_bind_apply, tsum_fintype]
    refine sum_congr rfl fun H _ => ?_
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  have hle : (runLaw A C).toOuterMeasure
      {x | ∃ p ∈ x.2.2, ∃ h ∈ p.2, ∃ l, lab x.1 h.request = some l ∧ P l x.2.1} ≤
      ENNReal.ofReal b := by
    rw [hlaw]
    calc ∑' k, PMF.uniformOfFintype K k * _ ≤ ∑' k, PMF.uniformOfFintype K k * ENNReal.ofReal b :=
          ENNReal.tsum_le_tsum fun k => by gcongr; exact hk k
      _ = ENNReal.ofReal b := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  exact (ENNReal.toReal_le_of_le_ofReal hb0 hle)

/-- **Search in a game's run, with labels independent of the start draw**:
`toReal_runLaw_hit_le` for `lab k = lab`. -/
theorem toReal_runLaw_hit_le_of_lab {K : Type} [Fintype K] [Nonempty K]
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffLabels e κ H H' → A k H = A k H')
    {C : K → Challenger X Y Req Resp} {resp : ∀ k, (C k).Coins → (X → Y) → ℕ → Req → Option Resp}
    (hC : ∀ k, (C k).AnswersBy (resp k)) {Q : ℕ} (hQ : ∀ k, (C k).Q ≤ Q)
    (hresp : ∀ k c j req H H', AgreeOffLabels e κ H H' → resp k c H j req = resp k c H' j req)
    {P : L → (X → Y) → Prop} (hP : ReadsBlocks e κ P) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ l, ((PMF.uniformOfFintype (X → Y)).toOuterMeasure {H | P l H}).toReal ≤ ε)
    (lab : Req → Option L) :
    ((runLaw A C).toOuterMeasure
        {x | ∃ p ∈ x.2.2, ∃ h ∈ p.2, ∃ l, lab h.request = some l ∧ P l x.2.1}).toReal ≤
      (√Q + 2 * t) ^ 2 * ε :=
  toReal_runLaw_hit_le A hA hC hQ hresp hP hε0 hε fun _ => lab

end RingSignature

end GordieHowe
