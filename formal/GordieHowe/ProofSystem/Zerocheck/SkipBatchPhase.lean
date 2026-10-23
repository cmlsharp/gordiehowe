-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.FieldSkipMasked
public import GordieHowe.Applications.Keccak.HashCircuit.SkipHVZK

@[expose] public section

/-!
# The batch phase of the masked skip zerocheck, at any degree

The phase of the C++ batch driver (`lib/gordiehowe/compiler/batch.h`, `BatchKernel::reduce`;
`field_skip.h`, `MaskedFieldSkip::prove` and `rows_of`) for a relation of degree at most `D` on `k`
operands, as a typed protocol phase, with the claim reduction "the relation holds on the committed
operands, or a skip event occurred at a challenge already drawn" (`reduction`), the honest causal
transcript family (`phaseFamily`) and the hiding law of a masked honest phase
(`maskedPhase_identDistrib`). The skip message has `e` coordinates, read at the skip domain's
`(D − 1)(w − 1)` points through `he : (D − 1)(w − 1) = e`, so that both the field batch
(`e = (2 − 1)(w − 1)`) and the bit-packed Keccak batch (`e = w − 1`, `HashCircuit.Skip.phase`) are
this phase at `D = 2` by definition. It reuses `HashCircuit.Skip`'s alternating rounds (`Skip.alt`,
`altFamily`) and one-move phases.

Message order (`MaskedFieldSkip::prove`, `rows_of`):

| Move | Sender | Value |
|---|---|---|
| `ρ ∈ K^n` | verifier | zerocheck point |
| skip message | prover | `(D − 1)(w − 1)` masked values |
| `r ∈ K` | verifier | skip challenge |
| round `i` | prover, then verifier | `D` masked coefficients, then `s_i` |
| terminal | prover | `k` masked operand claims |
| `u ∈ K^k` | verifier | batching scalars of the opening row |

The phase is followed by prover moves `R` without challenges (`spec`: none).

Events, charged at their challenges (`FieldSkip.soundness` on the unmasked transcript `sent − pad`,
the relation read from the context so that a merged relation may depend on `γ`): the `ρ` event
(degree `n`, multilinear in `ρ`), the `r` event (degree `D(w − 1)`), round `i`'s event (degree
`D + 1`), the `u` event (degree `1` in `u`). The errors sum to
`n/|K| + D(w − 1)/|K| + (D + 1)n/|K| + 1/|K|` (`error_sum`).
-/

namespace GordieHowe.BatchedZerocheck

open IOP GKR.Schedule Sumcheck.FieldSkip
open HashCircuit.Skip (alt altValues altChallenge altIndex altChallenge_val altChallenge_type
  altIndex_altChallenge altValues_snd altValues_fst_congr altValues_snd_congr oneMsg oneChal
  altFamily altFamily_fst inhabitedAppend fintypeAppend alt_inhabited alt_fintype alt_decidableEq
  alt_nonempty card_filter_cast_le update_agrees)
open scoped NNReal

/-! ### The phase -/

variable (K : Type) (e D n k : ℕ) {mR : ℕ} (R : ProtocolSpec mR)

/-- The terminal claims, the batching scalars `u` and the prover moves `R` after them. -/
abbrev Tail := one .P_to_V (Fin k → K) ++ (one .V_to_P (Fin k → K) ++ R)

/-- **The batch phase followed by `R`**: `ρ`, the skip message of `e` values, `r`, the `n` sumcheck
rounds of `D` coefficients, the `k` terminal claims, `u`, then the moves `R`, which have no
challenge. -/
abbrev phase : ProtocolSpec (1 + (1 + (1 + (roundLength n + (1 + (1 + mR)))))) :=
  one .V_to_P (Fin n → K) ++ (one .P_to_V (Fin e → K) ++
    (one .V_to_P K ++ (alt (Fin D → K) K n ++ Tail K k R)))

/-- **The batch phase** (`BatchKernel::reduce`): the phase with no moves after `u`. -/
abbrev spec := phase K e D n k empty

instance phase_inhabited [Field K] [∀ i, Inhabited (R.Type i)] :
    ∀ i, Inhabited ((phase K e D n k R).Type i) := by
  letI : Inhabited K := ⟨0⟩
  exact @inhabitedAppend _ _ _ _ (fun i => one_inhabited i)
    (@inhabitedAppend _ _ _ _ (fun i => one_inhabited i)
      (@inhabitedAppend _ _ _ _ (fun i => one_inhabited i)
        (@inhabitedAppend _ _ _ _ (alt_inhabited _ _ n)
          (@inhabitedAppend _ _ _ _ (fun i => one_inhabited i)
            (@inhabitedAppend _ _ _ _ (fun i => one_inhabited i) inferInstance)))))

instance phase_fintype [Fintype K] [∀ i : R.ChallengeIdx, Fintype (R.Challenge i)] :
    ∀ i : (phase K e D n k R).ChallengeIdx, Fintype ((phase K e D n k R).Challenge i) :=
  @fintypeAppend _ _ _ _ one_fintype
    (@fintypeAppend _ _ _ _ one_fintype
      (@fintypeAppend _ _ _ _ one_fintype
        (@fintypeAppend _ _ _ _ (alt_fintype _ _ n)
          (@fintypeAppend _ _ _ _ one_fintype
            (@fintypeAppend _ _ _ _ one_fintype inferInstance)))))

instance phase_decidableEq [DecidableEq K]
    [∀ i : R.ChallengeIdx, DecidableEq (R.Challenge i)] :
    ∀ i : (phase K e D n k R).ChallengeIdx, DecidableEq ((phase K e D n k R).Challenge i) :=
  @ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq
    (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq
      (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq
        (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ (alt_decidableEq _ _ n)
          (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq
            (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq
              inferInstance)))))

instance phase_nonempty [Nonempty K] [∀ i : R.ChallengeIdx, Nonempty (R.Challenge i)] :
    ∀ i : (phase K e D n k R).ChallengeIdx, Nonempty ((phase K e D n k R).Challenge i) :=
  @ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty
    (@ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty
      (@ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty
        (@ProtocolSpec.append_challenge_nonempty _ _ _ _ (alt_nonempty _ _ n)
          (@ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty
            (@ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty inferInstance)))))

/-- A complete transcript of the phase followed by `R`. -/
abbrev Full :=
  (phase K e D n k R).Transcript (Fin.last (1 + (1 + (1 + (roundLength n + (1 + (1 + mR)))))))

variable {K e D n k R}

/-- `ρ`. -/
def rho (tr : Full K e D n k R) : Fin n → K := oneValue tr.left
/-- The skip message. -/
def skipMsg (tr : Full K e D n k R) : Fin e → K := oneValue tr.right.left
/-- `r`. -/
def rChal (tr : Full K e D n k R) : K := oneValue tr.right.right.left
/-- The rounds' coefficient messages and challenges. -/
def roundVals (tr : Full K e D n k R) : Fin n → (Fin D → K) × K :=
  altValues _ _ n tr.right.right.right.left
/-- The terminal claims. -/
def terminalMsg (tr : Full K e D n k R) : Fin k → K := oneValue tr.right.right.right.right.left
/-- `u`. -/
def uChal (tr : Full K e D n k R) : Fin k → K :=
  oneValue tr.right.right.right.right.right.left
/-- The moves of `R`. -/
def tailOf (tr : Full K e D n k R) : R.Transcript (Fin.last mR) :=
  tr.right.right.right.right.right.right

/-- The challenges of a complete transcript, as `FieldSkip` reads them. -/
def challenges (tr : Full K e D n k R) : Challenges K n k :=
  ⟨rho tr, rChal tr, fun i => (roundVals tr i).2, uChal tr⟩

/-- The sent prover messages of a complete transcript, the skip message read at the skip domain's
`(D − 1)(w − 1)` points (`he`). -/
def messages {w : ℕ} (he : (D - 1) * (w - 1) = e) (tr : Full K e D n k R) : Transcript K w D n k :=
  ⟨fun i => skipMsg tr (Fin.cast he i), fun i => (roundVals tr i).1, terminalMsg tr⟩

/-- **The unmasked transcript** `sent − pad` for message pads `p` (`MaskedFieldSkip::message`). -/
def unmaskBy [Field K] {w : ℕ} (p tr : Transcript K w D n k) : Transcript K w D n k :=
  ⟨tr.skip - p.skip, tr.rounds - p.rounds, tr.terminal - p.terminal⟩

/-! ### Challenge positions -/

variable (K e D n k R)

/-- The move of `ρ`. -/
def idxRho : (phase K e D n k R).ChallengeIdx := ProtocolSpec.ChallengeIdx.inl ⟨0, rfl⟩
/-- The move of `r`. -/
def idxR : (phase K e D n k R).ChallengeIdx :=
  ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr
    (ProtocolSpec.ChallengeIdx.inl ⟨0, rfl⟩))
/-- The move of `s_j`. -/
def idxS (j : Fin n) : (phase K e D n k R).ChallengeIdx :=
  ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr
    (ProtocolSpec.ChallengeIdx.inl (altChallenge (Fin D → K) K n j))))
/-- The move of `u`. -/
def idxU : (phase K e D n k R).ChallengeIdx :=
  ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr
    (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr
      (ProtocolSpec.ChallengeIdx.inl ⟨0, rfl⟩)))))

/-- The verifier moves of the phase: `ρ`, `r`, the `s_j` and `u`. -/
def index [IsEmpty R.ChallengeIdx] :
    (phase K e D n k R).ChallengeIdx ≃ Unit ⊕ (Unit ⊕ (Fin n ⊕ Unit)) :=
  ProtocolSpec.challengeIdxEquiv.trans (Equiv.sumCongr (verifierIndex (Fin n → K))
    ((skipProver _ _).trans (ProtocolSpec.challengeIdxEquiv.trans
      (Equiv.sumCongr (verifierIndex K) (ProtocolSpec.challengeIdxEquiv.trans
        (Equiv.sumCongr (altIndex (Fin D → K) K n)
          ((skipProver _ _).trans (ProtocolSpec.challengeIdxEquiv.trans
            ((Equiv.sumCongr (verifierIndex (Fin k → K)) (Equiv.equivEmpty _)).trans
              (Equiv.sumEmpty _ _))))))))))

theorem index_idxRho [IsEmpty R.ChallengeIdx] :
    index K e D n k R (idxRho K e D n k R) = .inl () := rfl

theorem index_idxR [IsEmpty R.ChallengeIdx] :
    index K e D n k R (idxR K e D n k R) = .inr (.inl ()) := rfl

theorem index_idxS [IsEmpty R.ChallengeIdx] (j : Fin n) :
    index K e D n k R (idxS K e D n k R j) = .inr (.inr (.inl j)) := by
  simp only [index, idxS, Equiv.trans_apply, ProtocolSpec.challengeIdxEquiv_inl,
    ProtocolSpec.challengeIdxEquiv_inr, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    skipProver_inr, altIndex_altChallenge]

theorem index_idxU [IsEmpty R.ChallengeIdx] :
    index K e D n k R (idxU K e D n k R) = .inr (.inr (.inr ())) := by
  simp only [index, idxU, Equiv.trans_apply,
    ProtocolSpec.challengeIdxEquiv_inr, Equiv.sumCongr_apply, Sum.map_inr, skipProver_inr]

/-- Every verifier move is one of `ρ`, `r`, an `s_j` or `u`. -/
theorem challengeIdx_cases [IsEmpty R.ChallengeIdx] (i : (phase K e D n k R).ChallengeIdx) :
    i = idxRho K e D n k R ∨ i = idxR K e D n k R ∨ (∃ j, i = idxS K e D n k R j) ∨
      i = idxU K e D n k R := by
  rcases h : index K e D n k R i with u | u | j | u
  · exact Or.inl ((index K e D n k R).injective (h.trans (index_idxRho K e D n k R).symm))
  · exact Or.inr (Or.inl ((index K e D n k R).injective (h.trans (index_idxR K e D n k R).symm)))
  · exact Or.inr (Or.inr (Or.inl
      ⟨j, (index K e D n k R).injective (h.trans (index_idxS K e D n k R j).symm)⟩))
  · exact Or.inr (Or.inr (Or.inr
      ((index K e D n k R).injective (h.trans (index_idxU K e D n k R).symm))))

theorem idxRho_val : (idxRho K e D n k R).1.val = 0 := rfl
theorem idxR_val : (idxR K e D n k R).1.val = 2 := rfl
theorem idxS_val (j : Fin n) : (idxS K e D n k R j).1.val = 3 + (2 * j.val + 1) := by
  change 1 + (1 + (1 + (altChallenge (Fin D → K) K n j).1.val)) = _
  rw [altChallenge_val]
  omega
theorem idxU_val : (idxU K e D n k R).1.val = 3 + (roundLength n + 1) := by
  change 1 + (1 + (1 + (roundLength n + (1 + 0)))) = _
  omega

theorem idxRho_type : (phase K e D n k R).Challenge (idxRho K e D n k R) = (Fin n → K) := rfl
theorem idxR_type : (phase K e D n k R).Challenge (idxR K e D n k R) = K := rfl
theorem idxS_type (j : Fin n) : (phase K e D n k R).Challenge (idxS K e D n k R j) = K := by
  rw [idxS, ProtocolSpec.append_Challenge_inr, ProtocolSpec.append_Challenge_inr,
    ProtocolSpec.append_Challenge_inr, ProtocolSpec.append_Challenge_inl, altChallenge_type]
theorem idxU_type : (phase K e D n k R).Challenge (idxU K e D n k R) = (Fin k → K) := by
  rw [idxU, ProtocolSpec.append_Challenge_inr, ProtocolSpec.append_Challenge_inr,
    ProtocolSpec.append_Challenge_inr, ProtocolSpec.append_Challenge_inr,
    ProtocolSpec.append_Challenge_inr]
  rfl

variable {K e D n k R}

/-! ### Reading the challenges -/

theorem rho_eq (tr : Full K e D n k R) :
    rho tr = cast (idxRho_type K e D n k R) (tr (idxRho K e D n k R).1) := rfl

theorem rChal_eq (tr : Full K e D n k R) :
    rChal tr = cast (idxR_type K e D n k R) (tr (idxR K e D n k R).1) := by
  simp only [rChal, oneValue, ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right,
    ProtocolSpec.Transcript.fst, ProtocolSpec.Transcript.snd, cast_cast]
  rfl

theorem roundVals_snd_eq (tr : Full K e D n k R) (j : Fin n) :
    (roundVals tr j).2 = cast (idxS_type K e D n k R j) (tr (idxS K e D n k R j).1) := by
  rw [roundVals, altValues_snd]
  simp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right,
    ProtocolSpec.Transcript.fst, ProtocolSpec.Transcript.snd, cast_cast]
  rfl

theorem uChal_eq (tr : Full K e D n k R) :
    uChal tr = cast (idxU_type K e D n k R) (tr (idxU K e D n k R).1) := by
  simp only [uChal, oneValue, ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right,
    ProtocolSpec.Transcript.fst, ProtocolSpec.Transcript.snd, cast_cast]
  rfl

/-! ### Which entries each value reads -/

section Congr

variable {tr tr' : Full K e D n k R}

theorem rho_congr (h : ∀ j, j.val ≤ 0 → tr j = tr' j) : rho tr = rho tr' := by
  unfold rho oneValue
  exact left_agrees tr tr' 0 h _ le_rfl

theorem skipMsg_congr (h : ∀ j, j.val ≤ 1 → tr j = tr' j) : skipMsg tr = skipMsg tr' := by
  unfold skipMsg oneValue
  exact left_agrees tr.right tr'.right 0 (right_agrees tr tr' 0 h) _ le_rfl

/-- The entries after the first three moves agree through `m` when the transcripts agree
through `3 + m`. -/
theorem rest_agrees {m : ℕ} (h : ∀ j, j.val ≤ 3 + m → tr j = tr' j) :
    ∀ j, j.val ≤ m → tr.right.right.right j = tr'.right.right.right j :=
  right_agrees _ _ m (right_agrees _ _ (1 + m) (right_agrees tr tr' (1 + (1 + m))
    fun j hj => h j (by omega)))

theorem rChal_congr (h : ∀ j, j.val ≤ 2 → tr j = tr' j) : rChal tr = rChal tr' := by
  unfold rChal oneValue
  exact left_agrees tr.right.right tr'.right.right 0
    (right_agrees _ _ 0 (right_agrees tr tr' 1 h)) _ le_rfl

theorem roundVals_fst_congr (l : Fin n) (h : ∀ j, j.val ≤ 3 + 2 * l.val → tr j = tr' j) :
    (roundVals tr l).1 = (roundVals tr' l).1 :=
  altValues_fst_congr _ _ n l _ _ (left_agrees _ _ (2 * l.val) (rest_agrees h))

theorem roundVals_snd_congr (l : Fin n) (h : ∀ j, j.val ≤ 3 + (2 * l.val + 1) → tr j = tr' j) :
    (roundVals tr l).2 = (roundVals tr' l).2 :=
  altValues_snd_congr _ _ n l _ _ (left_agrees _ _ (2 * l.val + 1) (rest_agrees h))

theorem terminalMsg_congr (h : ∀ j, j.val ≤ 3 + roundLength n → tr j = tr' j) :
    terminalMsg tr = terminalMsg tr' := by
  unfold terminalMsg oneValue
  exact left_agrees _ _ 0 (right_agrees _ _ 0 (rest_agrees (m := roundLength n + 0) h))
    _ le_rfl

theorem uChal_congr (h : ∀ j, j.val ≤ 3 + (roundLength n + 1) → tr j = tr' j) :
    uChal tr = uChal tr' := by
  unfold uChal oneValue
  exact left_agrees _ _ 0 (right_agrees _ _ 0 (right_agrees _ _ 1
    (rest_agrees (m := roundLength n + 1) h))) _ le_rfl

end Congr

/-! ### The events -/

variable [Field K] [NeZero D] [IsEmpty R.ChallengeIdx] {w : ℕ} (he : (D - 1) * (w - 1) = e)
  {Ctx : Type} (rel : Ctx → Relation K k D) (dom : SkipPoints K w D) (ops : Ctx → Operands K w n k)
  (pad : Ctx → Transcript K w D n k)

/-- The event at each verifier move, on the unmasked transcript `sent − pad`. -/
def bad (i : (phase K e D n k R).ChallengeIdx) (c : Ctx) (tr : Full K e D n k R) : Prop :=
  Sum.elim (fun _ => (rhoEvent (rel c) (ops c)).BadAt (rho tr))
    (Sum.elim (fun _ => (rEvent (rel c) (ops c) dom (rho tr)
        (unmaskBy (pad c) (messages he tr)).skip).BadAt (rChal tr))
      (Sum.elim (fun j => (roundEvent (rel c) (ops c) dom (rho tr) (rChal tr)
          (unmaskBy (pad c) (messages he tr)).skip (unmaskBy (pad c) (messages he tr)).rounds
          (challenges tr).s j).BadAt ((challenges tr).s j))
        (fun _ => (uEvent (ops c) dom (challenges tr).s (rChal tr)
          (unmaskBy (pad c) (messages he tr)).terminal).BadAt (uChal tr))))
    (index K e D n k R i)

variable {he rel dom ops pad}

theorem bad_idxRho {c : Ctx} {tr : Full K e D n k R} :
    bad he rel dom ops pad (idxRho K e D n k R) c tr ↔
      (rhoEvent (rel c) (ops c)).BadAt (rho tr) := by
  simp only [bad, index_idxRho, Sum.elim_inl]

theorem bad_idxR {c : Ctx} {tr : Full K e D n k R} :
    bad he rel dom ops pad (idxR K e D n k R) c tr ↔
      (rEvent (rel c) (ops c) dom (rho tr)
        (unmaskBy (pad c) (messages he tr)).skip).BadAt (rChal tr) := by
  simp only [bad, index_idxR, Sum.elim_inl, Sum.elim_inr]

theorem bad_idxS {c : Ctx} {tr : Full K e D n k R} (j : Fin n) :
    bad he rel dom ops pad (idxS K e D n k R j) c tr ↔
      (roundEvent (rel c) (ops c) dom (rho tr) (rChal tr)
        (unmaskBy (pad c) (messages he tr)).skip (unmaskBy (pad c) (messages he tr)).rounds
        (challenges tr).s j).BadAt ((challenges tr).s j) := by
  simp only [bad, index_idxS, Sum.elim_inl, Sum.elim_inr]

theorem bad_idxU {c : Ctx} {tr : Full K e D n k R} :
    bad he rel dom ops pad (idxU K e D n k R) c tr ↔
      (uEvent (ops c) dom (challenges tr).s (rChal tr)
        (unmaskBy (pad c) (messages he tr)).terminal).BadAt (uChal tr) := by
  simp only [bad, index_idxU, Sum.elim_inr]

/-- **Causality.** The event at each move reads only the entries through that move. -/
theorem causal : TranscriptEventReduction.Causal (phase K e D n k R) (bad he rel dom ops pad) := by
  intro i c tr tr' h
  rcases challengeIdx_cases K e D n k R i with rfl | rfl | ⟨j, rfl⟩ | rfl
  · rw [idxRho_val] at h
    rw [bad_idxRho, bad_idxRho, rho_congr h]
  · rw [idxR_val] at h
    have hsk : (unmaskBy (pad c) (messages he tr)).skip = (unmaskBy (pad c) (messages he tr')).skip := by
      simp only [unmaskBy, messages, skipMsg_congr fun k hk => h k (by omega)]
    rw [bad_idxR, bad_idxR, rho_congr fun k hk => h k (by omega), hsk, rChal_congr h]
  · rw [idxS_val] at h
    have hsk : (unmaskBy (pad c) (messages he tr)).skip = (unmaskBy (pad c) (messages he tr')).skip := by
      simp only [unmaskBy, messages, skipMsg_congr fun k hk => h k (by omega)]
    rw [bad_idxS, bad_idxS, rho_congr fun k hk => h k (by omega),
      rChal_congr fun k hk => h k (by omega), hsk]
    have hs : (challenges tr).s j = (challenges tr').s j := roundVals_snd_congr j h
    rw [hs]
    refine roundEvent_badAt_congr (rel c) (ops c) dom (fun l hl => ?_)
      (fun v hv => roundVals_snd_congr v fun k hk => h k ?_) _
    · have : l.val ≤ j.val := hl
      change (roundVals tr l).1 - (pad c).rounds l = (roundVals tr' l).1 - (pad c).rounds l
      rw [roundVals_fst_congr l fun k hk => h k (by omega)]
    · have : v.val < j.val := hv
      omega
  · rw [idxU_val] at h
    have hs : (challenges tr).s = (challenges tr').s := by
      funext l
      exact roundVals_snd_congr l fun k hk => h k (by
        have := l.isLt
        simp only [roundLength_eq] at hk ⊢
        omega)
    have hterm : (unmaskBy (pad c) (messages he tr)).terminal =
        (unmaskBy (pad c) (messages he tr')).terminal := by
      simp only [unmaskBy, messages, terminalMsg_congr fun k hk => h k (by omega)]
    rw [bad_idxU, bad_idxU, hs, rChal_congr fun k hk => h k (by omega), hterm, uChal_congr h]

/-! ### Counting -/

variable (K e D n k R)

/-- The error of each move at skip width `w`: `n/|K|` at `ρ`, `D(w − 1)/|K|` at `r`, `(D + 1)/|K|`
at each `s_j`, `1/|K|` at `u`. -/
noncomputable def error [Fintype K] (w : ℕ) (i : (phase K e D n k R).ChallengeIdx) : ℝ≥0 :=
  Sum.elim (fun _ => (n : ℝ≥0) / Fintype.card K)
    (Sum.elim (fun _ => ((D * (w - 1) : ℕ) : ℝ≥0) / Fintype.card K)
      (Sum.elim (fun _ => ((D + 1 : ℕ) : ℝ≥0) / Fintype.card K)
        (fun _ => (1 : ℝ≥0) / Fintype.card K)))
    (index K e D n k R i)

omit [Field K] [NeZero D] in
/-- **The phase's total error.** -/
theorem error_sum [Fintype K] (w : ℕ) :
    ∑ i, error K e D n k R w i = (n : ℝ≥0) / Fintype.card K +
      ((D * (w - 1) : ℕ) : ℝ≥0) / Fintype.card K + ((D + 1 : ℕ) : ℝ≥0) * n / Fintype.card K +
        1 / Fintype.card K := by
  rw [← (index K e D n k R).symm.sum_comp]
  simp only [error, Equiv.apply_symm_apply, Fintype.sum_sum_type, Finset.univ_unique,
    Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Finset.card_singleton,
    Fintype.card_fin, nsmul_eq_mul]
  ring

variable {K e D n k R}

/-- A complete transcript with the challenge of move `i` replaced by `x`. -/
def upd (tr : Full K e D n k R) (i : (phase K e D n k R).ChallengeIdx)
    (x : (phase K e D n k R).Challenge i) : Full K e D n k R :=
  Function.update tr i.1 x

omit [Field K] [NeZero D] [IsEmpty R.ChallengeIdx] in
/-- A replaced transcript agrees with the original before the replaced move. -/
theorem upd_agrees (tr : Full K e D n k R) (i : (phase K e D n k R).ChallengeIdx)
    (x : (phase K e D n k R).Challenge i) {l : ℕ} (hl : l < i.1.val) :
    ∀ j, j.val ≤ l → upd tr i x j = tr j :=
  update_agrees tr i.1 x hl

variable (tr : Full K e D n k R)

omit [Field K] [NeZero D] [IsEmpty R.ChallengeIdx] in
theorem rho_upd (x : (phase K e D n k R).Challenge (idxRho K e D n k R)) :
    rho (upd tr (idxRho K e D n k R) x) = cast (idxRho_type K e D n k R) x :=
  (rho_eq _).trans (congrArg _ (Function.update_self _ _ _))

omit [Field K] [NeZero D] [IsEmpty R.ChallengeIdx] in
theorem rChal_upd (x : (phase K e D n k R).Challenge (idxR K e D n k R)) :
    rChal (upd tr (idxR K e D n k R) x) = cast (idxR_type K e D n k R) x :=
  (rChal_eq _).trans (congrArg _ (Function.update_self _ _ _))

omit [Field K] [NeZero D] [IsEmpty R.ChallengeIdx] in
theorem roundVals_snd_upd (j : Fin n) (x : (phase K e D n k R).Challenge (idxS K e D n k R j)) :
    (roundVals (upd tr (idxS K e D n k R j) x) j).2 = cast (idxS_type K e D n k R j) x :=
  (roundVals_snd_eq _ j).trans (congrArg _ (Function.update_self _ _ _))

omit [Field K] [NeZero D] [IsEmpty R.ChallengeIdx] in
theorem uChal_upd (x : (phase K e D n k R).Challenge (idxU K e D n k R)) :
    uChal (upd tr (idxU K e D n k R) x) = cast (idxU_type K e D n k R) x :=
  (uChal_eq _).trans (congrArg _ (Function.update_self _ _ _))

variable {tr}

open Classical in
/-- **The count at each move.** Replacing the challenge of move `i` in any complete transcript
makes that move's event true for at most an `error i` fraction of values. -/
theorem count [Fintype K] [∀ i : R.ChallengeIdx, Fintype (R.Challenge i)] (c : Ctx)
    (i : (phase K e D n k R).ChallengeIdx) (tr : Full K e D n k R) :
    ((Finset.univ.filter fun x : (phase K e D n k R).Challenge i =>
        bad he rel dom ops pad i c (Function.update tr i.1 x)).card : ℝ≥0) ≤
      error K e D n k R w i * Fintype.card ((phase K e D n k R).Challenge i) := by
  change ((Finset.univ.filter fun x => bad he rel dom ops pad i c (upd tr i x)).card : ℝ≥0) ≤ _
  rcases challengeIdx_cases K e D n k R i with rfl | rfl | ⟨j, rfl⟩ | rfl
  · have hx : ∀ x : (phase K e D n k R).Challenge (idxRho K e D n k R),
        bad he rel dom ops pad (idxRho K e D n k R) c (upd tr (idxRho K e D n k R) x) ↔
          (rhoEvent (rel c) (ops c)).BadAt (cast (idxRho_type K e D n k R) x) := by
      intro x
      rw [bad_idxRho, rho_upd]
    rw [Finset.filter_congr fun x _ => hx x]
    refine card_filter_cast_le (idxRho_type K e D n k R) _ ?_
    have h := (rhoEvent (rel c) (ops c)).card_badAt_le_nnreal
    rw [rhoEvent_deg] at h
    simpa only [error, index_idxRho, Sum.elim_inl] using h
  · have hag := upd_agrees tr (idxR K e D n k R)
    have hx : ∀ x : (phase K e D n k R).Challenge (idxR K e D n k R),
        bad he rel dom ops pad (idxR K e D n k R) c (upd tr (idxR K e D n k R) x) ↔
          (rEvent (rel c) (ops c) dom (rho tr) (unmaskBy (pad c) (messages he tr)).skip).BadAt
            (cast (idxR_type K e D n k R) x) := by
      intro x
      have hsk : (unmaskBy (pad c) (messages he (upd tr (idxR K e D n k R) x))).skip =
          (unmaskBy (pad c) (messages he tr)).skip := by
        simp only [unmaskBy, messages, skipMsg_congr (hag x (by rw [idxR_val]; omega))]
      rw [bad_idxR, rho_congr (hag x (by rw [idxR_val]; omega)), hsk, rChal_upd]
    rw [Finset.filter_congr fun x _ => hx x]
    refine card_filter_cast_le (idxR_type K e D n k R) _ ?_
    simpa only [error, index_idxR, Sum.elim_inl, Sum.elim_inr, rEvent_deg] using
      ChallengeEvent.card_filter_badAt_le
        (rEvent (rel c) (ops c) dom (rho tr) (unmaskBy (pad c) (messages he tr)).skip)
  · have hag := upd_agrees tr (idxS K e D n k R j)
    have hv : (idxS K e D n k R j).1.val = 3 + (2 * j.val + 1) := idxS_val K e D n k R j
    have hx : ∀ x : (phase K e D n k R).Challenge (idxS K e D n k R j),
        bad he rel dom ops pad (idxS K e D n k R j) c (upd tr (idxS K e D n k R j) x) ↔
          (roundEvent (rel c) (ops c) dom (rho tr) (rChal tr)
            (unmaskBy (pad c) (messages he tr)).skip (unmaskBy (pad c) (messages he tr)).rounds
            (challenges tr).s j).BadAt (cast (idxS_type K e D n k R j) x) := by
      intro x
      have hsk : (unmaskBy (pad c) (messages he (upd tr (idxS K e D n k R j) x))).skip =
          (unmaskBy (pad c) (messages he tr)).skip := by
        simp only [unmaskBy, messages, skipMsg_congr (hag x (by omega))]
      rw [bad_idxS, rho_congr (hag x (by omega)), rChal_congr (hag x (by omega)), hsk]
      change (roundEvent (rel c) (ops c) dom (rho tr) (rChal tr) _ _ _ j).BadAt
        (roundVals (upd tr (idxS K e D n k R j) x) j).2 ↔ _
      rw [roundVals_snd_upd]
      refine roundEvent_badAt_congr (rel c) (ops c) dom (fun l hl => ?_)
        (fun v hlt => roundVals_snd_congr v (hag x ?_)) _
      · have : l.val ≤ j.val := hl
        change (roundVals (upd tr (idxS K e D n k R j) x) l).1 - (pad c).rounds l =
          (roundVals tr l).1 - (pad c).rounds l
        rw [roundVals_fst_congr l (hag x (by omega))]
      · have : v.val < j.val := hlt
        omega
    rw [Finset.filter_congr fun x _ => hx x]
    refine card_filter_cast_le (idxS_type K e D n k R j) _ ?_
    simpa only [error, index_idxS, Sum.elim_inl, Sum.elim_inr, roundEvent_deg] using
      ChallengeEvent.card_filter_badAt_le
        (roundEvent (rel c) (ops c) dom (rho tr) (rChal tr)
          (unmaskBy (pad c) (messages he tr)).skip (unmaskBy (pad c) (messages he tr)).rounds
          (challenges tr).s j)
  · have hag := upd_agrees tr (idxU K e D n k R)
    have hv : (idxU K e D n k R).1.val = 3 + (roundLength n + 1) := idxU_val K e D n k R
    have hx : ∀ x : (phase K e D n k R).Challenge (idxU K e D n k R),
        bad he rel dom ops pad (idxU K e D n k R) c (upd tr (idxU K e D n k R) x) ↔
          (uEvent (ops c) dom (challenges tr).s (rChal tr)
            (unmaskBy (pad c) (messages he tr)).terminal).BadAt (cast (idxU_type K e D n k R) x) := by
      intro x
      have hs : (challenges (upd tr (idxU K e D n k R) x)).s = (challenges tr).s := by
        funext l
        exact roundVals_snd_congr l (hag x (by
          have := l.isLt
          simp only [roundLength_eq] at hv ⊢
          omega))
      have hterm : (unmaskBy (pad c) (messages he (upd tr (idxU K e D n k R) x))).terminal =
          (unmaskBy (pad c) (messages he tr)).terminal := by
        simp only [unmaskBy, messages, terminalMsg_congr (hag x (by omega))]
      rw [bad_idxU, hs, rChal_congr (hag x (by omega)), hterm, uChal_upd]
    rw [Finset.filter_congr fun x _ => hx x]
    refine card_filter_cast_le (idxU_type K e D n k R) _ ?_
    simpa only [error, index_idxU, Sum.elim_inr, uEvent_deg, Nat.cast_one] using
      (uEvent (ops c) dom (challenges tr).s (rChal tr)
        (unmaskBy (pad c) (messages he tr)).terminal).card_badAt_le_nnreal

/-! ### The reduction -/

/-- **Deterministic soundness of the phase.** Output claims that give the verifier's checks on the
unmasked transcript give the batch or an event at some move. -/
theorem sound {A : Ctx → Prop} {T : Ctx → Full K e D n k R → Prop}
    (hT : ∀ c tr, T c tr → A c ∧
      Accepts (rel c) (ops c) dom (challenges tr) (unmaskBy (pad c) (messages he tr)))
    (c : Ctx) (tr : Full K e D n k R) (h : T c tr) :
    (Holds (rel c) (ops c) ∧ A c) ∨ ∃ i, bad he rel dom ops pad i c tr := by
  obtain ⟨hA, hacc⟩ := hT c tr h
  rcases soundness (rel c) (ops c) dom hacc with h | h | h | ⟨j, h⟩ | h
  · exact Or.inl ⟨h, hA⟩
  · exact Or.inr ⟨idxRho K e D n k R, bad_idxRho.mpr h⟩
  · exact Or.inr ⟨idxR K e D n k R, bad_idxR.mpr h⟩
  · exact Or.inr ⟨idxS K e D n k R j, (bad_idxS j).mpr h⟩
  · exact Or.inr ⟨idxU K e D n k R, bad_idxU.mpr h⟩

variable [Fintype K] [∀ i : R.ChallengeIdx, Fintype (R.Challenge i)] [∀ i, Inhabited (R.Type i)]
  (he rel dom ops pad)

/-- **The phase as a claim reduction.** Input claim: the relation `rel c` on the committed operands
`ops c`, and `A c`. Output claim: `T c tr`, which must give `A c` and the verifier's checks on the
transcript unmasked by the message pads `pad c` (`hT`). Errors: `error`. -/
noncomputable def reduction (A : Ctx → Prop) (T : Ctx → Full K e D n k R → Prop)
    (hT : ∀ c tr, T c tr → A c ∧
      Accepts (rel c) (ops c) dom (challenges tr) (unmaskBy (pad c) (messages he tr))) :
    ClaimReduction (phase K e D n k R) Ctx (error K e D n k R w) :=
  TranscriptEventReduction.reduction (phase K e D n k R) (bad he rel dom ops pad) causal
    (fun c => Holds (rel c) (ops c) ∧ A c) T (error K e D n k R w)
    (fun c i tr => count c i tr) (sound hT)

/-! ### The honest causal phase -/

section Honest

variable {K : Type} [Field K] {e D w n k mR : ℕ} {R : ProtocolSpec mR}
  (he : (D - 1) * (w - 1) = e)

/-- **The honest phase followed by `R`.** `hon` is the honest transcript and `tail` the honest moves
of `R`, as functions of the challenges; each prover move evaluates them at the challenges already
drawn, the rest zero. The skip message is read at the skip domain's points (`he`). -/
def phaseFamily (hon : Challenges K n k → Transcript K w D n k)
    (tail : Challenges K n k → CausalTranscript R) : CausalTranscript (phase K e D n k R) :=
  (oneChal (Fin n → K)).append fun t1 =>
    (oneMsg fun i => (hon ⟨t1 ⟨0, by decide⟩, 0, 0, 0⟩).skip (Fin.cast he.symm i)).append fun _ =>
      (oneChal K).append fun t3 =>
        (altFamily n fun s j => (hon ⟨t1 ⟨0, by decide⟩, t3 ⟨0, by decide⟩, s, 0⟩).rounds j).append
          fun t4 =>
          (oneMsg (hon ⟨t1 ⟨0, by decide⟩, t3 ⟨0, by decide⟩,
            fun j => (altValues (Fin D → K) K n t4 j).2, 0⟩).terminal).append fun _ =>
            (oneChal (Fin k → K)).append fun t6 =>
              tail ⟨t1 ⟨0, by decide⟩, t3 ⟨0, by decide⟩,
                fun j => (altValues (Fin D → K) K n t4 j).2, t6 ⟨0, by decide⟩⟩

/-- The honest transcript's skip message reads only `ρ`. -/
def SkipCausal (hon : Challenges K n k → Transcript K w D n k) : Prop :=
  ∀ c c' : Challenges K n k, c.rho = c'.rho → (hon c).skip = (hon c').skip

/-- The honest transcript's round `j` reads only `ρ`, `r` and the challenges before `j`. -/
def RoundCausal (hon : Challenges K n k → Transcript K w D n k) : Prop :=
  ∀ (c c' : Challenges K n k) (j : Fin n), c.rho = c'.rho → c.r = c'.r →
    (∀ v, v < j → c.s v = c'.s v) → (hon c).rounds j = (hon c').rounds j

/-- The honest transcript's terminal claims read only `ρ`, `r` and `s`. -/
def TerminalCausal (hon : Challenges K n k → Transcript K w D n k) : Prop :=
  ∀ c c' : Challenges K n k, c.rho = c'.rho → c.r = c'.r → c.s = c'.s →
    (hon c).terminal = (hon c').terminal

/-- The challenges of `R` in a challenge vector of the phase. -/
def tailChallenges (ch : (phase K e D n k R).Challenges) : R.Challenges :=
  ch.right.right.right.right.right.right

variable (hon : Challenges K n k → Transcript K w D n k) (tail : Challenges K n k → CausalTranscript R)
  (ch : (phase K e D n k R).Challenges)

/-- The realized transcript's reads, move by move. -/
theorem phaseFamily_reads :
    let T := (phaseFamily he hon tail).transcript ch
    let ρ := rho T
    let r := rChal T
    let s := fun j => (roundVals T j).2
    skipMsg T = (fun i => (hon ⟨ρ, 0, 0, 0⟩).skip (Fin.cast he.symm i)) ∧
      (∀ j, (roundVals T j).1 = (hon ⟨ρ, r, fun v => if v < j then s v else 0, 0⟩).rounds j) ∧
      terminalMsg T = (hon ⟨ρ, r, s, 0⟩).terminal ∧
      tailOf T = (tail ⟨ρ, r, s, uChal T⟩).transcript (tailChallenges ch) := by
  dsimp only
  simp only [phaseFamily, skipMsg, roundVals, terminalMsg, tailOf, rho, rChal, uChal,
    CausalTranscript.append_left, CausalTranscript.append_right]
  exact ⟨rfl, fun j => altFamily_fst n _ _ j, rfl, rfl⟩

variable {hon}

/-- **The sent messages are the honest transcript** at the realized transcript's own challenges,
when the honest transcript reads only the challenges drawn before each move. -/
theorem messages_phaseFamily (hskip : SkipCausal hon) (hround : RoundCausal hon)
    (hterm : TerminalCausal hon) :
    messages he ((phaseFamily he hon tail).transcript ch) =
      hon (challenges ((phaseFamily he hon tail).transcript ch)) := by
  obtain ⟨h1, h2, h3, -⟩ := phaseFamily_reads he hon tail ch
  set T := (phaseFamily he hon tail).transcript ch
  change Transcript.mk (fun i => skipMsg T (Fin.cast he i)) (fun i => (roundVals T i).1)
      (terminalMsg T) =
    ⟨(hon (challenges T)).skip, (hon (challenges T)).rounds, (hon (challenges T)).terminal⟩
  congr 1
  · funext i
    rw [h1]
    change (hon _).skip (Fin.cast he.symm (Fin.cast he i)) = _
    rw [show Fin.cast he.symm (Fin.cast he i) = i from Fin.ext rfl]
    exact congrFun (hskip ⟨rho T, 0, 0, 0⟩ (challenges T) rfl) i
  · funext j
    rw [h2 j]
    exact hround _ _ j rfl rfl fun v hv => by simp only [hv, ↓reduceIte]; rfl
  · rw [h3]
    exact hterm _ _ rfl rfl rfl

/-- **The moves of `R` are `tail`** at the realized transcript's own challenges. -/
theorem tailOf_phaseFamily :
    tailOf ((phaseFamily he hon tail).transcript ch) =
      (tail (challenges ((phaseFamily he hon tail).transcript ch))).transcript
        (tailChallenges ch) :=
  (phaseFamily_reads he hon tail ch).2.2.2

/-! ### The honest transcript is causal -/

/-- The honest transcript of `FieldSkip` reads the challenges in order. -/
theorem honest_skipCausal (Q : Relation K k D) (ops : Operands K w n k) (dom : SkipPoints K w D) :
    SkipCausal (honest Q ops dom) := by
  intro c c' h
  simp only [honest, h]

theorem honest_roundCausal (Q : Relation K k D) (ops : Operands K w n k) (dom : SkipPoints K w D) :
    RoundCausal (honest Q ops dom) := by
  intro c c' j hρ hr hs
  simp only [honest, hρ, hr, Sumcheck.EqFactoredDeg.honest_congr c'.rho _ j fun v hv => hs v hv]

theorem honest_terminalCausal (Q : Relation K k D) (ops : Operands K w n k)
    (dom : SkipPoints K w D) : TerminalCausal (honest Q ops dom) := by
  intro c c' _ hr hs
  simp only [honest, hr, hs]

/-- Adding fixed message pads keeps the skip message causal. -/
theorem SkipCausal.add {hon : Challenges K n k → Transcript K w D n k} (h : SkipCausal hon)
    (p : Transcript K w D n k) :
    SkipCausal fun c => ⟨(hon c).skip + p.skip, (hon c).rounds + p.rounds,
      (hon c).terminal + p.terminal⟩ := fun c c' hc => by
  simp only [h c c' hc]

theorem RoundCausal.add {hon : Challenges K n k → Transcript K w D n k} (h : RoundCausal hon)
    (p : Transcript K w D n k) :
    RoundCausal fun c => ⟨(hon c).skip + p.skip, (hon c).rounds + p.rounds,
      (hon c).terminal + p.terminal⟩ := fun c c' j hρ hr hs => by
  simp only [Pi.add_apply, h c c' j hρ hr hs]

theorem TerminalCausal.add {hon : Challenges K n k → Transcript K w D n k} (h : TerminalCausal hon)
    (p : Transcript K w D n k) :
    TerminalCausal fun c => ⟨(hon c).skip + p.skip, (hon c).rounds + p.rounds,
      (hon c).terminal + p.terminal⟩ := fun c c' hρ hr hs => by
  simp only [h c c' hρ hr hs]

end Honest

/-! ### The hiding law -/

section Hiding

open HashCircuit.Skip (one_ext split_ext alt_ext)

variable {K : Type} [Field K] {e D w n k mR : ℕ} {R : ProtocolSpec mR}
  (he : (D - 1) * (w - 1) = e)

omit [Field K] in
/-- A complete transcript of the phase is fixed by its challenges, its messages and the moves of
`R`. -/
theorem ext_of {tr tr' : Full K e D n k R} (hc : challenges tr = challenges tr')
    (hm : messages he tr = messages he tr') (ht : tailOf tr = tailOf tr') : tr = tr' := by
  have hρ : rho tr = rho tr' := congrArg Challenges.rho hc
  have hrc : rChal tr = rChal tr' := congrArg Challenges.r hc
  have hs : ∀ j, (roundVals tr j).2 = (roundVals tr' j).2 :=
    fun j => congrFun (congrArg Challenges.s hc) j
  have hu : uChal tr = uChal tr' := congrArg Challenges.u hc
  have hsk : skipMsg tr = skipMsg tr' := by
    funext i
    have := congrFun (congrArg Transcript.skip hm) (Fin.cast he.symm i)
    simpa [messages] using this
  have hrd : ∀ j, (roundVals tr j).1 = (roundVals tr' j).1 :=
    fun j => congrFun (congrArg Transcript.rounds hm) j
  have hte : terminalMsg tr = terminalMsg tr' := congrArg Transcript.terminal hm
  exact split_ext (one_ext hρ) (split_ext (one_ext hsk) (split_ext (one_ext hrc)
    (split_ext (alt_ext _ _ n (funext fun j => Prod.ext (hrd j) (hs j)))
      (split_ext (one_ext hte) (split_ext (one_ext hu) ht)))))

omit [Field K] in
/-- The challenges of a challenge vector of the phase. -/
def challengesOf (ch : (phase K e D n k R).Challenges) : Challenges K n k :=
  ⟨cast (idxRho_type K e D n k R) (ch (idxRho K e D n k R)),
    cast (idxR_type K e D n k R) (ch (idxR K e D n k R)),
    fun j => cast (idxS_type K e D n k R j) (ch (idxS K e D n k R j)),
    cast (idxU_type K e D n k R) (ch (idxU K e D n k R))⟩

omit [Field K] in
/-- The challenges of a realized transcript are those it was run on. -/
theorem challenges_transcript (H : CausalTranscript (phase K e D n k R))
    (ch : (phase K e D n k R).Challenges) : challenges (H.transcript ch) = challengesOf ch := by
  simp only [challenges, challengesOf, rho_eq, rChal_eq, roundVals_snd_eq, uChal_eq,
    H.challenge]

/-- Two honest phases whose honest values and moves of `R` agree at the challenges realize the
same transcript. -/
theorem phaseFamily_transcript_congr {hon hon' : Challenges K n k → Transcript K w D n k}
    {tail tail' : Challenges K n k → CausalTranscript R} (hs : SkipCausal hon)
    (hr : RoundCausal hon) (ht : TerminalCausal hon) (hs' : SkipCausal hon')
    (hr' : RoundCausal hon') (ht' : TerminalCausal hon') (ch : (phase K e D n k R).Challenges)
    (hh : hon (challengesOf ch) = hon' (challengesOf ch))
    (hv : (tail (challengesOf ch)).transcript (tailChallenges ch) =
      (tail' (challengesOf ch)).transcript (tailChallenges ch)) :
    (phaseFamily he hon tail).transcript ch = (phaseFamily he hon' tail').transcript ch := by
  refine ext_of he ?_ ?_ ?_
  · rw [challenges_transcript, challenges_transcript]
  · rw [messages_phaseFamily he _ ch hs hr ht, messages_phaseFamily he _ ch hs' hr' ht',
      challenges_transcript, challenges_transcript, hh]
  · rw [tailOf_phaseFamily, tailOf_phaseFamily, challenges_transcript, challenges_transcript, hv]

open Sumcheck.FieldSkipMasked in
/-- **The value family**: the phase sending the coordinates of `v` as its messages, whatever the
challenges, with the moves `tail`. No prover runs. -/
def valuePhase (v : FreePads K w D n k) (tail : Challenges K n k → CausalTranscript R) :
    CausalTranscript (phase K e D n k R) :=
  phaseFamily he (fun _ => ofRevealed v) tail

open Sumcheck.FieldSkipMasked in
/-- **The masked honest phase sends values computed from the challenges**: the honest transcript
`hon` (causal) sent plus free pads `φ` is the value family at the honest values plus `φ`, when the
moves of `R` agree at the challenges. -/
theorem maskedPhase_eq_value {hon : Challenges K n k → Transcript K w D n k}
    (hs : SkipCausal hon) (hr : RoundCausal hon) (ht : TerminalCausal hon)
    (φ : FreePads K w D n k) {tail tail' : Challenges K n k → CausalTranscript R}
    (ch : (phase K e D n k R).Challenges)
    (hv : (tail (challengesOf ch)).transcript (tailChallenges ch) =
      (tail' (challengesOf ch)).transcript (tailChallenges ch)) :
    (phaseFamily he (fun c => ofRevealed (revealed (hon c) + φ)) tail).transcript ch =
      (valuePhase he (revealed (hon (challengesOf ch)) + φ) tail').transcript ch :=
  phaseFamily_transcript_congr he (hs.add (ofRevealed φ)) (hr.add (ofRevealed φ))
    (ht.add (ofRevealed φ)) (fun _ _ _ => rfl) (fun _c _c' _j _ _ _ => rfl)
    (fun _c _c' _ _ _ => rfl) ch rfl hv

open Sumcheck.FieldSkipMasked in
/-- **Hiding of the phase.** For fixed challenges, the honest transcript `hon` (causal) sent plus
uniform free pads has the law of the value family under uniform values: the bijection sends the
free pads `φ` to the honest values plus `φ`. -/
theorem maskedPhase_identDistrib [Fintype K] {hon : Challenges K n k → Transcript K w D n k}
    (hs : SkipCausal hon) (hr : RoundCausal hon) (ht : TerminalCausal hon)
    {tail : Challenges K n k → CausalTranscript R} (ch : (phase K e D n k R).Challenges) :
    (fun φ => (phaseFamily he (fun c => ofRevealed (revealed (hon c) + φ)) tail).transcript ch) =ᵈ
      (fun v => (valuePhase he v tail).transcript ch) :=
  IdentDistrib.of_equiv (Equiv.addLeft (revealed (hon (challengesOf ch))))
    fun φ => maskedPhase_eq_value he hs hr ht φ ch rfl

end Hiding

end GordieHowe.BatchedZerocheck
