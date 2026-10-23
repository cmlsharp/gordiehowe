-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.CompletenessAppend

@[expose] public section

/-!
# The `m`-fold append of protocols

`ProtocolSpec.appendN m P` runs the protocols `P 0, …, P (m - 1)` (with `n i` rounds each) in
order, over `lenN m n = ∑ i, n i` rounds (`lenN_eq_sum`). It is defined by recursion on `m`
through the binary `ProtocolSpec.append`: the empty protocol for `m = 0`, `P 0` for `m = 1`, and
`P 0` followed by the append of the rest for `m + 2`. So the instance `m = 2` is the binary
append `P 0 ++ P 1` by definition (`appendN_two`), and every lemma below is proved by the
same recursion from the binary one; the dependent-type casts stay inside the binary library.

* `chIdxEquivN`: the challenge rounds of the append are the challenge rounds of its parts
  (`PartChallengeIdx`: a part and one of its challenge rounds).
* `errN`: the round errors of the parts, read on the append; `errN_apply` gives the error of
  challenge round `k` as the error of the part's round `chIdxEquivN k`, and `sum_errN` sums them.
* `ClaimProof.andN`: claim-proving phases of the parts, on a common context, in sequence prove
  the conjunction of their claims (`andN_claim`) with the parts' errors (`errN`); its verifier
  accepts when every part's verifier accepts its part of the transcript (`andN_V`).
* `Transcript.part`, `joinN`: full transcripts of the append are the families of the parts' full
  transcripts; `chN` gives each part its challenges.
* `CausalTranscript.appendN`: honest transcript families of the parts, run in sequence, on whose
  transcripts the conjunction accepts when every part accepts (`andN_V_appendN`).
-/

namespace GordieHowe.IOP

open scoped NNReal

namespace ProtocolSpec

/-! ### The protocol -/

/-- The total number of rounds of `m` protocols with `n i` rounds each. -/
def lenN : (m : ℕ) → (Fin m → ℕ) → ℕ
  | 0, _ => 0
  | 1, n => n 0
  | m + 2, n => n 0 + lenN (m + 1) (fun i => n i.succ)

theorem lenN_eq_sum : (m : ℕ) → (n : Fin m → ℕ) → lenN m n = ∑ i, n i
  | 0, _ => rfl
  | 1, n => by simp [lenN]
  | m + 2, n => by
    change n 0 + lenN (m + 1) (fun i => n i.succ) = _
    rw [lenN_eq_sum (m + 1)]
    exact (Fin.sum_univ_succ n).symm

/-- **The `m`-fold append**: the protocols `P 0, …, P (m - 1)` in order. -/
def appendN : (m : ℕ) → {n : Fin m → ℕ} → ((i : Fin m) → ProtocolSpec (n i)) →
    ProtocolSpec (lenN m n)
  | 0, _, _ => ⟨Fin.elim0, Fin.elim0⟩
  | 1, _, P => P 0
  | m + 2, _, P => P 0 ++ appendN (m + 1) fun i => P i.succ

/-- Two protocols appended `2`-fold are appended. -/
theorem appendN_two {n : Fin 2 → ℕ} (P : (i : Fin 2) → ProtocolSpec (n i)) :
    appendN 2 P = P 0 ++ P 1 :=
  rfl

/-! ### Challenge rounds -/

/-- A pair of an index in `Fin (m + 1)` and a value is a value at index `0` or a pair of an
index in `Fin m` and a value at its successor. -/
def sigmaFinSuccEquiv {m : ℕ} (α : Fin (m + 1) → Type) :
    (Σ i, α i) ≃ α 0 ⊕ Σ i : Fin m, α i.succ where
  toFun x := Fin.cases (motive := fun i => α i → α 0 ⊕ Σ i : Fin m, α i.succ) Sum.inl
    (fun j y => Sum.inr ⟨j, y⟩) x.1 x.2
  invFun := Sum.elim (fun y => ⟨0, y⟩) fun y => ⟨y.1.succ, y.2⟩
  left_inv := by
    rintro ⟨i, y⟩
    cases i using Fin.cases <;> rfl
  right_inv := by
    rintro (y | ⟨j, y⟩) <;> rfl

/-- The challenge rounds of the `m`-fold append as dependent pairs of a part and one of its
challenge rounds, by the recursion of `appendN` (`chIdxEquivN` reads them as `PartChallengeIdx`). -/
def chIdxEquivSigma : (m : ℕ) → {n : Fin m → ℕ} → (P : (i : Fin m) → ProtocolSpec (n i)) →
    (appendN m P).ChallengeIdx ≃ Σ i, (P i).ChallengeIdx
  | 0, _, _ =>
    { toFun := fun k => k.1.elim0
      invFun := fun x => x.1.elim0
      left_inv := fun k => k.1.elim0
      right_inv := fun x => x.1.elim0 }
  | 1, _, P =>
    { toFun := fun k => ⟨0, k⟩
      invFun := fun x => Fin.cases (motive := fun i => (P i).ChallengeIdx → (P 0).ChallengeIdx)
        id (fun j => j.elim0) x.1 x.2
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨i, y⟩
        cases i using Fin.cases with
        | zero => rfl
        | succ j => exact j.elim0 }
  | m + 2, _, P => challengeIdxEquiv.trans
      ((Equiv.sumCongr (Equiv.refl _) (chIdxEquivSigma (m + 1) fun i => P i.succ)).trans
        (sigmaFinSuccEquiv fun i => (P i).ChallengeIdx).symm)

/-- **A challenge round of one part of an `m`-fold append**: the part and its challenge round. -/
structure PartChallengeIdx {m : ℕ} {n : Fin m → ℕ} (P : (i : Fin m) → ProtocolSpec (n i)) where
  /-- The part. -/
  part : Fin m
  /-- The part's challenge round. -/
  idx : (P part).ChallengeIdx

/-- Challenge rounds of the parts are dependent pairs. -/
def PartChallengeIdx.equivSigma {m : ℕ} {n : Fin m → ℕ} (P : (i : Fin m) → ProtocolSpec (n i)) :
    PartChallengeIdx P ≃ Σ i, (P i).ChallengeIdx where
  toFun x := ⟨x.part, x.idx⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The challenge rounds of the `m`-fold append** are the challenge rounds of its parts. -/
def chIdxEquivN (m : ℕ) {n : Fin m → ℕ} (P : (i : Fin m) → ProtocolSpec (n i)) :
    (appendN m P).ChallengeIdx ≃ PartChallengeIdx P :=
  (chIdxEquivSigma m P).trans (PartChallengeIdx.equivSigma P).symm

/-- The challenge types of the append are finite when the parts' are. -/
@[reducible] def appendNFintype : (m : ℕ) → {n : Fin m → ℕ} → (P : (i : Fin m) → ProtocolSpec (n i)) →
    (∀ i j, Fintype ((P i).Challenge j)) → ∀ k, Fintype ((appendN m P).Challenge k)
  | 0, _, _, _ => fun k => k.1.elim0
  | 1, _, _, h => h 0
  | m + 2, _, P, h =>
    letI := h 0
    letI := appendNFintype (m + 1) (fun i => P i.succ) fun i => h i.succ
    show ∀ k, Fintype ((P 0 ++ appendN (m + 1) fun i => P i.succ).Challenge k) from
      inferInstance

instance appendN_fintype {m : ℕ} {n : Fin m → ℕ} {P : (i : Fin m) → ProtocolSpec (n i)}
    [h : ∀ i j, Fintype ((P i).Challenge j)] : ∀ k, Fintype ((appendN m P).Challenge k) :=
  appendNFintype m P h

/-- The challenge types of the append have decidable equality when the parts' do. -/
@[reducible] def appendNDecidableEq : (m : ℕ) → {n : Fin m → ℕ} →
    (P : (i : Fin m) → ProtocolSpec (n i)) →
    (∀ i j, DecidableEq ((P i).Challenge j)) → ∀ k, DecidableEq ((appendN m P).Challenge k)
  | 0, _, _, _ => fun k => k.1.elim0
  | 1, _, _, h => h 0
  | m + 2, _, P, h =>
    letI := h 0
    letI := appendNDecidableEq (m + 1) (fun i => P i.succ) fun i => h i.succ
    show ∀ k, DecidableEq ((P 0 ++ appendN (m + 1) fun i => P i.succ).Challenge k) from
      inferInstance

instance appendN_decidableEq {m : ℕ} {n : Fin m → ℕ} {P : (i : Fin m) → ProtocolSpec (n i)}
    [h : ∀ i j, DecidableEq ((P i).Challenge j)] : ∀ k, DecidableEq ((appendN m P).Challenge k) :=
  appendNDecidableEq m P h

/-- The challenge types of the append are nonempty when the parts' are. -/
theorem appendNNonempty : (m : ℕ) → {n : Fin m → ℕ} → (P : (i : Fin m) → ProtocolSpec (n i)) →
    (∀ i j, Nonempty ((P i).Challenge j)) → ∀ k, Nonempty ((appendN m P).Challenge k)
  | 0, _, _, _ => fun k => k.1.elim0
  | 1, _, _, h => h 0
  | m + 2, _, P, h =>
    haveI := h 0
    haveI := appendNNonempty (m + 1) (fun i => P i.succ) fun i => h i.succ
    show ∀ k, Nonempty ((P 0 ++ appendN (m + 1) fun i => P i.succ).Challenge k) from
      inferInstance

instance appendN_nonempty {m : ℕ} {n : Fin m → ℕ} {P : (i : Fin m) → ProtocolSpec (n i)}
    [h : ∀ i j, Nonempty ((P i).Challenge j)] : ∀ k, Nonempty ((appendN m P).Challenge k) :=
  appendNNonempty m P h

/-! ### Errors -/

/-- The round errors of the parts, read on the challenge rounds of the append (in the form
`ClaimProof.and` produces). -/
def errN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (∀ i, (P i).ChallengeIdx → ℝ≥0) → (appendN m P).ChallengeIdx → ℝ≥0
  | 0, _, _, _ => fun k => k.1.elim0
  | 1, _, _, ε => ε 0
  | m + 2, _, _, ε => appendError (ε 0) (errN (m + 1) fun i => ε i.succ)

/-- **The error of challenge round `k` of the append is the error of the part's round that runs
it.** -/
theorem errN_apply_sigma : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (ε : ∀ i, (P i).ChallengeIdx → ℝ≥0) → (k : (appendN m P).ChallengeIdx) →
    errN m ε k = ε (chIdxEquivSigma m P k).1 (chIdxEquivSigma m P k).2
  | 0, _, _, _, k => k.1.elim0
  | 1, _, _, _, _ => rfl
  | m + 2, _, P, ε, k => by
    have e : chIdxEquivSigma (m + 2) P k = (sigmaFinSuccEquiv fun i => (P i).ChallengeIdx).symm
        (Sum.map id (chIdxEquivSigma (m + 1) fun i => P i.succ) (challengeIdxEquiv k)) := rfl
    change Sum.elim (ε 0) (errN (m + 1) fun i => ε i.succ) (challengeIdxEquiv k) = _
    rw [e]
    rcases challengeIdxEquiv k with j | j
    · rfl
    · exact errN_apply_sigma (m + 1) (fun i => ε i.succ) j

/-- **The error of challenge round `k` of the append is the error of the part's round that runs
it.** -/
theorem errN_apply {m : ℕ} {n : Fin m → ℕ} {P : (i : Fin m) → ProtocolSpec (n i)}
    (ε : ∀ i, (P i).ChallengeIdx → ℝ≥0) (k : (appendN m P).ChallengeIdx) :
    errN m ε k = ε (chIdxEquivN m P k).part (chIdxEquivN m P k).idx :=
  errN_apply_sigma m ε k

/-- The errors of the append sum to the parts' summed errors. -/
theorem sum_errN {m : ℕ} {n : Fin m → ℕ} {P : (i : Fin m) → ProtocolSpec (n i)}
    (ε : ∀ i, (P i).ChallengeIdx → ℝ≥0) : ∑ k, errN m ε k = ∑ i, ∑ j, ε i j := by
  simp only [errN_apply_sigma]
  rw [Equiv.sum_comp (chIdxEquivSigma m P) (fun x => ε x.1 x.2), Fintype.sum_sigma]

/-- A bound on every part's errors bounds every error of the append. -/
theorem errN_le {m : ℕ} {n : Fin m → ℕ} {P : (i : Fin m) → ProtocolSpec (n i)}
    {ε : ∀ i, (P i).ChallengeIdx → ℝ≥0} {δ : ℝ≥0} (h : ∀ i j, ε i j ≤ δ)
    (k : (appendN m P).ChallengeIdx) : errN m ε k ≤ δ := by
  rw [errN_apply]
  exact h _ _

/-! ### Transcripts and challenges -/

/-- The parts of a full transcript of the append. -/
def Transcript.part : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (appendN m P).Transcript (Fin.last (lenN m n)) → ∀ i, (P i).Transcript (Fin.last (n i))
  | 0, _, _, _ => fun i => i.elim0
  | 1, n, P, tr => Fin.cases (motive := fun i => (P i).Transcript (Fin.last (n i))) tr
      fun i => i.elim0
  | m + 2, n, P, tr => Fin.cases (motive := fun i => (P i).Transcript (Fin.last (n i)))
      tr.left (Transcript.part (m + 1) tr.right)

/-- The full transcript of the append from full transcripts of the parts. -/
def joinN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (∀ i, (P i).Transcript (Fin.last (n i))) → (appendN m P).Transcript (Fin.last (lenN m n))
  | 0, _, _, _ => fun i => i.elim0
  | 1, _, _, trs => trs 0
  | m + 2, _, _, trs => Transcript.join (trs 0) (joinN (m + 1) fun i => trs i.succ)

@[simp] theorem part_joinN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (trs : ∀ i, (P i).Transcript (Fin.last (n i))) → Transcript.part m (joinN m trs) = trs
  | 0, _, _, _ => funext fun i => i.elim0
  | 1, _, _, _ => funext fun i => by cases i using Fin.cases with
    | zero => rfl
    | succ i => exact i.elim0
  | m + 2, _, _, trs => funext fun i => by
    cases i using Fin.cases with
    | zero => exact Transcript.left_join _ _
    | succ i =>
      change Transcript.part (m + 1) (Transcript.join (trs 0) (joinN (m + 1) fun i => trs i.succ)).right
        i = trs i.succ
      rw [Transcript.right_join, part_joinN]

/-- The challenges of each part, read from the challenges of the append. -/
def chN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (appendN m P).Challenges → ∀ i, (P i).Challenges
  | 0, _, _, _ => fun i => i.elim0
  | 1, _, P, ch => Fin.cases (motive := fun i => (P i).Challenges) ch fun i => i.elim0
  | m + 2, _, P, ch => Fin.cases (motive := fun i => (P i).Challenges) ch.left
      (chN (m + 1) ch.right)

end ProtocolSpec

open ProtocolSpec

/-- **Every circuit's relation holds** at its public input `p i` on its witness `w i`. -/
def AllHold {m : ℕ} {Pub Wit : Fin m → Type} (holds : ∀ i, Pub i → Wit i → Prop) (p : ∀ i, Pub i)
    (w : ∀ i, Wit i) : Prop :=
  ∀ i, holds i (p i) (w i)

/-! ### Claim-proving phases in sequence -/

namespace ClaimProof

variable {Ctx : Type}

/-- The phase of no rounds proving the true claim. -/
def empty (P : ProtocolSpec 0) [∀ i, Fintype (P.Challenge i)] (ε : P.ChallengeIdx → ℝ≥0) :
    ClaimProof P Ctx ε where
  claim _ := True
  V _ _ := true
  S _ _ _ := True
  start _ _ h := absurd trivial h
  next m := m.elim0
  full _ _ _ := trivial
  rbr _ i := i.1.elim0

/-- **Claim-proving phases in sequence**: the phases `B i` of the parts, on a common context,
prove the conjunction of their claims (`andN_claim`) with the parts' errors (`errN`, `errN_apply`).
The verifier accepts when every part's verifier accepts its part of the transcript (`andN_V`).
For `m = 2` it is `ClaimProof.and` by definition. -/
def andN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    [∀ i j, Fintype ((P i).Challenge j)] → {ε : ∀ i, (P i).ChallengeIdx → ℝ≥0} →
    (∀ i, ClaimProof (P i) Ctx (ε i)) → ClaimProof (appendN m P) Ctx (ProtocolSpec.errN m ε)
  | 0, _, _, _, _, _ => @empty Ctx _ (fun k => k.1.elim0) _
  | 1, _, _, _, _, B => B 0
  | m + 2, _, _, _, _, B => (B 0).and (andN (m + 1) fun i => B i.succ)

theorem andN_two {n : Fin 2 → ℕ} {P : (i : Fin 2) → ProtocolSpec (n i)}
    [∀ i j, Fintype ((P i).Challenge j)] {ε : ∀ i, (P i).ChallengeIdx → ℝ≥0}
    (B : ∀ i, ClaimProof (P i) Ctx (ε i)) : andN 2 B = (B 0).and (B 1) :=
  rfl

@[simp] theorem andN_claim : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    [∀ i j, Fintype ((P i).Challenge j)] → {ε : ∀ i, (P i).ChallengeIdx → ℝ≥0} →
    (B : ∀ i, ClaimProof (P i) Ctx (ε i)) → (c : Ctx) →
    ((andN m B).claim c ↔ ∀ i, (B i).claim c)
  | 0, _, _, _, _, _, _ => ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | 1, _, _, _, _, B, c => (Fin.forall_fin_one (p := fun i => (B i).claim c)).symm
  | m + 2, _, _, _, _, B, c => by
    rw [Fin.forall_fin_succ, ← andN_claim (m + 1) (fun i => B i.succ) c]
    rfl

theorem andN_V : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    [∀ i j, Fintype ((P i).Challenge j)] → {ε : ∀ i, (P i).ChallengeIdx → ℝ≥0} →
    (B : ∀ i, ClaimProof (P i) Ctx (ε i)) → (c : Ctx) →
    (tr : (appendN m P).Transcript (Fin.last (lenN m n))) →
    ((andN m B).V c tr = true ↔ ∀ i, (B i).V c (Transcript.part m tr i) = true)
  | 0, _, _, _, _, _, _, _ => ⟨fun _ i => i.elim0, fun _ => rfl⟩
  | 1, _, _, _, _, B, c, tr =>
    (Fin.forall_fin_one (p := fun i => (B i).V c (Transcript.part 1 tr i) = true)).symm
  | m + 2, _, _, _, _, B, c, tr => by
    rw [Fin.forall_fin_succ]
    exact (Bool.and_eq_true _ _).to_iff.trans
      (and_congr Iff.rfl (andN_V (m + 1) (fun i => B i.succ) c tr.right))

end ClaimProof

/-! ### Honest transcripts in sequence -/

/-- **Honest transcript families of the parts, run in sequence.** For `m = 2` it is
`CausalTranscript.append` with a second family that ignores the first part's transcript. -/
def CausalTranscript.appendN : (m : ℕ) → {n : Fin m → ℕ} →
    {P : (i : Fin m) → ProtocolSpec (n i)} → (∀ i, CausalTranscript (P i)) →
    CausalTranscript (ProtocolSpec.appendN m P)
  | 0, _, _, _ => CausalTranscript.empty _
  | 1, _, _, H => H 0
  | m + 2, _, _, H => (H 0).append fun _ => CausalTranscript.appendN (m + 1) fun i => H i.succ

/-- The transcript of the parts in sequence joins the parts' transcripts at their challenges. -/
theorem CausalTranscript.appendN_transcript : (m : ℕ) → {n : Fin m → ℕ} →
    {P : (i : Fin m) → ProtocolSpec (n i)} → (H : ∀ i, CausalTranscript (P i)) →
    (ch : (ProtocolSpec.appendN m P).Challenges) →
    (CausalTranscript.appendN m H).transcript ch = joinN m fun i => (H i).transcript (chN m ch i)
  | 0, _, _, _, _ => funext fun i => i.elim0
  | 1, _, _, _, _ => rfl
  | m + 2, _, _, H, ch => by
    change Transcript.join ((H 0).transcript ch.left)
      ((CausalTranscript.appendN (m + 1) fun i => H i.succ).transcript ch.right) = _
    rw [CausalTranscript.appendN_transcript (m + 1)]
    rfl

/-- **Completeness of phases in sequence**: on the transcript of honest families run in
sequence, the conjunction accepts exactly when every part's verifier accepts that part's honest
transcript at its challenges. -/
theorem ClaimProof.andN_V_appendN {Ctx : Type} {m : ℕ} {n : Fin m → ℕ}
    {P : (i : Fin m) → ProtocolSpec (n i)} [∀ i j, Fintype ((P i).Challenge j)]
    {ε : ∀ i, (P i).ChallengeIdx → ℝ≥0} (B : ∀ i, ClaimProof (P i) Ctx (ε i)) (c : Ctx)
    (H : ∀ i, CausalTranscript (P i)) (ch : (ProtocolSpec.appendN m P).Challenges) :
    (ClaimProof.andN m B).V c ((CausalTranscript.appendN m H).transcript ch) = true ↔
      ∀ i, (B i).V c ((H i).transcript (chN m ch i)) = true := by
  rw [ClaimProof.andN_V, CausalTranscript.appendN_transcript, part_joinN]

end GordieHowe.IOP
