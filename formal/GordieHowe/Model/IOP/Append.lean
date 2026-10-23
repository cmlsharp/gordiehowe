-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.RBR

@[expose] public section

/-!
# Appending protocols: a claim-producing phase followed by claim-proving phases

`ProtocolSpec.append P₁ P₂` runs the rounds of `P₁` and then those of `P₂`, as ArkLib's
`ProtocolSpec.append` (`ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean`). A partial
transcript of the appended protocol is read through two projections: `Transcript.fst`, the
first `k` part-1 messages, and `Transcript.snd`, the first `k` part-2 messages. Both take the
length `k` and a proof that the transcript is long enough, as `Transcript.take` does, so no
statement needs an equation between lengths.

The two composition lemmas:

* `ClaimPhase.append_rbrKnowledgeSoundness`: a phase with a one-shot extractor that produces a
  claim, followed by a phase that is round-by-round sound relative to that claim, is
  round-by-round knowledge sound with the part-1 extractor, and each round keeps its error;
* `ClaimProof.and`: two claim-proving phases run in sequence prove the conjunction of their
  claims.

Both state functions are instances of `ProtocolSpec.appendState`: one family of propositions
about part-1 transcripts during part 1, and one about part-2 transcripts, given the whole
part-1 transcript, from the start of part 2.
-/

namespace GordieHowe.IOP

open scoped NNReal

variable {n n₁ n₂ : ℕ}

namespace ProtocolSpec

/-- The protocol that runs the rounds of `P₁` and then the rounds of `P₂`. -/
def append (P₁ : ProtocolSpec n₁) (P₂ : ProtocolSpec n₂) : ProtocolSpec (n₁ + n₂) where
  dir := Fin.append P₁.dir P₂.dir
  «Type» := Fin.append P₁.Type P₂.Type

/-- `P₁ ++ P₂` is `P₁.append P₂`. -/
instance : HAppend (ProtocolSpec n₁) (ProtocolSpec n₂) (ProtocolSpec (n₁ + n₂)) := ⟨append⟩

theorem hAppend_eq_append (P₁ : ProtocolSpec n₁) (P₂ : ProtocolSpec n₂) :
    P₁ ++ P₂ = P₁.append P₂ := rfl

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}

/-- A part-1 round of the appended protocol has the direction of the `P₁` round. -/
@[simp]
theorem append_dir_castAdd (j : Fin n₁) :
    (P₁ ++ P₂).dir (Fin.castAdd n₂ j) = P₁.dir j :=
  Fin.append_left P₁.dir P₂.dir j

/-- A part-2 round of the appended protocol has the direction of the `P₂` round. -/
@[simp]
theorem append_dir_natAdd (j : Fin n₂) :
    (P₁ ++ P₂).dir (Fin.natAdd n₁ j) = P₂.dir j :=
  Fin.append_right P₁.dir P₂.dir j

/-- A part-1 round of the appended protocol has the message type of the `P₁` round. -/
theorem append_Type_castAdd (j : Fin n₁) :
    (P₁ ++ P₂).Type (Fin.castAdd n₂ j) = P₁.Type j :=
  Fin.append_left P₁.Type P₂.Type j

/-- A part-2 round of the appended protocol has the message type of the `P₂` round. -/
theorem append_Type_natAdd (j : Fin n₂) :
    (P₁ ++ P₂).Type (Fin.natAdd n₁ j) = P₂.Type j :=
  Fin.append_right P₁.Type P₂.Type j

/-- The first `k` part-1 messages of a transcript of the appended protocol, `k` at most its
length. -/
def Transcript.fst {m : Fin (n₁ + n₂ + 1)} (tr : (P₁ ++ P₂).Transcript m) (k : Fin (n₁ + 1))
    (hk : (k : ℕ) ≤ m) : P₁.Transcript k :=
  fun i => cast (append_Type_castAdd (Fin.castLE (by omega) i)) (tr ⟨i, by omega⟩)

/-- The first `k` part-2 messages of a transcript of the appended protocol, `n₁ + k` at most
its length. -/
def Transcript.snd {m : Fin (n₁ + n₂ + 1)} (tr : (P₁ ++ P₂).Transcript m) (k : Fin (n₂ + 1))
    (hk : n₁ + k ≤ m) : P₂.Transcript k :=
  fun i => cast (append_Type_natAdd (Fin.castLE (by omega) i)) (tr ⟨n₁ + i, by omega⟩)

/-- The full `P₁` transcript inside a full transcript of the appended protocol. -/
def Transcript.left (tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))) :
    P₁.Transcript (Fin.last n₁) :=
  tr.fst (Fin.last n₁) (by simp)

/-- The full `P₂` transcript inside a full transcript of the appended protocol. -/
def Transcript.right (tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))) :
    P₂.Transcript (Fin.last n₂) :=
  tr.snd (Fin.last n₂) (by simp)

/-- Appending a message does not change the first `k` part-1 messages, `k` at most the length
before appending. -/
theorem Transcript.fst_concat_of_le {m : Fin (n₁ + n₂)}
    (tr : (P₁ ++ P₂).Transcript m.castSucc) (msg : (P₁ ++ P₂).Type m) (k : Fin (n₁ + 1))
    (hk : (k : ℕ) ≤ m) :
    ((P₁ ++ P₂).concat tr msg).fst k (by simp; omega) = tr.fst k (by simpa using hk) := by
  funext i
  have hi : (i : ℕ) < m := by
    have := i.2
    omega
  simp only [Transcript.fst, ProtocolSpec.concat, Fin.snoc, Fin.val_castSucc, hi, dite_true,
    cast_cast]
  rfl

/-- Appending the message of part-1 round `j` appends it to the part-1 transcript. -/
theorem Transcript.fst_concat_castAdd (j : Fin n₁)
    (tr : (P₁ ++ P₂).Transcript (Fin.castAdd n₂ j).castSucc)
    (msg : (P₁ ++ P₂).Type (Fin.castAdd n₂ j)) :
    ((P₁ ++ P₂).concat tr msg).fst j.succ (by simp) =
      P₁.concat (tr.fst j.castSucc (by simp)) (cast (append_Type_castAdd j) msg) := by
  funext i
  by_cases hi : (i : ℕ) < j
  · simp only [Transcript.fst, ProtocolSpec.concat, Fin.snoc, Fin.val_castSucc, Fin.val_castAdd,
      Fin.val_castLT, hi, dite_true, cast_cast]
    rfl
  · simp only [Transcript.fst, ProtocolSpec.concat, Fin.snoc, Fin.val_castSucc, Fin.val_castAdd,
      hi, dite_false, cast_cast]

/-- Appending the message of part-2 round `j` appends it to the part-2 transcript. -/
theorem Transcript.snd_concat_natAdd (j : Fin n₂)
    (tr : (P₁ ++ P₂).Transcript (Fin.natAdd n₁ j).castSucc)
    (msg : (P₁ ++ P₂).Type (Fin.natAdd n₁ j)) :
    ((P₁ ++ P₂).concat tr msg).snd j.succ (by simp [Nat.add_assoc]) =
      P₂.concat (tr.snd j.castSucc (by simp)) (cast (append_Type_natAdd j) msg) := by
  funext i
  by_cases hi : (i : ℕ) < j
  · simp only [Transcript.snd, ProtocolSpec.concat, Fin.snoc, Fin.val_castSucc, Fin.val_natAdd,
      Fin.val_castLT, hi, Nat.add_lt_add_iff_left, dite_true, cast_cast]
    rfl
  · simp only [Transcript.snd, ProtocolSpec.concat, Fin.snoc, Fin.val_castSucc, Fin.val_natAdd,
      hi, Nat.add_lt_add_iff_left, dite_false, cast_cast]

/-- The verifier round `i` of `P`, given that `i` is a verifier round. -/
def ChallengeIdx.mk {P : ProtocolSpec n} (i : Fin n) (h : P.dir i = .V_to_P) : P.ChallengeIdx :=
  ⟨i, h⟩

/-- The round index of `ChallengeIdx.mk i h` is `i`. -/
@[simp]
theorem ChallengeIdx.val_mk {P : ProtocolSpec n} (i : Fin n) (h : P.dir i = .V_to_P) :
    (ChallengeIdx.mk i h).1 = i :=
  rfl

/-- Verifier rounds are equal when their round indices are. -/
theorem ChallengeIdx.ext {P : ProtocolSpec n} {i i' : P.ChallengeIdx} (h : i.1 = i'.1) :
    i = i' :=
  Subtype.ext h

/-- The verifier round of the appended protocol for a verifier round of `P₁`. -/
def ChallengeIdx.inl (j : P₁.ChallengeIdx) : (P₁ ++ P₂).ChallengeIdx :=
  .mk (Fin.castAdd n₂ j.1) ((append_dir_castAdd j.1).trans j.2)

/-- The verifier round of the appended protocol for a verifier round of `P₂`. -/
def ChallengeIdx.inr (j : P₂.ChallengeIdx) : (P₁ ++ P₂).ChallengeIdx :=
  .mk (Fin.natAdd n₁ j.1) ((append_dir_natAdd j.1).trans j.2)

/-- The round index of `ChallengeIdx.inl j` is `j` in part 1. -/
@[simp]
theorem ChallengeIdx.val_inl (j : P₁.ChallengeIdx) :
    (ChallengeIdx.inl (P₂ := P₂) j).1 = Fin.castAdd n₂ j.1 :=
  rfl

/-- The round index of `ChallengeIdx.inr j` is `j` in part 2. -/
@[simp]
theorem ChallengeIdx.val_inr (j : P₂.ChallengeIdx) :
    (ChallengeIdx.inr (P₁ := P₁) j).1 = Fin.natAdd n₁ j.1 :=
  rfl

/-- The verifier round of `P₁` or of `P₂` that a verifier round of the appended protocol is. -/
def ChallengeIdx.toSum (i : (P₁ ++ P₂).ChallengeIdx) : P₁.ChallengeIdx ⊕ P₂.ChallengeIdx :=
  if h : (i.1 : ℕ) < n₁ then
    .inl (.mk ⟨i.1, h⟩ ((append_dir_castAdd (P₂ := P₂) ⟨i.1, h⟩).symm.trans i.2))
  else
    .inr (.mk ⟨i.1 - n₁, by omega⟩ (by
      have e : Fin.natAdd n₁ ⟨i.1 - n₁, by omega⟩ = i.1 :=
        Fin.ext (by simp only [Fin.val_natAdd]; omega)
      rw [← append_dir_natAdd (P₁ := P₁), e]
      exact i.2))

/-- `ChallengeIdx.toSum` inverts `ChallengeIdx.inl`. -/
@[simp]
theorem ChallengeIdx.toSum_inl (j : P₁.ChallengeIdx) :
    (ChallengeIdx.inl (P₂ := P₂) j).toSum = .inl j := by
  rw [ChallengeIdx.toSum, dite_eq_left (by simp)]
  rfl

/-- `ChallengeIdx.toSum` inverts `ChallengeIdx.inr`. -/
@[simp]
theorem ChallengeIdx.toSum_inr (j : P₂.ChallengeIdx) :
    (ChallengeIdx.inr (P₁ := P₁) j).toSum = .inr j := by
  rw [ChallengeIdx.toSum, dite_eq_right (by simp)]
  congr 1
  exact ChallengeIdx.ext (Fin.ext (by simp [ChallengeIdx.mk]))

/-- The verifier rounds of the appended protocol are those of `P₁` and those of `P₂`. -/
def challengeIdxEquiv : (P₁ ++ P₂).ChallengeIdx ≃ P₁.ChallengeIdx ⊕ P₂.ChallengeIdx where
  toFun := ChallengeIdx.toSum
  invFun := Sum.elim ChallengeIdx.inl ChallengeIdx.inr
  left_inv i := by
    rw [ChallengeIdx.toSum]
    split_ifs with h
    · rfl
    · exact ChallengeIdx.ext (Fin.ext (by
        simp only [Sum.elim_inr, ChallengeIdx.val_inr, ChallengeIdx.val_mk, Fin.val_natAdd]
        omega))
  right_inv s := by
    rcases s with j | j <;> simp

/-- A part-1 verifier round is the `P₁` verifier round it came from. -/
@[simp]
theorem challengeIdxEquiv_inl (j : P₁.ChallengeIdx) :
    challengeIdxEquiv (ChallengeIdx.inl (P₂ := P₂) j) = .inl j :=
  ChallengeIdx.toSum_inl j

/-- A part-2 verifier round is the `P₂` verifier round it came from. -/
@[simp]
theorem challengeIdxEquiv_inr (j : P₂.ChallengeIdx) :
    challengeIdxEquiv (ChallengeIdx.inr (P₁ := P₁) j) = .inr j :=
  ChallengeIdx.toSum_inr j

/-- Every verifier round of the appended protocol is a verifier round of `P₁` or of `P₂`. -/
theorem ChallengeIdx.inl_or_inr (i : (P₁ ++ P₂).ChallengeIdx) :
    (∃ j, i = ChallengeIdx.inl j) ∨ ∃ j, i = ChallengeIdx.inr j := by
  rcases h : challengeIdxEquiv i with j | j
  · exact .inl ⟨j, (challengeIdxEquiv.symm_apply_eq.mpr h.symm).symm⟩
  · exact .inr ⟨j, (challengeIdxEquiv.symm_apply_eq.mpr h.symm).symm⟩

/-- A part-1 verifier round of the appended protocol has the challenge type of the `P₁`
round. -/
theorem append_Challenge_inl (j : P₁.ChallengeIdx) :
    (P₁ ++ P₂).Challenge (ChallengeIdx.inl j) = P₁.Challenge j :=
  append_Type_castAdd j.1

/-- A part-2 verifier round of the appended protocol has the challenge type of the `P₂`
round. -/
theorem append_Challenge_inr (j : P₂.ChallengeIdx) :
    (P₁ ++ P₂).Challenge (ChallengeIdx.inr j) = P₂.Challenge j :=
  append_Type_natAdd j.1

/-- A verifier round of the appended protocol that is a `P₁` round has that round's challenge
type. -/
theorem append_Challenge_of_inl {i : (P₁ ++ P₂).ChallengeIdx} {j : P₁.ChallengeIdx}
    (h : challengeIdxEquiv i = .inl j) : (P₁ ++ P₂).Challenge i = P₁.Challenge j := by
  obtain rfl := (challengeIdxEquiv.symm_apply_eq.mpr h.symm)
  exact append_Challenge_inl j

/-- A verifier round of the appended protocol that is a `P₂` round has that round's challenge
type. -/
theorem append_Challenge_of_inr {i : (P₁ ++ P₂).ChallengeIdx} {j : P₂.ChallengeIdx}
    (h : challengeIdxEquiv i = .inr j) : (P₁ ++ P₂).Challenge i = P₂.Challenge j := by
  obtain rfl := (challengeIdxEquiv.symm_apply_eq.mpr h.symm)
  exact append_Challenge_inr j

/-- **The challenges of an appended protocol from those of its parts**: each verifier round of
`P₁ ++ P₂` takes the challenge of the `P₁` or `P₂` round it is. -/
def Challenges.join (left : P₁.Challenges) (right : P₂.Challenges) : (P₁ ++ P₂).Challenges :=
  fun i => match h : challengeIdxEquiv i with
    | .inl j => cast (append_Challenge_of_inl h).symm (left j)
    | .inr j => cast (append_Challenge_of_inr h).symm (right j)

/-- The challenges of a verifier round of the appended protocol are finite when those of both
protocols are. -/
instance [∀ i, Fintype (P₁.Challenge i)] [∀ i, Fintype (P₂.Challenge i)]
    (i : (P₁ ++ P₂).ChallengeIdx) : Fintype ((P₁ ++ P₂).Challenge i) :=
  match h : challengeIdxEquiv i with
  | .inl j => Fintype.ofEquiv (P₁.Challenge j) (Equiv.cast (append_Challenge_of_inl h).symm)
  | .inr j => Fintype.ofEquiv (P₂.Challenge j) (Equiv.cast (append_Challenge_of_inr h).symm)

/-- The challenges of a verifier round of the appended protocol have decidable equality when
those of both protocols do. -/
instance append_challenge_decidableEq [∀ i, DecidableEq (P₁.Challenge i)]
    [∀ i, DecidableEq (P₂.Challenge i)] (i : (P₁ ++ P₂).ChallengeIdx) :
    DecidableEq ((P₁ ++ P₂).Challenge i) :=
  match h : challengeIdxEquiv i with
  | .inl j => (Equiv.cast (append_Challenge_of_inl h)).decidableEq
  | .inr j => (Equiv.cast (append_Challenge_of_inr h)).decidableEq

/-- The challenges of a verifier round of the appended protocol are nonempty when those of
both protocols are. -/
instance append_challenge_nonempty [∀ i, Nonempty (P₁.Challenge i)] [∀ i, Nonempty (P₂.Challenge i)]
    (i : (P₁ ++ P₂).ChallengeIdx) : Nonempty ((P₁ ++ P₂).Challenge i) :=
  match h : challengeIdxEquiv i with
  | .inl j => (Equiv.cast (append_Challenge_of_inl h).symm).nonempty_congr.mp inferInstance
  | .inr j => (Equiv.cast (append_Challenge_of_inr h).symm).nonempty_congr.mp inferInstance

/-- **The round errors of an appended protocol**: `ε₁` at the verifier rounds of `P₁`, `ε₂` at
those of `P₂`. -/
def appendError (ε₁ : P₁.ChallengeIdx → ℝ≥0) (ε₂ : P₂.ChallengeIdx → ℝ≥0) :
    (P₁ ++ P₂).ChallengeIdx → ℝ≥0 :=
  fun i => Sum.elim ε₁ ε₂ (challengeIdxEquiv i)

section AppendError

variable (ε₁ : P₁.ChallengeIdx → ℝ≥0) (ε₂ : P₂.ChallengeIdx → ℝ≥0)

@[simp] theorem appendError_inl (j : P₁.ChallengeIdx) :
    appendError ε₁ ε₂ (ChallengeIdx.inl j) = ε₁ j := by
  simp only [appendError, challengeIdxEquiv_inl, Sum.elim_inl]

@[simp] theorem appendError_inr (j : P₂.ChallengeIdx) :
    appendError ε₁ ε₂ (ChallengeIdx.inr j) = ε₂ j := by
  simp only [appendError, challengeIdxEquiv_inr, Sum.elim_inr]

/-- The errors of an appended protocol sum to the sums of both protocols' errors. -/
theorem sum_appendError :
    ∑ i, appendError ε₁ ε₂ i = ∑ i, ε₁ i + ∑ j, ε₂ j := by
  rw [Fintype.sum_equiv challengeIdxEquiv (appendError ε₁ ε₂) (Sum.elim ε₁ ε₂) fun _ => rfl,
    Fintype.sum_sum_type]
  rfl

variable {ε₁ ε₂} in
/-- A bound on both protocols' errors bounds every error of the appended protocol. -/
theorem appendError_le {δ : ℝ≥0} (h₁ : ∀ j, ε₁ j ≤ δ) (h₂ : ∀ j, ε₂ j ≤ δ)
    (i : (P₁ ++ P₂).ChallengeIdx) : appendError ε₁ ε₂ i ≤ δ := by
  unfold appendError
  rcases challengeIdxEquiv i with j | j
  exacts [h₁ j, h₂ j]

/-- The largest error of an appended protocol is the larger of the two protocols' largest. -/
theorem maxError_appendError :
    maxError (appendError ε₁ ε₂) = max (maxError ε₁) (maxError ε₂) :=
  (maxError_comp_equiv (Sum.elim ε₁ ε₂) challengeIdxEquiv).trans (maxError_sum_elim ε₁ ε₂)

end AppendError

/-- A family of propositions about the partial transcripts of the appended protocol: `S₁` on
the part-1 transcript during part 1, and from the start of part 2, `S₂` of the whole part-1
transcript on the part-2 transcript. -/
def appendState (S₁ : (k : Fin (n₁ + 1)) → P₁.Transcript k → Prop)
    (S₂ : P₁.Transcript (Fin.last n₁) → (k : Fin (n₂ + 1)) → P₂.Transcript k → Prop)
    (m : Fin (n₁ + n₂ + 1)) (tr : (P₁ ++ P₂).Transcript m) : Prop :=
  if h : (m : ℕ) < n₁ then S₁ ⟨m, by omega⟩ (tr.fst ⟨m, by omega⟩ le_rfl)
  else S₂ (tr.fst (Fin.last n₁) (by simp; omega)) ⟨m - n₁, by omega⟩
    (tr.snd ⟨m - n₁, by omega⟩ (by simp; omega))

variable {S₁ : (k : Fin (n₁ + 1)) → P₁.Transcript k → Prop}
  {S₂ : P₁.Transcript (Fin.last n₁) → (k : Fin (n₂ + 1)) → P₂.Transcript k → Prop}

/-- During part 1, `appendState` is `S₁` of the part-1 transcript. -/
theorem appendState_iff_of_lt {k : Fin (n₁ + n₂ + 1)} {k₁ : Fin (n₁ + 1)} (hk : (k : ℕ) = k₁)
    (hlt : (k : ℕ) < n₁) (tr : (P₁ ++ P₂).Transcript k) :
    appendState S₁ S₂ k tr ↔ S₁ k₁ (tr.fst k₁ hk.ge) := by
  obtain ⟨k₁, hk₁⟩ := k₁
  simp only at hk
  subst hk
  rw [appendState, dite_eq_left hlt]

/-- From the start of part 2, `appendState` is `S₂` of the part-1 transcript on the part-2
transcript. -/
theorem appendState_iff_of_eq_add {k : Fin (n₁ + n₂ + 1)} {k₂ : Fin (n₂ + 1)}
    (hk : (k : ℕ) = n₁ + k₂) (tr : (P₁ ++ P₂).Transcript k) :
    appendState S₁ S₂ k tr ↔
      S₂ (tr.fst (Fin.last n₁) (by simp; omega)) k₂ (tr.snd k₂ hk.ge) := by
  obtain ⟨k₂, hk₂⟩ := k₂
  have e : (k : ℕ) - n₁ = k₂ := by simp only at hk; omega
  subst e
  rw [appendState, dite_eq_right (by simp only at hk; omega)]

/-- If `S₂` at the start of part 2 implies `S₁` on the whole part-1 transcript, then up to the
end of part 1 `appendState` implies `S₁` of the part-1 transcript. -/
theorem appendState_of_le (h0 : ∀ tr₁ tr₂, S₂ tr₁ 0 tr₂ → S₁ (Fin.last n₁) tr₁)
    {k : Fin (n₁ + n₂ + 1)} {k₁ : Fin (n₁ + 1)} (hk : (k : ℕ) = k₁)
    {tr : (P₁ ++ P₂).Transcript k} (h : appendState S₁ S₂ k tr) :
    S₁ k₁ (tr.fst k₁ hk.ge) := by
  obtain ⟨k₁, hk₁⟩ := k₁
  obtain ⟨k, hk'⟩ := k
  simp only at hk
  subst hk
  by_cases hlt : k < n₁
  · exact (appendState_iff_of_lt rfl hlt tr).mp h
  · obtain rfl : n₁ = k := by omega
    have key : ∀ {tr₁} {k₂ : Fin (n₂ + 1)}, (k₂ : ℕ) = 0 → ∀ {tr₂}, S₂ tr₁ k₂ tr₂ →
        S₁ (Fin.last n₁) tr₁ := by
      intro tr₁ k₂ hk₂ tr₂
      obtain rfl : k₂ = 0 := Fin.ext (by simpa using hk₂)
      exact h0 tr₁ tr₂
    exact key (by simp) ((appendState_iff_of_eq_add (k₂ := 0) (by simp) tr).mp h)

/-- A part-1 round moves `appendState` from false to true only if it moves `S₁` from false to
true, when `S₂` at the start of part 2 implies `S₁` on the whole part-1 transcript. -/
theorem appendState_flip_castAdd (h0 : ∀ tr₁ tr₂, S₂ tr₁ 0 tr₂ → S₁ (Fin.last n₁) tr₁)
    (j : Fin n₁) (tr : (P₁ ++ P₂).Transcript (Fin.castAdd n₂ j).castSucc)
    (msg : (P₁ ++ P₂).Type (Fin.castAdd n₂ j))
    (hnot : ¬ appendState S₁ S₂ _ tr) (h : appendState S₁ S₂ _ ((P₁ ++ P₂).concat tr msg)) :
    ¬ S₁ j.castSucc (tr.fst j.castSucc (by simp)) ∧
      S₁ j.succ (P₁.concat (tr.fst j.castSucc (by simp)) (cast (append_Type_castAdd j) msg)) := by
  refine ⟨fun h' => hnot ((appendState_iff_of_lt (k₁ := j.castSucc) (by simp) (by simp) tr).mpr h'),
    ?_⟩
  rw [← Transcript.fst_concat_castAdd]
  exact appendState_of_le h0 (k₁ := j.succ) (by simp) h

/-- A part-2 round moves `appendState` from false to true exactly when it moves `S₂` of the
part-1 transcript from false to true. -/
theorem appendState_flip_natAdd (j : Fin n₂)
    (tr : (P₁ ++ P₂).Transcript (Fin.natAdd n₁ j).castSucc)
    (msg : (P₁ ++ P₂).Type (Fin.natAdd n₁ j)) :
    (¬ appendState S₁ S₂ _ tr ∧ appendState S₁ S₂ _ ((P₁ ++ P₂).concat tr msg)) ↔
      (¬ S₂ (tr.fst (Fin.last n₁) (by simp)) j.castSucc (tr.snd j.castSucc (by simp)) ∧
        S₂ (tr.fst (Fin.last n₁) (by simp)) j.succ
          (P₂.concat (tr.snd j.castSucc (by simp)) (cast (append_Type_natAdd j) msg))) := by
  rw [appendState_iff_of_eq_add (k₂ := j.castSucc) (by simp),
    appendState_iff_of_eq_add (k₂ := j.succ) (by simp [Nat.add_assoc]),
    Transcript.snd_concat_natAdd,
    Transcript.fst_concat_of_le tr msg (Fin.last n₁) (by simp)]

end ProtocolSpec

/-- **The context of an appended phase**: the context of the phase before it and that phase's full
transcript. The second phase of `ClaimReduction.append` and
`ClaimPhase.append_rbrKnowledgeSoundness` proves a claim about this context. -/
@[ext]
structure AppendContext (Ctx : Type) (P : ProtocolSpec n) where
  /-- The context of the phase before. -/
  ctx : Ctx
  /-- The full transcript of the phase before. -/
  transcript : P.Transcript (Fin.last n)

open Finset in
/-- A counting bound transported along an equality of finite types: if every element of `s`
is cast into `t`, a bound on `t` bounds `s`. The statement is about Mathlib objects only and is
a candidate for `PQ/ToMathlib`. -/
theorem card_le_of_mapsTo_cast {α β : Type} [Fintype α] [Fintype β] (h : α = β) {s : Finset α}
    {t : Finset β} {a : ℝ≥0} (hst : ∀ x ∈ s, cast h x ∈ t)
    (ht : (#t : ℝ≥0) ≤ a * Fintype.card β) : (#s : ℝ≥0) ≤ a * Fintype.card α := by
  rw [Fintype.card_congr (Equiv.cast h)]
  refine le_trans (Nat.cast_le.mpr (card_le_card_of_injOn (cast h) hst ?_)) ht
  intro x _ y _ hxy
  exact (cast_inj h).mp hxy

open Classical in
/-- A claim-producing phase with a one-shot extractor: its state is true whenever its claim
holds. The fields are those of `KnowledgeStateFunction` and `rbrKnowledgeSoundness`, with
acceptance replaced by the claim. -/
structure ClaimPhase (P : ProtocolSpec n) (StmtIn WitIn : Type) (rel : Set (StmtIn × WitIn))
    [∀ i, Fintype (P.Challenge i)] (ε : P.ChallengeIdx → ℝ≥0) where
  /-- The one-shot extractor. -/
  E : Extractor P StmtIn WitIn
  /-- The claim the phase produces about the statement and its transcript. -/
  claim : StmtIn → P.Transcript (Fin.last n) → Prop
  /-- The state function. -/
  S : (m : Fin (n + 1)) → StmtIn → P.Transcript m → Prop
  /-- The state is false on the empty transcript. -/
  empty : ∀ x tr, ¬ S 0 x tr
  /-- A prover message does not make the state true. -/
  next : ∀ (m : Fin n), P.dir m = .P_to_V → ∀ x (tr : P.Transcript m.castSucc) msg,
    ¬ S m.castSucc x tr → ¬ S m.succ x (P.concat tr msg)
  /-- The state is true on a full transcript whose claim holds. -/
  full : ∀ x tr, claim x tr → S (Fin.last n) x tr
  /-- At every prefix before a verifier round, at most `ε i · |C_i|` challenges make the state
  true from false while the extractor fails on the prefix. -/
  rbr : ∀ (x : StmtIn) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
    ((Finset.univ.filter fun c : P.Challenge i =>
        (x, E i.1.castSucc x tr) ∉ rel ∧ ¬ S i.1.castSucc x tr ∧
          S i.1.succ x (P.concat tr c)).card : ℝ≥0) ≤
      ε i * Fintype.card (P.Challenge i)

open Classical in
/-- A phase proving a claim about a context, round-by-round sound relative to it: its state is
false at the start when the claim is false, is not made true by prover rounds, is true when
its verifier accepts, and at every prefix at most `ε i · |C_i|` challenges make it true from
false. -/
structure ClaimProof (P : ProtocolSpec n) (Ctx : Type) [∀ i, Fintype (P.Challenge i)]
    (ε : P.ChallengeIdx → ℝ≥0) where
  /-- The claim about the context. -/
  claim : Ctx → Prop
  /-- The verifier's decision on the context and the full transcript. -/
  V : Ctx → P.Transcript (Fin.last n) → Bool
  /-- The state function. -/
  S : (m : Fin (n + 1)) → Ctx → P.Transcript m → Prop
  /-- The state is false on the empty transcript when the claim is false. -/
  start : ∀ c tr, ¬ claim c → ¬ S 0 c tr
  /-- A prover message does not make the state true. -/
  next : ∀ (m : Fin n), P.dir m = .P_to_V → ∀ c (tr : P.Transcript m.castSucc) msg,
    ¬ S m.castSucc c tr → ¬ S m.succ c (P.concat tr msg)
  /-- The state is true on a full transcript the verifier accepts. -/
  full : ∀ c tr, V c tr = true → S (Fin.last n) c tr
  /-- At every prefix before a verifier round, at most `ε i · |C_i|` challenges make the state
  true from false. -/
  rbr : ∀ (c : Ctx) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
    ((Finset.univ.filter fun ch : P.Challenge i =>
        ¬ S i.1.castSucc c tr ∧ S i.1.succ c (P.concat tr ch)).card : ℝ≥0) ≤
      ε i * Fintype.card (P.Challenge i)

namespace ClaimProof

variable {P : ProtocolSpec n} {Ctx : Type} [∀ i, Fintype (P.Challenge i)]
  {ε : P.ChallengeIdx → ℝ≥0}

/-- Enlarge per-round error budgets without changing the verifier or claim. -/
def monoError (B : ClaimProof P Ctx ε) {δ : P.ChallengeIdx → ℝ≥0}
    (h : ∀ i, ε i ≤ δ i) : ClaimProof P Ctx δ where
  claim := B.claim
  V := B.V
  S := B.S
  start := B.start
  next := B.next
  full := B.full
  rbr c i tr := (B.rbr c i tr).trans (mul_le_mul_of_nonneg_right (h i) (by positivity))

/-- A state that is true at the start of a claim-proving phase implies the claim. -/
theorem claim_of_S (B : ClaimProof P Ctx ε) {c : Ctx} {tr : P.Transcript 0} (h : B.S 0 c tr) :
    B.claim c := by
  by_contra hc
  exact B.start c tr hc h

open Classical Finset in
/-- **Soundness of a claim-proving phase.** When the claim about `c` is false, every
deterministic prover makes the verifier accept on at most a `∑ i, ε i` fraction of the
challenge tuples. Built as a knowledge-soundness instance with witness type `Unit`,
relation `{p | B.claim p.1}` and verifier `B.V` conjoined with `decide (¬ B.claim ·)`: the
extractor is then irrelevant, since the relation already fails at `c`. -/
theorem accept_card_le [Fintype P.ChallengeIdx] (B : ClaimProof P Ctx ε) {c : Ctx}
    (hc : ¬ B.claim c) (prv : Prover P Ctx) :
    ((Finset.univ.filter fun ch : P.Challenges => B.V c (prv.run c ch) = true).card : ℝ≥0) ≤
      (∑ i, ε i) * Fintype.card P.Challenges := by
  let rel : Set (Ctx × Unit) := {p | B.claim p.1}
  let V' : Ctx → P.Transcript (Fin.last n) → Bool := fun x tr => B.V x tr && decide (¬ B.claim x)
  let S : (m : Fin (n + 1)) → Ctx → P.Transcript m → Prop := fun m x tr => B.S m x tr ∧ ¬ B.claim x
  have hempty : ∀ x tr, ¬ S 0 x tr := by
    intro x tr h
    exact B.start x tr h.2 h.1
  have hnext : ∀ (m : Fin n), P.dir m = .P_to_V → ∀ x (tr : P.Transcript m.castSucc) msg,
      ¬ S m.castSucc x tr → ¬ S m.succ x (P.concat tr msg) := by
    intro m hdir x tr msg hnot hcontra
    obtain ⟨hS2, hnc⟩ := hcontra
    exact B.next m hdir x tr msg (fun hA => hnot ⟨hA, hnc⟩) hS2
  have hfull : ∀ x tr, V' x tr = true → S (Fin.last n) x tr := by
    intro x tr h
    have h' : (B.V x tr && decide (¬ B.claim x)) = true := h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h'
    exact ⟨B.full x tr h'.1, h'.2⟩
  let Sfun : KnowledgeStateFunction V' := ⟨S, hempty, hnext, hfull⟩
  let E : Extractor P Ctx Unit := ⟨fun _ _ _ => ()⟩
  have hE' := knowledgeSoundness_count_of_rbr_count (rel := rel) (ε := ε) E Sfun (by
    intro x i tr
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (B.rbr x i tr)
    intro ch hch
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
    obtain ⟨hnr, hnS, hS2⟩ := hch
    have hnc : ¬ B.claim x := hnr
    have hnS' : ¬ B.S i.1.castSucc x tr := fun hA => hnS ⟨hA, hnc⟩
    have hS2' : B.S i.1.succ x (P.concat tr ch) ∧ ¬ B.claim x := hS2
    exact ⟨hnS', hS2'.1⟩)
  have hspec := hE' c prv
  have hVeq : ∀ tr, V' c tr = B.V c tr := by
    intro tr
    have hd : decide (¬ B.claim c) = true := decide_eq_true hc
    show (B.V c tr && decide (¬ B.claim c)) = B.V c tr
    rw [hd, Bool.and_true]
  have hrelfree : ∀ w, ((c, w) : Ctx × Unit) ∉ rel := fun _ => hc
  have hSame : (Finset.univ.filter fun ch : P.Challenges =>
      V' c (prv.run c ch) = true ∧ (c, E.straightLine rel (Fin.last n) c (prv.run c ch)) ∉ rel) =
      Finset.univ.filter fun ch : P.Challenges => B.V c (prv.run c ch) = true := by
    apply Finset.filter_congr
    intro ch _
    rw [hVeq (prv.run c ch)]
    exact and_iff_left (hrelfree (E.straightLine rel (Fin.last n) c (prv.run c ch)))
  calc ((Finset.univ.filter fun ch : P.Challenges => B.V c (prv.run c ch) = true).card : ℝ≥0)
      = ((Finset.univ.filter fun ch : P.Challenges =>
          V' c (prv.run c ch) = true ∧ (c, E.straightLine rel (Fin.last n) c (prv.run c ch)) ∉ rel).card : ℝ≥0) := by
        rw [hSame]
    _ ≤ (∑ i, ε i) * Fintype.card P.Challenges := hspec

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂} [∀ i, Fintype (P₁.Challenge i)]
  [∀ i, Fintype (P₂.Challenge i)] {ε₁ : P₁.ChallengeIdx → ℝ≥0} {ε₂ : P₂.ChallengeIdx → ℝ≥0}

open ProtocolSpec

/-- Two claim-proving phases in sequence prove the conjunction of their claims. The state is
`B₁`'s state on the part-1 transcript, held at its final value during part 2, and `B₂`'s
claim during part 1 and `B₂`'s state on the part-2 transcript during part 2. -/
def and (B₁ : ClaimProof P₁ Ctx ε₁) (B₂ : ClaimProof P₂ Ctx ε₂) :
    ClaimProof (P₁ ++ P₂) Ctx (appendError ε₁ ε₂) where
  claim c := B₁.claim c ∧ B₂.claim c
  V c tr := B₁.V c tr.left && B₂.V c tr.right
  S m c := appendState (fun k tr₁ => B₁.S k c tr₁ ∧ B₂.claim c)
    (fun tr₁ k tr₂ => B₁.S (Fin.last n₁) c tr₁ ∧ B₂.S k c tr₂) m
  start c tr hc h := by
    have h0 := appendState_of_le (fun tr₁ tr₂ h => ⟨h.1, B₂.claim_of_S h.2⟩) (k₁ := 0) rfl h
    exact hc ⟨B₁.claim_of_S h0.1, h0.2⟩
  next m hdir c tr msg hnot := by
    induction m using Fin.addCases with
    | left j =>
      intro h
      have hflip := appendState_flip_castAdd (fun tr₁ tr₂ h => ⟨h.1, B₂.claim_of_S h.2⟩) j tr msg
        hnot h
      exact B₁.next j (by simpa using hdir) c (tr.fst j.castSucc (by simp))
        (cast (append_Type_castAdd j) msg) (fun h' => hflip.1 ⟨h', hflip.2.2⟩) hflip.2.1
    | right j =>
      intro h
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j tr msg).mp ⟨hnot, h⟩
      exact B₂.next j (by simpa using hdir) c (tr.snd j.castSucc (by simp))
        (cast (append_Type_natAdd j) msg) (fun h' => hn ⟨hs.1, h'⟩) hs.2
  full c tr h := by
    rw [Bool.and_eq_true] at h
    exact (appendState_iff_of_eq_add (k₂ := Fin.last n₂) (by simp) tr).mpr
      ⟨B₁.full c _ h.1, B₂.full c _ h.2⟩
  rbr c i tr := by
    rcases ChallengeIdx.inl_or_inr i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [appendError_inl]
      refine card_le_of_mapsTo_cast (append_Challenge_inl j) (fun ch hch => ?_)
        (B₁.rbr c j (tr.fst j.1.castSucc (by simp)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      have hflip := appendState_flip_castAdd (fun tr₁ tr₂ h => ⟨h.1, B₂.claim_of_S h.2⟩) j.1 tr ch
        hch.1 hch.2
      exact ⟨fun h' => hflip.1 ⟨h', hflip.2.2⟩, hflip.2.1⟩
    · rw [appendError_inr]
      refine card_le_of_mapsTo_cast (append_Challenge_inr j) (fun ch hch => ?_)
        (B₂.rbr c j (tr.snd j.1.castSucc (by simp)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j.1 tr ch).mp hch
      exact ⟨fun h' => hn ⟨hs.1, h'⟩, hs.2⟩

variable (B₁ : ClaimProof P₁ Ctx ε₁) (B₂ : ClaimProof P₂ Ctx ε₂)

/-- The claim of the conjunction. -/
@[simp]
theorem and_claim (c : Ctx) : (B₁.and B₂).claim c ↔ B₁.claim c ∧ B₂.claim c :=
  Iff.rfl

/-- The verifier of the conjunction accepts when both verifiers accept their parts. -/
@[simp]
theorem and_V (c : Ctx) (tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))) :
    (B₁.and B₂).V c tr = (B₁.V c tr.left && B₂.V c tr.right) :=
  rfl

end ClaimProof

section AppendLeft

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂} {StmtIn WitIn : Type}

/-- **An extractor of `P₁` on the appended protocol**: `E` on the part-1 transcript, read up
to the current round during part 1 and in full during part 2.

Running time: one call of `E` on a prefix of the transcript; reading
the prefix copies at most `n₁` messages. This running time is argued here, not proved in Lean. -/
def Extractor.appendLeft (E : Extractor P₁ StmtIn WitIn) :
    Extractor (P₁ ++ P₂) StmtIn WitIn where
  extract m x tr := if h : (m : ℕ) ≤ n₁ then E ⟨m, by omega⟩ x (tr.fst ⟨m, by omega⟩ le_rfl)
    else E (Fin.last n₁) x (tr.fst (Fin.last n₁) (by simp; omega))

/-- During part 1, `E.appendLeft` is `E` on the part-1 prefix. -/
theorem Extractor.appendLeft_of_le (E : Extractor P₁ StmtIn WitIn)
    {m : Fin (n₁ + n₂ + 1)} (x : StmtIn) (tr : (P₁ ++ P₂).Transcript m) (h : (m : ℕ) ≤ n₁) :
    E.appendLeft m x tr = E ⟨m, by omega⟩ x (tr.fst ⟨m, by omega⟩ le_rfl) :=
  dite_eq_left h

end AppendLeft

namespace ClaimPhase

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂} [∀ i, Fintype (P₁.Challenge i)]
  [∀ i, Fintype (P₂.Challenge i)] [∀ i, Nonempty (P₁.Challenge i)]
  [∀ i, Nonempty (P₂.Challenge i)] {StmtIn WitIn : Type} {rel : Set (StmtIn × WitIn)}
  {ε₁ : P₁.ChallengeIdx → ℝ≥0} {ε₂ : P₂.ChallengeIdx → ℝ≥0}

open ProtocolSpec

/-- **The state function of an appended protocol**: `A.S` during part 1, and during part 2
`A.S` on the whole part-1 transcript or `B.S` on the part-2 transcript. `hclaim`: `B` proves
`A`'s claim. It is not required to be efficient (CMS19 Definition 8.5 asks only the extractor
to be). -/
def appendStateFn (A : ClaimPhase P₁ StmtIn WitIn rel ε₁)
    (B : ClaimProof P₂ (AppendContext StmtIn P₁) ε₂)
    (hclaim : ∀ x tr, B.claim ⟨x, tr⟩ ↔ A.claim x tr) :
    KnowledgeStateFunction (P := P₁ ++ P₂) fun x tr => B.V ⟨x, tr.left⟩ tr.right :=
  have h0 : ∀ x tr₁ tr₂, A.S (Fin.last n₁) x tr₁ ∨ B.S 0 ⟨x, tr₁⟩ tr₂ → A.S (Fin.last n₁) x tr₁ :=
    fun x tr₁ _ h => h.elim id fun h => A.full x tr₁ ((hclaim x tr₁).mp (B.claim_of_S h))
  { toFun := fun m x => appendState (fun k => A.S k x)
      (fun tr₁ k tr₂ => A.S (Fin.last n₁) x tr₁ ∨ B.S k ⟨x, tr₁⟩ tr₂) m
    toFun_empty := fun x tr h => A.empty x _ (appendState_of_le (h0 x) (k₁ := 0) rfl h)
    toFun_next := fun m hdir x tr msg hnot => by
      induction m using Fin.addCases with
      | left j =>
        intro h
        have hflip := appendState_flip_castAdd (h0 x) j tr msg hnot h
        exact A.next j (by simpa using hdir) x (tr.fst j.castSucc (by simp))
          (cast (append_Type_castAdd j) msg) hflip.1 hflip.2
      | right j =>
        intro h
        obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j tr msg).mp ⟨hnot, h⟩
        exact B.next j (by simpa using hdir) ⟨x, tr.fst (Fin.last n₁) (by simp)⟩
          (tr.snd j.castSucc (by simp)) (cast (append_Type_natAdd j) msg) (fun h' => hn (.inr h'))
          (hs.resolve_left fun h' => hn (.inl h'))
    toFun_full := fun x tr h =>
      (appendState_iff_of_eq_add (k₂ := Fin.last n₂) (by simp) tr).mpr
        (.inr (B.full ⟨x, tr.left⟩ tr.right h)) }

omit [∀ i, Nonempty (P₁.Challenge i)] [∀ i, Nonempty (P₂.Challenge i)] in
/-- The state of the appended protocol, as an `appendState`. -/
theorem appendStateFn_toFun (A : ClaimPhase P₁ StmtIn WitIn rel ε₁)
    (B : ClaimProof P₂ (AppendContext StmtIn P₁) ε₂)
    (hclaim : ∀ x tr, B.claim ⟨x, tr⟩ ↔ A.claim x tr) (m : Fin (n₁ + n₂ + 1)) (x : StmtIn)
    (tr : (P₁ ++ P₂).Transcript m) :
    (A.appendStateFn B hclaim).toFun m x tr = appendState (fun k => A.S k x)
      (fun tr₁ k tr₂ => A.S (Fin.last n₁) x tr₁ ∨ B.S k ⟨x, tr₁⟩ tr₂) m tr :=
  rfl

/-- **Append.** A claim-producing phase followed by a phase proving its claim is
round-by-round knowledge sound for the verifier of the second phase, at the extractor
`A.E.appendLeft` and the state function `appendStateFn`, and each round keeps its error. -/
theorem append_rbrKnowledgeSoundness (A : ClaimPhase P₁ StmtIn WitIn rel ε₁)
    (B : ClaimProof P₂ (AppendContext StmtIn P₁) ε₂)
    (hclaim : ∀ x tr, B.claim ⟨x, tr⟩ ↔ A.claim x tr) :
    rbrKnowledgeSoundness rel (fun x tr => B.V ⟨x, tr.left⟩ tr.right)
      A.E.appendLeft (A.appendStateFn B hclaim) (appendError ε₁ ε₂) := by
  have h0 : ∀ x tr₁ tr₂, A.S (Fin.last n₁) x tr₁ ∨ B.S 0 ⟨x, tr₁⟩ tr₂ → A.S (Fin.last n₁) x tr₁ :=
    fun x tr₁ _ h => h.elim id fun h => A.full x tr₁ ((hclaim x tr₁).mp (B.claim_of_S h))
  refine rbrKnowledgeSoundness_iff_count.mpr ?_
  intro x i tr
  rcases ChallengeIdx.inl_or_inr i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [appendError_inl]
    refine card_le_of_mapsTo_cast (append_Challenge_inl j) (fun c hc => ?_)
      (A.rbr x j (tr.fst j.1.castSucc (by simp)))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    simp only [appendStateFn_toFun] at hc
    have hflip := appendState_flip_castAdd (h0 x) j.1 tr c hc.2.1 hc.2.2
    refine ⟨?_, hflip.1, hflip.2⟩
    have hle : ((ChallengeIdx.inl (P₂ := P₂) j).1.castSucc : ℕ) ≤ n₁ := by simp
    have hE := hc.1
    rw [A.E.appendLeft_of_le x tr hle] at hE
    exact hE
  · rw [appendError_inr]
    refine card_le_of_mapsTo_cast (append_Challenge_inr j) (fun c hc => ?_)
      (B.rbr ⟨x, tr.fst (Fin.last n₁) (by simp)⟩ j (tr.snd j.1.castSucc (by simp)))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    simp only [appendStateFn_toFun] at hc
    obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j.1 tr c).mp hc.2
    exact ⟨fun h' => hn (.inr h'), hs.resolve_left fun h' => hn (.inl h')⟩

open Classical in
/-- **Append**, knowledge soundness: the error is the sum of the two phases' round errors, at
the straight-line extractor of `A.E.appendLeft`. -/
theorem append_knowledgeSoundness (A : ClaimPhase P₁ StmtIn WitIn rel ε₁)
    (B : ClaimProof P₂ (AppendContext StmtIn P₁) ε₂)
    (hclaim : ∀ x tr, B.claim ⟨x, tr⟩ ↔ A.claim x tr) :
    knowledgeSoundness rel (fun x tr => B.V ⟨x, tr.left⟩ tr.right)
      (A.E.appendLeft.straightLine rel) (∑ i, ε₁ i + ∑ j, ε₂ j) := by
  rw [← sum_appendError]
  exact knowledgeSoundness_of_rbr (A.append_rbrKnowledgeSoundness B hclaim)

end ClaimPhase

/-! ### Claim-proving phases: reading, guarding, weakening -/

section ClaimProofOps

variable {P : ProtocolSpec n} [∀ i, Fintype (P.Challenge i)] {ε : P.ChallengeIdx → ℝ≥0}
  {Ctx Ctx' : Type}

/-- A claim-proving phase read along a map of contexts. -/
def ClaimProof.comap (B : ClaimProof P Ctx ε) (f : Ctx' → Ctx) : ClaimProof P Ctx' ε where
  claim c := B.claim (f c)
  V c := B.V (f c)
  S m c := B.S m (f c)
  start c := B.start (f c)
  next m hdir c := B.next m hdir (f c)
  full c := B.full (f c)
  rbr c := B.rbr (f c)

@[simp]
theorem ClaimProof.comap_claim (B : ClaimProof P Ctx ε) (f : Ctx' → Ctx) (c : Ctx') :
    (B.comap f).claim c ↔ B.claim (f c) :=
  Iff.rfl

@[simp]
theorem ClaimProof.comap_V (B : ClaimProof P Ctx ε) (f : Ctx' → Ctx) (c : Ctx') :
    (B.comap f).V c = B.V (f c) :=
  rfl

/-- A claim-proving phase whose verifier first checks a condition `ok` on the context alone:
claim `ok c ∧ B.claim c`, verifier `ok c && B.V c tr`, state `ok c ∧ B.S m c tr`, the same
errors. -/
def ClaimProof.guard (B : ClaimProof P Ctx ε) (ok : Ctx → Bool) : ClaimProof P Ctx ε where
  claim c := ok c = true ∧ B.claim c
  V c tr := ok c && B.V c tr
  S m c tr := ok c = true ∧ B.S m c tr
  start c tr hc hs := hc ⟨hs.1, B.claim_of_S hs.2⟩
  next m hdir c tr msg hn hs := by
    refine hn ⟨hs.1, ?_⟩
    by_contra h
    exact B.next m hdir c tr msg h hs.2
  full c tr h := by
    rw [Bool.and_eq_true] at h
    exact ⟨h.1, B.full c tr h.2⟩
  rbr c i tr := by
    classical
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun ch hch => ?_)) (B.rbr c i tr)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
    exact ⟨fun h => hch.1 ⟨hch.2.1, h⟩, hch.2.2⟩

@[simp]
theorem ClaimProof.guard_claim (B : ClaimProof P Ctx ε) (ok : Ctx → Bool) (c : Ctx) :
    (B.guard ok).claim c ↔ ok c = true ∧ B.claim c :=
  Iff.rfl

@[simp]
theorem ClaimProof.guard_V (B : ClaimProof P Ctx ε) (ok : Ctx → Bool) (c : Ctx) :
    (B.guard ok).V c = fun tr => ok c && B.V c tr :=
  rfl

/-- A proof sound relative to a claim is sound relative to any weaker claim: the same
verifier, state and errors, since a false weaker claim makes the stronger one false. -/
def ClaimProof.weaken {m : ℕ} {Q : ProtocolSpec m} [∀ i, Fintype (Q.Challenge i)]
    {δ : Q.ChallengeIdx → ℝ≥0} {C : Type} (B : ClaimProof Q C δ) (claim' : C → Prop)
    (h : ∀ c, B.claim c → claim' c) : ClaimProof Q C δ where
  claim := claim'
  V := B.V
  S := B.S
  start c tr hc := B.start c tr fun hB => hc (h c hB)
  next := B.next
  full := B.full
  rbr := B.rbr

/-- A proof with the challenge types enumerated by other `Fintype` instances: the same claim,
verifier and state, since the counts do not depend on the enumeration. -/
def ClaimProof.ofFintype {m : ℕ} {Q : ProtocolSpec m} {C : Type} {δ : Q.ChallengeIdx → ℝ≥0}
    (inst inst' : ∀ i, Fintype (Q.Challenge i)) (B : @ClaimProof m Q C inst δ) :
    @ClaimProof m Q C inst' δ :=
  @ClaimProof.mk m Q C inst' δ (@ClaimProof.claim m Q C inst δ B) (@ClaimProof.V m Q C inst δ B)
    (@ClaimProof.S m Q C inst δ B) (@ClaimProof.start m Q C inst δ B)
    (@ClaimProof.next m Q C inst δ B) (@ClaimProof.full m Q C inst δ B) fun c i tr => by
      have h := @ClaimProof.rbr m Q C inst δ B c i tr
      have e : inst' = inst := Subsingleton.elim _ _
      subst e
      exact h

@[simp] theorem ClaimProof.ofFintype_V {m : ℕ} {Q : ProtocolSpec m} {C : Type}
    {δ : Q.ChallengeIdx → ℝ≥0} (inst inst' : ∀ i, Fintype (Q.Challenge i))
    (B : @ClaimProof m Q C inst δ) :
    @ClaimProof.V m Q C inst' δ (ClaimProof.ofFintype inst inst' B) =
      @ClaimProof.V m Q C inst δ B :=
  rfl

@[simp] theorem ClaimProof.ofFintype_claim {m : ℕ} {Q : ProtocolSpec m} {C : Type}
    {δ : Q.ChallengeIdx → ℝ≥0} (inst inst' : ∀ i, Fintype (Q.Challenge i))
    (B : @ClaimProof m Q C inst δ) :
    @ClaimProof.claim m Q C inst' δ (ClaimProof.ofFintype inst inst' B) =
      @ClaimProof.claim m Q C inst δ B :=
  rfl

/-- `B` with its verifier replaced by the equal verifier `V`. -/
def ClaimProof.withV (B : ClaimProof P Ctx ε) (V : Ctx → P.Transcript (Fin.last n) → Bool)
    (h : ∀ c tr, B.V c tr = V c tr) : ClaimProof P Ctx ε where
  claim := B.claim
  V := V
  S := B.S
  start := B.start
  next := B.next
  full c tr hV := B.full c tr ((h c tr).trans hV)
  rbr := B.rbr

end ClaimProofOps

/-! ### Prefixes of transcripts before a challenge round -/

section Prefix

variable {P : ProtocolSpec n}

/-- A transcript of the first `j + 1` rounds is its first `j` rounds with round `j` appended. -/
theorem ProtocolSpec.concat_take_succ {j : Fin n} (tr : P.Transcript j.succ) :
    P.concat (tr.take j.castSucc (Fin.castSucc_le_succ j)) (tr ⟨j, by simp⟩) = tr := by
  funext i
  by_cases hi : (i : ℕ) < j
  · exact (P.concat_apply_of_lt _ _ i hi).trans rfl
  · have h2 : (i : ℕ) < j + 1 := by simpa using i.2
    have e : i = ⟨j, by simp⟩ := Fin.ext (by simp only; omega)
    subst e
    exact P.concat_apply_last _ _

/-- At a prover round, the challenges drawn by the next prefix were drawn by the current one. -/
theorem ProtocolSpec.succ_le_castSucc_of_message {k : Fin n} (hk : P.dir k = .P_to_V)
    {j : P.ChallengeIdx} (h : j.1.succ ≤ k.succ) : j.1.succ ≤ k.castSucc := by
  have hne : j.1 ≠ k := fun e => by
    have := j.2
    rw [e, hk] at this
    cases this
  rw [Fin.le_def] at h ⊢
  simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
  have : (j.1 : ℕ) ≠ k := fun e => hne (Fin.ext e)
  omega

/-- **Before the first challenge round the state gives the claim**: prover rounds never make the
state true, so a state true at a prefix that precedes every challenge round was true on the empty
transcript. -/
theorem ClaimProof.claim_of_S_before {Ctx : Type} [∀ i, Fintype (P.Challenge i)]
    {ε : P.ChallengeIdx → ℝ≥0} (B : ClaimProof P Ctx ε) {c : Ctx} :
    ∀ {k : Fin (n + 1)}, (∀ i : P.ChallengeIdx, k ≤ i.1.castSucc) → ∀ {tr : P.Transcript k},
      B.S k c tr → B.claim c := by
  intro k
  induction k using Fin.induction with
  | zero => exact fun _ tr h => B.claim_of_S h
  | succ j ih =>
    intro hk tr h
    have hdir : P.dir j = .P_to_V := by
      cases hd : P.dir j with
      | P_to_V => rfl
      | V_to_P =>
        have := hk ⟨j, hd⟩
        rw [Fin.le_def] at this
        simp at this
    refine ih (fun i => (Fin.castSucc_le_succ j).trans (hk i)) (tr := tr.take j.castSucc
      (Fin.castSucc_le_succ j)) ?_
    by_contra hn
    exact B.next j hdir c _ (tr ⟨j, by simp⟩) hn ((P.concat_take_succ tr).symm ▸ h)

/-- **A full transcript up to and including the challenge round `j`.** -/
abbrev ProtocolSpec.Transcript.upTo (tr : P.Transcript (Fin.last n)) (j : P.ChallengeIdx) :
    P.Transcript j.1.succ :=
  tr.take j.1.succ (Fin.le_last _)

/-- **Every prefix extends to a full transcript** when every round's type is nonempty. -/
theorem ProtocolSpec.Transcript.exists_take_eq [∀ i, Nonempty (P.Type i)] {k : Fin (n + 1)}
    (trp : P.Transcript k) : ∃ tr : P.Transcript (Fin.last n), tr.take k (Fin.le_last k) = trp := by
  classical
  refine ⟨fun i => if h : (i : ℕ) < k then trp ⟨i, h⟩ else Classical.arbitrary _, ?_⟩
  funext i
  simp only [ProtocolSpec.Transcript.take, Fin.val_castLE, i.isLt, dite_true]

/-- A full transcript whose prefix up to the challenge round `j` is `trp` followed by `c` agrees
with `trp` before round `j`. -/
theorem ProtocolSpec.Transcript.apply_of_upTo_eq_concat {tr : P.Transcript (Fin.last n)}
    {j : P.ChallengeIdx} {trp : P.Transcript j.1.castSucc} {c : P.Challenge j}
    (h : tr.upTo j = P.concat trp c) (i : ℕ) (hi : i < j.1) :
    tr ⟨i, by simp only [Fin.val_last]; omega⟩ = trp ⟨i, hi⟩ := by
  have := congrFun h ⟨i, by simp only [Fin.val_succ]; omega⟩
  rw [ProtocolSpec.concat_apply_of_lt trp c i hi] at this
  exact this

/-- A full transcript whose prefix up to the challenge round `j` is `trp` followed by `c` has `c`
at round `j`. -/
theorem ProtocolSpec.Transcript.apply_of_upTo_eq_concat_self {tr : P.Transcript (Fin.last n)}
    {j : P.ChallengeIdx} {trp : P.Transcript j.1.castSucc} {c : P.Challenge j}
    (h : tr.upTo j = P.concat trp c) : tr j.1 = c := by
  have := congrFun h ⟨j.1, by simp⟩
  rw [ProtocolSpec.concat_apply_last trp c] at this
  exact this

/-- **A challenge has been drawn** before the prefix of length `k`. -/
def ChallengeDrawn (P : ProtocolSpec n) (k : Fin (n + 1)) : Prop :=
  ∃ j : P.ChallengeIdx, j.1.succ ≤ k

/-- A prover message draws no challenge. -/
theorem challengeDrawn_succ_of_message {k : Fin n} (hk : P.dir k = .P_to_V)
    (h : ChallengeDrawn P k.succ) : ChallengeDrawn P k.castSucc :=
  h.imp fun _ hj => ProtocolSpec.succ_le_castSucc_of_message hk hj

/-- No challenge drawn before `k` means every challenge round is at or after `k`. -/
theorem le_of_not_challengeDrawn {k : Fin (n + 1)} (h : ¬ ChallengeDrawn P k) (i : P.ChallengeIdx) :
    k ≤ i.1.castSucc := by
  by_contra hlt
  rw [not_le, Fin.lt_def] at hlt
  refine h ⟨i, ?_⟩
  rw [Fin.le_def]
  simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
  omega

/-- **The knowledge state function of a claim-proving phase**: once a challenge has been drawn,
the claim or the phase's state. The challenge condition makes the state false on the empty
transcript even when the claim holds. Not required to be efficient. -/
def ClaimProof.stateFn {Ctx : Type} [∀ i, Fintype (P.Challenge i)] [Nonempty P.ChallengeIdx]
    {ε : P.ChallengeIdx → ℝ≥0} (B : ClaimProof P Ctx ε) : KnowledgeStateFunction B.V where
  toFun k c tr := ChallengeDrawn P k ∧ (B.claim c ∨ B.S k c tr)
  toFun_empty _ _ h := by
    obtain ⟨⟨j, hj⟩, -⟩ := h
    exact absurd hj (by simp)
  toFun_next k hk c tr msg hnot h := by
    refine hnot ⟨challengeDrawn_succ_of_message hk h.1, h.2.imp id fun hS => ?_⟩
    by_contra hS'
    exact B.next k hk c tr msg hS' hS
  toFun_full c tr hV := by
    obtain ⟨j⟩ := ‹Nonempty P.ChallengeIdx›
    exact ⟨⟨j, Fin.le_last _⟩, .inr (B.full c tr hV)⟩

/-- **Round-by-round knowledge soundness of a claim-proving phase**, at its state function
`stateFn` and any extractor `E` that succeeds whenever the claim holds (`hE`), with the phase's
own round errors: while the extractor fails the claim is false, so the state flips only when the
phase's state flips. -/
theorem ClaimProof.rbrKnowledgeSoundness {Ctx W : Type} [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] [Nonempty P.ChallengeIdx] {ε : P.ChallengeIdx → ℝ≥0}
    (B : ClaimProof P Ctx ε) {rel : Set (Ctx × W)} (E : Extractor P Ctx W)
    (hE : ∀ k c tr, B.claim c → (c, E k c tr) ∈ rel) :
    IOP.rbrKnowledgeSoundness rel B.V E B.stateFn ε := by
  classical
  refine rbrKnowledgeSoundness_iff_count.mpr fun c i tr => ?_
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun ch hch => ?_)) (B.rbr c i tr)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
  obtain ⟨hrel, hnot, hd, hs⟩ := hch
  have hclaim : ¬ B.claim c := fun h => hrel (hE _ c tr h)
  refine ⟨fun hS => ?_, hs.resolve_left hclaim⟩
  by_cases hdr : ChallengeDrawn P i.1.castSucc
  · exact hnot ⟨hdr, .inr hS⟩
  · exact hclaim (B.claim_of_S_before (le_of_not_challengeDrawn hdr) hS)

end Prefix

end GordieHowe.IOP
