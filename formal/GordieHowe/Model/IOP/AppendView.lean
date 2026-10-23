-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.HVZK
public import GordieHowe.Model.IOP.CompletenessAppend

@[expose] public section

/-!
# Views of an appended protocol

The prover messages of `P₁ ++ P₂` are those of `P₁` followed by those of
`P₂` (`messageIdxEquiv`). Message views for each part, all reading the
challenges of some common type `Ch` (typically the appended protocol's, so an
earlier message may be queried by a later round), give the views of the
appended protocol (`appendMsg`). Its view is the pair of the parts' views
(`appendViewEquiv`), and on a joined transcript that pair is the parts' views
of the two transcripts (`appendViewEquiv_see`).
-/

namespace GordieHowe.IOP

open ProtocolSpec

variable {n₁ n₂ : ℕ} {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}

namespace ProtocolSpec

/-- A prover round of the first part, as a prover round of the appended protocol. -/
def MessageIdx.inl (j : P₁.MessageIdx) : (P₁ ++ P₂).MessageIdx :=
  ⟨Fin.castAdd n₂ j.1, (append_dir_castAdd j.1).trans j.2⟩

/-- A prover round of the second part, as a prover round of the appended protocol. -/
def MessageIdx.inr (j : P₂.MessageIdx) : (P₁ ++ P₂).MessageIdx :=
  ⟨Fin.natAdd n₁ j.1, (append_dir_natAdd j.1).trans j.2⟩

theorem MessageIdx.val_inl (j : P₁.MessageIdx) :
    (MessageIdx.inl (P₂ := P₂) j).1 = Fin.castAdd n₂ j.1 := rfl

theorem MessageIdx.val_inr (j : P₂.MessageIdx) :
    (MessageIdx.inr (P₁ := P₁) j).1 = Fin.natAdd n₁ j.1 := rfl

/-- Prover rounds are equal when their round indices are. -/
theorem MessageIdx.ext {n : ℕ} {P : ProtocolSpec n} {i i' : P.MessageIdx} (h : i.1 = i'.1) : i = i' :=
  Subtype.ext h

/-- The prover round of `P₁` or of `P₂` that a prover round of the appended protocol is. -/
def MessageIdx.toSum (i : (P₁ ++ P₂).MessageIdx) : P₁.MessageIdx ⊕ P₂.MessageIdx :=
  if h : (i.1 : ℕ) < n₁ then
    .inl ⟨⟨i.1, h⟩, (append_dir_castAdd (P₂ := P₂) ⟨i.1, h⟩).symm.trans i.2⟩
  else
    .inr ⟨⟨i.1 - n₁, by omega⟩, by
      have e : Fin.natAdd n₁ ⟨i.1 - n₁, by omega⟩ = i.1 :=
        Fin.ext (by simp only [Fin.val_natAdd]; omega)
      rw [← append_dir_natAdd (P₁ := P₁), e]
      exact i.2⟩

theorem MessageIdx.toSum_inl (j : P₁.MessageIdx) :
    (MessageIdx.inl (P₂ := P₂) j).toSum = .inl j := by
  rw [MessageIdx.toSum, dite_eq_left (by simp [MessageIdx.val_inl])]
  rfl

theorem MessageIdx.toSum_inr (j : P₂.MessageIdx) :
    (MessageIdx.inr (P₁ := P₁) j).toSum = .inr j := by
  rw [MessageIdx.toSum, dite_eq_right (by simp [MessageIdx.val_inr])]
  congr 1
  exact MessageIdx.ext (Fin.ext (show n₁ + (j.1 : ℕ) - n₁ = j.1 by omega))

/-- The prover rounds of the appended protocol are those of the two parts. -/
def messageIdxEquiv : (P₁ ++ P₂).MessageIdx ≃ P₁.MessageIdx ⊕ P₂.MessageIdx where
  toFun := MessageIdx.toSum
  invFun := Sum.elim MessageIdx.inl MessageIdx.inr
  left_inv i := by
    rw [MessageIdx.toSum]
    split_ifs with h
    · rfl
    · exact MessageIdx.ext (Fin.ext (by
        change n₁ + ((i.1 : ℕ) - n₁) = i.1
        omega))
  right_inv s := by
    rcases s with j | j
    · exact MessageIdx.toSum_inl j
    · exact MessageIdx.toSum_inr j

@[simp] theorem messageIdxEquiv_inl (j : P₁.MessageIdx) :
    messageIdxEquiv (MessageIdx.inl (P₂ := P₂) j) = .inl j := MessageIdx.toSum_inl j

@[simp] theorem messageIdxEquiv_inr (j : P₂.MessageIdx) :
    messageIdxEquiv (MessageIdx.inr (P₁ := P₁) j) = .inr j := MessageIdx.toSum_inr j

/-- A prover round of the appended protocol that `messageIdxEquiv` sends to a
`P₁` round is that round. -/
theorem MessageIdx.eq_inl_of_equiv {i : (P₁ ++ P₂).MessageIdx} {j : P₁.MessageIdx}
    (h : messageIdxEquiv i = .inl j) : i = MessageIdx.inl j :=
  (messageIdxEquiv.symm_apply_eq.mpr h.symm).symm

/-- A prover round of the appended protocol that `messageIdxEquiv` sends to a
`P₂` round is that round. -/
theorem MessageIdx.eq_inr_of_equiv {i : (P₁ ++ P₂).MessageIdx} {j : P₂.MessageIdx}
    (h : messageIdxEquiv i = .inr j) : i = MessageIdx.inr j :=
  (messageIdxEquiv.symm_apply_eq.mpr h.symm).symm

/-- Two full transcripts with the same challenges and the same prover messages
are equal. -/
theorem Transcript.ext_of_messages {n : ℕ} {P : ProtocolSpec n}
    {tr tr' : P.Transcript (Fin.last n)} {ch : P.Challenges} (h : ∀ i : P.ChallengeIdx, tr i.1 = ch i)
    (h' : ∀ i : P.ChallengeIdx, tr' i.1 = ch i) (hm : ∀ i : P.MessageIdx, tr i.1 = tr' i.1) :
    tr = tr' := by
  funext i
  cases hd : P.dir i with
  | P_to_V => exact hm ⟨i, hd⟩
  | V_to_P => exact (h ⟨i, hd⟩).trans (h' ⟨i, hd⟩).symm

/-- Joining the two parts of a full transcript gives it back. -/
@[simp] theorem Transcript.join_left_right (tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))) :
    Transcript.join tr.left tr.right = tr := by
  funext i
  induction i using Fin.addCases with
  | left j =>
    rw [Transcript.join_left]
    change cast _ (cast (append_Type_castAdd j) (tr (Fin.castAdd n₂ j))) = _
    rw [cast_cast, cast_eq]
  | right j =>
    rw [Transcript.join_right]
    change cast _ (cast (append_Type_natAdd j) (tr (Fin.natAdd n₁ j))) = _
    rw [cast_cast, cast_eq]

/-- The part-1 transcript of a full transcript with the challenges `ch` has the
challenges `ch.left`. -/
theorem Transcript.left_challenge {tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))}
    {ch : (P₁ ++ P₂).Challenges} (h : ∀ i : (P₁ ++ P₂).ChallengeIdx, tr i.1 = ch i)
    (j : P₁.ChallengeIdx) : tr.left j.1 = ch.left j := by
  change cast (append_Type_castAdd j.1) (tr (ChallengeIdx.inl (P₂ := P₂) j).1) =
    cast (append_Challenge_inl j) (ch (ChallengeIdx.inl j))
  rw [h]
  rfl

/-- The part-2 transcript of a full transcript with the challenges `ch` has the
challenges `ch.right`. -/
theorem Transcript.right_challenge {tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))}
    {ch : (P₁ ++ P₂).Challenges} (h : ∀ i : (P₁ ++ P₂).ChallengeIdx, tr i.1 = ch i)
    (j : P₂.ChallengeIdx) : tr.right j.1 = ch.right j := by
  change cast (append_Type_natAdd j.1) (tr (ChallengeIdx.inr (P₁ := P₁) j).1) =
    cast (append_Challenge_inr j) (ch (ChallengeIdx.inr j))
  rw [h]
  rfl

end ProtocolSpec

namespace MessageView

variable {M M' Ch ι A : Type}

/-- The same table, read on a message type equal to `M`. -/
def castMsg (O : MessageView M Ch ι A) (e : M' = M) : MessageView M' Ch ι A where
  read m := O.read (cast e m)
  read_injective _ _ h := (cast_inj e).mp (O.read_injective h)
  decEq := O.decEq
  queries := O.queries

@[simp] theorem see_castMsg (O : MessageView M Ch ι A) (e : M' = M) (ch : Ch) (m : M') :
    (O.castMsg e).see ch m = O.see ch (cast e m) := rfl

/-- A decoder read on a message type equal to `M`. -/
def Decoder.castMsg {O : MessageView M Ch ι A} (D : O.Decoder) (e : M' = M) :
    (O.castMsg e).Decoder where
  dec ch v := (D.dec ch v).map (cast e.symm)
  dec_see ch m := by
    rw [see_castMsg, D.dec_see, Option.map_some, cast_cast, cast_eq]

end MessageView

variable {Ch : Type} {Idx₁ Ans₁ : P₁.MessageIdx → Type} {Idx₂ Ans₂ : P₂.MessageIdx → Type}

/-- A family of types on the appended protocol's prover rounds, from a family
on each part. -/
def appendFamily (T₁ : P₁.MessageIdx → Type) (T₂ : P₂.MessageIdx → Type)
    (i : (P₁ ++ P₂).MessageIdx) : Type :=
  Sum.elim T₁ T₂ (messageIdxEquiv i)

/-- The view of prover round `i` of the appended protocol, given the round `s`
of a part that it is. -/
def appendMsgOf (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j))
    (i : (P₁ ++ P₂).MessageIdx) :
    ∀ s, messageIdxEquiv i = s → MessageView ((P₁ ++ P₂).Type i.1) Ch
      (Sum.elim Idx₁ Idx₂ s) (Sum.elim Ans₁ Ans₂ s)
  | .inl j, h => (msg₁ j).castMsg
      ((congrArg (fun i : (P₁ ++ P₂).MessageIdx => (P₁ ++ P₂).Type i.1)
        (MessageIdx.eq_inl_of_equiv h)).trans (append_Type_castAdd j.1))
  | .inr j, h => (msg₂ j).castMsg
      ((congrArg (fun i : (P₁ ++ P₂).MessageIdx => (P₁ ++ P₂).Type i.1)
        (MessageIdx.eq_inr_of_equiv h)).trans (append_Type_natAdd j.1))

/-- The message views of an appended protocol from the views of each part's
messages. -/
def appendMsg (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)) :
    ∀ i : (P₁ ++ P₂).MessageIdx, MessageView ((P₁ ++ P₂).Type i.1) Ch
      (appendFamily Idx₁ Idx₂ i) (appendFamily Ans₁ Ans₂ i) :=
  fun i => appendMsgOf msg₁ msg₂ i (messageIdxEquiv i) rfl

/-- Decoders of the appended views at the round `s` of a part, from decoders of the parts'
views on the rounds where a predicate holds. -/
def appendDecoderOf {msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j)}
    {msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)}
    {p₁ : P₁.MessageIdx → Prop} {p₂ : P₂.MessageIdx → Prop}
    (D₁ : ∀ j, p₁ j → (msg₁ j).Decoder) (D₂ : ∀ j, p₂ j → (msg₂ j).Decoder)
    (i : (P₁ ++ P₂).MessageIdx) :
    ∀ s (h : messageIdxEquiv i = s), Sum.elim p₁ p₂ s → (appendMsgOf msg₁ msg₂ i s h).Decoder
  | .inl j, _, hp => (D₁ j hp).castMsg _
  | .inr j, _, hp => (D₂ j hp).castMsg _

/-- **Decoders of the appended views**, at the rounds of the parts where the parts' views have
decoders. -/
def appendDecoder {msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j)}
    {msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)}
    {p₁ : P₁.MessageIdx → Prop} {p₂ : P₂.MessageIdx → Prop}
    (D₁ : ∀ j, p₁ j → (msg₁ j).Decoder) (D₂ : ∀ j, p₂ j → (msg₂ j).Decoder)
    (i : (P₁ ++ P₂).MessageIdx) (hi : Sum.elim p₁ p₂ (messageIdxEquiv i)) :
    (appendMsg msg₁ msg₂ i).Decoder :=
  appendDecoderOf D₁ D₂ i _ rfl hi

variable (Idx₁ Ans₁ Idx₂ Ans₂) in
/-- The type of what the verifier sees of a message at the round `s` of a part. -/
abbrev appendSeen (s : P₁.MessageIdx ⊕ P₂.MessageIdx) : Type :=
  Sum.elim Idx₁ Idx₂ s → Option (Sum.elim Ans₁ Ans₂ s)

theorem appendMsg_see_of_eq
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)) (ch : Ch)
    (i : (P₁ ++ P₂).MessageIdx) (s : P₁.MessageIdx ⊕ P₂.MessageIdx)
    (h : messageIdxEquiv i = s) (m : (P₁ ++ P₂).Type i.1) :
    cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) h) ((appendMsg msg₁ msg₂ i).see ch m) =
      (appendMsgOf msg₁ msg₂ i s h).see ch m := by
  subst h
  rfl

/-- On a part-1 round, the appended view is the part-1 view of the message. -/
theorem appendMsg_see_inl
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)) (ch : Ch)
    (j : P₁.MessageIdx) (m : (P₁ ++ P₂).Type (Fin.castAdd n₂ j.1)) :
    cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (messageIdxEquiv_inl j))
        ((appendMsg msg₁ msg₂ (MessageIdx.inl j)).see ch m) =
      (msg₁ j).see ch (cast (append_Type_castAdd j.1) m) :=
  appendMsg_see_of_eq msg₁ msg₂ ch (MessageIdx.inl j) (.inl j) (messageIdxEquiv_inl j) m

/-- On a part-2 round, the appended view is the part-2 view of the message. -/
theorem appendMsg_see_inr
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)) (ch : Ch)
    (j : P₂.MessageIdx) (m : (P₁ ++ P₂).Type (Fin.natAdd n₁ j.1)) :
    cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (messageIdxEquiv_inr j))
        ((appendMsg msg₁ msg₂ (MessageIdx.inr j)).see ch m) =
      (msg₂ j).see ch (cast (append_Type_natAdd j.1) m) :=
  appendMsg_see_of_eq msg₁ msg₂ ch (MessageIdx.inr j) (.inr j) (messageIdxEquiv_inr j) m

/-- What the verifier sees at a part-1 round of the appended protocol, as the part's seen
entries. -/
def appendSeenInl (j : P₁.MessageIdx)
    (v : appendFamily Idx₁ Idx₂ (MessageIdx.inl (P₂ := P₂) j) →
      Option (appendFamily Ans₁ Ans₂ (MessageIdx.inl (P₂ := P₂) j))) : Idx₁ j → Option (Ans₁ j) :=
  cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (messageIdxEquiv_inl j)) v

/-- What the verifier sees at a part-2 round of the appended protocol, as the part's seen
entries. -/
def appendSeenInr (j : P₂.MessageIdx)
    (v : appendFamily Idx₁ Idx₂ (MessageIdx.inr (P₁ := P₁) j) →
      Option (appendFamily Ans₁ Ans₂ (MessageIdx.inr (P₁ := P₁) j))) : Idx₂ j → Option (Ans₂ j) :=
  cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (messageIdxEquiv_inr j)) v

theorem appendSeenInl_see
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)) (ch : Ch)
    (j : P₁.MessageIdx) (m : (P₁ ++ P₂).Type (Fin.castAdd n₂ j.1)) :
    appendSeenInl j ((appendMsg msg₁ msg₂ (MessageIdx.inl j)).see ch m) =
      (msg₁ j).see ch (cast (append_Type_castAdd j.1) m) :=
  appendMsg_see_inl msg₁ msg₂ ch j m

theorem appendSeenInr_see
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)) (ch : Ch)
    (j : P₂.MessageIdx) (m : (P₁ ++ P₂).Type (Fin.natAdd n₁ j.1)) :
    appendSeenInr j ((appendMsg msg₁ msg₂ (MessageIdx.inr j)).see ch m) =
      (msg₂ j).see ch (cast (append_Type_natAdd j.1) m) :=
  appendMsg_see_inr msg₁ msg₂ ch j m

/-- A predicate on the rounds of the parts holds at a round of the appended protocol when it
holds at that round read in its part. -/
theorem sumElim_messageIdxEquiv {p₁ : P₁.MessageIdx → Prop} {p₂ : P₂.MessageIdx → Prop}
    {i : (P₁ ++ P₂).MessageIdx} (h₁ : ∀ j, i = MessageIdx.inl j → p₁ j)
    (h₂ : ∀ j, i = MessageIdx.inr j → p₂ j) : Sum.elim p₁ p₂ (messageIdxEquiv i) := by
  rcases h : messageIdxEquiv i with j | j
  · exact h₁ j (MessageIdx.eq_inl_of_equiv h)
  · exact h₂ j (MessageIdx.eq_inr_of_equiv h)

/-- On a part-1 round, the appended view determines the message when the part-1 view does. -/
theorem appendMsg_seeInjective_inl
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j))
    (j : P₁.MessageIdx) (h : (msg₁ j).SeeInjective) :
    (appendMsg msg₁ msg₂ (MessageIdx.inl j)).SeeInjective := fun ch m m' hm => by
  have e := congrArg (cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (messageIdxEquiv_inl j))) hm
  have e' := (appendMsg_see_inl msg₁ msg₂ ch j m).symm.trans
    (e.trans (appendMsg_see_inl msg₁ msg₂ ch j m'))
  exact (cast_inj _).1 (h ch _ _ e')

/-- On a part-2 round, the appended view determines the message when the part-2 view does. -/
theorem appendMsg_seeInjective_inr
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j))
    (j : P₂.MessageIdx) (h : (msg₂ j).SeeInjective) :
    (appendMsg msg₁ msg₂ (MessageIdx.inr j)).SeeInjective := fun ch m m' hm => by
  have e := congrArg (cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (messageIdxEquiv_inr j))) hm
  have e' := (appendMsg_see_inr msg₁ msg₂ ch j m).symm.trans
    (e.trans (appendMsg_see_inr msg₁ msg₂ ch j m'))
  exact (cast_inj _).1 (h ch _ _ e')

/-- The view of an appended protocol is the pair of the parts' views. -/
def appendViewEquiv :
    (∀ i : (P₁ ++ P₂).MessageIdx,
        appendFamily Idx₁ Idx₂ i → Option (appendFamily Ans₁ Ans₂ i)) ≃
      (∀ j : P₁.MessageIdx, Idx₁ j → Option (Ans₁ j)) ×
        (∀ j : P₂.MessageIdx, Idx₂ j → Option (Ans₂ j)) :=
  (Equiv.piCongrLeft (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) messageIdxEquiv).trans
    (Equiv.sumPiEquivProdPi _)

/-- The part-1 view of an appended view, round by round. -/
theorem appendViewEquiv_apply_fst
    (v : ∀ i : (P₁ ++ P₂).MessageIdx,
      appendFamily Idx₁ Idx₂ i → Option (appendFamily Ans₁ Ans₂ i)) (j : P₁.MessageIdx) :
    (appendViewEquiv v).1 j =
      cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (messageIdxEquiv_inl j))
        (v (MessageIdx.inl j)) :=
  Equiv.piCongrLeft_apply_eq_cast (P := appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (e := messageIdxEquiv) v
    (Sum.inl j)

/-- The part-2 view of an appended view, round by round. -/
theorem appendViewEquiv_apply_snd
    (v : ∀ i : (P₁ ++ P₂).MessageIdx,
      appendFamily Idx₁ Idx₂ i → Option (appendFamily Ans₁ Ans₂ i)) (j : P₂.MessageIdx) :
    (appendViewEquiv v).2 j =
      cast (congrArg (appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (messageIdxEquiv_inr j))
        (v (MessageIdx.inr j)) :=
  Equiv.piCongrLeft_apply_eq_cast (P := appendSeen Idx₁ Ans₁ Idx₂ Ans₂) (e := messageIdxEquiv) v
    (Sum.inr j)

/-- On a joined transcript, the appended view is the pair of the parts' views. -/
theorem appendViewEquiv_see
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)) (ch : Ch)
    (tr₁ : P₁.Transcript (Fin.last n₁)) (tr₂ : P₂.Transcript (Fin.last n₂)) :
    appendViewEquiv (fun i => (appendMsg msg₁ msg₂ i).see ch (Transcript.join tr₁ tr₂ i.1)) =
      (fun j => (msg₁ j).see ch (tr₁ j.1), fun j => (msg₂ j).see ch (tr₂ j.1)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · rw [appendViewEquiv_apply_fst]
    refine (appendMsg_see_inl msg₁ msg₂ ch j (Transcript.join tr₁ tr₂ (Fin.castAdd n₂ j.1))).trans ?_
    rw [Transcript.join_left, cast_cast, cast_eq]
  · rw [appendViewEquiv_apply_snd]
    refine (appendMsg_see_inr msg₁ msg₂ ch j (Transcript.join tr₁ tr₂ (Fin.natAdd n₁ j.1))).trans ?_
    rw [Transcript.join_right, cast_cast, cast_eq]

/-- On any full transcript, the appended view is the pair of the views of its
two parts. -/
theorem appendViewEquiv_see_left_right
    (msg₁ : ∀ j : P₁.MessageIdx, MessageView (P₁.Type j.1) Ch (Idx₁ j) (Ans₁ j))
    (msg₂ : ∀ j : P₂.MessageIdx, MessageView (P₂.Type j.1) Ch (Idx₂ j) (Ans₂ j)) (ch : Ch)
    (tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))) :
    appendViewEquiv (fun i => (appendMsg msg₁ msg₂ i).see ch (tr i.1)) =
      (fun j => (msg₁ j).see ch (tr.left j.1), fun j => (msg₂ j).see ch (tr.right j.1)) := by
  conv_lhs => rw [← Transcript.join_left_right tr]
  exact appendViewEquiv_see msg₁ msg₂ ch _ _

end GordieHowe.IOP
