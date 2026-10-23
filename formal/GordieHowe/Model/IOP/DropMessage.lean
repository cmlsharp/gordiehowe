-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.Completeness

@[expose] public section

/-!
# Moving a prover message into the context

`ProtocolSpec.dropMsg P s` is the protocol `P` with its prover round `s` removed; round `j` of
the new protocol runs round `dropUp s j` of `P`. A claim-proving phase `B` of `P` whose round-`s`
message is supplied by the context instead (`ClaimProof.dropMsg`) proves the same claim with the
same error at every challenge round: its verifier is `B.V` on the transcript with the message
put back at round `s` (`dropFull`), and its state is `B`'s state on the prefix without the
message before round `s` (`dropPre`) and with it put back from round `s` on (`dropPost`).
Before round `s`, the state of `B` does not depend on the message. At the challenge round just
before round `s`, the new state reads the message one round early; since a prover message never
makes a false state true, the event is contained in the event of `B` at that round.

This is the move of Ligero's mask message into the oracle message of Ligero as a commit-and-prove
system (`GordieHowe.Ligero.AgreementThreshold.sound`, `GordieHowe.Ligero.MaskTest.Pieces.sound`): the context of the proof phase is
the input and the oracle message, and the mask message is read from it. In the C++ the IDOT/IQUAD mask
rows are rows 1–2 of the round-0 tableau (`lib/ligero/ligero_param.h` lines 86–99), committed
with the witness rows.

`CausalTranscript.dropMsg` reads an honest transcript family of `P` as one of the new protocol,
on the challenges transported by `dropChEquiv`; on its runs the new verifier, given the dropped
message, is the old verifier (`dropFull_dropT`).
-/

namespace GordieHowe.IOP

open scoped NNReal

variable {n : ℕ}

namespace ProtocolSpec

/-! ### Round indices -/

/-- The round of a protocol of `n` rounds that runs round `j` of the protocol with round `s`
removed. -/
def dropUp (s : Fin n) (j : Fin (n - 1)) : Fin n :=
  ⟨if j.1 < s.1 then j.1 else j.1 + 1, by have := j.2; have := s.2; split <;> omega⟩

theorem val_dropUp (s : Fin n) (j : Fin (n - 1)) :
    (dropUp s j).1 = if j.1 < s.1 then j.1 else j.1 + 1 := rfl

theorem dropUp_ne (s : Fin n) (j : Fin (n - 1)) : dropUp s j ≠ s := by
  intro h
  have := congrArg Fin.val h
  rw [val_dropUp] at this
  split at this <;> omega

theorem dropUp_of_lt {s : Fin n} {j : Fin (n - 1)} (h : j.1 < s.1) :
    dropUp s j = ⟨j.1, by omega⟩ :=
  Fin.ext (if_pos h)

theorem dropUp_of_ge {s : Fin n} {j : Fin (n - 1)} (h : s.1 ≤ j.1) :
    dropUp s j = ⟨j.1 + 1, by have := j.2; omega⟩ :=
  Fin.ext (if_neg (by omega))

theorem dropUp_lt_dropUp_iff (s : Fin n) {j j' : Fin (n - 1)} :
    dropUp s j < dropUp s j' ↔ j < j' := by
  rw [Fin.lt_def, Fin.lt_def, val_dropUp, val_dropUp]
  split_ifs <;> omega

/-- The round of the protocol with round `s` removed that runs round `i ≠ s`. -/
def dropDown (s i : Fin n) (h : i ≠ s) : Fin (n - 1) :=
  ⟨if i.1 < s.1 then i.1 else i.1 - 1, by
    have h' : i.1 ≠ s.1 := fun e => h (Fin.ext e)
    have := i.2
    have := s.2
    split <;> omega⟩

theorem val_dropDown (s i : Fin n) (h : i ≠ s) :
    (dropDown s i h).1 = if i.1 < s.1 then i.1 else i.1 - 1 := rfl

theorem dropUp_dropDown (s i : Fin n) (h : i ≠ s) : dropUp s (dropDown s i h) = i := by
  have h' : i.1 ≠ s.1 := fun e => h (Fin.ext e)
  apply Fin.ext
  rw [val_dropUp, val_dropDown]
  split_ifs <;> omega

theorem dropDown_dropUp (s : Fin n) (j : Fin (n - 1)) :
    dropDown s (dropUp s j) (dropUp_ne s j) = j := by
  apply Fin.ext
  rw [val_dropDown, val_dropUp]
  split_ifs <;> omega

/-- Every round other than `s` is run by a round of the protocol with round `s` removed. -/
theorem exists_dropUp_eq {s i : Fin n} (h : i ≠ s) : ∃ j, dropUp s j = i :=
  ⟨dropDown s i h, dropUp_dropDown s i h⟩

/-! ### The protocol -/

/-- `P` with its round `s` removed. Round `j` runs round `dropUp s j` of `P`. -/
def dropMsg (P : ProtocolSpec n) (s : Fin n) : ProtocolSpec (n - 1) where
  dir j := P.dir (dropUp s j)
  «Type» j := P.Type (dropUp s j)

variable {P : ProtocolSpec n} {s : Fin n}

@[simp] theorem dropMsg_dir (j : Fin (n - 1)) : (P.dropMsg s).dir j = P.dir (dropUp s j) := rfl

@[simp] theorem dropMsg_Type (j : Fin (n - 1)) : (P.dropMsg s).Type j = P.Type (dropUp s j) := rfl

/-- The challenge round of `P` that runs challenge round `i` of `P.dropMsg s`. -/
def dropChallengeIdx (i : (P.dropMsg s).ChallengeIdx) : P.ChallengeIdx := ⟨dropUp s i.1, i.2⟩

/-- The prover round of `P` that runs prover round `i` of `P.dropMsg s`. -/
def dropMsgIdx (i : (P.dropMsg s).MessageIdx) : P.MessageIdx := ⟨dropUp s i.1, i.2⟩

instance dropMsg_fintype [∀ i, Fintype (P.Challenge i)] (i : (P.dropMsg s).ChallengeIdx) :
    Fintype ((P.dropMsg s).Challenge i) :=
  inferInstanceAs (Fintype (P.Challenge (dropChallengeIdx i)))

instance dropMsg_decidableEq [∀ i, DecidableEq (P.Challenge i)] (i : (P.dropMsg s).ChallengeIdx) :
    DecidableEq ((P.dropMsg s).Challenge i) :=
  inferInstanceAs (DecidableEq (P.Challenge (dropChallengeIdx i)))

instance dropMsg_nonempty [∀ i, Nonempty (P.Challenge i)] (i : (P.dropMsg s).ChallengeIdx) :
    Nonempty ((P.dropMsg s).Challenge i) :=
  inferInstanceAs (Nonempty (P.Challenge (dropChallengeIdx i)))

/-- A challenge round is not a prover round. -/
theorem ChallengeIdx.val_ne_of_dir (hs : P.dir s = .P_to_V) (i : P.ChallengeIdx) : i.1 ≠ s := by
  intro e
  have h := i.2
  rw [e, hs] at h
  exact absurd h (by decide)

/-- When round `s` is a prover round, `dropChallengeIdx` is a bijection onto the challenge rounds of
`P`. -/
def dropChallengeIdxEquiv (hs : P.dir s = .P_to_V) : (P.dropMsg s).ChallengeIdx ≃ P.ChallengeIdx where
  toFun := dropChallengeIdx
  invFun i := ⟨dropDown s i.1 (ChallengeIdx.val_ne_of_dir hs i), by
    change P.dir (dropUp s _) = _
    rw [dropUp_dropDown]
    exact i.2⟩
  left_inv i := Subtype.ext (dropDown_dropUp s i.1)
  right_inv i := Subtype.ext (dropUp_dropDown s i.1 (ChallengeIdx.val_ne_of_dir hs i))

@[simp] theorem dropChallengeIdxEquiv_apply (hs : P.dir s = .P_to_V) (i : (P.dropMsg s).ChallengeIdx) :
    dropChallengeIdxEquiv hs i = dropChallengeIdx i := rfl

/-- The challenges of `P.dropMsg s` are the challenges of `P`, round `i` at round
`dropChallengeIdx i`. -/
def dropChEquiv (hs : P.dir s = .P_to_V) : (P.dropMsg s).Challenges ≃ P.Challenges :=
  Equiv.piCongr (dropChallengeIdxEquiv hs) fun i => Equiv.refl (P.Challenge (dropChallengeIdx i))

@[simp] theorem dropChEquiv_apply (hs : P.dir s = .P_to_V) (ch : (P.dropMsg s).Challenges)
    (i : (P.dropMsg s).ChallengeIdx) : dropChEquiv hs ch (dropChallengeIdx i) = ch i :=
  Equiv.piCongr_apply_apply _ _ ch i

/-! ### Transcripts given entry by entry -/

section OfFun

variable {m : ℕ} {Q : ProtocolSpec m}

/-- The transcript of the first `k` rounds whose round `i` is `f i`. -/
def Transcript.ofFun (k : Fin (m + 1)) (f : ∀ i : Fin m, i.1 < k.1 → Q.Type i) :
    Q.Transcript k :=
  fun i => f (Fin.castLE (by omega) i) i.2

/-- Appending a message to a transcript given entry by entry appends one entry. -/
theorem concat_ofFun {j : Fin m} (f : ∀ i : Fin m, i.1 < j.1 → Q.Type i) (x : Q.Type j)
    (g : ∀ i : Fin m, i.1 < j.1 + 1 → Q.Type i)
    (hf : ∀ i (hi : i.1 < j.1), g i (by omega) = f i hi) (hx : g j (by omega) = x) :
    Q.concat (Transcript.ofFun j.castSucc f) x = Transcript.ofFun j.succ g := by
  funext ⟨i, hi⟩
  have hi' : i < j.1 + 1 := hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
  · rw [Q.concat_apply_of_lt _ x i hlt]
    exact (hf ⟨i, by omega⟩ hlt).symm
  · rw [Q.concat_apply_last]
    exact hx.symm

/-- A statement about a transcript given entry by entry depends only on the entries and on
the length, not on how the length is written. -/
theorem ofFun_congr (F : (k : Fin (m + 1)) → Q.Transcript k → Prop) {k₁ k₂ : Fin (m + 1)}
    (h : k₁ = k₂) (f₁ : ∀ i : Fin m, i.1 < k₁.1 → Q.Type i)
    (f₂ : ∀ i : Fin m, i.1 < k₂.1 → Q.Type i) (hf : ∀ i h₁ h₂, f₁ i h₁ = f₂ i h₂) :
    F k₁ (Transcript.ofFun k₁ f₁) ↔ F k₂ (Transcript.ofFun k₂ f₂) := by
  subst h
  have : f₁ = f₂ := funext fun i => funext fun hi => hf i hi hi
  subst this
  rfl

/-- Entries of a transcript at indices with the same value are equal. -/
theorem Transcript.heq_apply {k : Fin (m + 1)} (tr : Q.Transcript k) {i₁ i₂ : Fin k}
    (h : i₁.1 = i₂.1) : HEq (tr i₁) (tr i₂) := by
  obtain rfl : i₁ = i₂ := Fin.ext h
  rfl

/-- The last entry of an appended transcript, at an index written as a natural number. -/
theorem concat_heq_last {j : Fin m} (tr : Q.Transcript j.castSucc) (x : Q.Type j) {v : ℕ}
    (hv : v = j.1) (h : v < (j.succ : Fin (m + 1)).1) : HEq (Q.concat tr x ⟨v, h⟩) x := by
  subst hv
  rw [Q.concat_apply_last]

end OfFun

/-! ### Transcripts of the protocol with a round removed -/

section Transcripts

/-- Round `i ≠ s` of `P` read from a transcript of `P.dropMsg s` that contains its round. -/
def dropEntry {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k) (i : Fin n) (hs : i ≠ s)
    (h : (dropDown s i hs).1 < k.1) : P.Type i :=
  cast (congrArg P.Type (dropUp_dropDown s i hs)) (tr ⟨(dropDown s i hs).1, h⟩)

/-- Appending a later round does not change an entry. -/
theorem dropEntry_concat_of_lt {j : Fin (n - 1)} (tr : (P.dropMsg s).Transcript j.castSucc)
    (x : (P.dropMsg s).Type j) (i : Fin n) (hs : i ≠ s) (h : (dropDown s i hs).1 < j.1 + 1)
    (hlt : (dropDown s i hs).1 < j.1) :
    dropEntry ((P.dropMsg s).concat tr x) i hs h = dropEntry tr i hs hlt := by
  unfold dropEntry
  rw [(P.dropMsg s).concat_apply_of_lt tr x _ hlt]

/-- The entry of the appended round is the appended message. -/
theorem dropEntry_concat_self {j : Fin (n - 1)} (tr : (P.dropMsg s).Transcript j.castSucc)
    (x : (P.dropMsg s).Type j) (i : Fin n) (hs : i ≠ s) (h : (dropDown s i hs).1 < j.1 + 1)
    (hi : dropUp s j = i) :
    dropEntry ((P.dropMsg s).concat tr x) i hs h = cast (congrArg P.Type hi) x := by
  subst hi
  unfold dropEntry
  refine eq_of_heq ((cast_heq _ _).trans ((concat_heq_last tr x ?_ h).trans (cast_heq _ _).symm))
  rw [dropDown_dropUp]

/-- The round `i ≠ s` of `P`, from a transcript of `P.dropMsg s`, or the message `msg` at
`i = s`. -/
def dropOrig (msg : P.Type s) {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k)
    (i : Fin n) (h : ∀ hs : i ≠ s, (dropDown s i hs).1 < k.1) : P.Type i :=
  if hs : i = s then cast (congrArg P.Type hs.symm) msg else dropEntry tr i hs (h hs)

theorem dropOrig_self (msg : P.Type s) {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k)
    (h : ∀ hs : s ≠ s, (dropDown s s hs).1 < k.1) : dropOrig msg tr s h = msg := by
  rw [dropOrig, dif_pos rfl]
  rfl

theorem dropOrig_of_ne (msg : P.Type s) {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k)
    {i : Fin n} (h : ∀ hs : i ≠ s, (dropDown s i hs).1 < k.1) (hs : i ≠ s) :
    dropOrig msg tr i h = dropEntry tr i hs (h hs) := by
  rw [dropOrig, dif_neg hs]

theorem dropDown_lt_of_lt {i : Fin n} (hs : i ≠ s) {k : ℕ} (hi : i.1 < k) (hk : k ≤ s.1) :
    (dropDown s i hs).1 < k := by
  rw [val_dropDown, if_pos (by omega)]
  exact hi

theorem dropDown_lt_of_le {i : Fin n} (hs : i ≠ s) {k : ℕ} (hi : i.1 < k + 1) (hk : s.1 ≤ k) :
    (dropDown s i hs).1 < k := by
  have h' : i.1 ≠ s.1 := fun e => hs (Fin.ext e)
  rw [val_dropDown]
  split <;> omega

/-- The first `k ≤ s` rounds of `P` read from a transcript of `P.dropMsg s`. -/
def dropPre {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k) (hk : k.1 ≤ s.1) :
    P.Transcript ⟨k.1, by omega⟩ :=
  Transcript.ofFun _ fun i hi =>
    dropEntry tr i (fun e => by subst e; simp at hi; omega) (dropDown_lt_of_lt _ hi hk)

/-- The first `k + 1` rounds of `P`, `s ≤ k`, from a transcript of `P.dropMsg s` and the
message `msg` put back at round `s`. -/
def dropPost (msg : P.Type s) {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k)
    (hk : s.1 ≤ k.1) : P.Transcript ⟨k.1 + 1, by have := k.2; have := s.2; omega⟩ :=
  Transcript.ofFun _ fun i hi => dropOrig msg tr i fun hs => dropDown_lt_of_le hs hi hk

/-- A full transcript of `P` from a full transcript of `P.dropMsg s` and the message `msg` put
back at round `s`. -/
def dropFull (msg : P.Type s) (tr : (P.dropMsg s).Transcript (Fin.last (n - 1))) :
    P.Transcript (Fin.last n) :=
  Transcript.ofFun _ fun i hi => dropOrig msg tr i fun hs =>
    dropDown_lt_of_le hs (k := n - 1) (by have := i.2; have := s.2; omega) (by have := s.2; omega)

/-- A full transcript of `P` read as a full transcript of `P.dropMsg s`: round `s` is dropped. -/
def dropT (T : P.Transcript (Fin.last n)) : (P.dropMsg s).Transcript (Fin.last (n - 1)) :=
  fun j => T (dropUp s (Fin.castLE (by simp) j))

/-- Appending round `j` before round `s` appends round `j` of `P`. -/
theorem dropPre_concat {j : Fin (n - 1)} (hj : j.1 + 1 ≤ s.1)
    (tr : (P.dropMsg s).Transcript j.castSucc) (x : (P.dropMsg s).Type j) :
    dropPre ((P.dropMsg s).concat tr x) hj =
      P.concat (m := ⟨j.1, by omega⟩) (dropPre tr (by simp; omega))
        (cast (congrArg P.Type (dropUp_of_lt (by omega))) x) := by
  unfold dropPre
  refine (concat_ofFun (j := ⟨j.1, by omega⟩) _ _ _ (fun i hi => ?_) ?_).symm
  · exact dropEntry_concat_of_lt tr x i _ _ (dropDown_lt_of_lt _ hi (by omega))
  · exact dropEntry_concat_self tr x _ _ _ (dropUp_of_lt (by omega))

/-- At length `s`, putting the message back appends it at round `s`. -/
theorem dropPost_self (msg : P.Type s) {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k)
    (hk : k.1 = s.1) :
    dropPost msg tr hk.ge =
      P.concat (m := ⟨k.1, by omega⟩) (dropPre tr hk.le)
        (cast (congrArg P.Type (Fin.ext hk.symm)) msg) := by
  unfold dropPost dropPre
  refine (concat_ofFun (j := ⟨k.1, by omega⟩) _ _ _ (fun i hi => ?_) ?_).symm
  · exact dropOrig_of_ne msg tr _ _
  · have e : (⟨k.1, by omega⟩ : Fin n) = s := Fin.ext hk
    refine eq_of_heq ?_
    rw [dropOrig, dif_pos e]

/-- Appending round `j = s - 1` appends round `j` of `P` and the message. -/
theorem dropPost_concat_pre (msg : P.Type s) {j : Fin (n - 1)} (hj : j.1 + 1 = s.1)
    (tr : (P.dropMsg s).Transcript j.castSucc) (x : (P.dropMsg s).Type j) :
    dropPost msg ((P.dropMsg s).concat tr x) (by simp; omega) =
      P.concat (m := ⟨j.1 + 1, by omega⟩)
        (P.concat (m := ⟨j.1, by omega⟩) (dropPre tr (by simp; omega))
          (cast (congrArg P.Type (dropUp_of_lt (by omega))) x))
        (cast (congrArg P.Type (Fin.ext hj.symm)) msg) := by
  rw [dropPost_self msg _ (by simpa using hj), dropPre_concat (by omega)]

/-- Appending round `j ≥ s` appends round `j + 1` of `P`. -/
theorem dropPost_concat (msg : P.Type s) {j : Fin (n - 1)} (hj : s.1 ≤ j.1)
    (tr : (P.dropMsg s).Transcript j.castSucc) (x : (P.dropMsg s).Type j) :
    dropPost msg ((P.dropMsg s).concat tr x) (by simp; omega) =
      P.concat (m := ⟨j.1 + 1, by have := j.2; omega⟩) (dropPost msg tr hj)
        (cast (congrArg P.Type (dropUp_of_ge hj)) x) := by
  unfold dropPost
  refine (concat_ofFun (j := ⟨j.1 + 1, by have := j.2; omega⟩) _ _ _ (fun i hi => ?_) ?_).symm
  · by_cases hs : i = s
    · subst hs
      rw [dropOrig_self, dropOrig_self]
    · rw [dropOrig_of_ne msg _ _ hs, dropOrig_of_ne msg _ _ hs]
      exact dropEntry_concat_of_lt tr x i hs _ (dropDown_lt_of_le hs hi hj)
  · have hs : (⟨j.1 + 1, by have := j.2; omega⟩ : Fin n) ≠ s := fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
    rw [dropOrig_of_ne msg _ _ hs]
    exact dropEntry_concat_self tr x _ hs _ (dropUp_of_ge hj)

/-- The full transcript from length `n - 1` read through `dropPost` is `dropFull`. -/
theorem dropPost_last_iff (F : (k : Fin (n + 1)) → P.Transcript k → Prop) (msg : P.Type s)
    (tr : (P.dropMsg s).Transcript (Fin.last (n - 1))) (hk : s.1 ≤ (Fin.last (n - 1)).1) :
    F ⟨(Fin.last (n - 1)).1 + 1, by have := s.2; simp; omega⟩ (dropPost msg tr hk) ↔
      F (Fin.last n) (dropFull msg tr) :=
  ofFun_congr F (Fin.ext (by have := s.2; simp; omega)) _ _ fun _ _ _ => rfl

theorem dropFull_apply_self (msg : P.Type s) (tr : (P.dropMsg s).Transcript (Fin.last (n - 1))) :
    dropFull msg tr s = msg :=
  dropOrig_self msg tr _

theorem dropFull_apply_dropUp (msg : P.Type s)
    (tr : (P.dropMsg s).Transcript (Fin.last (n - 1))) (j : Fin (n - 1)) :
    dropFull msg tr (dropUp s j) = tr j := by
  change dropOrig msg tr (dropUp s j) _ = _
  rw [dropOrig_of_ne msg tr _ (dropUp_ne s j)]
  unfold dropEntry
  refine eq_of_heq ((cast_heq _ _).trans (Transcript.heq_apply tr ?_))
  rw [val_dropDown, val_dropUp]
  split_ifs <;> omega

/-- Putting the round-`s` message of `T` back into `dropT T` recovers `T`. -/
theorem dropFull_dropT (T : P.Transcript (Fin.last n)) :
    dropFull (T s) (dropT (s := s) T) = T := by
  funext i
  by_cases hs : i = s
  · subst hs
    exact dropFull_apply_self _ _
  · obtain ⟨j, rfl⟩ := exists_dropUp_eq hs
    exact dropFull_apply_dropUp _ _ j

/-- Dropping round `s` of `dropFull msg tr` recovers `tr`. -/
theorem dropT_dropFull (msg : P.Type s) (tr : (P.dropMsg s).Transcript (Fin.last (n - 1))) :
    dropT (dropFull msg tr) = tr :=
  funext fun j => dropFull_apply_dropUp msg tr j

/-- A full transcript of `P.dropMsg s` carrying the challenges `ch` gives, with the message put
back, a transcript carrying the transported challenges. -/
theorem dropFull_challenge (hs : P.dir s = .P_to_V) (msg : P.Type s)
    {tr : (P.dropMsg s).Transcript (Fin.last (n - 1))} {ch : (P.dropMsg s).Challenges}
    (htr : ∀ i : (P.dropMsg s).ChallengeIdx, tr i.1 = ch i) (i : P.ChallengeIdx) :
    dropFull msg tr i.1 = dropChEquiv hs ch i := by
  obtain ⟨i', rfl⟩ := (dropChallengeIdxEquiv hs).surjective i
  rw [dropChallengeIdxEquiv_apply, dropChEquiv_apply]
  exact (dropFull_apply_dropUp msg tr i'.1).trans (htr i')

/-- The challenges of `dropT T`, for a transcript `T` carrying the challenges `ch`. -/
theorem dropT_challenge (hs : P.dir s = .P_to_V) {T : P.Transcript (Fin.last n)}
    {ch : P.Challenges} (hT : ∀ i : P.ChallengeIdx, T i.1 = ch i)
    (i : (P.dropMsg s).ChallengeIdx) :
    dropT (s := s) T i.1 = (dropChEquiv hs).symm ch i := by
  have := hT (dropChallengeIdx i)
  rw [← (dropChEquiv hs).apply_symm_apply ch, dropChEquiv_apply] at this
  exact this

end Transcripts

/-! ### The state family -/

section Family

/-- A family indexed by the prefixes of `P`, read on prefixes of `P.dropMsg s` with the message
`msg`: before round `s` on the transcript without it, from round `s` on with it put back. -/
def dropFamily (F : (k : Fin (n + 1)) → P.Transcript k → Prop) (msg : P.Type s)
    (k : Fin (n - 1 + 1)) (tr : (P.dropMsg s).Transcript k) : Prop :=
  if h : k.1 < s.1 then F ⟨k.1, by omega⟩ (dropPre tr h.le)
  else F ⟨k.1 + 1, by have := k.2; have := s.2; omega⟩ (dropPost msg tr (by omega))

theorem dropFamily_of_lt (F : (k : Fin (n + 1)) → P.Transcript k → Prop) (msg : P.Type s)
    {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k) (h : k.1 < s.1) :
    dropFamily F msg k tr ↔ F ⟨k.1, by omega⟩ (dropPre tr h.le) := by
  rw [dropFamily, dif_pos h]

theorem dropFamily_of_ge (F : (k : Fin (n + 1)) → P.Transcript k → Prop) (msg : P.Type s)
    {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k) (h : s.1 ≤ k.1) :
    dropFamily F msg k tr ↔
      F ⟨k.1 + 1, by have := k.2; have := s.2; omega⟩ (dropPost msg tr h) := by
  rw [dropFamily, dif_neg (by omega)]

end Family

end ProtocolSpec

open ProtocolSpec

/-! ### The claim-proving phase -/

namespace ClaimProof

variable {P : ProtocolSpec n} {s : Fin n} [∀ i, Fintype (P.Challenge i)]
  {ε : P.ChallengeIdx → ℝ≥0} {Ctx Ctx' : Type}

/-- A prover message at round `s` does not make the state true, read on the prefix of length
`s` with the message appended. -/
theorem not_S_dropPost (B : ClaimProof P Ctx ε) (hs : P.dir s = .P_to_V) (c : Ctx)
    (msg : P.Type s) {k : Fin (n - 1 + 1)} (tr : (P.dropMsg s).Transcript k) (hk : k.1 = s.1)
    (hnot : ¬ B.S ⟨k.1, by omega⟩ c (dropPre tr hk.le)) :
    ¬ B.S ⟨k.1 + 1, by have := s.2; omega⟩ c (dropPost msg tr hk.ge) := by
  rw [dropPost_self msg tr hk]
  have hs' : P.dir ⟨k.1, by omega⟩ = .P_to_V := by
    rw [show (⟨k.1, by omega⟩ : Fin n) = s from Fin.ext hk]
    exact hs
  exact B.next ⟨k.1, by omega⟩ hs' c _ _ hnot

open Classical in
/-- **A claim-proving phase with its round-`s` prover message supplied by the context**: the
phase of `P.dropMsg s` on contexts `c'` of type `Ctx'`, reading the context `f c'` of `B` and the
message `mask c'`. Its claim is `B.claim (f c')`, its verifier is `B.V` on the full transcript
with the message put back (`dropFull`), and its error at challenge round `i` is the error of `B`
at the round `dropChallengeIdx i` that runs it. `hs` (a parameter condition): round `s` is a prover
round. -/
def dropMsg (B : ClaimProof P Ctx ε) (hs : P.dir s = .P_to_V) (f : Ctx' → Ctx)
    (mask : Ctx' → P.Type s) : ClaimProof (P.dropMsg s) Ctx' (fun i => ε (dropChallengeIdx i)) where
  claim c := B.claim (f c)
  V c tr := B.V (f c) (dropFull (mask c) tr)
  S k c tr := dropFamily (fun k tr => B.S k (f c) tr) (mask c) k tr
  start c tr hc := by
    by_cases h : (0 : Fin (n - 1 + 1)).1 < s.1
    · rw [dropFamily_of_lt _ _ _ h]
      exact B.start _ _ hc
    · rw [dropFamily_of_ge _ _ _ (by omega)]
      refine B.not_S_dropPost hs _ _ tr (by simp at h ⊢; omega) ?_
      exact B.start _ _ hc
  next j hdir c tr x hnot := by
    have hdir' : P.dir (dropUp s j) = .P_to_V := hdir
    rcases lt_trichotomy (j.1 + 1) s.1 with hj | hj | hj
    · rw [dropFamily_of_lt _ _ tr (by simp; omega)] at hnot
      rw [dropFamily_of_lt _ _ _ (by simp; omega), dropPre_concat (by omega)]
      rw [dropUp_of_lt (by omega)] at hdir'
      exact B.next ⟨j.1, by omega⟩ hdir' _ _ _ hnot
    · rw [dropFamily_of_lt _ _ tr (by simp; omega)] at hnot
      rw [dropFamily_of_ge _ _ _ (by simp; omega)]
      refine B.not_S_dropPost hs _ _ _ (by simpa using hj) ?_
      rw [dropPre_concat (by omega)]
      rw [dropUp_of_lt (by omega)] at hdir'
      exact B.next ⟨j.1, by omega⟩ hdir' _ _ _ hnot
    · rw [dropFamily_of_ge _ _ tr (by simp; omega)] at hnot
      rw [dropFamily_of_ge _ _ _ (by simp; omega), dropPost_concat _ (by omega)]
      rw [dropUp_of_ge (by omega)] at hdir'
      exact B.next ⟨j.1 + 1, by have := j.2; omega⟩ hdir' _ _ _ hnot
  full c tr hV := by
    rw [dropFamily_of_ge _ _ tr (by have := s.2; simp; omega)]
    exact (dropPost_last_iff (fun k tr => B.S k (f c) tr) _ tr _).mpr (B.full _ _ hV)
  rbr c i tr := by
    have hdirj : P.dir (dropUp s i.1) = .V_to_P := i.2
    rcases Nat.lt_or_ge (i.1.1 + 1) s.1 with hj | hj
    · -- before round `s - 1`: round `i.1` of `P`, read on `dropPre`
      have hu := dropUp_of_lt (s := s) (j := i.1) (by omega)
      let iP : P.ChallengeIdx := ⟨⟨i.1.1, by omega⟩, hu ▸ hdirj⟩
      have hε : ε (dropChallengeIdx i) = ε iP := congrArg ε (Subtype.ext hu)
      rw [hε]
      refine card_le_of_mapsTo_cast
        (show (P.dropMsg s).Challenge i = P.Challenge iP from congrArg P.Type hu) (fun ch hch => ?_)
        (B.rbr (f c) iP (dropPre tr (by simp; omega)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      obtain ⟨h0, h1⟩ := hch
      rw [dropFamily_of_lt _ _ tr (by simp; omega)] at h0
      rw [dropFamily_of_lt _ _ _ (by simp; omega), dropPre_concat (by omega)] at h1
      exact ⟨h0, h1⟩
    · rcases Nat.lt_or_ge i.1.1 s.1 with hj' | hj'
      · -- the round just before `s`: round `i.1` of `P`, then the message
        have hu := dropUp_of_lt (s := s) (j := i.1) hj'
        let iP : P.ChallengeIdx := ⟨⟨i.1.1, by omega⟩, hu ▸ hdirj⟩
        have hε : ε (dropChallengeIdx i) = ε iP := congrArg ε (Subtype.ext hu)
        rw [hε]
        refine card_le_of_mapsTo_cast
          (show (P.dropMsg s).Challenge i = P.Challenge iP from congrArg P.Type hu) (fun ch hch => ?_)
          (B.rbr (f c) iP (dropPre tr (by simp; omega)))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
        obtain ⟨h0, h1⟩ := hch
        rw [dropFamily_of_lt _ _ tr (by simp; omega)] at h0
        rw [dropFamily_of_ge _ _ _ (by simp; omega)] at h1
        refine ⟨h0, ?_⟩
        by_contra hn
        refine B.not_S_dropPost hs _ _ _ (by simp; omega) ?_ h1
        rw [dropPre_concat (by omega)]
        exact hn
      · -- from round `s` on: round `i.1 + 1` of `P`, read on `dropPost`
        have hu := dropUp_of_ge (s := s) (j := i.1) hj'
        let iP : P.ChallengeIdx := ⟨⟨i.1.1 + 1, by have := i.1.2; omega⟩, hu ▸ hdirj⟩
        have hε : ε (dropChallengeIdx i) = ε iP := congrArg ε (Subtype.ext hu)
        rw [hε]
        refine card_le_of_mapsTo_cast
          (show (P.dropMsg s).Challenge i = P.Challenge iP from congrArg P.Type hu) (fun ch hch => ?_)
          (B.rbr (f c) iP (dropPost (mask c) tr (by simp; omega)))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
        obtain ⟨h0, h1⟩ := hch
        rw [dropFamily_of_ge _ _ tr (by simp; omega)] at h0
        rw [dropFamily_of_ge _ _ _ (by simp; omega), dropPost_concat _ (by omega)] at h1
        exact ⟨h0, h1⟩

@[simp] theorem dropMsg_claim (B : ClaimProof P Ctx ε) (hs : P.dir s = .P_to_V) (f : Ctx' → Ctx)
    (mask : Ctx' → P.Type s) (c : Ctx') : (B.dropMsg hs f mask).claim c ↔ B.claim (f c) :=
  Iff.rfl

@[simp] theorem dropMsg_V (B : ClaimProof P Ctx ε) (hs : P.dir s = .P_to_V) (f : Ctx' → Ctx)
    (mask : Ctx' → P.Type s) (c : Ctx') (tr : (P.dropMsg s).Transcript (Fin.last (n - 1))) :
    (B.dropMsg hs f mask).V c tr = B.V (f c) (dropFull (mask c) tr) :=
  rfl

end ClaimProof

/-! ### Errors -/

/-- The errors of `P.dropMsg s`, read at the rounds of `P` that run them, sum to the errors of
`P` when round `s` is a prover round. -/
theorem sum_dropChIdx {P : ProtocolSpec n} {s : Fin n} (hs : P.dir s = .P_to_V)
    (ε : P.ChallengeIdx → ℝ≥0) : ∑ i, ε (dropChallengeIdx (s := s) i) = ∑ i, ε i :=
  Equiv.sum_comp (dropChallengeIdxEquiv hs) ε

/-! ### Honest transcripts -/

/-- **An honest transcript family of `P.dropMsg s`**: the runs of `H` at the challenges
transported by `dropChEquiv`, with round `s` dropped. `hs` (a parameter condition): round `s` is a
prover round. -/
def CausalTranscript.dropMsg {P : ProtocolSpec n} {s : Fin n} (H : CausalTranscript P)
    (hs : P.dir s = .P_to_V) : CausalTranscript (P.dropMsg s) where
  transcript ch := dropT (H.transcript (dropChEquiv hs ch))
  challenge ch i := by
    change H.transcript (dropChEquiv hs ch) (dropChallengeIdx i).1 = ch i
    rw [H.challenge, dropChEquiv_apply]
  causal i ch ch' h := by
    change H.transcript _ (dropMsgIdx i).1 = H.transcript _ (dropMsgIdx i).1
    refine H.causal (dropMsgIdx i) _ _ fun j hj => ?_
    obtain ⟨j', rfl⟩ := (dropChallengeIdxEquiv hs).surjective j
    rw [dropChallengeIdxEquiv_apply, dropChEquiv_apply, dropChEquiv_apply]
    exact h j' ((dropUp_lt_dropUp_iff s).1 hj)

theorem CausalTranscript.dropMsg_transcript {P : ProtocolSpec n} {s : Fin n}
    (H : CausalTranscript P) (hs : P.dir s = .P_to_V) (ch : (P.dropMsg s).Challenges) :
    (H.dropMsg hs).transcript ch = dropT (H.transcript (dropChEquiv hs ch)) :=
  rfl

end GordieHowe.IOP
