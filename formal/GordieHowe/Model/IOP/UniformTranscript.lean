-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.AppendView
public import GordieHowe.Foundations.Probability.IdentDistrib

@[expose] public section

/-!
# Uniform transcripts

The paper's `def:red-sec` (c) defines the **uniform
simulator**: it draws every challenge uniformly and every prover message uniformly from its finite
message set, independently, so its output is a uniform full transcript. This file holds the
protocol-level facts the uniform-simulator statements use.

* Finiteness and nonemptiness of transcripts (`ProtocolSpec.Transcript.instFintype`) and of the
  message types of an appended protocol (`appendTypeFintype`).
* The challenges and the full transcripts of `P₁ ++ P₂` are pairs (`challengesEquiv`,
  `transcriptEquiv`).
* **Value families** (`CausalTranscript.ValuesBijective`): a family `f : V → CausalTranscript P`
  whose transcript, as a function of the challenges and the value, is a bijection onto the full
  transcripts. Its transcript under uniform challenges and a uniform value is then uniform
  (`ValuesBijective.uniform`). One challenge, one message, the empty protocol and the sequential
  composition of such families are value families.
-/

namespace GordieHowe.IOP

open ProtocolSpec

variable {n n₁ n₂ : ℕ} {P : ProtocolSpec n} {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}

/-! ### Finite transcripts -/

/-- A transcript prefix of a protocol with finite message and challenge sets is finite. -/
instance ProtocolSpec.Transcript.instFintype {m : ℕ} {Q : ProtocolSpec m}
    [∀ i, Fintype (Q.Type i)] (k : Fin (m + 1)) : Fintype (Q.Transcript k) :=
  inferInstanceAs (Fintype ((i : Fin k) → Q.Type _))

/-- A transcript prefix of a protocol with nonempty message and challenge sets is nonempty. -/
instance ProtocolSpec.Transcript.instNonempty {m : ℕ} {Q : ProtocolSpec m}
    [∀ i, Nonempty (Q.Type i)] (k : Fin (m + 1)) : Nonempty (Q.Transcript k) :=
  inferInstanceAs (Nonempty ((i : Fin k) → Q.Type _))

/-- The message types of an appended protocol are finite when those of both parts are. -/
instance ProtocolSpec.appendTypeFintype [fa : ∀ i, Fintype (P₁.Type i)]
    [fb : ∀ i, Fintype (P₂.Type i)] : ∀ i, Fintype ((P₁ ++ P₂).Type i) := fun i =>
  Fin.addCases (motive := fun i => Fintype ((P₁ ++ P₂).Type i))
    (fun j => Fintype.ofEquiv (P₁.Type j) (Equiv.cast (append_Type_castAdd j).symm))
    (fun j => Fintype.ofEquiv (P₂.Type j) (Equiv.cast (append_Type_natAdd j).symm)) i

/-- The message types of an appended protocol are nonempty when those of both parts are. -/
instance ProtocolSpec.appendTypeNonempty [∀ i, Nonempty (P₁.Type i)]
    [∀ i, Nonempty (P₂.Type i)] : ∀ i, Nonempty ((P₁ ++ P₂).Type i) := fun i =>
  Fin.addCases (motive := fun i => Nonempty ((P₁ ++ P₂).Type i))
    (fun j => (Equiv.cast (append_Type_castAdd j).symm).nonempty_congr.mp inferInstance)
    (fun j => (Equiv.cast (append_Type_natAdd j).symm).nonempty_congr.mp inferInstance) i

/-! ### Challenges and transcripts of an appended protocol are pairs -/

namespace ProtocolSpec

/-- `Challenges.join` at a verifier round of the first part is that part's challenge. -/
theorem Challenges.join_inl (a : P₁.Challenges) (b : P₂.Challenges) (j : P₁.ChallengeIdx) :
    Challenges.join a b (ChallengeIdx.inl j) = cast (append_Challenge_inl j).symm (a j) := by
  unfold Challenges.join
  split
  · rename_i j' h
    obtain rfl : j' = j := Sum.inl_injective (h.symm.trans (challengeIdxEquiv_inl j))
    rfl
  · rename_i j' h
    exact absurd (h.symm.trans (challengeIdxEquiv_inl j)) Sum.inr_ne_inl

/-- `Challenges.join` at a verifier round of the second part is that part's challenge. -/
theorem Challenges.join_inr (a : P₁.Challenges) (b : P₂.Challenges) (j : P₂.ChallengeIdx) :
    Challenges.join a b (ChallengeIdx.inr j) = cast (append_Challenge_inr j).symm (b j) := by
  unfold Challenges.join
  split
  · rename_i j' h
    exact absurd (h.symm.trans (challengeIdxEquiv_inr j)) Sum.inl_ne_inr
  · rename_i j' h
    obtain rfl : j' = j := Sum.inr_injective (h.symm.trans (challengeIdxEquiv_inr j))
    rfl

@[simp] theorem Challenges.left_join (a : P₁.Challenges) (b : P₂.Challenges) :
    (Challenges.join a b).left = a := by
  funext j
  simp only [Challenges.left, Challenges.join_inl, cast_cast, cast_eq]

@[simp] theorem Challenges.right_join (a : P₁.Challenges) (b : P₂.Challenges) :
    (Challenges.join a b).right = b := by
  funext j
  simp only [Challenges.right, Challenges.join_inr, cast_cast, cast_eq]

/-- Challenges of an appended protocol agreeing on both parts are equal. -/
theorem Challenges.ext_left_right {ch ch' : (P₁ ++ P₂).Challenges} (hl : ch.left = ch'.left)
    (hr : ch.right = ch'.right) : ch = ch' := by
  funext i
  rcases ChallengeIdx.inl_or_inr i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h := congrFun hl j
    simp only [Challenges.left] at h
    exact (Equiv.cast _).injective h
  · have h := congrFun hr j
    simp only [Challenges.right] at h
    exact (Equiv.cast _).injective h

@[simp] theorem Challenges.join_left_right (ch : (P₁ ++ P₂).Challenges) :
    Challenges.join ch.left ch.right = ch :=
  Challenges.ext_left_right (Challenges.left_join _ _) (Challenges.right_join _ _)

/-- **The challenges of an appended protocol are pairs** of the parts' challenges. -/
def challengesEquiv : (P₁ ++ P₂).Challenges ≃ P₁.Challenges × P₂.Challenges where
  toFun ch := (ch.left, ch.right)
  invFun c := Challenges.join c.1 c.2
  left_inv ch := Challenges.join_left_right ch
  right_inv c := by simp

/-- **The full transcripts of an appended protocol are pairs** of the parts' full transcripts. -/
def transcriptEquiv :
    (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂)) ≃
      P₁.Transcript (Fin.last n₁) × P₂.Transcript (Fin.last n₂) where
  toFun tr := (tr.left, tr.right)
  invFun t := Transcript.join t.1 t.2
  left_inv tr := Transcript.join_left_right tr
  right_inv t := by simp

/-- **Joining two bijective transcript maps** on the parts' challenges and coins gives a bijective
transcript map on the appended protocol's challenges and the pairs of coins. -/
theorem bijective_join {S₁ S₂ : Type}
    {f₁ : P₁.Challenges × S₁ → P₁.Transcript (Fin.last n₁)}
    {f₂ : P₂.Challenges × S₂ → P₂.Transcript (Fin.last n₂)}
    (h₁ : Function.Bijective f₁) (h₂ : Function.Bijective f₂) :
    Function.Bijective fun x : (P₁ ++ P₂).Challenges × (S₁ × S₂) =>
      Transcript.join (f₁ (x.1.left, x.2.1)) (f₂ (x.1.right, x.2.2)) := by
  let e : (P₁ ++ P₂).Challenges × (S₁ × S₂) ≃ (P₁.Challenges × S₁) × (P₂.Challenges × S₂) :=
    (challengesEquiv.prodCongr (Equiv.refl _)).trans (Equiv.prodProdProdComm _ _ _ _)
  have : (fun x : (P₁ ++ P₂).Challenges × (S₁ × S₂) =>
      Transcript.join (f₁ (x.1.left, x.2.1)) (f₂ (x.1.right, x.2.2))) =
      transcriptEquiv.symm ∘ Prod.map f₁ f₂ ∘ e := rfl
  rw [this]
  exact transcriptEquiv.symm.bijective.comp ((h₁.prodMap h₂).comp e.bijective)

/-- Joining with a bijective transcript map of the second part on its challenges alone. -/
theorem bijective_join_unit {S₁ : Type}
    {f₁ : P₁.Challenges × S₁ → P₁.Transcript (Fin.last n₁)}
    {f₂ : P₂.Challenges × Unit → P₂.Transcript (Fin.last n₂)}
    (h₁ : Function.Bijective f₁) (h₂ : Function.Bijective f₂) :
    Function.Bijective fun x : (P₁ ++ P₂).Challenges × S₁ =>
      Transcript.join (f₁ (x.1.left, x.2)) (f₂ (x.1.right, ())) := by
  have h := (bijective_join h₁ h₂).comp
    ((Equiv.refl (P₁ ++ P₂).Challenges).prodCongr (Equiv.prodPUnit S₁).symm).bijective
  exact h

end ProtocolSpec

/-! ### Value families -/

namespace CausalTranscript

/-- **A value family**: the transcript of `f v` at the challenges `ch`, as a function of `(ch, v)`,
is a bijection onto the full transcripts. Under uniform challenges and a uniform value its
transcript is uniform (`ValuesBijective.uniform`): it is the uniform simulator of paper
`def:red-sec` (c). -/
def ValuesBijective {V : Type} (f : V → CausalTranscript P) : Prop :=
  Function.Bijective fun x : P.Challenges × V => (f x.2).transcript x.1

/-- The transcript of a value family under uniform challenges and a uniform value is uniform. -/
theorem ValuesBijective.uniform {V : Type} {f : V → CausalTranscript P} (h : ValuesBijective f)
    [Fintype P.Challenges] [Nonempty P.Challenges] [Fintype V] [Nonempty V]
    [Fintype (P.Transcript (Fin.last n))] [Nonempty (P.Transcript (Fin.last n))] :
    Uniform fun x : P.Challenges × V => (f x.2).transcript x.1 :=
  Uniform.of_equiv (Equiv.ofBijective _ h)

/-- Reparametrizing the values of a value family by a bijection gives a value family. -/
theorem ValuesBijective.comp_equiv {V W : Type} {f : V → CausalTranscript P}
    (h : ValuesBijective f) (e : W ≃ V) : ValuesBijective (f ∘ e) :=
  h.comp ((Equiv.refl P.Challenges).prodCongr e).bijective

/-- A family equal to a value family at every value is a value family. -/
theorem ValuesBijective.congr {V : Type} {f g : V → CausalTranscript P} (h : ValuesBijective f)
    (hfg : ∀ v ch, (f v).transcript ch = (g v).transcript ch) : ValuesBijective g := by
  have : (fun x : P.Challenges × V => (g x.2).transcript x.1) =
      fun x => (f x.2).transcript x.1 := funext fun x => (hfg x.2 x.1).symm
  unfold ValuesBijective
  rw [this]
  exact h

/-- The one move of a one-move protocol. -/
theorem fin_last_one_eq (i : Fin (Fin.last 1 : ℕ)) : i = ⟨0, Nat.zero_lt_one⟩ :=
  Fin.ext (Nat.lt_one_iff.mp i.isLt)

/-- A one-move protocol whose move is the prover's has no verifier round. -/
theorem not_challengeIdx_message {Msg : Type}
    (i : (⟨fun _ : Fin 1 => .P_to_V, fun _ => Msg⟩ : ProtocolSpec 1).ChallengeIdx) : False := by
  obtain ⟨j, h⟩ := i
  cases h

/-- **One fresh challenge** is a value family with no value. -/
theorem valuesBijective_oneChallenge (Msg : Type) :
    ValuesBijective fun _ : Unit => oneChallenge Msg := by
  refine ⟨fun x y h => ?_, fun tr => ⟨(fun _ => tr ⟨0, Nat.zero_lt_one⟩, ()), ?_⟩⟩
  · have h0 := congrFun h ⟨0, Nat.zero_lt_one⟩
    refine Prod.ext (funext fun i => ?_) rfl
    have hi : i = ⟨0, rfl⟩ := Subtype.ext (Subsingleton.elim _ _)
    subst hi
    exact h0
  · funext i
    rw [fin_last_one_eq i]
    rfl

/-- **One prover message** is a value family whose value is the message. -/
theorem valuesBijective_oneMessage (Msg : Type) :
    ValuesBijective fun m : Msg => oneMessage m := by
  refine ⟨fun x y h => ?_,
    fun tr => ⟨(fun i => (not_challengeIdx_message i).elim, tr ⟨0, Nat.zero_lt_one⟩), ?_⟩⟩
  · refine Prod.ext (funext fun i => (not_challengeIdx_message i).elim) ?_
    exact congrFun h ⟨0, Nat.zero_lt_one⟩
  · funext i
    rw [fin_last_one_eq i]
    rfl

/-- **The empty protocol** is a value family with no value. -/
theorem valuesBijective_empty (P : ProtocolSpec 0) :
    ValuesBijective fun _ : Unit => empty P := by
  refine ⟨fun x y _ => Prod.ext (funext fun i => i.1.elim0) rfl,
    fun tr => ⟨(fun i => i.1.elim0, ()), funext fun i => i.elim0⟩⟩

/-- **Two value families in sequence** form a value family whose value is the pair. -/
theorem ValuesBijective.append {V₁ V₂ : Type} {f₁ : V₁ → CausalTranscript P₁}
    {f₂ : V₂ → CausalTranscript P₂} (h₁ : ValuesBijective f₁) (h₂ : ValuesBijective f₂) :
    ValuesBijective fun v : V₁ × V₂ => (f₁ v.1).append fun _ => f₂ v.2 :=
  bijective_join (f₁ := fun y => (f₁ y.2).transcript y.1)
    (f₂ := fun y => (f₂ y.2).transcript y.1) h₁ h₂

/-- **A value family after one fresh challenge** is a value family with the same value. -/
theorem ValuesBijective.oneChallenge_append {Msg V : Type} {f : V → CausalTranscript P}
    (h : ValuesBijective f) :
    ValuesBijective fun v : V => (oneChallenge Msg).append fun _ => f v :=
  ((valuesBijective_oneChallenge Msg).append h).comp_equiv (Equiv.punitProd V).symm

end CausalTranscript

end GordieHowe.IOP
