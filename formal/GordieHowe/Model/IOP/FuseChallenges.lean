-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.Model.IOP.ClaimReduction
public import GordieHowe.Model.IOP.CompletenessAppend

@[expose] public section

/-!
# Fusing two leading verifier moves

Two adjacent verifier moves `a ∈ A`, then `b ∈ B`, at the start of a protocol carry the same
information as one verifier move `(a, b) ∈ A × B`: the protocol `one .V_to_P A ++ (one .V_to_P B
++ Q)` (`orig`) and the protocol `one .V_to_P (A × B) ++ Q` (`fused`) have the same full
transcripts up to the bijection `fuseEquiv`, and the same challenge vectors (`unfuseChallenges`).

* **Prefixes** (`unfuse`): a fused prefix of length `k` is the original prefix of length `0` when
  `k = 0` and of length `k + 1` otherwise (`shiftLen`).
* **Soundness** (`ClaimReduction.fuse`): a claim reduction on `orig` is one on `fused` with the
  state read on the original prefix, the error `ε₀ + ε₁` at the fused move and each later move's
  error unchanged (`fuseError`, `sum_fuseError`). With `¬ S(p)`, the challenges `(a, b)` making
  `S(p‖a‖b)` true are those with `S(p‖a)` (at most `ε₀|A|·|B|`) and, for each `a` with
  `¬ S(p‖a)`, at most `ε₁|B|` values `b` (`card_filter_prod_le`).
* **Honest transcripts** (`CausalTranscript.fuse`): an honest causal family on `orig` read
  through the bijection.
-/

namespace GordieHowe.IOP

open ProtocolSpec GKR.Schedule
open scoped NNReal

variable {m : ℕ} (A B : Type) (Q : ProtocolSpec m)

/-- **The two leading verifier moves** `a ∈ A`, `b ∈ B`, followed by `Q`. -/
abbrev orig : ProtocolSpec (1 + (1 + m)) := one .V_to_P A ++ (one .V_to_P B ++ Q)

/-- **The fused verifier move** `(a, b) ∈ A × B`, followed by `Q`. -/
abbrev fused : ProtocolSpec (1 + m) := one .V_to_P (A × B) ++ Q

/-- The original prefix length of a fused prefix of length `k`: `0` at `0`, else `k + 1`. -/
def shiftLen (k : ℕ) : ℕ := if k = 0 then 0 else k + 1

@[simp] theorem shiftLen_zero : shiftLen 0 = 0 := rfl

theorem shiftLen_of_ne {k : ℕ} (h : k ≠ 0) : shiftLen k = k + 1 := if_neg h

variable {A B Q}

/-! ### Message types and directions -/

theorem orig_Type_zero (i : Fin (1 + (1 + m))) (h : i.val = 0) : (orig A B Q).Type i = A := by
  have e : i = Fin.castAdd (1 + m) (0 : Fin 1) := Fin.ext (by simp [h])
  subst e
  exact append_Type_castAdd _

theorem orig_Type_one (i : Fin (1 + (1 + m))) (h : i.val = 1) : (orig A B Q).Type i = B := by
  have e : i = Fin.natAdd 1 (Fin.castAdd m (0 : Fin 1)) := Fin.ext (by simp [h])
  subst e
  exact (append_Type_natAdd _).trans (append_Type_castAdd _)

theorem fused_Type_zero (j : Fin (1 + m)) (h : j.val = 0) : (fused A B Q).Type j = (A × B) := by
  have e : j = Fin.castAdd m (0 : Fin 1) := Fin.ext (by simp [h])
  subst e
  exact append_Type_castAdd _

/-- A later original move has the message type of the fused move before it. -/
theorem orig_Type_shift (i : Fin (1 + (1 + m))) (j : Fin (1 + m)) (hi : i.val = j.val + 1)
    (hj : j.val ≠ 0) : (orig A B Q).Type i = (fused A B Q).Type j := by
  obtain ⟨jv, hjv⟩ := j
  obtain ⟨q, rfl⟩ : ∃ q, jv = q + 1 := ⟨jv - 1, by simp at hj; omega⟩
  have hq : q < m := by omega
  have ei : i = Fin.natAdd 1 (Fin.natAdd 1 ⟨q, hq⟩) := Fin.ext (by simp at hi ⊢; omega)
  have ej : (⟨q + 1, hjv⟩ : Fin (1 + m)) = Fin.natAdd 1 ⟨q, hq⟩ := Fin.ext (by simp; omega)
  subst ei
  rw [ej]
  exact ((append_Type_natAdd _).trans (append_Type_natAdd _)).trans (append_Type_natAdd _).symm

theorem orig_dir_zero (i : Fin (1 + (1 + m))) (h : i.val = 0) : (orig A B Q).dir i = .V_to_P := by
  have e : i = Fin.castAdd (1 + m) (0 : Fin 1) := Fin.ext (by simp [h])
  subst e
  exact append_dir_castAdd _

theorem orig_dir_one (i : Fin (1 + (1 + m))) (h : i.val = 1) : (orig A B Q).dir i = .V_to_P := by
  have e : i = Fin.natAdd 1 (Fin.castAdd m (0 : Fin 1)) := Fin.ext (by simp [h])
  subst e
  exact (append_dir_natAdd _).trans (append_dir_castAdd _)

theorem fused_dir_zero (j : Fin (1 + m)) (h : j.val = 0) : (fused A B Q).dir j = .V_to_P := by
  have e : j = Fin.castAdd m (0 : Fin 1) := Fin.ext (by simp [h])
  subst e
  exact append_dir_castAdd _

/-- A later original move has the direction of the fused move before it. -/
theorem orig_dir_shift (i : Fin (1 + (1 + m))) (j : Fin (1 + m)) (hi : i.val = j.val + 1)
    (hj : j.val ≠ 0) : (orig A B Q).dir i = (fused A B Q).dir j := by
  obtain ⟨jv, hjv⟩ := j
  obtain ⟨q, rfl⟩ : ∃ q, jv = q + 1 := ⟨jv - 1, by simp at hj; omega⟩
  have hq : q < m := by omega
  have ei : i = Fin.natAdd 1 (Fin.natAdd 1 ⟨q, hq⟩) := Fin.ext (by simp at hi ⊢; omega)
  have ej : (⟨q + 1, hjv⟩ : Fin (1 + m)) = Fin.natAdd 1 ⟨q, hq⟩ := Fin.ext (by simp; omega)
  subst ei
  rw [ej]
  exact ((append_dir_natAdd _).trans (append_dir_natAdd _)).trans (append_dir_natAdd _).symm

/-- A fused prover move is not the fused verifier move. -/
theorem fused_val_ne_of_dir {j : Fin (1 + m)} (h : (fused A B Q).dir j = .P_to_V) : j.val ≠ 0 :=
  fun h0 => by rw [fused_dir_zero j h0] at h; cases h

/-! ### Prefixes -/

/-- **The original prefix of a fused prefix** of length `k`, at an original length `k'` equal to
`shiftLen k`: the two coordinates of the fused move at moves `0` and `1`, then the later moves one
position later. -/
def unfuse {k : Fin (1 + m + 1)} (tr : (fused A B Q).Transcript k) (k' : Fin (1 + (1 + m) + 1))
    (hk : k'.val = shiftLen k.val) : (orig A B Q).Transcript k' := fun i =>
  if h0 : i.val = 0 then
    cast (orig_Type_zero (Fin.castLE (by omega) i) h0).symm
      (cast (fused_Type_zero _ rfl) (tr ⟨0, by
        have := i.2; unfold shiftLen at hk; split_ifs at hk <;> omega⟩)).1
  else if h1 : i.val = 1 then
    cast (orig_Type_one (Fin.castLE (by omega) i) h1).symm
      (cast (fused_Type_zero _ rfl) (tr ⟨0, by
        have := i.2; unfold shiftLen at hk; split_ifs at hk <;> omega⟩)).2
  else
    cast (orig_Type_shift (Fin.castLE (by omega) i) ⟨i.val - 1, by omega⟩ (by simp; omega)
        (by simp; omega)).symm
      (tr ⟨i.val - 1, by have := i.2; unfold shiftLen at hk; split_ifs at hk <;> omega⟩)

/-- The original prefix does not depend on how its length is named. -/
theorem unfuse_congr {k : Fin (1 + m + 1)} (tr : (fused A B Q).Transcript k)
    {k₁ k₂ : Fin (1 + (1 + m) + 1)} (e : k₁ = k₂) (h₁ : k₁.val = shiftLen k.val)
    (h₂ : k₂.val = shiftLen k.val) {S : (k : Fin (1 + (1 + m) + 1)) → (orig A B Q).Transcript k → Prop} :
    S k₁ (unfuse tr k₁ h₁) ↔ S k₂ (unfuse tr k₂ h₂) := by
  subst e
  rfl

/-- An earlier entry of an extended transcript is the entry before the extension. -/
theorem concat_heq_of_lt {n : ℕ} {P : ProtocolSpec n} {mv : Fin n} (tr : P.Transcript mv.castSucc)
    (msg : P.Type mv) (l : Fin mv.succ) (h : l.val < mv.val) :
    HEq (P.concat tr msg l) (tr ⟨l.val, h⟩) := by
  simp only [ProtocolSpec.concat, Fin.snoc, h, dite_true]
  exact cast_heq _ _

/-- The last entry of an extended transcript is the appended message. -/
theorem concat_heq_last {n : ℕ} {P : ProtocolSpec n} {mv : Fin n} (tr : P.Transcript mv.castSucc)
    (msg : P.Type mv) (l : Fin mv.succ) (h : l.val = mv.val) : HEq (P.concat tr msg l) msg := by
  have h' : ¬ l.val < mv.val := by omega
  simp only [ProtocolSpec.concat, Fin.snoc, h', dite_false]
  exact cast_heq _ _

theorem unfuse_heq_zero {k : Fin (1 + m + 1)} (tr : (fused A B Q).Transcript k)
    (k' : Fin (1 + (1 + m) + 1)) (hk : k'.val = shiftLen k.val) (l : Fin k') (h0 : l.val = 0)
    (H : 0 < k.val) :
    HEq (unfuse tr k' hk l) (cast (fused_Type_zero _ rfl) (tr ⟨0, H⟩)).1 := by
  unfold unfuse
  rw [dite_cond_eq_true (eq_true h0)]
  exact cast_heq _ _

theorem unfuse_heq_one {k : Fin (1 + m + 1)} (tr : (fused A B Q).Transcript k)
    (k' : Fin (1 + (1 + m) + 1)) (hk : k'.val = shiftLen k.val) (l : Fin k') (h1 : l.val = 1)
    (H : 0 < k.val) :
    HEq (unfuse tr k' hk l) (cast (fused_Type_zero _ rfl) (tr ⟨0, H⟩)).2 := by
  unfold unfuse
  rw [dite_cond_eq_false (eq_false (by omega)), dite_cond_eq_true (eq_true h1)]
  exact cast_heq _ _

theorem unfuse_heq_shift {k : Fin (1 + m + 1)} (tr : (fused A B Q).Transcript k)
    (k' : Fin (1 + (1 + m) + 1)) (hk : k'.val = shiftLen k.val) (l : Fin k') (h0 : l.val ≠ 0)
    (h1 : l.val ≠ 1) (H : l.val - 1 < k.val) :
    HEq (unfuse tr k' hk l) (tr ⟨l.val - 1, H⟩) := by
  unfold unfuse
  rw [dite_cond_eq_false (eq_false h0), dite_cond_eq_false (eq_false h1)]
  exact cast_heq _ _

/-- Heterogeneously equal values of types equal to a pair type have equal casts. -/
theorem cast_eq_cast_of_heq {α β γ : Type} {x : α} {y : β} (h : HEq x y) (p : α = γ) (q : β = γ) :
    cast p x = cast q y :=
  eq_of_heq ((cast_heq p x).trans (h.trans (cast_heq q y).symm))

/-- **A fused prover or later verifier move** extends the original prefix by the same message, one
position later. -/
theorem unfuse_concat_shift (j : Fin (1 + m)) (hj : j.val ≠ 0) (i : Fin (1 + (1 + m)))
    (hi : i.val = j.val + 1) (tr : (fused A B Q).Transcript j.castSucc)
    (msg : (fused A B Q).Type j) :
    unfuse ((fused A B Q).concat tr msg) i.succ (by simp [shiftLen_of_ne, hi]) =
      (orig A B Q).concat (unfuse tr i.castSucc (by simp [shiftLen_of_ne hj, hi]))
        (cast (orig_Type_shift i j hi hj).symm msg) := by
  funext l
  apply eq_of_heq
  have hl := l.2
  simp only [Fin.val_succ] at hl
  by_cases hlt : l.val < i.val
  · refine HEq.trans ?_ (concat_heq_of_lt _ _ l hlt).symm
    by_cases h0 : l.val = 0
    · refine (unfuse_heq_zero _ _ _ l h0 (by simp)).trans (HEq.trans ?_
        (unfuse_heq_zero tr i.castSucc _ ⟨l.val, hlt⟩ h0 (Nat.pos_of_ne_zero hj)).symm)
      rw [cast_eq_cast_of_heq (concat_heq_of_lt tr msg ⟨0, Nat.succ_pos _⟩ (Nat.pos_of_ne_zero hj)) _
        (fused_Type_zero _ rfl)]
    · by_cases h1 : l.val = 1
      · refine (unfuse_heq_one _ _ _ l h1 (by simp)).trans (HEq.trans ?_
          (unfuse_heq_one tr i.castSucc _ ⟨l.val, hlt⟩ h1 (Nat.pos_of_ne_zero hj)).symm)
        rw [cast_eq_cast_of_heq (concat_heq_of_lt tr msg ⟨0, Nat.succ_pos _⟩ (Nat.pos_of_ne_zero hj)) _
          (fused_Type_zero _ rfl)]
      · refine (unfuse_heq_shift _ _ _ l h0 h1 (by simp; omega)).trans (HEq.trans ?_
          (unfuse_heq_shift tr i.castSucc _ ⟨l.val, hlt⟩ h0 h1 (by simp; omega)).symm)
        exact concat_heq_of_lt _ _ _ (by simp; omega)
  · have hle : l.val = i.val := by omega
    refine (unfuse_heq_shift _ _ _ l (by omega) (by omega) (by simp; omega)).trans ?_
    refine (concat_heq_last _ _ _ (by simp; omega)).trans ?_
    exact ((concat_heq_last _ _ l hle).trans (cast_heq _ _)).symm

/-- **The fused verifier move** `(a, b)` extends the empty original prefix by `a`, then `b`. -/
theorem unfuse_concat_zero (tr : (fused A B Q).Transcript (⟨0, by omega⟩ : Fin (1 + m)).castSucc)
    (msg : (fused A B Q).Type ⟨0, by omega⟩) :
    unfuse ((fused A B Q).concat tr msg) (⟨1, by omega⟩ : Fin (1 + (1 + m))).succ
        (by simp [shiftLen]) =
      (orig A B Q).concat (m := ⟨1, by omega⟩)
        ((orig A B Q).concat (m := ⟨0, by omega⟩)
          (unfuse tr (⟨0, by omega⟩ : Fin (1 + (1 + m))).castSucc (by simp))
          (cast (orig_Type_zero _ rfl).symm (cast (fused_Type_zero _ rfl) msg).1))
        (cast (orig_Type_one _ rfl).symm (cast (fused_Type_zero _ rfl) msg).2) := by
  funext l
  apply eq_of_heq
  have hl := l.2
  simp only [Fin.val_succ] at hl
  by_cases h0 : l.val = 0
  · refine (unfuse_heq_zero _ _ _ l h0 (Nat.zero_lt_succ 0)).trans ?_
    refine HEq.trans ?_ (concat_heq_of_lt _ _ l (by simp; omega)).symm
    refine HEq.trans ?_ (concat_heq_last _ _ _ (by simp; omega)).symm
    refine HEq.trans ?_ (cast_heq _ _).symm
    rw [cast_eq_cast_of_heq (concat_heq_last _ _ _ (by simp)) _ (fused_Type_zero _ rfl)]
  · refine (unfuse_heq_one _ _ _ l (by omega) (Nat.zero_lt_succ 0)).trans ?_
    refine HEq.trans ?_ (concat_heq_last _ _ l (by simp; omega)).symm
    refine HEq.trans ?_ (cast_heq _ _).symm
    rw [cast_eq_cast_of_heq (concat_heq_last _ _ _ (by simp)) _ (fused_Type_zero _ rfl)]

/-! ### Verifier moves and errors -/

variable (A B Q) in
/-- The original move `a`. -/
abbrev idx₀ : (orig A B Q).ChallengeIdx := ⟨⟨0, by omega⟩, orig_dir_zero _ rfl⟩

variable (A B Q) in
/-- The original move `b`. -/
abbrev idx₁ : (orig A B Q).ChallengeIdx := ⟨⟨1, by omega⟩, orig_dir_one _ rfl⟩

variable (A B Q) in
/-- The fused move `(a, b)`. -/
abbrev fusedIdx₀ : (fused A B Q).ChallengeIdx := ⟨⟨0, by omega⟩, fused_dir_zero _ rfl⟩

/-- The original verifier move of a later fused verifier move: one position later. -/
def shiftIdx (i : (fused A B Q).ChallengeIdx) (h : i.1.val ≠ 0) : (orig A B Q).ChallengeIdx :=
  ⟨⟨i.1.val + 1, by omega⟩, (orig_dir_shift _ i.1 rfl h).trans i.2⟩

@[simp] theorem shiftIdx_val (i : (fused A B Q).ChallengeIdx) (h : i.1.val ≠ 0) :
    (shiftIdx i h).1.val = i.1.val + 1 := rfl

theorem eq_fusedIdx₀ {i : (fused A B Q).ChallengeIdx} (h : i.1.val = 0) : i = fusedIdx₀ A B Q :=
  Subtype.ext (Fin.ext h)

/-- **The fused round errors**: `ε₀ + ε₁` at the fused move, and each later move's original error. -/
def fuseError (ε : (orig A B Q).ChallengeIdx → ℝ≥0) (i : (fused A B Q).ChallengeIdx) : ℝ≥0 :=
  if h : i.1.val = 0 then ε (idx₀ A B Q) + ε (idx₁ A B Q) else ε (shiftIdx i h)

theorem fuseError_fusedIdx₀ (ε : (orig A B Q).ChallengeIdx → ℝ≥0) :
    fuseError ε (fusedIdx₀ A B Q) = ε (idx₀ A B Q) + ε (idx₁ A B Q) := dite_cond_eq_true (eq_true rfl)

theorem fuseError_shiftIdx (ε : (orig A B Q).ChallengeIdx → ℝ≥0) (i : (fused A B Q).ChallengeIdx)
    (h : i.1.val ≠ 0) : fuseError ε i = ε (shiftIdx i h) := dite_cond_eq_false (eq_false h)

/-- The original verifier move read by each fused one: `b` for the fused move. -/
def embedIdx (i : (fused A B Q).ChallengeIdx) : (orig A B Q).ChallengeIdx :=
  if h : i.1.val = 0 then idx₁ A B Q else shiftIdx i h

theorem embedIdx_val (i : (fused A B Q).ChallengeIdx) : (embedIdx i).1.val = i.1.val + 1 := by
  unfold embedIdx
  split_ifs with h
  · simp [idx₁, h]
  · rfl

theorem embedIdx_injective : Function.Injective (embedIdx (A := A) (B := B) (Q := Q)) := by
  intro i i' h
  have := congrArg (fun x => x.1.val) h
  simp only [embedIdx_val] at this
  exact Subtype.ext (Fin.ext (by omega))

/-- **The fused errors sum to the original ones.** -/
theorem sum_fuseError (ε : (orig A B Q).ChallengeIdx → ℝ≥0) :
    ∑ i, fuseError ε i = ∑ i, ε i := by
  classical
  have hsplit : ∀ i, fuseError ε i =
      ε (embedIdx i) + if i = fusedIdx₀ A B Q then ε (idx₀ A B Q) else 0 := by
    intro i
    unfold fuseError embedIdx
    by_cases h : i.1.val = 0
    · obtain rfl := eq_fusedIdx₀ h
      simp [add_comm]
    · have hne : i ≠ fusedIdx₀ A B Q := fun e => h (by rw [e])
      simp [h, hne]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (idx₀ A B Q)), add_comm]
  congr 1
  rw [← Finset.sum_image fun x _ y _ h => embedIdx_injective h]
  congr 1
  ext i'
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  constructor
  · rintro ⟨i, rfl⟩ e
    have := congrArg (fun x => x.1.val) e
    simp [embedIdx_val, idx₀] at this
  · intro hne
    have h0 : i'.1.val ≠ 0 := fun h => hne (Subtype.ext (Fin.ext h))
    have hlt : i'.1.val - 1 < 1 + m := by have := i'.1.2; omega
    by_cases h1 : i'.1.val = 1
    · refine ⟨fusedIdx₀ A B Q, Subtype.ext (Fin.ext ?_)⟩
      have := embedIdx_val (fusedIdx₀ A B Q)
      simp only at this
      omega
    · have hdir : (fused A B Q).dir ⟨i'.1.val - 1, hlt⟩ = .V_to_P :=
        (orig_dir_shift i'.1 ⟨i'.1.val - 1, hlt⟩ (by simp; omega) (by simp; omega)).symm.trans i'.2
      refine ⟨⟨_, hdir⟩, Subtype.ext (Fin.ext ?_)⟩
      have := embedIdx_val (⟨⟨_, hlt⟩, hdir⟩ : (fused A B Q).ChallengeIdx)
      simp only at this
      omega

/-! ### Counting at the fused move -/

open Classical in
/-- **A pair of challenges** `(a, b)` makes a two-step state true only through a first step that
does (at most `e₀|A|` values `a`, each with every `b`) or a second step from a false first step
(at most `e₁|B|` values `b` for each `a`). -/
theorem card_filter_prod_le {α β : Type} [Fintype α] [Fintype β] (P : α → Prop)
    (R : α → β → Prop) (e₀ e₁ : ℝ≥0)
    (h₀ : ((Finset.univ.filter P).card : ℝ≥0) ≤ e₀ * Fintype.card α)
    (h₁ : ∀ a, ((Finset.univ.filter fun b => ¬ P a ∧ R a b).card : ℝ≥0) ≤ e₁ * Fintype.card β) :
    ((Finset.univ.filter fun x : α × β => R x.1 x.2).card : ℝ≥0) ≤
      (e₀ + e₁) * Fintype.card (α × β) := by
  have hsub : (Finset.univ.filter fun x : α × β => R x.1 x.2) ⊆
      (Finset.univ.filter P) ×ˢ Finset.univ ∪
        Finset.univ.filter fun x : α × β => ¬ P x.1 ∧ R x.1 x.2 := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product, and_true] at hx ⊢
    by_cases hp : P x.1
    · exact Or.inl hp
    · exact Or.inr ⟨hp, hx⟩
  have hfib : (Finset.univ.filter fun x : α × β => ¬ P x.1 ∧ R x.1 x.2).card =
      ∑ a, (Finset.univ.filter fun b => ¬ P a ∧ R a b).card := by
    simp only [Finset.card_filter]
    exact Fintype.sum_prod_type _
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_product, Finset.card_univ, hfib] at hcard
  have hcard' : ((Finset.univ.filter fun x : α × β => R x.1 x.2).card : ℝ≥0) ≤
      ((Finset.univ.filter P).card : ℝ≥0) * Fintype.card β +
        ∑ a, ((Finset.univ.filter fun b => ¬ P a ∧ R a b).card : ℝ≥0) := by
    exact_mod_cast hcard
  refine hcard'.trans ?_
  have hsum : ∑ a, ((Finset.univ.filter fun b => ¬ P a ∧ R a b).card : ℝ≥0) ≤
      ∑ _a : α, e₁ * Fintype.card β := Finset.sum_le_sum fun a _ => h₁ a
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc ((Finset.univ.filter P).card : ℝ≥0) * Fintype.card β +
        ∑ a, ((Finset.univ.filter fun b => ¬ P a ∧ R a b).card : ℝ≥0)
      ≤ e₀ * Fintype.card α * Fintype.card β + Fintype.card α * (e₁ * Fintype.card β) :=
        add_le_add (mul_le_mul_of_nonneg_right h₀ (by positivity)) hsum
    _ = (e₀ + e₁) * Fintype.card (α × β) := by
        rw [Fintype.card_prod]
        push_cast
        ring

/-! ### Fusing a claim reduction -/

variable [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] {Ctx : Type}
  {ε : (orig A B Q).ChallengeIdx → ℝ≥0}

/-- The original full length is the shifted fused full length. -/
theorem shiftLen_last : (Fin.last (1 + (1 + m))).val = shiftLen (Fin.last (1 + m)).val := by
  simp [shiftLen_of_ne]
  omega

/-- The original prefix length of a fused prefix of length `k`. -/
def shift (k : Fin (1 + m + 1)) : Fin (1 + (1 + m) + 1) :=
  ⟨shiftLen k.val, by unfold shiftLen; split_ifs <;> omega⟩

/-- **The full original transcript of a full fused transcript.** -/
def unfuseFull (tr : (fused A B Q).Transcript (Fin.last (1 + m))) :
    (orig A B Q).Transcript (Fin.last (1 + (1 + m))) :=
  unfuse tr _ shiftLen_last

open Classical in
/-- **A claim reduction with its two leading verifier moves fused**: the state on a fused prefix
is the original state on the original prefix (`unfuse`); the error at the fused move is the sum
of the two original errors (`card_filter_prod_le`), and each later move keeps its error. -/
def ClaimReduction.fuse (R : ClaimReduction (orig A B Q) Ctx ε) :
    ClaimReduction (fused A B Q) Ctx (fuseError ε) where
  claim := R.claim
  claimOut c tr := R.claimOut c (unfuseFull tr)
  S k c tr := R.S (shift k) c (unfuse tr (shift k) rfl)
  start c tr h := R.start c _ h
  next mv hdir c tr msg hnot hS := by
    have hj := fused_val_ne_of_dir hdir
    let i : Fin (1 + (1 + m)) := ⟨mv.val + 1, by omega⟩
    have hdir' : (orig A B Q).dir i = .P_to_V := (orig_dir_shift i mv rfl hj).trans hdir
    have hnot' : ¬ R.S i.castSucc c (unfuse tr i.castSucc (by simp [i, shiftLen_of_ne hj])) :=
      fun h => hnot ((unfuse_congr tr (Fin.ext (by simp [shift, i, shiftLen_of_ne hj])) _ _
        (S := fun k t => R.S k c t)).mpr h)
    have hS' : R.S i.succ c (unfuse ((fused A B Q).concat tr msg) i.succ
        (by simp [i, shiftLen_of_ne])) :=
      (unfuse_congr _ (Fin.ext (by simp [shift, i, shiftLen_of_ne])) _ _
        (S := fun k t => R.S k c t)).mp hS
    rw [unfuse_concat_shift mv hj i rfl] at hS'
    exact R.next i hdir' c _ _ hnot' hS'
  full c tr h := (unfuse_congr tr (Fin.ext (by simp [shift, shiftLen_of_ne]; omega)) _ _
    (S := fun k t => R.S k c t)).mp (R.full c _ h)
  rbr c i tr := by
    by_cases h : i.1.val = 0
    · obtain rfl := eq_fusedIdx₀ h
      rw [fuseError_fusedIdx₀]
      generalize hT0 : unfuse tr (⟨0, by omega⟩ : Fin (1 + (1 + m))).castSucc
          (by simp [shiftLen]) = T0
      have hS0 : R.S (shift (fusedIdx₀ A B Q).1.castSucc) c
            (unfuse tr (shift (fusedIdx₀ A B Q).1.castSucc) rfl) ↔
          R.S (idx₀ A B Q).1.castSucc c T0 :=
        by rw [← hT0]; exact unfuse_congr tr (Fin.ext rfl) _ _ (S := fun k t => R.S k c t)
      have hS2 : ∀ ch : (fused A B Q).Challenge (fusedIdx₀ A B Q),
          R.S (shift (fusedIdx₀ A B Q).1.succ) c
            (unfuse ((fused A B Q).concat tr ch) (shift (fusedIdx₀ A B Q).1.succ) rfl) ↔
          R.S (idx₁ A B Q).1.succ c ((orig A B Q).concat (m := ⟨1, by omega⟩)
            ((orig A B Q).concat (m := ⟨0, by omega⟩) T0
              (cast (orig_Type_zero _ rfl).symm (cast (fused_Type_zero _ rfl) ch).1))
            (cast (orig_Type_one _ rfl).symm (cast (fused_Type_zero _ rfl) ch).2)) := by
        intro ch
        rw [← hT0, ← unfuse_concat_zero]
        exact unfuse_congr _ (Fin.ext (by simp [shift, shiftLen_of_ne, fusedIdx₀, idx₁])) _ _
          (S := fun k t => R.S k c t)
      refine @card_le_of_mapsTo_cast _ (A × B) (instFintypeChallengeHAppendHAddNat (fusedIdx₀ A B Q))
        _ (fused_Type_zero (fusedIdx₀ A B Q).1 rfl) _ (t := Finset.univ.filter fun x : A × B => ¬ R.S (idx₀ A B Q).1.castSucc c T0 ∧
          R.S (idx₁ A B Q).1.succ c ((orig A B Q).concat (m := ⟨1, by omega⟩)
            ((orig A B Q).concat (m := ⟨0, by omega⟩) T0
              (cast (orig_Type_zero _ rfl).symm x.1))
            (cast (orig_Type_one _ rfl).symm x.2))) _ (fun ch hch => ?_) ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
        exact ⟨fun h' => hch.1 (hS0.mpr h'), (hS2 ch).mp hch.2⟩
      · by_cases h0 : R.S (idx₀ A B Q).1.castSucc c T0
        · rw [Finset.filter_eq_empty_iff.mpr fun x _ hx => hx.1 h0]
          simp
        · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (card_filter_prod_le
            (fun a => R.S (idx₀ A B Q).1.succ c ((orig A B Q).concat (m := ⟨0, by omega⟩) T0
              (cast (orig_Type_zero _ rfl).symm a)))
            (fun a b => R.S (idx₁ A B Q).1.succ c ((orig A B Q).concat (m := ⟨1, by omega⟩)
              ((orig A B Q).concat (m := ⟨0, by omega⟩) T0 (cast (orig_Type_zero _ rfl).symm a))
              (cast (orig_Type_one _ rfl).symm b))) (ε (idx₀ A B Q)) (ε (idx₁ A B Q)) ?_ fun a => ?_)
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact hx.2
          · refine @card_le_of_mapsTo_cast A _ _ (instFintypeChallengeHAppendHAddNat (idx₀ A B Q))
              (orig_Type_zero _ rfl).symm _ _ _ (fun a ha => ?_)
              (R.rbr c (idx₀ A B Q) T0)
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            exact ⟨h0, ha⟩
          · exact @card_le_of_mapsTo_cast B _ _ (instFintypeChallengeHAppendHAddNat (idx₁ A B Q))
              (orig_Type_one _ rfl).symm _ _ _ (fun b hb => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
              exact hb) (R.rbr c (idx₁ A B Q) _)
    · rw [fuseError_shiftIdx ε i h]
      let i' := (shiftIdx i h).1
      have hi : i'.val = i.1.val + 1 := rfl
      refine card_le_of_mapsTo_cast (orig_Type_shift i' i.1 hi h).symm (fun ch hch => ?_)
        (R.rbr c (shiftIdx i h) (unfuse tr i'.castSucc (by simp [i', shiftLen_of_ne h])))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      refine ⟨fun h' => hch.1 ((unfuse_congr tr (Fin.ext (by simp [shift, i', shiftLen_of_ne h]))
        _ _ (S := fun k t => R.S k c t)).mpr h'), ?_⟩
      have h2 := (unfuse_congr _ (k₂ := i'.succ) (Fin.ext (by simp [shift, i', shiftLen_of_ne])) _
        (by simp [i', shiftLen_of_ne]) (S := fun k t => R.S k c t)).mp hch.2
      rw [unfuse_concat_shift i.1 h i' hi] at h2
      exact h2

@[simp] theorem ClaimReduction.fuse_claim (R : ClaimReduction (orig A B Q) Ctx ε) (c : Ctx) :
    R.fuse.claim c ↔ R.claim c := Iff.rfl

@[simp] theorem ClaimReduction.fuse_claimOut (R : ClaimReduction (orig A B Q) Ctx ε) (c : Ctx)
    (tr : (fused A B Q).Transcript (Fin.last (1 + m))) :
    R.fuse.claimOut c tr ↔ R.claimOut c (unfuseFull tr) := Iff.rfl

/-! ### Full transcripts and challenges -/

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
/-- **The fused full transcript of a full original transcript**: `(a, b)` at the fused move, then
the later moves one position earlier. -/
def fuseFull (tr : (orig A B Q).Transcript (Fin.last (1 + (1 + m)))) :
    (fused A B Q).Transcript (Fin.last (1 + m)) := fun j =>
  if h : j.val = 0 then
    cast (fused_Type_zero (Fin.castLE (by omega) j) h).symm
      (cast (orig_Type_zero _ rfl) (tr ⟨0, by simp⟩), cast (orig_Type_one _ rfl) (tr ⟨1, by simp⟩))
  else
    cast (orig_Type_shift ⟨j.val + 1, by omega⟩ (Fin.castLE (by omega) j) rfl h)
      (tr ⟨j.val + 1, by have := j.2; simp at this ⊢; omega⟩)

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
theorem fuseFull_heq_shift (tr : (orig A B Q).Transcript (Fin.last (1 + (1 + m))))
    (j : Fin (Fin.last (1 + m))) (h : j.val ≠ 0) (H : j.val + 1 < 1 + (1 + m)) :
    HEq (fuseFull tr j) (tr ⟨j.val + 1, H⟩) := by
  unfold fuseFull
  rw [dite_cond_eq_false (eq_false h)]
  exact cast_heq _ _

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
theorem cast_fuseFull_zero (tr : (orig A B Q).Transcript (Fin.last (1 + (1 + m))))
    (j : Fin (Fin.last (1 + m))) (h : j.val = 0) :
    cast (fused_Type_zero (Fin.castLE (by omega) j) h) (fuseFull tr j) =
      (cast (orig_Type_zero _ rfl) (tr ⟨0, by simp⟩), cast (orig_Type_one _ rfl) (tr ⟨1, by simp⟩)) := by
  unfold fuseFull
  rw [dite_cond_eq_true (eq_true h), cast_cast, cast_eq]

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
/-- Reading back the original transcript of a fused full transcript gives the original one. -/
theorem unfuseFull_fuseFull (tr : (orig A B Q).Transcript (Fin.last (1 + (1 + m)))) :
    unfuseFull (fuseFull tr) = tr := by
  funext l
  apply eq_of_heq
  have hl := l.2
  simp only [Fin.val_last] at hl
  by_cases h0 : l.val = 0
  · refine (unfuse_heq_zero _ _ _ l h0 (by simp)).trans ?_
    rw [cast_fuseFull_zero tr _ rfl]
    dsimp only
    refine (cast_heq _ _).trans ?_
    have e : l = ⟨0, by simp⟩ := Fin.ext h0
    subst e
    rfl
  · by_cases h1 : l.val = 1
    · refine (unfuse_heq_one _ _ _ l h1 (by simp)).trans ?_
      rw [cast_fuseFull_zero tr _ rfl]
      dsimp only
      refine (cast_heq _ _).trans ?_
      have e : l = ⟨1, by simp⟩ := Fin.ext h1
      subst e
      rfl
    · refine (unfuse_heq_shift _ _ _ l h0 h1 (by simp; omega)).trans ?_
      refine (fuseFull_heq_shift tr ⟨l.val - 1, show l.val - 1 < 1 + m by omega⟩
        (show l.val - 1 ≠ 0 by omega) (show l.val - 1 + 1 < 1 + (1 + m) by omega)).trans ?_
      have e : (⟨l.val - 1 + 1, show l.val - 1 + 1 < 1 + (1 + m) by omega⟩ :
          Fin (Fin.last (1 + (1 + m)))) = l := Fin.ext (show l.val - 1 + 1 = l.val by omega)
      rw [e]

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
/-- Fusing the original transcript of a fused full transcript gives the fused one. -/
theorem fuseFull_unfuseFull (tr : (fused A B Q).Transcript (Fin.last (1 + m))) :
    fuseFull (unfuseFull tr) = tr := by
  funext j
  by_cases h : j.val = 0
  · apply (cast_inj (fused_Type_zero (Fin.castLE (by omega) j) h)).mp
    rw [cast_fuseFull_zero _ _ h]
    refine Prod.ext ?_ ?_
    · obtain rfl : j = ⟨0, by simp⟩ := Fin.ext h
      simp [unfuseFull, unfuse]
      exact eq_of_heq ((cast_heq _ _).trans HEq.rfl)
    · obtain rfl : j = ⟨0, by simp⟩ := Fin.ext h
      simp [unfuseFull, unfuse]
  · have hj2 : j.val < 1 + m := j.2
    apply eq_of_heq
    refine (fuseFull_heq_shift (unfuseFull tr) j h (by omega)).trans ?_
    refine (unfuse_heq_shift tr (Fin.last _) shiftLen_last
      ⟨j.val + 1, show j.val + 1 < 1 + (1 + m) by omega⟩ (show j.val + 1 ≠ 0 by omega)
      (show j.val + 1 ≠ 1 by omega) (show j.val + 1 - 1 < 1 + m by omega)).trans ?_
    have e : (⟨j.val + 1 - 1, show j.val + 1 - 1 < 1 + m by omega⟩ : Fin (Fin.last (1 + m))) = j :=
      Fin.ext (by simp)
    rw [e]

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
variable (A B Q) in
/-- **The transcript bijection**: original full transcripts and fused full transcripts. -/
def fuseEquiv : (orig A B Q).Transcript (Fin.last (1 + (1 + m))) ≃
    (fused A B Q).Transcript (Fin.last (1 + m)) where
  toFun := fuseFull
  invFun := unfuseFull
  left_inv := unfuseFull_fuseFull
  right_inv := fuseFull_unfuseFull

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
/-- **The original challenges of fused challenges**: the two coordinates of the fused challenge,
then the later challenges one position later. -/
def unfuseChallenges (ch : (fused A B Q).Challenges) : (orig A B Q).Challenges := fun i =>
  if h0 : i.1.val = 0 then
    cast (orig_Type_zero _ h0).symm (cast (fused_Type_zero _ rfl) (ch (fusedIdx₀ A B Q))).1
  else if h1 : i.1.val = 1 then
    cast (orig_Type_one _ h1).symm (cast (fused_Type_zero _ rfl) (ch (fusedIdx₀ A B Q))).2
  else
    cast (orig_Type_shift i.1 ⟨i.1.val - 1, by omega⟩ (by simp; omega) (by simp; omega)).symm
      (ch ⟨⟨i.1.val - 1, by omega⟩,
        (orig_dir_shift i.1 ⟨i.1.val - 1, by omega⟩ (by simp; omega) (by simp; omega)).symm.trans
          i.2⟩)

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
/-- **The fused challenges of original challenges**: the pair of the two leading challenges at the
fused move, then each later challenge one position earlier; the inverse of `unfuseChallenges`. -/
def fuseChallenges (c : (orig A B Q).Challenges) : (fused A B Q).Challenges := fun i =>
  if h : i.1.val = 0 then
    cast (fused_Type_zero _ h).symm
      (cast (orig_Type_zero _ rfl) (c (idx₀ A B Q)), cast (orig_Type_one _ rfl) (c (idx₁ A B Q)))
  else cast (orig_Type_shift (shiftIdx i h).1 i.1 rfl h) (c (shiftIdx i h))

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
theorem unfuseChallenges_fuseChallenges (c : (orig A B Q).Challenges) :
    unfuseChallenges (fuseChallenges c) = c := by
  funext j
  apply eq_of_heq
  unfold unfuseChallenges
  by_cases h0 : j.1.val = 0
  · obtain rfl : j = idx₀ A B Q := Subtype.ext (Fin.ext h0)
    rw [dite_cond_eq_true (eq_true rfl)]
    refine (cast_heq _ _).trans ?_
    unfold fuseChallenges
    rw [dite_cond_eq_true (eq_true rfl), cast_cast, cast_eq]
    dsimp only
    exact cast_heq _ _
  by_cases h1 : j.1.val = 1
  · obtain rfl : j = idx₁ A B Q := Subtype.ext (Fin.ext h1)
    rw [dite_cond_eq_false (eq_false h0), dite_cond_eq_true (eq_true rfl)]
    refine (cast_heq _ _).trans ?_
    unfold fuseChallenges
    rw [dite_cond_eq_true (eq_true rfl), cast_cast, cast_eq]
    dsimp only
    exact cast_heq _ _
  rw [dite_cond_eq_false (eq_false h0), dite_cond_eq_false (eq_false h1)]
  refine (cast_heq _ _).trans ?_
  unfold fuseChallenges
  split
  · next h2 => exact absurd h2 (show j.1.val - 1 ≠ 0 by omega)
  · refine (cast_heq _ _).trans ?_
    exact congr_arg_heq c (Subtype.ext (Fin.ext (show j.1.val - 1 + 1 = j.1.val by omega)))

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
theorem fuseChallenges_unfuseChallenges (ch : (fused A B Q).Challenges) :
    fuseChallenges (unfuseChallenges ch) = ch := by
  funext i
  apply eq_of_heq
  unfold fuseChallenges
  by_cases h0 : i.1.val = 0
  · obtain rfl := eq_fusedIdx₀ h0
    rw [dite_cond_eq_true (eq_true rfl)]
    refine (cast_heq _ _).trans ?_
    unfold unfuseChallenges
    rw [dite_cond_eq_true (eq_true rfl), dite_cond_eq_false (eq_false (by simp)),
      dite_cond_eq_true (eq_true rfl), cast_cast, cast_eq, cast_cast, cast_eq, Prod.mk.eta]
    exact cast_heq _ _
  rw [dite_cond_eq_false (eq_false h0)]
  refine (cast_heq _ _).trans ?_
  unfold unfuseChallenges
  split
  · next h1 => exact absurd h1 (show i.1.val + 1 ≠ 0 by omega)
  split
  · next h2 => exact absurd h2 (show i.1.val + 1 ≠ 1 by omega)
  refine (cast_heq _ _).trans ?_
  exact congr_arg_heq ch (Subtype.ext (Fin.ext (show i.1.val + 1 - 1 = i.1.val by omega)))

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
variable (A B Q) in
/-- **The challenge bijection**: original challenge vectors and fused challenge vectors. -/
def challengesFuseEquiv : (orig A B Q).Challenges ≃ (fused A B Q).Challenges where
  toFun := fuseChallenges
  invFun := unfuseChallenges
  left_inv := unfuseChallenges_fuseChallenges
  right_inv := fuseChallenges_unfuseChallenges

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
theorem unfuseChallenges_bijective :
    Function.Bijective (unfuseChallenges (A := A) (B := B) (Q := Q)) :=
  (challengesFuseEquiv A B Q).symm.bijective

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
/-- **An honest causal family with its two leading challenges fused**: the original family on the
original challenges, read through the transcript bijection. -/
def CausalTranscript.fuse (T : CausalTranscript (orig A B Q)) : CausalTranscript (fused A B Q) where
  transcript ch := fuseFull (T.transcript (unfuseChallenges ch))
  challenge ch i := by
    by_cases h : i.1.val = 0
    · obtain rfl := eq_fusedIdx₀ h
      apply (cast_inj (fused_Type_zero (fusedIdx₀ A B Q).1 rfl)).mp
      rw [cast_fuseFull_zero _ _ rfl]
      have h0 := T.challenge (unfuseChallenges ch) (idx₀ A B Q)
      have h1 := T.challenge (unfuseChallenges ch) (idx₁ A B Q)
      refine Prod.ext ?_ ?_
      · dsimp only
        rw [h0]
        simp [unfuseChallenges]
        exact eq_of_heq ((cast_heq _ _).trans HEq.rfl)
      · dsimp only
        rw [h1]
        simp [unfuseChallenges]
    · have hi2 : i.1.val < 1 + m := i.1.2
      apply eq_of_heq
      refine (fuseFull_heq_shift _ i.1 h (by omega)).trans ?_
      refine (heq_of_eq (T.challenge (unfuseChallenges ch) (shiftIdx i h))).trans ?_
      unfold unfuseChallenges
      have h0' : ¬ (shiftIdx i h).1.val = 0 := by rw [shiftIdx_val]; omega
      have h1' : ¬ (shiftIdx i h).1.val = 1 := by rw [shiftIdx_val]; omega
      rw [dite_cond_eq_false (eq_false h0'), dite_cond_eq_false (eq_false h1')]
      refine (cast_heq _ _).trans ?_
      exact congr_arg_heq ch (Subtype.ext (Fin.ext (by simp)))
  causal mv ch ch' hagree := by
    have hj : mv.1.val ≠ 0 := fused_val_ne_of_dir mv.2
    apply eq_of_heq
    refine (fuseFull_heq_shift _ mv.1 hj (by omega)).trans (HEq.trans ?_
      (fuseFull_heq_shift _ mv.1 hj (by omega)).symm)
    refine heq_of_eq (T.causal ⟨⟨mv.1.val + 1, by omega⟩,
      (orig_dir_shift _ mv.1 rfl hj).trans mv.2⟩ _ _ fun j' hj' => ?_)
    have hlt : j'.1.val < mv.1.val + 1 := hj'
    have h0 : ch (fusedIdx₀ A B Q) = ch' (fusedIdx₀ A B Q) :=
      hagree _ (show (0 : ℕ) < mv.1.val by omega)
    unfold unfuseChallenges
    split_ifs with ha hb
    · rw [h0]
    · rw [h0]
    · congr 1
      exact hagree _ (show j'.1.val - 1 < mv.1.val by omega)

omit [Fintype A] [Fintype B] [∀ i, Fintype (Q.Challenge i)] in
@[simp] theorem CausalTranscript.fuse_transcript (T : CausalTranscript (orig A B Q))
    (ch : (fused A B Q).Challenges) :
    T.fuse.transcript ch = fuseEquiv A B Q (T.transcript (unfuseChallenges ch)) := rfl

/-! ### Transport along an equality of protocols -/

/-- A full transcript of `t` as one of `s`, for `s = t`. -/
def specTranscript : {s t : Σ n, ProtocolSpec n} → s = t →
    t.2.Transcript (Fin.last t.1) → s.2.Transcript (Fin.last s.1)
  | _, _, rfl, tr => tr

/-- The challenges of `t` as those of `s`, for `s = t`. -/
def specChallenges : {s t : Σ n, ProtocolSpec n} → s = t → t.2.Challenges → s.2.Challenges
  | _, _, rfl, ch => ch

/-- A verifier move of `t` as one of `s`, for `s = t`. -/
def specIdx : {s t : Σ n, ProtocolSpec n} → s = t → t.2.ChallengeIdx → s.2.ChallengeIdx
  | _, _, rfl, i => i

theorem specTranscript_bijective {s t : Σ n, ProtocolSpec n} (h : s = t) :
    Function.Bijective (specTranscript h) := by
  cases h
  exact Function.bijective_id

theorem specChallenges_bijective {s t : Σ n, ProtocolSpec n} (h : s = t) :
    Function.Bijective (specChallenges h) := by
  cases h
  exact Function.bijective_id

theorem specTranscript_symm {s t : Σ n, ProtocolSpec n} (h : s = t)
    (tr : s.2.Transcript (Fin.last s.1)) : specTranscript h (specTranscript h.symm tr) = tr := by
  cases h
  rfl

/-- A claim reduction on `s` as one on `t`, for `s = t`, with the errors read through `specIdx`;
the counts do not depend on the enumeration of the challenges. -/
def ClaimReduction.ofSpecEq {s t : Σ n, ProtocolSpec n} (h : s = t) {Ctx : Type}
    (instS : ∀ i, Fintype (s.2.Challenge i)) (instT : ∀ i, Fintype (t.2.Challenge i))
    {ε : s.2.ChallengeIdx → ℝ≥0} (R : @ClaimReduction s.1 s.2 Ctx instS ε) :
    @ClaimReduction t.1 t.2 Ctx instT (ε ∘ specIdx h) := by
  cases h
  have e : instT = instS := Subsingleton.elim _ _
  subst e
  exact R

theorem ClaimReduction.ofSpecEq_claim {s t : Σ n, ProtocolSpec n} (h : s = t) {Ctx : Type}
    (instS : ∀ i, Fintype (s.2.Challenge i)) (instT : ∀ i, Fintype (t.2.Challenge i))
    {ε : s.2.ChallengeIdx → ℝ≥0} (R : @ClaimReduction s.1 s.2 Ctx instS ε) (c : Ctx) :
    (ClaimReduction.ofSpecEq h instS instT R).claim c ↔ R.claim c := by
  cases h
  obtain rfl : instT = instS := Subsingleton.elim _ _
  rfl

theorem ClaimReduction.ofSpecEq_claimOut {s t : Σ n, ProtocolSpec n} (h : s = t) {Ctx : Type}
    (instS : ∀ i, Fintype (s.2.Challenge i)) (instT : ∀ i, Fintype (t.2.Challenge i))
    {ε : s.2.ChallengeIdx → ℝ≥0} (R : @ClaimReduction s.1 s.2 Ctx instS ε) (c : Ctx)
    (tr : t.2.Transcript (Fin.last t.1)) :
    (ClaimReduction.ofSpecEq h instS instT R).claimOut c tr ↔ R.claimOut c (specTranscript h tr) := by
  cases h
  obtain rfl : instT = instS := Subsingleton.elim _ _
  rfl

/-- An honest causal family on `s` as one on `t`, for `s = t`. -/
def CausalTranscript.ofSpecEq : {s t : Σ n, ProtocolSpec n} → s = t →
    CausalTranscript s.2 → CausalTranscript t.2
  | _, _, rfl, T => T

theorem CausalTranscript.ofSpecEq_transcript {s t : Σ n, ProtocolSpec n} (h : s = t)
    (T : CausalTranscript s.2) (ch : t.2.Challenges) :
    (T.ofSpecEq h).transcript ch = specTranscript h.symm (T.transcript (specChallenges h ch)) := by
  cases h
  rfl

end GordieHowe.IOP
