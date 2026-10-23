-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.CircuitProtocol
public import GordieHowe.Model.IOP.Append

@[expose] public section

/-!
# Typed no-copy Longfellow GKR schedule

The verifier first samples the initial point of `F^d`, for the circuit's output dimension `d`
(the paper's `ρ^(0) ← K^{m_0}`, prot:gkr). Each layer samples
alpha and beta, then interleaves a two-coordinate masked polynomial message
with its scalar challenge, in bit-first/hand-second order, and ends with two
masked wire claims. The terminal input-binding alpha is sampled last.
This describes transcript chronology rather than the serialization order of
`zk_proof.h`. Commitment and the packed terminal M message are separate phases.
-/
namespace GordieHowe.GKR.Schedule
open IOP

variable (F : Type) [Field F]

/-- A single typed message with its fixed sender. -/
def one (dir : Direction) (Msg : Type) : ProtocolSpec 1 where
  dir _ := dir
  «Type» _ := Msg

def empty : ProtocolSpec 0 where
  dir := Fin.elim0
  «Type» := Fin.elim0

/-- Two moves per omitted-p(1) sumcheck round. -/
def roundLength : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + (1 + roundLength k)

@[simp] theorem roundLength_eq (k : ℕ) : roundLength k = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [roundLength, ih]; omega

def rounds : (k : ℕ) → ProtocolSpec (roundLength k)
  | 0 => empty
  | k + 1 => one .P_to_V (F × F) ++ (one .V_to_P F ++ rounds k)

/-- Recursion follows the source circuit from output toward input. -/
def circuitLength {d : ℕ} : GKR.Circuit F d → ℕ
  | .input _ => 1
  | .layer (inDim := b) _ tail => 1 + (roundLength (2 * b) + (1 + circuitLength tail))

def circuit {d : ℕ} : (C : GKR.Circuit F d) → ProtocolSpec (circuitLength F C)
  | .input _ => one .V_to_P F
  | .layer (inDim := b) _ tail =>
    one .V_to_P (F × F) ++
      (rounds F (2 * b) ++ (one .P_to_V (F × F) ++ circuit tail))

/-- The initial verifier move: a point of `F^d`, for the output dimension `d`. -/
def initial (d : ℕ) : ProtocolSpec 1 := one .V_to_P (Fin d → F)

def spec {d : ℕ} (C : GKR.Circuit F d) : ProtocolSpec (1 + circuitLength F C) :=
  initial F d ++ circuit F C

/-- Read the completed one-message phase without imposing message semantics. -/
def oneValue {dir : Direction} {Msg : Type}
    (tr : (one dir Msg).Transcript (Fin.last 1)) : Msg := tr ⟨0, by decide⟩

/-- The first message of a phase is available as soon as one message exists. -/
def head {dir : Direction} {Msg : Type} {n : ℕ} {Q : ProtocolSpec n}
    {m : Fin (1 + n + 1)} (tr : (one dir Msg ++ Q).Transcript m)
    (hm : 1 ≤ m.val) : Msg := oneValue (tr.fst (Fin.last 1) hm)

/-- Reading the first message is invariant under later transcript extension. -/
theorem head_concat {dir : Direction} {Msg : Type} {n : ℕ} {Q : ProtocolSpec n}
    {m : Fin (1 + n)} (tr : (one dir Msg ++ Q).Transcript m.castSucc)
    (msg : (one dir Msg ++ Q).Type m) (hm : 1 ≤ m.val) :
    head ((one dir Msg ++ Q).concat tr msg) (by simp) = head tr hm := by
  unfold head
  rw [ProtocolSpec.Transcript.fst_concat_of_le _ _ _ hm]

/-- Completed initial verifier randomness and remaining circuit transcript. -/
def initialValues {d : ℕ} (C : GKR.Circuit F d)
    (tr : (spec F C).Transcript (Fin.last (1 + circuitLength F C))) :
    Fin d → F := oneValue tr.left

def circuitTranscript {d : ℕ} (C : GKR.Circuit F d)
    (tr : (spec F C).Transcript (Fin.last (1 + circuitLength F C))) :
    (circuit F C).Transcript (Fin.last (circuitLength F C)) := tr.right

/-- Decode the alternating prover pair and verifier scalar into round messages. -/
def roundMessages : (k : ℕ) →
    (rounds F k).Transcript (Fin.last (roundLength k)) →
    Fin k → LayerProtocol.Message F
  | 0, _ => Fin.elim0
  | k + 1, tr =>
    let pair := oneValue tr.left
    let rest := tr.right
    Fin.cases ⟨pair.1, pair.2, oneValue rest.left⟩ (roundMessages k rest.right)

/-- Exact recursive trace extraction from the typed circuit transcript. -/
def circuitTrace {d : ℕ} : (C : GKR.Circuit F d) →
    (circuit F C).Transcript (Fin.last (circuitLength F C)) → CircuitProtocol.Trace C
  | .input _, tr => oneValue tr
  | .layer (inDim := b) _ tail, tr =>
    let ab := oneValue tr.left
    let rest := tr.right
    let wc := oneValue rest.right.left
    { alpha := ab.1
      beta := ab.2
      rounds := fun i => roundMessages F (2*b) rest.left
        ⟨i.val, by simpa only [LayerSumcheck.schedule_length] using i.isLt⟩
      wc := ![wc.1, wc.2]
      tail := circuitTrace tail rest.right.right }

def trace {d : ℕ} (C : GKR.Circuit F d)
    (tr : (spec F C).Transcript (Fin.last (1 + circuitLength F C))) :
    CircuitProtocol.Trace C := circuitTrace F C (circuitTranscript F C tr)

@[simp] theorem roundMessages_zero (k : ℕ)
    (tr : (rounds F (k+1)).Transcript (Fin.last (roundLength (k+1)))) :
    roundMessages F (k+1) tr 0 =
      ⟨(oneValue tr.left).1, (oneValue tr.left).2,
        oneValue tr.right.left⟩ := rfl

@[simp] theorem roundMessages_succ (k : ℕ)
    (tr : (rounds F (k+1)).Transcript (Fin.last (roundLength (k+1)))) (i : Fin k) :
    roundMessages F (k+1) tr i.succ = roundMessages F k tr.right.right i := rfl

/-- Agreement through a global position restricts to the first appended phase. -/
theorem left_agrees {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (tr tr' : (A ++ B).Transcript (Fin.last (a+b))) (k : ℕ)
    (h : ∀ j, j.val ≤ k → tr j = tr' j) :
    ∀ j, j.val ≤ k → tr.left j = tr'.left j := by
  intro j hj
  simp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.fst, Prod.fst]
  congr 1
  exact h ⟨j.val, by simpa using Nat.lt_add_right b j.isLt⟩ hj

/-- Agreement in a later phase uses its global offset. -/
theorem right_agrees {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (tr tr' : (A ++ B).Transcript (Fin.last (a+b))) (k : ℕ)
    (h : ∀ j, j.val ≤ a+k → tr j = tr' j) :
    ∀ j, j.val ≤ k → tr.right j = tr'.right j := by
  intro j hj
  simp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.snd, Prod.snd]
  congr 1
  exact h ⟨a+j.val, by simpa using Nat.add_lt_add_left j.isLt a⟩ (Nat.add_le_add_left hj a)

/-- Replacing a message in the second phase leaves the entire first phase fixed. -/
theorem left_update_right {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (tr : (A ++ B).Transcript (Fin.last (a+b))) (i : Fin b)
    (msg : (A ++ B).Type (i.natAdd a)) :
    (ProtocolSpec.Transcript.left (P₁ := A) (P₂ := B) (Function.update tr (i.natAdd a) msg)) = tr.left := by
  classical
  funext j
  simp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.fst, Prod.fst]
  congr 1
  apply Function.update_of_ne
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd] at this
  have hj : j.val < a := j.isLt
  omega

/-- Replacing an earlier message leaves the entire second phase fixed. -/
theorem right_update_left {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (tr : (A ++ B).Transcript (Fin.last (a+b))) (i : Fin a)
    (msg : (A ++ B).Type (i.castAdd b)) :
    (ProtocolSpec.Transcript.right (P₁ := A) (P₂ := B) (Function.update tr (i.castAdd b) msg)) = tr.right := by
  classical
  funext j
  simp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.snd, Prod.snd]
  congr 1
  apply Function.update_of_ne
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd] at this
  have hi : i.val < a := i.isLt
  omega

/-- Updating a first-phase message projects to precisely that local update. -/
theorem left_update_left {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (tr : (A ++ B).Transcript (Fin.last (a+b))) (i : Fin a)
    (msg : (A ++ B).Type (i.castAdd b)) :
    (ProtocolSpec.Transcript.left (P₁ := A) (P₂ := B)
      (Function.update tr (i.castAdd b) msg)) =
    Function.update tr.left i (cast (ProtocolSpec.append_Type_castAdd i) msg) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    exact (congrArg (cast (ProtocolSpec.append_Type_castAdd i))
      (Function.update_self (i.castAdd b) msg tr)).trans
      (Function.update_self i (cast (ProtocolSpec.append_Type_castAdd i) msg) tr.left).symm
  · have hn : (⟨j.val, by have := j.isLt; simp_all; omega⟩ : Fin (a+b)) ≠ i.castAdd b := by
      intro he
      exact h (Fin.ext (congrArg (fun z : Fin (a+b) => z.val) he))
    simp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.fst, Prod.fst]
    exact (congrArg (cast (ProtocolSpec.append_Type_castAdd j))
      (Function.update_of_ne hn msg tr)).trans
      (Function.update_of_ne h (cast (ProtocolSpec.append_Type_castAdd i) msg) tr.left).symm

/-- Updating a second-phase message projects to precisely that local update. -/
theorem right_update_right {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (tr : (A ++ B).Transcript (Fin.last (a+b))) (i : Fin b)
    (msg : (A ++ B).Type (i.natAdd a)) :
    (ProtocolSpec.Transcript.right (P₁ := A) (P₂ := B)
      (Function.update tr (i.natAdd a) msg)) =
    Function.update tr.right i (cast (ProtocolSpec.append_Type_natAdd i) msg) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    exact (congrArg (cast (ProtocolSpec.append_Type_natAdd i))
      (Function.update_self (i.natAdd a) msg tr)).trans
      (Function.update_self i (cast (ProtocolSpec.append_Type_natAdd i) msg) tr.right).symm
  · have hn : (⟨a+j.val, by simpa using Nat.add_lt_add_left j.isLt a⟩ : Fin (a+b)) ≠ i.natAdd a := by
      intro he
      apply h
      apply Fin.ext
      have := congrArg Fin.val he
      simpa using this
    simp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.snd, Prod.snd]
    exact (congrArg (cast (ProtocolSpec.append_Type_natAdd j))
      (Function.update_of_ne hn msg tr)).trans
      (Function.update_of_ne h (cast (ProtocolSpec.append_Type_natAdd i) msg) tr.right).symm

instance one_inhabited {dir : Direction} {Msg : Type} [Inhabited Msg]
    (i : Fin 1) : Inhabited ((one dir Msg).Type i) := inferInstanceAs (Inhabited Msg)

def appendInhabited {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (fa : ∀ i, Inhabited (A.Type i)) (fb : ∀ i, Inhabited (B.Type i)) :
    ∀ i, Inhabited ((A ++ B).Type i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [ProtocolSpec.append_Type_castAdd]
    exact fa j
  · rw [ProtocolSpec.append_Type_natAdd]
    exact fb j

instance rounds_inhabited (k : ℕ) : ∀ i, Inhabited ((rounds F k).Type i) := by
  letI : Inhabited F := ⟨0⟩
  induction k with
  | zero => exact fun i => i.elim0
  | succ k ih => exact appendInhabited one_inhabited (appendInhabited one_inhabited ih)

instance circuit_inhabited : {d : ℕ} → (C : GKR.Circuit F d) →
    ∀ i, Inhabited ((circuit F C).Type i)
  | _, .input _ =>
    letI : Inhabited F := ⟨0⟩
    one_inhabited
  | _, .layer (inDim := b) _ tail =>
    letI : Inhabited F := ⟨0⟩
    appendInhabited one_inhabited (appendInhabited (rounds_inhabited F (2 * b))
      (appendInhabited one_inhabited (circuit_inhabited tail)))

instance spec_inhabited {d : ℕ} (C : GKR.Circuit F d) (i) :
    Inhabited ((spec F C).Type i) := by
  letI : Inhabited F := ⟨0⟩
  exact appendInhabited one_inhabited (circuit_inhabited F C) i

instance one_fintype {dir : Direction} {Msg : Type} [Fintype Msg]
    : ∀ i : (one dir Msg).ChallengeIdx, Fintype ((one dir Msg).Challenge i) :=
  fun _ => inferInstanceAs (Fintype Msg)

instance empty_fintype (i : empty.ChallengeIdx) : Fintype (empty.Challenge i) := i.1.elim0

instance one_nonempty {dir : Direction} {Msg : Type} [Nonempty Msg] :
    ∀ i : (one dir Msg).ChallengeIdx, Nonempty ((one dir Msg).Challenge i) :=
  fun _ => inferInstanceAs (Nonempty Msg)

/-- A prover message round has no challenge, so its challenge types are nonempty
vacuously. -/
instance one_P_to_V_nonempty {Msg : Type} :
    ∀ i : (one .P_to_V Msg).ChallengeIdx, Nonempty ((one .P_to_V Msg).Challenge i) :=
  fun i => absurd i.2 (by simp [one])

instance empty_nonempty (i : empty.ChallengeIdx) : Nonempty (empty.Challenge i) := i.1.elim0

def appendFintype {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (fa : ∀ i, Fintype (A.Challenge i)) (fb : ∀ i, Fintype (B.Challenge i)) :
    ∀ i : (A ++ B).ChallengeIdx, Fintype ((A ++ B).Challenge i) := by
  letI := fa
  letI := fb
  intro i
  infer_instance

instance rounds_fintype [Fintype F] (k : ℕ) :
    ∀ i : (rounds F k).ChallengeIdx, Fintype ((rounds F k).Challenge i) := by
  induction k with
  | zero => exact empty_fintype
  | succ k ih => exact appendFintype one_fintype (appendFintype one_fintype ih)

instance circuit_fintype [Fintype F] : {d : ℕ} → (C : GKR.Circuit F d) →
    ∀ i : (circuit F C).ChallengeIdx, Fintype ((circuit F C).Challenge i)
  | _, .input _ => one_fintype
  | _, .layer (inDim := b) _ tail =>
    appendFintype one_fintype (appendFintype (rounds_fintype F (2 * b))
      (appendFintype one_fintype (circuit_fintype tail)))

instance spec_fintype [Fintype F] {d : ℕ} (C : GKR.Circuit F d)
    (i : (spec F C).ChallengeIdx) : Fintype ((spec F C).Challenge i) :=
  appendFintype one_fintype (circuit_fintype F C) i

instance one_decidableEq {dir : Direction} {Msg : Type} [DecidableEq Msg] :
    ∀ i : (one dir Msg).ChallengeIdx, DecidableEq ((one dir Msg).Challenge i) :=
  fun _ => inferInstanceAs (DecidableEq Msg)

instance empty_decidableEq (i : empty.ChallengeIdx) : DecidableEq (empty.Challenge i) := i.1.elim0

instance rounds_decidableEq [DecidableEq F] :
    (k : ℕ) → ∀ i : (rounds F k).ChallengeIdx, DecidableEq ((rounds F k).Challenge i)
  | 0 => empty_decidableEq
  | k + 1 =>
    @ProtocolSpec.append_challenge_decidableEq _ _ (one .P_to_V (F × F))
      (one .V_to_P F ++ rounds F k) one_decidableEq
      (@ProtocolSpec.append_challenge_decidableEq _ _ (one .V_to_P F) (rounds F k) one_decidableEq
        (rounds_decidableEq k))

instance circuit_decidableEq [DecidableEq F] : {d : ℕ} → (C : GKR.Circuit F d) →
    ∀ i : (circuit F C).ChallengeIdx, DecidableEq ((circuit F C).Challenge i)
  | _, .input _ => one_decidableEq
  | _, .layer (inDim := b) _ tail =>
    @ProtocolSpec.append_challenge_decidableEq _ _ (one .V_to_P (F × F)) _ one_decidableEq
      (@ProtocolSpec.append_challenge_decidableEq _ _ (rounds F (2 * b)) _
        (rounds_decidableEq F (2 * b))
        (@ProtocolSpec.append_challenge_decidableEq _ _ (one .P_to_V (F × F)) (circuit F tail)
          one_decidableEq (circuit_decidableEq tail)))

instance spec_decidableEq [DecidableEq F] {d : ℕ} (C : GKR.Circuit F d)
    (i : (spec F C).ChallengeIdx) : DecidableEq ((spec F C).Challenge i) :=
  @ProtocolSpec.append_challenge_decidableEq _ _ (initial F d) (circuit F C) one_decidableEq
    (circuit_decidableEq F C) i

/-- The unique verifier message of a one-move phase. -/
def verifierIndex (Msg : Type) : (one .V_to_P Msg).ChallengeIdx ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0, rfl⟩
  left_inv i := by apply Subtype.ext; exact Fin.eq_zero i.1 |>.symm
  right_inv _ := rfl

/-- Prover-only phases contribute no challenge indices. -/
def skipProver {n : ℕ} (Msg : Type) (P : ProtocolSpec n) :
    (one .P_to_V Msg ++ P).ChallengeIdx ≃ P.ChallengeIdx :=
  ProtocolSpec.challengeIdxEquiv.trans
    { toFun := Sum.elim (fun i => nomatch i.2) id
      invFun := Sum.inr
      left_inv := by intro i; cases i with
        | inl i => cases i.2
        | inr i => rfl
      right_inv := fun _ => rfl }

@[simp] theorem skipProver_inr {n : ℕ} (Msg : Type) (P : ProtocolSpec n)
    (i : P.ChallengeIdx) : skipProver Msg P (ProtocolSpec.ChallengeIdx.inr i) = i :=
  (skipProver Msg P).apply_symm_apply i

/-- Zero is the current round; successors are the remaining rounds. -/
def unitFin (k : ℕ) : Unit ⊕ Fin k ≃ Fin (k+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (.inl ()) (fun i => .inr i)
  left_inv x := by cases x with | inl x => cases x; rfl | inr x => rfl
  right_inv x := by refine Fin.cases ?_ (fun _ => rfl) x; rfl

def roundIndex : (k : ℕ) → (rounds F k).ChallengeIdx ≃ Fin k
  | 0 => { toFun := fun i => i.1.elim0, invFun := Fin.elim0,
           left_inv := fun i => i.1.elim0, right_inv := fun i => i.elim0 }
  | k+1 => (skipProver (F×F) _).trans
      (ProtocolSpec.challengeIdxEquiv.trans
        ((Equiv.sumCongr (verifierIndex F) (roundIndex k)).trans (unitFin k)))

/-- Actual scalar challenge location of an interleaved round. -/
def roundChallenge : (k : ℕ) → Fin k → (rounds F k).ChallengeIdx
  | 0, j => j.elim0
  | k+1, j => Fin.cases
      (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inl ⟨0,rfl⟩))
      (fun i => ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr (roundChallenge k i))) j

@[simp] theorem roundIndex_roundChallenge (k : ℕ) (j : Fin k) :
    roundIndex F k (roundChallenge F k j) = j := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · change unitFin k ((Equiv.sumCongr (verifierIndex F) (roundIndex F k))
        (ProtocolSpec.challengeIdxEquiv (skipProver (F×F) _
          (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr
            (roundChallenge F k i)))))) = i.succ
      rw [skipProver_inr, ProtocolSpec.challengeIdxEquiv_inr]
      exact congrArg Fin.succ (ih i)


@[simp] theorem roundIndex_symm (k : ℕ) (j : Fin k) :
    (roundIndex F k).symm j = roundChallenge F k j := by
  apply (roundIndex F k).injective
  simp only [Equiv.apply_symm_apply, roundIndex_roundChallenge]

theorem roundChallenge_val (k : ℕ) (j : Fin k) :
    (roundChallenge F k j).1.val = 2*j.val+1 := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · change 1+(1+(roundChallenge F k i).1.val) = 2*(i.val+1)+1
      rw [ih]
      omega

/-- All interleaved challenge coordinates have exactly the scalar field type. -/
theorem roundChallenge_type (k : ℕ) (j : Fin k) :
    (rounds F k).Challenge (roundChallenge F k j) = F := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · change (one .P_to_V (F×F) ++ (one .V_to_P F ++ rounds F k)).Challenge
        (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr (roundChallenge F k i))) = F
      rw [ProtocolSpec.append_Challenge_inr, ProtocolSpec.append_Challenge_inr]
      exact ih i

/-- A decoded round depends only on the raw messages through its challenge. -/
theorem roundMessages_congr_at (k : ℕ) (j : Fin k)
    (tr tr' : (rounds F k).Transcript (Fin.last (roundLength k)))
    (h : ∀ i, i.val ≤ 2*j.val+1 → tr i = tr' i) :
    roundMessages F k tr j = roundMessages F k tr' j := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    revert h
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      have hpair : tr.left = tr'.left := by
        funext i
        apply left_agrees tr tr' 1 (fun i hi => h i hi) i
        have hi : i.val < 1 := i.isLt
        omega
      have hscalar : tr.right.left = tr'.right.left := by
        funext i
        apply left_agrees tr.right tr'.right 0
          (right_agrees tr tr' 0 (fun i hi => h i hi)) i
        have hi : i.val < 1 := i.isLt
        omega
      simp only [roundMessages_zero, hpair, hscalar]
    · intro h
      rw [roundMessages_succ, roundMessages_succ]
      apply ih j tr.right.right tr'.right.right
      intro i hi
      apply right_agrees tr.right tr'.right (2*j.val+1)
        (right_agrees tr tr' (1+(2*j.val+1)) ?_) i hi
      intro i hi
      apply h i
      change i.val ≤ 2*(j.val+1)+1
      omega


/-- Replace a scalar verifier challenge in the actual typed transcript. -/
def roundUpdate (k : ℕ) (tr : (rounds F k).Transcript (Fin.last (roundLength k)))
    (j : Fin k) (x : F) : (rounds F k).Transcript (Fin.last (roundLength k)) :=
  Function.update tr (roundChallenge F k j).1 (cast (roundChallenge_type F k j).symm x)

/-- The first prover message precedes every challenge and is unchanged. -/
theorem roundUpdate_first (k : ℕ)
    (tr : (rounds F (k+1)).Transcript (Fin.last (roundLength (k+1)))) (j : Fin (k+1)) (x : F) :
    (roundUpdate F (k+1) tr j x).left = tr.left := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact left_update_right tr _ _
  · exact left_update_right tr _ _

/-- Reading the selected scalar challenge returns its replacement exactly. -/
theorem roundUpdate_at (k : ℕ)
    (tr : (rounds F k).Transcript (Fin.last (roundLength k))) (j : Fin k) (x : F) :
    cast (roundChallenge_type F k j) (roundUpdate F k tr j x (roundChallenge F k j).1) = x := by
  unfold roundUpdate
  have h := Function.update_self (roundChallenge F k j).1
    (cast (roundChallenge_type F k j).symm x) tr
  exact (congrArg (cast (roundChallenge_type F k j)) h).trans (cast_cast _ _ _)

/-- The scalar challenge accessor is the corresponding typed raw coordinate. -/
theorem roundMessages_challenge (k : ℕ)
    (tr : (rounds F k).Transcript (Fin.last (roundLength k))) (j : Fin k) :
    (roundMessages F k tr j).challenge =
      cast (roundChallenge_type F k j) (tr (roundChallenge F k j).1) := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [roundMessages, roundChallenge, Fin.cases_zero, oneValue,
        ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.fst,
        ProtocolSpec.Transcript.snd, cast_cast]
      rfl
    · refine (ih tr.right.right j).trans ?_
      dsimp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.snd]
      exact (cast_cast _ _ _).trans (cast_cast _ _ _)

end GordieHowe.GKR.Schedule
