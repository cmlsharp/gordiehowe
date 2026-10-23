-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.AppendN
public import GordieHowe.Model.IOP.AppendView

@[expose] public section

/-!
# Views of an `m`-fold append, and a family of messages sent as one

The prover messages of `ProtocolSpec.appendN m P` are those of the parts. Message views of each
part, all reading challenges of a common type `Ch`, give the views of the append (`msgN`, by the
same recursion as `appendN`, through the binary `appendMsg`). Its view is the family of the
parts' views (`viewEquivN`), and on a full transcript that family is the parts' views of the
parts of the transcript (`viewEquivN_see`, `viewEquivN_see_part`).

`MessageView.pi` reads a family of messages `∀ i, M i`, sent in one round, as one table: the
position `⟨i, j⟩` (`CircuitPos`) is position `j` of message `i`, queried when message `i`'s view
queries it (`see_pi`). This is the view of the commitments of `m` circuits sent together.
-/

namespace GordieHowe.IOP

open ProtocolSpec

/-! ### A family of messages in one round -/

/-- **A position of one of a family of tables** (one table per circuit, for the commitments of
`m` circuits sent together): the circuit and a position of its table. -/
structure CircuitPos {ι : Type} (I : ι → Type) where
  /-- The circuit. -/
  circuit : ι
  /-- The position in its table. -/
  pos : I circuit

/-- **An entry of one of a family of tables**: the circuit and an entry of its table. -/
structure CircuitEntry {ι : Type} (A : ι → Type) where
  /-- The circuit. -/
  circuit : ι
  /-- The entry of its table. -/
  entry : A circuit

/-- The entries of one circuit's table, as entries of the family. -/
theorem CircuitEntry.mk_injective {ι : Type} {A : ι → Type} (i : ι) :
    Function.Injective (CircuitEntry.mk (A := A) i) := fun _ _ h => by
  cases h
  rfl

/-- Positions of a family of tables are dependent pairs. -/
def CircuitPos.equivSigma {ι : Type} (I : ι → Type) : CircuitPos I ≃ Σ i, I i where
  toFun x := ⟨x.circuit, x.pos⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace MessageView

variable {ι Ch : Type} [Fintype ι] [DecidableEq ι] {M I A : ι → Type}

/-- **A family of messages read as one table**: position `⟨i, j⟩` is position `j` of message
`i`, queried when the view of message `i` queries `j`. -/
def pi (O : ∀ i, MessageView (M i) Ch (I i) (A i)) :
    MessageView (∀ i, M i) Ch (CircuitPos I) (CircuitEntry A) where
  read m x := ⟨x.circuit, (O x.circuit).read (m x.circuit) x.pos⟩
  read_injective _ _ h := funext fun i =>
    (O i).read_injective (funext fun j => CircuitEntry.mk_injective i (congrFun h ⟨i, j⟩))
  queries ch := (Finset.univ.sigma fun i => (O i).queries ch).map
    (CircuitPos.equivSigma I).symm.toEmbedding
  decEq := letI := fun i => (O i).decEq
    fun x y => decidable_of_iff _ (CircuitPos.equivSigma I).injective.eq_iff

theorem mem_pi_queries (O : ∀ i, MessageView (M i) Ch (I i) (A i)) {ch : Ch} {x : CircuitPos I} :
    x ∈ (pi O).queries ch ↔ x.pos ∈ (O x.circuit).queries ch := by
  simp only [pi, Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  rfl

/-- What the verifier sees of a family at position `⟨i, j⟩` is what it sees of message `i` at
position `j`. -/
theorem see_pi (O : ∀ i, MessageView (M i) Ch (I i) (A i)) (ch : Ch) (m : ∀ i, M i)
    (x : CircuitPos I) :
    (pi O).see ch m x = ((O x.circuit).see ch (m x.circuit) x.pos).map (CircuitEntry.mk x.circuit) := by
  by_cases h : x.pos ∈ (O x.circuit).queries ch
  · rw [see_of_mem _ ((mem_pi_queries O).mpr h), see_of_mem _ h]
    rfl
  · have h' : x ∉ (pi O).queries ch := fun h' => h ((mem_pi_queries O).mp h')
    simp only [see, h, h', ↓reduceIte, Option.map_none]

/-- Two families look the same exactly when each message looks the same. -/
theorem see_pi_eq_iff (O : ∀ i, MessageView (M i) Ch (I i) (A i)) (ch : Ch) (m m' : ∀ i, M i) :
    (pi O).see ch m = (pi O).see ch m' ↔ ∀ i, (O i).see ch (m i) = (O i).see ch (m' i) := by
  constructor
  · intro h i
    funext j
    have := congrFun h ⟨i, j⟩
    rw [see_pi, see_pi] at this
    exact Option.map_injective (CircuitEntry.mk_injective i) this
  · intro h
    funext x
    rw [see_pi, see_pi, h x.circuit]

end MessageView

/-! ### Views of the append -/

variable {Ch : Type}

/-- A family of types on the prover rounds of the append, from a family on each part's prover
rounds. -/
def famN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (∀ i, (P i).MessageIdx → Type) → (appendN m P).MessageIdx → Type
  | 0, _, _, _ => fun k => k.1.elim0
  | 1, _, _, T => T 0
  | m + 2, _, _, T => appendFamily (T 0) (famN (m + 1) fun i => T i.succ)

/-- **The message views of the append** from the message views of the parts. -/
def msgN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    {Idx Ans : ∀ i, (P i).MessageIdx → Type} →
    (∀ i (j : (P i).MessageIdx), MessageView ((P i).Type j.1) Ch (Idx i j) (Ans i j)) →
    ∀ k : (appendN m P).MessageIdx,
      MessageView ((appendN m P).Type k.1) Ch (famN m Idx k) (famN m Ans k)
  | 0, _, _, _, _, _ => fun k => k.1.elim0
  | 1, _, _, _, _, msg => msg 0
  | m + 2, _, _, _, _, msg => appendMsg (msg 0) (msgN (m + 1) fun i => msg i.succ)

/-- **The view of the append is the family of the parts' views.** -/
def viewEquivN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    {Idx Ans : ∀ i, (P i).MessageIdx → Type} →
    (∀ k : (appendN m P).MessageIdx, famN m Idx k → Option (famN m Ans k)) ≃
      ∀ i, ∀ j : (P i).MessageIdx, Idx i j → Option (Ans i j)
  | 0, _, _, _, _ =>
    { toFun := fun _ i => i.elim0
      invFun := fun _ k => k.1.elim0
      left_inv := fun _ => funext fun k => k.1.elim0
      right_inv := fun _ => funext fun i => i.elim0 }
  | 1, _, P, Idx, Ans =>
    { toFun := fun v => Fin.cases (motive := fun i => ∀ j : (P i).MessageIdx,
        Idx i j → Option (Ans i j)) v fun i => i.elim0
      invFun := fun w => w 0
      left_inv := fun _ => rfl
      right_inv := fun w => funext fun i => by
        cases i using Fin.cases with
        | zero => rfl
        | succ i => exact i.elim0 }
  | m + 2, _, P, Idx, Ans => appendViewEquiv.trans
      ((Equiv.prodCongr (Equiv.refl _) (viewEquivN (m + 1))).trans
        (Fin.consEquiv fun i => ∀ j : (P i).MessageIdx, Idx i j → Option (Ans i j)))

/-- On a joined transcript, the family of the parts' views is the parts' views of the parts. -/
theorem viewEquivN_see : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    {Idx Ans : ∀ i, (P i).MessageIdx → Type} →
    (msg : ∀ i (j : (P i).MessageIdx), MessageView ((P i).Type j.1) Ch (Idx i j) (Ans i j)) →
    (ch : Ch) → (trs : ∀ i, (P i).Transcript (Fin.last (n i))) →
    viewEquivN m (fun k => (msgN m msg k).see ch (joinN m trs k.1)) =
      fun i j => (msg i j).see ch (trs i j.1)
  | 0, _, _, _, _, _, _, _ => funext fun i => i.elim0
  | 1, _, _, _, _, _, _, _ => funext fun i => by
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact i.elim0
  | m + 2, _, P, Idx, Ans, msg, ch, trs => by
    change Fin.consEquiv (fun i => ∀ j : (P i).MessageIdx, Idx i j → Option (Ans i j))
      (Prod.map id (viewEquivN (m + 1) (Idx := fun i => Idx i.succ) (Ans := fun i => Ans i.succ))
      (appendViewEquiv fun k => (appendMsg (msg 0) (msgN (m + 1) fun i => msg i.succ) k).see ch
        (Transcript.join (trs 0) (joinN (m + 1) fun i => trs i.succ) k.1))) = _
    rw [appendViewEquiv_see]
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact congrFun (viewEquivN_see (m + 1) (fun i => msg i.succ) ch _) i

/-- Joining the parts of a full transcript of the append gives it back. -/
@[simp] theorem joinN_part : (m : ℕ) → {n : Fin m → ℕ} →
    {P : (i : Fin m) → ProtocolSpec (n i)} →
    (tr : (appendN m P).Transcript (Fin.last (lenN m n))) → joinN m (Transcript.part m tr) = tr
  | 0, _, _, _ => funext fun i => i.elim0
  | 1, _, _, _ => rfl
  | m + 2, _, P, tr => by
    change Transcript.join tr.left (joinN (m + 1) (Transcript.part (m + 1) tr.right)) = tr
    rw [joinN_part (m + 1)]
    exact Transcript.join_left_right (P₁ := P 0) (P₂ := appendN (m + 1) fun i => P i.succ) tr

/-- On any full transcript, the family of the parts' views is the parts' views of its parts. -/
theorem viewEquivN_see_part {m : ℕ} {n : Fin m → ℕ} {P : (i : Fin m) → ProtocolSpec (n i)}
    {Idx Ans : ∀ i, (P i).MessageIdx → Type}
    (msg : ∀ i (j : (P i).MessageIdx), MessageView ((P i).Type j.1) Ch (Idx i j) (Ans i j))
    (ch : Ch) (tr : (appendN m P).Transcript (Fin.last (lenN m n))) :
    viewEquivN m (fun k => (msgN m msg k).see ch (tr k.1)) =
      fun i j => (msg i j).see ch (Transcript.part m tr i j.1) := by
  conv_lhs => rw [← joinN_part m tr]
  exact viewEquivN_see m msg ch _

/-- The parts of a full transcript carrying the challenges `ch` carry the parts' challenges. -/
theorem part_challenge : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    {tr : (appendN m P).Transcript (Fin.last (lenN m n))} → {ch : (appendN m P).Challenges} →
    (∀ k : (appendN m P).ChallengeIdx, tr k.1 = ch k) →
    ∀ i (j : (P i).ChallengeIdx), Transcript.part m tr i j.1 = chN m ch i j
  | 0, _, _, _, _, _, i, _ => i.elim0
  | 1, _, _, _, _, h, i, j => by
    cases i using Fin.cases with
    | zero => exact h j
    | succ i => exact i.elim0
  | m + 2, _, _, _, _, h, i, j => by
    cases i using Fin.cases with
    | zero => exact Transcript.left_challenge h j
    | succ i => exact part_challenge (m + 1) (Transcript.right_challenge h) i j

end GordieHowe.IOP
